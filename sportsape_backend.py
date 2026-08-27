#!/usr/bin/env python3
"""
Sportsape BitBot backend focused on browser-based login, route discovery, and balance extraction.
"""

from __future__ import annotations

import base64
import csv
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from queue import Empty, Queue
from urllib.parse import urljoin

import requests

from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from resource_path import resource_path, writable_path

LOGIN_URL = "https://www.ke.sportpesa.com/en/sports-betting/football-1/"
SITE_ORIGIN = "https://www.ke.sportpesa.com"
HOME_URL = f"{SITE_ORIGIN}/en"
USER_API_LOGIN_URL = "https://user-api.ke.sportpesa.com/player/v2/login"
CONFIG_PATH = Path(writable_path("config/endpoints.json"))
BUNDLED_CONFIG_PATH = Path(resource_path("config/endpoints.json"))
DISCOVERED_ROUTES_PATH = Path(writable_path("config/discovered_sportsape_routes.json"))
BALANCE_RE = re.compile(r"(?i)(?:kes|ksh)?\s*([0-9][0-9,]*\.?[0-9]{0,2})")
COIN_RE = re.compile(r"(?i)coins?\s*[:\-]?\s*([0-9][0-9,]*)")


class NullAIEngine:
    def __init__(self) -> None:
        self.enabled = False
        self.api_key = ""
        self.error_patterns = {}
        self.permanent_fixes = {}
        self.selector_learnings = {}
        self.operation_history = []
        self.system_state = {}
        self.self_improvement_log = []
        self.fix_history = []

    def pre_qualify_accounts_for_operation(self, *_args, **_kwargs):
        return {}

    def remember_repeated_task(self, *_args, **_kwargs):
        return None


class SportsapeBackend:
    """Browser-backed SportPesa integration with lightweight route discovery."""

    def __init__(self, headless: bool = True, verbose: bool = False):
        self.running = True
        self.headless = headless
        self.verbose = verbose
        self.base_url = LOGIN_URL
        self.permanent_failures: set[str] = set()
        self.ai_engine = NullAIEngine()
        self.browser_pool = None
        self.session = None
        self.selenium_fetcher = None
        self.selenium_driver = None
        self._balance_cache_lock = threading.Lock()
        self._gui_lock = threading.Lock()
        self._driver_lock = threading.Lock()
        self._active_drivers_lock = threading.Lock()
        self._route_file_lock = threading.Lock()
        self._preloaded_drivers = []
        self._driver_warmup_in_progress = False
        self._active_drivers = set()
        self.max_parallel_workers = 3
        self.max_preloaded_drivers = max(1, self.max_parallel_workers)
        self.balance_cache = {"timestamp": 0, "results": {}}
        self.route_config = self._load_route_config()

    def _load_route_config(self) -> dict:
        defaults = {
            "base_url": LOGIN_URL,
            "endpoints": {
                "country": "/api/country",
            },
            "route_candidates": {
                "login": ["/login_check", "/en/login"],
                "profile": ["/en/profile"],
                "deposit": ["/en/deposit"],
                "withdraw": ["/en/withdraw"],
            },
            "confirmed_routes": {
                "country": "/api/country",
            },
        }
        for path in (CONFIG_PATH, BUNDLED_CONFIG_PATH):
            if not path.exists():
                continue
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    merged = defaults.copy()
                    merged.update(data)
                    return merged
            except Exception:
                pass
        return defaults

    def _driver_is_usable(self, driver) -> bool:
        if not driver or not getattr(driver, "session_id", None):
            return False
        try:
            driver.execute_script("return document.readyState")
            return True
        except Exception:
            return False

    def _cleanup_driver(self, driver) -> None:
        if not driver:
            return
        temp_profile = getattr(driver, "_sportsape_temp_profile", None)
        with self._active_drivers_lock:
            self._active_drivers.discard(driver)
        try:
            driver.quit()
        except Exception:
            pass
        if temp_profile and os.path.exists(temp_profile):
            shutil.rmtree(temp_profile, ignore_errors=True)
        if self.selenium_driver is driver:
            self.selenium_driver = None

    def _track_active_driver(self, driver) -> None:
        if not driver:
            return
        with self._active_drivers_lock:
            self._active_drivers.add(driver)

    def _take_preloaded_driver(self):
        stale_drivers = []
        with self._driver_lock:
            while self._preloaded_drivers:
                driver = self._preloaded_drivers.pop(0)
                if self._driver_is_usable(driver):
                    self.selenium_driver = driver
                    return driver
                stale_drivers.append(driver)
        for driver in stale_drivers:
            self._cleanup_driver(driver)
        return None

    def _store_preloaded_driver(self, driver) -> bool:
        if not self._driver_is_usable(driver):
            self._cleanup_driver(driver)
            return False
        with self._driver_lock:
            self._preloaded_drivers = [
                existing for existing in self._preloaded_drivers if self._driver_is_usable(existing)
            ]
            if len(self._preloaded_drivers) < self.max_preloaded_drivers:
                self._preloaded_drivers.append(driver)
                self.selenium_driver = driver
                return True
        self._cleanup_driver(driver)
        return False

    def _reset_driver_state(self, driver) -> None:
        try:
            driver.delete_all_cookies()
        except Exception:
            pass
        try:
            driver.get(LOGIN_URL)
            WebDriverWait(driver, 10).until(
                lambda d: d.execute_script("return document.readyState") != "loading"
            )
            driver.execute_script("window.localStorage.clear();")
            driver.execute_script("window.sessionStorage.clear();")
            self._dismiss_visible_promos(driver, rounds=1)
        except Exception:
            pass

    def _acquire_driver(self, gui_callback=None):
        driver = self._take_preloaded_driver()
        if driver:
            self._emit_direct(gui_callback, "   Using preloaded browser session...")
            return driver
        start = time.perf_counter()
        driver = self._build_driver(gui_callback=gui_callback)
        self._emit_direct(gui_callback, f"   Browser launched in {time.perf_counter() - start:.1f}s")
        return driver

    def warm_browser(self, gui_callback=None) -> bool:
        existing_driver = self._take_preloaded_driver()
        if existing_driver:
            self._store_preloaded_driver(existing_driver)
            return True

        with self._driver_lock:
            if self._driver_warmup_in_progress:
                return True
            self._driver_warmup_in_progress = True

        driver = None
        try:
            driver = self._build_driver(gui_callback=gui_callback)
            self._reset_driver_state(driver)
            return self._store_preloaded_driver(driver)
        finally:
            if driver and driver not in self._preloaded_drivers:
                self._cleanup_driver(driver)
            with self._driver_lock:
                self._driver_warmup_in_progress = False

    def warm_browser_pool(self, target_count: int, gui_callback=None) -> bool:
        target_count = max(1, min(target_count, self.max_preloaded_drivers))
        prepared = 0
        with self._driver_lock:
            self._preloaded_drivers = [
                driver for driver in self._preloaded_drivers if self._driver_is_usable(driver)
            ]
            prepared = len(self._preloaded_drivers)
            if prepared >= target_count:
                return True
            if self._driver_warmup_in_progress:
                return prepared > 0
            self._driver_warmup_in_progress = True

        try:
            while prepared < target_count and self.running:
                driver = self._build_driver(gui_callback=gui_callback)
                try:
                    self._reset_driver_state(driver)
                    if self._store_preloaded_driver(driver):
                        prepared += 1
                        self._emit_direct(
                            gui_callback,
                            f"   Preloaded browser {prepared}/{target_count} ready for workers...",
                        )
                        driver = None
                    else:
                        break
                finally:
                    if driver:
                        self._cleanup_driver(driver)
            return prepared >= target_count
        finally:
            with self._driver_lock:
                self._driver_warmup_in_progress = False

    def _build_driver(self, gui_callback=None, force_visible=False) -> webdriver.Chrome:
        options = Options()
        options.page_load_strategy = 'normal'
        if self.headless and not force_visible:
            options.add_argument("--headless=new")
        if force_visible:
            options.add_argument("--window-size=1280,800")
        else:
            options.add_argument("--window-size=430,932")
        options.add_argument("--disable-gpu")
        options.add_argument("--no-sandbox")
        options.add_argument("--disable-dev-shm-usage")
        options.add_argument("--disable-blink-features=AutomationControlled")
        options.add_experimental_option("excludeSwitches", ["enable-automation", "enable-logging"])
        options.add_experimental_option("useAutomationExtension", False)
        options.add_experimental_option("prefs", {
            "credentials_enable_service": False,
            "profile.password_manager_enabled": False,
            "autofill.profile_enabled": False,
            "autofill.credit_card_enabled": False,
        })
        options.add_argument("--disable-extensions")
        options.add_argument("--disable-infobars")
        options.add_argument("--disable-notifications")
        options.add_argument("--dns-prefetch-disable")
        options.add_argument("--disable-browser-side-navigation")
        if not force_visible:
            options.add_experimental_option(
                "mobileEmulation",
                {
                    "deviceMetrics": {"width": 430, "height": 932, "pixelRatio": 2.75},
                    "userAgent": (
                        "Mozilla/5.0 (Linux; Android 13; Pixel 7) "
                        "AppleWebKit/537.36 (KHTML, like Gecko) "
                        "Chrome/137.0.0.0 Mobile Safari/537.36"
                    ),
                },
            )
        options.set_capability("goog:loggingPrefs", {"performance": "ALL", "browser": "ALL"})

        temp_profile = tempfile.mkdtemp(prefix="sportsape_chrome_")
        options.add_argument(f"--user-data-dir={temp_profile}")

        try:
            # Use a simpler service initialization
            service = Service()
            
            driver = webdriver.Chrome(service=service, options=options)
            self._track_active_driver(driver)
            self.selenium_driver = driver
            
            driver.set_page_load_timeout(30)
            
            # BLOCK HEAVY RESOURCES (Ads, Analytics, Tracking)
            driver.execute_cdp_cmd("Network.setBlockedURLs", {
                "urls": [
                    "*google-analytics.com*", "*googletagmanager.com*", "*facebook.net*",
                    "*doubleclick.net*", "*hotjar.com*", "*sentry.io*",
                ]
            })
            driver.execute_cdp_cmd("Network.enable", {})
            driver._sportsape_temp_profile = temp_profile  # type: ignore[attr-defined]
            return driver
        except Exception as e:
            self._emit_direct(gui_callback, f"   ❌ Browser launch failed: {str(e)[:50]}")
            # Cleanup profile if driver creation fails
            if os.path.exists(temp_profile):
                shutil.rmtree(temp_profile, ignore_errors=True)
            raise e

    def _emit_direct(self, gui_callback, message: str) -> None:
        """Internal emit that bypasses the verbose check for critical diagnostics"""
        if gui_callback:
            with self._gui_lock:
                gui_callback(message)

    def normalize_phone(self, phone: str) -> str:
        phone = "".join(filter(str.isdigit, phone))
        if phone.startswith("0"):
            return "254" + phone[1:]
        if phone.startswith("7") and len(phone) == 9:
            return "254" + phone
        if not phone.startswith("254"):
            return "254" + phone
        return phone

    def _format_sportsape_login_phone(self, phone: str) -> str:
        digits = "".join(filter(str.isdigit, phone))
        if digits.startswith("254") and len(digits) == 12:
            return "0" + digits[3:]
        if digits.startswith("7") and len(digits) == 9:
            return "0" + digits
        return digits

    def _find_first(self, driver: webdriver.Chrome, selectors: list[str]):
        for selector in selectors:
            try:
                element = driver.find_element(By.CSS_SELECTOR, selector)
                if element.is_displayed():
                    return element
            except Exception:
                continue
        return None

    def _emit(self, gui_callback, message: str) -> None:
        if gui_callback and self.verbose:
            with self._gui_lock:
                gui_callback(message)

    def _read_performance_messages(self, driver: webdriver.Chrome) -> list[dict]:
        messages = []
        for entry in driver.get_log("performance"):
            try:
                messages.append(json.loads(entry["message"])["message"])
            except Exception:
                continue
        return messages

    def _wait_for_site_shell(self, driver: webdriver.Chrome, timeout: int = 20) -> None:
        WebDriverWait(driver, timeout).until(
            lambda d: d.execute_script("return document.readyState") in {"interactive", "complete"}
        )
        WebDriverWait(driver, timeout).until(EC.presence_of_element_located((By.TAG_NAME, "body")))
        WebDriverWait(driver, timeout).until(
            lambda d: "sportpesa" in (
                d.execute_script("return ((document.body && document.body.innerText) || '').toLowerCase();")
            )
        )

    def _click_by_text(self, driver: webdriver.Chrome, labels: list[str]) -> bool:
        script = """
const labels = arguments[0].map(v => v.toLowerCase());
function visible(el) {
  if (!el) return false;
  const s = window.getComputedStyle(el);
  const r = el.getBoundingClientRect();
  return s.display !== 'none' && s.visibility !== 'hidden' &&
    parseFloat(s.opacity || '1') > 0.05 &&
    r.width > 6 && r.height > 6 &&
    r.bottom > 0 && r.right > 0 &&
    r.top < window.innerHeight && r.left < window.innerWidth;
}
function click(el) {
  try { el.click(); return true; } catch (e) {}
  try {
    el.dispatchEvent(new MouseEvent('click', {bubbles: true, cancelable: true, view: window}));
    return true;
  } catch (e) {}
  return false;
}
const nodes = Array.from(document.querySelectorAll('button,[role="button"],a,div,span'));
for (const node of nodes) {
  if (!visible(node)) continue;
  const text = (node.innerText || node.textContent || '').trim().toLowerCase().replace(/\\s+/g, ' ');
  if (!text) continue;
  if (labels.some(label => text === label || text.includes(label))) {
    if (click(node)) return true;
  }
}
return false;
"""
        try:
            return bool(driver.execute_script(script, labels))
        except Exception:
            return False

    def _click_first_visible_selector(self, driver: webdriver.Chrome, selectors: list[str]) -> bool:
        for selector in selectors:
            try:
                clicked = driver.execute_script(
                    """
const selector = arguments[0];
function visible(el) {
  if (!el) return false;
  const s = getComputedStyle(el);
  const r = el.getBoundingClientRect();
  return s.display !== 'none' && s.visibility !== 'hidden' &&
    parseFloat(s.opacity || '1') > 0.05 &&
    r.width > 4 && r.height > 4;
}
const nodes = Array.from(document.querySelectorAll(selector));
for (const node of nodes) {
  if (!visible(node)) continue;
  try { node.click(); return true; } catch (e) {}
  try {
    node.dispatchEvent(new MouseEvent('click', {bubbles: true, cancelable: true, view: window}));
    return true;
  } catch (e) {}
}
return false;
""",
                    selector,
                )
                if clicked:
                    return True
            except Exception:
                continue
        return False

    def _dismiss_visible_promos(self, driver: webdriver.Chrome, rounds: int = 3) -> int:
        total_actions = 0
        for _ in range(rounds):
            for selectors in (
                [".close.clickScale-92", ".close", ".closebtn"],
                [".swiperClose", ".closeBtnX", ".modal-close", ".popup-close-btn"],
                ["[class*='close']", "[id*='close']"],
            ):
                if self._click_first_visible_selector(driver, selectors):
                    total_actions += 1
                    time.sleep(0.3)
            self._click_by_text(
                driver,
                [
                    "close",
                    "skip",
                    "dismiss",
                    "cancel",
                    "no thanks",
                    "later",
                    "accept",
                    "accept all",
                    "agree",
                    "got it",
                ],
            )
            time.sleep(0.4)
        return total_actions

    def _find_login_inputs(self, driver: webdriver.Chrome):
        phone_input = self._find_first(
            driver,
            [
                "input[data-qa='common-login-username']",
                "input#username",
                "input[name='username']",
                "input#user",
                "input[name='user']",
                "input[placeholder*='obile']",
                "input[type='tel']",
                "input[inputmode='numeric']",
                "input[type='number']",
                "input[name*='phone']",
                "input[name*='mobile']",
                "input[id*='phone']",
                "input[id*='mobile']",
                "input[placeholder*='07']",
                "input[placeholder*='254']",
                "input[type='text']",
            ],
        )
        password_input = self._find_first(
            driver,
            [
                "input[data-qa='common-login-password']",
                "input#password",
                "input[type='password']",
                "input[name*='password']",
                "input[id*='password']",
            ],
        )
        return phone_input, password_input

    def _click_login_entry(self, driver: webdriver.Chrome) -> bool:
        phone_input, password_input = self._find_login_inputs(driver)
        if phone_input and password_input:
            return True
        # SportPesa mobile: the login form lives on its own /login page.
        try:
            driver.get(f"{SITE_ORIGIN}/login")
            return True
        except Exception:
            pass
        if self._click_by_text(driver, ["log in", "login", "sign in"]):
            return True
        for route in ("#/Login", "#/login"):
            try:
                driver.execute_script("window.location.hash = arguments[0];", route)
                time.sleep(0.2)
                return True
            except Exception:
                continue
        try:
            body = driver.find_element(By.TAG_NAME, "body")
            ActionChains(driver).move_to_element_with_offset(body, 285, 90).click().perform()
            return True
        except Exception:
            return False

    def _wait_for_login_inputs(self, driver: webdriver.Chrome, gui_callback=None, timeout: int = 20):
        deadline = time.time() + timeout
        self._dismiss_visible_promos(driver, rounds=2)
        self._emit(gui_callback, "   Opening login form...")
        self._click_login_entry(driver)
        retry_count = 0
        while time.time() < deadline:
            phone_input, password_input = self._find_login_inputs(driver)
            if phone_input and password_input:
                return phone_input, password_input
            time.sleep(0.3)
            retry_count += 1
            if retry_count in {4, 8}:
                self._dismiss_visible_promos(driver, rounds=1)
                self._click_login_entry(driver)
        return None, None

    def _click_login_submit(self, driver: webdriver.Chrome) -> bool:
        if self._click_first_visible_selector(
            driver,
            [
                "input[data-qa='common-login-submit']",
                "#secondary_login input[type='submit']",
                "button.login-form__button",
                "input[type='submit']",
                "button[type='submit']",
                ".paybtn.clickScale.flex-box-row.middle",
                ".btnPwd .paybtn",
            ],
        ):
            return True
        try:
            submit = self._find_first(
                driver,
                [
                    "button[type='submit']",
                    "input[type='submit']",
                    "button",
                    "[role='button']",
                ],
            )
            if submit:
                driver.execute_script("arguments[0].click();", submit)
                return True
        except Exception:
            pass
        if self._click_by_text(driver, ["log in", "login", "sign in"]):
            return True
        return False

    def _wait_for_post_login(self, driver: webdriver.Chrome, timeout: int = 15) -> str:
        deadline = time.time() + timeout
        while time.time() < deadline:
            self._dismiss_visible_promos(driver, rounds=1)
            try:
                body_text = driver.execute_script("return ((document.body && document.body.innerText) || '').toLowerCase();")
            except Exception:
                body_text = ""

            for marker in (
                "does not exist or incorrect",
                "incorrect password",
                "incorrect username",
                "invalid credentials",
                "invalid login",
                "user does not exist",
            ):
                if marker in body_text:
                    return "failed"

            # More reliable check: Wait until we see currency AND login inputs are gone
            # or we've reached a known logged-in state (like seeing 'Deposit' or 'KSH')
            has_currency = "ksh" in body_text or "kes" in body_text or "deposit" in body_text or "balance" in body_text or "logout" in body_text
            phone_input, password_input = self._find_login_inputs(driver)

            if has_currency and not (phone_input and password_input):
                return "ok"
            time.sleep(0.3)
        return "timeout"

    def _logout_current_session(self, driver: webdriver.Chrome) -> bool:
        self._dismiss_visible_promos(driver, rounds=1)
        if self._click_by_text(driver, ["logout", "log out", "sign out", "exit login", "exit"]):
            time.sleep(0.5)
            return True
        return False

    def _collect_network(self, driver: webdriver.Chrome, messages: list[dict] | None = None) -> list[dict]:
        if messages is None:
            messages = self._read_performance_messages(driver)
        entries = []
        seen = set()
        keywords = (
            "api",
            "login",
            "auth",
            "balance",
            "wallet",
            "user",
            "account",
            "profile",
            "withdraw",
            "deposit",
            "bonus",
            "country",
        )
        for message in messages:
            try:
                method = message.get("method")
                params = message.get("params", {})
                payload = None

                if method == "Network.requestWillBeSent":
                    request = params.get("request", {})
                    url = request.get("url", "")
                    if any(key in url.lower() for key in keywords):
                        payload = {
                            "kind": "request",
                            "method": request.get("method"),
                            "url": url,
                        }
                elif method == "Network.responseReceived":
                    response = params.get("response", {})
                    url = response.get("url", "")
                    if any(key in url.lower() for key in keywords):
                        payload = {
                            "kind": "response",
                            "status": response.get("status"),
                            "mimeType": response.get("mimeType"),
                            "url": url,
                            "requestId": params.get("requestId"),
                        }

                if payload:
                    key = f"{payload['kind']}::{payload['url']}"
                    if key not in seen:
                        seen.add(key)
                        entries.append(payload)
            except Exception:
                continue
        return entries

    def _extract_token(self, driver: webdriver.Chrome, messages: list[dict] | None = None) -> str | None:
        if messages is None:
            messages = self._read_performance_messages(driver)
        for message in messages:
            try:
                method = message.get("method")
                params = message.get("params", {})

                if method == "Network.responseReceived":
                    response = params.get("response", {})
                    url = response.get("url", "")
                    if any(key in url.lower() for key in ("login", "auth")) and response.get("status") == 200:
                        request_id = params.get("requestId")
                        if not request_id:
                            continue
                        try:
                            body = driver.execute_cdp_cmd("Network.getResponseBody", {"requestId": request_id})
                            body_text = body.get("body", "")
                            if not body_text:
                                continue
                            parsed = json.loads(body_text)
                            token = parsed.get("token")
                            if token:
                                return token
                        except Exception:
                            continue

                if method == "Network.requestWillBeSent":
                    headers = params.get("request", {}).get("headers", {})
                    auth = headers.get("Authorization", "")
                    if isinstance(auth, str) and auth.lower().startswith("bearer "):
                        return auth.split(" ", 1)[1].strip()
            except Exception:
                continue
        return None

    def _coerce_float(self, value) -> float | None:
        if value is None or isinstance(value, bool):
            return None
        try:
            if isinstance(value, str):
                cleaned = value.replace(",", "").strip()
                if not cleaned:
                    return None
                return float(cleaned)
            if isinstance(value, (int, float)):
                return float(value)
        except Exception:
            return None
        return None

    def _finalize_wallet_snapshot(self, snapshot: dict | None) -> dict | None:
        if not snapshot:
            return None
        balance = snapshot.get("balance")
        if balance is None:
            return None
        return {
            "balance": float(balance),
            "bonus": float(snapshot.get("bonus") or 0.0),
            "coins": float(snapshot.get("coins") or 0.0),
        }

    def _extract_wallet_snapshot_from_logs(self, driver: webdriver.Chrome, network_entries: list[dict]) -> dict | None:
        for entry in network_entries:
            if entry.get("kind") != "response":
                continue
            request_id = entry.get("requestId")
            if not request_id:
                continue
            try:
                body = driver.execute_cdp_cmd("Network.getResponseBody", {"requestId": request_id})
                body_text = body.get("body", "")
                if not body_text:
                    continue
                parsed = json.loads(body_text)
                result = self._extract_wallet_snapshot_from_json(parsed)
                if result is not None:
                    return result
            except Exception:
                continue
        return None

    def _extract_wallet_snapshot_from_json(self, data) -> dict | None:
        if isinstance(data, dict):
            balance_keys = ("balance", "available_balance", "main_balance")
            bonus_keys = ("bonus", "bonus_balance", "bonusBalance")
            coin_keys = ("coins", "coin", "coin_balance", "coinbalance")
            current = {"balance": None, "bonus": 0.0, "coins": 0.0}

            for key in balance_keys:
                if key in data:
                    current["balance"] = self._coerce_float(data[key])
                    if current["balance"] is not None:
                        break

            for key in bonus_keys:
                if key in data:
                    bonus = self._coerce_float(data[key])
                    if bonus is not None:
                        current["bonus"] = bonus
                        break

            for key in coin_keys:
                if key in data:
                    coins = self._coerce_float(data[key])
                    if coins is not None:
                        current["coins"] = coins
                        break

            for value in data.values():
                nested = self._extract_wallet_snapshot_from_json(value)
                if nested is not None:
                    if current["balance"] is None:
                        current["balance"] = nested.get("balance")
                    if not current["bonus"]:
                        current["bonus"] = nested.get("bonus", 0.0)
                    if not current["coins"]:
                        current["coins"] = nested.get("coins", 0.0)
                    if current["balance"] is not None and current["coins"] is not None:
                        break

            return self._finalize_wallet_snapshot(current)

        elif isinstance(data, list):
            for item in data:
                nested = self._extract_wallet_snapshot_from_json(item)
                if nested is not None:
                    return nested

        return None

    def _extract_wallet_snapshot_from_token(self, token: str | None) -> dict | None:
        if not token:
            return None
        parts = token.split(".")
        if len(parts) != 3:
            return None

        try:
            payload = parts[1]
            padding = 4 - (len(payload) % 4)
            if padding != 4:
                payload += "=" * padding
            decoded = base64.urlsafe_b64decode(payload)
            token_data = json.loads(decoded)
            return self._extract_wallet_snapshot_from_json(token_data)
        except Exception:
            return None

    def _extract_wallet_snapshot_from_sportpesa_api(self, driver: webdriver.Chrome) -> dict | None:
        """Fetch the SportPesa /api/wallets/balance endpoint from the logged-in page."""
        try:
            data = driver.execute_async_script(
                """
                var done = arguments[arguments.length - 1];
                fetch('/api/wallets/balance', {credentials: 'include', cache: 'no-store'})
                    .then(function (r) { return r.json(); })
                    .then(function (d) { done(d); })
                    .catch(function () { done(null); });
                """
            )
        except Exception:
            return None
        if not data:
            return None
        return self._extract_wallet_snapshot_from_json(data)

    def _extract_wallet_snapshot_from_page(self, driver: webdriver.Chrome) -> dict | None:
        try:
            script = r"""
            function scanText(text) {
                const normalized = (text || "").replace(/\s+/g, " ").trim();
                const balanceMatch = normalized.match(/(\d[\d,]*\.?\d*)\s*(?:KSH|KES)/i) || normalized.match(/(?:KSH|KES)\s*(\d[\d,]*\.?\d*)/i);
                const coinMatch = normalized.match(/coins?\s*[:\-]?\s*(\d[\d,]*)/i);
                
                return {
                    balance: balanceMatch ? balanceMatch[1].replace(/,/g, "") : null,
                    coins: coinMatch ? coinMatch[1].replace(/,/g, "") : null
                };
            }
            function visible(el) {
                if (!el) return false;
                const s = window.getComputedStyle(el);
                const r = el.getBoundingClientRect();
                return s.display !== 'none' && s.visibility !== 'hidden' &&
                    parseFloat(s.opacity || '1') > 0.05 && r.width > 2 && r.height > 2;
            }
            function scan(doc) {
                const found = { balance: null, coins: null };
                // 1. Target Balance specifically
                const bodyText = (doc.body ? doc.body.innerText : "").replace(/\s+/g, " ");
                const bMatch = bodyText.match(/(\d[\d,]*\.?\d*)\s*(?:KSH|KES)/i) || bodyText.match(/(?:KSH|KES)\s*(\d[\d,]*\.?\d*)/i);
                if (bMatch) found.balance = bMatch[1].replace(/,/g, "");

                // 2. Target Coins specifically - look for elements containing "Coins"
                const elements = doc.querySelectorAll('div, span, b, p, font, strong, a, li');
                for (const el of elements) {
                    if (!visible(el)) continue;
                    const text = (el.innerText || "").trim();
                    if (/^coins?$/i.test(text) || text.toLowerCase().includes("coins")) {
                        // Look at parent or siblings for the number
                        const parent = el.parentElement;
                        const pText = (parent ? parent.innerText : "").replace(/\s+/g, " ");
                        const cMatch = pText.match(/coins?\s*[:\-]?\s*(\d[\d,]*)/i);
                        if (cMatch) {
                            found.coins = cMatch[1].replace(/,/g, "");
                            break;
                        }
                    }
                }
                
                // 3. Last resort: scan all visible elements for any missed coins
                if (!found.coins) {
                    for (const el of elements) {
                        if (!visible(el)) continue;
                        const vals = scanText(el.innerText);
                        if (vals.coins) {
                            found.coins = vals.coins;
                            break;
                        }
                    }
                }

                return found;
            }
            function findWallet() {
                let res = scan(document);
                if (res.balance || res.coins) return res;
                const iframes = document.querySelectorAll('iframe');
                for (const frame of iframes) {
                    try {
                        res = scan(frame.contentDocument || frame.contentWindow.document);
                        if (res.balance || res.coins) return res;
                    } catch (e) {}
                }
                return scanText(document.body ? document.body.innerText : '');
            }
            return findWallet();
            """
            page_wallet = driver.execute_script(script)
            if isinstance(page_wallet, dict):
                snapshot = self._finalize_wallet_snapshot(
                    {
                        "balance": self._coerce_float(page_wallet.get("balance")),
                        "bonus": 0.0,
                        "coins": self._coerce_float(page_wallet.get("coins")) or 0.0,
                    }
                )
                if snapshot is not None:
                    return snapshot

            text = driver.execute_script("return (document.body && document.body.innerText) || '';")
        except Exception:
            return None

        lines = [line.strip() for line in text.splitlines() if line.strip()]
        balance = None
        bonus = 0.0
        coins = 0.0
        for index, line in enumerate(lines):
            lowered = line.lower()
            if "coin" in lowered and not coins:
                # Look for the word "coin" and a number near it
                # Join with next line if needed
                window = " ".join(lines[index:index + 2])
                coin_match = COIN_RE.search(window)
                if coin_match:
                    coins = self._coerce_float(coin_match.group(1)) or 0.0
            if any(key in lowered for key in ("balance", "wallet", "bonus")) and balance is None:
                window = " ".join(lines[index:index + 3])
                matches = BALANCE_RE.findall(window)
                if matches:
                    try:
                        balance = float(matches[0].replace(",", ""))
                        bonus = float(matches[1].replace(",", "")) if len(matches) > 1 else 0.0
                    except Exception:
                        continue
        return self._finalize_wallet_snapshot({"balance": balance, "bonus": bonus, "coins": coins})

    def _persist_routes(self, network_entries: list[dict]) -> None:
        route_map = {"confirmed": {}, "candidates": []}
        for entry in network_entries:
            url = entry.get("url", "")
            if not url.startswith("http"):
                continue
            if "/api/country" in url:
                route_map["confirmed"]["country"] = url
            elif any(key in url.lower() for key in ("login", "auth", "balance", "profile", "deposit", "withdraw", "bonus", "account")):
                route_map["candidates"].append({
                    "kind": entry.get("kind"),
                    "method": entry.get("method"),
                    "status": entry.get("status"),
                    "url": url,
                })

        route_map["candidates"] = sorted(
            route_map["candidates"],
            key=lambda item: (item.get("url", ""), item.get("kind", "")),
        )
        with self._route_file_lock:
            DISCOVERED_ROUTES_PATH.parent.mkdir(parents=True, exist_ok=True)
            DISCOVERED_ROUTES_PATH.write_text(json.dumps(route_map, indent=2), encoding="utf-8")

    def _navigate_to_profile(self, driver: webdriver.Chrome) -> bool:
        """Ensure we are on a page where the balance is visible (header for SportPesa)."""
        try:
            self._dismiss_visible_promos(driver, rounds=1)
            return True
        except Exception:
            return False

    def _get_driver_cookies(self, driver: webdriver.Chrome) -> dict[str, str]:
        """Extract cookies from the Chrome browser for injection into requests.

        The warm_browser preload loads the SportPesa page, which passes Akamai's
        bot-detection challenge and sets session cookies.  Reusing those cookies
        in a plain-requests call makes the API appear to be the same browsing
        session — bypassing the 403/503 challenge pages.
        """
        try:
            return {c["name"]: c["value"] for c in driver.get_cookies() if "name" in c}
        except Exception:
            return {}

    def _api_login(self, phone: str, password: str, timeout: int = 20, retries: int = 3,
                   cookies: dict[str, str] | None = None) -> dict:
        """Log in via the SportPesa JSON API without a browser.

        Returns {"ok": True, "balance": float, "currency": str, "token": str, "raw": dict}
        or {"ok": False, "error": str, "status": int, "body": str}.

        Akamai intermittently returns 403/503 challenge pages, so we retry with
        backoff before giving up and falling back to the browser.
        """
        headers = {
            "User-Agent": "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/137.0.0.0 Mobile Safari/537.36",
            "Accept": "application/json, text/plain, */*",
            "Content-Type": "application/json",
            "Referer": "https://www.ke.sportpesa.com/",
            "Origin": "https://www.ke.sportpesa.com",
            "X-Channel": "web",
        }
        last_err = "unknown error"
        for attempt in range(1, retries + 1):
            try:
                attempt_headers = dict(headers)
                attempt_headers["X-TRACK-ID"] = str(uuid.uuid4())
                # Use a Session so we can inject browser cookies to bypass Akamai
                session = requests.Session()
                if cookies:
                    for name, value in cookies.items():
                        session.cookies.set(name, value, domain=".ke.sportpesa.com")
                resp = session.post(
                    USER_API_LOGIN_URL,
                    json={"usr": phone, "pwd": password},
                    headers=attempt_headers,
                    timeout=timeout,
                )
                try:
                    data = resp.json()
                except Exception:
                    # Challenge / error HTML page -> retry with backoff
                    last_err = f"Non-JSON response (HTTP {resp.status_code})"
                    if attempt < retries:
                        time.sleep(1.5 * attempt)
                    continue
                if resp.status_code != 200:
                    message = data.get("description") or data.get("message") or f"HTTP {resp.status_code}"
                    last_err = message
                    if attempt < retries:
                        time.sleep(1.5 * attempt)
                    continue
                if data.get("balance") is None:
                    return {"ok": False, "error": "No balance in login response", "status": resp.status_code, "body": resp.text[:300]}
                try:
                    balance = float(data.get("balance") or 0)
                except Exception:
                    balance = 0.0
                return {
                    "ok": True,
                    "balance": balance,
                    "bonus": 0.0,
                    "currency": data.get("currency", "KES"),
                    "token": data.get("token", ""),
                    "username": data.get("username", ""),
                    "raw": data,
                }
            except Exception as exc:
                last_err = str(exc)[:200]
                if attempt < retries:
                    time.sleep(1.5 * attempt)
        return {"ok": False, "error": last_err, "status": None, "body": ""}

    def check_single_balance_api(self, phone: str, password: str, gui_callback=None) -> dict:
        """Fast balance check using only the SportPesa login API (no browser)."""
        normalized = self._format_sportsape_login_phone(phone)
        try:
            self._emit(gui_callback, "   Logging in via SportPesa API...")
            result = self._api_login(normalized, password)
            if not result["ok"]:
                return {
                    "status": "error",
                    "phone": phone,
                    "balance": 0,
                    "bonus": 0,
                    "coins": 0,
                    "message": f"API login failed: {result['error']}",
                    "api_used": True,
                }
            balance = result["balance"]
            bonus = result["bonus"]
            return {
                "status": "success",
                "phone": phone,
                "balance": balance,
                "bonus": bonus,
                "coins": 0,
                "total": balance + bonus,
                "message": "Success",
                "currency": result.get("currency", "KES"),
                "api_used": True,
            }
        except Exception as exc:
            if gui_callback:
                gui_callback(f"Error: {str(exc)[:100]}")
            return {
                "status": "error",
                "phone": phone,
                "balance": 0,
                "bonus": 0,
                "coins": 0,
                "message": str(exc)[:100],
                "api_used": True,
            }

    def check_single_balance(self, phone: str, password: str, gui_callback=None, driver=None) -> dict:
        normalized = self._format_sportsape_login_phone(phone)

        # ── Tier 1: Pure API  (fastest, no browser needed) ─────────────────
        try:
            api_result = self._api_login(normalized, password, retries=2)
            if api_result["ok"]:
                self._emit_direct(gui_callback, "   ✅ API login succeeded, reading balance from response...")
                balance = api_result["balance"]
                bonus = api_result["bonus"]
                return {
                    "status": "success",
                    "phone": phone,
                    "balance": balance,
                    "bonus": bonus,
                    "coins": 0,
                    "total": balance + bonus,
                    "message": "Success",
                    "currency": api_result.get("currency", "KES"),
                    "api_used": True,
                }
            self._emit_direct(gui_callback, f"   ⚠️ Tier-1 API blocked ({api_result['error']})")
        except Exception as exc:
            self._emit_direct(gui_callback, f"   ⚠️ Tier-1 API crashed ({str(exc)[:120]})")
            api_result = None

        # ── Tier 2: API with browser cookies  (bypasses Akamai) ──────────
        own_driver = driver is None
        try:
            if not driver:
                driver = self._acquire_driver(gui_callback=gui_callback)
            cookies = self._get_driver_cookies(driver)
            if cookies:
                self._emit_direct(gui_callback, "   🔁 Retrying API with browser session cookies...")
                api_result2 = self._api_login(normalized, password, cookies=cookies)
                if api_result2["ok"]:
                    self._emit_direct(gui_callback, "   ✅ Cookie-backed API login succeeded!")
                    balance = api_result2["balance"]
                    bonus = api_result2["bonus"]
                    return {
                        "status": "success",
                        "phone": phone,
                        "balance": balance,
                        "bonus": bonus,
                        "coins": 0,
                        "total": balance + bonus,
                        "message": "Success",
                        "currency": api_result2.get("currency", "KES"),
                        "api_used": True,
                    }
                self._emit_direct(gui_callback, f"   ⚠️ Cookie-backed API also blocked ({api_result2['error']})")

            # ── Tier 3: Full browser form fill  (most reliable) ───────────
            self._emit_direct(gui_callback, "   🌐 Starting browser form login (most reliable)...")
            driver.get(LOGIN_URL)
            WebDriverWait(driver, 10).until(lambda d: d.execute_script("return document.readyState") != "loading")

            phone_input, password_input = self._wait_for_login_inputs(driver, gui_callback=gui_callback)
            if not phone_input or not password_input:
                return {
                    "status": "error",
                    "phone": phone,
                    "balance": 0,
                    "bonus": 0,
                    "coins": 0,
                    "message": "Could not find SportPesa login inputs",
                }

            self._emit(gui_callback, "   Filling credentials...")
            phone_input.clear()
            phone_input.send_keys(normalized)
            password_input.clear()
            password_input.send_keys(password)
            time.sleep(0.8)

            self._emit(gui_callback, "   Clicking login...")
            clicked = self._click_login_submit(driver)
            login_state = self._wait_for_post_login(driver)
            if login_state == "failed":
                return {
                    "status": "error",
                    "phone": phone,
                    "balance": 0,
                    "bonus": 0,
                    "coins": 0,
                    "message": "Login failed: incorrect phone or password",
                    "clicked_login": clicked,
                    "logout_success": False,
                }
            if login_state == "timeout":
                self._emit(gui_callback, "   Login result unclear, continuing with extraction...")

            self._emit(gui_callback, "   Navigating to Profile...")
            self._navigate_to_profile(driver)
            time.sleep(0.8)

            self._emit(gui_callback, "   Collecting CDP network logs...")
            messages = self._read_performance_messages(driver)
            network_entries = self._collect_network(driver, messages=messages)
            self._persist_routes(network_entries)

            self._emit(gui_callback, "   Inspecting token payload if needed...")
            token = self._extract_token(driver, messages=messages)
            wallet_snapshot = self._extract_wallet_snapshot_from_logs(driver, network_entries)
            if wallet_snapshot is None:
                wallet_snapshot = self._extract_wallet_snapshot_from_token(token)
            if wallet_snapshot is None:
                self._emit(gui_callback, "   Querying SportPesa balance API...")
                wallet_snapshot = self._extract_wallet_snapshot_from_sportpesa_api(driver)
            if wallet_snapshot is None:
                self._emit(gui_callback, "   Falling back to page text wallet extraction...")
                wallet_snapshot = self._extract_wallet_snapshot_from_page(driver)

            logout_success = self._logout_current_session(driver)

            if wallet_snapshot is None:
                return {
                    "status": "error",
                    "phone": phone,
                    "balance": 0,
                    "bonus": 0,
                    "coins": 0,
                    "message": "Logged in or reached site, but no SportPesa wallet data was confirmed",
                    "clicked_login": clicked,
                    "logout_success": logout_success,
                }

            balance = wallet_snapshot["balance"]
            bonus = wallet_snapshot["bonus"]
            coins = wallet_snapshot["coins"]
            return {
                "status": "success",
                "phone": phone,
                "balance": balance,
                "bonus": bonus,
                "coins": coins,
                "total": balance + bonus,
                "message": "Success",
                "clicked_login": clicked,
                "logout_success": logout_success,
            }
        except Exception as exc:
            if gui_callback:
                gui_callback(f"Error: {str(exc)[:100]}")
            return {
                "status": "error",
                "phone": phone,
                "balance": 0,
                "bonus": 0,
                "coins": 0,
                "message": str(exc)[:100],
            }
        finally:
            if driver and own_driver:
                self._reset_driver_state(driver)
                if not self._store_preloaded_driver(driver):
                    self._cleanup_driver(driver)
            elif driver and not own_driver:
                self._reset_driver_state(driver)

    def check_balances(self, phone_list, password, gui_callback=None):
        results = []
        cache_results = {}
        indexed_results = {}

        def process_phone(phone, driver):
            normalized = self._format_sportsape_login_phone(phone)
            result = None
            for attempt in range(2):
                if not self.running:
                    break
                result = self.check_single_balance(normalized, password, gui_callback, driver=driver)
                if result["status"] == "success":
                    break
                if attempt == 0 and self.running:
                    self._emit_direct(gui_callback, f"Retrying {phone}...")
                    time.sleep(1)
            return result

        def worker(worker_id, work_queue):
            worker_results = {}
            driver = None
            try:
                driver = self._acquire_driver(gui_callback=gui_callback)
                self._emit_direct(gui_callback, f"⚙️ Worker {worker_id} ready")
                while self.running:
                    try:
                        index, phone = work_queue.get_nowait()
                    except Empty:
                        break
                    result = process_phone(phone, driver)
                    if result is None:
                        break
                    worker_results[index] = (phone, result)
                    if gui_callback:
                        if result["status"] == "success":
                            self._emit_direct(
                                gui_callback,
                                    f"Checking: {phone} Balance: KES {result['balance']:,.2f} | Bonus: KES {result.get('bonus', 0):,.2f}",
                            )
                        else:
                            self._emit_direct(gui_callback, f"Checking: {phone} Failed: {result['message']}")
            except Exception as exc:
                self._emit_direct(gui_callback, f"⚠️ Worker {worker_id} error: {str(exc)[:80]}")
            finally:
                if driver:
                    self._reset_driver_state(driver)
                    if not self._store_preloaded_driver(driver):
                        self._cleanup_driver(driver)
            return worker_results

        work_items = [(index, phone) for index, phone in enumerate(phone_list, start=1)]
        worker_count = min(self.max_parallel_workers, len(work_items)) if work_items else 0

        if worker_count <= 1:
            driver = None
            try:
                driver = self._acquire_driver(gui_callback=gui_callback)
                for index, phone in work_items:
                    if not self.running:
                        break
                    result = process_phone(phone, driver)
                    if result is None:
                        break
                    indexed_results[index] = (phone, result)
                    if gui_callback:
                        if result["status"] == "success":
                            self._emit_direct(
                                gui_callback,
                                    f"Checking: {phone} Balance: KES {result['balance']:,.2f} | Bonus: KES {result.get('bonus', 0):,.2f}",
                            )
                        else:
                            self._emit_direct(gui_callback, f"Checking: {phone} Failed: {result['message']}")
            finally:
                if driver:
                    self._reset_driver_state(driver)
                    if not self._store_preloaded_driver(driver):
                        self._cleanup_driver(driver)
        else:
            self._emit_direct(gui_callback, f"⚡ SAFE BATCH MODE: {worker_count} parallel workers")
            self.warm_browser_pool(worker_count, gui_callback=gui_callback)
            work_queue = Queue()
            for item in work_items:
                work_queue.put(item)
            with ThreadPoolExecutor(max_workers=worker_count) as executor:
                futures = [executor.submit(worker, worker_id, work_queue) for worker_id in range(1, worker_count + 1)]
                for future in as_completed(futures):
                    for index, value in future.result().items():
                        indexed_results[index] = value

        for index in sorted(indexed_results):
            phone, result = indexed_results[index]
            results.append(result)
            cache_results[phone] = result

        with self._balance_cache_lock:
            self.balance_cache["timestamp"] = time.time()
            self.balance_cache["results"] = cache_results

        # Emit total balance summary to GUI
        if gui_callback:
            total_bal = sum(r["balance"] for r in results if r["status"] == "success")
            total_bonus = sum(r["bonus"] for r in results if r["status"] == "success")
            success_count = sum(1 for r in results if r["status"] == "success")
            
            gui_callback("-" * 30)
            gui_callback(f"🏆 FINAL SUMMARY: {success_count}/{len(results)} Accounts Successful")
            gui_callback(f"💰 TOTAL BALANCE: KES {total_bal:,.2f}")
            gui_callback(f"🎁 TOTAL BONUS: KES {total_bonus:,.2f}")
            gui_callback("-" * 31) # Slightly different length to avoid GUI de-duplication

        self.generate_balance_report(results, gui_callback)
        self.generate_csv_report(results, gui_callback)
        
        if gui_callback:
            try:
                import winsound
                winsound.Beep(1000, 300)
            except Exception:
                pass
        
        return results

    def generate_csv_report(self, results, gui_callback=None):
        timestamp = datetime.now().strftime("%Y%m%d_%H%M")
        filename = f"balance_report_{timestamp}.csv"
        try:
            with open(filename, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow(["Phone", "Status", "Balance", "Bonus", "Message"])
                for item in results:
                    writer.writerow([
                        item["phone"],
                        item["status"],
                        f"{item['balance']:.2f}",
                        f"{item.get('bonus', 0):.2f}",
                        item["message"]
                    ])
            if gui_callback:
                gui_callback(f"CSV Report saved: {filename}")
        except Exception:
            pass

    def generate_balance_report(self, results, gui_callback=None):
        timestamp = datetime.now().strftime("%Y%m%d_%H%M")
        filename = f"balance_report_{timestamp}.txt"
        total_balance = sum(item["balance"] for item in results if item["status"] == "success")
        total_bonus = sum(item.get("bonus", 0) for item in results if item["status"] == "success")
        success_count = sum(1 for item in results if item["status"] == "success")
        failed_count = len(results) - success_count

        lines = [
            "=" * 80,
            "SPORTSAPE V2 BALANCE REPORT",
            "=" * 80,
            f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"Total Accounts: {len(results)}",
            f"Successful: {success_count}",
            f"Failed: {failed_count}",
            "",
            f"Total Balance: KES {total_balance:,.2f}",
            f"Total Bonus: KES {total_bonus:,.2f}",
            "",
        ]

        for item in results:
            if item["status"] == "success":
                lines.append(
                    f"{item['phone']}: Balance KES {item['balance']:,.2f} | Bonus KES {item.get('bonus', 0):,.2f}"
                )
            else:
                lines.append(f"{item['phone']}: FAILED - {item['message']}")

        Path(filename).write_text("\n".join(lines), encoding="utf-8")
        if gui_callback:
            gui_callback(f"Report saved: {filename}")

    def open_report_file(self, filepath):
        try:
            if sys.platform == "win32":
                os.startfile(filepath)
            elif sys.platform == "darwin":
                subprocess.run(["open", filepath], check=False)
            else:
                subprocess.run(["xdg-open", filepath], check=False)
        except Exception:
            pass

    def get_odi_key_and_cookie(self):
        return self.warm_browser()

    def change_bookie_url(self, new_url):
        self.base_url = new_url
        return True

    def login_with_balance(self, phone, password):
        return self.check_single_balance(self.normalize_phone(phone), password)

    def withdraw_funds(self, _phone, _password, _amount, _callback=None):
        return {"status": "error", "message": "Withdraw automation is not configured for SportPesa yet"}

    def check_account_balances(self, phone_list, password, gui_callback=None):
        results = self.check_balances(phone_list, password, gui_callback)
        ready = [item["phone"] for item in results if item["status"] == "success" and item["balance"] > 0]
        insufficient = [item["phone"] for item in results if item["status"] == "success" and item["balance"] <= 0]
        inactive = [item["phone"] for item in results if item["status"] != "success"]
        return ready, insufficient, inactive

    def place_single_bet_with_booking_code(self, *_args, **_kwargs):
        return {"status": "error", "message": "Bet placement is not configured for SportPesa yet"}

    def place_bets_with_booking_code(self, *_args, **_kwargs):
        return {"status": "error", "message": "Bet placement is not configured for SportPesa yet"}

    def roll_over_accounts(self, *_args, **_kwargs):
        return {"status": "error", "message": "Rollover is not configured for SportPesa yet"}

    def claim_bonuses_for_accounts(self, *_args, **_kwargs):
        return {"status": "error", "message": "Bonus claiming is not configured for SportPesa yet"}

    def batch_withdraw(self, *_args, **_kwargs):
        return {"status": "error", "message": "Batch withdraw is not configured for SportPesa yet"}

    def odileague_supa5_automation(self, *_args, **_kwargs):
        return {"status": "error", "message": "Supa5 automation is not configured for SportPesa yet"}

    def run_odileague_bonus(self, *_args, **_kwargs):
        return {"status": "error", "message": "Bonus automation is not configured for SportPesa yet"}

    def extract_tokens_for_accounts(self, *_args, **_kwargs):
        return False

    def load_tokens(self):
        return False

    def close_all_browsers(self):
        with self._driver_lock:
            drivers = list(self._preloaded_drivers)
            self._preloaded_drivers = []
        for driver in drivers:
            self._cleanup_driver(driver)
        with self._active_drivers_lock:
            active_drivers = list(self._active_drivers)
        for active_driver in active_drivers:
            if active_driver not in drivers:
                self._cleanup_driver(active_driver)
        if self.selenium_driver and self.selenium_driver not in drivers:
            self._cleanup_driver(self.selenium_driver)
        return None

    # ── Cookie-bridged API access (bypasses Akamai) ──────────────────────

    def _get_cookie_session(self, phone: str, password: str, gui_callback=None) -> tuple:
        """Login via browser, extract cookies, return a requests.Session.

        Returns (session, driver) or (None, None) on failure.
        The caller should call _cleanup_driver when done with the driver.
        """
        from selenium.webdriver.support.ui import WebDriverWait
        try:
            self._emit_direct(gui_callback, "Starting Akamai handshake (browser login)...")
            driver = self._build_driver(force_visible=False)
            # Login
            driver.get(LOGIN_URL)
            WebDriverWait(driver, 20).until(lambda d: d.execute_script("return document.readyState") != "loading")
            time.sleep(2)
            normalized = self._format_sportsape_login_phone(phone)
            pi, pw = self._wait_for_login_inputs(driver, gui_callback=gui_callback)
            if not pi or not pw:
                try: driver.quit()
                except: pass
                return None, None
            pi.clear(); pi.send_keys(normalized)
            pw.clear(); pw.send_keys(password)
            self._click_login_submit(driver)
            if self._wait_for_post_login(driver) != "ok":
                try: driver.quit()
                except: pass
                return None, None

            self._emit_direct(gui_callback, "Logged in. Extracting cookies...")
            # Extract all cookies into a Session
            session = requests.Session()
            session.headers.update({
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/148.0.0.0 Safari/537.36",
                "Origin": SITE_ORIGIN,
                "Referer": SITE_ORIGIN + "/",
                "Accept": "application/json, text/plain, */*",
            })
            for c in driver.get_cookies():
                session.cookies.set(c["name"], c["value"], domain=c.get("domain", ".ke.sportpesa.com"))
            self._emit_direct(gui_callback, f"Cookie session ready ({len(driver.get_cookies())} cookies)")
            return session, driver
        except Exception as e:
            self._emit_direct(gui_callback, f"Cookie session failed: {str(e)[:100]}")
            return None, None

    def get_transactions(self, phone: str, password: str, gui_callback=None) -> dict:
        """Get user transaction history via cookie-bridged API."""
        session, driver = self._get_cookie_session(phone, password, gui_callback)
        if not session:
            return {"status": "error", "message": "Could not establish cookie session"}
        try:
            resp = session.get(f"{SITE_ORIGIN}/api/users/transactions", timeout=15)
            if resp.status_code == 200 and "json" in resp.headers.get("Content-Type", ""):
                data = resp.json()
                self._emit_direct(gui_callback, f"Transactions: {len(data) if isinstance(data, list) else type(data).__name__}")
                return {"status": "success", "data": data}
            return {"status": "error", "message": f"HTTP {resp.status_code}: {resp.text[:200]}"}
        except Exception as e:
            return {"status": "error", "message": str(e)[:150]}
        finally:
            if driver: self._cleanup_driver(driver)

    def get_bet_history(self, phone: str, password: str, gui_callback=None) -> dict:
        """Get bet history via cookie-bridged API."""
        session, driver = self._get_cookie_session(phone, password, gui_callback)
        if not session:
            return {"status": "error", "message": "Could not establish cookie session"}
        try:
            resp = session.get(f"{SITE_ORIGIN}/api/users/bets", timeout=15)
            if resp.status_code == 200 and "json" in resp.headers.get("Content-Type", ""):
                data = resp.json()
                self._emit_direct(gui_callback, f"Bets: {len(data) if isinstance(data, list) else type(data).__name__}")
                return {"status": "success", "data": data}
            return {"status": "error", "message": f"HTTP {resp.status_code}: {resp.text[:200]}"}
        except Exception as e:
            return {"status": "error", "message": str(e)[:150]}
        finally:
            if driver: self._cleanup_driver(driver)

    def get_wallet_detail(self, phone: str, password: str, gui_callback=None) -> dict:
        """Get full wallet balance (sportsbook + casino) via cookie-bridged API."""
        session, driver = self._get_cookie_session(phone, password, gui_callback)
        if not session:
            return {"status": "error", "message": "Could not establish cookie session"}
        try:
            resp = session.get(f"{SITE_ORIGIN}/api/wallets/balance", timeout=15)
            if resp.status_code == 200 and "json" in resp.headers.get("Content-Type", ""):
                data = resp.json()
                sb = data.get("sportsbook", {})
                casino = data.get("casino", {})
                self._emit_direct(gui_callback,
                    f"Wallet: Sportsbook KES {sb.get('balance','?')} (bonus {sb.get('bonusBalance','?')}) | "
                    f"Casino KES {casino.get('balance','?')} (bonus {casino.get('bonusBalance','?')})")
                return {"status": "success", "data": data}
            return {"status": "error", "message": f"HTTP {resp.status_code}: {resp.text[:200]}"}
        except Exception as e:
            return {"status": "error", "message": str(e)[:150]}
        finally:
            if driver: self._cleanup_driver(driver)

    def get_casino_games(self, gui_callback=None) -> dict:
        """Get all casino game names and IDs (no login needed)."""
        try:
            resp = requests.get(
                "https://gpm-svc.ke.sportpesa.com/api/v1/games/platform/android",
                headers={"User-Agent": "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36",
                         "Origin": "https://casino-frontend.ke.sportpesa.com"}, timeout=20)
            if resp.status_code == 200:
                games = resp.json().get("games", {})
                self._emit_direct(gui_callback, f"Casino games: {len(games)} total")
                return {"status": "success", "count": len(games), "games": games}
            return {"status": "error", "message": f"HTTP {resp.status_code}"}
        except Exception as e:
            return {"status": "error", "message": str(e)[:150]}

    # ── Withdraw Automation ──────────────────────────────────────────────

    def withdraw_funds_browser(self, phone_list, password, amount, gui_callback=None):
        """Withdraw *amount* KES from each account in *phone_list* via browser."""
        results = []
        self._emit_direct(gui_callback, f"WITHDRAW: {len(phone_list)} accounts x KES {amount:,.0f}")

        driver = None
        try:
            driver = self._acquire_driver(gui_callback=gui_callback)
            for idx, phone in enumerate(phone_list, 1):
                if not self.running:
                    break
                normalized = self._format_sportsape_login_phone(phone)
                self._emit_direct(gui_callback, f"[{idx}/{len(phone_list)}] {phone} - logging in...")

                # Login
                driver.get(LOGIN_URL)
                WebDriverWait(driver, 15).until(lambda d: d.execute_script("return document.readyState") != "loading")
                time.sleep(1)
                pi, pw = self._wait_for_login_inputs(driver, gui_callback=gui_callback)
                if not pi or not pw:
                    results.append({"phone": phone, "status": "error", "message": "Login form not found"})
                    continue
                pi.clear(); pi.send_keys(normalized)
                pw.clear(); pw.send_keys(password)
                self._click_login_submit(driver)
                if self._wait_for_post_login(driver) != "ok":
                    results.append({"phone": phone, "status": "error", "message": "Login failed"})
                    continue

                # Navigate to withdraw page
                self._emit_direct(gui_callback, f"  Opening withdraw page...")
                driver.get(f"{SITE_ORIGIN}/en/withdraw")
                WebDriverWait(driver, 20).until(lambda d: d.execute_script("return document.readyState") != "loading")
                time.sleep(4)

                # Try to find and fill the withdraw form
                withdrew = False
                try:
                    # Find amount input
                    amount_inputs = driver.find_elements(By.CSS_SELECTOR, "input[type='number'], input[type='text'], input")
                    for inp in amount_inputs:
                        try:
                            parent_text = (inp.find_element(By.XPATH, "..").text or "").lower()
                            placeholder = (inp.get_attribute("placeholder") or "").lower()
                            name = (inp.get_attribute("name") or inp.get_attribute("id") or "").lower()
                            if any(k in parent_text + placeholder + name for k in ["amount", "kes", "withdraw"]):
                                inp.clear()
                                inp.send_keys(str(int(amount)))
                                self._emit_direct(gui_callback, f"  Amount set: KES {amount:,.0f}")
                                # Find submit button
                                for btn in driver.find_elements(By.CSS_SELECTOR, "button, input[type='submit']"):
                                    try:
                                        t = (btn.text or btn.get_attribute("value") or "").lower()
                                        if "withdraw" in t or "submit" in t or "confirm" in t:
                                            btn.click()
                                            withdrew = True
                                            self._emit_direct(gui_callback, f"  Withdraw submitted!")
                                            break
                                    except: pass
                                break
                        except: pass
                except Exception as e:
                    self._emit_direct(gui_callback, f"  Form error: {str(e)[:80]}")

                if not withdrew:
                    self._emit_direct(gui_callback, f"  Could not find withdraw form. Dumping page...")
                    try:
                        body = driver.execute_script("return document.body.innerText.substring(0,400)")
                        self._emit_direct(gui_callback, f"  Page: {body}")
                    except: pass

                # Logout
                self._logout_current_session(driver)
                results.append({"phone": phone, "status": "success" if withdrew else "error",
                                "message": "Withdrawn" if withdrew else "Form not found"})

            # Summary
            success = sum(1 for r in results if r["status"] == "success")
            self._emit_direct(gui_callback, f"DONE: {success}/{len(results)} withdrawals attempted")
            return results
        except Exception as e:
            self._emit_direct(gui_callback, f"Withdraw error: {str(e)[:120]}")
            return results
        finally:
            if driver:
                self._reset_driver_state(driver)
                self._store_preloaded_driver(driver)
        self._emit_direct(gui_callback, "Looking for game controls...")

        # Dismiss Buckle Up modal
        self._emit_direct(gui_callback, "Dismissing modals...")
        time.sleep(2)
        for attempt_x in range(20):
            try:
                closed = driver.execute_script("""
                    var btns = document.querySelectorAll('button,a,div,span');
                    for (var i = 0; i < btns.length; i++) {
                        var t = (btns[i].innerText || btns[i].textContent || '').trim();
                        if (t === 'X' || t === '\u00d7') { btns[i].click(); return 'clicked-X'; }
                        if (t === 'close') { btns[i].click(); return 'clicked-close'; } 
                    }
                    return 'no-modal';
                """)
                if 'no-modal' in (closed or ''): break
                time.sleep(0.5)
            except: pass
        driver.execute_script("var ovs=document.querySelectorAll('[class*=\"overlay\"],[class*=\"modal\"]');for(var i=0;i<ovs.length;i++)ovs[i].display='none'")

        def _find_btn(texts, timeout=10):
            deadline = time.time() + timeout
            while time.time() < deadline:
                for b in driver.find_elements(By.TAG_NAME, "button"):
                    try:
                        t = (b.text or "").strip().lower()
                        if any(x in t for x in texts) and b.is_displayed() and b.is_enabled():
                            return b
                    except: pass
                time.sleep(0.3)
            return None

        def _find_input(near, timeout=8):
            deadline = time.time() + timeout
            while time.time() < deadline:
                for inp in driver.find_elements(By.CSS_SELECTOR, "input"):
                    try:
                        if not inp.is_displayed() or not inp.is_enabled(): continue
                        tp = inp.get_attribute("type") or "text"
                        if tp == "hidden": continue
                        p = inp.find_element(By.XPATH, "..")
                        if any(t in (p.text or "").lower() for t in near):
                            return inp
                    except: pass
                time.sleep(0.3)
            return None

        # Set stake
        stake_inp = _find_input(["stake", "kes", "bet"], timeout=10)
        if not stake_inp:
            body = driver.execute_script("return (document.body||document.documentElement).innerText||''")
            self._emit_direct(gui_callback, f"No stake input. Body ({len(body)}): {body[:300]}")
            return {"status": "error", "message": "Stake input not found - is game loaded?"}
        driver.execute_script("arguments[0].focus(); arguments[0].select();", stake_inp)
        stake_inp.send_keys(str(int(stake)))
        self._emit_direct(gui_callback, f"Stake = KES {stake:.0f}")

        # Auto toggle OFF -> AUTO
        for el in driver.find_elements(By.CSS_SELECTOR, "button, [role='switch']"):
            try:
                if (el.text or "").strip().lower() == "off":
                    el.click(); self._emit_direct(gui_callback, "OFF -> AUTO"); time.sleep(0.3)
                    break
            except: pass

        # Auto Cashout
        ac_btn = _find_btn(["auto cashout", "auto cash"], timeout=5)
        if ac_btn: ac_btn.click(); time.sleep(0.3)
        ac_inp = _find_input(["auto", "cash", "multiplier", "payout"], timeout=5)
        if ac_inp:
            driver.execute_script("arguments[0].focus(); arguments[0].select();", ac_inp)
            ac_inp.send_keys(str(multiplier))
        self._emit_direct(gui_callback, f"Auto-cashout = {multiplier}x")

        # Bet loop
        bets = 0
        for i in range(rounds):
            play = _find_btn(["play"], timeout=20)
            if play:
                play.click(); bets += 1
                self._emit_direct(gui_callback, f"Bet {bets}/{rounds}")
                time.sleep(4)
        self._emit_direct(gui_callback, f"DONE: {bets} bets")
        return {"status": "success", "bets_placed": bets}

    def run_taxi_free_bet_loop(self, phone: str, password: str, stake: float = 15,
                                multiplier: float = 1.01, rounds: int = 15,
                                visible: bool = True, gui_callback=None) -> dict:
        """Auto-bet Taxi Ride Deluxe: login → casino → launch game → place bets.

        Places *rounds* bets of *stake* KES at *multiplier* auto-cashout,
        then optionally plays the resulting free rounds.
        """
        self._emit_direct(gui_callback, f"TAXI AUTO-BET: {rounds} rounds, KES {stake}, {multiplier}x")

        normalized = self._format_sportsape_login_phone(phone)
        api = self._api_login(normalized, password)
        if api["ok"]:
            self._emit_direct(gui_callback, f"Balance: KES {api['balance']:,.2f}")

        driver = None
        try:
            driver = self._acquire_driver(gui_callback=gui_callback)

            # ---- LOGIN (football page → login form) ----
            driver.get(LOGIN_URL)
            WebDriverWait(driver, 15).until(lambda d: d.execute_script("return document.readyState") != "loading")
            time.sleep(1)
            pi, pw = self._wait_for_login_inputs(driver, gui_callback=gui_callback)
            if not pi or not pw:
                return {"status": "error", "message": "Login form not found"}
            pi.clear(); pi.send_keys(normalized)
            pw.clear(); pw.send_keys(password)
            time.sleep(0.5)
            self._click_login_submit(driver)
            if self._wait_for_post_login(driver) != "ok":
                return {"status": "error", "message": "Login failed"}

            self._emit_direct(gui_callback, "Logged in. Opening casino...")

            # ---- CASINO ----
            driver.get(SITE_ORIGIN + "/en/casino")
            WebDriverWait(driver, 25).until(lambda d: d.execute_script("return document.readyState") != "loading")
            time.sleep(5)

            for f in driver.find_elements(By.TAG_NAME, "iframe"):
                if "casino" in (f.get_attribute("src") or "").lower():
                    driver.switch_to.frame(f)
                    self._emit_direct(gui_callback, "Switched to casino iframe")
                    break

            # Wait for casino SPA to render game cards
            self._emit_direct(gui_callback, "Waiting for casino games...")
            for attempt in range(20):
                time.sleep(3)
                body = driver.execute_script("return document.body.innerText.length")
                play = driver.execute_script("return document.querySelector('button') != null && document.querySelector('button').innerText.indexOf('Play') >= 0")
                if play and body > 800:
                    self._emit_direct(gui_callback, f"  Games loaded (body={body})")
                    break
                if attempt % 5 == 0:
                    self._emit_direct(gui_callback, f"  waiting... body={body}")

            # ---- FIND AND HOVER TAXI CARD, THEN CLICK PLAY ----
            self._emit_direct(gui_callback, "Finding Taxi Ride Deluxe...")
            card = driver.find_element(By.ID, "105762")
            driver.execute_script("arguments[0].scrollIntoView({block:'center'});", card)
            time.sleep(0.5)

            # HOVER over the card to reveal the Play overlay button
            from selenium.webdriver.common.action_chains import ActionChains
            ActionChains(driver).move_to_element(card).perform()
            self._emit_direct(gui_callback, "Hovering over Taxi card...")
            time.sleep(1.5)

            # Now find and click the Play overlay button
            play_btn = None
            for attempt2 in range(5):
                for btn in card.find_elements(By.TAG_NAME, "button"):
                    if btn.text.strip().lower() == "play":
                        play_btn = btn
                        break
                if play_btn:
                    break
                time.sleep(0.5)
            if not play_btn:
                # Try finding Play button by CSS selector
                for sel in ["button:has-text('Play')", "button", "a"]:
                    try:
                        btns = card.find_elements(By.CSS_SELECTOR, sel)
                        if isinstance(btns, list):
                            for b in btns:
                                if b.text.strip().lower() == "play":
                                    play_btn = b; break
                        if play_btn: break
                    except: pass
            if not play_btn:
                self._emit_direct(gui_callback, f"Play button not found. Card buttons: {[b.text for b in card.find_elements(By.TAG_NAME, 'button')]}")
                return {"status": "error", "message": "Play button not found"}
            play_btn.click()
            self._emit_direct(gui_callback, "Clicked Play on Taxi Ride Deluxe")
            time.sleep(2)

            # Game loads IN the same page (SPA view), wait for game elements
            # The game container might be a canvas, iframe, or div with class game-container
            self._emit_direct(gui_callback, "Waiting for game to load...")
            for attempt3 in range(20):
                time.sleep(2)
                has_game = driver.execute_script("""
                    return !!(
                        document.querySelector('canvas') ||
                        document.querySelector('iframe[src*=\"splitthepot\"]') ||
                        document.querySelector('.game-container') ||
                        document.querySelector('[class*=\"game\"] canvas') ||
                        document.querySelector('[class*=\"crash\"]')
                    );
                """)
                if has_game:
                    self._emit_direct(gui_callback, "Game loaded!")
                    break
                if attempt3 % 4 == 0:
                    body = driver.execute_script("return document.body.innerText.length")
                    self._emit_direct(gui_callback, f"  waiting for game... body={body}")

            # ---- DISMISS "Buckle Up" MODAL ----
            self._emit_direct(gui_callback, "Dismissing 'Buckle Up' modal...")
            time.sleep(3)
            # Click the X close button
            for attempt_x in range(10):
                try:
                    closed = driver.execute_script("""
                        var btns = document.querySelectorAll('button,a,div,span,[role=\"button\"]');
                        for (var i = 0; i < btns.length; i++) {
                            var t = (btns[i].innerText || btns[i].textContent || '').trim().toLowerCase();
                            var cls = (btns[i].className || '').toLowerCase();
                            // Look for close/X buttons
                            if (t === 'x' || t === '\u00d7' || t === 'close' ||
                                cls.indexOf('close') >= 0 || cls.indexOf('dismiss') >= 0) {
                                btns[i].click();
                                return 'clicked-X';
                            }
                        }
                        // Try to click overlay backdrop or find modal close
                        var modals = document.querySelectorAll('[class*=\"modal\"],[class*=\"overlay\"],[class*=\"popup\"],[class*=\"dialog\"]');
                        for (var j = 0; j < modals.length; j++) {
                            if (modals[j].offsetHeight > 0) {
                                // Find close button inside modal
                                var closeBtns = modals[j].querySelectorAll('button,a,[role=\"button\"]');
                                for (var k = 0; k < closeBtns.length; k++) {
                                    var ct = (closeBtns[k].innerText || '').trim().toLowerCase();
                                    if (ct === 'x' || ct === 'close' || ct === '\u00d7') {
                                        closeBtns[k].click();
                                        return 'clicked-modal-X';
                                    }
                                }
                                // Try clicking overlay itself
                                modals[j].style.display = 'none';
                                return 'hid-modal';
                            }
                        }
                        return 'no-modal-found';
                    """)
                    self._emit_direct(gui_callback, f"  Modal: {closed}")
                    if closed and 'no-modal' not in closed:
                        time.sleep(1)
                    else:
                        break
                except Exception:
                    time.sleep(0.5)
            driver.execute_script("""
                // Force-remove any remaining overlays
                var ovs = document.querySelectorAll('[class*=\"overlay\"],[class*=\"modal\"],[class*=\"popup\"]');
                for (var i = 0; i < ovs.length; i++) { ovs[i].style.display = 'none'; ovs[i].remove(); }
            """)
            self._emit_direct(gui_callback, "Modal dismissed")

            # ---- GAME CONTROL FINDERS ----
            def _find_btn(texts, timeout=10):
                deadline = time.time() + timeout
                while time.time() < deadline:
                    for b in driver.find_elements(By.TAG_NAME, "button"):
                        try:
                            t = (b.text or "").strip().lower()
                            if any(x in t for x in texts) and b.is_displayed() and b.is_enabled():
                                return b
                        except: pass
                    time.sleep(0.4)
                return None

            def _find_input(near_texts, timeout=8):
                deadline = time.time() + timeout
                while time.time() < deadline:
                    for inp in driver.find_elements(By.CSS_SELECTOR, "input"):
                        try:
                            tp = inp.get_attribute("type") or "text"
                            if tp == "hidden": continue
                            if not inp.is_displayed() or not inp.is_enabled(): continue
                            p = inp.find_element(By.XPATH, "..")
                            pt = (p.text or "").lower()
                            if any(t in pt for t in near_texts):
                                return inp
                        except: pass
                    time.sleep(0.4)
                return None

            # ---- SET STAKE 15 KES ----
            stake_inp = _find_input(["stake", "kes", "bet amount"], timeout=15)
            if not stake_inp:
                body = driver.execute_script("return (document.body||document.documentElement).innerText||''")
                self._emit_direct(gui_callback, f"No stake input. Body ({len(body)}): {body[:300]}")
                return {"status": "error", "message": "Stake input not found"}
            driver.execute_script("arguments[0].focus(); arguments[0].select();", stake_inp)
            stake_inp.send_keys(str(int(stake)))
            self._emit_direct(gui_callback, f"Stake set to KES {stake:.0f}")

            # ---- SWITCH AUTO MODE ON (OFF -> AUTO) ----
            time.sleep(0.5)
            auto_toggled = False
            for el in driver.find_elements(By.CSS_SELECTOR, "button, [role='switch'], .switch, .toggle, input[type='checkbox']"):
                try:
                    t = (el.text or el.get_attribute("aria-label") or "").lower()
                    if t == "off":
                        el.click(); auto_toggled = True
                        self._emit_direct(gui_callback, "Switched OFF -> AUTO")
                        time.sleep(0.4)
                        break
                except: pass
            if not auto_toggled:
                self._emit_direct(gui_callback, "AUTO toggle not found — may already be ON")

            # ---- SET AUTO-CASHOUT 1.01 ----
            ac_btn = _find_btn(["auto cashout", "auto cash"], timeout=5)
            if ac_btn:
                ac_btn.click()
                self._emit_direct(gui_callback, "Clicked Auto Cashout")
                time.sleep(0.5)
            ac_inp = _find_input(["auto", "cash", "multiplier", "payout"], timeout=5)
            if ac_inp:
                driver.execute_script("arguments[0].focus(); arguments[0].select();", ac_inp)
                ac_inp.send_keys(str(multiplier))
                self._emit_direct(gui_callback, f"Auto-cashout set to {multiplier}x")

            # ---- BETTING LOOP: 15 rounds of 15 KES at 1.01x ----
            bets_placed = 0
            self._emit_direct(gui_callback, f"Placing {rounds} bets...")
            for i in range(rounds):
                # Wait for PLAY during countdown ("Starts In")
                play_btn = _find_btn(["play", "bet"], timeout=20)
                if play_btn:
                    play_btn.click()
                    bets_placed += 1
                    self._emit_direct(gui_callback, f"  Bet {bets_placed}/{rounds} placed")
                    # At 1.01x auto-cashout, round completes near-instantly
                    time.sleep(4)
                else:
                    self._emit_direct(gui_callback, f"  Round {i+1}: PLAY not ready, waiting...")
                    time.sleep(6)
                    play_btn2 = _find_btn(["play", "bet"], timeout=10)
                    if play_btn2:
                        play_btn2.click(); bets_placed += 1
                        self._emit_direct(gui_callback, f"  Bet {bets_placed}/{rounds} placed (retry)")
                        time.sleep(4)

            self._emit_direct(gui_callback, f"DONE: {bets_placed}/{rounds} bets placed")
            # Check "Your Session" for count
            session_text = driver.execute_script("""
                var el = document.querySelector('[class*=\"session\"], [class*=\"Session\"]');
                return el ? el.innerText : 'no session panel';
            """)
            self._emit_direct(gui_callback, f"Session: {session_text[:200]}")
            return {"status": "success", "bets_placed": bets_placed}

        except Exception as e:
            self._emit_direct(gui_callback, f"Taxi error: {str(e)[:120]}")
            return {"status": "error", "message": str(e)[:120]}
        finally:
            if driver and not visible:
                self._reset_driver_state(driver)
                self._store_preloaded_driver(driver)
