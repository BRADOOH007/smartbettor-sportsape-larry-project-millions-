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
from selenium.webdriver.common.keys import Keys
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

    # Serializes logins across the 24/7 engine, withdrawals and deposits so the
    # site never sees two simultaneous logins from this tool (throttle/CAPTCHA safety).
    _login_lock = threading.Lock()

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
        self._jackpot_lock = threading.Lock()
        self._jackpot_next_scan = 0.0
        self._jackpot_state = None
        self._jackpot_cadence = 1500.0
        self._engine_busy = False
        self._last_crawled_games = []
        self.JACKPOT_PAGE_URL = "https://www.ke.sportpesa.com/en/mega-jackpot-pro"

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

    def _build_driver(self, gui_callback=None, force_visible=False, mobile=False,
                      headless=None, capture_perf=True, minimize=False) -> webdriver.Chrome:
        options = Options()
        options.page_load_strategy = 'normal'
        use_headless = self.headless if headless is None else bool(headless)
        if use_headless:
            options.add_argument("--headless=new")
        if mobile:
            options.add_argument("--window-size=430,932")
        else:
            options.add_argument("--window-size=1280,800")
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
        options.add_argument("--mute-audio")
        options.add_argument("--no-first-run")
        options.add_argument("--no-default-browser-check")
        if mobile or (not force_visible and not use_headless):
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
        if capture_perf:
            options.set_capability("goog:loggingPrefs", {"performance": "ALL", "browser": "ALL"})
        if minimize and not use_headless:
            options.add_argument("--start-minimized")

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
            if capture_perf:
                driver.execute_cdp_cmd("Network.enable", {})
            if minimize and not use_headless:
                try:
                    driver.minimize_window()
                except Exception:
                    pass
            driver._sportsape_temp_profile = temp_profile  # type: ignore[attr-defined]
            return driver
        except Exception as e:
            self._emit_direct(gui_callback, f"   ❌ Browser launch failed: {str(e)[:50]}")
            # Cleanup profile if driver creation fails
            if os.path.exists(temp_profile):
                shutil.rmtree(temp_profile, ignore_errors=True)
            raise e

    def _safe_get(self, driver, url: str, attempts: int = 3) -> None:
        """Navigate with a generous page-load timeout, retrying transient renderer timeouts."""
        last = None
        driver.set_page_load_timeout(45)
        for i in range(attempts):
            try:
                driver.get(url)
                return
            except Exception as exc:  # retry transient "Timed out receiving message from renderer"
                last = exc
                self._emit_direct(None, f"   ⏳ retry navigating to page ({i + 1}/{attempts})")
                time.sleep(2)
        raise last

    def _emit_direct(self, gui_callback, message: str) -> None:
        """Internal emit that bypasses the verbose check for critical diagnostics"""
        if gui_callback:
            with self._gui_lock:
                gui_callback(message)


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
                with self._login_lock:
                    driver.get(LOGIN_URL)
                    WebDriverWait(driver, 30).until(lambda d: d.execute_script("return document.readyState") != "loading")
                    time.sleep(1)
                    pi, pw = self._wait_for_login_inputs(driver, gui_callback=gui_callback, timeout=30)
                    if not pi or not pw:
                        results.append({"phone": phone, "status": "error", "message": "Login form not found"})
                        continue
                    pi.clear(); pi.send_keys(normalized)
                    pw.clear(); pw.send_keys(password)
                    self._click_login_submit(driver)
                    if self._wait_for_post_login(driver, timeout=30) != "ok":
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


    def deposit_funds_browser(self, phone, password, amount, gui_callback=None):
        """Request a KES *amount* deposit into the SportPesa account via M-Pesa.

        Opens the deposit page, fills the amount, and submits — this fires an
        STK push to the phone that only the account owner can approve (PIN/OK).
        The machine keeps running and the moment the money lands it will bet the
        pre-planned slip automatically. Login is retried and serialized against the
        machine's own logins; anything unfound gets dumped to the log for rewiring.
        """
        self._emit_direct(gui_callback,
                          f"DEPOSIT: KES {float(amount):,.2f} via M-Pesa (STK push → phone)")
        result = {"status": "error", "message": "Deposit not submitted"}
        driver = None
        try:
            driver = self._acquire_driver(gui_callback=gui_callback)
            normalized = self._format_sportsape_login_phone(phone)
            logged_in = False
            with self._login_lock:
                for attempt_n in (1, 2):
                    try:
                        self._emit_direct(gui_callback, f"  Login attempt {attempt_n} of 2...")
                        driver.get(LOGIN_URL)
                        WebDriverWait(driver, 30).until(lambda d: d.execute_script("return document.readyState") != "loading")
                        time.sleep(1)
                        pi, pw = self._wait_for_login_inputs(driver, gui_callback=gui_callback, timeout=30)
                        if not pi or not pw:
                            self._emit_direct(gui_callback,
                                              f"  (login form not found on attempt {attempt_n})")
                            if attempt_n == 1:
                                time.sleep(3)
                            continue
                        pi.clear(); pi.send_keys(normalized)
                        pw.clear(); pw.send_keys(password)
                        self._click_login_submit(driver)
                        st = self._wait_for_post_login(driver, timeout=30)
                        self._emit_direct(gui_callback, f"  Login status: {st}")
                        if st == "ok":
                            logged_in = True
                            break
                        if attempt_n == 1:
                            self._emit_direct(gui_callback, "  Retrying deposit login once...")
                            time.sleep(3)
                    except Exception as e:
                        self._emit_direct(gui_callback, f"  Login error: {str(e)[:100]}")
                        if attempt_n == 1:
                            time.sleep(3)
            if not logged_in:
                self._emit_direct(gui_callback,
                                  "  ⚠️ Login didn't confirm — opening the deposit page anyway "
                                  "(works if the session is actually live).")

            self._emit_direct(gui_callback, "  Opening deposit page...")
            # Live route (the site's own "Deposit" CTA points here, M-Pesa preselected)
            driver.get(f"{SITE_ORIGIN}/deposit_funds")
            WebDriverWait(driver, 25).until(lambda d: d.execute_script("return document.readyState") != "loading")
            time.sleep(6)
            try:
                self._dismiss_visible_promos(driver, rounds=1)
            except Exception:
                pass

            deposited = False
            try:
                # M-Pesa amount field is input#safaricom_amount[name=amount]
                amount_inp = None
                for sel in ("input#safaricom_amount[name='amount']",
                            "input[name='amount']",
                            "input[placeholder*='mount']"):
                    try:
                        amount_inp = driver.find_element(By.CSS_SELECTOR, sel)
                        break
                    except Exception:
                        continue
                if amount_inp is None:
                    amount_inp = next((i for i in driver.find_elements(By.CSS_SELECTOR, "input")
                                       if "safaricom" in ((i.get_attribute("id") or "") + (i.get_attribute("placeholder") or "")).lower()),
                                      None)
                if amount_inp is not None:
                    try:
                        amount_inp.clear()
                    except Exception:
                        pass
                    amount_inp.send_keys(str(int(float(amount))))
                    self._emit_direct(gui_callback, f"  Amount set: KES {amount:,.0f} (M-Pesa)")
                    # Confirmed button: <button class="amount-input-button">DEPOSIT</button>
                    for btn in driver.find_elements(By.CSS_SELECTOR,
                                                    "button.amount-input-button, button, input[type='submit']"):
                        try:
                            t = (btn.text or btn.get_attribute("value") or "").strip().lower()
                            if "deposit" in t and "loading" not in t:
                                btn.click()
                                deposited = True
                                self._emit_direct(gui_callback,
                                                  "  Payment submitted — STK push sent to your phone.")
                                break
                        except Exception:
                            pass
                else:
                    self._emit_direct(gui_callback,
                                      "  Amount input not found — falling back to generic scan...")
                    amount_inputs = driver.find_elements(By.CSS_SELECTOR, "input[type='number'], input[type='text'], input")
                    for inp in amount_inputs:
                        try:
                            parent_text = (inp.find_element(By.XPATH, "..").text or "").lower()
                            placeholder = (inp.get_attribute("placeholder") or "").lower()
                            name = (inp.get_attribute("name") or inp.get_attribute("id") or "").lower()
                            if any(k in parent_text + placeholder + name for k in ["amount", "kes", "topup", "top up"]):
                                try:
                                    inp.clear()
                                except Exception:
                                    pass
                                inp.send_keys(str(int(float(amount))))
                                self._emit_direct(gui_callback, f"  Amount set: KES {amount:,.0f}")
                                for btn in driver.find_elements(By.CSS_SELECTOR,
                                                                "button, input[type='submit'], "
                                                                ".paybtn.clickScale.flex-box-row.middle, "
                                                                ".btnPwd .paybtn"):
                                    try:
                                        t = (btn.text or btn.get_attribute("value") or "").lower()
                                        if any(k in t for k in ["deposit", "pay", "continue", "confirm", "mpesa", "stk"]):
                                            btn.click()
                                            deposited = True
                                            self._emit_direct(gui_callback,
                                                              "  Payment submitted — STK push sent to your phone.")
                                            break
                                    except Exception:
                                        pass
                                if deposited:
                                    break
                        except Exception:
                            pass
            except Exception as e:
                self._emit_direct(gui_callback, f"  Form error: {str(e)[:80]}")

            if deposited:
                time.sleep(6)
                try:
                    body = driver.execute_script("return document.body.innerText.substring(0,300)")
                    if any(k in body.lower() for k in ("insufficient", "error", "declined", "failed")):
                        self._emit_direct(gui_callback, f"  Deposit page reports: {body.strip()[:200]}")
                    else:
                        self._emit_direct(gui_callback,
                                          "  ✅ STK request sent — confirm the M-Pesa prompt on your phone. "
                                          "The machine bets as soon as the funds land.")
                except Exception:
                    pass

            if not deposited:
                self._emit_direct(gui_callback, "  Could not find the deposit form. Dumping page...")
                try:
                    body = driver.execute_script("return document.body.innerText.substring(0,500)")
                    self._emit_direct(gui_callback, f"  Page: {body}")
                except Exception:
                    pass

            self._logout_current_session(driver)
            result = {"status": "success" if deposited else "error",
                      "message": "STK sent" if deposited else "Form not found"}
            self._emit_direct(gui_callback,
                              f"DONE: {'STK push sent — approve it on your phone, the machine will bet once funds land.' if deposited else 'deposit form not found'}")
            return result
        except Exception as e:
            self._emit_direct(gui_callback, f"Deposit error: {str(e)[:120]}")
            return result
        finally:
            if driver:
                self._reset_driver_state(driver)
                self._store_preloaded_driver(driver)

    def _pool(self) -> float:
        """Current savings reserve (winnings banked toward the auto-withdraw)."""
        self._load_stats()
        try:
            return round(max(0.0, float(self._stats.get("savings_pool") or 0.0)), 2)
        except Exception:
            return 0.0

    def _credit_pool(self, delta: float) -> float:
        """Add *delta* (may be negative) to the savings reserve and persist it."""
        self._load_stats()
        cur = self._pool()
        new = round(max(0.0, cur + float(delta or 0.0)), 2)
        self._stats["savings_pool"] = new
        self._stats["pool_share"] = float(self._stats.get("pool_share") or self.DEFAULT_POOL_SHARE)
        self._save_stats()
        return new

    # ─────────────────────────────────────────────────────────────────────
    # FOOTBALL / SOCCER — today's matches + auto-bet on the sportsbook
    # ─────────────────────────────────────────────────────────────────────

    TODAY_GAMES_URL = (
        "https://www.ke.sportpesa.com/api/todays/1/games"
        "?type=prematch&section=today&markets_layout=multiple"
        "&o=startTime&pag_count=30&pag_min=1"
    )
    # Mobile "Today Games" listing page (kick-off times + odds in one DOM pass)
    TODAY_GAMES_PAGE_URL = "https://www.ke.sportpesa.com/en/sports-betting/football-1/today-games/"
    BETS_HISTORY_URL = "https://www.ke.sportpesa.com/bets/history"
    LEDGER_PATH = Path(writable_path("sportsape_ledger.json"))
    USAGE_PATH = Path(writable_path("sportsape_usage.json"))
    STATS_PATH = Path(writable_path("sportsape_stats.json"))
    WITHDRAW_PATH = Path(writable_path("sportsape_withdraw.json"))
    DEFAULT_POOL_SHARE = 0.25  # share of each win banked toward the auto-withdraw reserve


    def _ensure_bet_login(self, driver, phone: str, password: str, gui_callback=None):
        """Put `driver` on the today-games page and ensure we're logged in
        (re-logs-in when the session is gone — safe to call every round)."""
        normalized = self._format_sportsape_login_phone(phone)
        self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
        WebDriverWait(driver, 20).until(lambda d: d.execute_script("return document.readyState") != "loading")
        time.sleep(1)
        driver.execute_script("""
            var ov = document.querySelectorAll('[id*=responsive-image],[class*=ins-element],iframe');
            for(var i=0;i<ov.length;i++){ try{ ov[i].remove(); }catch(e){} }
        """)

        with self._login_lock:
            pi, pw = self._wait_for_login_inputs(driver, gui_callback=gui_callback)
            if pi and pw:
                pi.clear(); pi.send_keys(normalized)
                pw.clear(); pw.send_keys(password)
                time.sleep(0.5)
                self._click_login_submit(driver)
                if self._wait_for_post_login(driver) != "ok":
                    self._emit_direct(gui_callback, "⚠️ Browser login did not confirm — continuing anyway")
                else:
                    self._emit_direct(gui_callback, "✅ Logged in")
            else:
                if self._session_is_live(driver):
                    self._emit_direct(gui_callback, "✅ Session already live — already logged in")
                else:
                    self._emit_direct(gui_callback, "⚠️ Could not find login form — continuing anyway")
        self._dismiss_visible_promos(driver, rounds=1)

    def _session_is_live(self, driver) -> bool:
        """True when the current page already shows a logged-in account
        (currency / balance / Logout / Deposit present)."""
        try:
            body = driver.execute_script("return ((document.body && document.body.innerText) || '').toLowerCase();")
            return any(k in body for k in ("ksh", "kes", "logout", "deposit", "balance"))
        except Exception:
            return False

    def _place_one_bet(self, driver, phone: str, password: str, stake: float = 10,
                       visible: bool = True, gui_callback=None,
                       target_odds_min: float = 3.0, target_odds_max: float = 6.0,
                       odds_cap: float = 6.0, max_legs: int = 6,
                       min_lead_minutes: int = 10,
                       stake_percent: float = 0.0, stake_cap: float = 500.0,
                       prefer_more_legs: bool = False, reserve_pool: float = 0.0) -> dict:
        """One complete crawl-and-bet round on an already-built driver.

        Crawls + scrolls the listing, intelligently picks the best win-probability
        accumulator (never repeating a GAME across betslips), clicks the
        legs, sets the stake, PLACE BETs with smart retry/rebuild, and verifies via
        the emptied betslip / balance drop. When stake_percent > 0 the stake is
        compounded with the balance: max(base stake, balance * percent%), capped.
        *reserve_pool* KES of the balance is treated as SAVINGS that can never be
        bet — the machine waits instead of dipping into it, so the banked auto-
        withdraw amount survives losing streaks.
        Returns a dict; on success it also carries legs/stake/odds/possible_win
        so the engine can file it into the winnings ledger.
        """
        self._emit_direct(gui_callback,
                          f"FOOTBALL AUTO-BET: base KES {stake:,.0f} accumulator | "
                          f"legs x{target_odds_min:.0f}-{target_odds_max:.0f} (max {max_legs} legs)")
        target_min = float(target_odds_min)
        target_max = float(target_odds_max)
        try:
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)

            balance = self._read_balance_text(driver)
            if not balance:
                time.sleep(1.2)
                balance = self._read_balance_text(driver)
            self._emit_direct(gui_callback, f"Starting balance: KES {balance:,.2f}")

            # Compounded stake: bet a % of the bankroll (never below the base stake)
            if stake_percent and stake_percent > 0:
                stake = max(float(stake), round(balance * float(stake_percent) / 100.0, 2))
                if stake_cap and stake_cap > 0:
                    stake = min(stake, float(stake_cap))
                self._emit_direct(gui_callback,
                                  f"💹 Compounded stake: {stake_percent:g}% of bankroll "
                                  f"= KES {stake:,.2f} for this round")

            if float(balance) - float(reserve_pool or 0.0) < float(stake):
                available = max(0.0, float(balance) - float(reserve_pool or 0.0))
                deposit_needed = max(0.0, round(float(stake) - available, 2))
                self._emit_direct(gui_callback,
                                  f"💰 INSUFFICIENT FUNDS below savings — balance KES {balance:,.2f}, "
                                  f"reserve keeps KES {float(reserve_pool or 0.0):,.2f}, "
                                  f"so KES {available:,.2f} is spendable vs the KES {stake:,.0f} stake.")
                self._emit_direct(gui_callback,
                                  f"💳 DEPOSIT REQUIRED — add at least KES {deposit_needed:,.2f} "
                                  "to this account, then keep betting.")
                return {"status": "aborted", "message": "Insufficient balance below savings reserve",
                        "deposit_needed": deposit_needed, "balance": balance, "stake": float(stake)}
            stake = min(float(stake), float(balance) - float(reserve_pool or 0.0))

            # Wait for the AngularSON-rendered game rows to replace the skeleton placeholders
            render_deadline = time.time() + 25
            while time.time() < render_deadline:
                loaded = driver.execute_script(r"""
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
var real = 0, h = 0;
for (var i = 0; i < rows.length; i++) {
    h += rows[i].offsetHeight;
    if (rows[i].querySelector('.event-selection:not(.placeholder)')) real++;
}
return { real: real, h: h };
""")
                if (loaded or {}).get("real", 0) >= 3 and (loaded or {}).get("h", 0) > 0:
                    break
                time.sleep(1)

            # Crawl: scroll the listing a few times so infinite-scroll / pagination loads
            # many more games — we want every pending, placeable match, not just page 1.
            self._scroll_to_load_more_games(driver, gui_callback=gui_callback)

            games = self._extract_dom_games(driver)
            if not games:
                self._emit_direct(gui_callback, "⚠️ No game rows found on the today-games page")
                return {"status": "error", "message": "No games listed"}
            try:
                self._last_crawled_games = games
            except Exception:
                pass

            # Annotate every game with minutes remaining to kick-off
            now = datetime.now()
            for g in games:
                if g.get("start"):
                    mins = (g["start"] - now).total_seconds() / 60.0
                    g["mins_to_start"] = round(mins)
                else:
                    g["mins_to_start"] = None

            self._emit_direct(gui_callback, f"📅 Games ({len(games)}):")
            for g in sorted(games, key=lambda x: x.get("mins_to_start") if x.get("mins_to_start") is not None else 10**9):
                m = g.get("mins_to_start")
                if m is None:
                    tag = "❓ time unknown"
                elif m < -15:
                    tag = "🏁 already started"
                elif m < 0:
                    tag = "🔴 kicked off"
                elif m < min_lead_minutes:
                    tag = f"🔜 starts in {m}m — too close to place"
                else:
                    tag = f"⏳ starts in {m}m"
                o = g.get("home_odds")
                od = f" @{o:.2f}" if isinstance(o, (int, float)) else ""
                extra = []
                for key, mk in (("btts_yes", "BTTS"), ("over_25", "O/U 2.5")):
                    v = g.get(key)
                    if isinstance(v, (int, float)):
                        extra.append(f"{mk} {v:.2f}")
                self._emit_direct(gui_callback,
                                  f"  • {g['name']}{od} [{g.get('id')}] {tag}" + (f" | {' / '.join(extra)}" if extra else ""))

            # Placeable = still kicks off with at least min_lead_minutes to spare.
            # Close-to-kickoff games are exactly what we want to grab.
            playable = [g for g in games
                        if g.get("mins_to_start") is not None and g["mins_to_start"] >= min_lead_minutes]
            if not playable:
                self._emit_direct(gui_callback,
                                  f"⚠️ No games currently placeable (need >= {min_lead_minutes}m "
                                  "to kick-off). Re-crawling shortly.")
                return {"status": "aborted", "message": "No placeable games right now"}
            lead_by_gid = {str(g.get("id")): g.get("mins_to_start") for g in playable}

# Intelligent leg selection for the accumulator — never repeat a GAME
            # that already appeared in an earlier betslip (persisted across restarts),
            # so the same match is never wagered twice in different slips.
            self._load_usage()
            self._prune_usage()
            used_games = {str(gid) for gid in (self._used_games or {})}
            legs, product = self._select_football_legs(
                playable,
                target_min=target_min, target_max=target_max,
                odds_cap=odds_cap, max_legs=max_legs,
                used=used_games,
                prefer_more_legs=prefer_more_legs,
                gui_callback=gui_callback)
            if not legs:
                self._emit_direct(gui_callback,
                                  "⚠️ Could not build a sensible accumulator from the available odds "
                                  f"(cap x{odds_cap} per leg, target x{target_odds_min:.0f}-{target_odds_max:.0f}).")
                return {"status": "error", "message": "No accumulator combination found"}

            joint_prob = 1.0
            for o, name, gid, market, prob in legs:
                joint_prob *= prob
            self._emit_direct(gui_callback,
                              f"🎯 Selected {len(legs)} legs → combined x{product:.2f} "
                              f"| ~{joint_prob * 100:.1f}% estimated win chance:")
            for o, name, gid, market, prob in legs:
                self._emit_direct(gui_callback, f"   • {name} [{market}] @{o:.2f} (~{prob * 100:.0f}%)")

            # Kick-off guard: only bail if a chosen match is basically about to kick off
            # (close enough that the leg will be refused/suspended). Everything else
            # goes to the retry/rebuild machinery.
            grace_min = max(2, min_lead_minutes - 2)
            chosen_ids = {str(leg[2]) for leg in legs}
            for g in playable:
                if str(g.get("id")) in chosen_ids:
                    remaining = (g["start"] - datetime.now()).total_seconds() / 60.0
                    if remaining <= grace_min:
                        self._emit_direct(gui_callback,
                                          f"⏰ {g['name']} kicks off in {remaining:.0f}m — too close, "
                                          "skipping to the next crawl window.")
                        return {"status": "aborted", "message": "Kickoff too close, moved on"}

            picked_count = self._click_selected_legs(driver, legs, gui_callback=gui_callback)
            if picked_count < 3:
                self._emit_direct(gui_callback, "⚠️ Could not click the selected odds.")
                return {"status": "error", "message": f"Only {picked_count} odds selected"}

            # Place with automatic retries. If the slip loses selections (games going
            # in-play / odds removed) and drops below 3 legs, rebuild the slip with
            # fresh pickable games and try again (bounded rounds).
            placed = False
            used_legs = legs
            used_product = product
            used_ids = set(str(leg[2]) for leg in legs)
            for rebuild_round in range(1, 4):
                res = self._open_betslip_and_place(driver, stake, gui_callback=gui_callback,
                                                   before_balance=balance)
                if isinstance(res, bool) and res:
                    placed = True
                    break
                if not (isinstance(res, dict) and res.get("needs_legs")):
                    break
                # Rebuild: only games still kicking off with runway, and none used before
                now = datetime.now()
                remaining_playable = [
                    g for g in playable
                    if str(g.get("id")) not in used_ids and g.get("start")
                    and ((g["start"] - now).total_seconds() / 60.0) >= min_lead_minutes
                ]
                self._emit_direct(gui_callback,
                                  f"🔁 Rebuild #{rebuild_round}: reselecting from "
                                  f"{len(remaining_playable)} fresh upcoming games...")
                new_legs, new_product = self._select_football_legs(
                    remaining_playable, target_min=target_min, target_max=target_max,
                    odds_cap=odds_cap, max_legs=max_legs, used=used_games,
                    prefer_more_legs=prefer_more_legs,
                    gui_callback=gui_callback)
                if not new_legs:
                    self._emit_direct(gui_callback,
                                      "⚠️ Not enough fresh upcoming games to rebuild a valid "
                                      "3+-leg slip — no bet this round.")
                    return {"status": "aborted",
                            "message": "Slip lost selections and no fresh games left"}
                used_ids |= {str(l[2]) for l in new_legs}
                used_legs = new_legs
                used_product = new_product
                picked_count = self._click_selected_legs(driver, new_legs, gui_callback=gui_callback)
                if picked_count < 3:
                    return {"status": "error", "message": "Rebuild could not select 3 legs"}
                time.sleep(1)

            possible = round(float(stake) * used_product, 2)
            if placed:
                self._mark_legs_used(used_legs)
            return {"status": "success" if placed else "error",
                    "message": "Bet placed" if placed else "Bet not placed",
                    "legs": len(used_legs), "stake": float(stake),
                    "odds": round(used_product, 2), "possible_win": round(possible, 2),
                    "markets": [l[3] for l in used_legs],
                    "probs": [round(l[4], 4) for l in used_legs],
                    "lead_min": min((lead_by_gid.get(l[2]) or 999 for l in used_legs),
                                    default=None) or None,
                    "placed_at": datetime.now().isoformat(timespec="seconds")}

        except Exception as exc:
            self._emit_direct(gui_callback, f"Football bet error: {str(exc)[:150]}")
            return {"status": "error", "message": str(exc)[:150]}

    def _plan_ahead(self, driver, phone: str, password: str, stake: float = 10,
                    target_min: float = 3.0, target_max: float = 6.0,
                    odds_cap: float = 6.0, max_legs: int = 6,
                    min_lead_minutes: int = 10, gui_callback=None):
        """Dry-run while funds are pending: crawl the games and pre-plan the next
        slip WITHOUT clicking anything or placing a bet. Used by win-funded mode
        so the engine always knows which matches to grab the moment balance lands."""
        try:
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            self._load_usage()
            self._prune_usage()
            used_games = {str(gid) for gid in (self._used_games or {})}
            render_deadline = time.time() + 20
            while time.time() < render_deadline:
                loaded = driver.execute_script(r"""
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
var real = 0, h = 0;
for (var i = 0; i < rows.length; i++) {
    h += rows[i].offsetHeight;
    if (rows[i].querySelector('.event-selection:not(.placeholder)')) real++;
}
return { real: real, h: h };
""")
                if (loaded or {}).get("real", 0) >= 3 and (loaded or {}).get("h", 0) > 0:
                    break
                time.sleep(1)
            self._scroll_to_load_more_games(driver, gui_callback=gui_callback)
            games = self._extract_dom_games(driver)
            if not games:
                return
            now = datetime.now()
            for g in games:
                if g.get("start"):
                    g["mins_to_start"] = round((g["start"] - now).total_seconds() / 60.0)
                else:
                    g["mins_to_start"] = None
            playable = [g for g in games
                        if g.get("mins_to_start") is not None
                        and g["mins_to_start"] >= min_lead_minutes]
            legs, product = self._select_football_legs(
                playable, target_min=target_min, target_max=target_max,
                odds_cap=odds_cap, max_legs=max_legs,
                used=used_games, gui_callback=gui_callback)
            if legs:
                names = " | ".join(f"{l[1]} @{l[0]:.2f}" for l in legs)
                self._emit_direct(gui_callback,
                                  f"📋 PLANNED (KES {stake:,.0f} on arrival): {len(legs)} legs "
                                  f"→ x{product:.2f} — {names}")
            else:
                self._emit_direct(gui_callback,
                                  f"📋 Plan-ahead: no qualifying slip right now "
                                  f"({len(playable)} games placeable, "
                                  f"{len(used_games)} already used today).")
        except Exception:
            pass


    def _bet_schedule_stopped(self, stop_event) -> bool:
        """True when the scheduler must halt (kill switch or external stop event)."""
        if not getattr(self, "running", True):
            return True
        try:
            return bool(stop_event and stop_event.is_set())
        except Exception:
            return False

    def run_football_bet_schedule(self, phone: str, password: str, stake: float = 10,
                                  cadence_seconds: float = 3600.0, max_bets: int = None,
                                  retry_seconds: float = 300.0, monitor_seconds: float = 1800.0,
                                  gui_callback=None, stop_event=None,
                                   visible: bool = True, daily_bets: int = 20,
                                   stake_percent: float = 2.0, stake_cap: float = 500.0,
                                   chain_bets: bool = True, chain_gap: float = 25.0,
                                   longshot: bool = True, longshot_odds_min: float = 15.0,
                                   longshot_odds_max: float = 60.0, longshot_odds_cap: float = 1.75,
                                   longshot_legs: int = 10,
                                   auto_withdraw: bool = True, withdraw_amount: float = 200.0,
                                   headless: bool = False) -> dict:
        """24/7 auto-bet engine: places smart bets AND monitors winnings.

        Uses ONE long-lived browser session (stable for 24/7 running; the driver is
        re-healed automatically when it crashes). Each round it crawls today-games,
        picks the smartest accumulator (a game is never repeated across clean
        betslips), places it, then periodically opens the Bet History page and settles
        ledger entries — emitting 🏆 WON / ❌ LOST events and keeping the winnings
        panel honest across restarts (persistent ledger).

        It is HUNGRY: when a betslip is confirmed (placed), it instantly re-crawls and,
        if more qualifying games were spotted, it MOVES on and fills an entirely NEW
        betslip (`chain_bets`, default on) instead of idling. The runs keep chaining
        until the games are exhausted or the daily/max cap is reached — never less
        than three legs, never a repeated game.

        - with chaining ON: consecutive slips are placed ~every `chain_gap` seconds;
          when nothing is available the engine idles scanning every `retry_seconds`
          (no bet waits), and `cadence_seconds` is the idle re-scan ceiling,
        - with chaining OFF: classic pacing — NEVER more than one bet per hour
          (a `cadence_seconds` cooldown starts after each successful placement),
        - every `monitor_seconds` Bet History is synced for settled bets,
        - at most `daily_bets` bets per calendar day (default 10); past the cap the
          engine runs in MONITOR-ONLY mode and resumes betting next day,
        - `stake_percent > 0` compounds the stake with the bankroll:
          max(base stake, balance * stake_percent%), capped at `stake_cap`,
        - LEARNING: every settled bet is filed into lifetime stats (per market type +
        - per recipe/odds-band). Market types that beat their predicted fair chance
          get weighted up; consistent underperformers are RETIRED. Once 30+ bets are
          settled an epsilon-greedy bandit steers the odds band toward top-ROI recipes,
        - when the balance can't cover the stake it keeps the session alive in
          WIN-FUNDED mode: win-syncs, crawls the games to pre-plan the next slip,
          and bets automatically the moment winnings land in the account,
        - stop via stop_event or self.running == False (GUI emergency stop).
        """
        self._load_ledger()
        summary = self._ledger_summary()
        self._emit_direct(gui_callback,
                          f"📊 Tracked: {summary['placed']} bets | won {summary['won']} "
                          f"(+KES {summary['won_return']:,.2f}) | lost {summary['lost']} | "
                          f"active {summary['active']} | net {summary['net_profit']:+,.2f}")

        cadence = max(20.0, float(cadence_seconds))
        retry = max(10.0, float(retry_seconds))
        monitor = max(20.0, float(monitor_seconds))
        bets_placed = 0
        attempt = 0
        consec_fail = 0
        driver = None
        last_sync = 0.0
        active_day = ""
        daily_placed = 0
        next_daily_msg = 0.0
        last_placed_ts = 0.0
        next_cooldown_msg = 0.0
        max_bets = int(max_bets) if max_bets else None
        daily_bets = int(daily_bets) if daily_bets else 0
        longshot_placed_day = ""
        self._load_usage()
        limit_txt = "unlimited" if not max_bets else f"max {int(max_bets)}"
        daily_txt = "∞" if not daily_bets else f"max {int(daily_bets)}/day"
        chain_gap = max(10.0, float(chain_gap))
        self._emit_direct(gui_callback,
                          f"📡 BET MACHINE: crawling now, hungry mode "
                          f"{'ON (chained betslips ~every ' + str(int(chain_gap)) + 's while games remain)' if chain_bets else 'OFF (≤1 bet/hr)'}; "
                          f"daily {daily_txt}; scope {limit_txt}; "
                          f"idle scan every {retry:g}s; "
                          f"win-sync every {monitor:g}s; compounded stake "
                          f"{'OFF' if not stake_percent else f'{stake_percent:g}%'}; "
                          f"DAILY LONG-SHOT {'ON (one '+str(int(longshot_legs))+'+-leg ' + f'x{longshot_odds_min:g}-x{longshot_odds_max:g} slip/day)' if longshot else 'OFF'}; "
                          f"AUTO-WITHDRAW {f'ON (KES {withdraw_amount:g}/day)' if auto_withdraw else 'OFF'}")
        pool = self._pool()
        self._emit_direct(gui_callback,
                          f"💰 SAVINGS MODE: KES {pool:,.2f} reserved {('('+str(int((self._stats.get('pool_share') or self.DEFAULT_POOL_SHARE)*100))+'% of each win banked)') if pool else '(0 — will bank from first win)'}. "
                          f"Bets only spend balance ABOVE the reserve; at KES {withdraw_amount:,.0f} "
                          "saved the daily auto-withdraw fires and the cycle recycles.")
        self._jackpot_next_scan = time.time() + 45.0
        self._jackpot_state = None
        while True:
            if self._bet_schedule_stopped(stop_event):
                break
            if max_bets and bets_placed >= int(max_bets):
                self._emit_direct(gui_callback, f"✅ Reached limit of {int(max_bets)} bets — done")
                self._quit_bet_driver(driver)
                return {"status": "done", "message": "Max bets reached",
                        "bets_placed": bets_placed, "summary": self._ledger_summary()}
            attempt += 1
            # Savings-pool auto-withdraw: as soon as the banked reserve reaches the
            # threshold, move it out (daemon, non-blocking) and keep the cycle going.
            pool = self._pool()
            if auto_withdraw and float(withdraw_amount) > 0 and pool >= float(withdraw_amount):
                try:
                    self._maybe_auto_withdraw(phone, password, float(withdraw_amount),
                                              in_flight_key="pool", pool=pool,
                                              gui_callback=gui_callback)
                except Exception as e:
                    self._emit_direct(gui_callback, f"⚠️ Savings-withdraw skip: {str(e)[:80]}")
            # Daily rolling budget: count today's placements, reset on day change
            today = datetime.now().strftime("%Y-%m-%d")
            if today != active_day:
                active_day = today
                daily_placed = sum(
                    1 for e in getattr(self, "_bets", []) or []
                    if (e.get("placed_at") or "").startswith(today))
                self._emit_direct(gui_callback,
                                  f"🗓️ New day {today} — daily budget {daily_txt} "
                                  f"({daily_placed} placed so far)")
            if daily_bets and daily_placed >= daily_bets:
                # Daily cap reached: monitor winnings only, resume betting next day
                wait = monitor
                if time.time() >= next_daily_msg:
                    next_daily_msg = time.time() + 600
                    self._emit_direct(gui_callback,
                                      f"🎯 Daily cap of {daily_bets} bets reached for {today} — "
                                      "monitoring winnings; betting resumes tomorrow.")
                if (time.time() - last_sync) >= monitor and driver is not None:
                    try:
                        self._monitor_and_sync_winnings(driver, gui_callback=gui_callback)
                        last_sync = time.time()
                    except Exception as e:
                        self._emit_direct(gui_callback, f"⚠️ Win-sync hiccup: {str(e)[:100]}")
                waited = 0.0
                self._engine_busy = False
                while waited < wait:
                    if self._bet_schedule_stopped(stop_event):
                        break
                    self._jackpot_tick(phone, password, gui_callback=gui_callback)
                    time.sleep(min(10.0, wait - waited))
                    waited += 10.0
                continue
            # Hourly cooldown: only applies in classic mode (chaining disabled). In hungry
            # mode a placed bet is followed by a quick re-crawl for MORE betslips.
            if not chain_bets and last_placed_ts:
                elapsed = time.time() - last_placed_ts
                if elapsed < cadence:
                    remain = cadence - elapsed
                    if time.time() >= next_cooldown_msg:
                        next_cooldown_msg = time.time() + 600
                        self._emit_direct(gui_callback,
                                          f"⏳ Hourly cooldown — next bet window in "
                                          f"{remain / 60.0:.0f} min; games stay un-placed until then")
                    if (time.time() - last_sync) >= monitor and driver is not None:
                        try:
                            self._monitor_and_sync_winnings(driver, gui_callback=gui_callback)
                            last_sync = time.time()
                        except Exception as e:
                            self._emit_direct(gui_callback, f"⚠️ Win-sync hiccup: {str(e)[:100]}")
                    waited = 0.0
                    self._engine_busy = False
                    while waited < remain:
                        if self._bet_schedule_stopped(stop_event):
                            break
                        self._jackpot_tick(phone, password, gui_callback=gui_callback)
                        time.sleep(min(30.0, remain - waited))
                        waited += 30.0
                    continue
            try:
                self._engine_busy = True
                if driver is None:
                    self._emit_direct(gui_callback, "🌐 (re)opening stable browser session...")
                    driver = self._build_driver(gui_callback=gui_callback,
                                                force_visible=visible, mobile=False,
                                                headless=headless,
                                                capture_perf=False, minimize=True)
                elif not self._driver_is_usable(driver):
                    self._emit_direct(gui_callback, "🔧 Healed: old browser session died (window closed), rebuilding...")
                    self._quit_bet_driver(driver)
                    driver = self._build_driver(gui_callback=gui_callback,
                                                force_visible=visible, mobile=False,
                                                headless=headless,
                                                capture_perf=False, minimize=True)
                self._bet_driver = driver  # expose for emergency stop / healing
                # Eager login: confirm the session is live before crawling so the
                # machine is ready the moment balance lands (deposit works regardless —
                # it opens its own session — but this keeps the engine warm).
                self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
                if not self._session_is_live(driver):
                    for _try in range(2):
                        time.sleep(3)
                        self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
                        if self._session_is_live(driver):
                            break
                    if not self._session_is_live(driver):
                        self._emit_direct(gui_callback, "🔐 Login unreachable this round — re-crawling shortly.")
                self._emit_direct(gui_callback, f"⏱️ Crawl-and-bet attempt #{attempt} ...")
                # Daily LONG-SHOT ticket: one multi-leg x15-x60 accumulator per day,
                # placed on the first qualifying round; every other round bets smart.
                want_longshot = (bool(longshot) and longshot_placed_day != today)
                if want_longshot:
                    self._emit_direct(gui_callback,
                                      f"🎯 DAILY LONG-SHOT: one {int(longshot_legs)}-leg "
                                      f"x{longshot_odds_min:g}-x{longshot_odds_max:g} ticket today")
                    res = self._place_one_bet(driver, phone, password, stake=stake,
                                              visible=visible, gui_callback=gui_callback,
                                              target_odds_min=longshot_odds_min,
                                              target_odds_max=longshot_odds_max,
                                              odds_cap=longshot_odds_cap,
                                              max_legs=int(longshot_legs),
                                              stake_percent=stake_percent,
                                              stake_cap=stake_cap,
                                              prefer_more_legs=True,
                                              reserve_pool=pool)
                else:
                    lo, hi = self._bandit_target_range(3.0, 6.0)
                    res = self._place_one_bet(driver, phone, password, stake=stake,
                                              visible=visible, gui_callback=gui_callback,
                                              target_odds_min=lo, target_odds_max=hi,
                                              stake_percent=stake_percent,
                                              stake_cap=stake_cap,
                                              reserve_pool=pool)
                # A long-shot ticket that didn't qualify should NOT block the daily
                # smart pipeline — the round falls through to a normal smart bet.
                if want_longshot and not (isinstance(res, dict) and res.get("status") == "success"):
                    lo, hi = self._bandit_target_range(3.0, 6.0)
                    res = self._place_one_bet(driver, phone, password, stake=stake,
                                              visible=visible, gui_callback=gui_callback,
                                              target_odds_min=lo, target_odds_max=hi,
                                              stake_percent=stake_percent,
                                              stake_cap=stake_cap,
                                              reserve_pool=pool)
                    want_longshot = False
                status = res.get("status") if isinstance(res, dict) else "error"
                if status == "success":
                    if want_longshot:
                        longshot_placed_day = today
                    bets_placed += 1
                    daily_placed += 1
                    consec_fail = 0
                    last_placed_ts = time.time()
                    self._record_bet_from_result(res)
                    if chain_bets:
                        try:
                            self._backfill_bet_ids(driver, gui_callback=gui_callback)
                        except Exception as e:
                            self._emit_direct(gui_callback, f"⚠️ ID backfill skip: {str(e)[:80]}")
                    wait = chain_gap if chain_bets else cadence
                    tag = "🎯 LONG-SHOT" if want_longshot else "✅ SMART"
                    self._emit_direct(gui_callback,
                                      f"{tag} Bet #{bets_placed} placed (day {daily_placed}/{daily_txt}) — "
                                      f"{f'spotting more games → chaining next betslip in {chain_gap:g}s' if chain_bets else f'next hourly window in {cadence:g}s'}")
                elif res.get("deposit_needed") if isinstance(res, dict) else None:
                    need = res.get("deposit_needed", 0.0)
                    bal = res.get("balance", 0.0)
                    self._emit_direct(gui_callback,
                                      f"💰 Balance KES {bal:,.2f} is below the KES {stake:,.0f} "
                                      "stake — switching to WIN-FUNDED WAIT mode.")
                    self._emit_direct(gui_callback,
                                      f"⛽ Waiting for winnings to fund the next ticket. I'll "
                                      "keep win-syncing and crawling the games to pre-plan the "
                                      "slip, then bet automatically the moment funds land.")
                    # WIN-FUNDED WAIT: instead of hard-stopping the machine, keep the
                    # browser alive, settle winnings, read the live balance, and dry-run
                    # the games list to pre-plan the next slip — so e.g. 30 shillings
                    # lands -> one 10-stake bet fires, wait for more winnings -> bet again.
                    plan_next = time.time()
                    self._engine_busy = False
                    while not self._bet_schedule_stopped(stop_event):
                        if driver is None or not self._driver_is_usable(driver):
                            self._emit_direct(gui_callback,
                                              "🔧 Rebuilding browser for win-funded wait...")
                            self._quit_bet_driver(driver)
                            driver = self._build_driver(gui_callback=gui_callback,
                                                        force_visible=visible, mobile=False,
                                                        headless=headless,
                                                        capture_perf=False, minimize=True)
                            self._bet_driver = driver
                        if (time.time() - last_sync) >= monitor:
                            try:
                                self._monitor_and_sync_winnings(driver, gui_callback=gui_callback)
                                last_sync = time.time()
                            except Exception as e:
                                self._emit_direct(gui_callback,
                                                  f"⚠️ Win-sync hiccup: {str(e)[:100]}")
                        b2 = 0.0
                        try:
                            b2 = self._read_balance_text(driver) or 0.0
                        except Exception:
                            b2 = 0.0
                        eff_stake = stake
                        if stake_percent and stake_percent > 0:
                            eff_stake = max(stake, round(b2 * stake_percent / 100.0, 2))
                            if stake_cap and stake_cap > 0:
                                eff_stake = min(eff_stake, float(stake_cap))
                        pool_r = self._pool()
                        if b2 and (b2 - pool_r) >= eff_stake:
                            self._emit_direct(gui_callback,
                                              f"💵 KES {b2:,.2f} in the account covers a "
                                              f"KES {eff_stake:,.0f} ticket above the KES {pool_r:,.2f} "
                                              f"reserve — GO!")
                            break
                        if time.time() >= plan_next:
                            plan_next = time.time() + 120
                            try:
                                self._plan_ahead(driver, phone, password, stake=stake,
                                                 gui_callback=gui_callback)
                            except Exception as e:
                                self._emit_direct(gui_callback,
                                                  f"⚠️ Plan-ahead scan hiccup: {str(e)[:100]}")
                        if self._bet_schedule_stopped(stop_event):
                            break
                        self._jackpot_tick(phone, password, gui_callback=gui_callback)
                        time.sleep(10)
                    else:
                        self._quit_bet_driver(driver)
                        self._emit_direct(gui_callback,
                                          "⏹️ Win-funded wait cancelled (emergency stop).")
                        return {"status": "stopped",
                                "message": "Stopped while waiting for funds",
                                "bets_placed": bets_placed,
                                "summary": self._ledger_summary()}
                    continue
                else:
                    wait = retry
                    msg = (res.get("message") or "") if isinstance(res, dict) else ""
                    self._emit_direct(gui_callback,
                                      f"⏭️ No bet this round ({str(msg)[:90]}) — re-crawling in {retry:g}s")
                # Win monitoring: settle ledger entries right after a bet AND periodically
                if status == "success" or (time.time() - last_sync) >= monitor:
                    try:
                        self._monitor_and_sync_winnings(driver, gui_callback=gui_callback)
                        last_sync = time.time()
                    except Exception as e:
                        self._emit_direct(gui_callback, f"⚠️ Win-sync hiccup: {str(e)[:100]}")
                # Daily auto-withdraw: once a day, move out a slice of today's winnings
                if auto_withdraw:
                    try:
                        self._maybe_auto_withdraw(phone, password, float(withdraw_amount),
                                                  gui_callback=gui_callback)
                    except Exception as e:
                        self._emit_direct(gui_callback, f"⚠️ Auto-withdraw skip: {str(e)[:80]}")
            except Exception as exc:
                consec_fail += 1
                self._emit_direct(gui_callback,
                                  f"⚠️ Machine round crashed: {str(exc)[:120]} (fail #{consec_fail})")
                self._quit_bet_driver(driver)
                driver = None
                self._engine_busy = False
                if consec_fail >= 4:
                    self._emit_direct(gui_callback,
                                      "🌐 No connection or browser trouble — staying on and "
                                      "retrying every 60s until the network is back. The engine "
                                      "resumes betting on its own once online again.")
                    wait = 60.0
                else:
                    wait = retry
            # interruptible wait that honours the kill switch
            self._engine_busy = False
            waited = 0.0
            while waited < wait:
                if self._bet_schedule_stopped(stop_event):
                    break
                self._jackpot_tick(phone, password, gui_callback=gui_callback)
                time.sleep(min(5.0, wait - waited))
                waited += 5.0
        self._quit_bet_driver(driver)
        summary = self._ledger_summary()
        self._emit_direct(gui_callback, "⏹️ Bet machine stopped")
        return {"status": "stopped", "message": "Scheduler stopped",
                "bets_placed": bets_placed, "summary": summary}

    def force_stop_bet_driver(self):
        """Hard-kill the shared bet-session browser (used by the GUI emergency stop)."""
        try:
            if getattr(self, "_bet_driver", None) is not None:
                self._bet_driver.quit()
        except Exception:
            pass
        self._bet_driver = None

    def _quit_bet_driver(self, driver):
        """Quit a bet-session browser if still alive (idempotent, never throws)."""
        try:
            if driver is not None:
                driver.quit()
        except Exception:
            pass
        if getattr(self, "_bet_driver", None) is driver:
            self._bet_driver = None

    # ── Jackpot engine (MEGA POT / MID POT) ───────────────────────────
    # The SportPesa jackpots live in a cross-origin widget iframe. Reads + picks
    # are done through a dedicated browser (never the machine's bet session), so a
    # jackpot run can never disturb the accumulator engine. Placement reuses the
    # same logged-in account (KES 99 entry, MEGA 17 games Sat-Sun / MIDWEEK 13 Thu-Fri).
    JACKPOT_WIDGET_IFRAME_SELECTORS = (
        "#multijackpot-iframe",
        "iframe[src*='jackpot-widget']",
        "iframe[src*='jackpot']",
        "iframe",
    )
    JACKPOT_ROW_SELECTOR = ".event-row:not(.event-row-header)"
    JACKPOT_PICK_MAP = {"H": "button-Home", "D": "button-Draw", "A": "button-Away"}

    def _jackpot_tick(self, phone, password, gui_callback=None):
        """Called from every engine idle wait — keeps the machine analysing the
        current jackpot pool while it would otherwise be sleeping (always busy)."""
        try:
            if time.time() >= self._jackpot_next_scan:
                self._jackpot_next_scan = time.time() + self._jackpot_cadence
                self._jackpot_idle_scan(phone, password, gui_callback=gui_callback)
        except Exception as e:
            self._emit_direct(gui_callback, f"ℹ️ Jackpot scan skipped: {str(e)[:80]}")

    def _jackpot_dump_dir(self):
        try:
            d = Path(tempfile.gettempdir()) / "betflow_dumps"
            d.mkdir(parents=True, exist_ok=True)
            return d
        except Exception:
            return Path(".")

    def _dump_ctx(self, driver, tag: str, extra="inner"):
        """Best-effort forensics when the widget surprises us (never throws)."""
        try:
            d = self._jackpot_dump_dir()
            txt = "<!-- NO BODY -->"
            if extra == "outer":
                try:
                    body = driver.find_element(By.TAG_NAME, "body")
                    txt = body.text or "<!-- empty body -->"
                except Exception:
                    txt = "<!-- outer body not readable -->"
            else:
                try:
                    txt = driver.execute_script(
                        "return (document.body && (document.body.innerText || '')) || '';") or ""
                except Exception:
                    txt = "<!-- inner body not readable -->"
            p = d / f"{tag}.txt"
            p.write_text(f"{datetime.now().isoformat()}\n{extra}\n{txt[:200000]}",
                         encoding="utf-8", errors="replace")
            try:
                shot = d / f"{tag}.png"
                driver.save_screenshot(str(shot))
            except Exception:
                pass
        except Exception:
            pass

    def _widget_iframe(self, driver):
        """Return the jackpot widget iframe element (page context) or None."""
        iframe = None
        for sel in self.JACKPOT_WIDGET_IFRAME_SELECTORS:
            try:
                for e in driver.find_elements(By.CSS_SELECTOR, sel):
                    try:
                        if e.is_displayed() and e.get_attribute("src"):
                            iframe = e
                            break
                    except Exception:
                        continue
            except Exception:
                continue
            if iframe is not None:
                break
        return iframe

    def _odds_float(self, raw, default=None):
        if raw is None:
            return default
        m = re.search(r"\d+(?:[.,]\d+)?", str(raw).replace(",", "."))
        if not m:
            return default
        try:
            v = float(m.group(0))
            return v if v >= 1.01 else default
        except Exception:
            return default

    def _fetch_jackpot_pool(self, driver, gui_callback=None):
        """Open the jackpot page, enter the widget iframe and parse every game row
        (position, teams, match id, 1X2 odds). Pool name detected from widget copy."""
        try:
            self._safe_get(driver, self.JACKPOT_PAGE_URL)
        except Exception as e:
            self._emit_direct(gui_callback, f"⚠️ Jackpot page failed to load: {str(e)[:90]}")
            return None
        iframe = self._widget_iframe(driver)
        if iframe is None:
            self._dump_ctx(driver, "jackpot_no_iframe", extra="outer")
            self._emit_direct(gui_callback, "⚠️ Jackpot widget iframe not found on the page.")
            return None
        try:
            driver.switch_to.frame(iframe)
        except Exception as e:
            self._emit_direct(gui_callback, f"⚠️ Could not switch into widget: {str(e)[:80]}")
            return None
        rows = []
        deadline = time.time() + 25
        while time.time() < deadline:
            try:
                rows = driver.find_elements(By.CSS_SELECTOR, self.JACKPOT_ROW_SELECTOR)
                real = [r for r in rows if r.find_elements(By.CSS_SELECTOR, "[data-testid^='button-']")]
                if len(real) >= 8:
                    rows = real
                    break
            except Exception:
                pass
            time.sleep(1)
        if len(rows) < 8:
            self._dump_ctx(driver, "jackpot_empty_widget")
            self._emit_direct(gui_callback,
                              "⚠️ Jackpot widget rendered empty (Akamai challenge hit). "
                              "Retrying with a fresh browser helps; nothing was placed.")
            try:
                driver.switch_to.default_content()
            except Exception:
                pass
            return None
        body = ((driver.execute_script("return (document.body && document.body.innerText) || '';") or ""))
        bl = body.lower()
        if "midweek" in bl and "mega" not in bl:
            pname = "MIDWEEK"
        elif "mega" in bl:
            pname = "MEGA"
        else:
            pname = "UNKNOWN"
        events = []
        for i, row in enumerate(rows):
            ev = {"order": i + 1, "match_id": "", "home": "", "away": "",
                  "raw": "", "odds_1": None, "odds_x": None, "odds_2": None}
            try:
                flags = row.find_elements(By.CSS_SELECTOR, "[data-testid^='sr:match:']")
                if flags:
                    ev["match_id"] = flags[0].get_attribute("data-testid") or ""
                names = row.find_elements(By.CSS_SELECTOR, ".team-name")
                if len(names) >= 2:
                    ev["home"] = names[0].text.strip()
                    ev["away"] = names[1].text.strip()
                elif len(names) == 1:
                    ev["home"] = names[0].text.strip()
                for key, testid in (("odds_1", "button-Home"),
                                    ("odds_x", "button-Draw"),
                                    ("odds_2", "button-Away")):
                    try:
                        sel = row.find_element(By.CSS_SELECTOR, f"[data-testid='{testid}']")
                        ev[key] = self._odds_float(sel.text.strip().split("\n")[-1])
                    except Exception:
                        pass
                ev["raw"] = (row.text or "")[:260]
            except Exception:
                pass
            events.append(ev)
        try:
            driver.switch_to.default_content()
        except Exception:
            pass
        if not events:
            return None
        return {"name": pname, "count": len(events), "events": events,
                "ts": time.time(), "url": self.JACKPOT_PAGE_URL}

    def _poisson_score_outcomes(self, lh, la, n=13):
        """Exact (H, D, A) probabilities from two independent Poissons over a 0..n grid."""
        import math
        ph = [math.exp(-lh)]
        pa = [math.exp(-la)]
        for k in range(1, n):
            ph.append(ph[-1] * lh / k)
            pa.append(pa[-1] * la / k)
        s = sum(ph)
        ph = [x / s for x in ph] if s else ph
        s = sum(pa)
        pa = [x / s for x in pa] if s else pa
        H = D = A = 0.0
        for i in range(n):
            for j in range(n):
                p = ph[i] * pa[j]
                if i > j:
                    H += p
                elif i == j:
                    D += p
                else:
                    A += p
        t = H + D + A
        return (H / t, D / t, A / t) if t else (0.0, 0.0, 0.0)

    def _fit_poisson(self, p1, pd, p2):
        """Fit (lambda_home, lambda_away) to fair 1X2 probabilities (coarse grid + refine)."""
        best = None
        best_err = 1e9
        step = 0.15
        for i in range(1, 35):
            lh = 0.25 + i * step
            for la_ix in range(1, 35):
                la = 0.25 + la_ix * step
                sh, sd, sa = self._poisson_score_outcomes(lh, la)
                err = (sh - p1) ** 2 + (sd - pd) ** 2 + (sa - p2) ** 2
                if err < best_err:
                    best_err = err
                    best = (lh, la)
        if best is None:
            return None
        lh, la = best
        step2 = 0.01
        for d1 in (-0.2, 0.0, 0.2):
            for d2 in (-0.2, 0.0, 0.2):
                for k1 in range(-5, 6):
                    lh2 = max(0.2, lh + d1 + k1 * step2)
                    for k2 in range(-5, 6):
                        la2 = max(0.2, la + d2 + k2 * step2)
                        sh, sd, sa = self._poisson_score_outcomes(lh2, la2)
                        err = (sh - p1) ** 2 + (sd - pd) ** 2 + (sa - p2) ** 2
                        if err < best_err - 1e-12:
                            best_err = err
                            lh, la = lh2, la2
        return lh, la

    def _total_goals_from_ou(self, over_prob, lo=0.5, hi=6.0):
        """Estimate combined expected goals lambda so that P(total > 2.5) == over_prob."""
        import math
        target = max(0.03, min(0.97, float(over_prob)))
        for _ in range(60):
            mid = (lo + hi) / 2.0
            p_gt = 1.0
            for k in range(0, 4):
                p_gt -= math.exp(-mid) * (mid ** k) / math.factorial(k)
            if p_gt > target:
                hi = mid
            else:
                lo = mid
        return (lo + hi) / 2.0

    def _crawl_ou_for_match(self, ev, games):
        """Match a jackpot event to a crawled today-game and return the fair Over-2.5
        probability (second market — real info beyond the 1X2 odds)."""
        try:
            hk = re.sub(r"[^a-z0-9]", "", (ev.get("home") or "").lower())
            ak = re.sub(r"[^a-z0-9]", "", (ev.get("away") or "").lower())
            if not hk or not ak:
                return None
            for g in games or []:
                name = (g.get("name") or "").lower()
                h, a = name.split("v", 1) if "v" in name else ("", "")
                h = re.sub(r"[^a-z0-9]", "", h)
                a = re.sub(r"[^a-z0-9]", "", a)
                if not h or not a:
                    continue
                if {h, a} == {hk, ak}:
                    if g.get("ou"):
                        fair = self._fair_win_probs(g.get("ou")) or []
                        if fair and fair[0] and isinstance(g.get("over_25"), (int, float)):
                            return fair[0]
                    if g.get("over_25"):
                        return 1.0 / float(g["over_25"])
                    return None
        except Exception:
            pass
        return None

    def _analyze_event(self, ev, games=None):
        """One game's prediction: fair odds -> Poisson fit -> Monte-Carlo outcome odds,
        cross-checked with the crawled Over/Under market, plus a draw floor and a
        favourite-commitment clamp so single legs never become reckless 1.05 shots."""
        o1 = float(ev.get("odds_1") or 0)
        ox = float(ev.get("odds_x") or 0)
        o2 = float(ev.get("odds_2") or 0)
        if o1 < 1.01 or ox < 1.01 or o2 < 1.01:
            return None
        m = 1.0 / o1 + 1.0 / ox + 1.0 / o2
        p1, pd, p2 = (1.0 / o1) / m, (1.0 / ox) / m, (1.0 / o2) / m
        fitted = self._fit_poisson(p1, pd, p2)
        if fitted is None:
            H, D, A = p1, pd, p2
        else:
            lh, la = fitted
            ou_p = self._crawl_ou_for_match(ev, games)
            if ou_p is not None:
                lam = self._total_goals_from_ou(ou_p)
                tot = lh + la
                if tot > 0.1:
                    lh = lh / tot * lam
                    la = la / tot * lam
            H, D, A = self._poisson_score_outcomes(lh, la)
        H = 0.62 * H + 0.38 * p1
        D = 0.62 * D + 0.38 * pd
        A = 0.62 * A + 0.38 * p2
        D = max(D, 0.235)  # draws are the jackpot blind-spot — never starve them out
        totp = H + D + A
        H, D, A = H / totp, D / totp, A / totp
        mx = max(H, D, A)
        cap = 0.63
        if mx > cap:  # don't over-commit to a walking favourite (odds-trapping guard)
            excess = mx - cap
            scale = 1.0 - (excess / max((1.0 - mx), 1e-9))
            if mx == H:
                D, A = D * scale, A * scale
                H = cap
            elif mx == D:
                H, A = H * scale, A * scale
                D = cap
            else:
                H, D = H * scale, D * scale
                A = cap
            totp = H + D + A
            H, D, A = H / totp, D / totp, A / totp
        pick = "H" if H >= D and H >= A else ("D" if D >= A else "A")
        conf = max(H, D, A)
        return {"order": ev.get("order"),
                "home": ev.get("home", ""), "away": ev.get("away", ""),
                "pick": pick, "conf": round(conf, 4),
                "probs": [round(H, 4), round(D, 4), round(A, 4)],
                "odds": [round(o1, 2), round(ox, 2), round(o2, 2)],
                "match_id": ev.get("match_id", "")}

    def _analyze_jackpot_pool(self, pool):
        picks = []
        for ev in pool.get("events") or []:
            r = self._analyze_event(ev, games=self._last_crawled_games)
            if r is not None:
                picks.append(r)
        return picks

    def _cached_jackpot_picks(self, pool):
        st = self._jackpot_state or {}
        if not st:
            return None
        if time.time() - (st.get("ts") or 0) > 45 * 60:
            return None
        if st.get("pool_name") != pool.get("name"):
            return None
        old_ids = [e.get("match_id") for e in (st.get("pool") or {}).get("events") or []]
        new_ids = [e.get("match_id") for e in pool.get("events") or []]
        if old_ids != new_ids or not st.get("picks"):
            return None
        return st.get("picks")

    def _widget_select(self, sel):
        try:
            return sel.text.strip()
        except Exception:
            return ""

    def _find_betslip_confirm(self, driver):
        """Locate the widget's place-bet button (unknown markup — try many signals)."""
        cands = []
        for sel in ("button[type='submit']", "button", "[role='button']"):
            try:
                for e in driver.find_elements(By.CSS_SELECTOR, sel):
                    try:
                        if not e.is_displayed():
                            continue
                    except Exception:
                        pass
                    t = (e.text or "").strip()
                    tl = t.lower()
                    if any(k in tl for k in ("place bet", "confirm", "next", "bet now",
                                             "submit", "place typical bet", "place jackpot")):
                        cands.append((e, tl))
                if cands:
                    break
            except Exception:
                continue
        # prefer the most specific phrase
        def _rank(c):
            t = c[1]
            return (5 if t.startswith("place") else 4 if "confirm" in t else 3 if "next" in t
                    else 0, len(t))
        cands.sort(key=_rank, reverse=True)
        return cands

    def _set_jackpot_stake(self, driver, stake):
        """Populate the stake box if the widget exposes one (best effort)."""
        try:
            inputs = driver.find_elements(By.CSS_SELECTOR,
                                          "input[type='text'],input[type='number'],input")
            for inp in inputs:
                try:
                    ph = ((inp.get_attribute("placeholder") or "") +
                          " " + (inp.get_attribute("class") or "")).lower()
                except Exception:
                    ph = ""
                if not inp.is_displayed():
                    continue
                val = None
                try:
                    val = inp.get_attribute("value")
                except Exception:
                    pass
                if ("stake" in ph or "bet" in ph or "amount" in ph or "99" in (val or "")):
                    try:
                        inp.clear()
                        inp.send_keys(str(int(stake)))
                        return True
                    except Exception:
                        pass
            return False
        except Exception:
            return False

    def _jackpot_confirmed(self, driver) -> bool:
        try:
            body = (driver.execute_script(
                "return (document.body && document.body.innerText) || '';") or "").lower()
            marks = ("successful", "successfully", "bet received", "bet placed",
                     "order received", "confirmation", "receipt", "request accepted",
                     "thank you")
            if any(mk in body for mk in marks):
                return True
            try:
                n = len(driver.find_elements(By.CSS_SELECTOR,
                    "[data-testid^='button-'].select, .event-selection.select"))
                if n < 4:
                    return True
            except Exception:
                pass
        except Exception:
            pass
        return False

    def _place_jackpot_on_driver(self, driver, pool, picks, stake=99.0, gui_callback=None):
        """Pick every game in the widget and submit the KES 99 jackpot entry."""
        try:
            self._safe_get(driver, self.JACKPOT_PAGE_URL)
        except Exception as e:
            return {"status": "error", "message": f"page: {str(e)[:80]}"}
        iframe = self._widget_iframe(driver)
        if iframe is None:
            return {"status": "error", "message": "widget iframe missing"}
        try:
            driver.switch_to.frame(iframe)
        except Exception as e:
            return {"status": "error", "message": f"iframe: {str(e)[:60]}"}
        rows = []
        deadline = time.time() + 20
        while time.time() < deadline:
            try:
                rows = driver.find_elements(By.CSS_SELECTOR, self.JACKPOT_ROW_SELECTOR)
                if len(rows) >= 8:
                    break
            except Exception:
                pass
            time.sleep(1)
        if len(rows) < 8:
            self._dump_ctx(driver, "jackpot_place_empty")
            return {"status": "error", "message": "widget rows did not render (Akamai)"}
        n = min(len(rows), len(picks), pool.get("count") or len(picks))
        clicked = 0
        first_missing = None
        for i in range(n):
            pick = picks[i]
            testid = self.JACKPOT_PICK_MAP.get(pick.get("pick"))
            if not testid:
                continue
            try:
                sel = rows[i].find_element(By.CSS_SELECTOR, f"[data-testid='{testid}']")
                try:
                    driver.execute_script(
                        "arguments[0].scrollIntoView({block:'center', behavior:'instant'});", sel)
                except Exception:
                    pass
                time.sleep(0.12)
                try:
                    sel.click()
                except Exception:
                    driver.execute_script("arguments[0].click();", sel)
                clicked += 1
            except Exception as e:
                if first_missing is None:
                    first_missing = (i + 1, str(e)[:60])
                continue
        if clicked < n:
            self._dump_ctx(driver, f"jackpot_picks_only_{clicked}_of_{n}")
            return {"status": "error",
                    "message": f"only {clicked}/{n} picks applied"
                               + (f" (failed on #{first_missing[0]}: {first_missing[1]})"
                                  if first_missing else "")}
        time.sleep(1.5)
        self._set_jackpot_stake(driver, stake)
        confs = self._find_betslip_confirm(driver)
        if not confs:
            time.sleep(1.5)
            confs = self._find_betslip_confirm(driver)
        if not confs:
            self._dump_ctx(driver, "jackpot_no_submit")
            return {"status": "error", "message": "betslip confirm button not found"}
        btn = confs[0][0]
        try:
            driver.execute_script(
                "arguments[0].scrollIntoView({block:'center', behavior:'instant'});", btn)
        except Exception:
            pass
        try:
            btn.click()
        except Exception:
            try:
                driver.execute_script("arguments[0].click();", btn)
            except Exception as e:
                return {"status": "error", "message": f"could not click confirm: {str(e)[:60]}"}
        time.sleep(4)
        ok = self._jackpot_confirmed(driver)
        if not ok:
            # some builds need a second confirmation step
            again = self._find_betslip_confirm(driver)
            if again:
                try:
                    again[0][0].click()
                    time.sleep(4)
                except Exception:
                    pass
            ok = self._jackpot_confirmed(driver)
        try:
            driver.switch_to.default_content()
        except Exception:
            pass
        if not ok:
            self._dump_ctx(driver, "jackpot_not_confirmed")
            return {"status": "error",
                    "message": "submitted but confirmation text not seen — verify manually"}
        prod = 1.0
        for p in picks:
            try:
                if p.get("pick") == "H":
                    prod *= p["odds"][0]
                elif p.get("pick") == "D":
                    prod *= p["odds"][1]
                else:
                    prod *= p["odds"][2]
            except Exception:
                pass
        return {"status": "ok", "message": "jackpot placed", "count": clicked,
                "product": round(prod, 2), "stake": stake}

    def _record_jackpot_entry(self, pool, picks, stake, res, pool_label):
        prod = float(res.get("product") or 0)
        entry = {
            "id": None,
            "placed_at": datetime.now().isoformat(timespec="seconds"),
            "legs": int(res.get("count") or len(picks)),
            "stake": round(float(stake), 2),
            "odds": round(prod, 2),
            "possible_win": round(prod * float(stake), 2),
            "markets": [f"jackpot-{str(pool_label).lower()}"],
            "probs": [float(p.get("conf") or 0) for p in picks],
            "status": "active",
            "settled_at": None,
            "won_amount": None,
            "recipe": {"legs": int(res.get("count") or len(picks)),
                       "band": self._band_of(prod) if prod else "-",
                       "lead": "jackpot",
                       "mix": f"jackpot-{str(pool_label).lower()}"},
        }
        try:
            self._bets = getattr(self, "_bets", None) or []
            self._bets.append(entry)
            self._save_ledger()
        except Exception as e:
            self._emit_direct(None, f"⚠️ Ledger save hiccup: {str(e)[:80]}")

    def _jackpot_idle_scan(self, phone, password, gui_callback=None):
        """Opportunistic pool analysis during engine idle — fills the machine's
        quiet time, caches predictions so a button press places instantly."""
        if not self._jackpot_lock.acquire(blocking=False):
            return
        driver = None
        try:
            self._emit_direct(gui_callback, "🔎 Idle job: analysing current jackpot pool...")
            driver = self._build_driver(gui_callback=gui_callback, force_visible=True,
                                        mobile=False, headless=False,
                                        capture_perf=False, minimize=True)
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            pool = self._fetch_jackpot_pool(driver, gui_callback=gui_callback)
            if not pool:
                return
            st = self._jackpot_state or {}
            same = (st.get("pool_name") == pool.get("name") and
                    time.time() - (st.get("ts") or 0) < 4 * 3600 and
                    [e.get("match_id") for e in (st.get("pool") or {}).get("events") or []]
                    == [e.get("match_id") for e in pool.get("events") or []])
            if same and st.get("picks"):
                self._emit_direct(gui_callback, self._jackpot_summary(st.get("picks"),
                                                                      pool.get("name")))
                return
            self._emit_direct(gui_callback, "🧠 Analysing games: Poisson model + "
                                            "Over/Under cross-market...")
            picks = self._analyze_jackpot_pool(pool)
            if not picks:
                self._emit_direct(gui_callback, "⚠️ No analysable games found in the pool.")
                return
            self._jackpot_state = {"pool": pool, "picks": picks,
                                   "pool_name": pool.get("name"), "ts": time.time()}
            self._emit_direct(gui_callback, self._jackpot_summary(picks, pool.get("name")))
        except Exception as e:
            self._emit_direct(gui_callback, f"ℹ️ Jackpot idle scan skipped: {str(e)[:90]}")
        finally:
            try:
                if driver is not None:
                    driver.quit()
            except Exception:
                pass
            try:
                self._jackpot_lock.release()
            except Exception:
                pass

    def _jackpot_summary(self, picks, pool_name):
        nH = sum(1 for p in picks if p.get("pick") == "H")
        nD = sum(1 for p in picks if p.get("pick") == "D")
        nA = sum(1 for p in picks if p.get("pick") == "A")
        winp = 1.0
        for p in picks:
            winp *= max(0.01, float(p.get("conf") or 0))
        est = max(2, int(round(1.0 / max(winp, 1e-9))))
        return (f"🎯 {pool_name} JACKPOT analysed: {len(picks)} games → "
                f"{nH}× Home, {nD}× Draw, {nA}× Away | combined win est. ~1/{est:,} "
                f"| press the POT button to place." if pool_name else
                f"🎯 Jackpot analysed: {len(picks)} games → {nH}×Home {nD}×Draw {nA}×Away.")

    def run_jackpot_button(self, phone, password, pool_key="mega", stake=99.0,
                           gui_callback=None):
        """GUI MEGA POT / MID POT handler — dedicated browser (isolated from the
        accumulator engine), guarded balance check, prediction + automatic placement."""
        label = "MIDWEEK" if pool_key == "mid" else "MEGA"
        emoji = "🀄" if pool_key == "mid" else "🎰"
        stake = max(10.0, min(999.0, float(stake) if stake else 99.0))
        if not self._jackpot_lock.acquire(blocking=False):
            self._emit_direct(gui_callback, "⏳ A jackpot flow is already running — try again shortly.")
            return {"status": "busy"}
        driver = None
        try:
            self._emit_direct(gui_callback,
                              f"{emoji} {label} JACKPOT requested — KES {stake:,.0f} entry. "
                              "Opening dedicated session (machine keeps running untouched)...")
            # Wait until the accumulator engine is between rounds so the two flows
            # never place against each other on the same account.
            t0 = time.time()
            while getattr(self, "_engine_busy", False) and time.time() - t0 < 120:
                time.sleep(3)
            driver = self._build_driver(gui_callback=gui_callback, force_visible=True,
                                        mobile=False, headless=False,
                                        capture_perf=False, minimize=True)
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            try:
                balance = self._read_balance_text(driver)
            except Exception:
                balance = 0.0
            self._emit_direct(gui_callback, f"💰 Balance: KES {balance:,.2f}")
            if balance < stake:
                self._emit_direct(gui_callback,
                                  f"💳 Not enough balance (KES {balance:,.2f}) for the "
                                  f"KES {stake:,.0f} {label} entry.")
                return {"status": "no_funds",
                        "needed": round(stake - balance, 2), "balance": balance}
            pool = self._fetch_jackpot_pool(driver, gui_callback=gui_callback)
            if not pool:
                return {"status": "error", "message": "no pool"}
            detected = pool.get("name") or "UNKNOWN"
            if detected not in ("UNKNOWN", "MEGA", "MIDWEEK"):
                detected = "UNKNOWN"
            if detected not in ("UNKNOWN",) and detected.upper() != label.upper():
                self._emit_direct(gui_callback,
                                  f"⚠️ Right now the ACTIVE pool is {detected} (not {label}). "
                                  f"Nothing was placed. Press the {detected} POT button if that's the one "
                                  "you want.")
                return {"status": "bail", "message": f"active pool is {detected}"}
            active = detected if detected != "UNKNOWN" else label
            picks = self._cached_jackpot_picks(pool)
            if not picks:
                self._emit_direct(gui_callback,
                                  f"🧠 {active}: computing per-game prediction "
                                  "(Poisson + cross-market, not blind odds)...")
                picks = self._analyze_jackpot_pool(pool)
            if not picks:
                self._emit_direct(gui_callback, "⚠️ Could not compute picks — no bet placed.")
                return {"status": "error", "message": "no picks"}
            self._emit_direct(gui_callback, self._jackpot_summary(picks, active))
            self._emit_direct(gui_callback,
                              f"🌍 Placing KES {stake:,.0f} {active} JACKPOT "
                              f"({len(picks)} picks, entry 99-style) now...")
            res = self._place_jackpot_on_driver(driver, pool, picks, stake=stake,
                                                gui_callback=gui_callback)
            if res.get("status") == "ok":
                self._record_jackpot_entry(pool, picks, stake, res, active)
                self._jackpot_state = {"pool": pool, "picks": picks,
                                       "pool_name": active, "ts": time.time()}
                note = (f"{emoji} {active} JACKPOT PLACED ✅ KES {stake:,.0f} — "
                        f"{res.get('count')} picks, combined {res.get('product') or '?'}x "
                        f"(book value KES {float(res.get('product') or 0) * stake:,.0f}) "
                        f"— good luck!")
            else:
                note = (f"❌ {active} JACKPOT NOT placed: {res.get('message') or 'unknown'}. "
                        "No money moved; a dump was saved for debugging.")
            self._emit_direct(gui_callback, note)
            return res
        except Exception as e:
            self._emit_direct(gui_callback, f"❌ Jackpot flow crashed: {str(e)[:140]}")
            return {"status": "error", "message": str(e)}
        finally:
            try:
                if driver is not None:
                    driver.quit()
            except Exception:
                pass
            try:
                self._jackpot_lock.release()
            except Exception:
                pass

    # ── No-repeat memory: which (game, market) combos already appear in a betslip ──
    def _load_usage(self):
        if getattr(self, "_used_games", None) is None:
            self._used_games = {}
        try:
            if self.USAGE_PATH.exists():
                data = json.loads(self.USAGE_PATH.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    self._used_games = data
        except Exception:
            pass

    def _save_usage(self):
        try:
            self.USAGE_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.USAGE_PATH.write_text(json.dumps(self._used_games, indent=2), encoding="utf-8")
        except Exception:
            pass

    def _prune_usage(self, max_age_hours: float = 8.0):
        """Drop usage entries older than max_age_hours — those games are long since
        over and can never be re-bet, so they must not block anything."""
        cutoff = datetime.now().timestamp() - max_age_hours * 3600.0
        before = len(self._used_games)
        keep = {}
        for gid, mks in (self._used_games or {}).items():
            fresh = {mk: ts for mk, ts in (mks or {}).items()
                     if not ts or self._ts(ts) > cutoff}
            if fresh:
                keep[gid] = fresh
        if len(keep) != before:
            self._used_games = keep
            self._save_usage()

    @staticmethod
    def _ts(iso) -> float:
        try:
            return datetime.fromisoformat(iso).timestamp()
        except Exception:
            try:
                return datetime.strptime(iso, "%d/%m/%y %H:%M").timestamp()
            except Exception:
                return 0.0

    def _mark_legs_used(self, legs):
        if getattr(self, "_used_games", None) is None:
            self._load_usage()
        for o, name, gid, market, prob in legs:
            m = self._used_games.setdefault(str(gid), {})
            m[market] = datetime.now().isoformat(timespec="seconds")
        self._save_usage()

    # ── Winnings ledger (persisted, survives restarts) ──────────────────────
    def _load_ledger(self):
        if getattr(self, "_bets", None) is None:
            self._bets = []
        try:
            if self.LEDGER_PATH.exists():
                data = json.loads(self.LEDGER_PATH.read_text(encoding="utf-8"))
                if isinstance(data, list):
                    self._bets = data
        except Exception:
            pass

    def _save_ledger(self):
        try:
            self.LEDGER_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.LEDGER_PATH.write_text(json.dumps(self._bets, indent=2), encoding="utf-8")
        except Exception:
            pass

    def _record_bet_from_result(self, res: dict):
        if getattr(self, "_bets", None) is None:
            self._bets = []
        self._bets.append({
            "id": None,
            "placed_at": res.get("placed_at") or datetime.now().isoformat(timespec="seconds"),
            "legs": int(res.get("legs") or 0),
            "stake": round(float(res.get("stake") or 0), 2),
            "odds": round(float(res.get("odds") or 0), 2),
            "possible_win": round(float(res.get("possible_win") or 0), 2),
            "markets": list(res.get("markets") or []),
            "probs": [round(float(p), 4) for p in (res.get("probs") or [])],
            "status": "active",
            "settled_at": None,
            "won_amount": None,
            "recipe": {
                "legs": int(res.get("legs") or 0),
                "band": self._band_of(res.get("odds")),
                "lead": self._lead_bucket(res.get("lead_min")),
                "mix": "-".join(sorted(set(res.get("markets") or []))) or "-",
            },
        })
        self._save_ledger()

    def _ledger_summary(self) -> dict:
        active = won = lost = void = 0
        won_return = 0.0
        staked = 0.0
        for b in getattr(self, "_bets", []) or []:
            st = b.get("status", "active")
            staked += float(b.get("stake") or 0)
            if st == "won":
                won += 1
                won_return += float(b.get("won_amount") or b.get("possible_win") or 0)
            elif st == "lost":
                lost += 1
            elif st == "void":
                void += 1
                won_return += float(b.get("stake") or 0)
            else:
                active += 1
        net_profit = round(won_return - staked, 2)
        return {"placed": len(self._bets), "active": active, "won": won,
                "lost": lost, "void": void, "won_return": round(won_return, 2),
                "staked": round(staked, 2), "net_profit": net_profit}

    # ── Learning engine: the tool grows in intelligence the longer it runs ──
    # Core loop: every settled bet is filed into lifetime stats, per MARKET TYPE
    # (home / btts / over / double_chance / dnb / ...) AND per RECIPE (leg count,
    # odds band, lead-time bucket, market mix). Real hit-rates are compared against
    # the fair probabilities we predicted. Market types that beat prediction are
    # weighted up; ones that lose consistently are retired. Once enough bets have
    # settled, an epsilon-greedy bandit starts steering the odds band toward the
    # top-ROI recipes.
    MIN_BANDIT_SETTLED = 30
    RETIRE_TRIALS = 24          # sample size before we trust a market type
    RETIRE_HINT = 0.06          # real hit-rate must fall this far below predicted
    RECHECK_DAYS = 1

    @staticmethod
    def _band_of(odds: float) -> str:
        """Categorise a slip's combined odds into a recipe band."""
        o = float(odds or 0)
        if o < 3.0:
            return "lt3"
        if o <= 4.0:
            return "3-4"
        if o <= 5.0:
            return "4-5"
        if o <= 6.0:
            return "5-6"
        return "gt6"

    @staticmethod
    def _lead_bucket(mins) -> str:
        try:
            m = int(mins)
        except (TypeError, ValueError):
            return "-"
        if m < 0:
            return "started"
        if m <= 15:
            return "0-15"
        if m <= 45:
            return "16-45"
        return "45+"

    def _load_stats(self):
        if getattr(self, "_stats", None) is None:
            self._stats = {"market_types": {}, "recipes": {}, "retired_markets": [],
                           "settled": 0, "last_recalib": None}
        try:
            if self.STATS_PATH.exists():
                data = json.loads(self.STATS_PATH.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    self._stats = data
        except Exception:
            pass

    def _save_stats(self):
        try:
            self._stats["settled"] = int(self._stats.get("settled") or 0)
            self.STATS_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.STATS_PATH.write_text(json.dumps(self._stats, indent=2), encoding="utf-8")
        except Exception:
            pass

    def _record_settled_stats(self, b: dict):
        """File one settled bet into lifetime stats (market types + recipe).

        Note: an accumulator slip only reports its overall outcome, so a WON slip
        credits every involved market type (all its legs won), and a LOST slip
        debits every involved market type (conservative — any of its legs may have
        failed). This keeps market-type hit-rates honest (lower-bound) over time.
        """
        self._load_stats()
        st = b.get("status", "active")
        if st not in ("won", "lost"):
            return
        markets = b.get("markets") or []
        probs = b.get("probs") or []
        won = 1 if st == "won" else 0
        mt = self._stats.setdefault("market_types", {})
        for i, mk in enumerate(markets):
            e = mt.setdefault(str(mk), {"trials": 0, "won": 0, "expected": 0.0,
                                        "bad_streak": 0, "weight": 1.0})
            e["trials"] = int(e.get("trials") or 0) + 1
            e["won"] = int(e.get("won") or 0) + won
            e["expected"] = float(e.get("expected") or 0.0) + float(probs[i] if i < len(probs) else 0)
        # recipe stats
        key = (b.get("recipe") or
               {"legs": b.get("legs"), "band": self._band_of(b.get("odds")),
                "lead": b.get("lead_bucket") or "-", "mix": "-".join(sorted(set(markets))) or "-"})
        key_s = f"{key.get('legs')}L@{key.get('band')}/{key.get('lead')}/[{key.get('mix')}]"
        r = self._stats.setdefault("recipes", {}).setdefault(
            key_s, {"trials": 0, "won": 0, "stake": 0.0, "ret": 0.0})
        r["trials"] = int(r.get("trials") or 0) + 1
        r["won"] = int(r.get("won") or 0) + won
        r["stake"] = float(r.get("stake") or 0.0) + float(b.get("stake") or 0)
        r["ret"] = float(r.get("ret") or 0.0) + float(b.get("won_amount") or 0)
        self._stats["settled"] = int(self._stats.get("settled") or 0) + 1
        self._maybe_recalibrate()
        self._save_stats()

    def _maybe_recalibrate(self):
        """Daily: recompute market-type weights/retirement + preferred odds band."""
        stats = self._stats
        try:
            last = stats.get("last_recalib")
            if last and (datetime.now() - datetime.fromisoformat(last)).days < self.RECHECK_DAYS:
                return
        except Exception:
            pass
        # market-type calibration vs fair probability
        retired = set(stats.get("retired_markets") or [])
        for mk, e in (stats.get("market_types") or {}).items():
            trials = int(e.get("trials") or 0)
            if trials < self.RETIRE_TRIALS:
                continue
            real = (e.get("won") or 0) / trials
            pred = (e.get("expected") or 0.0) / trials
            deficit = pred - real
            if deficit >= self.RETIRE_HINT:
                e["bad_streak"] = int(e.get("bad_streak") or 0) + 1
                if int(e.get("bad_streak") or 0) >= 2 and mk not in retired:
                    retired.add(mk)
                    self._emit_direct(None,
                                      f"🧠 RETIRING market '{mk}': real hit-rate {real:.0%} "
                                      f"vs predicted {pred:.0%} ({trials} bets)")
            else:
                e["bad_streak"] = 0
                if real >= pred + 0.03:
                    e["weight"] = min(1.5, 1.0 + round((real - pred) * 5, 2))
        stats["retired_markets"] = sorted(retired)
        stats["last_recalib"] = datetime.now().isoformat(timespec="seconds")

    def _market_type_weight(self, mk: str) -> float:
        self._load_stats()
        return float((self._stats.get("market_types") or {}).get(str(mk), {}).get("weight") or 1.0)

    def is_market_retired(self, mk: str) -> bool:
        self._load_stats()
        return str(mk) in (self._stats.get("retired_markets") or [])

    def _bandit_target_range(self, default_lo: float, default_hi: float) -> tuple:
        """Steer the combined-odds window toward the top-ROI band once enough bets
        have settled (epsilon-greedy: 15% exploration, otherwise best observed ROI)."""
        self._load_stats()
        settled = int(self._stats.get("settled") or 0)
        if settled < self.MIN_BANDIT_SETTLED:
            return float(default_lo), float(default_hi)
        bands = {"3-4": (3.0, 4.0), "4-5": (4.0, 5.0), "5-6": (5.0, 6.0)}
        recs = self._stats.get("recipes") or {}
        eligible = {}
        for k, v in recs.items():
            if "@" not in k:
                continue
            band = k.split("@")[1].split("/")[0]
            if band not in bands:
                continue
            if int(v.get("trials") or 0) >= 5:
                roi = ((v.get("ret") or 0.0) - (v.get("stake") or 0.0)) / max(1e-9, (v.get("stake") or 0.0))
                eligible.setdefault(band, []).append(roi)
        if not eligible:
            return float(default_lo), float(default_hi)
        import random
        eps = 0.15
        if random.random() < eps:
            band = random.choice(list(bands))
        else:
            band = max(eligible, key=lambda b: sum(eligible[b]) / len(eligible[b]))
        lo, hi = bands[band]
        prev = getattr(self, "_bandit_banner", None)
        if prev != (band, settled):
            self._bandit_banner = (band, settled)
            self._emit_direct(None, f"🎰 Bandit steering to {band} ({lo:g}-{hi:g}) "
                                    f"[{settled} settled bets learned]")
        # never leave the caller's safe overall window
        return max(float(default_lo), lo), min(float(default_hi), hi)

    # ── Bet History scraping for win monitoring ─────────────────────────────
    def _extract_bet_history(self, driver) -> list[dict]:
        """Parse the Bet History page (.bet-container rows) into normalized records."""
        try:
            rows = driver.execute_script(r"""
var out = [];
document.querySelectorAll('.bet-container').forEach(function(c){
   var pick = function(sel){ var e = c.querySelector(sel); return e ? (e.innerText||'').trim() : ''; };
   out.push({
      id: pick('.bet_id').replace(/Bet ID\s*[:#]?\s*/i,'').trim(),
      date: pick('.bet_date').replace(/Date of bet\s*[:#]?\s*/i,'').trim(),
      desc: pick('.bet_description').replace(/Description\s*[:#]?\s*/i,'').trim(),
      amount: pick('.bet_amount').replace(/Bet amount\s*[:#]?\s*/i,'').trim(),
      win: pick('.bet_winnings').replace(/Possible Win\s*[:#]?\s*/i,'').trim(),
      status: pick('.bet_status').replace(/Bet status\s*[:#]?\s*/i,'').trim()
   });
});
return out;
""")
        except Exception:
            return []
        parsed = []
        for r in rows or []:
            def money(s):
                m = re.search(r"([0-9][0-9,]*\.?[0-9]{0,2})", s or "")
                if not m:
                    return None
                return round(float(m.group(1).replace(",", "")), 2)
            legs_m = re.search(r"\((\d+)\)", r.get("desc") or "")
            parsed.append({
                "id": str(r.get("id") or "").strip(),
                "date": (r.get("date") or "").strip(),
                "legs": int(legs_m.group(1)) if legs_m else 0,
                "stake": money(r.get("amount")),
                "win": money(r.get("win")),
                "status": (r.get("status") or "").strip(),
            })
        return parsed

    def _normalize_bet_status(self, raw: str) -> str:
        t = (raw or "").lower()
        if "refund" in t or "cancel" in t:
            return "void"
        if "won" in t and "not" not in t:
            return "won"
        if "not won" in t or "lost" in t:
            return "lost"
        return "active"

    def _match_ledger_bet(self, row: dict, placed_at_iso: str, stake, possible_win):
        """Return the seconds between the site row time and our placement time when
        the row plausibly IS our placed bet (same legs/stake/possible win), else None."""
        try:
            drow = datetime.strptime(row["date"], "%d/%m/%y %H:%M")
        except Exception:
            return None
        try:
            dplaced = datetime.fromisoformat(placed_at_iso)
        except Exception:
            return None
        diff = (dplaced - drow).total_seconds()
        if abs(diff) > 900:
            return None
        if abs((row.get("stake") if row.get("stake") is not None else 0) - float(stake)) > 0.01:
            return None
        if abs((row.get("win") if row.get("win") is not None else 0) - float(possible_win)) > 0.02:
            return None
        return abs(diff)

    def _backfill_bet_ids(self, driver, gui_callback=None) -> int:
        """Resolve real platform Bet IDs for freshly-placed ledger bets (id=None)
        by matching against Bet History, without settling statuses."""
        try:
            self._safe_get(driver, self.BETS_HISTORY_URL)
        except Exception:
            return 0
        time.sleep(1.2)
        try:
            rows = self._extract_bet_history(driver)
        except Exception:
            rows = []
        filled = 0
        for b in getattr(self, "_bets", []):
            if b.get("id"):
                continue
            best_id, best_diff = None, None
            for r in rows:
                if b.get("legs") != r.get("legs"):
                    continue
                diff = self._match_ledger_bet(r, b.get("placed_at", ""),
                                              b.get("stake") or 0,
                                              b.get("possible_win") or 0)
                if diff is not None and (best_diff is None or diff < best_diff):
                    best_id, best_diff = r["id"], diff
            if best_id:
                b["id"] = best_id
                filled += 1
        if filled:
            self._save_ledger()
            self._emit_direct(gui_callback, f"🔗 Bet ID backfilled for {filled} placed bet(s)")
        return filled

    def _monitor_and_sync_winnings(self, driver, gui_callback=None) -> dict:
        """Open Bet History, settle ledger entries and emit WON / LOST events."""
        self._safe_get(driver, self.BETS_HISTORY_URL)
        time.sleep(1.5)
        rows = self._extract_bet_history(driver)
        if not rows:
            return self._ledger_summary()
        site = {}
        for r in rows:
            if r["id"]:
                site[r["id"]] = r
        changed = False
        for b in getattr(self, "_bets", []) or []:
            # attach id to freshly-placed bets by (legs, date, stake, possible win)
            if not b.get("id"):
                best_id = None
                best_diff = None
                for r in rows:
                    if b.get("legs") != r.get("legs"):
                        continue
                    diff = self._match_ledger_bet(r, b.get("placed_at", ""),
                                                  b.get("stake") or 0,
                                                  b.get("possible_win") or 0)
                    if diff is not None and (best_diff is None or diff < best_diff):
                        best_id = r["id"]
                        best_diff = diff
                if best_id:
                    b["id"] = best_id
                    changed = True
            row = site.get(str(b.get("id"))) if b.get("id") else None
            if not row:
                continue
            new_status = self._normalize_bet_status(row.get("status"))
            old_status = b.get("status", "active")
            if old_status in ("won", "lost", "void") or new_status == old_status:
                continue
            b["status"] = new_status
            b["settled_at"] = datetime.now().isoformat(timespec="seconds")
            changed = True
            self._record_settled_stats(b)
            if new_status == "won":
                w = row.get("win") if row.get("win") is not None else b.get("possible_win")
                b["won_amount"] = w
                profit = round((w or 0) - (b.get("stake") or 0), 2)
                self._emit_direct(gui_callback,
                                  f"🏆 WON! Bet #{b.get('id')} → +KES {w:,.2f} "
                                  f"(back KES {(b.get('stake') or 0):,.2f} + KES {profit:,.2f} profit)")
                if (w or 0) > 0:
                    self._load_stats()
                    share = float(self._stats.get("pool_share") or self.DEFAULT_POOL_SHARE)
                    bank = round((w or 0) * share, 2)
                    new_pool = self._credit_pool(bank)
                    self._emit_direct(gui_callback,
                                      f"💰 Savings: +KES {bank:,.2f} banked ({share * 100:.0f}% of the win) "
                                      f"→ reserve KES {new_pool:,.2f} ({'ready to auto-withdraw' if new_pool >= 200.0 else 'toward 200'})")
            elif new_status == "lost":
                self._emit_direct(gui_callback,
                                  f"❌ LOST Bet #{b.get('id')} (−KES {(b.get('stake') or 0):,.2f})")
            elif new_status == "void":
                self._emit_direct(gui_callback,
                                  f"♻️ {row.get('status')} Bet #{b.get('id')} (stake returned)")
        if changed:
            self._save_ledger()
        summary = self._ledger_summary()
        self._emit_direct(gui_callback,
                          f"📊 Winnings: {summary['won']} won (+KES {summary['won_return']:,.2f}) | "
                          f"{summary['lost']} lost | {summary['void']} void | "
                          f"{summary['active']} active | net {summary['net_profit']:+,.2f}")
        return summary

    def _today_won_amount(self) -> float:
        """Sum of won_amount across ledger bets settled today."""
        today = datetime.now().strftime("%Y-%m-%d")
        total = 0.0
        for b in getattr(self, "_bets", []) or []:
            if (b.get("status") == "won" and b.get("won_amount")
                    and (b.get("settled_at") or "").startswith(today)):
                total += float(b.get("won_amount") or 0.0)
        return round(total, 2)

    def _auto_withdraw_env(self) -> dict:
        try:
            with open(self.WITHDRAW_PATH, "r", encoding="utf-8") as fh:
                return json.loads(fh.read() or "{}") or {}
        except Exception:
            return {}

    def _save_auto_withdraw_env(self, env: dict) -> None:
        try:
            with open(self.WITHDRAW_PATH, "w", encoding="utf-8") as fh:
                fh.write(json.dumps(env, indent=2))
        except Exception as e:
            self._emit_direct(None, f"⚠️ Auto-withdraw marker save failed: {str(e)[:80]}")

    def _maybe_auto_withdraw(self, phone: str, password: str,
                             amount: float = 200.0, in_flight_key: str = "auto",
                             pool: float = 0.0, gui_callback=None) -> bool:
        """Once per calendar day, if the auto-withdraw condition is met, fire a
        background withdrawal of that amount.

        Condition (either is enough):
          - `pool > 0`  : the SAVINGS reserve reached *amount* (even if the wins
                          that built it were spread over several days), or
          - legacy       : today's settled winnings alone cover *amount*.

        Runs the browser withdraw on a daemon thread so the 24/7 betting engine is
        never blocked. Returns True when a withdrawal was triggered.
        """
        if not phone or not password or not amount or amount <= 0:
            return False
        if getattr(self, "_auto_withdraw_flags", {}).get(in_flight_key) is True:
            return False
        today = datetime.now().strftime("%Y-%m-%d")
        env = self._auto_withdraw_env()
        last_done = env.get("last_auto_withdraw") or ""
        done_key = f"{last_done}:{in_flight_key}"
        if done_key == f"{today}:{in_flight_key}":
            return False
        pool = float(pool or 0.0)
        if pool > 0:
            if pool < float(amount):
                return False
            trigger = pool
        else:
            win_today = self._today_won_amount()
            if win_today < float(amount):
                return False
            trigger = win_today
        self._auto_withdraw_flags = getattr(self, "_auto_withdraw_flags", {})
        self._auto_withdraw_flags[in_flight_key] = True
        to_withdraw = min(float(amount), trigger)

        def _job():
            try:
                self._emit_direct(gui_callback,
                                  f"💰 AUTO-WITHDRAW: {'savings reserve KES '+f'{trigger:,.2f}' if pool > 0 else 'today +KES '+f'{trigger:,.2f}'} — "
                                  f"withdrawing KES {to_withdraw:,.0f} (daily, once).")
                res = self.withdraw_funds_browser([phone], password, to_withdraw,
                                                  gui_callback=gui_callback)
                ok = isinstance(res, list) and res and res[0].get("status") == "success"
                if not ok:
                    self._emit_direct(gui_callback,
                                      f"⚠️ Auto-withdraw didn't confirm on the site: "
                                      f"{str(res)[:120]}")
                else:
                    if pool > 0:
                        self._credit_pool(-float(trigger))
                        self._emit_direct(gui_callback,
                                          "💰 Reserve recycles — the KES 200 savings moved out, "
                                          "pool resets and keeps banking new wins.")
                    env["last_auto_withdraw"] = today
                    self._save_auto_withdraw_env(env)
                    self._emit_direct(gui_callback,
                                      f"✅ Daily auto-withdraw done — KES {to_withdraw:,.0f} "
                                      "is on its way out.")
            except Exception as e:
                self._emit_direct(gui_callback,
                                  f"⚠️ Auto-withdraw crashed: {str(e)[:120]}")
            finally:
                try:
                    self._auto_withdraw_flags[in_flight_key] = False
                except Exception:
                    pass

        import threading
        threading.Thread(target=_job, daemon=True).start()
        return True

    def _parse_sportpesa_kickoff(self, raw) -> datetime | None:
        """Parse SportPesa kick-off text like '09/09/26 - 17:00' (or ISO) into a datetime."""
        if not raw:
            return None
        raw = str(raw).strip()
        for fmt in ("%d/%m/%y - %H:%M", "%d/%m/%Y - %H:%M",
                    "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d %H:%M", "%d/%m/%y %H:%M"):
            try:
                return datetime.strptime(raw, fmt)
            except (ValueError, TypeError):
                continue
        m = re.search(r"(\d{2})/(\d{2})/(\d{2})\s*[-–—]?\s*(\d{1,2}):(\d{2})", raw)
        if m:
            dd, mm, yy, hh, mi = m.groups()
            try:
                return datetime(int("20" + yy), int(mm), int(dd), int(hh), int(mi))
            except ValueError:
                return None
        return None

    def _scroll_to_load_more_games(self, driver, max_scrolls: int = 6,
                                   gui_callback=None) -> int:
        """Crawl the listing: scroll the page + inner containers to trigger the
        infinite-scroll / pagination, so we capture as many placeable games as possible.

        Returns the number of .event-row rows visible after crawling.
        """
        for i in range(max_scrolls):
            driver.execute_script(r"""
window.scrollTo(0, document.body.scrollHeight);
var scr = document.querySelectorAll('.event-sports__row, .event-sports__sticky, [class*="event-list"], [class*="scroll"], .data-live-scroll, main, [role="main"], .container, .content, .event-tabs-holder__content');
for (var s = 0; s < scr.length; s++) {
    var el = scr[s];
    if (el.scrollHeight > el.clientHeight + 40) {
        el.scrollTop = el.scrollHeight;
    }
}
if (document.documentElement) document.documentElement.scrollTop = document.documentElement.scrollHeight;
return true;
""")
            time.sleep(1.5)
            count = driver.execute_script(
                "return document.querySelectorAll('.event-row:not(.event-row-header)').length;")
            if i >= 2 and count == last:
                break
            last = count
        self._emit_direct(gui_callback, f"  🔎 crawled listing — {count or 0} event rows loaded")
        return count or 0

    def _extract_dom_games(self, driver) -> list[dict]:
        """Read today's game rows: kick-off time, teams and per-market odds.

        Markets captured per game:
          - home_odds : "3 Way" market, HOME selection
          - btts_yes  : "Both Teams To Score", YES selection
          - over_25   : "Over/Under 2.5", OVER selection
        """
        rows = driver.execute_script(r"""
var results = [];
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
for (var r = 0; r < rows.length; r++) {
    var row = rows[r];
    var text = (row.innerText || '').replace(/\s+/g, ' ');
    var names = row.querySelectorAll('.event-names .event-text');
    var nameList = [];
    var skip = { '3 WAY': 1, '2 WAY': 1, '1X2': 1, 'MATCH': 1, 'MATCH WINNER': 1,
                 'OVER/UNDER': 1, 'OVER': 1, 'UNDER': 1, 'BOTH TEAMS TO SCORE': 1,
                 'HANDICAP': 1, 'DOUBLE CHANCE': 1, 'FIRST TEAM TO SCORE': 1,
                 'DRAW': 1, 'YES': 1, 'NO': 1, '1': 1, '2': 1, 'X': 1 };
    function firstLine(v) { return (v || '').split(/[\n\r]+/)[0].trim(); }
    function isLabel(v) {
        var up = firstLine(v).toUpperCase();
        return skip[up] || up.indexOf('==') >= 0;
    }
    for (var n = 0; n < names.length; n++) {
        var v = (names[n].innerText || '').trim();
        if (v && !names[n].classList.contains('placeholder') && !isLabel(v)) nameList.push(v);
    }
    var home = nameList.length > 0 ? nameList[0] : '';
    var away = nameList.length > 1 ? nameList[1] : '';
    if (!home && !away) {
        var filtered = [];
        var all = row.querySelectorAll('.event-text');
        for (var a = 0; a < all.length && filtered.length < 2; a++) {
            var el = all[a];
            var v2 = (el.innerText || '').trim();
            if (!v2 || el.classList.contains('placeholder')) continue;
            if (isLabel(v2)) continue;
            filtered.push(v2);
        }
        home = filtered.length > 0 ? filtered[0] : '';
        away = filtered.length > 1 ? filtered[1] : '';
    }
    if (!home && !away) continue;

    // Pull odds per market from the row's .event-market blocks
    var markets = row.querySelectorAll('.event-market');
    var homeOdds = '', bttsYes = '', over25 = '';
    var h3 = [], btts2 = [], ou2 = [];
    for (var i = 0; i < markets.length; i++) {
        var m = markets[i];
        var nameEl = m.querySelector('.event-market-name');
        var nm = nameEl ? (nameEl.innerText || '').trim().toUpperCase() : '';
        var sels = m.querySelectorAll('.event-selection:not(.placeholder):not(.event-selection-disabled)');
        function oddAt(idx) { return sels.length > idx ? (sels[idx].innerText || '').trim() : ''; }
        function collect(target, n) { for (var v = 0; v < Math.min(n, sels.length); v++) target.push(oddAt(v)); }
        if (nm.indexOf('3 WAY') >= 0) {
            if (!homeOdds) homeOdds = oddAt(0);
            collect(h3, 3);
        } else if (nm.indexOf('BOTH TEAMS') >= 0) {
            if (!bttsYes) bttsYes = oddAt(0);
            collect(btts2, 2);
        } else if (nm.indexOf('OVER/UNDER') >= 0) {
            if (!over25) over25 = oddAt(0);
            collect(ou2, 2);
        }
    }
    if (!homeOdds && !bttsYes && !over25) continue;

    var idMatch = text.match(/ID:\s*(\d+)/i);
    var timeMatch = text.match(/(\d{2}\/\d{2}\/\d{2})\s*-\s*(\d{1,2}:\d{2})/);
    results.push({
        id: idMatch ? idMatch[1] : '',
        rawTime: timeMatch ? timeMatch[1] + ' - ' + timeMatch[2] : '',
        home: home,
        away: away,
        homeOdds: homeOdds,
        bttsYes: bttsYes,
        over25: over25,
        h3: h3,
        btts2: btts2,
        ou2: ou2
    });
}
return results;
""")
        games = []
        for g in rows or []:
            name = f"{g.get('home', '').strip()} vs {g.get('away', '').strip()}"

            def _f(key):
                try:
                    return float((g.get(key) or "").replace(",", ""))
                except (TypeError, ValueError):
                    return None

            def _fl(key):
                out = []
                for v in g.get(key) or []:
                    try:
                        f = float(str(v).replace(",", ""))
                    except (TypeError, ValueError):
                        continue
                    if f:
                        out.append(f)
                return out

            games.append({
                "id": str(g.get("id") or ""),
                "name": name,
                "home": g.get("home", "").strip(),
                "away": g.get("away", "").strip(),
                "home_odds": _f("homeOdds"),
                "btts_yes": _f("bttsYes"),
                "over_25": _f("over25"),
                "h3": _fl("h3"),
                "btts": _fl("btts2"),
                "ou": _fl("ou2"),
                "start": self._parse_sportpesa_kickoff(g.get("rawTime")),
                "start_raw": g.get("rawTime") or "",
            })
        return games

    # ── Full market list for one game (↗ the "26 ›" expander) ───────────────
    def _close_analysis_pages(self, driver, gui_callback=None):
        """Close the H2H/analysis overlay — the 'network'-looking icon just below the
        market expander. It opens its own page/modal (game preview, stats, head-to
        head, Betradar widget) and must be closed as a page afterwards, otherwise it
        blocks the site scripts and makes the session feel frozen/hung."""
        try:
            handles = driver.window_handles
            while len(handles) > 1:
                driver.switch_to.window(handles[-1])
                try:
                    driver.close()
                except Exception:
                    break
                handles = driver.window_handles
            if handles:
                driver.switch_to.window(handles[0])
        except Exception:
            try:
                if driver.window_handles:
                    driver.switch_to.window(driver.window_handles[0])
            except Exception:
                pass
        close_js = [
            "var x=document.querySelectorAll('[ng-click*=close],[ng-click*=Close],[ng-click*=close_]');"  # noqa: E501
            "for(var i=0;i<x.length;i++){var v=(x[i].getAttribute('ng-click')||'');"
            "if(/close/i.test(v)){x[i].click();return true;}}return false;",
            "var b=document.querySelector('.modal-close,.close-btn,.ui-dialog-titlebar-close,.btn-close,[data-dismiss=modal]');"
            "if(b){b.click();return true;}return false;",
        ]
        for js in close_js:
            try:
                if driver.execute_script(js):
                    break
            except Exception:
                pass
        try:
            driver.switch_to.active_element.send_keys(Keys.ESCAPE)
        except Exception:
            pass

    def _extract_full_markets(self, driver) -> list:
        """Parse every market panel on a game /markets page.

        Returns [{name, selections: [{name, odds}]}] — includes DOUBLE CHANCE,
        DRAW NO BET, 1X2 variants, every Total-Over/Under line and combos.
        """
        raw = driver.execute_script(r"""
var out = [];
var els = document.querySelectorAll('.event-market');
for (var i = 0; i < els.length; i++) {
    var m = els[i];
    var nameEl = m.querySelector('.event-market-name');
    var name = nameEl ? (nameEl.innerText || '').replace(/\s+/g, ' ').trim() : '';
    var sels = [];
    var ss = m.querySelectorAll('.event-selection:not(.placeholder)');
    for (var s = 0; s < ss.length; s++) {
        if (/disabled/i.test(ss[s].className || '')) continue;
        sels.push((ss[s].innerText || '').replace(/\s+/g, ' ').trim());
    }
    if (!name || !sels.length) continue;
    out.push({ name: name, sels: sels });
}
return JSON.stringify(out);
""")
        markets = []
        try:
            raw_list = json.loads(raw or "[]")
        except Exception:
            return markets
        for m in raw_list or []:
            selections = []
            for txt in m.get("sels") or []:
                odds = None
                mt = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*$", txt)
                if mt:
                    try:
                        odds = float(mt.group(1))
                    except ValueError:
                        odds = None
                    name = (txt[: mt.start()]).strip()
                else:
                    name = txt
                selections.append({"name": name, "odds": odds})
            markets.append({"name": (m.get("name") or "").strip(), "selections": selections})
        return markets

    def _open_game_full_markets(self, driver, gid=None, timeout: int = 45, gui_callback=None) -> dict:
        """Open the FULL market list for one game (Double Chance, DNB, 1X2, all the
        Over/Under lines, combos...). Clicks the game's 'more-markets' arrow (the
        '26 ›' expander — NOT the 'network' H2H/analysis icon below it).

        If we are already on a /games/N/markets page, it just parses it. Returns
        {status, url, markets} with markets = [{name, selections:[{name, odds}]}].
        """
        url = ""
        if "/games/" in (driver.current_url or "") and "/markets" in (driver.current_url or ""):
            try:
                url = driver.current_url
            except Exception:
                url = ""
        else:
            try:
                clicked = driver.execute_script(r"""
var gid = arguments[0] || null;
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
var target = null;
if (gid) {
    for (var r = 0; r < rows.length; r++) {
        if ((rows[r].innerText || '').indexOf('ID: ' + gid) >= 0) { target = rows[r]; break; }
    }
}
if (!target) {
    for (var r = 0; r < rows.length; r++) {
        if (rows[r].offsetHeight > 0) { target = rows[r]; break; }
    }
}
if (!target) return 'norow';
var el = target.querySelector('.event-more-markets');
if (!el) return 'noarrow';
el.click();
return 'clicked';
""", gid)
                self._emit_direct(gui_callback,
                                  f"↗ Full-markets opener: {clicked}"
                                  if clicked != "clicked" else "")
            except Exception:
                pass
            # wait for the /markets route + market panels to render (renderer-safe)
            deadline = time.time() + float(timeout)
            while time.time() < deadline:
                try:
                    url = driver.current_url
                    if "/games/" in url and "/markets" in url:
                        n = driver.execute_script(
                            "return document.querySelectorAll('.event-market').length;")
                        if n and n >= 3:
                            break
                except Exception:
                    pass
                time.sleep(1)
            time.sleep(1)
            self._close_analysis_pages(driver, gui_callback=gui_callback)
        markets = self._extract_full_markets(driver)
        return {"status": "ok", "url": url, "markets": markets}

    def _dump_full_markets_text(self, markets, max_markets: int = 40) -> list[str]:
        """Human-readable lines for the GUI log: 'MARKET — selection @ odds'."""
        lines = []
        for m in (markets or [])[:max_markets]:
            parts = ", ".join(
                f"{s.get('name', '')} @ {s.get('odds', '')}" for s in m.get("selections") or [])
            lines.append(f"▸ {m.get('name', '').upper()}: {parts}")
        return lines

    @staticmethod
    def _fair_win_probs(odds_list) -> list | None:
        """Convert a bookmaker odds list into margin-corrected win probabilities.

        Bookmaker odds imply probabilities that SUM TO MORE than 1 (the bookmaker's
        margin/overround). Dividing by the sum re-normalises them so the result sums
        to exactly 1 — an unbiased estimate of the true outcome likelihood.
        """
        ps = []
        for o in odds_list or []:
            try:
                o = float(o)
            except (TypeError, ValueError):
                continue
            if o and o > 1.0:
                ps.append(1.0 / o)
        if len(ps) < 2:
            return None
        s = sum(ps)
        return [p / s for p in ps]

    def _select_football_legs(self, games, target_min: float = 3.0, target_max: float = 6.0,
                              odds_cap: float = 6.0, max_legs: int = 6, min_legs: int = 3,
                              used=(), prefer_more_legs: bool = False,
                              gui_callback=None) -> tuple:
        """Pick the accumulator legs MOST LIKELY TO WIN while meeting the payout target.

        Strategy (not random picks): the bookmaker's odds already summarise every
        market's informed opinion. We convert the odds to win probabilities and strip
        the bookmaker's margin (_fair_win_probs), which makes the probabilities honest.
        For each game we take the SINGLE most likely selection across three markets:

- home    : "3 Way" market, HOME win
  - btts    : "Both Teams To Score", YES
  - over    : "Over/Under 2.5", OVER

        Then we search every min_legs..max_legs combination of those selections whose
        combined odds sit inside the [target_min, target_max] window and pick the one
        with the HIGHEST combined win probability (product of margin-corrected per-leg
        probs). Ties are broken by combined odds closest to the middle of the target
        window. If nothing lands in range, we fall back to the least-risky near-miss
        (highest combined probability below target_max * 1.1, closest to target_min).
        min_legs defaults to 3 because SportPesa rejects slips with fewer than 3
        selections ("Not valid").

        Returns (legs, product) where legs is a list of
        (odds, display_name, game_id, market, win_prob) tuples, or (None, 0.0).
        """
        # One most-likely selection per game (a game already bet today is SKIPPED
        # entirely — the same match must never appear again in a different slip.
        # Market types that beat prediction are weighted up; ones that keep losing
        # vs their predicted fair probability are retired by the learning engine.)
        used_set = set(used) if used else set()
        self._load_stats()
        per_game = {}
        for g in games:
            gid = g.get("id", "")
            h3 = self._fair_win_probs(g.get("h3")) or []
            btts = self._fair_win_probs(g.get("btts")) or []
            ou = self._fair_win_probs(g.get("ou")) or []
            options = []
            if h3 and isinstance(g.get("home_odds"), (int, float)):
                options.append((g["home_odds"], h3[0], "home", ""))
            if btts and isinstance(g.get("btts_yes"), (int, float)):
                options.append((g["btts_yes"], btts[0], "btts", " BTTS:YES"))
            if ou and isinstance(g.get("over_25"), (int, float)):
                options.append((g["over_25"], ou[0], "over", " O/U 2.5 OVER"))
            valid = []
            for o, p, mk, suf in options:
                if not (1.01 < o <= odds_cap):
                    continue
                if str(gid) in used_set:
                    continue
                if self.is_market_retired(mk):
                    continue
                valid.append((o, p * self._market_type_weight(mk), p, mk, suf))
            if not valid:
                continue
            # most likely to win among the still-free markets (weighted by what we've learned)
            valid.sort(key=lambda c: c[1], reverse=True)
            o, _w, p, mk, suf = valid[0]
            per_game[gid] = (o, f"{g.get('name', '')}{suf}", gid, mk, p)

        cands = list(per_game.values())
        if len(cands) < min_legs:
            return None, 0.0
        cands.sort(key=lambda c: c[0])
        pool = cands[: min(len(cands), max_legs + 5)]
        mid = (target_min + target_max) / 2.0
        lo = target_min
        hi = target_max * 1.10

        import itertools

        def _joint(combo):
            prod_o = 1.0
            prod_p = 1.0
            for c in combo:
                prod_o *= c[0]
                prod_p *= c[4]
            return prod_o, prod_p

        best = None
        best_rank = None
        for size in range(min_legs, max_legs + 1):
            if len(pool) < size:
                break
            for combo in itertools.combinations(pool, size):
                prod_o, prod_p = _joint(combo)
                if prod_o < lo or prod_o > hi:
                    continue
                # Long-shot mode: use AS MANY games as possible to build the big
                # multi-match ticket; otherwise prefer the highest win probability.
                if prefer_more_legs:
                    rank = (len(combo), prod_p, -abs(prod_o - mid))
                else:
                    rank = (prod_p, -abs(prod_o - mid))
                if best_rank is None or rank > best_rank:
                    best_rank = rank
                    best = (combo, prod_o)
        if best is None and pool:
            tightest = None
            tightest_rank = None
            for size in range(min_legs, max_legs + 1):
                if len(pool) < size:
                    break
                for combo in itertools.combinations(pool, size):
                    prod_o, prod_p = _joint(combo)
                    if prod_o > target_max * 1.1:
                        continue
                    # closest to target_min, highest probability wins ties
                    if prefer_more_legs:
                        rank = (len(combo), -abs(prod_o - target_min), prod_p)
                    else:
                        rank = (-abs(prod_o - target_min), prod_p)
                    if tightest_rank is None or rank > tightest_rank:
                        tightest_rank = rank
                        tightest = (combo, prod_o)
            if tightest:
                best = tightest
        if best:
            return best
        return None, 0.0

    def _click_selected_legs(self, driver, legs, gui_callback=None) -> int:
        """Click the right per-market odd for each leg (by event ID, then market name)."""
        count = 0
        for odds, name, gid, market, prob in legs:
            home = name.split(" vs ")[0].strip() if " vs " in name else str(name).strip()
            ok = driver.execute_script(r"""
var home = arguments[0];
var gid = arguments[1];
var market = arguments[2];
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
function marketTarget(row) {
    var query = '';
    if (market === 'home') query = '3 WAY';
    else if (market === 'btts') query = 'BOTH TEAMS';
    else if (market === 'over') query = 'OVER/UNDER';
    if (!query) return null;
    var markets = row.querySelectorAll('.event-market');
    for (var i = 0; i < markets.length; i++) {
        var m = markets[i];
        var nmEl = m.querySelector('.event-market-name');
        var nm = nmEl ? (nmEl.innerText || '').trim().toUpperCase() : '';
        if (nm.indexOf(query) < 0) continue;
        var sels = m.querySelectorAll('.event-selection:not(.placeholder):not(.event-selection-disabled)');
        if (sels.length > 0) return sels[0];
    }
    return null;
}
function pick(row) {
    var sel = marketTarget(row);
    if (!sel) return false;
    if (!sel.classList.contains('event-selection-picked')) {
        try { sel.click(); } catch (e) { return false; }
    }
    return true;
}
for (var r = 0; r < rows.length; r++) {
    var row = rows[r];
    if (gid && (row.innerText || '').indexOf('ID: ' + gid) >= 0) {
        if (pick(row)) return true;
    }
}
for (var r = 0; r < rows.length; r++) {
    var row = rows[r];
    var names = row.querySelectorAll('.event-names .event-text');
    var h = names.length > 0 ? (names[0].innerText || '').trim() : '';
    if (h && h.toUpperCase() === home.toUpperCase()) {
        if (pick(row)) return true;
    }
}
return false;
""", home, gid, market)
            if ok:
                count += 1
                self._emit_direct(gui_callback, f"   ✅ {name} [{market}] @{odds:.2f} selected")
            else:
                self._emit_direct(gui_callback, f"   ⚠️ Could not find/click {name}")
            time.sleep(0.3)
        return count

    def _read_balance_text(self, driver) -> float:
        """Read the wallet balance from the page (skip bet figures like POSSIBLE WIN)."""
        val = driver.execute_script("""
var b = document.body.innerText || '';
var re = /(?:KSH|KES)\\s*([0-9][0-9,]*(?:\\.[0-9]{1,2})?)/gi;
var ms = [];
var m;
while ((m = re.exec(b))) ms.push({ v: m[1].replace(/[, ]/g, ''), i: m.index });
for (var k = 0; k < ms.length; k++) {
    var before = b.substring(Math.max(0, ms[k].i - 30), ms[k].i).toUpperCase();
    if (/(POSSIBLE|TOTAL|STAKE|AMOUNT|WIN|ODDS|SELEC\\.?)/.test(before)) continue;
    return ms[k].v;
}
return '';
""")
        try:
            return float(val or 0)
        except (TypeError, ValueError):
            return 0.0

    def _read_betslip_totals(self, driver) -> dict:
        """Return {odds, win} parsed from the open betslip panel text."""
        raw = driver.execute_script("""
var form = document.querySelector('form.live-betslip');
if (!form) return null;
var t = form.innerText || '';
var out = { odds: null, win: null };
var mO = t.match(/TOTAL ODDS[:\\s]*([0-9][0-9.,]*)/i);
if (mO) out.odds = mO[1].replace(/,/g, '');
var mW = t.match(/POSSIBLE WIN[^0-9]*([0-9][0-9,.]*)/i);
if (mW) out.win = mW[1].replace(/\\s/g, '');
return out;
""")
        if not raw:
            return {"odds": None, "win": None}
        for key in ("odds", "win"):
            try:
                raw[key] = float(raw[key]) if raw[key] else None
            except (TypeError, ValueError):
                raw[key] = None
        return raw

    def _read_betslip_stake_derived(self, driver):
        """Derive the current stake from the slip totals (possible win / total odds)."""
        try:
            t = self._read_betslip_totals(driver)
            odds = float(t.get("odds") or 0)
            win = float(t.get("win") or 0)
        except (TypeError, ValueError):
            return None
        if odds > 0 and win > 0:
            return round(win / odds, 2)
        return None

    def _locate_stake_input(self, driver):
        """Return the betslip stake input (data-qa/name/id/placeholder hints first,
        then an input near a stake/amount/label, then any visible input)."""
        return driver.execute_script("""
var form = document.querySelector('form.live-betslip');
if (!form) return null;
var cands = form.querySelectorAll('input');
for (var i = 0; i < cands.length; i++) {
    var el = cands[i];
    var qa = ((el.getAttribute('data-qa')||'')+' '+(el.name||'')+' '+(el.id||'')+' '+
              (el.getAttribute('placeholder')||'')+' '+(el.className||'')).toLowerCase();
    if (/stake|amount/.test(qa) && el.type !== 'hidden') return el;
}
var labs = form.querySelectorAll('label,span,div');
for (var i = 0; i < labs.length; i++) {
    var t = (labs[i].innerText || labs[i].textContent || '').trim().toLowerCase();
    if (!/stake|amount|kes/.test(t)) continue;
    var ns = labs[i].querySelectorAll('input');
    for (var j = 0; j < ns.length; j++) if (ns[j].type !== 'hidden') return ns[j];
}
for (var i = 0; i < cands.length; i++) {
    var el = cands[i];
    if (el.type === 'hidden') continue;
    var r = el.getBoundingClientRect();
    if (r.width > 0 && r.height > 0) return el;
}
return null;
""")

    def _read_stake_input(self, driver):
        """Read the numeric stake currently shown in the betslip amount input."""
        el = self._locate_stake_input(driver)
        if not el:
            return None
        try:
            val = el.get_attribute("value")
            if val is None or val == "":
                val = el.get_attribute("value")
            if val is None or val == "":
                return None
            return float(str(val).replace(",", ""))
        except (TypeError, ValueError):
            return None

    def _click_amount_button(self, driver, symbol: str) -> bool:
        """Click the +/- stepper inside the betslip amount controls."""
        return bool(driver.execute_script("""
var form = document.querySelector('form.live-betslip');
if (!form) return false;
var els = form.querySelectorAll('div, span, a, button');
for (var i = 0; i < els.length; i++) {
    var el = els[i];
    if (el.offsetHeight <= 0 || el.offsetWidth <= 0) continue;
    if ((el.innerText || '').trim() === arguments[0]) {
        try { el.click(); return true; } catch (e) { return false; }
    }
}
return false;
""", symbol))

    def _set_stake_in_betslip(self, driver, stake: float, gui_callback=None) -> bool:
        """Adjust the betslip stake to the requested amount and verify the REAL amount.

        The React-bound amount field (#amount-prematch etc.) is the authoritative
        read; the possible-win/total-odds ratio carries a site boost (~3%) so it is
        only a cross-check, never a steering signal. Strategy: type the exact amount
        into the field first, else steer the +/- stepper reading the field itself.
        Returns True ONLY once a verified stake within tolerance is on the slip.
        """
        stake = max(10.0, round(float(stake), 2))

        # 1) type the exact amount into the real field (precise path)
        if self._type_stake(driver, stake, gui_callback=gui_callback):
            cur = self._read_stake_input(driver) or self._read_betslip_stake_derived(driver)
            self._emit_direct(gui_callback, f"   ✅ Stake typed = KES {cur:.2f}")
            return True

        # 2) +/- stepper, steering on the field read (input-primary)
        best = (None, 1e9)
        last_value = None
        stable = 0
        for _clicks in range(40):
            cur = self._read_stake_input(driver) or self._read_betslip_stake_derived(driver)
            if cur is None:
                break
            diff = cur - stake
            if abs(diff) < abs(best[1]):
                best = (cur, diff)
            if abs(diff) < 0.01:
                self._emit_direct(gui_callback, f"   ✅ Stake = KES {cur:.2f}")
                return True
            self._click_amount_button(driver, "-" if diff > 0 else "+")
            if last_value is not None and abs(cur - last_value) < 0.01:
                stable += 1
                if stable >= 3:
                    break
            else:
                stable = 0
            last_value = cur
            time.sleep(0.15)

        # 3) native value-setter fallback
        if self._set_stake_direct(driver, stake, gui_callback=gui_callback):
            cur = self._read_stake_input(driver) or self._read_betslip_stake_derived(driver)
            self._emit_direct(gui_callback, f"   ✅ Stake set natively = KES {cur:.2f}")
            return True

        cur = self._read_stake_input(driver) or self._read_betslip_stake_derived(driver)
        ok = cur is not None and abs(cur - stake) < 1.0
        if ok:
            self._emit_direct(gui_callback, f"   ✅ Stake = KES {cur:.2f}")
        else:
            self._emit_direct(gui_callback,
                              f"   ❌ Stake is KES {cur if cur is not None else '?'} — "
                              f"target was KES {stake:.2f}")
        return ok

    def _type_stake(self, driver, stake: float, gui_callback=None) -> bool:
        """Select the real stake field content and type the requested amount."""
        el = self._locate_stake_input(driver)
        if not el:
            return False
        try:
            from selenium.webdriver.common.keys import Keys
            el.click()
            time.sleep(0.2)
            el.send_keys(Keys.CONTROL, "a")
            el.send_keys(f"{stake:.2f}".rstrip("0").rstrip("."))
            time.sleep(0.3)
            el.send_keys(Keys.ENTER)
            time.sleep(0.4)
            el.send_keys(Keys.TAB)
            time.sleep(0.4)
        except Exception as e:
            self._emit_direct(gui_callback, f"   ⚠️ Could not type stake: {str(e)[:80]}")
            return False
        cur = self._read_stake_input(driver) or self._read_betslip_stake_derived(driver)
        return cur is not None and abs(cur - float(stake)) < 1.0

    def _set_stake_direct(self, driver, stake: float, gui_callback=None) -> bool:
        """Force-set the betslip stake via the native value setter + events (React-safe)."""
        ok = driver.execute_script("""
var form = document.querySelector('form.live-betslip');
if (!form) return false;
var cands = form.querySelectorAll('input');
var inp = null;
for (var i = 0; i < cands.length; i++) {
    var el = cands[i];
    var qa = ((el.getAttribute('data-qa')||'')+' '+(el.name||'')+' '+(el.id||'')+' '+
              (el.getAttribute('placeholder')||'')+' '+(el.className||'')).toLowerCase();
    if (/stake|amount/.test(qa) && el.type !== 'hidden') { inp = el; break; }
}
var labs = form.querySelectorAll('label,span,div');
for (var i = 0; i < labs.length; i++) {
    var t = (labs[i].innerText || labs[i].textContent || '').trim().toLowerCase();
    if (!/stake|amount|kes/.test(t)) continue;
    var ns = labs[i].querySelectorAll('input');
    for (var j = 0; j < ns.length; j++) if (ns[j].type !== 'hidden') { inp = ns[j]; break; }
    if (inp) break;
}
if (!inp) {
    for (var i = 0; i < cands.length; i++) {
        var el = cands[i];
        if (el.type === 'hidden') continue;
        var r = el.getBoundingClientRect();
        if (r.width > 0 && r.height > 0) { inp = el; break; }
    }
}
if (!inp) return false;
var target = String(arguments[0]);
var proto = Object.getPrototypeOf(inp);
var desc = Object.getOwnPropertyDescriptor(proto, 'value');
var setter = (desc && desc.set) ? desc.set : function (v) { this.value = v; };
setter.call(inp, target);
inp.dispatchEvent(new Event('input', {bubbles: true}));
inp.dispatchEvent(new Event('change', {bubbles: true}));
inp.dispatchEvent(new KeyboardEvent('keyup', {bubbles: true, key: 'Enter'}));
inp.blur();
return true;
""", stake)
        if not ok:
            return False
        time.sleep(0.4)
        cur = self._read_betslip_stake_derived(driver) or self._read_stake_input(driver)
        good = cur is not None and abs(cur - float(stake)) < 1.0
        if good:
            self._emit_direct(gui_callback, f"   ✅ Stake set natively = KES {cur:.2f}")
        return good

    def _read_betslip_count(self, driver) -> int:
        """Return how many selections are currently on the betslip (-1 = unknown)."""
        v = driver.execute_script(r"""
try {
    var app = document.querySelector('body');
    var svc = window.angular && window.angular.element(app).injector().get('BetslipService');
    if (!svc) return -1;
    var c = svc.count();
    return (typeof c === 'number') ? c : -1;
} catch (e) { return -1; }
""")
        try:
            return int(v)
        except (TypeError, ValueError):
            return -1

    def _read_confirm_prompt(self, driver) -> dict:
        """Inspect the visible SweetAlert / modal and classify what it is saying."""
        data = driver.execute_script(r"""
var out = { text: '', visible: false, has_ok: false, has_cancel: false, slip_count: -1 };
var sw = document.querySelector('.sweet-alert.showSweetAlert, .sweet-alert') ||
         document.querySelector('[class*="swal"]');
if (sw && sw.offsetHeight > 0 && (sw.innerText || '').trim()) {
    out.visible = true;
    out.text = ((sw.innerText || '').replace(/\s+/g, ' ')).trim().slice(0, 500);
    var btns = sw.querySelectorAll('button');
    for (var i = 0; i < btns.length; i++) {
        var t = (btns[i].innerText || '').trim().toLowerCase();
        var cls = typeof btns[i].className === 'string' ? btns[i].className : '';
        if (t === 'ok' || cls.indexOf('confirm') >= 0) out.has_ok = true;
        if (t === 'cancel' || cls.indexOf('cancel') >= 0) out.has_cancel = true;
    }
}
try {
    var app = document.querySelector('body');
    out.slip_count = window.angular.element(app).injector().get('BetslipService').count() || 0;
} catch (e) {}
return out;
""")
        data = data or {}
        text = (data.get("text") or "").lower()
        data["flags"] = {
            "confirm": "confirm" in text or "your bet" in text,
            "invalid": any(k in text for k in ("not valid", "invalid", "unavailable",
                                               "suspended", "no longer available", "removed")),
            "odds_changed": any(k in text for k in ("odds have changed", "have changed",
                                                    "new odds", "price change")),
            "inplay": any(k in text for k in ("in play", "inplay", "already started",
                                              "already in", "kicked off", "remove these games")),
            "funds": any(k in text for k in ("insufficient", "deposit", "top up",
                                             "low balance", "not enough balance")),
        }
        return data

    def _click_modal_button(self, driver, label: str) -> bool:
        """Click the OK or Cancel button of the visible prompt (never a market option)."""
        return bool(driver.execute_script(r"""
var want = arguments[0].toLowerCase();
var containers = [];
var sw = document.querySelector('.sweet-alert.showSweetAlert, .sweet-alert') ||
         document.querySelector('[class*="swal"]');
if (sw && sw.offsetHeight > 0) containers.push(sw);
for (var c = 0; c < containers.length; c++) {
    var btns = containers[c].querySelectorAll('button, a, [role="button"]');
    for (var i = 0; i < btns.length; i++) {
        var t = (btns[i].innerText || '').trim().toLowerCase();
        if (t !== want) continue;
        if (btns[i].offsetHeight > 0) { try { btns[i].click(); return true; } catch (e) {} }
    }
}
var all = document.querySelectorAll('a, button, div, span, li');
for (var i = 0; i < all.length; i++) {
    var el = all[i];
    if (el.offsetHeight <= 0) continue;
    if (el.closest('.event-row')) continue;
    if (typeof el.className === 'string' && el.className.indexOf('event-selection') >= 0) continue;
    if ((el.innerText || '').trim().toLowerCase() === want) {
        try { el.click(); return true; } catch (e) {}
    }
}
return false;
""", label))

    def _handle_confirm_prompt(self, driver, timeout: int = 12) -> str:
        """Act on the open bet confirmation prompt.

        Returns one of:
          'confirmed' — a clean "Confirm your bet" prompt was accepted,
          'accepted'  — an informational prompt (odds changed / in-play / removed) was OK'd,
          'invalid'   — the slip was flagged "Not valid" (selection suspended/removed),
          'funds'     — the bookmaker asked for a deposit (prompt dismissed),
          'none'      — no prompt appeared before the timeout.
        """
        deadline = time.time() + timeout
        while time.time() < deadline:
            st = self._read_confirm_prompt(driver)
            if st.get("visible") and st.get("text"):
                f = st.get("flags", {})
                if f.get("funds"):
                    self._click_modal_button(driver, "cancel")
                    return "funds"
                if f.get("invalid"):
                    self._click_modal_button(driver, "ok")
                    return "invalid"
                if f.get("confirm"):
                    self._click_modal_button(driver, "ok")
                    return "confirmed"
                self._click_modal_button(driver, "ok")
                return "accepted"
            time.sleep(1)
        return "none"

    def _click_place_bet_button(self, driver) -> bool:
        """Click the REAL PLACE BET button (the one with ng-click, not the inert wrapper)."""
        return bool(driver.execute_script(r"""
var cands = [];
var els = document.querySelectorAll('a, button, div, span');
for (var i = 0; i < els.length; i++) {
    var el = els[i];
    if (el.offsetHeight <= 0 || el.offsetWidth <= 0) continue;
    var t = (el.innerText || '').trim().toLowerCase();
    if (t !== 'place bet') continue;
    var ng = el.getAttribute('ng-click') || '';
    var cls = (typeof el.className === 'string') ? el.className : '';
    cands.push({ el: el, ng: ng, cls: cls, area: el.offsetWidth * el.offsetHeight });
}
cands.sort(function (a, b) {
    var ang = a.ng ? 1 : 0, bng = b.ng ? 1 : 0;
    if (ang !== bng) return bng - ang;
    var ap = a.cls.indexOf('place-bet') >= 0 ? 1 : 0, bp = b.cls.indexOf('place-bet') >= 0 ? 1 : 0;
    if (ap !== bp) return bp - ap;
    return a.area - b.area;
});
if (!cands.length) return false;
try { cands[0].el.click(); } catch (e) { return false; }
return true;
"""))

    def _bet_succeeded(self, driver) -> bool:
        """Check for a success signal on the page after placing the bet.

        Strongest signal: the Angular BetslipService reports 0 selections
        (the slip is emptied once the bet is accepted).
        """
        count = driver.execute_script(r"""
try {
    var app = document.querySelector('body');
    return window.angular && (window.angular.element(app).injector().get('BetslipService').count() || 0);
} catch (e) {
    return -1;
}
""")
        if isinstance(count, (int, float)) and count == 0:
            return True
        return bool(driver.execute_script("""
var b = (document.body.innerText || '').toLowerCase();
return b.indexOf('bet successfully placed') >= 0 ||
       b.indexOf('your bet has been placed') >= 0 ||
       b.indexOf('bet placed successfully') >= 0 ||
       b.indexOf('bet received') >= 0 ||
       b.indexOf('betslip is empty') >= 0 ||
       b.indexOf('you have placed') >= 0;
"""))

    def _clear_betslip(self, driver, gui_callback=None) -> bool:
        """Try to remove every selection / clear the betslip. Bounded and safe:
        clearing a slip can never place a bet. Returns True if the slip reads empty."""
        from selenium.webdriver.common.by import By
        try:
            candidates = (
                "//div[contains(@class,'slip')]//button[contains(@class,'remove')]",
                "//div[contains(@class,'slip')]//*[contains(text(),'Remove')]",
                "//div[contains(@class,'slip')]//*[contains(text(),'CLEAR')]",
                "//div[contains(@class,'slip')]//*[contains(text(),'Clear')]",
                "//div[contains(@class,'slip')]//*[@title='Remove']",
                "//button[contains(@class,'remove')] | //a[contains(@class,'remove')]",
                "//*[contains(@class,'fa-trash') or contains(@class,'trash')]",
            )
            for expr in candidates:
                try:
                    els = driver.find_elements(By.XPATH, expr)
                    for el in els[:20]:
                        try:
                            if el.is_displayed():
                                el.click()
                                time.sleep(0.3)
                        except Exception:
                            pass
                except Exception:
                    pass
            deadline = time.time() + 8
            while time.time() < deadline:
                if self._read_betslip_count(driver) == 0:
                    return True
                time.sleep(0.5)
            return False
        except Exception:
            return False

    def _open_betslip_and_place(self, driver, stake: float, gui_callback=None,
                                before_balance: float = 0.0,
                                max_attempts: int = 6) -> object:
        """Open the betslip, set the stake, and PLACE + CONFIRM with automatic retries.

        Bets sometimes fail to go through because odds change or games start while we bet.
        The bookmaker then shows a prompt (odds changed / in-play games / "Not valid",
        sometimes a deposit request). This method is smart about those prompts:

          - "Confirm your bet"            -> click OK, then verify the slip emptied / balance drop;
          - "odds have changed"           -> OK it to accept the new prices, verify, retry if needed;
          - in-play / selections removed  -> OK it (they get auto-removed), verify, retry;
          - "Not valid" prompt            -> OK it and re-check the slip count — if it dropped
             below 3, return {'needs_legs': True} so the caller rebuilds the slip;
          - deposit / insufficient funds  -> dismissed, return False (caller reports DEPOSIT).

        Returns True on a placed bet, False on hard failure, or a dict with
        {'needs_legs': True, 'count': n} when the slip must be rebuilt.
        """
        if before_balance > 0.0 and before_balance < float(stake):
            self._emit_direct(gui_callback,
                              f"💰 INSUFFICIENT BALANCE — KES {before_balance:,.2f} available, "
                              f"KES {stake:,.2f} needed (deposit at least "
                              f"KES {stake - before_balance:,.2f}).")
            return False

        self._emit_direct(gui_callback, "Opening betslip...")
        # Desktop auto-opens the panel when odds are selected; mobile needs the counter.
        panel_h = driver.execute_script(r"""
var p = document.querySelector('form.live-betslip');
return p ? p.offsetHeight : 0;
""")
        if panel_h:
            self._emit_direct(gui_callback, "  Bet slip panel already open")
        else:
            driver.execute_script("""
var slip = document.querySelector('[data-qa="betslip-counter"]');
if (slip) {
    slip.style.cssText = 'display:flex!important;position:fixed;bottom:0;left:0;right:0;z-index:9999;background:#1a2a3a;color:white;padding:12px;justify-content:center;align-items:center;cursor:pointer;';
    slip.click();
}
""")
            time.sleep(2)
            panel_h = driver.execute_script(r"""
var p = document.querySelector('form.live-betslip');
return p ? p.offsetHeight : 0;
""")
        if not panel_h:
            self._emit_direct(gui_callback, "⚠️ Betslip panel did not open")
            return False

        totals = self._read_betslip_totals(driver)
        self._emit_direct(gui_callback,
                          f"  Total odds: {totals['odds']} | Possible win: KSH {totals['win']}")

        consec_invalid = 0
        for attempt in range(1, max_attempts + 1):
            slip_count = self._read_betslip_count(driver)
            # The slip is empty or shrank below what SportPesa accepts (min 3 selections).
            # Empty means the removal prompt stripped every selection without placing — rebuild.
            if slip_count == 0 or (slip_count > 0 and slip_count < 3):
                self._emit_direct(gui_callback,
                                  f"⚠️ {slip_count if slip_count > 0 else 'No'} selection(s) "
                                  "left on the slip (games removed/already in play) — "
                                  "need at least 3 to bet.")
                return {"needs_legs": True, "count": slip_count}

            stake_ok = self._set_stake_in_betslip(driver, stake, gui_callback=gui_callback)
            if not stake_ok:
                # Never place with an unverified stake. Placing anyway is what
                # surfaced as "insufficient funds" / oversized bets when the slip
                # kept its default or last-used amount instead of the requested one.
                self._emit_direct(gui_callback,
                                  f"  🛑 ABORT: could not set the stake to KES {stake:,.2f}. "
                                  "Not placing the bet with an unknown stake.")
                return False
            # final re-check right before clicking PLACE. The React-bound amount field
            # (#amount-prematch) is the authoritative stake; the possible-win/odds ratio
            # carries a ~3% site boost, so it only cross-checks. Abort on disagreement —
            # that means the displayed amount differs from what would actually be placed.
            final_in = self._read_stake_input(driver)
            final_der = self._read_betslip_stake_derived(driver)
            if final_in is not None and final_der is not None and \
                    abs(final_in - final_der) > max(2.0, 0.15 * stake):
                self._emit_direct(gui_callback,
                                  f"  🛑 ABORT: field shows KES {final_in:.2f} but slip pays "
                                  f"like KES {final_der:.2f} — amount/model mismatch. Not placing.")
                return False
            guard_value = final_in if final_in is not None else final_der
            if guard_value is not None and abs(guard_value - stake) >= 1.0:
                self._emit_direct(gui_callback,
                                  f"  🛑 ABORT: slip shows KES {guard_value:.2f}, need KES {stake:,.2f}. "
                                  "Not placing.")
                return False
            totals2 = self._read_betslip_totals(driver)
            self._emit_direct(gui_callback,
                              f"  Attempt {attempt}/{max_attempts} | Total odds: "
                              f"{totals2['odds']} | Possible win: KSH {totals2['win']}")

            self._emit_direct(gui_callback, "Placing bet...")
            if not self._click_place_bet_button(driver):
                self._emit_direct(gui_callback, "  ⚠️ PLACE BET button not found — retrying")
                time.sleep(2)
                continue
            self._emit_direct(gui_callback, "  ✅ PLACE BET clicked")
            time.sleep(1)

            act = self._handle_confirm_prompt(driver, timeout=10)
            if act == "funds":
                self._emit_direct(gui_callback,
                                  "💰 Bet rejected — the bookmaker reports insufficient balance/deposit.")
                return False
            elif act == "none":
                self._emit_direct(gui_callback, "  (no confirmation prompt appeared — re-checking)")
            elif act == "confirmed":
                self._emit_direct(gui_callback, "  ✅ Confirm prompt accepted")
            elif act == "invalid":
                consec_invalid += 1
                self._emit_direct(gui_callback,
                                  "  ↻ \"Not valid\" prompt handled (selection suspended/removed) — re-checking")
            else:
                consec_invalid = 0
                self._emit_direct(gui_callback,
                                  f"  ↻ Prompt handled ({act}: odds changed / in-play / removed) — re-checking")
            time.sleep(2)

            if self._bet_succeeded(driver):
                self._emit_direct(gui_callback, "✅ Betslip emptied — bet placed")
                return True
            after = self._read_balance_text(driver)
            dropped = (before_balance > 0.0) and (after > 0.0) and (before_balance - after) >= 1.0
            if dropped:
                self._emit_direct(gui_callback,
                                  f"✅ Balance reduced: KES {before_balance:,.2f} → "
                                  f"KES {after:,.2f} — bet placed")
                return True
            # A suspended/removed leg keeps blocking submission → stop retrying the same
            # dead slip. Clear it so the caller rebuilds from fresh, upcoming games
            # instead of burning the remaining attempts on a slip that can't submit.
            if act == "invalid" and consec_invalid >= 2:
                self._emit_direct(gui_callback,
                                  "  ↻ Suspended selection keeps blocking submit — clearing slip, "
                                  "will rebuild from fresh games.")
                if self._clear_betslip(driver, gui_callback=gui_callback):
                    return {"needs_legs": True, "count": 0}
                return False
            self._emit_direct(gui_callback,
                              f"  Balance KES {after:,.2f} unchanged — will retry placement")
            time.sleep(1)

        self._emit_direct(gui_callback,
                          "⚠️ Could not place the bet after repeated attempts (odds kept changing "
                          "or games went in-play).")
        return False

