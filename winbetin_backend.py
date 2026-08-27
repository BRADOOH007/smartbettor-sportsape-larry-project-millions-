#!/usr/bin/env python3
"""
Winbetin backend focused on browser-based login, route discovery, and balance extraction.
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
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from queue import Empty, Queue
from urllib.parse import urljoin

from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from resource_path import resource_path, writable_path

LOGIN_URL = "https://winbetin.com/#/Login"
SITE_ORIGIN = "https://winbetin.com"
HOME_URL = f"{SITE_ORIGIN}/"
CONFIG_PATH = Path(writable_path("config/endpoints.json"))
BUNDLED_CONFIG_PATH = Path(resource_path("config/endpoints.json"))
DISCOVERED_ROUTES_PATH = Path(writable_path("config/discovered_winbetin_routes.json"))
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


class WinbetinBackend:
    """Browser-backed Winbetin integration with lightweight route discovery."""

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
                "login": ["/kickGoLogin", "/#/Login"],
                "profile": ["/profile"],
                "deposit": ["/deposite", "/depositerecords"],
                "withdraw": ["/withdraw", "/withdrawlimit"],
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
        temp_profile = getattr(driver, "_winbetin_temp_profile", None)
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

    def _build_driver(self, gui_callback=None) -> webdriver.Chrome:
        options = Options()
        options.page_load_strategy = 'eager'  # Don't wait for all images/ads to load
        if self.headless:
            options.add_argument("--headless=new")
        options.add_argument("--window-size=430,932")
        options.add_argument("--disable-gpu")
        options.add_argument("--no-sandbox")
        options.add_argument("--disable-dev-shm-usage")
        options.add_argument("--disable-blink-features=AutomationControlled")
        options.add_experimental_option("excludeSwitches", ["enable-automation", "enable-logging"])
        options.add_experimental_option("useAutomationExtension", False)
        # Suppress "Save password" and other automation popups
        options.add_experimental_option("prefs", {
            "credentials_enable_service": False,
            "profile.password_manager_enabled": False,
            "autofill.profile_enabled": False,
            "autofill.credit_card_enabled": False,
            "profile.managed_default_content_settings.images": 2  # Disable images for speed
        })
        options.add_argument("--disable-extensions")
        options.add_argument("--disable-infobars")
        options.add_argument("--disable-notifications")
        options.add_argument("--dns-prefetch-disable")
        options.add_argument("--disable-browser-side-navigation")
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

        temp_profile = tempfile.mkdtemp(prefix="winbetin_chrome_")
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
                    "*doubleclick.net*", "*hotjar.com*", "*sentry.io*", "*.png", "*.jpg", 
                    "*.jpeg", "*.gif", "*.svg", "*.webp", "*.mp4", "*.woff*"
                ]
            })
            driver.execute_cdp_cmd("Network.enable", {})
            driver._winbetin_temp_profile = temp_profile  # type: ignore[attr-defined]
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

    def _format_winbetin_login_phone(self, phone: str) -> str:
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
            lambda d: "winbetin" in (
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
                [".swiperClose", ".closeBtnX"],
                ["[class*='close']", "[id*='close']"],
            ):
                if self._click_first_visible_selector(driver, selectors):
                    total_actions += 1
                    time.sleep(0.3)
            self._click_by_text(driver, ["close", "skip", "dismiss", "cancel", "no thanks", "later"])
            time.sleep(0.4)
        return total_actions

    def _find_login_inputs(self, driver: webdriver.Chrome):
        phone_input = self._find_first(
            driver,
            [
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
                "input[type='password']",
                "input[name*='password']",
                "input[id*='password']",
            ],
        )
        return phone_input, password_input

    def _click_login_entry(self, driver: webdriver.Chrome) -> bool:
        if self._click_first_visible_selector(driver, [".login_in.clickScale-92", ".login_in"]):
            return True
        if self._click_by_text(driver, ["log in", "login"]):
            return True
        try:
            if driver.execute_script("if (window.TurnToPage) { window.TurnToPage(3); return true; } return false;"):
                return True
        except Exception:
            pass
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

    def _wait_for_post_login(self, driver: webdriver.Chrome, timeout: int = 15) -> None:
        deadline = time.time() + timeout
        while time.time() < deadline:
            self._dismiss_visible_promos(driver, rounds=1)
            try:
                body_text = driver.execute_script("return ((document.body && document.body.innerText) || '').toLowerCase();")
            except Exception:
                body_text = ""
            
            # More reliable check: Wait until we see currency AND login inputs are gone
            # or we've reached a known logged-in state (like seeing 'Deposit' or 'KSH')
            has_currency = "ksh" in body_text or "kes" in body_text or "deposit" in body_text
            phone_input, password_input = self._find_login_inputs(driver)
            
            if has_currency and not (phone_input and password_input):
                return
            time.sleep(0.3)

    def _logout_current_session(self, driver: webdriver.Chrome) -> bool:
        self._dismiss_visible_promos(driver, rounds=1)
        self._click_by_text(driver, ["profile"])
        time.sleep(0.5)
        self._dismiss_visible_promos(driver, rounds=1)
        if self._click_by_text(driver, ["logout", "log out", "sign out", "exit login", "exit"]):
            time.sleep(0.5)
            return True
        for route in ("#/profile", "#/Profile"):
            try:
                driver.execute_script("window.location.hash = arguments[0];", route)
            except Exception:
                continue
            time.sleep(0.5)
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
            bonus_keys = ("bonus", "bonus_balance")
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
        """Force navigation to the profile page where balance and coins are visible."""
        try:
            # First try direct hash navigation as it's fastest
            driver.execute_script("window.location.hash = '#/profile';")
            time.sleep(1)
            self._dismiss_visible_promos(driver, rounds=1)
            
            # Verify we are on profile or try clicking the Profile tab
            body_text = driver.execute_script("return (document.body && document.body.innerText) || '';").lower()
            if "my balance" in body_text or "coins" in body_text:
                return True
                
            # Fallback: click the Profile tab in the bottom navigation
            self._click_by_text(driver, ["profile"])
            time.sleep(1)
            return True
        except Exception:
            return False

    def check_single_balance(self, phone: str, password: str, gui_callback=None, driver=None) -> dict:
        external_driver = driver is not None
        try:
            if not driver:
                driver = self._acquire_driver(gui_callback=gui_callback)

            self._emit(gui_callback, "   Loading login page...")
            driver.get(LOGIN_URL)
            # wait_for_site_shell is often too slow, use a lighter check
            WebDriverWait(driver, 10).until(lambda d: d.execute_script("return document.readyState") != "loading")

            phone_input, password_input = self._wait_for_login_inputs(driver, gui_callback=gui_callback)

            if not phone_input or not password_input:
                return {
                    "status": "error",
                    "phone": phone,
                    "balance": 0,
                    "bonus": 0,
                    "coins": 0,
                    "message": "Could not find Winbetin login inputs",
                }

            self._emit(gui_callback, "   Filling credentials...")
            phone_input.clear()
            phone_input.send_keys(self._format_winbetin_login_phone(phone))
            password_input.clear()
            password_input.send_keys(password)
            time.sleep(0.8)

            self._emit(gui_callback, "   Clicking login...")
            clicked = self._click_login_submit(driver)
            self._wait_for_post_login(driver)
            
            self._emit(gui_callback, "   Navigating to Profile...")
            self._navigate_to_profile(driver)
            # Short delay for header stabilization
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
                    "message": "Logged in or reached site, but no Winbetin wallet data was confirmed",
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
            if driver and not external_driver:
                self._reset_driver_state(driver)
                if not self._store_preloaded_driver(driver):
                    self._cleanup_driver(driver)
            elif driver and external_driver:
                # If reusing, just clear session for next account
                self._reset_driver_state(driver)

    def check_balances(self, phone_list, password, gui_callback=None):
        results = []
        cache_results = {}
        indexed_results = {}

        def process_phone(phone, driver):
            normalized = self._format_winbetin_login_phone(phone)
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
                                f"Checking: {phone} Balance: KES {result['balance']:,.2f} | Coins: {result.get('coins', 0):,.0f}",
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
                                f"Checking: {phone} Balance: KES {result['balance']:,.2f} | Coins: {result.get('coins', 0):,.0f}",
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
            total_coins = sum(r.get("coins", 0) for r in results if r["status"] == "success")
            success_count = sum(1 for r in results if r["status"] == "success")
            
            gui_callback("-" * 30)
            gui_callback(f"🏆 FINAL SUMMARY: {success_count}/{len(results)} Accounts Successful")
            gui_callback(f"💰 TOTAL BALANCE: KES {total_bal:,.2f}")
            gui_callback(f"🪙 TOTAL COINS: {total_coins:,.0f}")
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
                writer.writerow(["Phone", "Status", "Balance", "Coins", "Bonus", "Message"])
                for item in results:
                    writer.writerow([
                        item["phone"],
                        item["status"],
                        f"{item['balance']:.2f}",
                        f"{item.get('coins', 0):.0f}",
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
        total_coins = sum(item.get("coins", 0) for item in results if item["status"] == "success")
        success_count = sum(1 for item in results if item["status"] == "success")
        failed_count = len(results) - success_count

        lines = [
            "=" * 80,
            "WINBETIN BALANCE AND COINS REPORT",
            "=" * 80,
            f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"Total Accounts: {len(results)}",
            f"Successful: {success_count}",
            f"Failed: {failed_count}",
            "",
            f"Total Balance: KES {total_balance:,.2f}",
            f"Total Coins: {total_coins:,.0f}",
            "",
        ]

        for item in results:
            if item["status"] == "success":
                lines.append(
                    f"{item['phone']}: Balance KES {item['balance']:,.2f} | Coins {item.get('coins', 0):,.0f}"
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
        return {"status": "error", "message": "Withdraw automation is not configured for Winbetin yet"}

    def check_account_balances(self, phone_list, password, gui_callback=None):
        results = self.check_balances(phone_list, password, gui_callback)
        ready = [item["phone"] for item in results if item["status"] == "success" and item["balance"] > 0]
        insufficient = [item["phone"] for item in results if item["status"] == "success" and item["balance"] <= 0]
        inactive = [item["phone"] for item in results if item["status"] != "success"]
        return ready, insufficient, inactive

    def place_single_bet_with_booking_code(self, *_args, **_kwargs):
        return {"status": "error", "message": "Bet placement is not configured for Winbetin yet"}

    def place_bets_with_booking_code(self, *_args, **_kwargs):
        return {"status": "error", "message": "Bet placement is not configured for Winbetin yet"}

    def roll_over_accounts(self, *_args, **_kwargs):
        return {"status": "error", "message": "Rollover is not configured for Winbetin yet"}

    def claim_bonuses_for_accounts(self, *_args, **_kwargs):
        return {"status": "error", "message": "Bonus claiming is not configured for Winbetin yet"}

    def batch_withdraw(self, *_args, **_kwargs):
        return {"status": "error", "message": "Batch withdraw is not configured for Winbetin yet"}

    def odileague_supa5_automation(self, *_args, **_kwargs):
        return {"status": "error", "message": "Supa5 automation is not configured for Winbetin yet"}

    def run_odileague_bonus(self, *_args, **_kwargs):
        return {"status": "error", "message": "Bonus automation is not configured for Winbetin yet"}

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

    def shutdown_all_executors(self):
        return None
