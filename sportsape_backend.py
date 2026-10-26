#!/usr/bin/env python3
"""
Sportsape BitBot backend focused on browser-based login, route discovery, and balance extraction.
"""

from __future__ import annotations

import base64
import csv
import hashlib
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
from collections import deque
from datetime import datetime, timedelta
from pathlib import Path
from queue import Empty, Queue
from urllib.parse import urljoin

import requests

from sportsape_grok import GrokGovernor

try:
    from sportsape_supabase import get_sync as _sb_get_sync
except Exception:  # cloud sync optional — engine must run without it
    _sb_get_sync = None

try:
    from sportsape_agents import AgentHub, LeagueContextAgent
except Exception:  # agents layer optional — engine must run without it
    AgentHub = None
    LeagueContextAgent = None

from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys


# ── Scoped Chrome reaper ─────────────────────────────────────────────────────
# Every browser this tool launches is given its own throwaway profile via
# --user-data-dir=<tempdir>/sportsape_chrome_XXXX. That marker is the ONLY thing
# we are allowed to match on: the user's personal Chrome uses the real
# "User Data" directory and must never be touched by any kill below.
_CHROME_PROFILE_MARKER = "sportsape_chrome_"

# Spawning a console process on Windows flashes a black terminal window. The
# reaper runs on every driver cleanup, so an unhidden shell made a window pop
# open and vanish over and over. CREATE_NO_WINDOW keeps it invisible.
_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0x08000000)

# The process listing is expensive (and used to be re-run per driver), so cache
# it briefly. Orphaned chrome does not appear and vanish inside 3 seconds.
_CHROME_PID_CACHE: tuple[float, list[tuple[int, str]]] = (0.0, [])
_CHROME_PID_TTL = 3.0


# ── ONE BROWSER PER ACCOUNT (cross-process) ─────────────────────────
# SportPesa allows a single active session per account. The moment a second
# browser logs the same phone in, the book kills the older token and every
# subsequent PLACE fails with 403 "User logged from another device".
#
# This was NOT only an orphan problem: the engine itself opened extra browsers
# for an account it already had a live driver for (bet history, winnings sync,
# jackpot scan, pre-window research, market sweep), each one logging in again.
# The old `_jackpot_lock` / `_engine_busy` waits only sequenced the BETS, not
# the logins, so the conflict still happened.
#
# Ownership is enforced with an exclusive OS file lock per account. An OS lock
# is released automatically if the process dies, so a crashed run can never
# leave an account permanently locked.
_ACCOUNT_LOCK_DIR = os.path.join(tempfile.gettempdir(), "sportsape_account_locks")
_ACCOUNT_LOCKS: dict[str, dict] = {}
_ACCOUNT_LOCKS_GUARD = threading.Lock()

# ── GLOBAL LOGIN SERIALISATION (2026-10-05) ────────────────────────────
# The per-account lock above stops two browsers fighting over the SAME phone.
# It does nothing for two DIFFERENT accounts, which both mint tokens at the
# same moment. Live evidence: with both workers running, 0798810080 got
# 'User logged from another device' at PLACE time twice in five minutes while
# its own account logged in three times in ninety seconds. Whether the book
# scopes a session to the account or to the client fingerprint, the safe
# assumption is that it does not tolerate overlapping credential POSTs.
#
# So every credential POST - from ANY account, in ANY thread - is funnelled
# through one gate and separated by a settle delay. This costs a few seconds
# per login and removes a whole class of self-inflicted session rejections.
_LOGIN_GATE = threading.Lock()
_LOGIN_LAST_POST = 0.0
_LOGIN_SETTLE_S = 25.0


def _acquire_login_gate(phone: str = "") -> float:
    """Serialise credential POSTs globally. Returns seconds spent waiting."""
    global _LOGIN_LAST_POST
    waited = 0.0
    with _LOGIN_GATE:
        now = time.time()
        gap = _LOGIN_SETTLE_S - (now - _LOGIN_LAST_POST)
        if gap > 0:
            waited = gap
            time.sleep(gap)
        # Claim the slot before releasing the lock so a competing thread waits
        # for OUR settle window rather than firing immediately behind us.
        _LOGIN_LAST_POST = time.time()
    return waited


def _kill_chrome_for_profile(profile_path: str) -> int:
    """Force-kill every chrome.exe still running on `profile_path`. Returns count.

    Scoped strictly to the temp profile WE created (sportsape_chrome_*), matched
    on the full profile path, so the user's own Chrome is never touched. Used as
    a backstop when driver.quit() fails and leaves a browser orphaned.
    """
    if not profile_path:
        return 0
    try:
        target = os.path.normcase(os.path.abspath(profile_path))
    except Exception:
        return 0
    try:
        out = subprocess.run(
            "powershell -NoProfile -NonInteractive -Command \"Get-CimInstance "
            "Win32_Process -Filter \\\"Name='chrome.exe'\\\" | Select-Object "
            "ProcessId, CommandLine | ConvertTo-Json -Compress\"",
            capture_output=True, text=True, timeout=30)
    except Exception:
        return 0
    import json as _json
    try:
        rows = _json.loads((out.stdout or "").strip() or "[]")
        if isinstance(rows, dict):
            rows = [rows]
    except Exception:
        return 0
    killed = 0
    for rec in rows or []:
        cmd = rec.get("CommandLine") or ""
        if target not in os.path.normcase(cmd):
            continue
        pid = rec.get("ProcessId")
        if not pid:
            continue
        try:
            subprocess.run(["taskkill", "/PID", str(pid), "/F"],
                           capture_output=True, timeout=15)
            killed += 1
        except Exception:
            pass
    return killed


def _account_lock_key(phone) -> str:
    digits = "".join(ch for ch in str(phone or "") if ch.isdigit())
    return digits or ("unknown_" + str(abs(hash(str(phone))) % 10**8))


def _acquire_account_session(phone, blocking: bool = False,
                             timeout: float = 0.0) -> bool:
    """Claim exclusive browser ownership of `phone`. True when this process owns it.

    Re-entrant within a process (depth counted) so nested helpers can each take
    the account without deadlocking, but exclusive ACROSS processes, so a test
    script and the engine can never both drive one account."""
    key = _account_lock_key(phone)
    deadline = time.time() + max(0.0, float(timeout))
    while True:
        with _ACCOUNT_LOCKS_GUARD:
            ent = _ACCOUNT_LOCKS.get(key)
            if ent is not None and ent["depth"] > 0:
                ent["depth"] += 1
                return True
            try:
                os.makedirs(_ACCOUNT_LOCK_DIR, exist_ok=True)
                # "a+b" never truncates. Truncating would destroy the byte range
                # another process has locked and silently defeat the guard.
                fh = open(os.path.join(_ACCOUNT_LOCK_DIR, f"{key}.lock"), "a+b")
                if os.fstat(fh.fileno()).st_size == 0:
                    fh.write(b" ")
                    fh.flush()
                fh.seek(0)
                import msvcrt
                msvcrt.locking(fh.fileno(), msvcrt.LK_NBLCK, 1)
                _ACCOUNT_LOCKS[key] = {
                    "fh": fh, "depth": 1, "owner": os.getpid(),
                    "since": time.time(), "phone": str(phone)}
                return True
            except Exception:
                try:
                    fh.close()
                except Exception:
                    pass
        if not blocking or time.time() >= deadline:
            return False
        time.sleep(0.5)


def _release_account_session(phone) -> None:
    """Give up browser ownership of `phone` (safe to call when not held)."""
    key = _account_lock_key(phone)
    with _ACCOUNT_LOCKS_GUARD:
        ent = _ACCOUNT_LOCKS.get(key)
        if ent is None:
            return
        ent["depth"] -= 1
        if ent["depth"] > 0:
            return
        _ACCOUNT_LOCKS.pop(key, None)
        try:
            import msvcrt
            fh = ent.get("fh")
            if fh is not None:
                fh.seek(0)
                msvcrt.locking(fh.fileno(), msvcrt.LK_UNLCK, 1)
                fh.close()
        except Exception:
            pass


def _account_session_holder(phone) -> dict:
    """Describe who currently owns `phone` (for skip messages). Never raises."""
    key = _account_lock_key(phone)
    try:
        with _ACCOUNT_LOCKS_GUARD:
            ent = _ACCOUNT_LOCKS.get(key)
            if ent:
                return {"pid": ent.get("owner"), "held": True,
                        "for_s": round(time.time() - (ent.get("since") or 0), 1)}
    except Exception:
        pass
    return {"pid": None, "held": False, "for_s": 0.0}


def _our_chrome_pids(max_age: float | None = None) -> list[tuple[int, str]]:
    """Return [(pid, command_line)] for chrome processes using OUR temp profile.

    A process qualifies only when its command line contains the sportsape_chrome_
    marker AND does not reference the user's real Chrome profile directory. That
    double condition is deliberate defence-in-depth: if the marker were somehow
    absent we must fail safe and leave the user's browser alone.

    Results are cached for a few seconds so repeated calls (the live-driver
    exclusion scan runs once per driver) do not spawn a shell per call.
    """
    global _CHROME_PID_CACHE
    ttl = _CHROME_PID_TTL if max_age is None else max_age
    stamp, cached = _CHROME_PID_CACHE
    if cached and (time.time() - stamp) < ttl:
        return list(cached)

    found: list[tuple[int, str]] = []
    raw = ""
    delim = None
    # wmic is gone from modern Windows builds; skip straight to PowerShell
    # instead of probing for it and flashing a console on every call.
    # Filter INSIDE the WMI query: marshalling every chrome.exe on the box to
    # PowerShell took ~10s per call, which stalled driver cleanup and fed the
    # "renderer hang" abort loop. Letting WMI do the LIKE narrows the result
    # set server-side and returns in well under a second.
    try:
        proc = subprocess.run(
            ["powershell", "-NoProfile", "-NonInteractive", "-Command",
             "Get-CimInstance Win32_Process "
             "-Filter \"Name='chrome.exe' AND CommandLine LIKE '%sportsape_chrome_%'\" | "
             "ForEach-Object { \"$($_.ProcessId)|$($_.CommandLine)\" }"],
            capture_output=True, text=True, timeout=45,
            creationflags=_NO_WINDOW,
        )
        raw = proc.stdout or ""
        delim = "pipe"
    except Exception:
        return found

    user_profile = (os.environ.get("LOCALAPPDATA", "") or "").rstrip("\\")
    # Both spellings occur in real command lines: the browser uses
    # "...\Google\Chrome\User Data" while some children reference "...\User".
    real_dirs = [
        os.path.join(user_profile, "Google", "Chrome", "User").lower(),
        os.path.join(user_profile, "Google", "Chrome").lower(),
    ]

    for line in raw.splitlines():
        line = line.strip()
        if not line or _CHROME_PROFILE_MARKER not in line:
            continue
        low = line.lower()
        # Never touch the user's own browser, whatever else matches.
        if any(rd and rd in low for rd in real_dirs):
            continue
        pid = None
        if delim == "pipe":
            # "<pid>|<commandline>" — pid is an exact leading field.
            head, _sep, _rest = line.partition("|")
            head = head.strip()
            if head.isdigit():
                pid = int(head)
        if pid is None:
            continue
        found.append((pid, line))

    _CHROME_PID_CACHE = (time.time(), list(found))
    return found


def reap_our_chrome(extra_exclude: set[int] | None = None) -> int:
    """Kill ONLY orphaned chrome processes left by this tool. Never the user's.

    Skips any pid in extra_exclude (drivers still in use). Returns how many were
    killed. Safe to call repeatedly and at any time.
    """
    keep = set(extra_exclude or ())
    # Ask the live driver objects for their chrome pids so a browser we are
    # still using is never reaped out from under the session.
    killed = 0
    for pid, _cmd in _our_chrome_pids(max_age=0.0):
        if pid in keep:
            continue
        try:
            subprocess.run(["taskkill", "/F", "/PID", str(pid), "/T"],
                           capture_output=True, timeout=20,
                           creationflags=_NO_WINDOW)
            killed += 1
        except Exception:
            continue
    if killed:
        try:
            print(f"[reaper] cleaned {killed} orphaned sportsape chrome process(es)")
        except Exception:
            pass
    return killed
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
        self.max_parallel_workers = 2
        self.max_preloaded_drivers = max(1, self.max_parallel_workers)
        self.balance_cache = {"timestamp": 0, "results": {}}
        self.route_config = self._load_route_config()
        self._jackpot_lock = threading.Lock()
        self._jackpot_next_scan = 0.0
        self._jackpot_state = None
        self._jackpot_states = {}      # per-pool research cache: {"MEGA": st, "MIDWEEK": st}
        self._jackpot_cadence = 1500.0
        self._fit_poisson_cache = {}   # (p1,pd,p2)-rounded -> (lh, la) — _fit_poisson is O(grid²)
        self._engine_busy = False
        self._last_crawled_games = []
        self._last_emit_key = None
        self._last_emit_time = 0
        # Per-account worker architecture: each phone owns ONE dedicated browser
        # session (`_worker_drivers[phone]`) and one serializing lock, so deposits/
        # bet rounds / balance touches never open a second login on the same account
        # (which would invalidate the account's live session). Guarded by _driver_lock.
        self._worker_drivers = {}      # phone -> its dedicated Chrome webdriver
        self._account_locks = {}       # phone -> threading.Lock (serializes that session)
        self._worker_threads = []      # running per-account worker threads
        self._sched_lock = threading.Lock()   # serializes SCHED_STATE reads/writes
        self._bets_lock = threading.Lock()    # serializes the shared bets-placed counter
        self._used_lock = threading.Lock()    # serializes used-game memory (2 workers write it)
        self._account_buckets = {}          # phone -> disjoint board bucket (assigned first-seen)
        self._game_owners = {}              # gid -> phone (hard single-owner: one
                                            # game may NEVER be bet by two accounts)
        self._gid_src = {}                  # gid -> listing URL that contains its row
                                            # (merged games live on popular/football-1/
                                            # upcoming listings, not the today tab)
        self._suspended_until = {}          # "gid|market" -> epoch ts: legs the book
                                            # flagged "Not valid"/suspended at PLACE.
                                            # Rebuilders skip them until they clear so
                                            # a dead leg can't block every 300s crawl.
        self._log_ring = deque(maxlen=150)
        self._gov_overrides = {}          # governor runtime overrides: param -> value
        self._gov_paused_reason = None     # governor pause: non-None => engine holds betting
        self._engine_state = {}            # live telemetry snapshot for the governor
        self._grok = None
        self._agent_hub = None
        # Login anti-thrash state (2026-10-05): _auth_ok_at records the last
        # SUCCESSFUL authentication per phone so other components requesting a
        # login in the same window reuse that token instead of POSTing a new one
        # and superseding it. _auth_backoff holds {phone: ts_until_backoff_ends}
        # plus {phone+"_n": consecutive_rejections} so a rejected session is left
        # alone to settle instead of being hammered into a permanent lockout.
        self._auth_ok_at = {}
        self._auth_backoff = {}
        self._agent_stop = threading.Event()
        self._agent_thread = None
        self.JACKPOT_PAGE_URL = "https://www.ke.sportpesa.com/en/mega-jackpot-pro"
        # A genuine Chrome-for-Windows user agent used by the stealth layer in
        # headless mode — hides the automation signature from Akamai/Cloudflare.
        self.STEALTH_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                           "(KHTML, like Gecko) Chrome/138.0.0.0 Safari/537.36")
        # ── Cash-out policy ────────────────────────────────────────────────
        # When an active accumulator reaches "majority of legs won correctly and
        # one (or few) left to play", the site offers a cash-out. If the offered
        # amount is >= this fraction of the possible win we cash out automatically.
        self.cashout_threshold = 0.75
        self.auto_cashout_enabled = True
        self._cashout_probed = {}        # bet_id -> last probe timestamp (rate limiter)
        self._odds_history = None        # gid -> {first/last odds per market, kickoff}
        self._dc_scrape_at = {}        # gid -> last Double-Chance full-market scrape time

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
        """True only when this browser can still be driven.

        CRITICAL FIX (2026-10-05). The old check was `session_id is set` plus a
        `execute_script` ping. When the chromedriver PROCESS dies, Selenium
        keeps `session_id` populated, so the check passed and every later call
        went to a dead socket and BLOCKED on urllib3 retries until they raised
        MaxRetryError (WinError 10061, connection refused). Observed live: the
        engine sat silent for 28 minutes inside one dead driver, then the next
        browser build hung too — no bets, no log, no recovery.

        We now check the chromedriver process itself first. If the OS process
        has exited, this is a corpse and we return False immediately, so the
        caller's existing rebuild path runs BEFORE any blocking HTTP call is
        ever attempted. That single check converts a 28-minute silent hang into
        a clean rebuild in seconds.
        """
        if not driver or not getattr(driver, "session_id", None):
            return False
        # 1) Is the chromedriver process still alive?
        try:
            _svc = getattr(driver, "service", None)
            _proc = getattr(_svc, "process", None) if _svc is not None else None
            if _proc is not None:
                _poll = getattr(_proc, "poll", None)
                if callable(_poll):
                    _rc = _poll()
                    if _rc is not None:
                        return False        # process exited -> corpse
        except Exception:
            pass
        # 2) Can we still talk to it? Bounded so a half-dead driver cannot
        #    block the calling thread for the full script timeout.
        try:
            driver.set_script_timeout(6)
        except Exception:
            pass
        try:
            driver.execute_script("return document.readyState")
            return True
        except Exception:
            return False

    def _driver_health_check(self, driver, phone: str, password: str,
                              gui_callback=None) -> bool:
        """INDUSTRIAL-GRADE FIX (2026-10-04): comprehensive driver health check.

        Detects and recovers from:
        - 'invalid session id' (chromedriver crash)
        - 'no such window' (browser window closed)
        - 'tab crashed' (renderer OOM)
        - Dead session token (wallet API returns 401/403)

        Returns True if the driver is healthy or was successfully recovered.
        Returns False if the driver is dead and needs a full rebuild.
        """
        if not driver:
            return False
        # Check 1: basic session validity
        try:
            _ = driver.session_id
        except Exception:
            return False
        # Check 2: can we execute JS?
        try:
            driver.execute_script("return document.readyState")
        except Exception as e:
            _err = str(e).lower()
            if "invalid session id" in _err or "no such window" in _err:
                return False  # dead — needs rebuild
            if "tab crashed" in _err:
                return False  # dead — needs rebuild
            # Other errors might be transient
            return True
        # Check 3: is the session token alive?
        # A browser that has NEVER been logged in (freshly built this round) has
        # no token yet. Treating "not logged in" as a dead token there caused a
        # pointless teardown+rebuild on every fresh warm-up, which churned extra
        # Chrome profiles and burned the account's login budget. Only a browser
        # that was PREVIOUSLY logged in can have a token that went dead.
        _ever_logged = bool(getattr(driver, "_sportsape_logged_in", False))
        try:
            if not self._session_is_live(driver, deep_check=True):
                if not _ever_logged:
                    # Fresh browser — normal, not a fault. Let the caller's
                    # _ensure_bet_login perform the first real login.
                    return True
                # Token is dead — try to re-login on this same browser
                self._emit_direct(gui_callback,
                                  f"  🔐 {phone}: session token dead — re-logging in on existing browser")
                try:
                    self._dismiss_foreign_session_prompt(driver)
                except Exception:
                    pass
                try:
                    self._logout_current_session(driver)
                except Exception:
                    pass
                time.sleep(3)
                try:
                    with self._login_lock:
                        if self._hard_spa_login(driver, phone, password,
                                                gui_callback=gui_callback, force=True):
                            return True
                except Exception:
                    pass
                # Re-login failed — browser might be in a bad state
                return False
        except Exception:
            pass
        return True

    def _close_stray_tabs(self, driver) -> None:
        """Close any extra browser tabs beyond the first (main) tab."""
        if not driver:
            return
        try:
            handles = driver.window_handles
            if len(handles) <= 1:
                return
            for handle in list(handles)[1:]:
                try:
                    driver.switch_to.window(handle)
                    driver.close()
                except Exception:
                    pass
            driver.switch_to.window(handles[0])
        except Exception:
            pass

    def _live_driver_pids(self) -> set[int]:
        """PIDs of chrome backing every driver we still hold a handle to.

        These are excluded from reaping so a rotation never kills the browser a
        worker is actively betting through.
        """
        pids: set[int] = set()
        drivers: list = []
        with self._active_drivers_lock:
            drivers.extend(list(self._active_drivers))
        try:
            with self._driver_lock:
                drivers.extend(list(self._worker_drivers.values()))
        except Exception:
            pass
        try:
            drivers.extend(list(self._preloaded_drivers))
        except Exception:
            pass
        try:
            if self._bet_driver:
                drivers.append(self._bet_driver)
        except Exception:
            pass
        # One process listing, reused for every driver. Calling the lister per
        # driver meant one PowerShell spawn (and one console flash) each.
        listing = _our_chrome_pids()
        for d in drivers:
            # session_id is a chromedriver SESSION KEY, not an OS pid — using it
            # as one could accidentally protect the wrong process. Resolve the
            # real browser pid from the temp profile we handed that driver.
            try:
                prof = getattr(d, "_sportsape_temp_profile", None)
                if prof:
                    for pid, cmd in listing:
                        if prof.lower() in cmd.lower():
                            pids.add(pid)
            except Exception:
                continue
            try:
                service = getattr(d, "service", None)
                spid = getattr(service, "process", None)
                if spid is not None and getattr(spid, "pid", None):
                    pids.add(int(spid.pid))
            except Exception:
                continue
        return pids

    def _cleanup_driver(self, driver) -> None:
        if not driver:
            return
        temp_profile = getattr(driver, "_sportsape_temp_profile", None)
        # Release this browser's claim on the account so the next build (or the
        # other worker) can take it. Without this a crashed/quit driver keeps the
        # account locked for the life of the process.
        acct = getattr(driver, "_sportsape_account", None)
        with self._active_drivers_lock:
            self._active_drivers.discard(driver)
        try:
            driver.quit()
        except Exception:
            pass
        if acct:
            try:
                _release_account_session(acct)
            except Exception:
                pass
            try:
                driver._sportsape_account = None
            except Exception:
                pass
        if temp_profile and os.path.exists(temp_profile):
            shutil.rmtree(temp_profile, ignore_errors=True)
        if self.selenium_driver is driver:
            self.selenium_driver = None
        # NOTE: deliberately do NOT reap here. This is the hot path — it runs on
        # every driver teardown while other workers are mid-bet. Reaping any
        # sportsape chrome not perfectly matched in the exclusion set killed
        # live worker browsers and produced the "consecutive aborts" loop.
        # Orphans are swept once at startup and once at shutdown, when nothing
        # of ours is in use.

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
                      headless=None, capture_perf=True, minimize=False,
                      phone=None) -> webdriver.Chrome:
        # ONE BROWSER PER ACCOUNT. Building a driver for an account another
        # process already owns would create a second session and get BOTH tokens
        # revoked ("logged in from another device"). Ownership itself is claimed
        # in _set_account_driver so claim/release stay exactly paired; this is an
        # early check so we fail loudly instead of launching a doomed browser.
        _account_guard = str(phone) if phone is not None else None
        if _account_guard is not None:
            _who = _account_session_holder(_account_guard)
            if _who.get("held") and _who.get("pid") != os.getpid():
                raise RuntimeError(
                    f"refusing to open a browser for {_account_guard}: another "
                    f"process (pid {_who.get('pid')}) already drives that account. "
                    f"Two sessions on one account = 403 'logged in from another device'.")
        options = Options()
        # 'normal' waits for EVERY subresource: ad tags, trackers, pixels and the
        # live-score websocket on today's-games. On this SPA that regularly blew
        # past the page-load timeout and surfaced as
        #   "tab crashed" / "Timed out receiving message from renderer",
        # which cost a full browser rebuild each time (12+ in the crash trace).
        # 'eager' returns at DOMContentLoaded and lets the crawler's existing
        # explicit waits (row counts, staleness, placeable counts) do the
        # synchronising — that is where the real readiness check already lives.
        options.page_load_strategy = 'eager'
        use_headless = self.headless if headless is None else bool(headless)
        if use_headless:
            options.add_argument("--headless=new")
        if mobile:
            options.add_argument("--window-size=430,932")
        else:
            options.add_argument("--window-size=1280,800")
        options.add_argument("--disable-gpu")
        options.add_argument("--no-sandbox")
        options.add_argument("--disable-dev-shm-usage")   # Linux-only, no-op here; kept for parity
        # --disable-dev-shm-usage does nothing on Windows, so nothing was ever
        # bounding renderer memory. The extended board pulls 150+ fixtures of
        # live odds — each a ticking DOM subtree — and one renderer can blow its
        # budget and die outright ("tab crashed"). Cap the heap so an over-budget
        # renderer GCs instead of taking the tab with it.
        options.add_argument("--js-flags=--max-old-space-size=768")
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
        # ── RAM and CPU savings — keeps the tool lightweight ───────────────
        options.add_argument("--disable-background-networking")
        options.add_argument("--disable-background-timer-throttling")
        options.add_argument("--disable-backgrounding-occluded-windows")
        options.add_argument("--disable-breakpad")          # no crash reports
        options.add_argument("--disable-component-update")
        options.add_argument("--disable-client-side-phishing-detection")
        options.add_argument("--disable-default-apps")
        options.add_argument("--disable-hang-monitor")
        options.add_argument("--disable-popup-blocking")
        options.add_argument("--disable-prompt-on-repost")
        options.add_argument("--disable-sync")
        options.add_argument("--disable-translate")
        options.add_argument("--metrics-recording-only")
        options.add_argument("--no-service-autorun")
        options.add_argument("--password-store=basic")
        options.add_argument("--safebrowsing-disable-auto-update")
        # Don't load images in headless mode — the scraper only needs DOM text
        if use_headless:
            options.add_experimental_option("prefs", {
                "credentials_enable_service": False,
                "profile.password_manager_enabled": False,
                "autofill.profile_enabled": False,
                "autofill.credit_card_enabled": False,
                "profile.managed_default_content_settings.images": 2,  # block images
            })
        # STEALTH: present a real Chrome in headless so Akamai/Cloudflare
        # challenges cannot fingerprint the default "HeadlessChrome" UA.
        if use_headless:
            options.add_argument("--headless=new")
            options.add_argument("--lang=en-KE")
            options.add_argument(f"--user-agent={self.STEALTH_UA}")
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

        # Put the ACCOUNT in the profile directory name (2026-10-05).
        #
        # WHY: until now every profile was `sportsape_chrome_<random>`, so
        # neither an operator nor the reaper could tell which account an
        # orphaned browser belonged to. With two accounts running we measured 4
        # live profiles and could not say which 2 were legitimate. That made it
        # impossible to scope the orphan sweep to one account - the very thing
        # that stops two browsers fighting over one session.
        #
        # The random suffix still guarantees uniqueness; the phone simply makes
        # each profile self-identifying in the process list, in the temp folder
        # listing, and in our own logs. Falls back to a neutral token when no
        # phone is known.
        _acct_tag = "".join(ch for ch in str(phone or "") if ch.isdigit())[:12]
        if not _acct_tag:
            _acct_tag = "shared"
        # ONE BROWSER PER ACCOUNT.
        #
        # ROLLED BACK OUT OF THIS HOT PATH (2026-10-05). Calling the duplicate
        # sweep here looked thorough, but `_build_driver` is on the critical
        # path of EVERY browser start and the sweep shells out to a CIM query
        # over all chrome processes. Doing that inline stalled the workers:
        # both accounts went silent and Fibi reported "ENGINE STALL: no round
        # completed in ~16 min". Correctness is not worth a stalled engine, so
        # the sweep now runs only at the explicit round-start call sites (where
        # it was already wired) and is throttled there.
        temp_profile = tempfile.mkdtemp(prefix=f"sportsape_chrome_{_acct_tag}_")
        options.add_argument(f"--user-data-dir={temp_profile}")
        # Stability for concurrent workers: prevent the renderer from hanging
        # (which surfaces as "timeout: Timed out receiving message from renderer")
        # when multiple Chrome instances share /dev/shm.
        options.add_argument("--disable-dev-shm-usage")
        options.add_argument("--no-sandbox")
        options.add_argument("--disable-gpu")
        options.add_argument("--disable-software-rasterizer")

        try:
            # Resolve the driver from the LOCAL cache first: an empty Service
            # path makes Selenium Manager phone googlechromelabs.github.io on
            # every launch, and when that fetch is slow it raises and the
            # session dies with the generic "Unable to obtain driver for
            # chrome" (measured live 2026-10-16: every win-sync failed for 40
            # minutes while a matching driver sat in the cache). An explicit
            # path makes DriverFinder skip the manager altogether.
            try:
                import betflow as _bf
                _drv = _bf.local_chromedriver()
            except Exception:
                _drv = ""
            try:
                service = Service(executable_path=_drv)
                driver = webdriver.Chrome(service=service, options=options)
            except Exception:
                if not _drv:
                    raise
                # Cached driver rejected -> let the manager resolve one.
                service = Service()
                driver = webdriver.Chrome(service=service, options=options)
            self._track_active_driver(driver)
            self.selenium_driver = driver

            driver.set_page_load_timeout(90)
            driver.set_script_timeout(45)

            # STEALTH CDP layer: hide automation fingerprints, spoof the UA and
            # client-hint headers to match a genuine Chrome on Windows (this is what
            # lets headless sessions pass Akamai's JS/header checks on the widget).
            try:
                driver.set_page_load_timeout(30)
                driver.set_script_timeout(10)
            except Exception:
                pass
            try:
                driver.execute_cdp_cmd("Page.addScriptToEvaluateOnNewDocument", {"source": (
                    "Object.defineProperty(navigator, 'webdriver', {get: () => undefined});"
                    "Object.defineProperty(navigator, 'languages',"
                    " {get: () => ['en-KE', 'en-US', 'en']});"
                    "Object.defineProperty(navigator, 'plugins', {get: () => [1,2,3,4,5]});"
                    "window.chrome = window.chrome || {runtime: {}};"
                )})
                driver.execute_cdp_cmd("Emulation.setUserAgentOverride", {
                    "userAgent": self.STEALTH_UA,
                    "acceptLanguage": "en-KE,en-US;q=0.9,en;q=0.8",
                    "platform": "Win32",
                })
                driver.execute_cdp_cmd("Network.setExtraHTTPHeaders", {
                    "headers": {
                        "Accept-Language": "en-KE,en-US;q=0.9,en;q=0.8",
                        "sec-ch-ua": ('"Chromium";v="138", "Google Chrome";v="138", '
                                       '"Not.A/Brand";v="24"'),
                        "sec-ch-ua-mobile": "?0",
                        "sec-ch-ua-platform": '"Windows"',
                    }
                })
            except Exception:
                pass
            
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
            # Deliberately NOT stamped with the account here: _build_driver only
            # performs the cross-process guard above. The claim is taken in
            # _set_account_driver, which is the single point paired with release
            # on teardown. Stamping here would mark a driver as owning an
            # account whose lock was never actually taken.
            driver._sportsape_account = None  # type: ignore[attr-defined]
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
                exc_s = str(exc).lower()
                # A renderer timeout usually leaves the tab mid-navigation and
                # the old document still on screen, so re-issuing get() straight
                # away can wedge on the same pending work. Tear the session down
                # first: a hung renderer almost never recovers, and the caller's
                # own rebuild path handles a genuinely dead browser. One cheap
                # stop/start is still worth trying because it is far cheaper than
                # the full driver rebuild this used to trigger.
                if "tab crashed" in exc_s or "no such window" in exc_s:
                    self._emit_direct(None, f"   ⚠️ tab crashed navigating — discarding "
                                            f"browser ({i + 1}/{attempts})")
                    raise
                if "invalid session id" in exc_s:
                    self._emit_direct(None, f"   ⚠️ session lost navigating "
                                            f"({i + 1}/{attempts})")
                    raise
                self._emit_direct(None, f"   ↻ retry navigating to page ({i + 1}/{attempts})")
                try:
                    driver.execute_script("window.stop();")
                except Exception:
                    pass
                time.sleep(2)
        raise last

    def _exec_script(self, driver, code: str, default=None, timeout: float = 12.0,
                     refresh_on_hang: bool = False, label: str = "script") -> object:
        """Run page-side JS behind a short, bounded timeout so a busy/stuck
        renderer can NEVER stall a maintenance task or surface the raw
        'Timed out receiving message from renderer' error.

        A renderer that is busy with the heavy SPA (animations, infinite
        scroll, ads) stops answering CDP commands; with the default 45s script
        timeout that means up to 45 seconds of blocking per call. Here the call
        is capped at `timeout` seconds, and on the specific renderer-hang
        exception it retries once after a page refresh when asked, then returns
        `default` with a single calm note — the task continues next cycle with
        a fresh page. Unrelated JS errors still propagate.
        """
        prev = None
        try:
            prev = driver.timeouts.script
        except Exception:
            prev = None
        try:
            try:
                driver.set_script_timeout(timeout)
            except Exception:
                pass
            return driver.execute_script(code)
        except Exception as exc:
            msg = str(exc)
            is_hang = ("Timed out receiving message from renderer" in msg
                       or "script timeout" in msg or "renderer" in msg.lower())
            if is_hang and refresh_on_hang:
                try:
                    time.sleep(1.0)
                    self._safe_get(driver, driver.current_url, attempts=1)
                    driver.set_script_timeout(timeout)
                    return driver.execute_script(code)
                except Exception:
                    pass
            if is_hang:
                self._emit_direct(None, f"   ⏸️ Renderer busy — {label} skipped (will retry next cycle)")
                return default
            raise
        finally:
            if prev is not None:
                try:
                    driver.set_script_timeout(prev)
                except Exception:
                    pass

    def _exec_async_script(self, driver, code: str, default=None, timeout: float = 12.0,
                           label: str = "async script") -> object:
        """execute_async_script variant of _exec_script — same bounded-timeout,
        renderer-hang-safe behavior (used by the wallet/API page probes)."""
        prev = None
        try:
            prev = driver.timeouts.script
        except Exception:
            prev = None
        try:
            try:
                driver.set_script_timeout(timeout)
            except Exception:
                pass
            return driver.execute_async_script(code)
        except Exception as exc:
            msg = str(exc)
            if ("Timed out receiving message from renderer" in msg
                    or "script timeout" in msg or "renderer" in msg.lower()):
                self._emit_direct(None, f"   ⏸️ Renderer busy — {label} skipped (will retry next cycle)")
                return default
            raise
        finally:
            if prev is not None:
                try:
                    driver.set_script_timeout(prev)
                except Exception:
                    pass

    def _emit_direct(self, gui_callback, message: str) -> None:
        """Internal emit that bypasses the verbose check for critical diagnostics.
        Dedup: collapse identical messages within 45s into one."""
        now = time.time()
        key = str(message).strip().lower().replace(" ", "")
        _prev_key = getattr(self, "_last_emit_key", None)
        _prev_time = float(getattr(self, "_last_emit_time", 0.0) or 0.0)
        if key == _prev_key and (now - _prev_time) < 45:
            return
        self._last_emit_key = key
        self._last_emit_time = now
        try:
            self._log_ring.append((time.time(), str(message)))
        except Exception:
            pass
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
// Collect all matching nodes, then pick the best: exact text match first,
// then the rightmost (highest x) so the "Agree"/"Accept" button on the RIGHT
// of a two-button modal is chosen over a "Disagree"/"Decline" on the left.
const matches = [];
for (const node of nodes) {
  if (!visible(node)) continue;
  const text = (node.innerText || node.textContent || '').trim().toLowerCase().replace(/\\s+/g, ' ');
  if (!text) continue;
  const exact = labels.some(label => text === label);
  const sub = !exact && labels.some(label => text.includes(label));
  if (exact || sub) {
    const r = node.getBoundingClientRect();
    matches.push({ node, exact, x: r.left + r.width / 2, text });
  }
}
// exact matches first, then rightmost
matches.sort((a, b) => (b.exact - a.exact) || (b.x - a.x));
for (const m of matches) {
  if (click(m.node)) return true;
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
                    "i agree",
                    "i accept",
                    "confirm",
                    "ok",
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

    def _force_clear_session(self, driver: webdriver.Chrome) -> None:
        """Make sure NO account session survives on this driver before switching
        to another account. Best-effort logout click first, then wipe client-side
        auth storage so a stale session can never place bets under the wrong phone."""
        try:
            from selenium.webdriver.common.by import By
        except Exception:
            By = None
        # 1) Try the visible logout control first.
        if not self._logout_current_session(driver):
            # 2) If the user-menu is collapsed, toggle it (mobile/login header).
            self._click_by_text(driver, ["account", "my account", "profile", "menu"])
        self._logout_current_session(driver)
        # 3) Blow away client-side auth regardless of UI (cookies, localStorage,
        #    sessionStorage, IndexedDB). SportPesa keeps sessions in web storage,
        #    so a failed UI logout cannot leave the old account live.
        try:
            driver.execute_script("""
try {
  localStorage.clear();
  sessionStorage.clear();
  var dbs = indexedDB.databases ? indexedDB.databases() : Promise.resolve([]);
  dbs.then(function(list){
    list.forEach(function(db){ indexedDB.deleteDatabase(db.name); });
  });
} catch (e) {}
return true;
""")
        except Exception:
            pass
        try:
            cookie_hosts = {c.get("domain", "").lstrip(".") for c in (driver.get_cookies() or [])}
            for host in cookie_hosts:
                try:
                    driver.delete_all_cookies()
                except Exception:
                    pass
        except Exception:
            pass
        # 4) A fresh document confirms logout (no stored session phone).
        try:
            driver.get(self.LOGIN_URL)
            time.sleep(0.6)
        except Exception:
            pass

    def _logout_current_session(self, driver: webdriver.Chrome) -> bool:
        self._dismiss_visible_promos(driver, rounds=1)
        clicked = False
        # Order matters: prefer the explicit control. The bare "exit" token is a
        # last resort because it also matches incidental text ("exit speed")
        # and could activate the wrong control entirely.
        for labels in (["logout", "log out", "sign out", "exit login", "log-out"],
                       ["exit"]):
            try:
                if self._click_by_text(driver, labels):
                    clicked = True
                    break
            except Exception:
                continue
        if clicked:
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

            # Recurse into nested wallets (e.g. {"casino": {...}, "sportsbook": {...}}).
            # The betting balance lives in the SPORTSBOOK wallet — the casino wallet
            # can legitimately read 0.0, so we must NOT let a casino 0.0 mask the
            # real sportsbook figure. Prefer sportsbook; fall back to the largest
            # explicit balance found.
            nested_snaps = []
            for value in data.values():
                nested = self._extract_wallet_snapshot_from_json(value)
                if nested is not None:
                    nested_snaps.append(nested)
            best = self._prefer_wallet_snapshot(nested_snaps)
            if best is not None:
                if current["balance"] is None:
                    current["balance"] = best.get("balance")
                elif best.get("balance") is not None:
                    current["balance"] = max(current["balance"], best.get("balance"))
                if not current["bonus"]:
                    current["bonus"] = best.get("bonus", 0.0)
                if not current["coins"]:
                    current["coins"] = best.get("coins", 0.0)

            return self._finalize_wallet_snapshot(current)

        elif isinstance(data, list):
            snaps = []
            for item in data:
                nested = self._extract_wallet_snapshot_from_json(item)
                if nested is not None:
                    snaps.append(nested)
            return self._prefer_wallet_snapshot(snaps)

        return None

    def _prefer_wallet_snapshot(self, snaps: list) -> dict | None:
        """From a list of wallet snapshots pick the authoritative betting balance:
        the sportsbook wallet when present, else the largest explicit balance."""
        if not snaps:
            return None
        sportsbook = [s for s in snaps if s.get("bonus") is not None or s.get("balance") is not None]
        return max(snaps, key=lambda s: float(s.get("balance") or 0))

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
            data = self._exec_async_script(
                driver,
                """
                var done = arguments[arguments.length - 1];
                var controller = new AbortController();
                var timeoutId = setTimeout(function() { controller.abort(); }, 12000);
                fetch('/api/wallets/balance', {credentials: 'include', cache: 'no-store', signal: controller.signal})
                    .then(function (r) { clearTimeout(timeoutId); return r.json(); })
                    .then(function (d) { done(d); })
                    .catch(function () { clearTimeout(timeoutId); done(null); });
                """,
                default=None, timeout=10.0, label="wallet API snapshot")
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
            page_wallet = self._exec_script(driver, script, default=None, timeout=8.0,
                                            refresh_on_hang=True, label="page wallet snapshot")
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
                # API-first: replay a previously-captured withdraw endpoint when known.
                withdrew = False
                try:
                    api_r = self._try_api_wallet_action(driver, "withdraw",
                                                        {"amount": int(amount)})
                except Exception:
                    api_r = {"success": False}
                if api_r.get("success"):
                    withdrew = True
                    self._emit_direct(gui_callback,
                                      f"  ✅ Withdraw via API endpoint: KES {amount:,.0f}")
                if not withdrew:
                    self._inject_xhr_capture(driver)
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

                if withdrew:
                    try:
                        captured = self._read_xhr_capture(driver, "wallet")
                        if captured:
                            best = captured[-1]
                            self._save_captured_route("withdraw", {
                                "url": best.get("url", ""),
                                "method": best.get("method", "POST"),
                                "captured_at": int(best.get("t", 0)),
                                "note": "Auto-captured from live withdraw page"
                            })
                            self._emit_direct(gui_callback,
                                              f"  📡 Learned withdraw endpoint: {best.get('url', '?')}")
                    except Exception:
                        pass

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
        pre-planned slip automatically. Login is retried and serialized.

        Serialization: each account now owns ONE dedicated browser session (the
        per-account worker). A deposit grabs that account's session lock and reuses
        its dedicated driver — so there is never a second login on the same account
        and the other accounts' workers keep betting untouched. If the account has
        no session yet, one is built and registered for its worker to inherit.
        """
        self._emit_direct(gui_callback,
                          f"DEPOSIT: KES {float(amount):,.2f} via M-Pesa (STK push → phone)")
        result = {"status": "error", "message": "Deposit not submitted"}
        driver = None
        borrowed = False
        lock = self._account_session_lock(phone)
        _got_lock = False
        _lock_waits = 0
        # Long first rounds (driver build + login + crawl) can hold the account's
        # session lock for several minutes; wait it out in passes instead of giving
        # up, so a deposit always slips in the moment the account is between rounds.
        while _lock_waits < 6:
            _got_lock = lock.acquire(timeout=60)
            if _got_lock:
                break
            _lock_waits += 1
            self._emit_direct(gui_callback,
                              f"  ⏳ {phone} is mid-round — deposit waits its turn "
                              f"(attempt {_lock_waits} of 6)...")
        if not _got_lock:
            self._emit_direct(gui_callback,
                              f"  ⏳ Account {phone} stayed busy ~6 min — deposit deferred, "
                              "retry shortly.")
            return result
        try:
            # Use THIS account's dedicated session (single login per account).
            with self._driver_lock:
                driver = self._worker_drivers.get(str(phone))
            if driver is not None and self._driver_is_usable(driver):
                borrowed = True
                self._emit_direct(gui_callback,
                                  f"   Using {phone}'s dedicated session (no second login)...")
            else:
                driver = self._set_account_driver(
                    phone, self._acquire_driver(gui_callback=gui_callback))
                self._emit_direct(gui_callback,
                                  "   Opened a fresh session for this account "
                                  "(the account worker will inherit it).")
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            try:
                logged_in = bool(self._session_is_live(driver))
            except Exception:
                logged_in = False
            if not logged_in:
                self._emit_direct(gui_callback,
                                  "  ⚠️ Login didn't confirm — opening the deposit page anyway "
                                  "(works if the session is actually live).")

            self._emit_direct(gui_callback, "  Opening deposit page (unified multi-URL flow)...")
            self._inject_xhr_capture(driver)
            _deposit_urls = [
                f"{SITE_ORIGIN}/deposit_funds",
                f"{SITE_ORIGIN}/en/deposit",
                f"{SITE_ORIGIN}/deposit",
            ]
            try:
                with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                       "config", "discovered_sportsape_routes.json"),
                          encoding="utf-8") as _f:
                    _saved = json.load(_f).get("wallet", {}).get("deposit")
                    if _saved and _saved.get("url"):
                        from urllib.parse import urlparse
                        _pu = urlparse(_saved["url"])
                        _saved_path = _pu.path + ("?" + _pu.query if _pu.query else "")
                        if _saved_path not in {"".join(urlparse(u).path + ("?" + urlparse(u).query if urlparse(u).query else "")) for u in _deposit_urls}:
                            _deposit_urls.append(f"{SITE_ORIGIN}{_saved_path}")
            except Exception:
                pass

            deposited = False

            # A deposit URL that never fires the page-load event would block
            # driver.get() for ChromeDriver's default 300s (measured 2026-10-09:
            # account 2 frozen on /en/deposit for minutes inside the exe). Cap
            # the load so the URL loop advances and the API fallback fires.
            try:
                driver.set_page_load_timeout(30)
                driver.set_script_timeout(30)
            except Exception:
                pass

            def _try_fill_and_submit(drv, amt, ui_cb) -> bool:
                """Find amount input (main doc or iframe) + submit button; return True if clicked."""
                search_scopes = [(drv, "main")]
                try:
                    for _fr in drv.find_elements(By.TAG_NAME, "iframe"):
                        try:
                            drv.switch_to.frame(_fr)
                            search_scopes.append((drv, "iframe"))
                            drv.switch_to.default_content()
                        except Exception:
                            try:
                                drv.switch_to.default_content()
                            except Exception:
                                pass
                except Exception:
                    pass
                for _scope_drv, _tag in search_scopes:
                    try:
                        if _tag == "iframe":
                            try:
                                drv.switch_to.default_content()
                                _all_fr = drv.find_elements(By.TAG_NAME, "iframe")
                                for _fr in _all_fr:
                                    try:
                                        drv.switch_to.frame(_fr)
                                        break
                                    except Exception:
                                        continue
                            except Exception:
                                continue
                        amount_inp = None
                        for _sel in ("input#safaricom_amount[name='amount']",
                                     "input[name='amount']",
                                     "input[placeholder*='mount']",
                                     "input[data-qa*='amount']",
                                     "input[aria-label*='amount' i]"):
                            try:
                                amount_inp = _scope_drv.find_element(By.CSS_SELECTOR, _sel)
                                break
                            except Exception:
                                continue
                        if amount_inp is None:
                            amount_inp = next((i for i in _scope_drv.find_elements(By.CSS_SELECTOR, "input")
                                               if "safaricom" in ((i.get_attribute("id") or "") + (i.get_attribute("placeholder") or "")).lower()),
                                              None)
                        if amount_inp is None:
                            _all_inputs = _scope_drv.find_elements(By.CSS_SELECTOR,
                                                                    "input[type='number'], input[type='text'], input")
                            for inp in _all_inputs:
                                try:
                                    pt = (inp.find_element(By.XPATH, "..").text or "").lower()
                                    ph = (inp.get_attribute("placeholder") or "").lower()
                                    nm = (inp.get_attribute("name") or inp.get_attribute("id") or "").lower()
                                    if any(k in pt + ph + nm for k in ["amount", "kes", "topup", "top up"]):
                                        amount_inp = inp
                                        break
                                except Exception:
                                    continue
                        if amount_inp is None:
                            try:
                                drv.switch_to.default_content()
                            except Exception:
                                pass
                            continue
                        try:
                            amount_inp.clear()
                        except Exception:
                            pass
                        amount_inp.send_keys(str(int(float(amt))))
                        self._emit_direct(ui_cb,
                                          f"  [{_tag}] Amount set: KES {amt:,.0f}")
                        btn_candidates = []
                        for _sel in ["button.amount-input-button", "button", "input[type='submit']",
                                     ".paybtn.clickScale.flex-box-row.middle", ".btnPwd .paybtn",
                                     "[role='button']", "a[href*='deposit' i]"]:
                            try:
                                btn_candidates.extend(_scope_drv.find_elements(By.CSS_SELECTOR, _sel))
                            except Exception:
                                continue
                        for _idx, btn in enumerate(btn_candidates[:60]):
                            try:
                                if not btn.is_displayed():
                                    continue
                                t = (btn.text or btn.get_attribute("value") or btn.get_attribute("aria-label") or "").strip().lower()
                                if any(k in t for k in ["deposit", "pay", "continue", "confirm", "mpesa", "stk", "submit"]):
                                    if "loading" in t or "disabled" in (btn.get_attribute("class") or "").lower():
                                        continue
                                    btn.click()
                                    try:
                                        drv.switch_to.default_content()
                                    except Exception:
                                        pass
                                    self._emit_direct(ui_cb,
                                                      f"  [{_tag}] Payment submitted — STK push sent to your phone.")
                                    return True
                            except Exception:
                                continue
                        try:
                            drv.switch_to.default_content()
                        except Exception:
                            pass
                    except Exception as _fe:
                        try:
                            drv.switch_to.default_content()
                        except Exception:
                            pass
                        continue
                try:
                    drv.switch_to.default_content()
                except Exception:
                    pass
                return False

            for _ui, _url in enumerate(_deposit_urls, 1):
                if deposited:
                    break
                self._emit_direct(gui_callback, f"  URL {_ui}/{len(_deposit_urls)}: {_url.replace(SITE_ORIGIN,'')}")
                try:
                    driver.get(_url)
                    WebDriverWait(driver, 25).until(
                        lambda d: d.execute_script("return document.readyState") == "complete"
                        or d.execute_script("return document.body && document.body.innerText.length > 200"))
                except Exception:
                    pass
                _loaded = time.time() + 15
                while time.time() < _loaded and not deposited:
                    try:
                        _bt = driver.execute_script("return (document.body && document.body.innerText) || '';").lower()
                        if any(k in _bt for k in ["amount", "mpesa", "safaricom", "deposit", "top up"]):
                            break
                    except Exception:
                        pass
                    time.sleep(1.5)
                for _pr in range(3):
                    try:
                        self._dismiss_visible_promos(driver, rounds=2)
                    except Exception:
                        pass
                    try:
                        for _el in driver.find_elements(By.CSS_SELECTOR,
                                                        ".modal .close, [data-dismiss], ._close, .popup-close, .cta-close"):
                            try:
                                if _el.is_displayed():
                                    _el.click()
                            except Exception:
                                continue
                    except Exception:
                        pass
                    time.sleep(0.8)
                try:
                    if _try_fill_and_submit(driver, amount, gui_callback):
                        deposited = True
                        break
                except Exception as _e:
                    self._emit_direct(gui_callback, f"  [{_ui}] form scan: {str(_e)[:60]}")
                if _ui == 2 and not deposited:
                    try:
                        self._emit_direct(gui_callback, "  Trying captured API deposit endpoint early...")
                        _api_r = self._try_api_wallet_action(driver, "deposit",
                                                             {"amount": int(float(amount))})
                        if _api_r.get("success"):
                            deposited = True
                            self._emit_direct(gui_callback,
                                              "  ✅ API deposit — STK push sent to your phone.")
                            break
                    except Exception:
                        pass

            if not deposited:
                try:
                    self._emit_direct(gui_callback, "  Last resort: API deposit fallback.")
                    _api_r = self._try_api_wallet_action(driver, "deposit",
                                                         {"amount": int(float(amount))})
                    if _api_r.get("success"):
                        deposited = True
                        self._emit_direct(gui_callback,
                                          "  ✅ API fallback — STK push sent to your phone.")
                except Exception:
                    pass

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
                try:
                    captured = self._read_xhr_capture(driver, "wallet")
                    if captured:
                        best = captured[-1]
                        self._save_captured_route("deposit", {
                            "url": best.get("url", ""),
                            "method": best.get("method", "POST"),
                            "captured_at": int(best.get("t", 0)),
                            "note": "Auto-captured from live deposit page"
                        })
                        self._emit_direct(gui_callback,
                                          f"  📡 Learned deposit endpoint: {best.get('url', '?')}")
                except Exception:
                    pass

            if not deposited:
                self._emit_direct(gui_callback, "  Could not find the deposit form. Dumping page...")
                try:
                    body = driver.execute_script("return document.body.innerText.substring(0,500)")
                    self._emit_direct(gui_callback, f"  Page: {body}")
                except Exception:
                    pass

            if not borrowed:
                try:
                    self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                except Exception:
                    pass
            self._engine_state["_balance_refreshed"] = False
            try:
                _recheck, _rc_ok = self._read_balance_confirmed(driver, wait=10.0)
                if _rc_ok:
                    self._balance_cache = getattr(self, "_balance_cache", None) \
                        or self._load_balance_cache()
                    self._balance_cache[str(phone)] = {
                        "balance": _recheck, "confirmed": True, "ts": time.time()}
                    self._save_balance_cache()
                    self._engine_state["_balance_refreshed"] = True
                    self._emit_direct(gui_callback,
                                      f"  ⚡ Post-deposit balance for {phone}: KES {_recheck:,.2f}")
            except Exception:
                pass
            result = {"status": "success" if deposited else "error",
                      "message": "STK sent" if deposited else "Form not found"}
            self._emit_direct(gui_callback,
                              f"DONE: {'STK push sent — approve it on your phone, the machine will bet once funds land.' if deposited else 'deposit form not found'}")
            return result
        except Exception as e:
            self._emit_direct(gui_callback, f"Deposit error: {str(e)[:120]}")
            return result
        finally:
            # Return the account's dedicated session untouched; a brand-new deposit
            # session has already been REGISTERED as the account's session (its
            # worker re-logs-in on the next round). No pool reset here — that would
            # double-own the same browser.
            if borrowed:
                try:
                    self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                except Exception:
                    pass
            try:
                lock.release()
            except Exception:
                pass

    def deposit_funds_multi(self, phones, password, amount, gui_callback=None):
        """Fund EVERY account. Each account receives its own M-Pesa STK push
        (approve on the phone). After that the machine keeps running: any account
        in WIN-FUNDED WAIT resumes the moment its funds land, and all per-account
        workers keep betting until day caps.
        Deposits for different accounts run concurrently — each waits only on its
        own account's session lock, never on another account's queue.
        """
        seen = []
        for phone in phones:
            if phone in seen:
                continue
            seen.append(phone)
        targets = seen
        if not targets:
            return {"status": "success", "results": []}
        self._emit_direct(
            gui_callback,
            f"💳 Deposit request: KES {float(amount):,.2f} each for "
            f"{', '.join(targets)} (M-Pesa — one STK push per account; "
            "approve each on your phone; the machine bets as funds land).")
        _done = {}

        def _run_one(p):
            try:
                _done[str(p)] = self.deposit_funds_browser(p, password, amount,
                                                           gui_callback=gui_callback)
            except Exception as e:
                self._emit_direct(gui_callback, f"Deposit error {p}: {str(e)[:100]}")
                _done[str(p)] = {"status": "error"}
        _threads = [threading.Thread(target=_run_one, args=(p,), daemon=True)
                    for p in targets]
        for t in _threads:
            t.start()
        for t in _threads:
            t.join()
        results = [{"phone": p,
                    "status": _done.get(str(p), {}).get("status", "error")
                              if isinstance(_done.get(str(p)), dict) else "error"}
                   for p in targets]
        ok_count = sum(1 for r in results if r.get("status") == "success")
        self._emit_direct(
            gui_callback,
            f"💵 FUNDING DONE: {ok_count}/{len(results)} account(s) got their "
            f"KES {float(amount):,.0f} STK push. Approve each prompt on the phone — "
            "the machine bets as funds land and keeps going until the day caps.")
        return {"status": "success" if ok_count == len(results) else "partial",
                "results": results}

    def _pool(self) -> float:
        """Current savings reserve. Waived automatically when balance is critically
        low so the pool never blocks a KES 10 bet when the account only has KES 15."""
        self._load_stats()
        try:
            pool = round(max(0.0, float(self._stats.get("savings_pool") or 0.0)), 2)
            return pool
        except Exception:
            return 0.0

    def _effective_pool(self, balance: float, stake: float) -> float:
        """Return the effective pool reserve to apply for this bet.

        If balance < 3 × stake the pool is waived — no point protecting savings
        when there's barely enough to place even one bet.  The pool will rebuild
        from the next win.
        """
        pool = self._pool()
        if pool <= 0:
            return 0.0
        # Waive the pool if it would block the bet
        if float(balance) < float(stake) * 3:
            return 0.0
        return pool

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
    UPCOMING_GAMES_PAGE_URL = "https://www.ke.sportpesa.com/en/sports-betting/football-1/upcoming-games/"
    # Football-1 home listing — has upcoming games beyond just "today"; used as
    # a fallback when the today-games tab returns zero rows (e.g. late night or
    # early morning when the day hasn't loaded yet).
    FOOTBALL_HOME_URL = "https://www.ke.sportpesa.com/en/sports-betting/football-1/"
    # Popular-games listing — another fixture feed that often carries more rows
    # than the today tab, so the board-gather merges it too.
    POPULAR_GAMES_URL = "https://www.ke.sportpesa.com/en/sports-betting/football-1/popular-games/"
    BETS_HISTORY_URL = "https://www.ke.sportpesa.com/bets/history"
    LEDGER_PATH = Path(writable_path("sportsape_ledger.json"))
    BALANCES_PATH = Path(writable_path("sportsape_balances.json"))
    BALANCES_TTL_SECONDS = 300  # re-read a cached balance after 5 minutes
    BALANCES_STALE_TTL_SECONDS = 3600  # stale fallback valid up to 1 hour (only when live read fails)
    SCHED_STATE_PATH = Path(writable_path("sportsape_sched_state.json"))
    LEDGER_ARCHIVE_PATH = Path(writable_path("sportsape_ledger_archive.json"))
    LEDGER_KEEP_SETTLED_DAYS = 14  # settled rows older than this drop into the archive
    USAGE_PATH = Path(writable_path("sportsape_usage.json"))
    STATS_PATH = Path(writable_path("sportsape_stats.json"))
    WITHDRAW_PATH = Path(writable_path("sportsape_withdraw.json"))
    FORM_CACHE_PATH = Path(writable_path("sportsape_form_cache.json"))
    FORM_TTL_SECONDS = 6 * 3600  # team form is refreshed at most every ~6h
    ENRICH_PATH = Path(writable_path("sportsape_enrich_cache.json"))
    ENRICH_TTL_SECONDS = 6 * 3600  # game enrichment (injuries, weather) valid 6h
    ODDS_HISTORY_PATH = Path(writable_path("sportsape_odds_history.json"))
    # ── OWNER DECISION (2026-10-01): Option A gate profile ───────────────────
    # "Fewer artificial gates, more bets" — but NOT at the cost of staking on
    # markets the engine is demonstrably bad at.
    #
    # RELAXED (shape gates — these were manufacturing junk legs):
    #   MIN_COMBINED_ODDS 2.50 -> 1.60. The x2.50 floor forced the engine to
    #     pad a 2-leg slip with a third coin-flip just to reach the target,
    #     which is how Salvadoran/Peruvian domestic fixtures with no form data
    #     kept ending up in real tickets. A 2-leg x1.6 slip is a genuine bet.
    #   MIN_LEG_CONF 0.55 -> 0.42, BTTS_STRONG_FLOOR 0.50 -> 0.42, so short-
    #     priced and BTTS legs are no longer deleted from the board.
    #   MIN_LEG_ODDS 1.20 -> 1.05 (still blocks 1.01/1.02 dead filler).
    #   MAX_GOALS_LEGS_PER_SLIP 2 -> 4.
    #
    # KEPT (calibration/value gates — the model is 29+ points wrong here):
    #   RAW_LEG_VETO 0.40, SLIP_MIN_EV 1.05, retired_markets, recipe vetoes,
    #   correlation caps, Kelly sizing. The ledger shows over1 priced at 84%
    #   hitting 55% over 29 trials and under575 -37 points; these gates are
    #   the only thing preventing real stakes on markets the model cannot
    #   price. Injuries + H2H scoring remain the primary filters.
    MIN_LEG_CONF = 0.42  # relaxed 0.55: only markets with a genuine shot
    # OWNER RULE (2026-10-05): never bet a leg priced 1.00-1.09.
    # The gate below is a STRICT `>` (see `if not (self.MIN_LEG_ODDS < o)`),
    # so 1.09 admits only legs at 1.10 and above — the whole 1.00-1.09 band,
    # including the 1.01/1.02/1.06 dead filler, is now excluded.
    #
    # Why: a 1.06 leg returns ~6% on the stake, so it contributes essentially
    # nothing to the payout, yet it still carries real downside (it loses on
    # the rare event and can be voided/settled early on a lineup change) and it
    # consumes one of only 6 slip slots. It also quietly drags the combined
    # odds down, which is what made the slips bottom out at x1.6-x1.9.
    #
    # Trade-off to watch: this narrows an already-thin board. The selector
    # previously reported ~24 of 33 games with "no options". If slip building
    # starts declining more often, raise MAX_SLIP_LEGS_HARD or the combined
    # floor rather than lowering this number back into dead-filler territory.
    MIN_LEG_ODDS = 1.09
    # ── EDGE-AWARE RANKING tunables (2026-10-05) ────────────────────
    # How strongly a leg's disagreement with the book influences its rank.
    # 0.0 reproduces the old pure-confidence behaviour; 0.30 is a deliberate
    # nudge that can flip a leg only when we rate it materially above the
    # price, while confidence still dominates. Higher values chase value
    # harder and accept more coin-flip legs — not recommended before the
    # calibration data is trustworthy.
    _EDGE_VALUE_WEIGHT = 1.20
    # Cap on the square-rooted edge ratio. At 1.25 a leg must look ~1.56x more
    # likely than its price implies before it saturates; this stops a single
    # noisy longshot from dominating the whole board.
    _EDGE_RATIO_CAP = 1.25
    # Share of the final rank score that comes from the edge term rather than
    # raw confidence (see _edge_key for the measurements behind this). 0.0
    # restores pure confidence-primary ranking.
    _EDGE_CONF_BLEND = 0.50
    RAW_LEG_VETO = 0.40  # hard veto: never bet a leg whose raw fair prob is below this.
                         # (2026-09-28, OWNER decision — FIRST-BET TEST): relaxed to
                         # 0.40 to match the long-shot branch. The 0.50/0.45 bars plus
                         # the x1.20 odds floor left only 3 of 25-32 games qualifying
                         # on overnight boards (every matchup evenly priced ~0.40-0.50
                         # fair), which could never build an x2.50 slip. 0.40 still
                         # admits only genuine near-even favourites and still blocks
                         # the 0.136/0.21 garbage the veto was created for. REVISIT
                         # after the first real bet lands.
    BTTS_STRONG_FLOOR = 0.42  # relaxed 0.50 -> 0.42 (Option A): BTTS legs are no
                              # longer deleted from the board, but a sub-42% GG
                              # pick is still blocked (a true coin-flip is a
                              # donation). Injuries + H2H now do the screening.
    MIN_COMBINED_ODDS = 1.6  # relaxed 2.50 -> 1.60 (Option A): the x2.50 floor
                             # was manufacturing junk — it forced a 3rd coin-flip
                             # leg onto 2-leg slips, which is how unknown
                             # domestic fixtures kept reaching real tickets.
                             # x1.60 allows a clean 2-leg slip and stops the
                             # engine padding legs just to hit a target.
    MIN_STAKE = 10.0  # OWNER RULE (2026-09-30): the KES 5 floor produced tiny
                      # tickets that grew the bank at a crawl. Floor is KES 10
                      # (never below — the owner mandates every real bet is at
                      # least KES 10), stake scales with balance/sureness and
                      # is capped at KES 20 so a single slip can't torch the
                      # bankroll.
    # OWNER RULES (2026-09-25) — the two numbers above were the whole staking
    # policy, and both were static. The 09-24 ledger adds two more:
    #  • SLIP_MIN_EV — a slip can only be staked (at ANY size) when the market-
    #    weight-corrected joint win chance times the combined odds clears this
    #    floor. Below it the slip is negative-EV once the book's margin is
    #    stripped → it's a donation, not a bet. (Mirrors the old per-leg kelly
    #    veto, applied at the SLIP level where it actually decides money.)
    #  • STAKE_BANKROLL_SHARE — even a "high-confidence" slip never risks more
    #    than this fraction of the current balance, so a young KES 6.47 bankroll
    #    can't be consumed by one too-good slip before it ever grows.
    # RELAXED 1.05 -> 0.95 (owner decision, 2026-10-02): at 1.05 the EV gate
    # rejected EVERY round — 6 consecutive FOOTBALL AUTO-BET rounds with a
    # balance read and zero real slips placed (all 4 went to shadow). It was
    # eating the whole board, not protecting it. 0.95 still refuses a slip whose
    # market-weight-corrected joint probability times the combined odds is
    # below 0.95, which keeps the worst-priced markets out while letting
    # genuinely marginal-but-positive slips through.
    SLIP_MIN_EV = 0.95
    STAKE_BANKROLL_SHARE = 0.33
    # OWNER RULE (2026-09-26), relaxed 2 -> 4 (Option A, 2026-10-01): the cap
    # existed because a 4x-"over" slip settled LOST — every leg correlated and
    # died together. Relaxed rather than removed: over-stacking the same
    # correlated goals market is still the one shape guaranteed to fail
    # together, so a hard ceiling remains even with the gates relaxed.
    MAX_GOALS_LEGS_PER_SLIP = 4
    # OWNER DECISION (2026-10-02): savings reserve OFF. At the default 0.25 the
    # KES 31.87 pool left only KES 3.39 spendable of a KES 35.26 balance — under
    # the KES 10 minimum, so the engine could not stake despite being funded and
    # active. Share is 0.0 so no new wins are banked into the reserve; the
    # existing pool is zeroed in stats (see _pool).
    DEFAULT_POOL_SHARE = 0.0  # share of each win banked toward the auto-withdraw reserve (off)

    # Market groups for the owner's market whitelist (all-on by default).
    # mk -> group; toggling a group in the GUI removes those markets entirely.
    _MK_GROUP_MAP = {
        "home": "1x2", "draw": "1x2", "away": "1x2",
        "btts": "btts", "btts_no": "btts",
        "over": "ou25", "under": "ou25",
        "over15": "ou15",
        "dc_1x": "dc", "dc_x2": "dc", "dc_12": "dc",
        "dnb_home": "dnb", "dnb_away": "dnb",
        "ftts_home": "ftts", "ftts_away": "ftts", "ftts_no": "ftts",
    }

    def _market_ok(self, mk: str) -> bool:
        """Whitelist gate: the owner toggles which market groups the selector may use."""
        wl = getattr(self, "_market_whitelist", None)
        if not wl or wl == "*":
            return True
        grp = self._MK_GROUP_MAP.get(mk)
        if grp is None and str(mk).startswith(("over", "under")):
            grp = "ou25"
        return (grp or mk) in wl


    _AUTH_COOLDOWN_S = 600.0   # 10 min quiet after repeated login rejections

    def _ensure_bet_login(self, driver, phone: str, password: str, gui_callback=None):
        """Put `driver` on the today-games page and ensure we're logged in.

        ANTI-THRASH GUARD (2026-10-05). Several components ask for a login for
        the same account in the same round (startup win-sync, balance sweep,
        jackpot research, the worker itself). Each POST /login_check supersedes
        the previous token, so they invalidate each other and the book answers
        "User logged from another device". The engine then compounded it by
        retrying the pre-slip gate 3x per round, every ~2 min — roughly 90 login
        POSTs per hour. Measured on a live run: 34 dismissals, 33 failed logins,
        31 gate failures and ZERO bets placed, with recovery never succeeding.

        We now record a successful authentication and treat a login as
        idempotent: if this account authenticated recently AND the wallet probe
        confirms the session, we do nothing at all — no POST, no dismissal, no
        logout. Repeated rejections put the account into a growing cooldown so
        the session is left alone to recover instead of being beaten to death.
        """
        key = str(phone or "")
        now = time.time()
        # Respect an active cooldown: do not touch the session at all.
        _cool = getattr(self, "_auth_backoff", {}) or {}
        _until = float(_cool.get(key) or 0.0)
        if _until > now:
            self._emit_direct(
                gui_callback,
                f"⏸️ {phone}: login backing off for "
                f"{int((_until - now) / 60) + 1} more min — repeated attempts were "
                "invalidating our own session (the book throttles back-to-back "
                "logins). Will retry when the cooldown expires.")
            return
        normalized = self._format_sportsape_login_phone(phone)
        # Idempotency: a recent successful login + a live wallet means every
        # caller in this window shares ONE token instead of replacing it.
        _authed = getattr(self, "_auth_ok_at", {}) or {}
        if (now - float(_authed.get(key) or 0.0)) < self._AUTH_COOLDOWN_S:
            try:
                if self._session_is_live(driver, deep_check=True):
                    return
            except Exception:
                pass
            # Session died inside the window — clear so we re-authenticate once.
            _authed.pop(key, None)
            self._auth_ok_at = _authed
        self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
        force_relogin = False
        try:
            force_flags = (self._engine_state or {}).get("force_relogin") or {}
            if str(phone or "") in force_flags:
                force_relogin = True
                force_flags.pop(str(phone or ""), None)
                self._emit_direct(gui_callback,
                                  f"👁️ SUPERVISOR: forcing re-login for {phone}")
                try:
                    self._logout_current_session(driver)
                except Exception:
                    pass
        except Exception:
            pass
        _ready = "loading"
        for _i in range(8):
            try:
                _ready = self._exec_script(driver, "return document.readyState",
                                           default="loading", timeout=2.0,
                                           label="readyState probe")
            except Exception:
                _ready = "loading"
            if _ready != "loading":
                break
            time.sleep(0.75)
        if _ready == "loading":
            self._emit_direct(gui_callback, "⚠️ Page still loading after retries — continuing")
        time.sleep(1)
        driver.execute_script("""
            var ov = document.querySelectorAll('[id*=responsive-image],[class*=ins-element],iframe');
            for(var i=0;i<ov.length;i++){ try{ ov[i].remove(); }catch(e){} }
        """)

        with self._login_lock:
            if phone:
                if self._hard_spa_login(driver, phone, password, gui_callback=gui_callback):
                    # Record the successful authentication so other components
                    # asking for a login in this window reuse this token instead
                    # of POSTing a second one and invalidating it.
                    try:
                        self._auth_ok_at[str(phone)] = time.time()
                        # A success clears any accumulated backoff.
                        (getattr(self, "_auth_backoff", {}) or {}).pop(str(phone), None)
                    except Exception:
                        pass
                    if self._agent_hub is not None:
                        try:
                            self._agent_hub.record_login(phone)
                        except Exception:
                            pass
                    self._dismiss_visible_promos(driver, rounds=1)
                    return
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
                        if self._agent_hub is not None:
                            try:
                                self._agent_hub.record_login(phone)
                            except Exception:
                                pass
                else:
                    if self._session_is_live(driver, deep_check=False):
                        self._emit_direct(gui_callback, "✅ Session already live — already logged in")
                        if self._agent_hub is not None:
                            try:
                                self._agent_hub.record_login(phone)
                            except Exception:
                                pass
                    else:
                        self._emit_direct(gui_callback, "⚠️ Could not find login form — continuing anyway")
            else:
                if self._session_is_live(driver, deep_check=False):
                    self._emit_direct(gui_callback, "✅ Session already live — already logged in")
                else:
                    self._emit_direct(gui_callback, "⚠️ No phone — continuing without login")
        self._dismiss_visible_promos(driver, rounds=1)

    def _spa_logged_attr(self, driver) -> str:
        """The server renders `logged=\"1\"` on the SPA only when the Symfony
        session behind it is genuinely authenticated. This is the single honest
        signal the SPA uses (isAuthenticated() -> e.logged === '1'); the old
        \"KES/deposit text\" heuristics below it are useless for gate decisions."""
        try:
            return str(self._exec_script(
                driver,
                "return (document.body && "
                "document.body.innerHTML.indexOf('logged=\"1\"') >= 0) ? '1' : '0';",
                default="0", timeout=8.0, refresh_on_hang=True, label="logged attr"))
        except Exception:
            return "0"

    def _hard_spa_login(self, driver, phone: str, password: str,
                        gui_callback=None, timeout: int = 50,
                        force: bool = False) -> bool:
        """REAL SportPesa web login. Opens the login dialog and SUBMITS the actual
        #secondary_login form (POST /login_check with username+password), then
        waits for the server-rendered page to flip `logged=\"1\"`.

        Root cause uncover: the previous flow clicked at "Login" text / mis-matched
        submit selectors, so the credentials were NEVER posted (zero network POSTs).
        The SPA then rendered logged=\"0\", placeBet() gates on isAuthenticated() and
        redirected us to /login — every round died exactly there. Submitting the real
        form fixes the session bell-to-bell.

        force=True: ALWAYS re-submit the real form, even when logged=\"1\" is already
        rendered. The SPA silently re-mounts an EMPTY page (bare body, live to the
        wallet API, logged=\"1\" intact) ~7min after login while we tour games —
        the only known way back to a hydrated slip is a genuine fresh session POST,
        so the mint gate calls us with force=True.

        INDUSTRIAL-GRADE FIX (2026-10-04): logged=\"1\" alone is NEVER accepted as
        proof of a live session. The attribute survives server-side token
        invalidation, so a browser can look logged in while every PLACE returns
        403. We now ALWAYS verify the wallet API returns 200 before declaring
        success. If the wallet probe fails, we force a fresh login."""
        normalized = self._format_sportsape_login_phone(phone)
        if not force:
            try:
                if self._spa_logged_attr(driver) == "1":
                    # logged="1" is necessary but NOT sufficient — verify the
                    # wallet API actually returns 200 before trusting the session.
                    try:
                        if self._session_is_live(driver, deep_check=True):
                            try:
                                driver._sportsape_logged_in = True
                            except Exception:
                                pass
                            return True
                    except Exception:
                        pass
                    # Wallet probe failed — the token is dead even though the
                    # page still renders logged="1". Fall through to force a
                    # fresh login below.
                    self._emit_direct(gui_callback,
                                      f"  ⚠️ {phone}: logged=\"1\" present but wallet API "
                                      "rejected the token — forcing fresh login.")
            except Exception:
                pass
        for _attempt in range(3):
            # RELIABILITY FIX (2026-10-04): re-open the login entry on every
            # attempt. _click_login_entry falls back to a full driver.get() on
            # /login, and that navigation can land on a still-hydrating SPA
            # where #username / #password do not exist yet. The old code opened
            # the entry ONCE and then polled the DOM, so a form that mounted a
            # moment later was never retried and the attempt failed with
            # "Hard login did not reach logged=1" even though the credentials
            # were fine. Re-opening per attempt makes the poll actually able to
            # observe a late-mounting form.
            try:
                self._dismiss_foreign_session_prompt(driver)
            except Exception:
                pass
            try:
                self._click_login_entry(driver)
            except Exception:
                pass
            inputs_found = None
            deadline = time.time() + 20
            while time.time() < deadline:
                try:
                    from selenium.webdriver.common.by import By
                    u = driver.find_element(By.ID, "username")
                    p = driver.find_element(By.ID, "password")
                    if u and p:
                        inputs_found = (u, p)
                        break
                except Exception:
                    pass
                time.sleep(0.4)
                # Re-click the entry mid-wait if the form still has not mounted.
                if time.time() > deadline - 12:
                    try:
                        self._click_login_entry(driver)
                    except Exception:
                        pass
            if not inputs_found:
                continue
            u, p = inputs_found
            # Global login serialisation: never overlap credential POSTs with
            # another account's, and always leave a settle gap after the last
            # one. See _acquire_login_gate for why this is not paranoia.
            try:
                _waited = _acquire_login_gate(phone)
                if _waited > 1:
                    self._emit_direct(
                        gui_callback,
                        f"  ⏳ Waited {_waited:.0f}s to submit credentials "
                        "(another account was authenticating).")
            except Exception:
                pass
            try:
                u.clear()
                u.send_keys(normalized)
                p.clear()
                p.send_keys(password)
                time.sleep(0.5)
                driver.execute_script("document.getElementById('secondary_login').submit();")
                self._emit_direct(gui_callback,
                                  f"  🔐 Submitting real login form for {phone}...")
            except Exception as exc:
                self._emit_direct(gui_callback,
                                  f"  ⚠️ login form fill failed: {str(exc)[:80]}")
                continue
            deadline = time.time() + timeout
            # Poll the cheap signal every second, but probe the authoritative
            # wallet API at most every 8s (each probe can take seconds).
            next_deep = 0.0
            while time.time() < deadline:
                time.sleep(1)
                # Cheap signal first: the SPA normally flips logged="1" promptly.
                try:
                    if self._spa_logged_attr(driver) == "1":
                        # Remember this browser has held a session, so a later
                        # dead-token finding is a real regression (worth a
                        # re-login) rather than a fresh browser's first login.
                        try:
                            driver._sportsape_logged_in = True
                        except Exception:
                            pass
                        self._emit_direct(gui_callback,
                                          f"  ✅ Logged in as {phone} "
                                          "(server session confirmed)")
                        return True
                except Exception:
                    pass
                # AUTHORITATIVE SIGNAL (fix 2026-10-05). The login gate above
                # already knows logged="1" alone is not proof, yet success here
                # was still gated on that one attribute. The SPA frequently
                # HIDES logged="1" while the wallet API is fully live - the app's
                # own log says so: "wallet API live (identity hidden by SPA)".
                # So every failed attempt here used to return False, print
                # "session not confirmed", and trigger ANOTHER re-login, and
                # each re-login supersedes our own token - which is how a single
                # account ends up fighting itself with 'User logged from another
                # device'. Observed 6+ false negatives in one hour, each one
                # minting a fresh token. A live wallet API is real proof, so we
                # accept it.
                if time.time() >= next_deep:
                    next_deep = time.time() + 8
                    try:
                        if self._session_is_live(driver, deep_check=True):
                            try:
                                driver._sportsape_logged_in = True
                            except Exception:
                                pass
                            self._emit_direct(
                                gui_callback,
                                f"  ✅ Logged in as {phone} "
                                "(wallet API live; SPA hides the logged flag)")
                            return True
                    except Exception:
                        pass
        self._emit_direct(gui_callback,
                          "  ⚠️ Hard login did not reach logged=\"1\" — session not confirmed")
        return False

    def _session_is_live(self, driver, deep_check: bool = True) -> bool:
        """True when the current page actually has a valid logged-in session.

        The wallet API is the ONLY trustworthy signal, so it is probed FIRST when
        deep_check is on. Returning early on logged="1" was wrong: that attribute
        survives a server-side invalidation, so the session looked confirmed and
        then every PLACE returned 403 "Forbidden". A cheap logged="1" check now
        only stands in when deep_check is off."""
        if not deep_check:
            try:
                if self._spa_logged_attr(driver) == "1":
                    return True
            except Exception:
                pass
        try:
            auth_ok = self._exec_async_script(
                driver,
                """
                var done = arguments[arguments.length - 1];
                var tid = setTimeout(function(){ done(null); }, 8000);
                fetch('/api/wallets/balance', {credentials: 'include', cache: 'no-store'})
                    .then(function(r){
                        clearTimeout(tid);
                        if (r.status === 200) { done(true); }
                        else { done('http' + r.status); }
                    })
                    .catch(function(){ clearTimeout(tid); done('neterr'); });
                """,
                default=False, timeout=12.0, label="session API probe")
            if auth_ok is True:
                return True
            if isinstance(auth_ok, str) and auth_ok.startswith("http"):
                # The wallet endpoint answered and said NO (401/403). That is a
                # definitive rejection, so do NOT let logged="1" rescue it —
                # that attribute outlives a server-killed token and is exactly
                # what let a dead session look live and then fail every PLACE.
                return False
        except Exception:
            pass
        # Only fall back to the rendered DOM when the probe could not run at all
        # (timeout / network error / endpoint blocked). An unreachable endpoint is
        # not evidence the session died.
        try:
            if self._spa_logged_attr(driver) == "1":
                return True
            body = self._exec_script(
                driver,
                "return ((document.body && document.body.innerText) || '').toLowerCase();",
                default='', timeout=8.0, refresh_on_hang=True, label="session body")
            return any(k in body for k in ("ksh", "kes", "logout", "deposit", "balance"))
        except Exception:
            return False

    def _dismiss_foreign_session_prompt(self, driver) -> bool:
        """Click through SportPesa's 'You have logged in from another device'
        notice so it cannot sit over the listing or swallow the next click."""
        try:
            body = self._exec_script(
                driver,
                "return ((document.body && document.body.innerText) || '').toLowerCase();",
                default='', timeout=6.0, label="foreign-session scan") or ""
        except Exception:
            return False
        needles = ("logged in from another device", "logged from another device",
                   "logged in on another device", "another device")
        if not any(n in body for n in needles):
            return False
        try:
            if self._click_by_text(driver, ["okay", "ok", "continue", "proceed",
                                            "got it", "close", "dismiss", "yes"]):
                time.sleep(0.6)
                return True
        except Exception:
            pass
        return False

    def _confirm_session_ready(self, driver, phone: str, password: str,
                               gui_callback=None) -> bool:
        """PROVE this browser can bet on `phone` before any slip work begins.

        Two checks, both required:
          1. the wallet API returns 200 (the session token is genuinely alive), and
          2. no 'logged in from another device' notice is on screen.
        logged="1" alone is deliberately NOT accepted: it survives server-side
        invalidation, which is what produced 403 Forbidden on PLACE."""
        if self._dismiss_foreign_session_prompt(driver):
            self._emit_direct(gui_callback,
                              "  👆 Dismissed a 'logged in from another device' "
                              "notice — re-checking the session now it is cleared.")
            # DISMISSING IS THE FIX, NOT THE FAILURE (2026-10-06).
            #
            # This used to `return False` the moment a notice was found, so the
            # gate failed the attempt BECAUSE it had successfully dismissed the
            # notice - and never re-checked whether the session was usable. The
            # notice is a stale alert the SPA leaves on screen from an EARLIER
            # session event; the current session is frequently perfectly fine,
            # which is why the wallet API returns 200 in the very same rounds
            # where placement is later refused.
            #
            # The log showed this exactly, three attempts running:
            #   👆 Dismissed a 'logged in from another device' notice.
            #   🔐 PRE-SLIP LOGIN GATE failed (1/3)
            #   ... (2/3) ... (3/3) -> round skipped, no bet
            # Every attempt dismissed the alert and failed anyway, because
            # dismissal was scored as a fault rather than as the cure.
            #
            # So: clear the notice, give the SPA a moment to drop the stale
            # session, then verify properly below. Only a session that is STILL
            # not live after that is a genuine failure.
            time.sleep(0.8)
        try:
            live = self._session_is_live(driver, deep_check=True)
        except Exception:
            live = False
        if not live:
            return False
        try:
            who = self._who_is_logged_in(driver)
        except Exception:
            who = ""
        expected = "".join(ch for ch in str(phone or "") if ch.isdigit())
        if who and expected and who != expected:
            self._emit_direct(gui_callback,
                              f"  ⛔ Session identity mismatch: page shows {who}, "
                              f"expected {expected}.")
            return False
        self._emit_direct(gui_callback,
                          f"  ✅ PRE-SLIP LOGIN GATE passed — wallet API live"
                          + (f", identity {who}" if who else " (identity hidden by SPA)")
                          + ". Proceeding to slip build.")
        return True

    def _who_is_logged_in(self, driver) -> str:
        """Best-effort read of WHICH account the current session belongs to, as
        normalized digits (e.g. "0700000001"). Returns '' when the page does not expose
        the account identity (we then rely on live/logged-out only)."""
        try:
            raw = self._exec_script(driver, r"""
var b = (document.body && document.body.innerText) || '';
var m = b.match(/(?:254)?0?[17][0129][0-9]{7}/g);
return m ? m[0] : '';
""", default='', timeout=8.0, refresh_on_hang=True, label="who-logged-in")
        except Exception:
            return ""
        if not raw:
            return ""
        digits = "".join(ch for ch in str(raw) if ch.isdigit())
        if len(digits) == 12 and digits.startswith("254"):
            digits = "0" + digits[3:]
        if len(digits) == 9 and digits.startswith("7"):
            digits = "0" + digits
        return digits if len(digits) >= 10 else ""

    def _assert_account_session(self, driver, phone: str, password: str,
                                gui_callback=None) -> bool:
        """Ensure the session is (a) actually logged in and (b) belongs to `phone`.
        If the session was lost mid-run, or a stray account session is active, it
        re-logs-in / switches accounts before betting. Returns True when the driver
        is confirmed live on the right account."""
        expected = "".join(ch for ch in str(phone or "") if ch.isdigit())
        # DEAD-DRIVER GUARD (2026-10-05). Re-logging in on a driver whose
        # session has already died ("invalid session id" /
        # HTTPConnectionPool) can NEVER succeed — the browser is a corpse — yet
        # the old code retried twice, burning ~90s of wall-clock and a chunk of
        # CPU per round before the caller's heal path finally replaced it. We
        # now detect the corpse up front, say so plainly, and hand straight back
        # so the worker's next iteration rebuilds the browser properly.
        try:
            if not self._driver_is_usable(driver):
                self._emit_direct(
                    gui_callback,
                    f"\U0001f6ab7 {phone}: browser session is dead — skipping this round "
                    "so the driver can be rebuilt cleanly.")
                return False
        except Exception:
            pass
        for _attempt in range(2):
            live = False
            try:
                live = self._session_is_live(driver)
            except Exception:
                live = False
            who = self._who_is_logged_in(driver)
            if not live:
                self._emit_direct(gui_callback,
                                  f"🔐 Session lost — re-logging in as {phone}")
                try:
                    self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
                except Exception as e:
                    self._emit_direct(gui_callback, f"⚠️ Re-login failed: {str(e)[:80]}")
                    continue
                continue
            if who and expected and who != expected:
                self._emit_direct(gui_callback,
                                  f"⚠️ Account mismatch: page shows {who} but we want "
                                  f"{expected} — switching accounts")
                try:
                    self._logout_current_session(driver)
                except Exception:
                    pass
                try:
                    self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
                except Exception as e:
                    self._emit_direct(gui_callback, f"⚠️ Re-login failed: {str(e)[:80]}")
                    continue
                continue
            # live and (identity matches or identity hidden) -> good
            return bool(live)
        self._emit_direct(gui_callback,
                          "🔐 Could not re-establish the correct account session — skipping this round.")
        return False

    def _place_one_bet(self, driver, phone: str, password: str, stake: float = 10,
                       visible: bool = True, gui_callback=None,
                       target_odds_min: float = 3.0, target_odds_max: float = 6.0,
                       odds_cap: float = 8.0, max_legs: int = 14, min_legs: int = 2,
                       min_lead_minutes: int = 5,
                       stake_percent: float = 0.0, stake_cap: float = 500.0,
                       prefer_more_legs: bool = False, reserve_pool: float = 0.0,
                       jitter_seed: int = 0,
                       conf_floor=None, no_odds_cap=False,
                        researched_only=False, round_risk: bool = True,
                        board_wide: bool = False,
                        cfg=None,
                        combined_floor_override: float = 0.0) -> dict:
        """One complete crawl-and-bot round on an already-built driver.

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
            if not self._assert_account_session(driver, phone, password,
                                                gui_callback=gui_callback):
                return {"status": "error",
                        "message": "Account session could not be re-established"}
            # ── PRE-SLIP LOGIN GATE (owner rule) ───────────────────────────
            # Nothing may be crawled, researched or slipped until the wallet API
            # proves THIS browser owns a live session on THIS account. The SPA's
            # logged="1" attribute stays set after the server kills the token, so
            # it is not proof — the wallet probe is. When the book reports
            # "User logged from another device" we click Okay and re-login in a
            # bounded loop instead of crawling a session that cannot bet.
            # Anchor to the SPA games page FIRST so the probe's relative
            # /api/wallets/balance request actually resolves; probing a stale or
            # error page would time out and degrade to the weak DOM fallback.
            _gate_ok = False
            # BACKOFF RESPECT (2026-10-05): the gate must not start its 3
            # dismiss+logout+login cycles while this account is already in a
            # login cooldown. Doing so re-created the exact thrash the backoff
            # exists to stop — one stuck account still burned 3 fresh login POSTs
            # per round, which is what kept it permanently wedged (0 bets in 52
            # minutes while the other account placed 3). If we are cooling down,
            # decline this round immediately and let the session settle.
            _bo = getattr(self, "_auth_backoff", {}) or {}
            _bo_until = float(_bo.get(str(phone or "")) or 0.0)
            if _bo_until > time.time():
                self._emit_direct(
                    gui_callback,
                    f"⏸️ {phone}: login in cooldown "
                    f"({int((_bo_until - time.time()) / 60) + 1} min left) — skipping this "
                    "round rather than superseding our own session again.")
                return {"status": "skipped", "skipped": True,
                        "message": "login cooldown active — round skipped by design"}
            for _try in range(3):
                # Re-anchor to the games page on EVERY attempt, not just the
                # first. `_logout_current_session` leaves the SPA on a
                # logged-out route, where the relative /api/wallets/balance
                # probe cannot resolve — so probing there degraded to the weak
                # DOM fallback and could never confirm, even after a perfectly
                # good re-login. That is what made the gate burn all 3 attempts
                # and skip the round.
                try:
                    self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                    time.sleep(0.8)
                except Exception:
                    pass
                if self._confirm_session_ready(driver, phone, password,
                                                gui_callback=gui_callback):
                    _gate_ok = True
                    break
                self._emit_direct(
                    gui_callback,
                    f"🔐 PRE-SLIP LOGIN GATE failed ({_try + 1}/3) — dismissing any "
                    f"'logged in elsewhere' prompt and re-logging in.")
                try:
                    self._dismiss_foreign_session_prompt(driver)
                except Exception:
                    pass
                try:
                    self._logout_current_session(driver)
                except Exception:
                    pass
                # Let the old session actually die on the server before we
                # present new credentials. Re-submitting instantly races the
                # teardown and the book answers "another device" again.
                time.sleep(4)
                try:
                    self._hard_spa_login(driver, phone, password,
                                         gui_callback=gui_callback, force=True)
                except Exception:
                    pass
                time.sleep(2)
            if not _gate_ok:
                return {"status": "skipped", "skipped": True,
                        "message": "PRE-SLIP LOGIN GATE: could not confirm a live "
                                   "session on this account after 3 attempts"}
            self._close_stray_tabs(driver)

            # FRESH SLIP EVERY ROUND (owner rule): the betslip panel is persistent
            # across navigation. If the previous round died on a suspended/removed
            # selection, those stale legs sit in the panel, read as a "payable" slip,
            # and block every later PLACE with "Not valid" — the exact account-2 bug.
            # Clear at the start so each round rebuilds from the legs it actually
            # clicks. (Clearing can never place a bet — it is always safe.)
            try:
                if self._read_betslip_count(driver) > 0:
                    self._clear_betslip(driver, gui_callback=gui_callback)
                    self._emit_direct(gui_callback,
                                      "  🧹 Cleared stale persistent betslip before this round.")
            except Exception:
                pass

            balance, balance_confirmed = self._read_balance_confirmed(
                driver, wait=20.0, phone=phone, password=password)
            if balance_confirmed:
                self._balance_cache = getattr(self, "_balance_cache", None) or self._load_balance_cache()
                self._balance_cache[str(phone)] = {"balance": balance, "confirmed": True,
                                                   "ts": time.time()}
                self._save_balance_cache()
            if not balance_confirmed:
                ent = self._cached_balance_for(phone, allow_stale=True)
                if ent and ent.get("confirmed"):
                    balance = float(ent.get("balance") or 0)
                    balance_confirmed = True
                    cache_age_s = int(time.time() - float(ent.get("ts") or 0))
                    self._emit_direct(
                        gui_callback,
                        f"ℹ️ Balance re-read lagged; using cached KES {balance:,.2f} "
                        f"({cache_age_s}s old) for {phone}.")
            if not balance_confirmed:
                self._emit_direct(gui_callback,
                                  "ℹ️ Balance not readable from page — estimating from "
                                  "launch sweep / last known balance minus active stakes.")
                # Estimate (owner's model): launch-sweep balance minus every stake
                # placed since → presumed remaining. Never blocks a bet or deposit.
                est, src = self._est_balance_for(phone)
                if src != "none":
                    balance = max(0.0, est)
                    balance_confirmed = True
                    self._emit_direct(gui_callback,
                                      f"ℹ️ Estimated balance for {phone}: KES {balance:,.2f}")
                else:
                    # OWNER RULE (2026-09-28): no readable balance means the
                    # account is PARKED for this round — never bet it. Parking is
                    # a skip, not a shutdown: the next account in the list still
                    # gets its turn, so one unreadable number cannot stall the
                    # whole fleet.
                    # Park it the same way the rest of the engine does: a
                    # _parked_until entry the scheduler already understands, plus
                    # the supervisor beat so Fleet State shows it resting.
                    try:
                        if not hasattr(self, "_parked_until"):
                            self._parked_until = {}
                        self._parked_until[str(phone)] = time.time() + 1800.0
                    except Exception:
                        pass
                    if self._agent_hub is not None:
                        try:
                            self._agent_hub.supervisor.beat_parked(phone)
                        except Exception:
                            pass
                    self._emit_direct(gui_callback,
                                      f"🅿️ PARKED {phone} — no balance on record. "
                                      f"Skipping to the next account.")
                    # "skipped", not "aborted": an unreadable balance is a benign
                    # decline, not a broken session. Reporting it as aborted made
                    # the supervisor rebuild drivers for a parked account, which
                    # was itself causing the renderer hangs.
                    return {"status": "skipped", "skipped": True,
                            "message": "Parked — balance unreadable",
                            "balance_unreadable": True, "parked": True}
            self._emit_direct(gui_callback, f"Starting balance: KES {balance:,.2f}")
            if self._agent_hub is not None:
                try:
                    self._agent_hub.supervisor.beat_balance_read(phone)
                except Exception:
                    pass

            # ── PORTFOLIO GATE (2026-09-26): drawdown circuit breakers ─────
            # Checked before any stake is sized or any slip is built. The
            # portfolio-level halt is evaluated FIRST, because it catches the
            # failure per-account checks structurally cannot see: every account
            # bleeding at once. Per-account, an account down 40% from its own
            # peak is frozen and must be reviewed by the owner.
            _fleet = dict(getattr(self, "_engine_state", {}).get("balances") or {})
            # Only a positive, readable figure may enter the fleet equity picture.
            # A 0.0 here means "we could not read this account" — feeding it in
            # records an equity of just the open stake, which reads as a ~50%
            # drawdown and latches a portfolio halt against a healthy account.
            try:
                _own = float(balance)
            except (TypeError, ValueError):
                _own = 0.0
            if _own > 0.0:
                _fleet[phone] = _own
            else:
                self._emit_direct(
                    gui_callback,
                    f"ℹ️ Not folding a zero/unreadable balance for {phone} into the "
                    f"fleet equity — the breakers treat it as unknown until a real "
                    f"reading arrives.")
            # NOTE: the whole fleet is passed, never just {phone: balance}. Peaks
            # and drawdown are both fleet-level quantities, so feeding one account
            # makes the others look like they vanished and manufactures a fake
            # portfolio crash that halts every account for no reason.
            self._note_balances(_fleet)
            _allowed, _why = self._circuit_breaker_check(phone, balance, _fleet)
            if not _allowed:
                # A refusal with no reason is unactionable: the operator sees
                # "no bet this round ()" and cannot tell a real freeze from a
                # bookkeeping artifact. Name the live state that caused it.
                if not str(_why).strip():
                    _pf = self._load_portfolio()
                    _why = ("portfolio breaker refused this round "
                            f"(halted={bool(_pf.get('halted'))}, "
                            f"frozen={bool((_pf.get('frozen') or {}).get(phone))}, "
                            f"halt_reason={_pf.get('halt_reason') or 'none'}, "
                            f"equity={self._equity_for(phone, balance):.2f}, "
                            f"peak={_pf.get('peaks', {}).get(phone)})")
                self._count_refusal(_why.split(":")[0][:40])
                self._emit_direct(gui_callback, f"🛑 {phone}: {_why} — no bet this round.")
                # Inside the guard on purpose. When the breaker ALLOWS, _why is
                # '' — returning here unconditionally made every healthy round
                # report a skip with an empty reason and circuit_breaker=True,
                # and no bet was ever placed.
                return {"status": "skipped", "skipped": True, "message": _why,
                        "circuit_breaker": True}

            # Stake is fixed — always use exactly the base stake passed in.
            # Risk manager and compounding are disabled: the owner wants KES 10
            # minimum always, no automatic increases.
            stake = max(self.MIN_STAKE, float(stake))
            # DRAWDOWN RECOVERY MODE (2026-10-05). The breaker ALLOWED this
            # round, but only because the account is frozen-but-recovering: it
            # has to be able to win its way back over the threshold, so the
            # stake is cut rather than the account being allowed full size.
            # Without this the freeze is a deadlock (see the latch-recovery
            # comment in _circuit_breaker_check).
            try:
                if (getattr(self, "_recovery_mode", None) or {}).get(str(phone)):
                    stake = max(self.MIN_STAKE,
                                round(stake * self.DRAWDOWN_RECOVERY_STAKE_PCT, 2))
                    self._emit_direct(
                        gui_callback,
                        f"💠 {phone}: DRAWDOWN RECOVERY MODE — stake reduced to "
                        f"KES {stake:,.2f} until the balance climbs back above "
                        f"the -{self.ACCOUNT_DRAWDOWN_FREEZE:.0%} drawdown limit.")
            except Exception:
                pass

            # Effective pool: waived automatically when balance is low so the
            # savings reserve never blocks a legitimate KES 10 bet.
            effective_reserve = self._effective_pool(float(balance), float(stake))

            if float(balance) - effective_reserve < float(stake):
                # If total balance (ignoring reserve) covers the stake, just bet.
                if float(balance) >= float(stake):
                    if effective_reserve > 0:
                        self._emit_direct(gui_callback,
                                          f"💡 Balance KES {balance:,.2f} — pool "
                                          f"KES {effective_reserve:,.2f} waived (balance too low "
                                          "to reserve savings right now).")
                    # Proceed
                else:
                    # Cross-check: if the startup sweep confirmed this account has
                    # plenty, a sudden 'low' here is a misread — force one more read.
                    start_b = self._start_balances.get(phone) if isinstance(
                        getattr(self, "_start_balances", None), dict) else None
                    if start_b and start_b.get("confirmed") \
                            and float(start_b.get("balance") or 0) >= float(stake) * 2:
                        try:
                            recheck, recheck_ok = self._read_balance_confirmed(driver, wait=10.0)
                            if recheck_ok and recheck > balance:
                                balance = recheck
                        except Exception:
                            pass
                    # SMART STOP (owner rule): once we KNOW the balance is below the
                    # base stake, STOP attempting real bets — no "bet the full tiny
                    # balance to grow it". Parking via the no-funds rest path so we
                    # follow winnings but place nothing until funds return.
                    if float(balance) < float(stake):
                        available = max(0.0, float(balance))
                        deposit_needed = max(0.0, round(float(stake) - available, 2))
                        # Rate-limit the deposit nag — say it once, then go quiet
                        # for 10 rounds. Keep doing shadow bets in the meantime.
                        _dep_key = f"_deposit_nag_count_{phone}"
                        _nag_count = int(getattr(self, _dep_key, 0)) + 1
                        setattr(self, _dep_key, _nag_count)
                        if _nag_count == 1 or (_nag_count % 10) == 0:
                            self._emit_direct(gui_callback,
                                              f"💰 FUNDS LOW on {phone}: "
                                              f"KES {balance:,.2f} available, "
                                              f"need KES {deposit_needed:,.2f}. "
                                              "Continuing shadow picks and learning while waiting.")
                            if self._agent_hub is not None:
                                try:
                                    self._agent_hub.alert(
                                        "deposit",
                                        f"FUNDS LOW on {phone}: "
                                        f"balance KES {balance:,.2f}; "
                                        f"need KES {deposit_needed:,.2f}.",
                                        gui_callback=gui_callback)
                                except Exception:
                                    pass
                        # Inside `if balance < stake`. Returning here made every
                        # round claim "Insufficient balance" regardless of funds.
                        return {"status": "skipped", "skipped": True,
                                "message": "Insufficient balance",
                                "deposit_needed": deposit_needed,
                                "balance": balance,
                                "stake": float(stake)}
            # Reached only when balance >= stake: stake stays the base value passed
            # in — never reduced by the reserve, never raised to grow a tiny pot.
            stake = max(self.MIN_STAKE, float(stake))

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
                # Today-games tab is empty — try the football-1 home listing which
                # carries upcoming fixtures beyond just today's schedule.
                self._emit_direct(gui_callback,
                                  "⚠️ No game rows on today-games page — trying football-1 home listing...")
                try:
                    self._safe_get(driver, self.FOOTBALL_HOME_URL)
                    time.sleep(2.0)
                    self._scroll_to_load_more_games(driver, gui_callback=gui_callback)
                    games = self._extract_dom_games(driver)
                except Exception:
                    pass
            if not games:
                # Transient crawl failure (DOM not ready / renderer hiccup) — reuse
                # last good board for 15 min so "fix there many games" doesn't stall.
                _cached = getattr(self, "_last_crawled_games", None) or []
                _cached_ts = float(getattr(self, "_last_crawled_games_ts", 0) or 0)
                if _cached and (time.time() - _cached_ts) < 900:
                    games = list(_cached)
                    self._emit_direct(gui_callback,
                                      f"♻️ Reusing cached board: {len(games)} games (crawl transient)")
                else:
                    self._emit_direct(gui_callback, "⚠️ No game rows found on either listing page")
                    return {"status": "error", "message": "No games listed"}
            try:
                self._last_crawled_games = games
                self._last_crawled_games_ts = time.time()
            except Exception:
                pass
            self._record_odds_ticks(games)

            # Owner rule (2026-09): fetch MORE than whatever the today tab offers.
            # Dedup means each of the shared 14-15 games is bet once across all
            # numbers, so a bigger board every round guarantees the accumulator is
            # always buildable. When today's tab is thin, merge the dedicated
            # football-home + upcoming 24-48 h listings (deduped by game id).
            if len([g for g in games if g.get("start")]) < 20:
                _known = {str(g.get("id")) for g in games}
                for _url in (self.POPULAR_GAMES_URL, self.FOOTBALL_HOME_URL,
                         self.UPCOMING_GAMES_PAGE_URL):
                    try:
                        self._safe_get(driver, _url)
                        time.sleep(1.2)
                        self._scroll_to_load_more_games(driver, max_scrolls=3,
                                                        gui_callback=gui_callback)
                        _batch = self._extract_dom_games(driver) or []
                        _fresh = [g for g in _batch
                                  if str(g.get("id")) and str(g.get("id")) not in _known]
                        if _fresh:
                            games += _fresh
                            _known |= {str(g.get("id")) for g in _fresh}
                            # These rows live on the merged listing, NOT the today tab.
                            # Remember their source URL so the leg-click flow can open
                            # the right listing when looking the row up by id.
                            for _g in _fresh:
                                self._gid_src[str(_g.get("id"))] = _url
                            _src = (_url.split("/")[-2] or "listing").replace("-", " ")
                            self._emit_direct(gui_callback,
                                              f"📈 Extended board: +{len(_fresh)} games from {_src}")
                    except Exception as _e:
                        self._emit_direct(gui_callback,
                                          f"  ↖ Extra-board scrape skip: {str(_e)[:80]}")
                # Back on the today listing so the leg-click flow behaves as usual.
                try:
                    self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                    time.sleep(1.0)
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

            # One-line game summary instead of a full listing (keeps the terminal quiet);
            # only the run's selected legs get logged at bet time.
            # Owner rule (2026-09-22): placeable = today+tomorrow only (far-future
            # lines from the extended board get suspended before kick-off).
            playable = [g for g in games
                        if g.get("mins_to_start") is not None
                        and g["mins_to_start"] >= min_lead_minutes
                        and self._is_recent_enough(g)]
            far_future = sum(1 for g in games
                             if g.get("mins_to_start") is not None
                             and g["mins_to_start"] >= min_lead_minutes
                             and not self._is_recent_enough(g))
            started = sum(1 for g in games if (g.get("mins_to_start") or 0) < 0)
            closing = sum(1 for g in games
                          if (g.get("mins_to_start") or 0) >= 0 and g["mins_to_start"] < min_lead_minutes)
            self._emit_direct(gui_callback,
                              f"📅 {len(games)} games on tab (⏳ {len(playable)} placeable, "
                              f"🔜 {closing} too close, 🏁 {started} already underway, "
                              f"📆 {far_future} beyond tomorrow)")
            if not playable:
                # No placeable games on today's tab — try the upcoming-games page
                # which lists fixtures from the next 24–48 h.
                self._emit_direct(gui_callback,
                                  f"⚠️ No placeable games on today's tab (need >= {min_lead_minutes}m) "
                                  "— checking upcoming-games listing...")
                try:
                    self._safe_get(driver, self.UPCOMING_GAMES_PAGE_URL)
                    time.sleep(2.0)
                    self._scroll_to_load_more_games(driver, gui_callback=gui_callback)
                    upcoming = self._extract_dom_games(driver) or []
                    now2 = datetime.now()
                    for g in upcoming:
                        if g.get("start"):
                            g["mins_to_start"] = round((g["start"] - now2).total_seconds() / 60.0)
                        else:
                            g["mins_to_start"] = None
                    more_playable = [g for g in upcoming
                                     if g.get("mins_to_start") is not None
                                     and g["mins_to_start"] >= min_lead_minutes
                                     and self._is_recent_enough(g)]
                    if more_playable:
                        self._emit_direct(gui_callback,
                                          f"✅ Found {len(more_playable)} placeable upcoming games — continuing")
                        for _g in upcoming:
                            self._gid_src[str(_g.get("id"))] = self.UPCOMING_GAMES_PAGE_URL
                        games = games + [g for g in upcoming
                                         if str(g.get("id")) not in {str(x.get("id")) for x in games}]
                        playable = more_playable
                        self._record_odds_ticks(upcoming)
                        lead_by_gid = {str(g.get("id")): g.get("mins_to_start") for g in playable}
                    else:
                        self._emit_direct(gui_callback,
                                          "⚠️ No upcoming games placeable either — re-crawling shortly.")
                        return {"status": "skipped", "skipped": True,
                    "message": "No placeable games right now"}
                except Exception as _e:
                    self._emit_direct(gui_callback,
                                      f"⚠️ Upcoming-games fallback failed: {str(_e)[:80]}")
                    return {"status": "skipped", "skipped": True,
                    "message": "No placeable games right now"}
            if not playable:
                self._emit_direct(gui_callback,
                                  f"⚠️ No games currently placeable (need >= {min_lead_minutes}m "
                                  "to kick-off). Re-crawling shortly.")
                return {"status": "skipped", "skipped": True,
                    "message": "No placeable games right now"}
            # ── Per-account hard split: each worker gets its OWN preferred slice
            # of the board. Even when the slice is thin and the round falls back
            # to the full board, the global used_set below blocks the whole game
            # (owner rule 2026-09: no match repeats today across ANY number) — so
            # the first account to place a game owns it and the others pick fresh
            # ones, while still being free to exploit MANY markets per game.
            # Keep the pre-slice full board so a slice that fails to build a
            # combo can widen to the whole board (owner rule: "make sure ALL the
            # accounts get games") — the fix for account-2 starvation, where one
            # account's gid-parity slice held only suspended fixtures and every
            # round died with "No accumulator combination found".
            _full_playable = list(playable)
            if not board_wide:
                try:
                    with self._used_lock:
                        buk = self._account_buckets
                        if str(phone or "") not in buk:
                            buk[str(phone or "")] = len(buk)
                    _bkt = buk[str(phone or "")]
                    _nacc = max(2, len(buk))
                    _bucket = [g for g in playable
                               if (int(str(g.get("id") or "0")) % _nacc) == _bkt]
                    # ── ADAPTIVE SLICE (owner rule: "so many games — no blocker,
                    #    make sure ALL the accounts get games, never the
                    #    'Not enough qualifying games' message") ──
                    # The account only sticks to its disjoint slice when that slice
                    # alone is rich enough to build the accumulator. A thin slice
                    # (narrower than what's needed for the full slip) falls back
                    # to the FULL board for this round, so a rich results board
                    # ALWAYS yields a bet on every account instead of starving one
                    # account while the board sits open.
                    _need_at_least = max(int(max_legs) * 2, 6)
                    if _bucket and len(_bucket) >= _need_at_least:
                        self._emit_direct(
                            gui_callback,
                            f"🔀 {phone}: preferred own slice of the board "
                            f"({len(_bucket)}/{len(playable)} games — "
                            "accounts prefer not to share a match)")
                        playable = _bucket  # first draft off own slice
                    # Shared-board allowance: when the account's own slice is thin
                    # the account drafts off the FULL board — but NEVER onto a game
                    # that another account already owns. Every game has a SINGLE
                    # owner (first-seen claim). A sibling may not touch it even on
                    # a different market, so one bad game can never bleed two slips:
                    # each account ends up on its OWN disjoint ~15-game pool.
                    try:
                        _own = getattr(self, "_game_owners", None) or {}
                        _pg = str(phone or "")
                        for _g in list(playable or []):
                            _own.setdefault(str(_g.get("id") or ""), _pg)
                        _blocked = {_gid for _gid, _o in _own.items() if _o != _pg}
                        if _blocked:
                            playable = [g for g in playable
                                        if str(g.get("id") or "") not in _blocked]
                    except Exception:
                        pass
                except Exception:
                    pass
            lead_by_gid = {str(g.get("id")): g.get("mins_to_start") for g in playable}

            # Due-diligence pre-flight: open + READ the stats overlay for the top
            # candidate games BEFORE picking, caching form/injuries/weather. The
            # selector then weighs real research, so games with no genuine chance
            # (bad form, key injuries) are pushed down instead of being bet blind.
            try:
                # Study EVERY viable candidate (not just top-N) before selection,
                # bounded by a hard time budget so the round never stalls.
                self._preflight_diligence(driver, playable, gui_callback=gui_callback,
                                          budget=len(playable) or 40, timeout=75.0)
            except Exception as e:
                self._emit_direct(gui_callback,
                                  f"🔎 Pre-flight skip: {str(e)[:80]}")

            # Intelligent leg selection for the accumulator — never repeat a GAME
            # that already appeared in an earlier betslip (persisted across restarts),
            # so the same match is never wagered twice in different slips.
            self._load_usage()
            self._prune_usage()
            # Build used_set with BOTH "gid" (legacy) and "gid|market" keys.
            # The selector blocks: same game+same market (gid|mk in used_set)
            # but allows: same game+different market (only gid|other_mk blocked).
            used_games = set()
            for gid_key, mks in (self._used_games or {}).items():
                # Block the WHOLE game (owner rule: the same match must never be
                # wagered twice today across ANY of the numbers — the 14-15 shared
                # games each get bet at most once, market choice cannot repeat it).
                used_games.add(str(gid_key))
                for mk_val in (mks or {}):
                    used_games.add(f"{gid_key}|{mk_val}")   # finer legacy net

            # CORRELATION-AWARE DRAFTING (2026-09-30): games sitting on a sibling
            # account's ACTIVE slip can't be drafted by this account either — the
            # hard _correlation_verdict would refuse the whole slip at submit time.
            # Bet-flow imports happen at startup, so `_game_owners` (set during
            # THIS session's slice logic) and `_used_games` are often cold and the
            # full-board fallback keeps picking a sibling's match, sees
            # "correlation: game X is already held" and dies for the round. Feed
            # the live exposure map in as used-games so a draft can never even try.
            try:
                _exp_held = self._active_exposure().get("games") or {}
                _phx = str(phone or "")
                for _gid, _owner_set in _exp_held.items():
                    if _owner_set - {_phx}:
                        used_games.add(str(_gid))
            except Exception:
                pass

            # Double-chance pre-flight: read real DC (1X/X2/12) odds off the
            # full-market page of near-kickoff games so DC legs are selectable
            # even when the opportunity scout has not visited them.
            try:
                self._scrape_dc_odds(driver, playable, gui_callback=gui_callback)
            except Exception as e:
                self._emit_direct(gui_callback,
                                  f"↖ DC scrape skip: {str(e)[:80]}")

            # Full-market expansion: disabled in the BET path (2026-09-22 owner
            # rule) — the odds we price slips with live on the hydrated LISTING
            # rows, and the slip is now clicked straight off those rows. Opening
            # every imminent game's /markets page (which renders 0 boxes) just
            # stalls the accumulator behind minute-long dead navigations.
            # Kept OFF here; the idle pre-window research thread may still run it.
            try:
                self._scrape_full_markets_all(driver, playable[:2], gui_callback=gui_callback)
            except Exception as e:
                self._emit_direct(gui_callback,
                                  f"🧮 Full-market expansion skip: {str(e)[:80]}")

            legs, product = self._select_football_legs(
                playable,
                target_min=target_min, target_max=target_max,
                odds_cap=odds_cap, max_legs=max_legs,
                used=used_games,
                prefer_more_legs=prefer_more_legs,
                seed=jitter_seed,
                conf_floor=conf_floor, no_odds_cap=no_odds_cap,
                researched_only=researched_only,
                gui_callback=gui_callback)
            if not legs:
                # No combo fit the target odds window — one modest widening that
                # STILL KEEPS the confidence floor (never re-run with floor 0):
                # we'd rather skip a round than bet legs the model rates poor.
                self._emit_direct(gui_callback,
                                  f"⚠️ No combo in target x{target_odds_min:.0f}-x{target_odds_max:.0f} "
                                  f"— widening window slightly and retrying (floor kept)...")
                legs, product = self._select_football_legs(
                    playable,
                    target_min=max(self.MIN_COMBINED_ODDS, target_min * 0.85),
                    target_max=min(target_max * 2.0, 30.0),
                    odds_cap=odds_cap, max_legs=max_legs, min_legs=min_legs,
                    used=used_games,
                    prefer_more_legs=prefer_more_legs,
                    seed=jitter_seed,
                    conf_floor=conf_floor, no_odds_cap=no_odds_cap,
                    researched_only=researched_only,
                    gui_callback=gui_callback)
            if not legs and _full_playable and len(_full_playable) > len(playable):
                # ACCOUNT-STARVATION FIX (2026-09-30): the account's own gid-parity
                # slice came back empty (e.g. its fixtures were all suspended, or
                # the suspend-bench cleared them after repeated "Not valid" reject-
                # ions). Draft instead from the FULL board — the global used_set
                # still blocks games wagered on any number today, and _game_owners
                # stops a sibling re-using the same match — so a thin account gets
                # a real chance instead of sitting out round after round while the
                # board sits open. This is exactly what the adaptive-slice comment
                # above promised but never delivered: it checked raw game count,
                # not qualifying legs, so it never fired when it mattered.
                # Re-apply the owner block at use-time so a sibling's freshly-claimed
                # match can never slip into this account's fallback draft.
                try:
                    _own2 = getattr(self, "_game_owners", None) or {}
                    _pg2 = str(phone or "")
                    _blocked2 = {_gid for _gid, _o in _own2.items() if _o != _pg2}
                    if _blocked2:
                        _full_playable = [g for g in _full_playable
                                          if str(g.get("id") or "") not in _blocked2]
                except Exception:
                    pass
                self._emit_direct(gui_callback,
                                  f"🔀 {phone}: own slice had no qualifying combo "
                                  f"— drafting from the full board ({len(_full_playable)} games)...")
                legs, product = self._select_football_legs(
                    _full_playable,
                    target_min=target_min, target_max=target_max,
                    odds_cap=odds_cap, max_legs=max_legs, min_legs=min_legs,
                    used=used_games,
                    prefer_more_legs=prefer_more_legs,
                    seed=jitter_seed,
                    conf_floor=conf_floor, no_odds_cap=no_odds_cap,
                    researched_only=researched_only,
                    gui_callback=gui_callback)
                if legs:
                    self._emit_direct(gui_callback,
                                      f"✅ {phone}: full-board draft yielded "
                                      f"{len(legs)} leg(s) @ x{round(product, 2)}")
            if not legs:
                self._emit_direct(gui_callback,
                                  "⚠️ Not enough qualifying games this round — re-crawling shortly.")
                # "skipped", NOT "aborted" (2026-09-27). A thin board where no
                # qualifying combination clears the odds floor is a HEALTHY
                # outcome: the engine crawled fine and correctly declined to bet.
                # Reporting it as "aborted" made the supervisor count ordinary
                # quiet rounds as a broken session, so it rebuilt drivers on a
                # timer (18+/hour) and manufactured the selenium instability it
                # was warning about. Nothing failed here; there was simply
                # nothing worth betting on.
                return {"status": "skipped", "skipped": True,
                        "message": "No accumulator combination found"}

            # ── Always-learn shadow pick (owner rule: the tool improves every
            # round it runs). Record a runner-up slip from the games NOT used in
            # this round's real pick, so the learning engine scores a fresh data
            # point even when a bet fires normally. Never touches money.
            try:
                chosen_ids = {str(l[2]) for l in legs}
                _leftover = [g for g in playable if str(g.get("id")) not in chosen_ids]
                if _leftover:
                    _shadow_legs, _sp = self._select_football_legs(
                        _leftover, target_min=target_min, target_max=target_max,
                        odds_cap=odds_cap, max_legs=max_legs, used=used_games,
                        prefer_more_legs=prefer_more_legs, seed=(jitter_seed + 7),
                        conf_floor=conf_floor, no_odds_cap=no_odds_cap,
                        researched_only=researched_only, gui_callback=gui_callback)
                    if _shadow_legs:
                        self._record_shadow_pick(_shadow_legs, phone,
                                                 playable=_leftover,
                                                 gui_callback=gui_callback)
            except Exception:
                pass

            joint_prob = 1.0
            for o, name, gid, market, prob in legs:
                joint_prob *= prob
            # ── OWNER RULE (2026-09-26): single-market concentration cap ──
            # The real-money ledger's biggest loser was the "small odds = safe"
            # cluster: 2L@lt3 (217 bets, -12.4%) and 3L@lt3 (214 bets, -55.6%) —
            # 431 of the ~1,465 settled, all sub-3.0 combined odds, all the same
            # low-odds family. That is precisely the trap the owner called out:
            # combining several tiny-odds legs feels safe but multiplies the
            # bookmaker's margin, not our edge, so the slip dies slowly and often.
            # Two limits now apply before a slip is allowed to be priced:
            #   * no market may hold more than MAX_MARKET_LEGS_PER_SLIP slots
            #     (stops one market being bet 3-4x — the correlated-bet trap), and
            #   * a slip whose combined odds sit BELOW MIN_SKEW_ODDS is refused,
            #     because that is the losing low-odds family itself.
            _mk_counts: dict = {}
            for _o, _n, _g, _m, _p in legs:
                _mk_counts[_m] = _mk_counts.get(_m, 0) + 1
            _over_cap = [m for m, n in _mk_counts.items() if n > self.MAX_MARKET_LEGS_PER_SLIP]
            _skew_bad = product < self.MIN_SKEW_ODDS
            if _over_cap:
                self._emit_direct(gui_callback,
                                  f"⛔ slip rejected: {', '.join(_over_cap)} held more than "
                                  f"{self.MAX_MARKET_LEGS_PER_SLIP} legs (concentration cap)")
            if _skew_bad:
                self._emit_direct(gui_callback,
                                  f"⛔ slip rejected: combined x{product:.2f} is below the "
                                  f"x{self.MIN_SKEW_ODDS:.2f} skew floor — this low-odds family "
                                  "is the historical loser (431 bets, -43% ROI), not a safe bet")
            if _over_cap or _skew_bad:
                # Refuse the slip cleanly (same contract as every other
                # no-combo bail-out in this function) so the caller re-selects
                # on the next round instead of pricing a slip we just rejected.
                # "skipped" = healthy decline, not a session failure (2026-09-27).
                return {"status": "skipped", "skipped": True,
                        "message": (f"Slip refused ({'; '.join(_over_cap) if _over_cap else ''}"
                                    f"{' concentration' if _over_cap else ''}"
                                    f"{' + ' if _over_cap and _skew_bad else ''}"
                                    f"{'sub-x%.2f skew' % product if _skew_bad else ''}"
                                    ).strip()}
            self._emit_direct(gui_callback,
                              f"🎯 Selected {len(legs)} legs → combined x{product:.2f} "
                              f"| ~{joint_prob * 100:.1f}% weighted win chance:")
            leg_by_gid = {str(g.get("id")): g for g in playable}
            soonest_ko = None
            for o, name, gid, market, prob in legs:
                _g = leg_by_gid.get(str(gid))
                kf = _g.get("ko_label") if _g else ""
                _start = _g.get("start") if _g else None
                # DATE-AWARE KICKOFF (2026-10-05). ko_label carries only HH:MM,
                # so a match at 21:00 TOMORROW printed exactly like one at 21:00
                # today - which reads as "already under way" and sent this whole
                # investigation down the wrong path. The leg was correctly
                # playable; only the log lied. Show the weekday+day whenever the
                # kick-off is not today.
                if _start is not None:
                    try:
                        if _start.date() != datetime.now().date():
                            kf = f"{_start.strftime('%a %d %b')} {_start.strftime('%H:%M')}"
                    except Exception:
                        pass
                k_end = self._ko_end_hhmm(_start)
                drift = self._drift_k(gid, market, o)
                d_mark = f" | drift {'▲' if drift > 1.005 else ('▼' if drift < 0.995 else '＝')}x{drift:.2f}"
                k_mark = (f" | ⏰ k.o. {kf} → ends ~{k_end}"
                          if (kf and k_end) else (f" | k.o. {kf}" if kf else ""))
                self._emit_direct(gui_callback,
                                  f"   • {name} [{market}] @{o:.2f} (~{prob * 100:.0f}%){k_mark}{d_mark}")
                if _start:
                    _mins = (_start - datetime.now()).total_seconds() / 60.0
                    if soonest_ko is None or _mins < soonest_ko:
                        soonest_ko = _mins
            if soonest_ko is not None:
                if soonest_ko < 0:
                    self._emit_direct(gui_callback,
                                      f"⏱ First leg kicks off in-play (+{-soonest_ko:.0f}m) — momentum bet")
                else:
                    self._emit_direct(gui_callback,
                                      f"⏱ First chosen leg kicks off in {soonest_ko:.0f}m — "
                                      "no artificial minimum, betting it")

            # ── Owner rule (2026-09-23): binary confidence stake — 20 / 10 ──
            # A "too good" slip is one the MACHINE is genuinely confident about,
            # NOT one whose odds happen to be small. OWNER LEARNING (2026-09-25):
            # the old rule doubled the stake when every leg was low-odds (<=1.35),
            # which assumed small odds = sure win. The 09-24 ledger refutes that:
            # over 415 trials "over" landed 74.8% vs the 82.6% it was priced at, and
            # the x1.2-1.35 "bankers" kept losing (over15 was retired outright). So
            # the double-stake now rests SOLELY on the market-weight-corrected joint
            # probability clearing a real floor. If nothing is that confident we
            # stake KES 10, never more.
            _n_legs = len(legs)
            _max_odds = max(float(o) for o, _n, _g, _m, _p in legs) if legs else 1.0
            high_conf = joint_prob >= 0.62  # weighted joint win chance (markets already penalized)

            # ── PORTFOLIO GATE: cross-account correlation (2026-09-26) ────
            # With one account this is a no-op. With a fleet it is the whole
            # point: two accounts on one match (or three on one market) is ONE
            # position with the bookmaker's margin counted two or three times,
            # which looks diversified in the UI and is not diversified at all.
            # NOTE: the correlation and recipe-veto checks are deliberately NOT
            # run here. Further down, a failed leg click triggers a rebuild that
            # REBINDS used_legs to a different, narrower slip. Gates evaluated
            # against the pre-rebuild `legs` would clear one slip while the
            # bookmaker takes another, so they run after the rebuild instead.

            # ── Stake: variance-scaled FRACTIONAL KELLY (2026-09-26) ─────
            # Replaces the flat "20 if confident / 10 otherwise" rule. Kelly is
            # the only sizing rule that respects the price you were actually
            # offered, and it is scaled by (a) KELLY_FRACTION, because the
            # model's own calibration error is material and full Kelly turns
            # mispriced probability straight into ruin, and (b) the account's
            # realised volatility, so a high-variance account automatically
            # bets smaller on the same signal. Hard-capped as a share of both
            # the account balance and the whole portfolio.
            _fleet_total = 0.0
            for _b in (getattr(self, "_engine_state", {}).get("balances") or {}).values():
                try:
                    _fleet_total += float(_b or 0.0)
                except (TypeError, ValueError):
                    pass
            _fleet_total += float(balance or 0.0)
            sized = self._kelly_stake(phone, balance, joint_prob, product, _fleet_total)
            if sized <= 0:
                # OWNER decision (2026-09-29, FIRST-BET TEST): a joint prob that
                # doesn't clear the positive-edge line at 1/5 Kelly USED TO SKIP
                # the slip entirely ("no positive edge") — which froze the machine
                # on every healthy-looking board (asteady 2-3 leg slips ~x2.5-3.0
                # with ~33-37% pooled prob = ~0.92-0.94 EV, just under the line).
                # While the FIRST-BET TEST is on, Kelly only floors: no-edge ->
                # MIN stake instead of $0, so the tool actually bets. The
                # downstream gates (bankroll share, SLIP_MIN_EV, MIN_STAKE) still
                # bind hard, so a no-edge slip is ALWAYS capped to the minimum.
                # REVISIT once the first real bet has landed and we re-tighten.
                self._emit_direct(
                    gui_callback,
                    f"🎲 Kelly: joint {joint_prob*100:.1f}% @ x{product:.2f} has no "
                    f"positive edge at 1/5 Kelly — TEST MODE floors it to MIN stake.")
                sized = self.MIN_STAKE
            self._emit_direct(gui_callback,
                              f"📐 Kelly stake: KES {sized:,.2f} (joint {joint_prob*100:.1f}% "
                              f"@ x{product:.2f}, 1/{int(round(1/self.KELLY_FRACTION))} Kelly, "
                              f"vol-scaled)")

            # ── OWNER GATE 1 (2026-09-25): slip-level EV, not per-leg odds ──
            # "Too good" was being read as small per-leg odds. The ledger says
            # that's exactly backwards (the x1.2-1.35 'bankers' kept losing).
            # A slip is only worth a FULL stake when the WEIGHTED joint prob
            # times the COMBINED odds clears the positive-EV floor. Below it,
            # whatever the legs look like, the slip is negative-EV once the
            # book's margin is stripped → downgrade to MIN stake (never $0).
            _slip_ev = joint_prob * float(product) if product else 0.0
            if _slip_ev < self.SLIP_MIN_EV:
                sized = min(sized, self.MIN_STAKE)
                self._emit_direct(gui_callback,
                                  f"⛔ slip EV {_slip_ev:.2f} < {self.SLIP_MIN_EV:.2f} — "
                                  f"MIN stake only (owner rule)")

            # ── OWNER GATE 2 (2026-09-25): never torch the bankroll ──
            # Even a genuine high-confidence slip never risks more than the
            # bankroll share, and never bets its final KES (only what it can
            # afford to lose and keep going). A fresh KES 6.47 or 29.29
            # bankroll must survive to compound, not die on one slip.
            sized = min(sized, max(self.MIN_STAKE, float(balance) * self.STAKE_BANKROLL_SHARE))
            sized = min(sized, max(self.MIN_STAKE, float(balance) * 0.95))

            if stake_cap and stake_cap > 0:
                sized = min(sized, float(stake_cap))
            sized = min(sized, max(1.0, float(balance)))
            sized = max(self.MIN_STAKE, sized)
            self._emit_direct(gui_callback,
                              "🎚 {0}-leg slip @ up-to-x{1:.2f} odds ({2}% joint win) -- "
                              "stake KES {3:.2f}{4}".format(
                                  _n_legs, _max_odds, joint_prob * 100.0, sized,
                                  " (TOO GOOD)" if high_conf else ""))
            stake = sized

            # Kick-off guard: only bail if a chosen match is basically about to kick off
            # (close enough that the leg will be refused/suspended). Everything else
            # goes to the retry/rebuild machinery. We allow games right down to the
            # final moments — no artificial 15-minute minimum.
            grace_min = max(1, min_lead_minutes - 1)
            chosen_ids = {str(leg[2]) for leg in legs}
            for g in playable:
                if str(g.get("id")) in chosen_ids:
                    remaining = (g["start"] - datetime.now()).total_seconds() / 60.0
                    if remaining <= grace_min:
                        self._emit_direct(gui_callback,
                                          f"⏰ {g['name']} kicks off in {remaining:.0f}m — too close, "
                                          "skipping to the next crawl window.")
                        return {"status": "skipped", "skipped": True,
                    "message": "Kickoff too close, moved on"}

            self._stats_per_leg(driver, legs, gui_callback=gui_callback)
            if not self._assert_account_session(driver, phone, password,
                                                gui_callback=gui_callback):
                return {"status": "error",
                        "message": "Account session dropped while studying legs"}
            picked_count = self._click_selected_legs(driver, legs, gui_callback=gui_callback)
            if picked_count < 2:
                self._emit_direct(gui_callback, "⚠️ Could not click the selected odds.")
                return {"status": "error", "message": f"Only {picked_count} odds selected"}

            # ── Portfolio gates, applied to the slip about to be submitted ──
            # This MUST run before _open_betslip_and_place: that call commits the
            # money, so a refusal raised after it is worthless. It is a closure
            # because a rebuild mid-loop swaps the legs, and the swapped slip
            # needs re-checking before the next attempt submits it.
            def _portfolio_gates(_legs_, _product_):
                _gids = [str(l[2]) for l in _legs_]
                _gnames = [l[1] for l in _legs_]
                _gmkts = [l[3] for l in _legs_]
                _ok, _why = self._correlation_verdict(phone, _gids, _gnames, _gmkts)
                if not _ok:
                    self._count_refusal("cross-account correlation")
                    return False, (f"correlation: {_why or 'account/league/market overlap'}")
                # Losing-recipe veto: a shape that has cleared VETO_MIN_TRIALS real
                # bets at VETO_ROI or worse is not retried. Betting it again is not
                # a new attempt, it is the identical bet the ledger already
                # proved loses. This is where the learning actually removes money
                # from play rather than merely reporting it.
                _vkey = "{0}L@{1}/{2}/[{3}]".format(
                    len(_legs_), self._band_of(_product_),
                    self._lead_bucket(min((lead_by_gid.get(l[2]) or 999
                                           for l in _legs_), default=None) or None),
                    "-".join(sorted(set(_gmkts))) or "-")
                if self._recipe_vetoed(_vkey):
                    self._count_refusal("vetoed losing recipe")
                    return False, f"vetoed recipe: {_vkey}"
                return True, ""

            # Place with automatic retries. If the slip loses selections (games going
            # in-play / odds removed) and drops below 3 legs, rebuild the slip with
            # fresh pickable games and try again (bounded rounds).
            placed = False
            used_legs = legs
            used_product = product
            used_ids = set(str(leg[2]) for leg in legs)
            _gate_ok, _gate_why = _portfolio_gates(used_legs, used_product)
            if not _gate_ok:
                self._emit_direct(gui_callback, f"🛑 portfolio refused this slip — {_gate_why}")
                # ONLY a refused gate may return. When the gates PASS, control must
                # fall through to the placement loop below. This return used to sit
                # at the same indent as the `if`, so it fired unconditionally and
                # silently discarded every approved slip — the engine reported "no
                # bet" forever, with an empty reason, and placed nothing at all.
                return {"status": "skipped", "skipped": True, "message": _gate_why,
                        "circuit_breaker": "HALT" in _gate_why.upper(),
                        "correlation_blocked": "correlation" in _gate_why,
                        "recipe_vetoed": "vetoed recipe" in _gate_why}
            for rebuild_round in range(1, 4):
                # A rebuild cannot fix a dead session: the token was rejected by
                # the server, so reselecting legs just repeats the same 403 on a
                # doomed token. _open_betslip_and_place parks the account when it
                # cannot recover, so stop the loop instead of burning two more
                # full crawls against a book that has already refused us.
                try:
                    if str(phone) in (getattr(self, "_parked_until", {}) or {}):
                        self._emit_direct(
                            gui_callback,
                            f"🅿️ {phone}: account is parked after a session rejection — "
                            f"skipping rebuild #{rebuild_round} (a new slip cannot fix "
                            f"a dead token).")
                        break
                except Exception:
                    pass
                # Publish the odds floor this round insists on so the place step can
                # refuse a slip the site degraded below it (see the ODDS FLOOR
                # check inside _open_betslip_and_place). Set immediately before
                # the call and cleared after, so it can never leak across rounds.
                try:
                    self._active_odds_floor = float(target_min)
                except Exception:
                    self._active_odds_floor = 0.0
                res = self._open_betslip_and_place(driver, stake, phone, password,
                                                   gui_callback=gui_callback,
                                                   before_balance=balance,
                                                   legs=used_legs)
                try:
                    self._active_odds_floor = 0.0
                except Exception:
                    pass
                if isinstance(res, bool) and res:
                    placed = True
                    break
                if not (isinstance(res, dict) and res.get("needs_legs")):
                    break
                # The betslip persists across navigation (owner rule): whatever it
                # still holds from the failed attempt must NOT stack into the new
                # legs, or the slip silently mixes old+new selections and the odds
                # read comes out meaningless. Clear it before re-clicking.
                if self._clear_betslip(driver, gui_callback=gui_callback):
                    self._emit_direct(gui_callback,
                                      "  🧹 Cleared the persistent betslip before rebuild.")
                # STACKING GUARD (2026-09-30): a best-effort clear that returned
                # False leaves the old selections in the slip, and clicking the
                # rebuild's fresh legs stacks onto them (3 → 6 → 8) — exactly the
                # dead "Not valid" loop seen on the account-2 rebuild. If the slip
                # is NOT genuinely empty now, do not click: hand back cleanly so
                # the worker re-crawls a fresh page where removal buttons answer.
                try:
                    _leftover = self._read_betslip_count(driver) or 0
                except Exception:
                    _leftover = 0
                if int(_leftover or 0) > 0:
                    self._emit_direct(
                        gui_callback,
                        f"  ⚠️ Slip not empty after clear ({_leftover} leftover) — "
                        "refusing to stack rebuild legs on it; moving on.")
                    return {"status": "skipped", "skipped": True,
                            "message": f"could not clear the persistent slip ({_leftover} leftover)"}
                # Rebuild: only games still kicking off with runway, and none used before
                # ACCOUNT-STARVATION FIX (2026-09-30): this was the LAST hole. The
                # initial draft can now widen to the full board, but if own-slice
                # picks suspend MID-SUBMIT the rebuild re-selected only from the
                # narrowed slice — thin accounts looped "Bet not placed" forever with
                # plenty of fresh games sitting on the full board. Widen the same way
                # the initial draft does: own slice first, full board (minus the owner
                # rule) if the slice comes up short.
                now = datetime.now()
                _slice_fresh = [
                    g for g in playable
                    if str(g.get("id")) not in used_ids and g.get("start")
                    and ((g["start"] - now).total_seconds() / 60.0) >= min_lead_minutes
                ]
                _pool_fresh = _slice_fresh
                if len(_slice_fresh) < max(int(max_legs) * 2, 6) and _full_playable:
                    try:
                        _own2 = getattr(self, "_game_owners", None) or {}
                        _pg2 = str(phone or "")
                        _full_playable = [g for g in _full_playable
                                          if str(g.get("id") or "") not in
                                          {_gid for _gid, _o in _own2.items() if _o != _pg2}]
                    except Exception:
                        pass
                    _full_fresh = [
                        g for g in _full_playable
                        if str(g.get("id")) not in used_ids and g.get("start")
                        and ((g["start"] - now).total_seconds() / 60.0) >= min_lead_minutes
                    ]
                    if len(_full_fresh) > len(_slice_fresh):
                        self._emit_direct(
                            gui_callback,
                            f"🔀 {phone}: rebuild widening from own slice "
                            f"({len(_slice_fresh)} fresh) to the full board "
                            f"({len(_full_fresh)} fresh)...")
                        _pool_fresh = _full_fresh
                remaining_playable = _pool_fresh
                self._emit_direct(gui_callback,
                                  f"🔁 Rebuild #{rebuild_round}: reselecting from "
                                  f"{len(remaining_playable)} fresh upcoming games...")
                new_legs, new_product = self._select_football_legs(
                    remaining_playable, target_min=target_min, target_max=target_max,
                    odds_cap=odds_cap, max_legs=max_legs, used=used_games,
                    prefer_more_legs=prefer_more_legs, seed=jitter_seed,
                    conf_floor=conf_floor, no_odds_cap=no_odds_cap,
                    researched_only=researched_only,
                    gui_callback=gui_callback)
                if not new_legs:
                    self._emit_direct(gui_callback,
                                      "⚠️ Not enough fresh upcoming games to rebuild a valid "
                                      "2+-leg slip — no bet this round.")
                    return {"status": "skipped", "skipped": True,
                            "message": "Slip lost selections and no fresh games left"}
                used_ids |= {str(l[2]) for l in new_legs}
                used_legs = new_legs
                used_product = new_product
                if not self._assert_account_session(driver, phone, password,
                                                    gui_callback=gui_callback):
                    return {"status": "error",
                            "message": "Account session dropped during rebuild"}
                picked_count = self._click_selected_legs(driver, new_legs, gui_callback=gui_callback)
                if picked_count < 2:
                    return {"status": "error", "message": "Rebuild could not select 2 legs"}
                time.sleep(1)
                # The rebuild swapped the legs, so the slip that is about to be
                # submitted is a DIFFERENT bet than the one vetted above. Re-run
                # the gates on the new shape rather than trusting the old verdict.
                _gate_ok, _gate_why = _portfolio_gates(used_legs, used_product)
                if not _gate_ok:
                    self._emit_direct(gui_callback,
                                      f"🛑 portfolio refused the rebuilt slip — {_gate_why}")
                    # Same rule as the pre-loop gate: only a refusal returns. A
                    # passing re-gate must continue to the submit path.
                    return {"status": "skipped", "skipped": True, "message": _gate_why,
                            "circuit_breaker": "HALT" in _gate_why.upper(),
                            "correlation_blocked": "correlation" in _gate_why,
                            "recipe_vetoed": "vetoed recipe" in _gate_why}

            possible = round(float(stake) * used_product, 2)
            if placed:
                self._mark_legs_used(used_legs)
            real_stake = float(getattr(self, "_last_placed_stake", None)) \
                if (placed and getattr(self, "_last_placed_stake", None) is not None) \
                else float(stake)
            # ── CLV snapshot (2026-09-26): remember the price we were offered ──
            # Re-read later (CLV_RECHECK_LEAD_MIN before kick-off) to see whether
            # the market moved in our favour. Positive CLV = we beat the closing
            # price = real edge, even if this particular slip loses. This is the
            # only metric that separates skill from luck over thousands of bets.
            if placed:
                try:
                    self._snapshot_clv(
                        [str(l[2]) for l in used_legs],
                        [l[3] for l in used_legs],
                        [(str(l[2]), l[3], l[0]) for l in used_legs],
                        phone=phone)
                except Exception:
                    pass
            return {"status": "success" if placed else "error",
                    "message": "Bet placed" if placed else "Bet not placed",
                    "legs": len(used_legs), "stake": real_stake,
                    "odds": round(used_product, 2), "possible_win": round(real_stake * used_product, 2),
                    "markets": [l[3] for l in used_legs],
                    "probs": [round(l[4], 4) for l in used_legs],
                    "game_ids": [str(l[2]) for l in used_legs],
                    "leg_names": [l[1] for l in used_legs],
                    "lead_min": min((lead_by_gid.get(l[2]) or 999 for l in used_legs),
                                    default=None) or None,
                    "placed_at": datetime.now().isoformat(timespec="seconds")}

        except Exception as exc:
            self._emit_direct(gui_callback, f"Football bet error: {str(exc)[:150]}")
            return {"status": "error", "message": str(exc)[:150]}

    def _record_shadow_pick(self, legs, phone: str, playable=None, gui_callback=None):
        """Record a shadow bet (stake=0, status='shadow') for a slip the machine
        would pick but is NOT placing with real money. Runs on EVERY round so the
        learning engine always gains a data point — whether or not funds exist —
        making the machine measurably smarter the longer it runs 24/7.

        Deduplicates: same game-set within the same session → only one shadow."""
        try:
            if not legs:
                return
            shadow_game_ids = frozenset(str(l[2]) for l in legs)
            existing = [
                b for b in (getattr(self, "_bets", None) or [])
                if b.get("status") == "shadow"
                and frozenset(b.get("shadow_game_ids") or []) == shadow_game_ids
            ]
            if existing:
                return
            if getattr(self, "_bets", None) is None:
                self._bets = []
            lead_bucket = self._lead_bucket(
                min((g.get("mins_to_start") or 999
                     for g in (playable or [])
                     if str(g.get("id")) in shadow_game_ids),
                    default=None))
            shadow_entry = {
                "id": None,
                "phone": phone or "",
                "placed_at": datetime.now().isoformat(timespec="seconds"),
                "legs": len(legs),
                "stake": 0.0,
                "odds": round(float(self._leg_product(legs)), 2),
                "possible_win": 0.0,
                "markets": [l[3] for l in legs],
                "probs": [round(l[4], 4) for l in legs],
                "status": "shadow",
                "settled_at": None,
                "won_amount": None,
                "shadow_game_ids": sorted(str(l[2]) for l in legs),
                "shadow_legs": [
                    {"gid": str(l[2]), "name": l[1], "market": l[3],
                     "odds": round(l[0], 3), "prob": round(l[4], 4)}
                    for l in legs
                ],
                "recipe": {
                    "legs": len(legs),
                    "band": self._band_of(float(self._leg_product(legs))),
                    "lead": lead_bucket,
                    "mix": "-".join(sorted(set(l[3] for l in legs))) or "-",
                },
            }
            self._bets.append(shadow_entry)
            self._save_ledger()
            self._emit_direct(gui_callback,
                              f"🔮 Shadow bet recorded ({len(legs)} legs) — machine will "
                              "score its outcome for learning regardless of funds.")
        except Exception:
            pass

    @staticmethod
    def _leg_product(legs) -> float:
        p = 1.0
        for l in (legs or []):
            try:
                p *= float(l[0])
            except (TypeError, ValueError):
                continue
        return p

    def _plan_ahead(self, driver, phone: str, password: str, stake: float = 10,
                    target_min: float = 3.0, target_max: float = 6.0,
                    odds_cap: float = 8.0, max_legs: int = 14,
                    min_lead_minutes: int = 5, gui_callback=None):
        """Dry-run while funds are pending: crawl the games and pre-plan the next
        slip WITHOUT clicking anything or placing a bet. Used by win-funded mode
        so the engine always knows which matches to grab the moment balance lands.

        Any qualifying slip is also recorded as a *shadow bet* (stake=0, status=
        'shadow') so the learning engine can score whether it would have won —
        giving the machine continuous learning even when it cannot bet real money.
        """
        try:
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            self._load_usage()
            self._prune_usage()
            used_games = set()
            for gid_key, mks in (self._used_games or {}).items():
                used_games.add(str(gid_key))
                for mk_val in (mks or {}):
                    used_games.add(f"{gid_key}|{mk_val}")
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
            # If today-games is empty, fall back to the football-1 home listing
            # which always has upcoming fixtures.
            if not games:
                self._emit_direct(gui_callback,
                                  "📋 Plan-ahead: today-games empty — trying football-1 home listing...")
                try:
                    self._safe_get(driver, self.FOOTBALL_HOME_URL)
                    time.sleep(1.5)
                    self._scroll_to_load_more_games(driver, gui_callback=gui_callback)
                    games = self._extract_dom_games(driver) or []
                except Exception:
                    pass
            # Also sample the upcoming-games tab to widen the pool.
            back_to = None
            try:
                back_to = driver.current_url
                self._safe_get(driver, self.UPCOMING_GAMES_PAGE_URL)
                time.sleep(1.4)
                extra_games = self._extract_dom_games(driver) or []
                known = {str(g.get("id")) for g in (games or [])}
                games = (games or []) + [g for g in extra_games
                                         if str(g.get("id")) not in known]
            except Exception:
                pass
            finally:
                try:
                    if back_to:
                        self._safe_get(driver, back_to)
                except Exception:
                    pass
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
                        and g["mins_to_start"] >= min_lead_minutes
                        and self._is_recent_enough(g)]
            # Same per-account slice-of-the-board split as _place_one_bet, so a
            # pre-planned slip never targets a match the other account is on.
            try:
                with self._used_lock:
                    buk = self._account_buckets
                    if str(phone or "") not in buk:
                        buk[str(phone or "")] = len(buk)
                _bkt = buk[str(phone or "")]
                _nacc = max(2, len(buk))
                _bucket = [g for g in playable
                           if (int(str(g.get("id") or "0")) % _nacc) == _bkt]
                if _bucket:
                    playable = _bucket
            except Exception:
                pass
            jitter_seed = getattr(self, "_last_jitter_seed", 0)
            try:
                self._scrape_dc_odds(driver, playable, gui_callback=gui_callback,
                                     max_open=8)
            except Exception:
                pass
            legs, product = self._select_football_legs(
                playable, target_min=target_min, target_max=target_max,
                odds_cap=odds_cap, max_legs=max_legs,
                used=used_games, seed=jitter_seed or 0, gui_callback=gui_callback)
            if legs:
                names = " | ".join(f"{l[1]} @{l[0]:.2f}" for l in legs)
                self._emit_direct(gui_callback,
                                  f"📋 PLANNED (KES {stake:,.0f} on arrival): {len(legs)} legs "
                                  f"→ x{product:.2f} — {names}")
                # ── Shadow bet: record this planned slip so we can learn from
                # its outcome even though no real money was staked.
                # We avoid duplicating a shadow bet for the same game set
                # within the same plan-ahead session (checked by game IDs).
                try:
                    shadow_game_ids = frozenset(str(l[2]) for l in legs)
                    existing_shadows = [
                        b for b in (getattr(self, "_bets", None) or [])
                        if b.get("status") == "shadow"
                        and frozenset(b.get("shadow_game_ids") or []) == shadow_game_ids
                    ]
                    if not existing_shadows:
                        if getattr(self, "_bets", None) is None:
                            self._bets = []
                        shadow_entry = {
                            "id": None,
                            "phone": phone or "",
                            "placed_at": datetime.now().isoformat(timespec="seconds"),
                            "legs": len(legs),
                            "stake": 0.0,          # no real money
                            "odds": round(product, 2),
                            "possible_win": 0.0,
                            "markets": [l[3] for l in legs],
                            "probs": [round(l[4], 4) for l in legs],
                            "status": "shadow",    # sentinel — not a real bet
                            "settled_at": None,
                            "won_amount": None,
                            "shadow_game_ids": sorted(str(l[2]) for l in legs),
                            "shadow_legs": [
                                {"gid": str(l[2]), "name": l[1], "market": l[3],
                                 "odds": round(l[0], 3), "prob": round(l[4], 4)}
                                for l in legs
                            ],
                            "recipe": {
                                "legs": len(legs),
                                "band": self._band_of(product),
                                "lead": self._lead_bucket(
                                    min((g.get("mins_to_start") or 999
                                         for g in playable
                                         if str(g.get("id")) in shadow_game_ids),
                                        default=None)),
                                "mix": "-".join(sorted(set(l[3] for l in legs))) or "-",
                            },
                        }
                        self._bets.append(shadow_entry)
                        self._save_ledger()
                        self._emit_direct(gui_callback,
                                          f"🔮 Shadow bet recorded ({len(legs)} legs x{product:.2f}) "
                                          "— will score outcome when results land, regardless of funds.")
                except Exception:
                    pass
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

    # ── Grok governor: watching brain that can steer conservative controls ──
    _GOV_ALLOWED = {
        "stake_percent": (0.5, 20.0),
        "stake_cap": (10.0, 2000.0),
        "research_seconds": (10.0, 300.0),
        # OWNER RULE (2026-09-26): the floor is now 10 MINUTES, not 10 seconds.
        # The engine was chaining a fresh betslip every ~25s, so it never had time
        # to think — it re-drafted on whatever the board happened to show, which
        # is exactly how 431 low-odds bets piled up at -43% ROI. Ten minutes gives
        # the research pass time to actually resolve, the market-weight read to
        # settle, and kick-off times to move before the next decision. The
        # governor may slow this further but can never cut it below 10 minutes.
        "chain_gap": (600.0, 3600.0),
        "min_lead_minutes": (5.0, 45.0),
        "target_odds_min": (1.5, 100.0),
        "target_odds_max": (1.5, 100.0),
        "odds_cap": (1.2, 3.0),
        "prefer_more_legs": (0, 1),
        "win_wait_max": (30.0, 1800.0),
        "fund_recheck_min": (2.0, 240.0),
    }
    _GOV_JOURNAL_PATH = Path(writable_path("sportsape_grok_journal.json"))

    def _grok_log_tail(self, n: int = 25, max_len: int = 200) -> list:
        try:
            ring = list(self._log_ring)[-n:]
        except Exception:
            ring = []
        return [{"t": datetime.fromtimestamp(ts).strftime("%H:%M:%S"), "m": str(msg)[:max_len]}
                for ts, msg in ring]

    def _grok_journal(self, limit: int = 20) -> list:
        try:
            with open(self._GOV_JOURNAL_PATH, "r", encoding="utf-8") as f:
                rows = json.load(f)
            return rows if isinstance(rows, list) else []
        except Exception:
            return []

    def _grok_journal_append(self, entry: dict):
        try:
            rows = self._grok_journal(limit=10**6)
            rows.append(entry)
            rows = rows[-200:]
            with open(self._GOV_JOURNAL_PATH, "w", encoding="utf-8") as f:
                json.dump(rows, f, indent=2)
        except Exception:
            pass

    def _grok_snapshot(self) -> dict:
        es = getattr(self, "_engine_state", {}) or {}
        try:
            summary = self._ledger_summary()
        except Exception:
            summary = {}
        now = datetime.now()
        period = "night" if now.hour >= 18 else "day"
        per_account = []
        for p in es.get("phones") or []:
            try:
                placed = self._today_placed_for(p, now.strftime("%Y-%m-%d"),
                                                include_orphans=False)
                remaining, _period, cap, _pl = self._period_remaining_for(
                    p, es.get("daily_bets") or 20, now.strftime("%Y-%m-%d"),
                    include_orphans=False)
            except Exception:
                placed, remaining, cap = 0, 0, 0
            per_account.append({
                "phone": p,
                "last_balance": (es.get("balances") or {}).get(p),
                "placed_today": placed,
                "cap_this_period": cap,
                "remaining_budget": remaining,
            })
        jackpots = {}
        for pool, st in (getattr(self, "_jackpot_states", {}) or {}).items():
            jackpots[pool] = {
                "scanned_at": getattr(st, "scanned_at", None) if not isinstance(st, dict) else st.get("scanned_at"),
                "state": getattr(st, "state", None) if not isinstance(st, dict) else st.get("state"),
                "ready": getattr(st, "ready", False) if not isinstance(st, dict) else st.get("ready", False),
            }
        staked = float((summary or {}).get("staked") or 0)
        net = float((summary or {}).get("net_profit") or 0)
        return {
            "time": now.strftime("%Y-%m-%d %H:%M:%S"),
            "period": period,
            "engine_busy": bool(es.get("engine_busy")),
            "win_funded_wait": bool(es.get("win_funded_wait")),
            "governor_paused": self._gov_paused_reason,
            "overrides": dict(self._gov_overrides),
            "active_params": dict(es.get("active_params") or {}),
            "round_attempt": es.get("round_attempt"),
            "last_round_status": es.get("last_round_status"),
            "last_round_message": es.get("last_round_message"),
            "consecutive_failures": es.get("consecutive_failures"),
            "driver_heals": int(es.get("driver_heals") or 0),
            "uptime_seconds": int(round((time.time() - float(es.get("started_at") or time.time())))),
            "bets_placed_this_run": es.get("bets_placed"),
            "longshot": dict(es.get("longshot") or {}),
            "accounts": per_account,
            "ledger": {
                "placed": (summary or {}).get("placed"),
                "active": (summary or {}).get("active"),
                "won": (summary or {}).get("won"),
                "lost": (summary or {}).get("lost"),
                "void": (summary or {}).get("void"),
                "won_return": (summary or {}).get("won_return"),
                "staked": (summary or {}).get("staked"),
                "net_profit": (summary or {}).get("net_profit"),
                "roi_pct": round((net / staked * 100.0), 2) if staked else None,
                "per_phone": (summary or {}).get("per_phone"),
            },
            "jackpots": jackpots,
        }

    # ── Agent helpers ──────────────────────────────────────────────────────

    def _active_exposure(self) -> tuple:
        """Return (active_bet_count, sum_possible_win) for the current book."""
        count = 0
        total = 0.0
        try:
            for b in (self._bets or []):
                if (b.get("status") or "").lower() in ("active", "unconfirmed", "pending", ""):
                    count += 1
                    total += float(b.get("possible_win") or 0)
        except Exception:
            pass
        return count, total

    def notify(self, kind: str, text: str):
        """Public hook for GUI / external callers to push an alert."""
        if self._agent_hub is not None:
            try:
                self._agent_hub.alert(kind, text)
            except Exception:
                pass

    def _agent_worker(self, gui_callback, cal_interval_hours: float):
        """Background thread: periodic calibration, daily report, cache cleanup,
        bet-history summary, and Fibi supervision.

        Performance notes:
        - The sleep at the bottom is a single time.sleep(60) broken into 1s
          chunks so the stop event is checked frequently — but we only do real
          work when a timer fires, so the thread is idle (zero CPU) otherwise.
        - sync_bet_results only runs when the ledger has changed (checked by
          bets count + last settled timestamp) to avoid reading the whole list
          every minute when nothing happened.
        - cache.evict() runs every 30 min, not every 60 s.
        """
        cal_interval_s  = max(600.0, cal_interval_hours * 3600.0)
        last_cal        = time.time()
        last_report     = time.time()
        last_sup        = 0.0
        last_evict      = time.time()
        last_history    = 0.0
        last_idle_sync  = 0.0
        idle_sync_interval = 300.0   # check wins every 5 min when engine is idle
        last_clean      = 0.0
        sup_interval    = 120.0   # Fibi check every 2 min
        report_interval = 24 * 3600.0
        evict_interval  = 30 * 60.0   # cache eviction every 30 min
        history_interval = 300.0       # bet-history summary every 5 min
        clean_interval   = 3600.0      # balance-report cleaner every hour

        # Track bets fingerprint so we only run history agent when something changed
        _last_bets_fingerprint = (-1, "")

        # Short initial delay — let the engine complete its first round before
        # the supervisor and history agents start talking over each other.
        for _ in range(5):
            if self._agent_stop.is_set():
                return
            time.sleep(1.0)

        while not self._agent_stop.is_set():
            try:
                now = time.time()

                # ── calibration (every cal_interval_hours) ──────────────────
                if (now - last_cal) >= cal_interval_s and self._agent_hub is not None:
                    try:
                        rows = [b for b in (self._bets or [])
                                if (b.get("status") or "").lower() in ("won", "lost", "void")]
                        if len(rows) >= 10:
                            audit = self._agent_hub.calibrate(rows)
                            settled = audit.get("settled", 0)
                            msg = self._agent_hub.calibrator.summary_line(audit, settled)
                            self._emit_direct(gui_callback, f"📊 {msg}")
                            stats = self._stats if isinstance(self._stats, dict) else {}
                            mw = audit.get("market_weights") or {}
                            if mw:
                                old = stats.get("market_types") or {}
                                stats["market_types"] = {**old, **mw}
                            retire = audit.get("retire") or []
                            if retire:
                                old_r = set(stats.get("retired_markets") or [])
                                stats["retired_markets"] = list(old_r.union(retire))
                            self._stats = stats
                            try:
                                from sportsape_settings import writable_path as _wp
                                sp = Path(_wp("sportsape_stats.json"))
                                sp.write_text(json.dumps(stats, indent=2), encoding="utf-8")
                            except Exception:
                                pass
                            if any((b.get("delta") or 0) < -0.10
                                   for b in (audit.get("buckets") or {}).values()
                                   if b.get("n", 0) >= 15):
                                self._agent_hub.alert("cal",
                                    f"⚠️ Model drift: {msg}", gui_callback=gui_callback)
                            last_cal = now
                            try:
                                self._agent_hub.fibi.beat_agent("calibrator")
                            except Exception:
                                pass
                    except Exception as e:
                        self._emit_direct(gui_callback,
                                          f"⚠️ Calibration hiccup: {str(e)[:80]}")

                # ── daily report ────────────────────────────────────────────
                if (now - last_report) >= report_interval and self._agent_hub is not None:
                    try:
                        summary = self._ledger_summary()
                        journal = self._grok_journal()
                        report = self._agent_hub.reporter.daily(summary, journal)
                        self._emit_direct(gui_callback, f"📈 {report}")
                        last_report = now
                        try:
                            self._agent_hub.fibi.beat_agent("reporter")
                        except Exception:
                            pass
                    except Exception:
                        pass

                # ── stale cache cleanup (every 30 min) ──────────────────────
                if (now - last_evict) >= evict_interval and self._agent_hub is not None:
                    try:
                        self._agent_hub.cache.evict(stale_secs=12 * 3600)
                        last_evict = now
                    except Exception:
                        pass

                # ── bet history summary (every 5 min, only if bets changed) ─
                if (now - last_history) >= history_interval and self._agent_hub is not None:
                    try:
                        bets = list(getattr(self, "_bets", None) or [])
                        # Fingerprint = (count, last settled_at) — cheap to compute
                        last_settled = next(
                            (b.get("settled_at") or "" for b in reversed(bets)
                             if b.get("settled_at")), "")
                        fp = (len(bets), last_settled)
                        if fp != _last_bets_fingerprint:
                            _last_bets_fingerprint = fp
                            self._agent_hub.sync_bet_results(bets, gui_callback=gui_callback)
                            # Run bet recovery whenever bets change
                            self._agent_hub.run_bet_recovery(bets, gui_callback=gui_callback)
                        last_history = now
                    except Exception:
                        pass

                # ── session health check (every 2 min) ──────────────────────
                if self._agent_hub is not None:
                    try:
                        phones = list((self._engine_state or {}).get("phones") or [])
                        actions = self._agent_hub.check_session_health(
                            phones, gui_callback=gui_callback)
                        for act in actions:
                            if act.get("action") == "force_relogin":
                                p = act.get("phone")
                                if p:
                                    self._engine_state.setdefault(
                                        "force_relogin", {})[p] = True
                    except Exception:
                        pass

                # ── balance report file cleaner (every hour) ────────────────
                if (now - last_clean) >= clean_interval and self._agent_hub is not None:
                    try:
                        self._agent_hub.clean_balance_reports(gui_callback=gui_callback)
                        last_clean = now
                    except Exception:
                        pass

                # ── Fibi supervision (every 2 min) ──────────────────────────
                if (now - last_sup) >= sup_interval and self._agent_hub is not None:
                    try:
                        summary = self._ledger_summary()
                        accounts = list(getattr(self, "_accounts_active", []) or [])
                        findings = self._agent_hub.fibi.check(
                            engine_state=self._engine_state,
                            ledger_summary=summary,
                            accounts=accounts,
                            gui_callback=gui_callback,
                            agent_cache=self._agent_hub.cache,
                        )
                        pending = self._agent_hub.fibi.pending()
                        for rec in pending:
                            action = rec.get("action")
                            if action == "rebuild_driver":
                                self._emit_direct(gui_callback,
                                                  f"🌸 Fibi: {rec.get('reason')} — "
                                                  "queuing driver rebuild on next round.")
                                self._engine_state["force_driver_rebuild"] = True
                            elif action == "force_relogin":
                                self._emit_direct(gui_callback,
                                                  f"🌸 Fibi: {rec.get('reason')} — "
                                                  "will force re-login next round for this phone.")
                                target = rec.get("phone")
                                if target:
                                    self._engine_state.setdefault("force_relogin", {})[target] = True
                            elif action == "unpark_account":
                                target = rec.get("phone")
                                if target:
                                    try:
                                        if hasattr(self, "_parked_until"):
                                            self._parked_until.pop(target, None)
                                    except Exception:
                                        pass
                                    self._emit_direct(gui_callback,
                                                      f"🌸 Fibi: unparked {target}")
                            elif action in (
                                "wake_up_analyst", "wake_up_scout",
                                "wake_up_bet_history", "wake_up_calibrator",
                                "wake_up_reporter", "wake_up_risk",
                                "wake_up_cleaner",
                            ):
                                agent_name = rec.get("agent") or action.replace("wake_up_", "")
                                self._emit_direct(gui_callback,
                                                  f"🌸 Fibi: waking {agent_name} — "
                                                  f"{rec.get('reason','stalled')}")
                                try:
                                    self._agent_hub.fibi.beat_agent(agent_name)
                                except Exception:
                                    pass
                        if pending:
                            self._agent_hub.fibi.ack()
                        last_sup = now
                    except Exception:
                        pass

                # ── Idle win-sync: when the engine is not actively betting,
                # open a headless browser every 5 min to check bet history
                # and settle any wins so the ledger stays current 24/7.
                # After the sync, do a PRE-WINDOW RESEARCH pass:
                # crawl upcoming fixtures, run the analyst on top candidates,
                # and cache picks so the bet machine fires instantly when the
                # betting window opens.
                # Wider gap when nothing needs settling: the 5-min cadence
                # was burning two full logins per cycle 24/7 against Akamai
                # for nothing (measured 2026-10-26 - the storm ran while the
                # daily cap hold parked the machine). Active bets keep the
                # 5-min rhythm; otherwise settle research runs every 15.
                _quick_active = sum(
                    1 for b in (getattr(self, "_bets", None) or [])
                    if (b.get("status") or "") in ("active", "unconfirmed")
                    and not str(b.get("status", "")).startswith("shadow"))
                _idle_gap = idle_sync_interval if _quick_active else 900.0
                if (now - last_idle_sync) >= _idle_gap:
                    try:
                        _workers_running = any(
                            t.is_alive() for t in (getattr(self, "_worker_threads", []) or []))
                        _active_bets = sum(
                            1 for b in (getattr(self, "_bets", None) or [])
                            if (b.get("status") or "") in ("active", "unconfirmed")
                            and not str(b.get("status", "")).startswith("shadow"))
                        _phones = list((self._engine_state or {}).get("phones") or [])
                        _pw     = str((self._engine_state or {}).get("password") or "")
                        # The bet workers sleep through the daily-cap hold
                        # (an hours-long wait inside their own thread), so
                        # "no workers alive" is the wrong test for "safe to
                        # sync" - measured 2026-10-14: the whole hold window
                        # went unsettled and the learning journal wrote an
                        # empty day. The adapter sets cap_hold while it holds;
                        # holding means no browser is open, so the sync is
                        # safe exactly then.
                        _holding = bool((self._engine_state or {}).get("cap_hold"))
                        if (not _workers_running or _holding) and _phones and _pw:
                            now_h = datetime.now().hour
                            now_m = datetime.now().minute
                            # 1) Check active bet results
                            if _active_bets > 0:
                                self._emit_direct(
                                    gui_callback,
                                    f"🕐 [{now_h:02d}:{now_m:02d}] Idle: "
                                    f"{_active_bets} active bet(s) — checking results...")
                                for _ph in _phones[:2]:
                                    try:
                                        self.sync_winnings_now(
                                            _ph, _pw, gui_callback=gui_callback)
                                    except Exception:
                                        pass
                            # 2) Pre-window research — crawl + analyse upcoming games
                            # so picks are warm when the betting window opens.
                            try:
                                self._idle_prewindow_research(
                                    _phones[0], _pw,
                                    gui_callback=gui_callback)
                            except Exception:
                                pass
                        last_idle_sync = now
                    except Exception:
                        pass

            except Exception:
                pass

            # Sleep 60 s in 1-second increments so the stop event is checked promptly
            for _ in range(60):
                if self._agent_stop.is_set():
                    return
                time.sleep(1.0)

    def _grok_next_interval(self, base: float) -> float:
        """Adaptive oversight cadence: tight while the machine is mid-flow, light when idle.

        While the engine has recently placed a bet or is waiting for funds (WIN-FUNDED
        WAIT), watch every `base` seconds. Once it settles into monitor-only / long
        gaps, drop to at least 5 minutes — oversight without burning tokens.
        """
        try:
            es = self._engine_state or {}
            last_placed = float(es.get("last_placed_ts") or 0)
        except Exception:
            last_placed = 0
        active = bool(es.get("win_funded_wait")) or (
            last_placed > 0 and (time.time() - last_placed) < 1800)
        return base if active else max(base, 300.0)

    def _grok_worker(self, gui_callback, phone, password, acc_list, interval: float):
        """Background loop: snapshot -> Grok -> apply whitelisted actions, forever."""
        fail_streak = 0
        while not self._grok_stop.is_set():
            started = time.time()
            try:
                if self._grok is None:
                    return
                state = self._grok_snapshot()
                log_tail = self._grok_log_tail(n=25, max_len=200)
                journal = self._grok_journal(limit=20)
                res = self._grok.advise(state, log_tail, journal)
                fail_streak = 0
                self._emit_direct(gui_callback,
                                  f"🤖 {res.get('observation') or 'No observation.'}")
                issues = res.get("issues") or []
                for it in issues[:5]:
                    sev = str(it.get("severity", "low"))
                    what = str(it.get("what", ""))[:180]
                    self._emit_direct(gui_callback, f"🤖 [{sev}] {what}")
                for a in res.get("actions") or []:
                    try:
                        self._grok_apply(a, gui_callback, phone, password, acc_list)
                    except Exception as e:
                        self._emit_direct(gui_callback,
                                          f"🤖 action skipped: {str(e)[:100]}")
                if self._gov_paused_reason:
                    self._emit_direct(gui_callback,
                                      f"🧊 Engine is PAUSED by the governor: {self._gov_paused_reason}")
                self._grok_journal_append({
                    "t": datetime.now().isoformat(timespec="seconds"),
                    "ok": res.get("ok"),
                    "observation": res.get("observation", ""),
                    "issues": issues,
                    "actions": res.get("actions", []),
                })
            except Exception as e:
                fail_streak += 1
                self._emit_direct(gui_callback, f"🤖 Grok cycle error: {str(e)[:120]}")
                if fail_streak >= 4:
                    self._emit_direct(gui_callback,
                                      "🤖 Grok disabled after repeated API failures — "
                                      "engine continues on its own.")
                    return
            # honour the (adaptive) interval, checking the stop flag along the way
            next_wait = self._grok_next_interval(interval)
            waited = 0.0
            while waited < next_wait and not self._grok_stop.is_set():
                time.sleep(min(5.0, next_wait - waited))
                waited += 5.0

    def _grok_apply(self, action, gui_callback, phone, password, acc_list):
        if not isinstance(action, dict):
            return
        op = action.get("op")
        if op == "emit":
            msg = str(action.get("message", "")).strip()
            if msg:
                self._emit_direct(gui_callback, f"🤖 {msg[:240]}")
        elif op == "set_param":
            name = str(action.get("param", "")).strip()
            value = action.get("value")
            if name not in self._GOV_ALLOWED:
                self._emit_direct(gui_callback, f"🤖 rejected unknown param '{name}'")
                return
            lo, hi = self._GOV_ALLOWED[name]
            try:
                v = float(value)
            except (TypeError, ValueError):
                return
            if name == "prefer_more_legs":
                value_num = 1.0 if v >= 0.5 else 0.0
            else:
                value_num = max(lo, min(hi, v))
            if name == "target_odds_min" and self._gov_overrides.get("target_odds_max",
                                                                     value_num + 1) <= value_num:
                value_num = min(value_num, self._gov_overrides.get("target_odds_max", value_num + 1) - 0.5)
            if name == "target_odds_max" and self._gov_overrides.get("target_odds_min",
                                                                     value_num - 1) >= value_num:
                value_num = max(value_num, self._gov_overrides.get("target_odds_min", value_num - 1) + 0.5)
            old = self._gov_overrides.get(name)
            self._gov_overrides[name] = value_num
            self._emit_direct(gui_callback,
                              f"🤖 override {name}: "
                              f"{('(unchanged) ' if old == value_num else '')}{value_num:g}")
        elif op == "pause":
            self._gov_paused_reason = str(action.get("reason", "")).strip() or "governor decision"
            self._emit_direct(gui_callback, f"🧊 PAUSED by governor: {self._gov_paused_reason}")
            if self._agent_hub is not None:
                try:
                    self._agent_hub.alert("gov",
                        f"🧊 GOVERNOR PAUSED betting: {self._gov_paused_reason}",
                        gui_callback=gui_callback)
                except Exception:
                    pass
        elif op == "resume":
            if self._gov_paused_reason:
                self._emit_direct(gui_callback, f"▶️ Governor resumed: {self._gov_paused_reason}")
                if self._agent_hub is not None:
                    try:
                        self._agent_hub.alert("gov",
                            f"▶️ Governor resumed: {self._gov_paused_reason}",
                            gui_callback=gui_callback)
                    except Exception:
                        pass
            self._gov_paused_reason = None
        elif op == "rotate":
            if isinstance(acc_list, list) and len(acc_list) > 1:
                idx = (self._engine_state.get("acc_idx", 0) + 1) % len(acc_list)
                self._engine_state["acc_idx"] = idx
                self._emit_direct(gui_callback,
                                  f"🤖 rotate: next round on {acc_list[idx]} "
                                  f"({str(action.get('message', ''))[:120]})")
        elif op == "jackpot_run":
            msg = str(action.get("message", ""))[:120]
            self._emit_direct(gui_callback, f"🤖 jackpot analysis: {msg or 'triggered'}")
            if phone and password:
                try:
                    self._jackpot_idle_scan(phone, password, gui_callback=gui_callback)
                except Exception as e:
                    self._emit_direct(gui_callback, f"🤖 jackpot scan skipped: {str(e)[:90]}")

    def _gov(self, name, default):
        """Read a governor override with a default (thread-safe enough for our use)."""
        try:
            return self._gov_overrides.get(name, default)
        except Exception:
            return default

    def _load_sched_state(self) -> dict:
        """Persistent scheduler state (acc_idx, bets today, long-shot day) so a
        restart does not reset rotation back to account #0 or re-fire the daily
        long-shot. Values are keyed by date; a stale day's entry is ignored."""
        try:
            if self.SCHED_STATE_PATH.exists():
                data = json.loads(self.SCHED_STATE_PATH.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    return data
        except Exception:
            pass
        return {}

    def _save_sched_state(self, state: dict):
        try:
            self.SCHED_STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.SCHED_STATE_PATH.write_text(json.dumps(state, indent=2), encoding="utf-8")
        except Exception:
            pass

    # ── Per-account worker plumbing ──────────────────────────────────────
    # Every phone in the list gets ONE dedicated Chrome session. Deposit /
    # withdraw / balance flows reuse that session under the account's own lock,
    # so there is exactly ONE login per account at any moment — the second-login
    # collision that killed the old rotating single-session engine is impossible.

    def _account_session_lock(self, phone) -> threading.Lock:
        """Return (creating if needed) the serializing lock for *phone*'s session."""
        phone = str(phone)
        with self._driver_lock:
            if phone not in self._account_locks:
                self._account_locks[phone] = threading.Lock()
            return self._account_locks[phone]

    def _yield_session_for_deposit(self, lock, phone, gui_callback=None):
        """Release *phone*'s session lock briefly so a queued deposit/withdraw on
        THIS phone can run now instead of waiting out the whole fund-watch window,
        then re-acquire before the caller touches the driver again.
        Returns True normally (never raises); the lock is guaranteed held on return."""
        try:
            lock.release()
        except Exception:
            return False
        waited = 0.0
        while waited < 600.0:
            time.sleep(10)
            waited += 10.0
            if lock.acquire(timeout=5):
                self._emit_direct(gui_callback,
                                  f"🔓 {phone}: session lock back after {waited:.0f}s — "
                                  "deposit slot served.")
                return True
        self._emit_direct(gui_callback,
                          f"⏳ {phone}: deposit still on the session — blocking until free.")
        lock.acquire(timeout=1200)
        return True

    def _account_driver(self, phone):
        """The dedicated driver for *phone* (None until its worker builds one)."""
        with self._driver_lock:
            return self._worker_drivers.get(str(phone))

    def _borrow_account_browser(self, phone, gui_callback=None, **build_kw):
        """Get a browser for `phone` WITHOUT ever creating a second session.

        Returns ``(driver, owned)``. If this account already has a live browser,
        that browser is reused and ``owned`` is False — the caller must NOT quit
        it. Only when the account has no browser does one get built (and then
        ``owned`` is True, so the caller must clean it up).

        Background jobs (bet history, winnings sync, jackpot scan, pre-window
        research, market sweep) used to open their OWN headless browser and log
        the account in again, which is exactly what makes the book revoke the
        first token. Reusing the account's single browser removes that whole
        class of failure.
        """
        phone = str(phone)
        existing = self._account_driver(phone)
        if existing is not None:
            try:
                if self._driver_is_usable(existing):
                    return existing, False
            except Exception:
                pass
        # No live browser for this account: take exclusive ownership and build one.
        drv = self._build_driver(gui_callback=gui_callback, phone=phone, **build_kw)
        return self._set_account_driver(phone, drv), True

    def _set_account_driver(self, phone, driver):
        """Register *driver* as the ONE browser for *phone*.

        This is the single claim point for account ownership. Claiming here (not
        at build time) keeps claim and release exactly paired: a preloaded driver
        adopted for an account gets claimed on adoption, and every exit path
        releases via _cleanup_driver/_quit_bet_driver. If the account already has
        a different live browser, the existing one is returned instead — two
        browsers on one account is the 403 "logged in from another device" bug.
        """
        phone = str(phone)
        with self._driver_lock:
            cur = self._worker_drivers.get(phone)
        if cur is not None and cur is not driver:
            try:
                if self._driver_is_usable(cur):
                    return cur
            except Exception:
                pass
        acct = getattr(driver, "_sportsape_account", None)
        if acct != phone:
            if acct:
                try:
                    _release_account_session(acct)
                except Exception:
                    pass
            try:
                if not _acquire_account_session(phone):
                    _who = _account_session_holder(phone)
                    raise RuntimeError(
                        f"account {phone} is owned by another process "
                        f"(pid {_who.get('pid')})")
            except RuntimeError:
                raise
            except Exception:
                pass
            try:
                driver._sportsape_account = phone  # type: ignore[attr-defined]
            except Exception:
                pass
        with self._driver_lock:
            self._worker_drivers[phone] = driver
        return driver

    def _clear_account_driver(self, phone):
        """Drop the registry entry after the browser was quit (worker heal path)."""
        phone = str(phone)
        with self._driver_lock:
            self._worker_drivers.pop(phone, None)

\
    _PROFILE_PREFIX = "sportsape_chrome_"

    @staticmethod
    def _proc_creation_epoch(rows, pid):
        """CreationDate (as epoch seconds) for `pid` from a Win32_Process JSON
        row set, or None when unavailable. WMI reports this as a string, so we
        accept both the '...Z' ISO form and a PS datetime string."""
        for rec in rows or []:
            try:
                if int(rec.get("ProcessId") or 0) != int(pid):
                    continue
            except Exception:
                continue
            raw = rec.get("CreationDate") or rec.get("creationdate")
            if not raw:
                return None
            try:
                import datetime as _dt
                s = str(raw).strip()
                if s.endswith("Z"):
                    s = s[:-1]
                # /Date(1700000000000)/ form
                if s.startswith("/Date("):
                    import re as _re
                    m = _re.search(r"/Date\((-?\d+)", s)
                    return int(m.group(1)) / 1000.0 if m else None
                for fmt in ("%Y-%m-%dT%H:%M:%S.%f", "%Y-%m-%dT%H:%M:%S",
                            "%Y-%m-%d %H:%M:%S.%f", "%Y-%m-%d %H:%M:%S"):
                    try:
                        return _dt.datetime.strptime(s, fmt).timestamp()
                    except ValueError:
                        continue
            except Exception:
                return None
            return None
        return None

    def _reap_stale_chromedrivers(self, gui_callback=None) -> dict:
        """Kill chromedriver.exe processes that belong to this tool but no longer
        own a live browser (2026-10-05).

        WHY THIS EXISTS. The original ownership probe could only prove a driver
        was ours by finding a surviving chrome.exe child that carries our
        temp-profile marker. A driver whose browser has been replaced or crashed
        has NO chrome child at all, so it could never be proven ours — and the
        conservative sweep then spared it FOREVER. The tool rebuilds a browser
        whenever one dies, so every rebuild leaked a driver. Measured on a live
        run: 16 chromedriver processes for 2 browsers, 14 of them orphans,
        each holding a port and burning CPU. That is what sent the fans wild.

        IDENTIFICATION (two independent signals, both required, so we still
        never touch another tool's driver):
          1. the process runs from the Selenium manager cache, AND
          2. it is NOT one of our currently-live drivers, AND
          3. it owns no chrome child carrying our profile marker.
        An old driver from some other automation tool would also satisfy (1),
        but it would still own its own chrome children and is never in our live
        set, so in practice we only reap our own leftovers. To stay strictly
        conservative we additionally require the driver to be older than
        `min_age_s`, which gives a driver that is mid-boot time to attach.
        """
        import subprocess as _sp
        import time as _t
        min_age_s = 180.0
        try:
            r = _sp.run(
                "powershell -NoProfile -NonInteractive -Command "
                "\"Get-CimInstance Win32_Process | Where-Object { $_.Name -in "
                "@('chromedriver.exe','chrome.exe') } | Select-Object Name, "
                "ProcessId, ParentProcessId, ExecutablePath, CommandLine, "
                "CreationDate | ConvertTo-Json -Compress\"",
                capture_output=True, text=True, timeout=40, shell=True)
        except Exception:
            return {"killed": 0, "skipped": "probe failed"}
        import json as _json
        try:
            rows = _json.loads((r.stdout or "").strip() or "[]")
            if isinstance(rows, dict):
                rows = [rows]
        except Exception:
            return {"killed": 0, "skipped": "unparseable probe"}

        # PIDs of drivers we are actively using right now — never touch these.
        live = set()
        try:
            for d in self._worker_drivers.values():
                pr = getattr(getattr(d, "service", None), "process", None)
                if pr is not None and getattr(pr, "pid", None):
                    live.add(int(pr.pid))
        except Exception:
            pass

        marker = self._PROFILE_PREFIX
        chrome_by_parent = {}
        # EVERY chrome parent, ours or not (2026-10-16, see the safety note
        # below): a driver attached to somebody else's browser is just as
        # "in use" as one attached to ours.
        chrome_parents_any = set()
        drivers = []
        for rec in rows or []:
            try:
                pid = int(rec.get("ProcessId") or 0)
                ppid = int(rec.get("ParentProcessId") or 0)
            except Exception:
                continue
            name = (rec.get("Name") or "").lower()
            if name == "chrome.exe":
                chrome_parents_any.add(ppid)
                if marker in (rec.get("CommandLine") or ""):
                    chrome_by_parent.setdefault(ppid, []).append(pid)
            elif name == "chromedriver.exe":
                drivers.append((pid, ppid, rec.get("ExecutablePath") or ""))

        # SAFETY (2026-10-05): a driver that still OWNS a live chrome carrying
        # our profile marker is in use and must NEVER be reaped — even if this
        # process has no handle on it. My first version protected only the PIDs
        # in self._worker_drivers, which are invisible when the reaper is called
        # from another process (or after a driver was re-registered); it then
        # killed every driver including the live ones and broke the engine's
        # ability to place bets. Ownership of our own chrome is the real proof
        # of life, so that is what gates the kill.
        for drv_pid, _ppid, _exe in drivers:
            if chrome_by_parent.get(drv_pid):
                live.add(drv_pid)

        # SAFETY (2026-10-16, owner request "closing the tool must not alter
        # the user's browser"): the rule above only protected drivers that own
        # OUR profile marker. A driver belonging to somebody ELSE's automation
        # owns chrome.exe children too, but they carry no marker - so this
        # reaper happily killed their chromedriver 180s after they launched it,
        # taking their browser session out from under them. Every chromedriver
        # runs from the SAME selenium cache, so the exe path cannot tell the
        # two apart. The decisive signal is use: a driver with any live chrome
        # child is attached to a browser that is in use, whoever owns it.
        anyone_parent = chrome_parents_any
        for drv_pid, _ppid, _exe in drivers:
            if drv_pid in anyone_parent:
                live.add(drv_pid)

        if not drivers:
            return {"killed": 0, "skipped": "no chromedriver found"}

        killed, spared = 0, []
        for pid, _ppid, exe in drivers:
            if pid in live:
                continue
            if marker not in (exe or "").lower() and \
               "selenium" not in (exe or "").lower():
                # Not launched from the Selenium cache — not provably ours.
                spared.append(pid)
                continue
            # Age gate: never reap a driver young enough to still be booting.
            try:
                created = self._proc_creation_epoch(rows, pid)
                if created and (_t.time() - created) < min_age_s:
                    spared.append(pid)
                    continue
            except Exception:
                pass
            try:
                _sp.run(["taskkill", "/PID", str(pid), "/F"],
                        capture_output=True, timeout=15)
                killed += 1
            except Exception:
                spared.append(pid)
        if killed:
            self._emit_direct(
                gui_callback,
                f"\U0001f9f9 Reaped {killed} stale chromedriver process(es) "
                f"(no live browser) — frees CPU/RAM; {len(spared)} spared.")
        return {"killed": killed, "spared": spared, "live": sorted(live)}

    def _reap_orphaned_chrome(self, gui_callback=None) -> dict:
        """Kill chrome.exe processes running on OUR temp profile whose
        chromedriver parent is gone (2026-10-05).

        WHY THIS EXISTS. _reap_stale_chromedrivers cleans up the opposite case -
        a driver with no browser. This handles a browser with no driver: when
        chromedriver is killed or crashes, its chrome children SURVIVE. Nobody
        can drive that browser any more, yet it keeps running, keeps its
        SportPesa session alive, and keeps its own token current.

        That is not just wasted CPU. A live orphan means TWO browsers for one
        account, and each one's login mints a token that invalidates the other.
        Measured on a live run: 3 live browsers for 2 accounts, and an account
        that logged in successfully at 23:06:23 was told "logged in from
        another device" six seconds later with no other account logging in at
        all. The engine then burned its whole round re-authenticating and
        placed nothing.

        IDENTIFICATION (strict, so the user's own Chrome is never touched):
          1. the command line carries our sportsape_chrome_ profile marker, AND
          2. its parent process is no longer a live chromedriver.
        Personal Chrome shares no marker and is excluded by (1) alone.
        """
        import subprocess as _sp
        try:
            r = _sp.run(
                "powershell -NoProfile -NonInteractive -Command "
                "\"Get-CimInstance Win32_Process | Where-Object { $_.Name -in "
                "@('chromedriver.exe','chrome.exe') } | Select-Object Name, "
                "ProcessId, ParentProcessId, CommandLine | ConvertTo-Json -Compress\"",
                capture_output=True, text=True, timeout=40, shell=True)
        except Exception:
            return {"killed": 0, "skipped": "probe failed"}
        import json as _json
        try:
            rows = _json.loads((r.stdout or "").strip() or "[]")
            if isinstance(rows, dict):
                rows = [rows]
        except Exception:
            return {"killed": 0, "skipped": "unparseable probe"}

        marker = self._PROFILE_PREFIX
        live_driver_pids, chrome_rows = set(), []
        for rec in rows or []:
            try:
                pid = int(rec.get("ProcessId") or 0)
                ppid = int(rec.get("ParentProcessId") or 0)
            except Exception:
                continue
            name = (rec.get("Name") or "").lower()
            if name == "chromedriver.exe":
                live_driver_pids.add(pid)
            elif name == "chrome.exe":
                chrome_rows.append((pid, ppid, rec.get("CommandLine") or ""))

        # A chromedriver's children may be re-parented, so also treat any pid
        # that IS a currently-live driver of ours as "owned".
        owned = set()
        try:
            for d in self._worker_drivers.values():
                pr = getattr(getattr(d, "service", None), "process", None)
                if pr is not None and getattr(pr, "pid", None):
                    owned.add(int(pr.pid))
        except Exception:
            pass
        live_driver_pids |= owned

        killed, spared, accounts = 0, [], set()
        for pid, ppid, cmd in chrome_rows:
            if marker not in cmd:
                continue                      # not ours -> never touch
            if ppid in live_driver_pids:
                continue                      # its driver is alive -> healthy
            # The profile name carries the phone, so we can say which account
            # was being fought over.
            try:
                m = re.search(re.escape(marker) + r"(\d*)_", cmd)
                if m and m.group(1):
                    accounts.add(m.group(1))
            except Exception:
                pass
            try:
                _sp.run(["taskkill", "/PID", str(pid), "/F"],
                        capture_output=True, timeout=15)
                killed += 1
            except Exception:
                spared.append(pid)
        if killed:
            who = (" for " + ", ".join(sorted(accounts))) if accounts else ""
            self._emit_direct(
                gui_callback,
                f"  \U0001f9d9 Reaped {killed} orphaned browser process(es){who} "
                f"(profile with no live chromedriver) — these held stale "
                f"sessions that invalidate our own login; {len(spared)} spared.")
        return {"killed": killed, "spared": spared, "accounts": sorted(accounts)}

    def _kill_duplicate_browsers_for_account(self, phone: str,
                                            keep_profile: str = None,
                                            gui_callback=None) -> int:
        """Enforce AT MOST ONE live browser per account.

        WHY THIS IS NEEDED ON TOP OF THE ORPHAN SWEEP. An orphan is a browser
        whose chromedriver is gone. The observed failure was different: a live
        browser with a live chromedriver that the registry had already stopped
        tracking, so the orphan sweep correctly spared it. Measured profiles:
        `0798810080` running TWO browsers at once. Two live browsers on one
        account each mint a token that kills the other's, so the account logs
        in successfully and is then told "logged in from another device" - and
        the round is spent re-authenticating instead of betting.

        We therefore clear every chrome process running on one of THIS account's
        profiles, except the profile we are about to keep. Safety: the path must
        carry our `sportsape_chrome_` marker AND the account's digits, so no
        other account's browser and no personal Chrome can match.
        """
        import subprocess as _sp
        tag = "".join(ch for ch in str(phone or "") if ch.isdigit())[:12]
        if not tag:
            return 0
        # THROTTLE, BEFORE THE QUERY (2026-10-05). This method shells out to a
        # CIM process query, which costs real time on a machine running 20+
        # chrome processes. Called unthrottled from the browser-build hot path
        # it stalled the workers badly enough for Fibi to report an engine
        # stall. One sweep per account per 60s is ample, because duplicates are
        # created by rebuilds rather than continuously.
        _now = time.time()
        _seen = getattr(self, "_dup_sweep_at", None)
        if not isinstance(_seen, dict):
            _seen = {}
            self._dup_sweep_at = _seen
        if _now - _seen.get(tag, 0.0) < 60.0:
            return 0
        _seen[tag] = _now
        marker = self._PROFILE_PREFIX
        want = f"{marker}{tag}_"
        keep = os.path.normcase(os.path.abspath(keep_profile)) if keep_profile else None
        try:
            r = _sp.run(
                "powershell -NoProfile -NonInteractive -Command "
                "\"Get-CimInstance Win32_Process -Filter \\\"Name='chrome.exe'\\\" | "
                "Select-Object ProcessId, CommandLine | ConvertTo-Json -Compress\"",
                capture_output=True, text=True, timeout=40, shell=True)
        except Exception:
            return 0
        import json as _json
        try:
            rows = _json.loads((r.stdout or "").strip() or "[]")
            if isinstance(rows, dict):
                rows = [rows]
        except Exception:
            return 0

        killed = 0
        for rec in rows or []:
            try:
                pid = int(rec.get("ProcessId") or 0)
            except Exception:
                continue
            cmd = rec.get("CommandLine") or ""
            # Two independent gates: our marker AND this exact account's tag.
            if marker not in cmd or want not in cmd:
                continue
            if keep and keep in os.path.normcase(cmd):
                continue
            try:
                _sp.run(["taskkill", "/PID", str(pid), "/F"],
                        capture_output=True, timeout=15)
                killed += 1
            except Exception:
                pass
        if killed:
            self._emit_direct(
                gui_callback,
                f"  \U0001f534 Cleared {killed} duplicate browser process(es) for "
                f"{phone} — only ONE live browser may hold a session per account, "
                f"and extras were invalidating our own login.")
        return killed

    def _chromedriver__our_pids(self, live_pids: set = None) -> set:
        """Return the PIDs of chromedriver.exe processes that belong to THIS
        tool (i.e. whose spawned chrome.exe uses one of our temp profiles).
        Chrome instances created by the user's own Selenium/chromedriver or any
        other tool are never returned, so the sweep below can never kill them."""
        import subprocess as _sp
        profile_marker = self._PROFILE_PREFIX
        driver_cmd = (
            "powershell -NoProfile -NonInteractive -Command "
            "\"Get-CimInstance Win32_Process | "
            "Where-Object { $_.Name -in @('chromedriver.exe','chrome.exe') } | "
            "Select-Object Name, ProcessId, ParentProcessId, CommandLine | "
            "ConvertTo-Json -Compress\""
        )
        try:
            r = _sp.run(driver_cmd, capture_output=True, text=True,
                        timeout=30, shell=True)
        except Exception:
            return set()
        raw = (r.stdout or "").strip()
        if not raw:
            return set()
        try:
            import json as _json
            rows = _json.loads(raw)
            if isinstance(rows, dict):
                rows = [rows]
        except Exception:
            return set()
        # Build two maps: chrome pid -> command line, chromedriver pid -> its chrome children
        chrome_cmdline = {}
        drv_children = {}
        drv_pids = set()
        worker_pids = set()
        for rec in rows or []:
            try:
                pid = int(rec.get("ProcessId") or 0)
            except Exception:
                continue
            name = (rec.get("Name") or "").lower()
            cmd = (rec.get("CommandLine") or "")
            if name == "chrome.exe":
                chrome_cmdline[pid] = cmd
            elif name == "chromedriver.exe":
                drv_pids.add(pid)
                try:
                    if not cmd or "chrome" not in cmd.lower():
                        worker_pids.add(pid)
                except Exception:
                    pass
        try:
            for rec in rows or []:
                try:
                    pid = int(rec.get("ProcessId") or 0)
                    ppid = int(rec.get("ParentProcessId") or 0)
                except Exception:
                    continue
                if pid in drv_pids or ppid in drv_pids:
                    if (rec.get("Name") or "").lower() == "chrome.exe":
                        drv_children.setdefault(ppid, []).append(pid)
        except Exception:
            pass
        ours = set()
        for drv in drv_pids:
            for child in drv_children.get(drv, []):
                if profile_marker in (chrome_cmdline.get(child) or ""):
                    ours.add(drv)
                    break
        # Fall back: never touch anything that can't be proven ours.
        return ours

    def _sweep_orphan_chromedrivers(self, gui_callback=None,
                                    aggressive: bool = False,
                                    live_pids: set = None) -> dict:
        """Kill orphaned chromedriver.exe processes that belong to THIS tool
        (verified via our -user-data-dir=sportsape_chrome_* temp profile on the
        child chrome.exe it spawned). Never touches chromedrivers owned by the
        user or by any other software: without proof the child chrome is ours,
        the driver is left alone."""
        import subprocess as _sp
        live = set(int(p) for p in (live_pids or ()))
        objs = []
        try:
            objs = list(self._worker_drivers.values())
        except Exception:
            pass
        for d in objs:
            try:
                pr = d.service.process
                if pr is not None and pr.pid:
                    live.add(int(pr.pid))
            except Exception:
                pass
        ours = self._chromedriver__our_pids(live_pids=live)
        if not ours:
            return {"killed": 0, "kept_live": list(live),
                    "note": "ownership probe found no tool chromedrivers"}
        rows = sorted(o for o in ours if o not in live)
        if not rows:
            return {"killed": 0, "kept_live": sorted(live | ours),
                    "note": "all tool drivers are live/in-use"}
        kept, killed = [], 0
        for pid in rows:
            if pid in live:
                kept.append(pid)
                continue
            if not aggressive:
                # give freshly-spawned drivers a grace window so we never kill
                # a driver that is mid-boot for this round.
                try:
                    _sp.run(["tasklist", "/FI", "PID eq " + str(pid),
                             "/FO", "CSV", "/NH"],
                            capture_output=True, text=True, timeout=12)
                except Exception:
                    pass
            try:
                _sp.run(["taskkill", "/PID", str(pid), "/F"],
                        capture_output=True, timeout=12)
                killed += 1
            except Exception:
                kept.append(pid)
        self._emit_direct(gui_callback,
                          f"   Orphan chromedriver sweep: killed {killed} | "
                          f"kept {len(kept)} live/in-use (tool-owned only)")
        return {"killed": killed, "kept_live": kept}
    def _close_all_account_drivers(self):
        """Emergency stop: quit every dedicated account browser and clear the map."""
        self._sweep_orphan_chromedrivers(gui_callback=None, aggressive=True)

        with self._driver_lock:
            drivers = list(self._worker_drivers.values())
            self._worker_drivers.clear()
        for d in drivers:
            acct = getattr(d, "_sportsape_account", None)
            try:
                d.quit()
            except Exception:
                pass
            if acct:
                try:
                    _release_account_session(acct)
                except Exception:
                    pass
                try:
                    d._sportsape_account = None
                except Exception:
                    pass

    def shutdown_all_browsers(self) -> int:
        """Quit EVERY browser this engine ever created, and nothing else.
        Covers worker drivers, preloaded pool, the shared _bet_driver and the
        tracked _active_drivers set. Runs at GUI close / app exit so no
        sportsape_temp Chrome is left alive on the system. Returns count."""
        closed = 0
        seen = set()
        buckets = []
        try:
            buckets.append(dict(self._worker_drivers).values())
        except Exception:
            pass
        try:
            buckets.append(list(self._preloaded_drivers))
        except Exception:
            pass
        try:
            buckets.append([self._bet_driver] if self._bet_driver else [])
        except Exception:
            pass
        try:
            buckets.append(list(self._active_drivers))
        except Exception:
            pass
        for bucket in buckets:
            for d in bucket or []:
                if not d or id(d) in seen:
                    continue
                seen.add(id(d))
                try:
                    d.quit()
                except Exception:
                    pass
                tmp = getattr(d, "_sportsape_temp_profile", None)
                if tmp and os.path.exists(tmp):
                    shutil.rmtree(tmp, ignore_errors=True)
                closed += 1
        with self._active_drivers_lock:
            self._active_drivers.clear()
        with self._driver_lock:
            self._worker_drivers.clear()
        try:
            self._preloaded_drivers = []
        except Exception:
            pass
        try:
            self._bet_driver = None
        except Exception:
            pass
        # Final sweep: any chrome still tagged with our temp-profile marker is
        # an orphan from a crash. The user's own Chrome is excluded by the
        # marker's profile-dir guard inside the reaper.
        try:
            reap_our_chrome()
        except Exception:
            pass
        try:
            self.selenium_driver = None
        except Exception:
            pass
        return closed

    def run_football_bet_schedule(self, phone: str = None, password: str = None,
                                   phones: list = None, stake: float = 10,
                                   cadence_seconds: float = 3600.0, max_bets: int = None,
                                   retry_seconds: float = 300.0, monitor_seconds: float = 600.0,
                                   gui_callback=None, stop_event=None,
                                    visible: bool = True, daily_bets: int = 20,
                                    stake_percent: float = 2.0, stake_cap: float = 500.0,
                                    chain_bets: bool = True, chain_gap: float = 600.0,
                                    research_seconds: float = 60.0,
                                    longshot: bool = True, longshot_odds_min: float = 15.0,
                                    longshot_odds_max: float = 60.0, longshot_odds_cap: float = 0.0,
                                    longshot_legs: int = 14,
                                    auto_withdraw: bool = True, withdraw_amount: float = 200.0,
                                    headless: bool = False,
                                    market_whitelist="*",
                                    grok_api_key: str = None, grok_model: str = "grok-3",
                                    grok_interval: float = 90.0,
agent_cfg: dict = None,
                                     jev_api_key: str = None,
                                     jev_weight: float = 0.35,
                                     cashout_enabled: bool = True,
                                     cashout_threshold: float = 0.75,
                                     cal_interval_hours: float = 4.0,
                                     roll_over: bool = False,
                                     conf_floor: float = None,
                                     min_legs: int = 2,
                                     max_legs: int = 4) -> dict:
        """24/7 auto-bet engine: places smart bets AND monitors winnings.

        Users ONE long-lived browser session (stable for 24/7 running; the driver is
        re-healed automatically when it crashes). Each round it crawls today-games,
        picks the smartest accumulator (a game is never repeated across clean
        betslips), places it, then periodically opens the Bet History page and settles
        ledger entries — emitting 🏆 WON / ❌ LOST events and keeping the winnings
        panel honest across restarts (persistent ledger).
        """
        self.auto_cashout_enabled = bool(cashout_enabled)
        self.cashout_threshold = max(0.1, min(1.0, float(cashout_threshold or 0.75)))
        # ── Account rotation ───────────────────────────────────────────────
        # When several phone numbers are listed ("20 bets/day per account"),
        # the engine ROTATES through them: each round uses the next account that
        # still has daily budget left. Accounts that hit their cap are left alone;
        # when every account is capped the loop drops into monitor-only sync.
        acc_list = [p for p in (phones or []) if str(p).strip()]
        if not acc_list:
            acc_list = [phone] if str(phone or "").strip() else []
            phone = acc_list[0] if acc_list else ""
        acc_list = [str(p).strip() for p in acc_list]
        # Publish the REAL account list for the supervisor (2026-09-27).
        # Fibi was reading self._accounts_active, which nothing ever set, so it
        # received an empty list and fell back to whatever phone numbers it found
        # in the ledger/supervisor history. That made it park and rebuild drivers
        # for accounts this machine no longer trades (two stale MSISDNs in the
        # 011.../072... ledger history), emitting hundreds of warnings an hour
        # about accounts nobody owns.
        self._accounts_active = list(acc_list)
        acc_idx = 0
        active_phone = acc_list[acc_idx] if acc_list else ""
        # ── Roll-over mode (owner rule): KES 50, exactly 3 clean/sure legs,
        #    twice per day per account. Only high-confidence (>=0.80) legs allowed.
        if roll_over:
            stake = 50
            daily_bets = 2
            min_legs = 3
            max_legs = 3
            conf_floor = 0.80
        # force a real re-login the first time the active account changes
        session_phone = None
        # ── Persistent rotation state (survives restarts) ──────────────────
        SCHED_STATE = self._load_sched_state()
        today = datetime.now().strftime("%Y-%m-%d")
        if SCHED_STATE.get("date") == today:
            acc_idx = min(int(SCHED_STATE.get("acc_idx", 0)), len(acc_list) - 1)
            active_phone = acc_list[acc_idx] if acc_list else ""
            # Sanity-check the stored counter against the actual ledger count.
            # If the stored count is higher than the real count (e.g. after an
            # engine restart that accumulated counts), reset to the real value.
            self._load_ledger()
            _real_today = sum(
                1 for b in (getattr(self, "_bets", None) or [])
                if str(b.get("placed_at") or "").startswith(today)
                and not str(b.get("status") or "").startswith("shadow")
                and float(b.get("stake") or 0) > 0
            )
            _stored = int(SCHED_STATE.get("bets_placed_today") or 0)
            if _stored > _real_today:
                self._emit_direct(gui_callback,
                                  f"🔧 Counter mismatch: sched says {_stored} bets "
                                  f"today but ledger shows {_real_today} — correcting.")
                SCHED_STATE["bets_placed_today"] = _real_today
                self._save_sched_state(SCHED_STATE)
        else:
            SCHED_STATE = {"date": today, "acc_idx": 0, "bets_placed_today": 0,
                           "longshot_placed_day": ""}
            self._save_sched_state(SCHED_STATE)

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
        waiting_funds = {}   # account phone -> ts of the last time it was found short
        dead_until = {}      # account phone -> ts until which it is parked (login failures)
        login_fail_count = {}  # account phone -> consecutive login failures this run
        recheck_wait = max(120.0, float(self._gov('fund_recheck_min', 30.0)) * 60.0)
        next_daily_msg = 0.0
        last_placed_ts = 0.0
        next_cooldown_msg = 0.0
        max_bets = int(max_bets) if max_bets else None
        daily_bets = int(daily_bets) if daily_bets else 0
        longshot_placed_day = SCHED_STATE.get("longshot_placed_day", "")
        self._load_usage()
        limit_txt = "unlimited" if not max_bets else f"max {int(max_bets)}"
        daily_txt = "∞" if not daily_bets else f"max {int(daily_bets)}/day"
        chain_gap = max(600.0, float(chain_gap))  # OWNER: 10 min between slips
        self._emit_direct(gui_callback,
                          f"📡 BET MACHINE: crawling now, hungry mode "
                           f"{'ON (chained betslips ~every ' + f'{chain_gap/60:g} min while games remain)' if chain_bets else 'OFF (≤1 bet/hr)'}; "
                          f"daily {daily_txt}; scope {limit_txt}; "
                          f"idle scan every {retry:g}s; "
                          f"win-sync every {monitor:g}s; compounded stake "
                          f"{'OFF' if not stake_percent else f'{stake_percent:g}%'}; "
                          f"DAILY LONG-SHOT {'ON (one '+str(int(longshot_legs))+'+-leg ' + f'x{longshot_odds_min:g}-x{longshot_odds_max:g} slip/day)' if longshot else 'OFF'}; "
                          f"AUTO-WITHDRAW {f'ON (KES {withdraw_amount:g}/day)' if auto_withdraw else 'OFF'}")
        if roll_over:
            self._emit_direct(gui_callback,
                              f"🎰 ROLL-OVER MODE ON: KES 50, exactly 3 sure legs "
                              f"(conf ≥ 0.80), combined x2.5-x3.5, 2 slips/day per account.")
        pool = self._pool()
        self._emit_direct(gui_callback,
                          f"💰 SAVINGS MODE: KES {pool:,.2f} reserved {('('+str(int((self._stats.get('pool_share') or self.DEFAULT_POOL_SHARE)*100))+'% of each win banked)') if pool else '(0 — will bank from first win)'}. "
                          f"Bets only spend balance ABOVE the reserve; at KES {withdraw_amount:,.0f} "
                          "saved the daily auto-withdraw fires and the cycle recycles.")
        self._jackpot_next_scan = time.time() + 45.0
        self._jackpot_state = None

        # ── Governor: AI oversight with key rotation across Grok + Gemini ──
        self._gov_overrides = {}
        self._gov_paused_reason = None
        self._grok_full_disable = False
        self._grok = None
        self._grok_stop = threading.Event()
        self._grok_thread = None
        self._grok_hard_failed = None
        # acfg must be defined before Grok so we can read ai_keys from it
        acfg = agent_cfg if isinstance(agent_cfg, dict) else {}
        # Build a rotating client from all configured AI keys
        _ai_keys = [k for k in (acfg.get("ai_keys") or [grok_api_key or ""])
                    if str(k or "").strip()]
        if not _ai_keys and (grok_api_key or "").strip():
            _ai_keys = [(grok_api_key or "").strip()]
        if _ai_keys:
            try:
                from sportsape_grok import RotatingGovernor as _RG
                self._grok = _RG(_ai_keys, timeout=45,
                                 max_calls_per_hour=int(acfg.get("ai_calls_per_hour") or 0))
                def _describe(k):
                    if k.startswith("gsk_"):
                        return "Grok"
                    if k.startswith("sk-proj-"):
                        return "OpenAI"
                    if k.startswith("AQ."):
                        return "Gemini"
                    return "Grok"
                key_desc = " + ".join(_describe(k) for k in _ai_keys[:3])
                self._emit_direct(gui_callback,
                                  f"🤖 AI governor ONLINE ({key_desc}, "
                                  f"{len(_ai_keys)} key(s) in rotation)")
            except Exception as _ge:
                self._grok = None
                self._emit_direct(gui_callback,
                                  f"⚠️ AI governor failed to start: {str(_ge)[:80]}")
        else:
            self._grok_full_disable = True
            self._emit_direct(gui_callback,
                              "ℹ️ No AI key supplied — engine self-governs on calibrated defaults")
        # ── JEV: fast independent leg-probability validator ────────────────
        # JEV (https://jevapi.org/) is a typed-decision model answering in
        # 70-500ms.  When a key is present we ask it for a second opinion on the
        # candidate legs each round and blend its probability into the slip
        # ranking.  Strictly fail-open — no key, timeout, or API error falls
        # back to the engine's own DU/PTN probabilities.
        self._jev = None
        _jev_key = str(acfg.get("jev_api_key") or jev_api_key or "").strip()
        if _jev_key:
            try:
                from sportsape_jev import JevLegValidator, DEFAULT_BLEND
                if jev_weight is None:
                    jev_weight = float(acfg.get("jev_weight") or DEFAULT_BLEND)
                self._jev = JevLegValidator(api_key=_jev_key, weight=jev_weight)
                self._emit_direct(gui_callback,
                                  f"🧠 JEV leg validator ONLINE (blend "
                                  f"{jev_weight:.0%} second-opinion)")
            except Exception as _je:
                self._jev = None
                self._emit_direct(gui_callback,
                                  f"⚠️ JEV disabled after start error: {str(_je)[:80]}")
        elif acfg.get("jev_api_key") or jev_api_key:
            self._emit_direct(gui_callback, "⚠️ JEV start failure — key ignored")
        else:
            self._emit_direct(gui_callback,
                              "ℹ️ No JEV key — leg probs from DU/PTN model only")
        self._engine_state.update({
            "started_at": time.time(),
            "phones":     acc_list,
            "password":   password,   # stored for idle monitor — never logged
            "stake":      float(stake),
            "daily_bets": daily_bets,
            "chain_bets": chain_bets,
            "period":     None,
        })
        # ── Agents: research analyst, risk manager, calibrator, alerts ─────
        # (acfg already assigned above before the Grok block)
        # Enable agents by default — especially when a Grok key is available.
        _agents_on = bool(acfg.get("agents_enabled", True))
        if AgentHub is not None and _agents_on:
            try:
                alert_cfg = {
                    "enabled": bool(acfg.get("alerts_enabled")),
                    "provider": acfg.get("alert_provider") or "none",
                    "twilio_sid": acfg.get("twilio_sid"),
                    "twilio_auth": acfg.get("twilio_auth"),
                    "twilio_from": acfg.get("twilio_from"),
                    "to_phone": acfg.get("alert_phone"),
                    "webhook_url": acfg.get("webhook_url"),
                    "webhook_token": acfg.get("webhook_token"),
                }
                # Build API-Football key list for rotation
                _af_keys = [k for k in (acfg.get("api_football_keys") or [acfg.get("api_football_key") or ""])
                            if str(k or "").strip()]
                _af_key_primary = _af_keys[0] if _af_keys else ""

                self._agent_hub = AgentHub(governor=self._grok, alert_cfg=alert_cfg,
                                           search_dir=os.path.dirname(os.path.abspath(__file__)),
                                           api_football_key=_af_key_primary,
                                           api_football_keys=_af_keys)
                self._agent_stop = threading.Event()
                self._agent_thread = threading.Thread(
                    target=self._agent_worker,
                    args=(gui_callback, float(cal_interval_hours)),
                    daemon=True)
                self._agent_thread.start()
                _grok_status = "+ AI picks (Grok)" if self._grok else "(no Grok key)"
                _api_status  = "+ real form (API-Football)" if acfg.get("api_football_key") else ""
                self._emit_direct(gui_callback,
                                  f"🧠 AGENTS ONLINE {_grok_status} {_api_status} — "
                                  "APEX analyst + league context + session health + "
                                  "bet recovery + Fibi + workspace cleaner")
                # ── Learning summary on startup ────────────────────────────
                try:
                    self._load_stats()
                    _st = self._stats or {}
                    _settled = int(_st.get("settled") or 0)
                    _mt = _st.get("market_types") or {}
                    _ret = _st.get("retired_markets") or []
                    if _settled > 0:
                        best_mk = max(
                            ((mk, float(e.get("won",0))/max(1,int(e.get("trials",1))))
                             for mk, e in _mt.items() if int(e.get("trials",0)) >= 3),
                            key=lambda x: x[1], default=("?", 0))
                        self._emit_direct(gui_callback,
                                          f"📊 LEARNING: {_settled} settled bets | "
                                          f"best market: {best_mk[0]} ({best_mk[1]:.0%} hit rate) | "
                                          f"retired: {_ret or 'none'} | "
                                          f"pool: KES {_st.get('savings_pool',0):,.2f}")
                    else:
                        self._emit_direct(gui_callback,
                                          "📊 LEARNING: no settled bets yet — "
                                          "machine will calibrate after first settlements")
                except Exception:
                    pass
            except Exception as e:
                self._agent_hub = None
                self._emit_direct(gui_callback,
                                  f"⚠️ Agents failed to start: {str(e)[:100]}")
        else:
            self._agent_hub = None

        # ── Startup balance sweep: know each account's funds BEFORE the first
        # bet, so we never keep asking an already-funded account for a deposit.
        # Runs in a background daemon thread (its own throwaway browser) so a
        # long phone list never stalls the betting loop. `self._start_balances`
        # fills in as each account is checked, and `_place_one_bet` cross-checks
        # against it before ever emitting a 'deposit needed'. ──
        # ── Fresh board for the day: archive the previous day's pending slips
        # to a dated snapshot and start at 0 active, so the ledger and game
        # counts read clean on every launch. Wins from old slips still settle
        # via win-sync straight from the SportPesa site. ──
        try:
            self._fresh_day_board(datetime.now().strftime("%Y-%m-%d"),
                                  gui_callback=gui_callback, force=True)
        except Exception:
            pass
        self._start_balances = {}
        self._balance_sweep_busy = True

        def _sweep_worker():
            try:
                sweep_res = self._startup_balance_sweep(
                    acc_list, password, gui_callback=gui_callback,
                    visible=visible, headless=headless, driver=None)
                self._start_balances = sweep_res
                funded_now = [p for p, r in sweep_res.items()
                              if r.get("confirmed")
                              and float(r.get("balance") or 0) >= float(stake)]
                if funded_now:
                    self._emit_direct(
                        gui_callback,
                        f"💰 {len(funded_now)} account(s) confirmed funded: "
                        f"{', '.join(funded_now[:6])}{'…' if len(funded_now) > 6 else ''}")
            except Exception as e:
                self._emit_direct(gui_callback,
                                  f"⚠️ Startup balance sweep skip: {str(e)[:80]}")
            finally:
                self._balance_sweep_busy = False

        threading.Thread(target=_sweep_worker, daemon=True).start()
        # ── Per-account workers ──────────────────────────────────────
        # Replaces the old rotating single-session loop: one dedicated browser +
        # betting loop per phone, each serialized by the account's own session
        # lock. Global state is kept correct with locks:
        #   * shared["bets_placed"] / SCHED_STATE bets+long-shot  -> _sched_lock
        #   * per-account driver registry                          -> _driver_lock
        cfg = {
            "stake": float(stake),
            "visible": bool(visible),
            "headless": bool(headless),
            "roll_over": bool(roll_over),
            "cadence": cadence,
            "retry": retry,
            "monitor": monitor,
            "chain_bets": bool(chain_bets),
            "chain_gap": chain_gap,
            "research_seconds": float(research_seconds),
            "daily_bets": daily_bets,
            "max_bets": max_bets,
            "stake_percent": float(stake_percent or 0.0),
            "stake_cap": float(stake_cap or 0.0),
            "longshot": bool(longshot),
            "longshot_odds_min": float(longshot_odds_min),
            "longshot_odds_max": float(longshot_odds_max),
            "longshot_odds_cap": float(longshot_odds_cap or 0.0),
            "longshot_legs": int(longshot_legs),
            "auto_withdraw": bool(auto_withdraw),
            "withdraw_amount": float(withdraw_amount),
            "recheck_wait": recheck_wait,
            "multi": len(acc_list) > 1,
        }
        if roll_over:
            # ROLL-OVER owns the day: disable the OTHER owner-rule bets — the
            # KES-10 "sure-single" and the x15-x60 long-shot — so they can never
            # consume the two daily roll-over slots with slips that are NOT
            # "KES 50 @ ~x3.00 / exactly 3 legs".
            cfg["sure_single"] = False
            cfg["longshot"] = False
        # ── shared["bets_placed"] starts from the actual today-count in the
        # ledger, not 0, so restarting doesn't lose track of the daily cap.
        _today_str = datetime.now().strftime("%Y-%m-%d")
        _actual_today = sum(
            1 for b in (getattr(self, "_bets", None) or [])
            if str(b.get("placed_at") or "").startswith(_today_str)
            and not str(b.get("status") or "").startswith("shadow")
            and float(b.get("stake") or 0) > 0
        )
        shared = {"bets_placed": _actual_today}
        if _actual_today > 0:
            self._emit_direct(gui_callback,
                              f"📋 Resuming: {_actual_today} real bet(s) already placed "
                              f"today — daily cap counts from {_actual_today}")
        cap_reached = threading.Event()

        # ── Kill-on-restart: stop any still-running workers from a previous
        # run so we never end up with two sets of workers betting simultaneously.
        _prev_threads = getattr(self, "_worker_threads", []) or []
        _prev_cap = getattr(self, "_worker_cap_reached", None)
        if _prev_threads and any(t.is_alive() for t in _prev_threads):
            self._emit_direct(gui_callback,
                              "🔄 Stopping previous worker session before restarting...")
            if _prev_cap is not None:
                try:
                    _prev_cap.set()
                except Exception:
                    pass
            # Also signal the shared stop_event from the previous run if it exists
            _prev_stop = getattr(self, "_prev_stop_event", None)
            if _prev_stop is not None:
                try:
                    _prev_stop.set()
                except Exception:
                    pass
            # Give workers up to 8 s to wind down gracefully
            _deadline = time.time() + 8.0
            for _t in _prev_threads:
                _remaining = max(0.1, _deadline - time.time())
                try:
                    _t.join(timeout=_remaining)
                except Exception:
                    pass
            # Quit any lingering driver sessions
            try:
                for _ph, _drv in list((self._worker_drivers or {}).items()):
                    try:
                        self._quit_bet_driver(_drv)
                    except Exception:
                        pass
                self._worker_drivers.clear()
            except Exception:
                pass
            self._emit_direct(gui_callback, "✅ Previous session stopped — starting fresh.")

        self._worker_cap_reached = cap_reached
        self._prev_stop_event = stop_event
        # ── Startup sweep: clear any sportsape chrome orphaned by a previous
        # crash before warming new browsers. Scoped to our own temp-profile
        # marker, so the user's personal Chrome is never affected.
        try:
            _orphans = reap_our_chrome()
            if _orphans:
                self._emit_direct(gui_callback,
                                  f"🧹 Cleaned {_orphans} orphaned chrome process(es) "
                                  "from a previous session (user browser untouched).")
        except Exception:
            pass
        # ── Warm browsers BEFORE workers start (cold-start was causing
        # 45s renderer timeouts on first round). Each account gets its
        # own pre-heated session so the first crawl is instant.
        try:
            self._emit_direct(gui_callback,
                              f"🔥 Warming {len(acc_list)} browser(s) before first bet — "
                              "please wait ~10s...")
            for _wp in acc_list:
                if not self._account_driver(_wp):
                    try:
                        _drv = self._build_driver(gui_callback=gui_callback,
                                                  force_visible=cfg["visible"], mobile=False,
                                                  headless=cfg["headless"],
                                                  capture_perf=False, minimize=True,
                                                  phone=_wp)
                        self._set_account_driver(_wp, _drv)
                        # INDUSTRIAL-GRADE FIX (2026-10-04): verify the session
                        # is actually live after warmup. A browser that "looks" ready
                        # but has a dead token will fail every bet. Probe the wallet
                        # API once here so we catch a dead session before the worker
                        # starts betting.
                        try:
                            if self._session_is_live(_drv, deep_check=True):
                                self._emit_direct(gui_callback, f"   ✅ {_wp} browser ready (session confirmed)")
                            else:
                                self._emit_direct(gui_callback, f"   ⚠️ {_wp} browser ready but session not live — will re-login on first bet")
                        except Exception:
                            self._emit_direct(gui_callback, f"   ✅ {_wp} browser ready")
                    except Exception as _we:
                        self._emit_direct(gui_callback, f"   ⚠️ warmup {_wp} failed: {str(_we)[:80]}")
            self._emit_direct(gui_callback, "🔥 All browsers warmed — starting workers...")
        except Exception:
            pass
        self._worker_threads = []
        self._phone_workers = {}
        self._acc_list_last = [str(p) for p in acc_list]
        for _p in acc_list:
            _pstop = threading.Event()
            _t = threading.Thread(
                target=self._run_account_worker,
                args=(_p, password, cfg, shared, cap_reached,
                      gui_callback, stop_event, _pstop),
                daemon=True, name=f"acc-worker-{_p}")
            _t.start()
            self._worker_threads.append(_t)
            self._phone_workers[str(_p)] = {"thread": _t, "stop": _pstop}
        self._emit_direct(
            gui_callback,
            f"🚀 {len(acc_list)} dedicated per-account worker(s) started "
            f"({', '.join(acc_list)}) — each owns its own browser session; "
            "no more account switching / second-login collisions.")
        try:
            while True:
                if self._bet_schedule_stopped(stop_event):
                    break
                if cap_reached.is_set():
                    break
                try:
                    self._reconcile_account_workers(
                        password, cfg, shared, cap_reached,
                        gui_callback=gui_callback, stop_event=stop_event)
                except Exception as _re:
                    self._emit_direct(gui_callback,
                                      f"⚠️ worker reconcile error: {str(_re)[:80]}")
                time.sleep(2.0)
        finally:
            cap_reached.set()
            try:
                self._phone_workers = {}
            except Exception:
                pass
            for _t in self._worker_threads:
                try:
                    _t.join(timeout=10)
                except Exception:
                    pass
        if max_bets and shared["bets_placed"] >= int(max_bets):
            self._emit_direct(gui_callback, f"✅ Reached limit of {int(max_bets)} bets — done")
        if self._grok_thread is not None:
            try:
                self._grok_stop.set()
                self._grok_thread.join(timeout=6)
            except Exception:
                pass
        if self._agent_thread is not None:
            try:
                self._agent_stop.set()
                self._agent_thread.join(timeout=4)
            except Exception:
                pass
        self._close_all_account_drivers()
        self._engine_busy = False
        summary = self._ledger_summary()
        self._emit_direct(gui_callback, "⏹️ Bet machine stopped")
        return {"status": "stopped", "message": "Scheduler stopped",
                "bets_placed": shared["bets_placed"], "summary": summary}

    def _reconcile_account_workers(self, password, cfg, shared, cap_reached,
                                   gui_callback=None, stop_event=None):
        """Diff the engine_state phone list (owned live by the GUI phone box)
        against the running per-account workers. Numbers newly typed into the
        box get a dedicated worker; numbers deleted get their worker wound down.
        Called every ~2s from the scheduler's supervise loop while betting."""
        wanted = [str(p) for p in (self._engine_state.get("phones") or []) if str(p).strip()]
        if not wanted:
            wanted = [str(p) for p in (getattr(self, "_acc_list_last", None) or []) if str(p).strip()]
        if not wanted:
            return
        workers = dict(getattr(self, "_phone_workers", None) or {})
        changed = False
        for ph in list(workers.keys()):
            if ph in wanted:
                continue
            changed = True
            entry = workers[ph]
            try:
                entry["stop"].set()
            except Exception:
                pass
            t = entry.get("thread")
            if t is not None:
                try:
                    t.join(timeout=12)
                except Exception:
                    pass
            self._emit_direct(gui_callback,
                              f"🛑 {ph} removed from phone list — worker winding down.")
            workers.pop(ph, None)
        for ph in wanted:
            if ph in workers:
                continue
            if self._bet_schedule_stopped(stop_event) or cap_reached.is_set():
                break
            changed = True
            pstop = threading.Event()
            t = threading.Thread(
                target=self._run_account_worker,
                args=(ph, password, cfg, shared, cap_reached,
                      gui_callback, stop_event, pstop),
                daemon=True, name=f"acc-worker-{ph}")
            t.start()
            workers[ph] = {"thread": t, "stop": pstop}
            self._worker_threads.append(t)
            self._emit_direct(gui_callback,
                              f"🆕 {ph} added to phone list — dedicated worker started.")
        if changed:
            self._phone_workers = workers

    def _run_account_worker(self, phone, password, cfg, shared, cap_reached,
                            gui_callback=None, stop_event=None, phone_stop_event=None):
        """Dedicated betting loop for ONE account: owns its own browser session
        (registered in self._worker_drivers[phone]) and runs every task for that
        phone — balance-aware betting, win-sync, WIN-FUNDED wait, auto-withdraw —
        serialized by the account's own session lock so deposits/withdraws share
        that same session instead of opening a second login that would invalidate
        the account's live session."""
        active_phone = str(phone)
        stake = float(cfg.get("stake", 10) or 0)
        cadence = float(cfg.get("cadence", 3600) or 20)
        retry = float(cfg.get("retry", 300) or 10)
        monitor = float(cfg.get("monitor", 600) or 20)
        chain_bets = bool(cfg.get("chain_bets", True))
        # OWNER RULE (2026-09-26): 10 minutes between betslips, not 25 seconds.
        # 25s left no time for the research pass to resolve or for the market
        # weights to be re-read, so the machine re-drafted on the raw board and
        # buried itself in low-odds losers. floor/min = default = 10 minutes.
        chain_gap = max(600.0, float(cfg.get("chain_gap", 600.0) or 600.0))
        daily_bets = int(cfg.get("daily_bets") or 0)
        max_bets = int(cfg["max_bets"]) if cfg.get("max_bets") else None
        longshot = bool(cfg.get("longshot", True))
        longshot_odds_min = float(cfg.get("longshot_odds_min", 15) or 1)
        longshot_odds_max = float(cfg.get("longshot_odds_max", 60) or 2)
        longshot_odds_cap = float(cfg.get("longshot_odds_cap", 0) or 0)
        longshot_legs = int(cfg.get("longshot_legs", 10) or 2)
        # The long-shot leg count is hard-capped at MAX_SLIP_LEGS_HARD inside the
        # selector, so a configured 14 could only ever build 6. Clamp it HERE, at
        # the point of use, so every downstream announcement, log line and odds
        # target describes the ticket that can actually be built. Promising a
        # 14-leg ticket and then betting 6 is a promise the engine cannot keep,
        # and the operator is left deciding whether the machine is broken.
        if longshot_legs > self.MAX_SLIP_LEGS_HARD or longshot_legs <= 0:
            _requested_legs = longshot_legs
            longshot_legs = self.MAX_SLIP_LEGS_HARD if _requested_legs > 0 else 2
            if _requested_legs > self.MAX_SLIP_LEGS_HARD:
                self._emit_direct(
                    gui_callback,
                    f"ℹ Long-shot leg count {_requested_legs} reduced to "
                    f"{longshot_legs}: a slip can never carry more than "
                    f"{self.MAX_SLIP_LEGS_HARD} legs (MAX_SLIP_LEGS_HARD).")
        # CRASHFIX (2026-10-04): the long-shot → normal-bet fallback below builds
        # a SMART slip using max_legs / min_legs / conf_floor, but those three
        # names were never assigned in this scope. Any round where a long-shot
        # failed to qualify therefore died with
        #   NameError: name 'max_legs' is not defined
        # and the whole round was lost — logged as "round crashed (fail #1)".
        # The path was unreachable while the long-shot block was disabled by
        # `if False and longshot:`, which is exactly why the defect survived.
        # Defaults mirror the normal SMART slip the worker builds every round.
        max_legs = 4
        min_legs = 2
        conf_floor = None
        auto_withdraw = bool(cfg.get("auto_withdraw", True))
        withdraw_amount = float(cfg.get("withdraw_amount", 200) or 0)
        stake_percent = float(cfg.get("stake_percent") or 0.0)
        stake_cap = float(cfg.get("stake_cap") or 0.0)
        # ── OWNER RULE (locked): the stake is ALWAYS the KES 10 minimum. No
        # compounding, no proportional scaling — a good bet never costs more. ──
        stake_percent = 0.0
        stake_cap = 0.0
        # ── Market whitelist from the GUI toggles ("*" = all markets on). ──
        market_whitelist = cfg.get("market_whitelist", "*")
        if isinstance(market_whitelist, (list, tuple, set)):
            self._market_whitelist = {str(m).strip() for m in market_whitelist if str(m).strip()}
        elif isinstance(market_whitelist, str) and market_whitelist.strip() != "*":
            self._market_whitelist = {m.strip() for m in market_whitelist.split(",") if m.strip()}
        else:
            self._market_whitelist = "*"
        recheck_wait = max(120.0, float(cfg.get("recheck_wait", 1800.0) or 0))
        inc_orph = not bool(cfg.get("multi", True))
        attempt = 0
        consec_fail = 0
        driver = None
        last_sync = 0.0
        active_day = ""
        waiting_since = None
        login_fail_count = 0
        dead_until = 0.0
        no_funds_confirmed_count = 0
        last_placed_ts = 0.0
        next_cooldown_msg = 0.0
        next_cap_msg = 0.0
        day_cap, night_cap = self._period_caps(daily_bets)  # initialise before loop

        def _stop():
            if self._bet_schedule_stopped(stop_event) or cap_reached.is_set():
                return True
            try:
                if phone_stop_event is not None and phone_stop_event.is_set():
                    return True
            except Exception:
                pass
            return False

        while True:
            if _stop():
                break
            if max_bets and shared["bets_placed"] >= int(max_bets):
                cap_reached.set()
                break
            attempt += 1
            today = datetime.now().strftime("%Y-%m-%d")
# ── Day rollover: reset per-day counters for this worker. ──
            if today != active_day:
                active_day = today
                waiting_since = None
                with self._sched_lock:
                    st = self._load_sched_state()
                    if st.get("date") != today:
                        st.update({"date": today, "bets_placed_today": 0,
                                   "longshot_placed_day": ""})
                        self._save_sched_state(st)
                        # New day → fresh board: archive yesterday's pending slips
                        # to a dated snapshot and start the day at 0 active.
                        self._fresh_day_board(today, gui_callback=gui_callback)
                        # Weekly portfolio digest (2026-09-26) — the owner's
                        # standing checkpoint on whether the whole fleet is
                        # actually making money, so risk limits get widened on
                        # evidence instead of on how a quiet week felt.
                        try:
                            _iso = datetime.now().isocalendar()
                            _wk = f"{_iso[0]}-W{_iso[1]:02d}"
                            if st.get("last_digest_week") != _wk:
                                st["last_digest_week"] = _wk
                                self._save_sched_state(st)
                                self._emit_portfolio_digest(gui_callback=gui_callback)
                        except Exception:
                            pass
                day_cap, night_cap = self._period_caps(daily_bets)
                placed_now = self._today_placed_for(active_phone, today,
                                                    include_orphans=inc_orph)
                self._emit_direct(gui_callback,
                                  f"🗓️ New day {today} — {active_phone} day/night "
                                  f"split {day_cap}+{night_cap} (already placed {placed_now})")
            # ── Savings-pool auto-withdraw (shared, in_flight-guarded). ──
            pool = self._pool()
            if auto_withdraw and withdraw_amount > 0 and pool >= withdraw_amount:
                try:
                    self._maybe_auto_withdraw(active_phone, password, withdraw_amount,
                                              in_flight_key="pool", pool=pool,
                                              gui_callback=gui_callback)
                except Exception as e:
                    self._emit_direct(gui_callback,
                                      f"⚠️ Savings-withdraw skip: {str(e)[:80]}")
            # ── Daily budget for THIS account (per-period window). ──
            budget_txt = None
            if daily_bets:
                remaining, _p, _cap, _placed_now = self._period_remaining_for(
                    active_phone,                 daily_bets, today, include_orphans=inc_orph)
                if cfg.get("roll_over"):
                    # ROLL-OVER (owner rule): exactly 2 slips/day per account —
                    # KES 50 @ ~x3.00, exactly 3 legs, split 1 daytime + 1 after
                    # 18:00. When both slots are used the account turns
                    # monitor-only (win-sync + jackpot research) and the machine
                    # bets again at the next window / next day.
                    if remaining <= 0:
                        budget_txt = (f"{_p} roll-over slot used "
                                      f"({_placed_now}/2 today)")
                else:
                    # Owner rule (2026-09-18, ENFORCED IN CODE): in normal mode a
                    # fixed daily slip-count NEVER parks a healthy account —
                    # budget_txt stays None. The daily budget remains a hard
                    # SAFETY floor only (never stake more than balance allows),
                    # never a fixed game-count ceiling; parking is reserved ONLY
                    # for genuinely exhausted banks (no playable games / no
                    # balance), driven by the playable-board + balance checks
                    # below — never by a fixed slip-count.
                    budget_txt = None
            if budget_txt is not None:
                # Account hit its period cap → monitor winnings AND research jackpots.
                if time.time() >= next_cap_msg:
                    next_cap_msg = time.time() + 600
                    _dc, _nc = self._period_caps(daily_bets)
                    self._emit_direct(
                        gui_callback,
                        f"🎯 {active_phone}: period cap reached ({budget_txt}) for "
                        f"{today} — monitoring winnings + researching jackpots; "
                        f"betting resumes at next window (night cap {_nc}).")
                lock = self._account_session_lock(active_phone)
                if lock.acquire(timeout=20):
                    try:
                        if driver is not None and self._driver_is_usable(driver) \
                                and (time.time() - last_sync) >= monitor:
                            try:
                                self._monitor_and_sync_winnings(driver,
                                                                gui_callback=gui_callback)
                                last_sync = time.time()
                            except Exception as e:
                                self._emit_direct(gui_callback,
                                                  f"⚠️ Win-sync hiccup: {str(e)[:100]}")
                        # ── Jackpot idle research ──────────────────────────
                        # During dead time (cap reached / no bets) silently
                        # build and cache picks for both jackpot pools so the
                        # MEGA POT and MID POT buttons are instantly ready.
                        if driver is not None and self._driver_is_usable(driver):
                            try:
                                self._idle_jackpot_research(
                                    driver, active_phone, password,
                                    gui_callback=gui_callback)
                            except Exception:
                                pass
                    finally:
                        lock.release()
                self._engine_busy = False
                wait = max(30.0, min(monitor, 300.0))
                waited = 0.0
                while waited < wait and not _stop():
                    time.sleep(min(10.0, wait - waited))
                    waited += 10.0
                continue
            # ── Hourly cooldown (classic mode only). ──
            if not chain_bets and last_placed_ts:
                elapsed = time.time() - last_placed_ts
                if elapsed < cadence:
                    remain = cadence - elapsed
                    if time.time() >= next_cooldown_msg:
                        next_cooldown_msg = time.time() + 600
                        self._emit_direct(gui_callback,
                                          f"⏳ {active_phone}: hourly cooldown — "
                                          f"next bet window in {remain / 60.0:.0f} min")
                    self._engine_busy = False
                    waited = 0.0
                    while waited < remain and not _stop():
                        time.sleep(min(30.0, remain - waited))
                        waited += 30.0
                    continue
            # ── Round: hold the account's session lock for the whole round, so
            # deposits/withdraws wait for us instead of opening a second login. ──
            lock = self._account_session_lock(active_phone)
            if not lock.acquire(timeout=150):
                self._emit_direct(gui_callback,
                                  f"⏳ {active_phone}: session busy (deposit/withdraw) — "
                                  "round deferred.")
                self._engine_busy = False
                waited = 0.0
                while waited < retry and not _stop():
                    time.sleep(10)
                    waited += 10.0
                continue
            try:
                self._engine_busy = True
                # Governor pause (GUI / emergency holds).
                if self._gov_paused_reason:
                    self._emit_direct(gui_callback,
                                      f"🧊 Governor pause — {active_phone} betting held "
                                      f"({self._gov_paused_reason}).")
                    if driver is not None and (time.time() - last_sync) >= monitor \
                            and self._gov_paused_reason != "deposit in progress":
                        try:
                            self._monitor_and_sync_winnings(driver,
                                                            gui_callback=gui_callback)
                            last_sync = time.time()
                        except Exception:
                            pass
                    waited = 0.0
                    while waited < retry and not _stop():
                        time.sleep(min(10.0, retry - waited))
                        waited += 10.0
                    continue
                # ── Parked (no funds → rest hour; login failures) → follow winnings
                # ONLY while parked: settle the ledger, surface WON/LOST events, and
                # keep the balance cache warm — but place NO bets until the rest ends.
                if dead_until and time.time() < dead_until:
                    _park_rem = int((dead_until - time.time()) / 60.0)
                    self._emit_direct(gui_callback,
                                      f"💤 {active_phone} RESTING (no funds / login down) — "
                                      f"{_park_rem} more min of rest, win-sync only (no bets). "
                                      "Other accounts continue with available funds.")
                    self._engine_busy = False
                    waited = 0.0
                    _park = max(retry, dead_until - time.time())
                    while waited < _park and not _stop():
                        # ── REST ≠ idle: follow winnings on the rest account ──
                        # settle any active bets and keep the cached balance fresh so
                        # the next fund check resumes the moment a win lands.
                        try:
                            if driver is not None and self._driver_is_usable(driver) \
                                    and (waited >= 30.0) and ((waited % 150.0) < 15.0):
                                try:
                                    self._monitor_and_sync_winnings(
                                        driver, gui_callback=gui_callback)
                                except Exception:
                                    pass
                            elif driver is not None and self._driver_is_usable(driver) \
                                    and (waited % 150.0) < 8.0:
                                self._emit_direct(gui_callback,
                                                  f"🔭 ({active_phone}) rest-room research: "
                                                  "scanning live games, scores + odds drift "
                                                  "to pre-stage the comeback slips...")
                                try:
                                    self._research_between_bets(
                                        driver, gui_callback=gui_callback,
                                        timeout=float(self._gov("research_seconds",
                                                                cfg.get("research_seconds", 45.0))))
                                except Exception:
                                    pass
                        except Exception:
                            pass
                        time.sleep(min(10.0, _park - waited))
                        waited += 10.0
                    continue
                # ── Dedicated browser: build / heal / forced rebuild. ──
                # A deposit (or withdraw) may have registered a fresh session for
                # this account since our last round — adopt it instead of keeping
                # two browsers alive on the same account (that re-creates the old
                # second-login collision).
                _reg = self._account_driver(active_phone)
                if _reg is not None and _reg is not driver:
                    if driver is not None:
                        try:
                            self._quit_bet_driver(driver)
                        except Exception:
                            pass
                    driver = _reg
                    self._emit_direct(gui_callback,
                                      f"🔁 {active_phone}: adopting freshly-registered "
                                      "session (single browser per account).")
                if driver is None:
                    self._emit_direct(gui_callback,
                                      f"🌐 ({active_phone}) opening stable browser session...")
                    # Clear any browser left behind on one of our profiles whose
                    # chromedriver has died, BEFORE opening the replacement. An
                    # orphan is invisible to the driver registry (it has no live
                    # driver object) but it is still logged in, and its session
                    # will invalidate the one we are about to create - which is
                    # how an account could log in successfully and be told
                    # "logged in from another device" seconds later.
                    try:
                        self._reap_orphaned_chrome(gui_callback=gui_callback)
                    except Exception:
                        pass
                    try:
                        self._kill_duplicate_browsers_for_account(
                            active_phone, gui_callback=gui_callback)
                    except Exception:
                        pass
                    driver = self._set_account_driver(
                        active_phone,
                        self._build_driver(gui_callback=gui_callback,
                                           force_visible=cfg["visible"], mobile=False,
                                           headless=cfg["headless"],
                                           capture_perf=False, minimize=True,
                                           phone=active_phone))
                elif not self._driver_is_usable(driver):
                    self._emit_direct(gui_callback,
                                      f"🔧 ({active_phone}) old browser died, rebuilding...")
                    self._engine_state["driver_heals"] = int(self._engine_state.get("driver_heals", 0)) + 1
                    if self._agent_hub is not None:
                        try:
                            self._agent_hub.supervisor.beat_driver_heal()
                        except Exception:
                            pass
                    self._quit_bet_driver(driver)
                    driver = self._set_account_driver(
                        active_phone,
                        self._build_driver(gui_callback=gui_callback,
                                           force_visible=cfg["visible"], mobile=False,
                                           headless=cfg["headless"],
                                           capture_perf=False, minimize=True,
                                           phone=active_phone))
                else:
                    # FROZEN ACCOUNT: DO NOT CHURN ITS SESSION (2026-10-05). A
                    # frozen account cannot place a bet, yet the supervisor still tore its
                    # browser down and rebuilt it every ~90s, and every rebuild mints a
                    # fresh token. Live log: "forced rebuild of 0798810080 session" three
                    # times in four minutes for an account that cannot bet at all.
                    #
                    # That is not merely waste. If the book caps concurrent sessions per
                    # client rather than per account, this endless re-authentication
                    # invalidates the OTHER account's token - which is exactly what
                    # followed: 0706719388 built a clean 2-leg x1.69 slip and the click
                    # returned "POST /api/bets/place -> http403".
                    #
                    # We hold the existing browser (balance reads keep working) and stop
                    # rebuilding. The freeze itself is NOT changed by this.
                    _acct_frozen = False
                    try:
                        _pf_now = self._load_portfolio()
                        _acct_frozen = bool((_pf_now.get("frozen") or {}).get(str(active_phone)))
                    except Exception:
                        _acct_frozen = False
                    if self._engine_state.get("force_driver_rebuild") and _acct_frozen:
                        self._engine_state.pop("force_driver_rebuild", None)
                        self._emit_direct(
                            gui_callback,
                            f"\U0001f441 SUPERVISOR: rebuild of FROZEN {active_phone} SUPPRESSED "
                            f"- it cannot bet, and re-minting its token every 90s was "
                            f"invalidating the other account's session.")
                    elif self._engine_state.get("force_driver_rebuild"):
                        self._emit_direct(gui_callback,
                                          f"\U0001f441 SUPERVISOR: forced rebuild of {active_phone} session.")
                        self._engine_state.pop("force_driver_rebuild", None)
                        self._engine_state["driver_heals"] = int(self._engine_state.get("driver_heals", 0)) + 1
                        if self._agent_hub is not None:
                            try:
                                self._agent_hub.supervisor.beat_driver_heal()
                            except Exception:
                                pass
                        self._quit_bet_driver(driver)
                        driver = self._set_account_driver(
                            active_phone,
                            self._build_driver(gui_callback=gui_callback,
                                               force_visible=cfg["visible"], mobile=False,
                                               headless=cfg["headless"],
                                               capture_perf=False, minimize=True,
                                               phone=active_phone))
                # Eager login: confirm this account's session is live before crawling.
                # INDUSTRIAL-GRADE FIX (2026-10-04): run a full health check first.
                # This catches dead tokens, crashed browsers, and stale sessions
                # before we try to bet — preventing the "another device" death spiral.
                if not self._driver_health_check(driver, active_phone, password, gui_callback=gui_callback):
                    # Driver is dead — rebuild it
                    self._emit_direct(gui_callback,
                                      f"🔧 ({active_phone}) driver health check failed — rebuilding browser...")
                    self._engine_state["driver_heals"] = int(self._engine_state.get("driver_heals", 0)) + 1
                    if self._agent_hub is not None:
                        try:
                            self._agent_hub.supervisor.beat_driver_heal()
                        except Exception:
                            pass
                    self._quit_bet_driver(driver)
                    driver = self._set_account_driver(
                        active_phone,
                        self._build_driver(gui_callback=gui_callback,
                                           force_visible=cfg["visible"], mobile=False,
                                           headless=cfg["headless"],
                                           capture_perf=False, minimize=True,
                                           phone=active_phone))
                self._ensure_bet_login(driver, active_phone, password, gui_callback=gui_callback)
                if not self._session_is_live(driver):
                    for _try in range(2):
                        time.sleep(3)
                        self._ensure_bet_login(driver, active_phone, password,
                                               gui_callback=gui_callback)
                        if self._session_is_live(driver):
                            break
                    if not self._session_is_live(driver):
                        login_fail_count += 1
                        self._emit_direct(gui_callback,
                                          f"🔐 {active_phone} login unreachable this round.")
                        if login_fail_count >= 3:
                            dead_until = time.time() + max(120.0, recheck_wait * 2)
                            login_fail_count = 0
                            self._emit_direct(gui_callback,
                                              f"🪦 Parking {active_phone}: {3} straight login "
                                              "failures — will re-check later.")
                            if self._agent_hub is not None:
                                try:
                                    self._agent_hub.supervisor.beat_parked(active_phone)
                                except Exception:
                                    pass
                    else:
                        login_fail_count = 0
                else:
                    login_fail_count = 0
                # Win-sync catch-up: settle bets that finished while away/stopped.
                # Check more frequently when there are active bets that could settle.
                _active_count = sum(1 for b in (getattr(self, "_bets", None) or [])
                                    if (b.get("status") or "") in ("active", "unconfirmed")
                                    and not str(b.get("status", "")).startswith("shadow"))
                # Poll faster while a slip is still awaiting confirmation — that
                # is exactly the window in which a phantom would otherwise sit
                # unnoticed inflating exposure.
                _sync_interval = 180.0 if _active_count > 0 else max(60.0, monitor / 4)
                if driver is not None and (time.time() - last_sync) >= _sync_interval:
                    try:
                        self._monitor_and_sync_winnings(driver, gui_callback=gui_callback)
                        last_sync = time.time()
                    except Exception as e:
                        self._emit_direct(gui_callback,
                                          f"⚠️ Win-sync catch-up hiccup: {str(e)[:90]}")
                self._emit_direct(gui_callback,
                                  f"⏱️ Crawl-and-bet attempt #{attempt} ({active_phone}) ...")
                # ── CHEAP FROZEN-ACCOUNT PRE-CHECK (2026-10-05) ──────────
                # The drawdown gate used to run only AFTER a full board crawl
                # and a login gate. A frozen account therefore paid for a
                # complete crawl every 5 minutes to be told the same thing:
                # "account frozen: -47% from peak". Observed 38 times in 3
                # hours, which is where the CPU went. The latch is already
                # persisted, so we can answer from it for free and skip the
                # crawl entirely.
                # This does NOT change the risk limit - the freeze still
                # applies and no bet is placed; we simply stop paying to
                # discover it.
                try:
                    _pf = self._load_portfolio()
                    if _pf.get("frozen", {}).get(str(active_phone)):
                        self._emit_direct(
                            gui_callback,
                            f"⏸️ {active_phone}: account is frozen by the drawdown "
                            f"breaker — skipping the board crawl entirely this round "
                            f"(no risk change; the freeze stands).")
                        self._engine_state["frozen_skips"] = int(
                            self._engine_state.get("frozen_skips", 0)) + 1
                        # Sleep the SAME interval the engine uses between
                        # rounds (the "re-crawling in 300s" cadence). A short
                        # sleep here produced a tight spin - "Crawl-and-bet
                        # attempt #13..#19" every 30 s, all skipped instantly -
                        # which burned CPU and buried the real log in noise.
                        time.sleep(300.0)
                        continue
                except Exception:
                    pass
                # Governor overrides (whitelisted + clamped upstream) applied per round.
                _gov_stake_percent = self._gov('stake_percent', stake_percent)
                _gov_stake_cap = self._gov('stake_cap', stake_cap)
                _gov_mll = self._gov('min_lead_minutes', 5.0)
                _gov_oc = self._gov('odds_cap', 6.0)
                _gov_pref_legs = bool(self._gov('prefer_more_legs', 0))
                # DAILY LONG-SHOT / FISHNET SCHEDULING (2026-10-05). Both of these open a
                # separate bet-schedule branch that replaces the normal SMART
                # round. If the account is in a login cooldown they cannot
                # succeed — the pre-slip gate will decline them — but they were
                # still being attempted EVERY round (fishnet fired 4x on one
                # stuck account), burning the round and flooding the log with
                # retries that were doomed by construction. When an account is
                # cooling down we defer these to the normal path and let the
                # cooldown run.
                _bo_active = bool(
                    float((getattr(self, "_auth_backoff", {}) or {}).get(
                        str(active_phone)) or 0.0) > time.time())
                if _bo_active and (want_longshot or want_fishnet):
                    self._emit_direct(
                        gui_callback,
                        f"⏸️ {active_phone}: deferring the "
                        + ("long-shot" if want_longshot else "fishnet")
                        + " ticket — this account is in a login cooldown.")
                    want_longshot = False
                    want_fishnet = False
                    if self._agent_hub is not None:
                        try:
                            self._agent_hub.supervisor.beat_agent("risk")
                        except Exception:
                            pass

                # Daily LONG-SHOT: TWO x15-x60 accumulators per day —
                # first fires on the first qualifying round of the day,
                # second fires after 18:00 on the first qualifying round that evening.
                # BUDGET GUARD: if remaining balance can cover ≤ 2 more bets, fire
                # any pending longshot immediately rather than waiting for later.
                want_longshot = False
                # DAILY SURE-SINGLE (owner rule — "one odd for sure roll over daily on
                # ALL accounts so we never go broke"): fires FIRST each day, at x1.50-
                # x2.50 on 2-3 sure-researched 1X2 legs, board-wide so every account
                # always gets a qualifying game. Day-gated once per account.
                want_sure = False
                if bool((cfg or {}).get("sure_single", True)):
                    with self._sched_lock:
                        st = self._load_sched_state()
                        if st.get("date") != today:
                            st.update({"date": today, "bets_placed_today": 0,
                                       "longshot_placed_day": "",
                                       "longshot2_placed_day": "", "sure_placed_day": ""})
                        _sure_day = st.get("sure_placed_day") or ""
                        _sure_pend = float(st.get("sure_pending_ts") or 0)
                    if _sure_day != today and (time.time() - _sure_pend) > 900:
                        with self._sched_lock:
                            st = self._load_sched_state()
                            st["sure_pending_ts"] = time.time()
                            self._save_sched_state(st)
                        want_sure = True
                if want_sure:
                    _sure_stake = 10.0
                    try:
                        _cached_bal = 999.0
                        _bc = self._cached_balance_for(active_phone, allow_stale=True)
                        if _bc and _bc.get("confirmed"):
                            _cached_bal = float(_bc.get("balance") or 999)
                    except Exception:
                        pass
                    self._emit_direct(gui_callback,
                                      f"🎯 {active_phone} DAILY SURE-SINGLE: 2-3 x1.50-x2.50 "
                                      f"researched legs (stake {_sure_stake:.0f}) — earliest "
                                      f"rollover so we never go broke")
                    res = self._place_one_bet(
                        driver, active_phone, password,
                        stake=_sure_stake,
                        cfg=cfg,
                        board_wide=True,
                        researched_only=True,
                        target_odds_min=1.5,
                        target_odds_max=2.5,
                        max_legs=3,
                        prefer_more_legs=False,
                        stake_percent=self._gov('stake_percent', 5.0),
                        stake_cap=self._gov('stake_cap', 20.0),
                        reserve_pool=0,
                        jitter_seed=(int((re.sub(r"\D", "", str(active_phone or "")) or "0")[-6:])
                                     + int(datetime.now().strftime("%Y%m%d%H"))),
                        no_odds_cap=True,
                        conf_floor=0,
                        gui_callback=gui_callback,
                        odds_cap=self._gov('odds_cap', 5.0),
                        min_lead_minutes=5.0)
                    with self._sched_lock:
                        st = self._load_sched_state()
                        st["sure_placed_day"] = today
                        st["sure_pending_ts"] = 0
                        self._save_sched_state(st)
                    if res and res.get("ok"):
                        self._emit_direct(gui_callback,
                                          f"✅ {active_phone} SURE-SINGLE placed "
                                          f"({res.get('odd', '')}) — bankroll rolls over.")
                        continue
                if longshot:
                    with self._sched_lock:
                        st = self._load_sched_state()
                        if st.get("date") != today:
                            st.update({"date": today, "bets_placed_today": 0,
                                       "longshot_placed_day": "",
                                       "longshot2_placed_day": ""})
                        _ls_day  = st.get("longshot_placed_day") or ""
                        _ls2_day = st.get("longshot2_placed_day") or ""
                        _ls_pend = float(st.get("longshot_pending_ts") or 0)
                        _ls2_pend = float(st.get("longshot2_pending_ts") or 0)
                        hour_now = datetime.now().hour

                        # Estimate remaining balance
                        _cached_bal = 999.0
                        try:
                            _bc = self._cached_balance_for(active_phone, allow_stale=True)
                            if _bc and _bc.get("confirmed"):
                                _cached_bal = float(_bc.get("balance") or 999)
                        except Exception:
                            pass
                        _balance_tight = _cached_bal <= float(stake) * 3

                        # First longshot: any time today, not yet placed
                        if _ls_day != today and (time.time() - _ls_pend) > 900:
                            st["longshot_pending_ts"] = time.time()
                            st["longshot_which"] = 1
                            self._save_sched_state(st)
                            want_longshot = True
                        # Second longshot: normally after 18:00 — BUT if balance is
                        # tight, fire it NOW to guarantee both longshots run before
                        # funds run out, regardless of the time-of-day restriction.
                        elif _ls2_day != today and (time.time() - _ls2_pend) > 900:
                            if hour_now >= 18 or _balance_tight:
                                if _balance_tight and hour_now < 18:
                                    self._emit_direct(gui_callback,
                                                      f"⚡ Balance tight (KES {_cached_bal:.0f}) — "
                                                      "firing 2nd longshot now before funds run out")
                                st["longshot2_pending_ts"] = time.time()
                                st["longshot_which"] = 2
                                self._save_sched_state(st)
                                want_longshot = True
                # ── FISHNET LOTTERY (owner rule) ───────────────────────────
                # Once or twice a day per account: bundle every game the machine
                # already bet today (across ALL accounts) into one long multi-leg
                # lottery slip. Fires only after the pool has enough games, so it
                # never runs before the normal slips have built a meaningful fishnet.
                want_fishnet = False
                with self._sched_lock:
                    st = self._load_sched_state()
                    if st.get("date") != today:
                        st.update({"date": today, "bets_placed_today": 0,
                                   "fishnet_placed_day": "", "fishnet2_placed_day": ""})
                    _fn_day  = st.get("fishnet_placed_day") or ""
                    _fn2_day = st.get("fishnet2_placed_day") or ""
                    _fn_pend = float(st.get("fishnet_pending_ts") or 0)
                    _fn2_pend = float(st.get("fishnet2_pending_ts") or 0)
                    hour_now = datetime.now().hour
                    _pool = self._fishnet_pool_today()
                    _pool_ready = len(_pool) >= 4
                    if _fn_day != today and _pool_ready and (time.time() - _fn_pend) > 1800:
                        st["fishnet_pending_ts"] = time.time()
                        st["fishnet_which"] = 1
                        self._save_sched_state(st)
                        want_fishnet = True
                    elif _fn2_day != today and _pool_ready and (time.time() - _fn2_pend) > 1800 \
                            and hour_now >= 18:
                        st["fishnet2_pending_ts"] = time.time()
                        st["fishnet_which"] = 2
                        self._save_sched_state(st)
                        want_fishnet = True
                if want_fishnet:
                    with self._sched_lock:
                        st = self._load_sched_state()
                        _which_label = "2nd" if int(st.get("fishnet_which") or 1) == 2 else "1st"
                    self._emit_direct(gui_callback,
                                      f"🐟 {active_phone} FISHNET LOTTERY ({_which_label}): "
                                      f"bundling today's pooled games into one long slip")
                    _fn_res = self._place_fishnet_bet(
                        driver, active_phone, password, stake=stake,
                        gui_callback=gui_callback, max_legs=14)
                    if isinstance(_fn_res, dict) and _fn_res.get("status") == "success":
                        with self._sched_lock:
                            st = self._load_sched_state()
                            _which = int(st.get("fishnet_which") or 1)
                            if _which == 2:
                                st["fishnet2_placed_day"] = today
                                st.pop("fishnet2_pending_ts", None)
                            else:
                                st["fishnet_placed_day"] = today
                                st.pop("fishnet_pending_ts", None)
                            st.pop("fishnet_which", None)
                            self._save_sched_state(st)
                        self._record_bet_from_result(_fn_res, phone=active_phone)
                        with self._bets_lock:
                            shared["bets_placed"] += 1
                        self._emit_direct(gui_callback,
                                          f"🐟 {active_phone} FISHNET placed "
                                          f"({_fn_res.get('legs')} legs @x{_fn_res.get('odds')})")
                        continue
                    else:
                        # Fishnet failed this round — clear the pending marker so a
                        # later round retries instead of losing the daily slot.
                        with self._sched_lock:
                            st = self._load_sched_state()
                            st["fishnet_pending_ts"] = 0
                            st.pop("fishnet_which", None)
                            self._save_sched_state(st)
                        self._emit_direct(gui_callback,
                                          f"🐟 Fishnet skipped this round: "
                                          f"{(isinstance(_fn_res, dict) and _fn_res.get('message')) or 'not enough live pooled games'}")
                # Per-account deterministic tie-break seed (never stack identical slips).
                jitter_seed = (int((re.sub(r"\D", "", str(active_phone or "")) or "0")[-6:])
                               + int(datetime.now().strftime("%Y%m%d%H")))
                if want_longshot:
                    with self._sched_lock:
                        st = self._load_sched_state()
                        _which_label = "2nd" if int(st.get("longshot_which") or 1) == 2 else "1st"
                    self._emit_direct(gui_callback,
                                      f"🎯 {active_phone} DAILY LONG-SHOT ({_which_label}): "
                                      f"{int(longshot_legs)}-leg "
                                      f"x{longshot_odds_min:g}-x{longshot_odds_max:g} ticket today")
                    longshot_odds_cap_v = float(longshot_odds_cap or 0)
                    try:
                        res = self._place_one_bet(driver, active_phone, password, stake=stake,
                                                  visible=cfg["visible"],
                                                  gui_callback=gui_callback,
                                                  target_odds_min=longshot_odds_min,
                                                  target_odds_max=longshot_odds_max,
                                                  odds_cap=longshot_odds_cap or 8.0,
                                                  max_legs=int(longshot_legs),
                                                  stake_percent=_gov_stake_percent,
                                                  stake_cap=_gov_stake_cap,
                                                  min_lead_minutes=_gov_mll,
                                                  prefer_more_legs=True,
                                                  board_wide=True,
                                                  reserve_pool=0,
                                                  jitter_seed=jitter_seed,
                                                  no_odds_cap=(longshot_odds_cap_v <= 0),
                                                  conf_floor=0.0,
                                                  researched_only=bool(longshot_odds_cap_v <= 0))
                    except Exception as _ls_exc:
                        _ls_err = str(_ls_exc).lower()
                        if "invalid session id" in _ls_err or "no such window" in _ls_err:
                            self._emit_direct(gui_callback,
                                              f"⚠️ {active_phone}: browser crashed during longshot — rebuilding driver")
                            self._engine_state["driver_heals"] = int(self._engine_state.get("driver_heals", 0)) + 1
                            self._quit_bet_driver(driver)
                            driver = self._set_account_driver(
                                active_phone,
                                self._build_driver(gui_callback=gui_callback,
                                                   force_visible=cfg["visible"], mobile=False,
                                                   headless=cfg["headless"],
                                                   capture_perf=False, minimize=True,
                                                   phone=active_phone))
                            self._ensure_bet_login(driver, active_phone, password, gui_callback=gui_callback)
                            res = {"status": "error", "message": "driver rebuilt after crash"}
                        else:
                            raise
                else:
                    if cfg.get("roll_over"):
                        # ROLL-OVER (owner rule): KES 50, exactly 3 legs, combined
                        # odds ~x3.00 (2.5-3.5), ONLY high-confidence legs — this
                        # is the dedicated roll-over slip, not the flat x5-6 plan.
                        self._emit_direct(gui_callback,
                            f"🎰 {active_phone}: ROLL-OVER slip — KES 50, "
                            f"3 legs, x2.5-x3.5, conf ≥ 0.80")
                        res = self._place_one_bet(
                            driver, active_phone, password, stake=stake,
                            visible=cfg["visible"],
                            gui_callback=gui_callback,
                            target_odds_min=2.5, target_odds_max=3.5,
                            odds_cap=_gov_oc,
                            max_legs=3, min_legs=3, conf_floor=0.80,
                            stake_percent=_gov_stake_percent,
                            stake_cap=_gov_stake_cap,
                            min_lead_minutes=_gov_mll,
                            prefer_more_legs=False,
                            reserve_pool=0,
                            jitter_seed=jitter_seed)
                    else:
                        # OWNER FLOOR (2026-09-28): the live band is
                        # self.MIN_COMBINED_ODDS (2.5) up to _gov('target_odds_max'),
                        # NOT a hardcoded x5-x6. A KES 10 bet at the 2.5 floor
                        # returns at least KES 20, which is what the owner asked
                        # for. The old x5-x6 default demanded roughly double that
                        # and, with the retry ladder already degraded to x3-x4,
                        # could not be filled even from a 62-game placeable board —
                        # so the engine sat refusing to bet on a healthy account.
                        # The 2.5 floor stays absolute; only the band above it moved.
                        _hi = float(self._gov('target_odds_max', 6.0) or 6.0)
                        lo = max(float(self.MIN_COMBINED_ODDS),
                                 float(self._gov('target_odds_min', 0.0) or 0.0))
                        hi = max(lo, _hi)
                        try:
                            res = self._place_one_bet(driver, active_phone, password, stake=stake,
                                                      visible=cfg["visible"],
                                                      gui_callback=gui_callback,
                                                      target_odds_min=lo, target_odds_max=hi,
                                                      odds_cap=_gov_oc,
                                                      max_legs=4,
                                                      stake_percent=_gov_stake_percent,
                                                      stake_cap=_gov_stake_cap,
                                                      min_lead_minutes=_gov_mll,
                                                      prefer_more_legs=False,
                                                      reserve_pool=0,
                                                      jitter_seed=jitter_seed)
                        except Exception as _bet_exc:
                            _bet_err = str(_bet_exc).lower()
                            if "invalid session id" in _bet_err or "no such window" in _bet_err:
                                self._emit_direct(gui_callback,
                                                  f"⚠️ {active_phone}: browser crashed during bet — rebuilding driver")
                                self._engine_state["driver_heals"] = int(self._engine_state.get("driver_heals", 0)) + 1
                                self._quit_bet_driver(driver)
                                driver = self._set_account_driver(
                                    active_phone,
                                    self._build_driver(gui_callback=gui_callback,
                                                       force_visible=cfg["visible"], mobile=False,
                                                       headless=cfg["headless"],
                                                       capture_perf=False, minimize=True,
                                                       phone=active_phone))
                                self._ensure_bet_login(driver, active_phone, password, gui_callback=gui_callback)
                                res = {"status": "error", "message": "driver rebuilt after crash"}
                            else:
                                raise
                # A long-shot that didn't qualify on this account → try the other
                # accounts before falling back to a normal bet.  This handles the
                # common case where a game is suspended mid-placement on one account
                # but the slip is still valid on a fresh session for another account.
                want_longshot_eff = want_longshot
                if want_longshot and not (isinstance(res, dict)
                                          and res.get("status") == "success"):
                    _ls_fail_msg = str((res or {}).get("message") or "") if isinstance(res, dict) else ""
                    _ls_suspended = any(k in _ls_fail_msg.lower()
                                        for k in ("suspend", "abort", "odds removed",
                                                  "not enough", "no bet", "no combo",
                                                  "no accumulator"))
                    # Try other accounts for the longshot if this one failed
                    _alt_tried = False
                    if _ls_suspended or (isinstance(res, dict) and res.get("status") != "success"):
                        _all_phones = list((shared or {}).get("phones") or [])
                        _alt_phones = [p for p in _all_phones if p != active_phone]
                        for _alt_ph in _alt_phones[:2]:
                            try:
                                _alt_driver = self._account_driver(_alt_ph)
                                if _alt_driver is None or not self._driver_is_usable(_alt_driver):
                                    continue
                                self._emit_direct(
                                    gui_callback,
                                    f"🎯 Longshot failed on {active_phone} "
                                    f"({_ls_fail_msg[:60] or 'suspended'}) — "
                                    f"trying on {_alt_ph}...")
                                longshot_odds_cap_v2 = float(longshot_odds_cap or 0)
                                _alt_res = self._place_one_bet(
                                    _alt_driver, _alt_ph, password, stake=stake,
                                    visible=cfg["visible"], gui_callback=gui_callback,
                                    board_wide=True,
                                    target_odds_min=longshot_odds_min,
                                    target_odds_max=longshot_odds_max,
                                    odds_cap=longshot_odds_cap_v2 or 2.5,
                                    max_legs=int(longshot_legs),
                                    stake_percent=_gov_stake_percent,
                                    stake_cap=_gov_stake_cap,
                                    min_lead_minutes=_gov_mll,
                                    prefer_more_legs=True,
                                    reserve_pool=0,
                                    jitter_seed=jitter_seed + 1,
                                    no_odds_cap=(longshot_odds_cap_v2 <= 0),
                                    conf_floor=0.0,
                                    researched_only=False)
                                if isinstance(_alt_res, dict) and _alt_res.get("status") == "success":
                                    self._emit_direct(
                                        gui_callback,
                                        f"✅ Longshot placed on {_alt_ph} instead!")
                                    res = _alt_res
                                    # Record against the alt phone — but mark the longshot
                                    # as used for today so we don't double-fire
                                    with self._sched_lock:
                                        _st2 = self._load_sched_state()
                                        _which2 = int(_st2.get("longshot_which") or 1)
                                        if _which2 == 2:
                                            _st2["longshot2_placed_day"] = today
                                        else:
                                            _st2["longshot_placed_day"] = today
                                        _st2.pop("longshot_which", None)
                                        self._save_sched_state(_st2)
                                    self._record_bet_from_result(_alt_res, phone=_alt_ph)
                                    _alt_tried = True
                                    break
                            except Exception:
                                continue
                    # If alt account also failed, fall through to normal smart bet
                    if not _alt_tried and not (isinstance(res, dict) and res.get("status") == "success"):
                        lo, hi = self._bandit_target_range(
                            self._gov('target_odds_min', 5.0),
                            self._gov('target_odds_max', 6.0))
                        res = self._place_one_bet(driver, active_phone, password, stake=stake,
                                                  visible=cfg["visible"],
                                                  gui_callback=gui_callback,
                                                  target_odds_min=lo, target_odds_max=hi,
                                                  odds_cap=_gov_oc,
                                                  max_legs=max_legs,
                                                  min_legs=min_legs,
                                                  conf_floor=conf_floor,
                                                  stake_percent=_gov_stake_percent,
                                                  stake_cap=_gov_stake_cap,
                                                  min_lead_minutes=_gov_mll,
                                                  prefer_more_legs=False,
                                                  reserve_pool=0,
                                                  jitter_seed=jitter_seed)
                        want_longshot_eff = False
                status = res.get("status") if isinstance(res, dict) else "error"
                if self._agent_hub is not None:
                    try:
                        self._agent_hub.supervisor.beat_round(self._engine_state, active_phone)
                        self._agent_hub.supervisor.beat_agent("risk")
                    except Exception:
                        pass
                    if isinstance(res, dict) and res.get("balance_unreadable"):
                        try:
                            self._agent_hub.supervisor.beat_balance_unreadable(active_phone)
                        except Exception:
                            pass
                try:
                    self._engine_state.update({
                        "active_phone": active_phone,
                        "last_round_status": status,
                        "last_round_message": str(res.get("message", ""))[:200]
                                             if isinstance(res, dict) else "",
                        "engine_busy": True,
                        "consecutive_failures": consec_fail,
                        "win_funded_wait": False,
                        "period": ("night" if datetime.now().hour >= 18 else "day"),
                    })
                    self._engine_state.setdefault("workers", {})[active_phone] = {
                        "status": status,
                        "round_attempt": attempt,
                        "last_ts": time.time(),
                        "longshot": bool(want_longshot_eff),
                    }
                except Exception:
                    pass
                try:
                    self._engine_state.setdefault("balances", {})[active_phone] = \
                        res.get("balance") if isinstance(res, dict) else None
                except Exception:
                    pass
                if status == "success":
                    login_fail_count = 0
                    dead_until = 0.0
                    no_funds_confirmed_count = 0
                    if self._agent_hub is not None:
                        try:
                            self._agent_hub.supervisor.beat_unparked(active_phone)
                        except Exception:
                            pass
                        try:
                            placed_stake = res.get("stake") if isinstance(res, dict) else stake
                            placed_odds = res.get("odds") if isinstance(res, dict) else 0
                            self._agent_hub.supervisor.beat_bet_placed(
                                active_phone, placed_stake, placed_odds)
                        except Exception:
                            pass
                    if want_longshot_eff:
                        with self._sched_lock:
                            st = self._load_sched_state()
                            _which = int(st.get("longshot_which") or 1)
                            if _which == 2:
                                st["longshot2_placed_day"] = today
                                st.pop("longshot2_pending_ts", None)
                            else:
                                st["longshot_placed_day"] = today
                                st.pop("longshot_pending_ts", None)
                            st.pop("longshot_which", None)
                            self._save_sched_state(st)
                    with self._sched_lock:
                        st = self._load_sched_state()
                        st["bets_placed_today"] = int(st.get("bets_placed_today", 0)) + 1
                        if st.get("date") != today:
                            st["date"] = today
                        # Rich per-number counters (used by the daily cap board).
                        _per_num = st.setdefault("bets_by_number", {})
                        _per_num[str(active_phone)] = int(_per_num.get(str(active_phone), 0)) + 1
                        st["acc_idx"] = 0  # this worker owns exactly one account
                        self._save_sched_state(st)
                    with self._bets_lock:
                        shared["bets_placed"] += 1
                    last_placed_ts = time.time()
                    self._engine_state["last_placed_ts"] = last_placed_ts
                    self._record_bet_from_result(res, phone=active_phone)
                    if self._agent_hub is not None:
                        try:
                            _pwin = (res.get("possible_win") if isinstance(res, dict) else None)
                            self._agent_hub.alert(
                                "bet",
                                f"{'🎯 LONG-SHOT' if want_longshot_eff else '✅ SMART'} bet on "
                                f"{active_phone}: "
                                f"KES {res.get('stake') if isinstance(res, dict) else stake}"
                                f" @ x{res.get('odds') if isinstance(res, dict) else 0:.2f}"
                                + (f" (possible KES {_pwin:,.2f})" if _pwin else ""),
                                gui_callback=gui_callback)
                        except Exception:
                            pass
                    if chain_bets:
                        try:
                            self._backfill_bet_ids(driver, gui_callback=gui_callback)
                        except Exception as e:
                            self._emit_direct(gui_callback,
                                              f"⚠️ ID backfill skip: {str(e)[:80]}")
                        # Research-paced pacing before the next slip build.
                        try:
                            self._research_between_bets(
                                driver, gui_callback=gui_callback,
                                timeout=float(self._gov('research_seconds',
                                                        cfg.get("research_seconds", 60.0))))
                        except Exception as e:
                            self._emit_direct(gui_callback,
                                              f"🔬 research window skip: {str(e)[:80]}")
                    wait = self._gov('chain_gap', chain_gap) if chain_bets else cadence
                    tag = "🎯 LONG-SHOT" if want_longshot_eff else "✅ SMART"
                    daily_now = self._today_placed_for(active_phone, today,
                                                       include_orphans=inc_orph)
                    self._emit_direct(
                        gui_callback,
                        f"{tag} Bet #{shared['bets_placed']} placed on {active_phone} "
                        f"(day {daily_now}/{'∞' if not daily_bets else int(daily_bets)}) — "
                        + (f"spotting more games → next slip after research "
                           f"({chain_gap/60:g} min)" if chain_bets
                           else f"next window in {cadence/60:g} min"))
                    if max_bets and shared["bets_placed"] >= int(max_bets):
                        cap_reached.set()
                        self._engine_busy = False
                        continue
                elif res.get("deposit_needed") if isinstance(res, dict) else None:
                    need = res.get("deposit_needed", 0.0)
                    bal = res.get("balance", 0.0)
                    bal_confirmed_in_round = bool(res.get("balance") and float(res.get("balance") or 0) > 0)
                    self._engine_state["win_funded_wait"] = True
                    waiting_since = waiting_since or time.time()
                    _inner_done = False
                    _shadow_promoted_ok = False
                    while not _inner_done and not _stop():
                        _balance_read_attempted = False
                        _balance_was_confirmed = False
                        _b2 = 0.0
                        if driver is not None and self._driver_is_usable(driver):
                            try:
                                driver.switch_to.window(driver.window_handles[0])
                                self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                                time.sleep(0.8)
                            except Exception:
                                pass
                            try:
                                _b2, _b2c = self._read_balance_confirmed(driver, wait=8.0)
                                _balance_read_attempted = True
                                if _b2c:
                                    _balance_was_confirmed = True
                                    self._balance_cache = getattr(self, "_balance_cache", None) \
                                        or self._load_balance_cache()
                                    self._balance_cache[str(active_phone)] = {
                                        "balance": _b2, "confirmed": True, "ts": time.time()}
                                    self._save_balance_cache()
                                else:
                                    try:
                                        _b2p = self._read_balance_patient(driver, wait=5.0)
                                        if _b2p and _b2p > 0:
                                            _b2 = _b2p
                                            _balance_was_confirmed = True
                                            self._balance_cache = getattr(self, "_balance_cache", None) \
                                                or self._load_balance_cache()
                                            self._balance_cache[str(active_phone)] = {
                                                "balance": _b2, "confirmed": True, "ts": time.time()}
                                            self._save_balance_cache()
                                    except Exception:
                                        pass
                            except Exception:
                                pass
                        if not _balance_was_confirmed:
                            if self._engine_state.pop("_balance_refreshed", False):
                                _ent = self._cached_balance_for(active_phone, allow_stale=True)
                                if _ent and _ent.get("confirmed"):
                                    _b2 = max(0.0, float(_ent.get("balance") or 0))
                                    if _b2 >= stake:
                                        _balance_was_confirmed = True
                                        self._emit_direct(gui_callback,
                                                          f"⚡ {active_phone}: manual balance check "
                                                          f"confirmed KES {_b2:,.2f} — resuming!")
                        if not _balance_was_confirmed:
                            _est, _src = self._est_balance_for(active_phone)
                            if _src != "none" and _est >= stake:
                                _b2 = _est
                        pool_r = self._pool()
                        eff_stake = stake
                        funds_sufficient_now = (
                            (float(_b2) - pool_r) >= eff_stake
                            or (not _balance_was_confirmed and not bal_confirmed_in_round))
                        if funds_sufficient_now and float(_b2) >= eff_stake:
                            no_funds_confirmed_count = 0
                            waiting_since = None
                            self._engine_state["win_funded_wait"] = False
                            self._emit_direct(gui_callback,
                                              f"💵 KES {_b2:,.2f} in {active_phone} covers "
                                              f"KES {eff_stake:,.0f} (reserve KES {pool_r:,.2f}) — GO!")
                            if self._agent_hub is not None:
                                try:
                                    self._agent_hub.supervisor.beat_unparked(active_phone)
                                except Exception:
                                    pass
                            if driver is not None and self._driver_is_usable(driver) and float(_b2) >= eff_stake:
                                _shadow = None
                                try:
                                    _shadows = [
                                        b for b in (getattr(self, "_bets", None) or [])
                                        if b.get("status") == "shadow" and b.get("shadow_legs")
                                    ]
                                    if _shadows:
                                        _shadows.sort(key=lambda x: x.get("placed_at") or "", reverse=True)
                                        _shadow = _shadows[0]
                                except Exception:
                                    _shadow = None
                                if _shadow and _shadow.get("shadow_legs"):
                                    _legs_info = _shadow.get("shadow_legs") or []
                                    self._emit_direct(gui_callback,
                                                      f"⚡ Promoting pre-built shadow slip "
                                                      f"({len(_legs_info)} legs, x{_shadow.get('odds', '?'):.2f})")
                                    _promoted_legs = []
                                    for _lg in _legs_info:
                                        _promoted_legs.append((
                                            float(_lg.get("odds") or 1.5),
                                            str(_lg.get("name") or ""),
                                            str(_lg.get("gid") or ""),
                                            str(_lg.get("market") or "over"),
                                            float(_lg.get("prob") or 0.5),
                                        ))
                                    try:
                                        self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                                        time.sleep(1.2)
                                        self._scroll_to_load_more_games(driver, gui_callback=gui_callback)
                                        _pc = self._click_selected_legs(driver, _promoted_legs, gui_callback=gui_callback)
                                        if _pc >= 2:
                                            _pres = self._open_betslip_and_place(
                                                driver, stake, active_phone, password,
                                                gui_callback=gui_callback, before_balance=_b2,
                                                legs=_promoted_legs)
                                            if isinstance(_pres, bool) and _pres:
                                                _shadow["status"] = "shadow_promoted"
                                                _shadow["settled_at"] = datetime.now().isoformat(timespec="seconds")
                                                self._save_ledger()
                                                self._record_bet_from_result({
                                                    "status": "success",
                                                    "legs": len(_promoted_legs),
                                                    "stake": stake,
                                                    "odds": float(_shadow.get("odds") or 1.5),
                                                    "possible_win": round(stake * float(_shadow.get("odds") or 1.5), 2),
                                                    "markets": _shadow.get("markets") or [],
                                                    "probs": _shadow.get("probs") or [],
                                                    "game_ids": _shadow.get("shadow_game_ids") or [],
                                                    "placed_at": datetime.now().isoformat(timespec="seconds"),
                                                }, phone=active_phone)
                                                self._emit_direct(gui_callback,
                                                                  f"✅ Shadow promoted and placed on {active_phone}!")
                                                with self._bets_lock:
                                                    shared["bets_placed"] += 1
                                                last_placed_ts = time.time()
                                                _shadow_promoted_ok = True
                                    except Exception as _pe:
                                        self._emit_direct(gui_callback,
                                                          f"⚠️ Shadow promotion failed ({str(_pe)[:80]})")
                            _inner_done = True
                            continue
                        if _balance_was_confirmed:
                            no_funds_confirmed_count += 1
                            _backoff_s = max(300.0, float(recheck_wait) * 0.5 if no_funds_confirmed_count >= 2 else 120.0)
                            if no_funds_confirmed_count >= 2:
                                # OWNER RULE (2026-09-23): rest the account for a full
                                # hour when NO FUNDS are confirmed. During that hour we
                                # follow winnings (settle ledger, emit WON/LOST) but place
                                # NO bets. Browser stays open on purpose so the rest-hour
                                # win-sync below can actually read Bet History.
                                _park_s = max(3600.0, float(recheck_wait))
                                self._emit_direct(
                                    gui_callback,
                                    f"🛑 {active_phone}: confirmed NO FUNDS x{no_funds_confirmed_count} "
                                    f"(KES {_b2:,.2f} < KES {eff_stake:,.0f}) — resting this account "
                                    f"for {_park_s / 60:.0f} min: following winnings only, "
                                    "NO bets until funds return. Other accounts continue betting.")
                                dead_until = time.time() + _park_s
                                if self._agent_hub is not None:
                                    try:
                                        self._agent_hub.supervisor.beat_parked(active_phone)
                                    except Exception:
                                        pass
                                _inner_done = True
                                continue
                            else:
                                self._emit_direct(
                                    gui_callback,
                                    f"⏳ {active_phone}: KES {_b2:,.2f} < KES {eff_stake:,.0f} "
                                    f"(confirm #{no_funds_confirmed_count}) — waiting {_backoff_s / 60:.0f} min, "
                                    "one plan-ahead scan, then recheck.")
                                try:
                                    if driver is not None and self._driver_is_usable(driver):
                                        self._plan_ahead(driver, active_phone, password,
                                                         stake=stake, gui_callback=gui_callback)
                                except Exception:
                                    pass
                                _wait_til = time.time() + _backoff_s
                                while time.time() < _wait_til and not _stop():
                                    time.sleep(min(10.0, _wait_til - time.time()))
                                    if self._engine_state.get("_balance_refreshed"):
                                        break
                                _inner_done = True
                                continue
                        else:
                            self._emit_direct(gui_callback,
                                              f"⏳ {active_phone}: balance temporarily unreadable "
                                              f"(KES {bal:,.2f} cached) — quick plan-ahead, then cycling.")
                            try:
                                if driver is not None and self._driver_is_usable(driver):
                                    self._plan_ahead(driver, active_phone, password,
                                                     stake=stake, gui_callback=gui_callback)
                            except Exception:
                                pass
                            _quick_wait = 180.0
                            _wt = time.time() + _quick_wait
                            while time.time() < _wt and not _stop():
                                time.sleep(min(10.0, _wt - time.time()))
                                if self._engine_state.get("_balance_refreshed"):
                                    break
                            _inner_done = True
                            continue
                    if _shadow_promoted_ok:
                        wait = self._gov('chain_gap', chain_gap) if chain_bets else cadence
                        self._engine_busy = False
                        waited = 0.0
                        while waited < wait and not _stop():
                            time.sleep(min(10.0, wait - waited))
                            waited += 10.0
                        continue
                    wait = retry
                else:
                    wait = retry
                    msg = (res.get("message") or "") if isinstance(res, dict) else ""
                    if not str(msg).strip():
                        # An unexplained empty reason is the worst kind of log
                        # line: the operator sees "no bet this round ()" and
                        # cannot tell a deliberate decline from a silent fault.
                        # Report the truth rather than inventing a cause.
                        _st = (res.get("status") if isinstance(res, dict) else "") or "unknown"
                        _keys = sorted(res.keys()) if isinstance(res, dict) else []
                        msg = (f"declined by the risk layer, no reason given "
                               f"(status={_st}, keys={_keys}) — no bet placed")
                        self._emit_direct(
                            gui_callback,
                            f"⚠️ {active_phone}: {msg}")
                    self._emit_direct(gui_callback,
                                      f"⏭️ {active_phone}: no bet this round "
                                      f"({str(msg)[:90]}) — re-crawling in {retry:g}s")
                    # A HEALTHY DECLINE IS NOT A FAILURE (2026-09-27).
                    # The portfolio gates (drawdown halt, correlation, Kelly,
                    # recipe veto) and thin-board "no qualifying combination"
                    # returns deliberately decline without touching the browser.
                    # Those all reported "aborted", so the supervisor counted
                    # ordinary quiet rounds as a broken session and tore down and
                    # rebuilt drivers every few minutes (18+/hour) — manufacturing
                    # the selenium instability it was warning about, and burying
                    # the real state in hundreds of warnings. Only genuine
                    # technical failures count as aborts.
                    _declined = bool(isinstance(res, dict) and (
                        res.get("skipped") or res.get("circuit_breaker")
                        or res.get("correlation_blocked") or res.get("kelly_blocked")
                        or res.get("recipe_vetoed")))
                    if _declined:
                        try:
                            if self._agent_hub is not None:
                                self._agent_hub.supervisor.note_skip(str(msg)[:90])
                        except Exception:
                            pass
                        # A deliberate decline means the round completed cleanly,
                        # so it clears any genuine abort streak accumulated earlier.
                        if status == "aborted" and self._agent_hub is not None:
                            try:
                                self._agent_hub.supervisor.clear_aborts(
                                    f"round declined cleanly: {str(msg)[:70]}")
                            except Exception:
                                pass
                    elif status == "aborted" or status == "error":
                        if self._agent_hub is not None:
                            try:
                                self._agent_hub.supervisor.beat_abort(str(msg)[:90])
                            except Exception:
                                pass
                # Win monitoring: settle ledger entries after a bet AND periodically.
                if status == "success" or (time.time() - last_sync) >= monitor:
                    try:
                        self._monitor_and_sync_winnings(driver, gui_callback=gui_callback)
                        last_sync = time.time()
                    except Exception as e:
                        self._emit_direct(gui_callback, f"⚠️ Win-sync hiccup: {str(e)[:100]}")
                # Daily auto-withdraw (this account, once per day, own session).
                if auto_withdraw:
                    try:
                        self._maybe_auto_withdraw(active_phone, password, withdraw_amount,
                                                  gui_callback=gui_callback)
                    except Exception as e:
                        self._emit_direct(gui_callback,
                                          f"⚠️ Auto-withdraw skip: {str(e)[:80]}")
            except Exception as exc:
                _exc_s = str(exc).lower()
                _is_net = ("err_internet_disconnected" in _exc_s or "err_name_not_resolved" in _exc_s
                           or "err_connection" in _exc_s or "net::err_" in _exc_s)
                _is_renderer = ("timed out receiving message from renderer" in _exc_s
                                or "timeout: timed out" in _exc_s)
                # Network down — keep browser, just wait for net to return
                if _is_net:
                    self._emit_direct(gui_callback,
                                      f"🌐 {active_phone} offline (net down) — keeping browser, "
                                      "retrying in 60s until net returns.")
                    consec_fail = max(0, consec_fail - 1)  # don't penalise net blips
                    self._engine_state["consecutive_failures"] = consec_fail
                    if self._agent_hub is not None:
                        try:
                            self._agent_hub.supervisor.beat_abort(f"net down: {str(exc)[:60]}")
                        except Exception:
                            pass
                    self._engine_busy = False
                    # keep driver alive — don't quit
                    wait = 60.0
                elif _is_renderer:
                    consec_fail += 1
                    self._engine_state["consecutive_failures"] = consec_fail
                    try:
                        import traceback as _tb
                        _crash_body = "".join(_tb.format_exception(type(exc), exc, exc.__traceback__))
                        _crash_file = writable_path("sportsape_crash_trace.txt")
                        with open(_crash_file, "a", encoding="utf-8") as _cf:
                            _cf.write(f"[{datetime.now().isoformat(timespec='seconds')}] "
                                      f"{active_phone} renderer hang (fail #{consec_fail})\n{_crash_body}\n")
                    except Exception:
                        _crash_body = ""
                    self._emit_direct(gui_callback,
                                      f"🔧 {active_phone} renderer hang (45s) — rebuilding browser "
                                      f"(fail #{consec_fail})"
                                      + (f" → trace saved" if _crash_body else ""))
                    if self._agent_hub is not None:
                        try:
                            self._agent_hub.supervisor.beat_driver_heal()
                        except Exception:
                            pass
                    self._quit_bet_driver(driver)
                    driver = None
                    self._clear_account_driver(active_phone)
                else:
                    consec_fail += 1
                    self._engine_state["consecutive_failures"] = consec_fail
                    try:
                        import traceback as _tb
                        _crash_body = "".join(_tb.format_exception(type(exc), exc, exc.__traceback__))
                        _crash_file = writable_path("sportsape_crash_trace.txt")
                        with open(_crash_file, "a", encoding="utf-8") as _cf:
                            _cf.write(f"[{datetime.now().isoformat(timespec='seconds')}] "
                                      f"{active_phone} round crash (fail #{consec_fail})\n{_crash_body}\n")
                    except Exception:
                        _crash_body = ""
                    self._emit_direct(gui_callback,
                                      f"⚠️ {active_phone} round crashed: {str(exc)[:120]} "
                                      f"(fail #{consec_fail})"
                                      + (f" → full trace saved to sportsape_crash_trace.txt"
                                         if _crash_body else ""))
                    if self._agent_hub is not None:
                        try:
                            self._agent_hub.supervisor.beat_abort(f"crash: {str(exc)[:90]}")
                        except Exception:
                            pass
                    self._quit_bet_driver(driver)
                    driver = None
                    self._clear_account_driver(active_phone)
                self._engine_busy = False
                # keep 60s for net blips even when consec_fail low
                if _is_net:
                    wait = 60.0
                else:
                    wait = 60.0 if consec_fail >= 4 else retry
                if consec_fail >= 4 and not _is_net:
                    self._emit_direct(
                        gui_callback,
                        f"🌐 {active_phone}: no connection or browser trouble — staying on, "
                        "retrying every 60s until the network is back.")
            finally:
                try:
                    lock.release()
                except Exception:
                    pass
            # Interruptible wait that honours the kill switch / cap signal.
            self._engine_busy = False
            waited = 0.0
            while waited < wait:
                if _stop():
                    break
                time.sleep(min(5.0, wait - waited))
                waited += 5.0
        # Worker teardown: close its own browser and drop the registry entry.
        if driver is not None:
            try:
                self._quit_bet_driver(driver)
            except Exception:
                pass
        self._clear_account_driver(active_phone)
        self._engine_busy = False
        self._emit_direct(gui_callback,
                          f"⏹️ {active_phone} worker stopped (run total "
                          f"{shared['bets_placed']} bets).")

    def force_stop_bet_driver(self):
        """Hard-kill every per-account worker's browser (GUI emergency stop)."""
        self._close_all_account_drivers()
        # Legacy single-session pointer, if any, for code that still touches it.
        try:
            if getattr(self, "_bet_driver", None) is not None:
                self._bet_driver.quit()
        except Exception:
            pass
        self._bet_driver = None

    def _quit_bet_driver(self, driver):
        """Quit a bet-session browser and clean its temp profile (idempotent, never throws).

        LEAK FIX (2026-10-05): `driver.quit()` is best-effort and SILENTLY FAILS
        when the driver session has already died — which is exactly what happens
        after a chromedriver crash ("invalid session id" / HTTPConnectionPool).
        The Chrome it launched then keeps running with its profile open, so every
        crash-and-rebuild left another live browser behind. Measured live: 3 Chrome
        profiles for 2 accounts and 53% CPU. Deleting the profile directory also
        fails while Chrome holds it, so we now kill the browser by its own
        profile marker as a guaranteed backstop.
        """
        temp_profile = None
        try:
            if driver is not None:
                temp_profile = getattr(driver, "_sportsape_temp_profile", None)
                acct = getattr(driver, "_sportsape_account", None)
                # ORDER MATTERS (2026-10-05). If the chromedriver process has
                # already died, `driver.quit()` BLOCKS: it opens an HTTP
                # connection to a dead socket and retries until it gives up —
                # which is how one crashed driver froze the engine for 28
                # minutes ("opening stable browser session" then total silence).
                # Probe the process FIRST and skip quit() for a corpse, going
                # straight to the profile-scoped kill below.
                _alive = True
                try:
                    _proc = getattr(getattr(driver, "service", None), "process", None)
                    if _proc is not None and callable(getattr(_proc, "poll", None)):
                        _alive = _proc.poll() is None
                except Exception:
                    _alive = True
                if _alive:
                    try:
                        driver.quit()
                    except Exception:
                        pass
                else:
                    self._emit_direct(
                        None,
                        "   chromedriver had already exited — skipping driver.quit() "
                        "and clearing the browser by its profile instead.")
                if acct:
                    try:
                        _release_account_session(acct)
                        driver._sportsape_account = None
                    except Exception:
                        pass
                with self._active_drivers_lock:
                    self._active_drivers.discard(driver)
        except Exception:
            pass
        if getattr(self, "_bet_driver", None) is driver:
            self._bet_driver = None
        # Backstop: if quit() failed the browser is very likely still alive.
        # Kill anything still using OUR temp profile before deleting it.
        if temp_profile:
            try:
                _kill_chrome_for_profile(temp_profile)
            except Exception:
                pass
            try:
                if os.path.exists(temp_profile):
                    shutil.rmtree(temp_profile, ignore_errors=True)
            except Exception:
                pass

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
        key = (round(float(p1), 4), round(float(pd), 4), round(float(p2), 4))
        cached = self._fit_poisson_cache.get(key)
        if cached is not None:
            return cached
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
            self._fit_poisson_cache[key] = None
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
        self._fit_poisson_cache[key] = (lh, la)
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

    def _poisson_over_under(self, lam_total, line=2.5):
        """P(total > line) for a Poisson total-goal model with expected lam_total."""
        import math
        k_max = int(max(3, lam_total + 8))
        p_gt = 0.0
        for k in range(k_max + 1):
            if k > line:
                p_gt += math.exp(-lam_total) * (lam_total ** k) / math.factorial(k)
        return p_gt

    def _calibrated_goals_probs(self, g, h3_probs, ou_probs):
        """Calibrate the goals-market probabilities with a real O/U line.

        2026-09-24 (#5): the 2.5-line probability already comes from the book's
        own O/U line (the strongest single source). The Poisson fit to the 1X2
        odds adds the SHAPE — it rescales 1X2-derived goals to the book's total-
        goals line, then derives a consistent Over/Under 1.5 probability. When
        no real 1.5 line exists on the listing, the model still yields one;
        when it does, the two independent estimates get blended 50/50 so no
        single listing glitch warps the leg probability.

        Returns {"over25": p, "under25": p, "over15": p, "under15": p} or None
        when there is nothing to calibrate."""
        try:
            if not ou_probs or float(ou_probs[0] or 0) <= 0.03:
                return None
            p_over25_book = float(ou_probs[0])
            lam_total = self._total_goals_from_ou(p_over25_book)
            p_over15_cal = self._poisson_over_under(lam_total, 1.5)
            p_over25_cal = self._poisson_over_under(lam_total, 2.5)
            # Optionally use the 1X2 Poisson fit as a second estimate on the 1.5 line
            if len(h3_probs) >= 3 and all(float(x or 0) > 0.01 for x in h3_probs):
                try:
                    fit = self._fit_poisson(float(h3_probs[0]), float(h3_probs[1]),
                                            float(h3_probs[2]))
                    if fit:
                        lh, la = fit
                        tot = lh + la
                        if tot > 0.1:
                            lh = lh / tot * lam_total
                            la = la / tot * lam_total
                            p15_h2 = self._poisson_over_under(lh + la, 1.5)
                            p_over15_cal = 0.5 * p_over15_cal + 0.5 * p15_h2
                except Exception:
                    pass
            p_over15_cal = max(0.02, min(0.98, p_over15_cal))
            return {
                "over25": p_over25_book,
                "under25": 1.0 - p_over25_book,
                "over15": p_over15_cal,
                "under15": 1.0 - p_over15_cal,
            }
        except Exception:
            return None

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

    def _analyze_event(self, ev, games=None, form=None):
        """One game's prediction: fair odds -> Poisson fit -> Monte-Carlo outcome odds,
        cross-checked with the crawled Over/Under market, optionally tilted by the
        searched team form (W/D/L streaks), plus a draw floor and a favourite-commitment
        clamp so single legs never become reckless 1.05 shots."""
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
            fw = float((form or {}).get("weight") or 0)
            if lh > 0.1 and la > 0.1 and fw > 0 and (form or {}).get("home_adv") is not None:
                adv = min(1.0, max(-1.0, float(form.get("home_adv") or 0.0)))
                shift = min(0.20, abs(fw * adv * 0.5))  # bounded form tilt on the model lambda
                lh = max(0.2, lh * (1 + shift * (1.0 if adv > 0 else -1.0)))
                la = max(0.2, la * (1 - shift * (1.0 if adv > 0 else -1.0)))
                H, D, A = self._poisson_score_outcomes(lh, la)
        H = 0.62 * H + 0.38 * p1
        D = 0.62 * D + 0.38 * pd
        A = 0.62 * A + 0.38 * p2
        D = max(D, 0.235)
        _gid = str(ev.get("match_id") or ev.get("id") or "")
        _home_n = str(ev.get("home") or "")
        _away_n = str(ev.get("away") or "")
        _ev_enr = None
        try:
            _ev_enr = self._enrichment_for(_gid) if _gid else None
        except Exception:
            _ev_enr = None
        if _ev_enr and (_ev_enr.get("injuries") or _ev_enr.get("suspensions")):
            _inj = " ".join(_ev_enr.get("injuries") or []) + " " + " ".join(_ev_enr.get("suspensions") or [])
            _low = _inj.lower()
            if _home_n and any(w for w in _home_n.split() if len(w) > 3 and w.lower()[:5] in _low):
                _cut = min(0.08, max(H, 0.04) * 0.18)
                H = max(0.02, H - _cut)
                D += _cut * 0.40
                A += _cut * 0.60
            if _away_n and any(w for w in _away_n.split() if len(w) > 3 and w.lower()[:5] in _low):
                _cut = min(0.08, max(A, 0.04) * 0.18)
                A = max(0.02, A - _cut)
                D += _cut * 0.40
                H += _cut * 0.60
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
        fmeta = {}
        if form is not None and (form or {}).get("weight"):
            fmeta = {"form_adv": (form or {}).get("home_adv"),
                     "form_weight": (form or {}).get("weight")}
        return {"order": ev.get("order"),
                "home": ev.get("home", ""), "away": ev.get("away", ""),
                "pick": pick, "conf": round(conf, 4),
                "probs": [round(H, 4), round(D, 4), round(A, 4)],
                "odds": [round(o1, 2), round(ox, 2), round(o2, 2)],
                "match_id": ev.get("match_id", ""), "form": fmeta or None}

    def _analyze_jackpot_pool(self, pool, driver=None, gui_callback=None, form_budget=8):
        picks = []
        form_map = self._form_snapshot_map(pool, driver=driver, gui_callback=gui_callback,
                                           budget=form_budget)
        for idx, ev in enumerate(pool.get("events") or []):
            form = None
            if isinstance(form_map, dict):
                form = form_map.get(idx) or form_map.get(ev.get("order")) or None
            r = self._analyze_event(ev, games=getattr(self, "_last_crawled_games", None), form=form)
            if r is not None:
                picks.append(r)
        return picks

    # ── Team-form lookup (search box, defensively crawled + cached) ──────
    def _form_team_key(self, name: str) -> str:
        return re.sub(r"[^a-z0-9]", "", (name or "").lower())

    def _load_form_cache(self) -> dict:
        """Return the LIVE form-cache dict (never a copy).

        BUGFIX (2026-10-05): this used to end with `return cache or {}`. When
        the cache was empty — which is exactly the state on a fresh install —
        `{}` is falsy, so the method returned a NEW throwaway dict instead of
        the stored one. Callers then mutated that throwaway and
        _cache_form_entry reported success while persisting NOTHING. The file
        stayed at 0 teams forever, so the analyst always received "Form data
        is absent" and skipped all 338 games, and the form/lineup/similar-
        opponent factors were permanently inert.

        We now always return the real container so in-memory writes stick, and
        we normalise a malformed file into a usable dict instead of dropping it.
        """
        cache = getattr(self, "_form_cache_data", None)
        if cache is None:
            cache = {}
            try:
                if self.FORM_CACHE_PATH.exists():
                    raw = json.loads(self.FORM_CACHE_PATH.read_text(encoding="utf-8"))
                    if isinstance(raw, dict):
                        teams = raw.get("teams")
                        if isinstance(teams, dict):
                            cache = teams
            except Exception:
                cache = {}
            self._form_cache_data = cache
        elif not isinstance(cache, dict):
            cache = {}
            self._form_cache_data = cache
        return cache

    def _save_form_cache(self):
        try:
            self.FORM_CACHE_PATH.write_text(
                json.dumps({"teams": self._load_form_cache() or {}}, ensure_ascii=False),
                encoding="utf-8")
            return True
        except Exception:
            return False

    def _fresh_form(self, team: str):
        """Return cached {'results','n','ts'} for a team if still fresh, else None."""
        cache = self._load_form_cache()
        entry = cache.get(self._form_team_key(team))
        if not entry:
            return None
        if time.time() - (entry.get("ts") or 0) > self.FORM_TTL_SECONDS:
            return None
        n = max(0, int(entry.get("n") or 0))
        if n < 3:
            return None
        return entry

    def _load_enrich_cache(self) -> dict:
        """Persistent per-game enrichment (injuries, weather, venue...). keyed by game id."""
        try:
            if self.ENRICH_PATH.exists():
                data = json.loads(self.ENRICH_PATH.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    return data
        except Exception:
            pass
        return {}

    def _save_enrich_cache(self):
        try:
            self.ENRICH_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.ENRICH_PATH.write_text(
                json.dumps(getattr(self, "_enrich_cache", {}), indent=2), encoding="utf-8")
        except Exception:
            pass

    def _enrichment_for(self, game_id) -> dict | None:
        """Return fresh enrichment for a game id, or None."""
        if not game_id:
            return None
        cache = getattr(self, "_enrich_cache", None)
        if cache is None:
            cache = self._load_enrich_cache()
            self._enrich_cache = cache
        ent = cache.get(str(game_id))
        if not ent or not isinstance(ent, dict):
            return None
        if time.time() - (float(ent.get("ts") or 0)) > self.ENRICH_TTL_SECONDS:
            return None
        if not (ent.get("injuries") or ent.get("suspensions")
                or ent.get("weather") or ent.get("raw_snippet")
                or ent.get("lineups") or ent.get("formations")):
            return None
        return ent

    def _set_enrichment(self, game_id, enr: dict):
        if not game_id or not enr:
            return
        try:
            cache = getattr(self, "_enrich_cache", None)
            if cache is None:
                cache = self._load_enrich_cache()
                self._enrich_cache = cache
            cache[str(game_id)] = dict(enr, ts=time.time())
            self._save_enrich_cache()
        except Exception:
            pass

    @staticmethod
    def _lineup_formation_k(el: dict, market: str = "") -> float:
        """Multiplier in [0.88, 1.06] from confirmed XI + formation (2026-10-05).

        OWNER REQUEST: weight injuries, lineups and formations heavily. A
        CONFIRMED starting XI is one of the strongest pre-match signals
        available, because it tells us the actual attacking and defensive
        shape rather than the season-long average.

        Deliberately conservative and evidence-weighted:
          * a confirmed full XI (>= 9 named players) is worth a real lift,
            scaled by how much of it we can parse;
          * a recognised formation is worth a small lift, and an ATTACKING
            shape (3-4-3 / 4-3-3 / 4-2-3-1) is lifted only for goal markets
            while a defensive one is trimmed there;
          * a lineup we only partially parsed yields proportionally less;
          * no data at all is exactly neutral (1.0) — absence of a lineup is
            NOT evidence of weakness, and must never silently punish a game.
        """
        if not el:
            return 1.0
        k = 1.0
        lineups = el.get("lineups") or {}
        forms = el.get("formations") or {}
        mk = str(market or "").lower()

        # How much of a full XI do we actually have, per side?
        named = 0.0
        for side in ("home", "away"):
            n = len(lineups.get(side) or [])
            if n >= 9:
                named += 1.0
            elif n >= 5:
                named += 0.5
        if named >= 2:
            k *= 1.06          # both XIs confirmed
        elif named >= 1:
            k *= 1.03# one confirmed
        elif named > 0:
            # A partial XI (only a handful of names parsed) is weaker evidence
            # and must earn proportionally less than a confirmed one — but it is
            # still evidence, so it must not round away to exactly neutral.
            k *= 1.0 + 0.03 * named

        # Formation read, applied only where it is actually informative.
        if forms:
            atk = ("4-3-3", "3-4-3", "4-2-3-1", "3-2-4-1", "4-1-2-1-2")
            defn = ("5-3-2", "5-4-1", "4-5-1", "3-5-2", "5-2-3")
            _goal_market = mk.startswith(("over", "under", "btts"))
            f_home = str(forms.get("home") or "")
            f_away = str(forms.get("away") or "")
            if _goal_market:
                # Attacking shape at both ends -> goals more likely.
                if f_home in atk and f_away in atk:
                    k *= 1.05
                elif (f_home in defn) or (f_away in defn):
                    k *= 0.93
            else:
                # 1X2 / DC: shape alone is weak evidence, keep it gentle.
                if f_home in atk and f_away in defn:
                    k *= 1.02
        return max(0.88, min(1.06, k))

    @staticmethod
    def _split_enrichment_sides(content: str, home_hint: str = "",
                                away_hint: str = "") -> dict:
        """Split a stats-overlay dump into a HOME block and an AWAY block.

        Lineups and formations are PER-SIDE facts, so they cannot be read from
        the overlay as one blob. We look, in order of reliability, for:
          1. an explicit "Home" / "Away" label,
          2. the away team name appearing as its own heading line,
          3. a fallback that returns the whole text for 'home' and nothing for
             'away' (never fabricate a second identical side).

        Returning only one side is deliberate and safe: a single-sided XI is
        still signal, whereas a duplicated one is actively misleading.
        """
        out = {"home": "", "away": ""}
        if not content:
            return out
        home_hint = str(home_hint or "").strip()
        away_hint = str(away_hint or "").strip()

        # 1) explicit Home/Away labels
        mh = re.search(r"^\s*home(?:\s+team)?\s*:?\s*$", content,
                       re.IGNORECASE | re.MULTILINE)
        ma = re.search(r"^\s*away(?:\s+team)?\s*:?\s*$", content,
                       re.IGNORECASE | re.MULTILINE)
        if mh and ma and ma.start() > mh.start():
            out["home"] = content[mh.end():ma.start()]
            out["away"] = content[ma.end():]
            return out

        # 2) away team name as its own line (the usual single-XI layout:
        #    home XI first, then the away heading, then the away XI)
        if away_hint:
            pat = r"^\s*" + re.escape(away_hint) + r"\s*$"
            ma = re.search(pat, content, re.IGNORECASE | re.MULTILINE)
            if ma:
                out["home"] = content[:ma.start()]
                out["away"] = content[ma.end():]
                return out

        # 3) best effort: split on the away name appearing anywhere as a line
        if home_hint and away_hint:
            idx = content.lower().find(away_hint.lower())
            if idx > 0:
                out["home"] = content[:idx]
                out["away"] = content[idx:]
                return out

        out["home"] = content
        return out

    @staticmethod
    def _parse_enrichment_from_text(content: str, home_hint: str = "",
                                    away_hint: str = "") -> dict:
        """Extract injuries/suspensions/weather/venue/referee from a Betradar
        stats-overlay text dump. Shared by the per-leg stats reader and the
        research enrichment path so both keep the same findings."""
        result = {}
        if not content:
            return result
        low = content.lower()
        snippet = content[:600]
        inj_lines = []
        # FALSE-POSITIVE GUARD (2026-10-05). The old matcher fired on any line
        # containing "out " / "missing" / "injury", which swept in overlay
        # CHROME such as competition names ("Australia Cup, Knockout Stage",
        # "U23 AFC Asian Cup, Knockout stage") and — worst of all — the literal
        # string "No missing players". The result was 5-6 phantom "injury flags"
        # on ordinary games, which then tripped _enrichment_veto and vetoed the
        # whole fixture. Verified live: games were skipped for "6 injury flags"
        # that were purely competition labels.
        #
        # A real injury line names a PERSON and a PROBLEM. We now require an
        # explicit absence keyword AND a player-shaped name AND that the line is
        # not a competition/stage/venue label AND does not deny any absence.
        _ABSENCE_KW = ("injured", "injury", "injuries", "suspension",
                       "suspended", "unavailable", "ruled out", "out for",
                       "doubtful", "misses", "missed", "absent")
        _NEGATIVE = ("no missing players", "no injuries", "no suspensions",
                     "none missing", "no missing", "squad fully available",
                     "no players missing", "full squad", "no injury",
                     "no suspension", "fit and available")
        _BOILERPLATE = ("cup,", "stage", "league,", "round", "group ",
                        "knockout", "playoff", "qualif", "friendly",
                        "relegation", "championship", "premier league,")

        def _player_shaped(line: str) -> bool:
            return len(re.findall(r"\b[A-Z][a-zA-Z'.-]{1,}\b", line)) >= 2

        _seen_inj = set()
        for line in content.splitlines():
            l = line.strip()
            low = l.lower()
            if not (5 < len(l) < 150):
                continue
            if any(n in low for n in _NEGATIVE):
                continue                    # explicitly DENIES any absence
            if not any(k in low for k in _ABSENCE_KW):
                continue
            if any(b in low for b in _BOILERPLATE):
                continue                    # competition / stage label
            if not _player_shaped(l):
                continue                    # no person named -> not an injury
            if l in _seen_inj:
                continue                    # overlay repeats a line per column
            _seen_inj.add(l)
            inj_lines.append(l)
        if inj_lines:
            result["injuries"] = inj_lines[:6]
        for pat in (r"weather[:\s]+([^\n]{3,60})",
                    r"(sunny|cloudy|rain|wind|snow|clear|overcast)[^\n]{0,40}"):
            m = re.search(pat, content, re.IGNORECASE)
            if m:
                result["weather"] = m.group(0).strip()[:80]
                break
        for pat in (r"venue[:\s]+([^\n]{3,60})",
                    r"stadium[:\s]+([^\n]{3,60})"):
            m = re.search(pat, content, re.IGNORECASE)
            if m:
                result["venue"] = m.group(1).strip()[:60]
                break
        m = re.search(r"referee[:\s]+([^\n]{3,50})", content, re.IGNORECASE)
        if m:
            result["referee"] = m.group(1).strip()[:50]
        # ── LINEUPS / FORMATIONS (2026-10-05, owner request) ────────────
        # Parsed from the SAME stats-overlay text we already fetch, so this
        # costs no extra page load and no extra API call. SportPesa's overlay
        # renders the probable XI and the formation (4-3-3, 4-4-2, 3-5-2 ...)
        # for each side when the bookmaker publishes them.
        # Split the overlay into per-team regions so each side gets ITS OWN
        # XI and formation. A single shared regex matched the first block for
        # both sides, so home and away were always identical — which is worse
        # than useless, because it looks like real data.
        # Team headings in these overlays are the two team names on/near the
        # title line, or explicit "Home"/"Away" labels.
        _blocks = SportsapeBackend._split_enrichment_sides(
            content, home_hint, away_hint)
        for side, blk in _blocks.items():
            if not blk:
                continue
            # Formation for THIS side.
            fm = re.search(
                r"(?:formation|setup|system)\s*[:\-]?\s*(\d-\d-\d(?:-\d)?)",
                blk, re.IGNORECASE)
            if not fm:
                fm = re.search(r"^\s*(\d-\d-\d(?:-\d)?)\s*$", blk,
                               re.IGNORECASE | re.MULTILINE)
            if fm:
                result.setdefault("formations", {})[side] = fm.group(1)
            # Probable XI for THIS side, taken from the block that follows the
            # XI/Team-News heading up to the next heading.
            xi = re.search(
                r"(?:starting\s*xi|probable\s*(?:xi|lineup)|team\s*news|line\s*up)"
                r"[^\n]{0,40}\n((?:[^\n]*\n){0,16})",
                blk, re.IGNORECASE)
            seg = xi.group(1) if xi else blk
            names = []
            _team_words = set()
            for hint in (home_hint, away_hint):
                for w in re.split(r"[^A-Za-z]+", str(hint or "")):
                    if len(w) >= 3:
                        _team_words.add(w.lower())
            for ln in seg.splitlines():
                ln = ln.strip()
                if not ln or len(ln) < 3 or len(ln) > 60:
                    continue
                if re.match(r"^(form|rating|odds|venue|weather|referee|coach|"
                            r"injury|suspension|past|head|h2h|overall|formation|"
                            r"starting|probable|team\s*news)", ln, re.IGNORECASE):
                    continue
                if not re.search(r"[A-Za-z]{2}", ln):
                    continue
                # A bare team name is a heading, not a player.
                words = [w for w in re.split(r"[^A-Za-z]+", ln) if len(w) >= 3]
                if words and all(w.lower() in _team_words for w in words):
                    continue
                names.append(ln)
                if len(names) >= 11:
                    break
            if names:
                result.setdefault("lineups", {})[side] = names
        result["raw_snippet"] = snippet
        return result

    @staticmethod
    def _enrichment_k(el: dict, home_n: str = "", away_n: str = "") -> float:
        """Score a game's enrichment into a multiplier applied to its legs.

        Injury/suspension noise genuinely trims a game: each distinct injury line
        costs ~6% (capped), a named-side hit costs ~8% more. Returns a float in
        [0.70, 1.0] — real signal, not a cosmetic -0.05."""
        if not el:
            return 1.0
        inj = el.get("injuries") or []
        sus = el.get("suspensions") or []
        con = " ".join(inj) + " " + " ".join(sus)
        if not con.strip():
            return 1.0
        n_inj = len(inj)
        k = 1.0 - min(0.20, 0.06 * float(n_inj))   # each injury line ~6%, capped 20%
        low = con.lower()
        if home_n:
            if any(w for w in (home_n or "").split() if len(w) > 3 and w.lower()[:5] in low):
                k -= 0.08
        if away_n:
            if any(w for w in (away_n or "").split() if len(w) > 3 and w.lower()[:5] in low):
                k -= 0.08
        return max(0.70, k)

    @staticmethod
    def _enrichment_veto(el: dict) -> str | None:
        """Return a human reason to DROP this game entirely (skip every leg), or
        None when the game is clear. A game with several injuries/suspensions or a
        stated key-absence is not a value bet — it's a donation."""
        if not el:
            return None
        inj = el.get("injuries") or []
        sus = el.get("suspensions") or []
        lines = inj + sus
        if len(lines) >= 3:
            return f"{len(lines)} injury/suspension flags"
        low = " ".join(lines).lower()
        for kw in ("out for", "ruled out", "sidelined", "long-term", "season",
                   "top scorer", "key player", "captain", "first choice", "doubtful"):
            if kw in low:
                return f"key absence: {kw}"
        return None

    def _cache_form_entry(self, team: str, entry: dict):
        """Persist a freshly researched form entry for one team (extends TTL)."""
        try:
            cache = self._load_form_cache()
            cache[self._form_team_key(team)] = dict(entry, ts=time.time())
            self._save_form_cache()
            return True
        except Exception:
            return False

    def _search_input(self, driver, reveal=True):
        """Locate the site's search box. On sportpesa the box is hidden behind a
        header 'Search' link (next to Help / the live clock) — clicking it slides
        the input in. reveal tries that first when no input is visible."""
        out = self._find_search_input(driver)
        if out is not None or not reveal:
            return out
        try:
            self._reveal_site_search(driver)
            time.sleep(1.6)
        except Exception:
            return None
        return self._find_search_input(driver)

    def _reveal_site_search(self, driver):
        """Click the header 'Search' trigger so the input panel appears."""
        js = r"""
var rows = document.querySelectorAll('a, span, button, div, i');
var best = null;
for (var i = 0; i < rows.length; i++) {
    var el = rows[i];
    var t = (el.innerText || '').trim();
    if (t.toLowerCase() === 'search') {
        if (el.offsetParent === null) continue;
        if (best === null || el.getBoundingClientRect().width < best.width) {
            best = {el: el, width: el.getBoundingClientRect().width, tag: el.tagName};
        }
    }
}
if (!best) return 'notext';
try { best.el.scrollIntoView({block: 'center'}); best.el.click(); return 'clicked:' + best.tag; }
catch (err) { return 'err:' + err; }
"""
        try:
            return driver.execute_script(js)
        except Exception:
            return 'jserr'

    def _find_search_input(self, driver):
        cands = [
            "input[type='search']",
            "input[type='text'][placeholder*='Search' i]",
            "input[placeholder*='Search' i]",
            "input[name='q']",
            "input[id*='search' i]",
            "[class*='search'] input",
            "input[placeholder*='search' i]",
        ]
        for sel in cands:
            try:
                els = driver.find_elements(By.CSS_SELECTOR, sel)
                for e in els:
                    try:
                        if e.is_displayed() and e.is_enabled():
                            if e.tag_name.lower() == "input":
                                return e
                    except Exception:
                        continue
            except Exception:
                continue
        return None

    def _form_sequence_from_text(self, text: str):
        """Find a run of ≥3 W/D/L letters (team form badges) in raw dropdown text.
        Handles both 'WWDLW' and spaced/cell-separated 'W D L W L' badges."""
        if not text:
            return None
        collapsed = re.sub(r"[\s.\u00b7-]+", "", text)
        runs = re.findall(r"[WDL]{2,12}", collapsed, flags=re.IGNORECASE)
        best = None
        for run in runs:
            if len(run) < 3:
                continue
            # Prioritise longer, then highest D-content (draws are magnetism)
            score = (len(run), run.count("D"))
            if best is None or score > best[0]:
                best = (score, run)
        if best is None:
            return None
        return best[1]

    def _search_team_form(self, driver, team: str, gui_callback=None) -> dict:
        """Full team-form lookup for ONE team: search the site search box to
        surface the team's match, open the Statistics / H2H (Betradar) overlay,
        read the Overall Form rating + W/D/L run and cache it.

        Every failure degrades to None (odds-only model keeps running) and saves
        a forensic dump. Best effort: never raises."""
        team = (team or "").strip()
        key = self._form_team_key(team)
        if not key:
            return None
        fresh = self._fresh_form(team)
        if fresh:
            return dict(fresh, team=team)
        try:
            # find the match via the search box, then open its stats overlay
            row = self._surface_team_row(driver, team)
            if row is None:
                self._dump_ctx(driver, f"form_team_row_not_found_{team[:12].replace(' ', '_')}",
                               extra="outer")
                self._emit_direct(gui_callback,
                                  f"🔍 Form lookup: no match found for '{team}' — "
                                  "odds-only model stays active.")
                return None
            clicked, windows = self._row_stats_icon_click(driver, team)
            if not clicked:
                self._dump_ctx(driver, f"form_stats_icon_missing_{team[:12].replace(' ', '_')}",
                               extra="inner")
                return None
            text = self._read_overlay_text(driver, windows, timeout=10)
            if not text:
                return None
            parsed = self._parse_h2h_form(text, team, "")
            def _lbl_match(entry, name):
                lbl = (entry or {}).get("team") or ""
                want = (name or "").split()[0][:4].lower() if (name or "").strip() else ""
                return bool(want and want in lbl.lower())
            entry = parsed.get("home")
            if not entry or not _lbl_match(entry, team):
                alt = parsed.get("away")
                if alt and _lbl_match(alt, team):
                    entry = alt
            if not entry or (entry.get("n") or 0) < 3:
                if not entry:
                    self._dump_ctx(driver, "form_h2h_unparseable", extra="inner")
                self._emit_direct(gui_callback,
                                  f"🔍 Form lookup for '{team}' returned no W/D/L run — "
                                  "odds-only model stays active.")
                return None
            self._cache_form_entry(team, entry)
            try:
                self._close_analysis_pages(driver, gui_callback=gui_callback)
            except Exception:
                pass
            self._emit_direct(gui_callback,
                              f"📈 Form {team}: {entry['results'][-min(entry['n'], 6):]} "
                              f"({entry['n']} games, score {entry.get('form_score')}/100)")
            return dict(entry, team=team)
        except Exception as e:
            self._emit_direct(gui_callback, f"🔍 Form lookup skipped for {team}: {str(e)[:70]}")
            return None

    def _h2h_match_form(self, driver, home: str, away: str, gui_callback=None):
        """One search + one stats overlay read yields BOTH teams' form for a game.
        Returns (home_entry, away_entry) or (None, None) on any failure."""
        home = (home or "").strip()
        away = (away or "").strip()
        hf = self._fresh_form(home)
        af = self._fresh_form(away)
        if hf and af:
            return dict(hf, team=home), dict(af, team=away)
        try:
            row = self._surface_team_row(driver, home, away=away)
            if row is None:
                return None, None
            clicked, windows = self._row_stats_icon_click(driver, home)
            if not clicked:
                return None, None
            text = self._read_overlay_text(driver, windows, timeout=10)
            if not text:
                return None, None
            # sanity: the researched page must actually mention BOTH teams
            lowt = (text or "").lower()
            for probe in ((home or ""), (away or "")):
                w = next((x for x in probe.split() if len(x) > 3), "")
                if w and w.lower()[:5] not in lowt:
                    self._dump_ctx(driver, "h2h_wrong_match_page", extra="inner")
                    return None, None
            parsed = self._parse_h2h_form(text, home, away)
            e_home = parsed.get("home") or {}
            e_away = parsed.get("away") or {}
            if (e_home.get("n") or 0) >= 3:
                self._cache_form_entry(home, e_home)
            else:
                hf = None
            if (e_away.get("n") or 0) >= 3:
                self._cache_form_entry(away, e_away)
            else:
                af = None
            e_home = dict(e_home, team=home) if (e_home.get("n") or 0) >= 3 else None
            e_away = dict(e_away, team=away) if (e_away.get("n") or 0) >= 3 else None
            if e_home or e_away:
                self._emit_direct(gui_callback,
                                  f"📈 H2H research {home} vs {away}: "
                                  f"{e_home['results'] if e_home else '-'} "
                                  f"{('score ' + str(e_home.get('form_score')) + '/100') if e_home else ''}"
                                  f" | "
                                  f"{e_away['results'] if e_away else '-'} "
                                  f"{('score ' + str(e_away.get('form_score')) + '/100') if e_away else ''}")
            # close the stats overlay tab so consecutive research passes don't leak windows
            try:
                self._close_analysis_pages(driver, gui_callback=gui_callback)
            except Exception:
                pass
            return e_home, e_away
        except Exception as e:
            self._emit_direct(gui_callback, f"🔍 H2H research skipped: {str(e)[:70]}")
            return None, None

    def _surface_team_row(self, driver, team: str, away: str = "", max_wait: float = 12.0):
        """Search-box the team on the today / upcoming pages and return the VISIBLE
        row element handle, or None. Uses the header Search trigger (icon near Help).
        Matches rows that contain the first words of BOTH teams (when away given),
        so a search for 'Melbourne Victory' can't lock onto an unrelated fixture
        that merely contains 'South Melbourne'."""
        team_keys = [w[:5].lower() for w in (team or "").split()[:2] if w]
        away_keys = [w[:5].lower() for w in (away or "").split()[:2] if w]
        if not team_keys:
            return None
        for url in (self.TODAY_GAMES_PAGE_URL, self.UPCOMING_GAMES_PAGE_URL):
            try:
                self._safe_get(driver, url)
                self._dismiss_visible_promos(driver, rounds=1)
            except Exception:
                continue
            box = self._search_input(driver)
            if box is None:
                continue
            try:
                box.click()
                box.clear()
                box.send_keys(team[:40])
            except Exception:
                continue
            found = None
            deadline = time.time() + max_wait
            while time.time() < deadline:
                found = driver.execute_script(r"""
var teamKeys = arguments[0];
var awayKeys = arguments[1];
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
for (var i = 0; i < rows.length; i++) {
    var t = (rows[i].innerText || '').toLowerCase();
    var ok = teamKeys.length > 0;
    for (var j = 0; j < teamKeys.length && ok; j++) {
        if (t.indexOf(teamKeys[j]) < 0) ok = false;
    }
    for (var j = 0; j < awayKeys.length && ok; j++) {
        if (t.indexOf(awayKeys[j]) < 0) ok = false;
    }
    if (ok && rows[i].offsetParent !== null) return rows[i];
}
return null;
""", team_keys, away_keys)
                if found:
                    return found
                time.sleep(1.2)
            try:
                box.clear()
            except Exception:
                pass
        return None

    def _row_stats_icon_click(self, driver, team: str):
        """Click a row's Statistics/H2H trigger (the 'network' icon). Returns
        (clicked: bool, windows_after: int)."""
        if team is None or team == "":
            return False, len(driver.window_handles) if driver else 0
        before = len(driver.window_handles)
        try:
            res = driver.execute_script(r"""
var q = arguments[0].slice(0, 4).toLowerCase();
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
var row = null;
for (var i = 0; i < rows.length; i++) {
    var t = (rows[i].innerText || '');
    if (t.toLowerCase().indexOf(q) >= 0 && rows[i].offsetParent !== null) { row = rows[i]; break; }
}
if (!row) return 'norow';
var cands = row.querySelectorAll('button, a, span, i, div, [ng-click]');
for (var i = 0; i < cands.length; i++) {
    var el = cands[i];
    var hay = (((el.getAttribute('ng-click') || '') + ' ' + (el.getAttribute('class') || '') + ' ' +
                (el.getAttribute('title') || '')).toLowerCase());
    if (/openbetradarh2h|stats|h2h|preview|analysis/.test(hay)) {
        try {
            if (el.offsetParent === null) continue;
            el.scrollIntoView({block: 'center'});
            el.click();
            return 'clicked';
        } catch (e) { continue; }
    }
}
return 'noicon';
""", team)
            return res == "clicked", len(driver.window_handles)
        except Exception:
            try:
                return False, len(driver.window_handles)
            except Exception:
                return False, before

    def _read_overlay_text(self, driver, windows_before: int, timeout: float = 10.0):
        """After clicking the stats icon, the Betradar overlay may open as a NEW
        window (statsthub.sportradar.com) or render in the current page. Wait for
        'Form'/'Overall Form' text and return the full body text (or '')."""
        deadline = time.time() + timeout
        handle = None
        try:
            windows = driver.window_handles
            if len(windows) > windows_before and len(windows) > 1:
                handle = windows[-1]
                driver.switch_to.window(handle)
        except Exception:
            pass
        out = ""
        while time.time() < deadline:
            try:
                out = driver.execute_script(
                    "return (document.body && document.body.innerText) || '';") or ""
            except Exception:
                out = ""
            low = out.lower()
            if "overall form" in low or (handle is None and re.search(r"\bform\b", low)):
                break
            time.sleep(1.0)
        if not out:
            try:
                self._dump_ctx(driver, "overlay_text_empty", extra="inner")
            except Exception:
                pass
        return out

    def _parse_h2h_form(self, text: str, home: str, away: str):
        """Parse the Betradar H2H match page (statsthub) into per-team form.

        Structure (observed live):
          <Home Name>
          Overall Form
          47
          / 100
          (...) WDL Direction
          <Away Name>
          Overall Form
          60
          / 100
          (...) WDL Direction
          ...
          Last Matches- <Home short>
            <date> | <league> | <round>
            TeamA
            TeamB
             2
             3
            FT
            L          <-- result letter (team's perspective), newest first
            ...
          Last Matches- <Away short>
            ...

        Returns {"home": {"results","n","form_score"}, "away": {...}} with only
        usable (n >= 3) teams filled. Purely string-based, no DOM needed."""
        out = {"home": None, "away": None}
        if not text:
            return out
        scores = re.findall(r"Overall Form\s*\n?\s*(\d{1,3})\s*\n?\s*/\s*100", text)
        # Also accept bare "N / 100" pair (limited-coverage layout shows two
        # big numbers, one per team, only the second labelled Overall Form).
        if len(scores) < 2:
            bare = re.findall(r"(\d{1,3})\s*\n?\s*/\s*100", text)
            for b in bare:
                if len(scores) >= 2:
                    break
                scores.append(int(b))
        # m[0] = junk, then (label, content) pairs
        m = re.split(r"Last Matches-\s*([A-Za-z0-9 .'&\u2011-]{2,40})", text)
        # m[0] = junk, then (label, content) pairs
        sections = []
        for i in range(1, len(m) - 1, 2):
            sections.append((m[i].strip(), m[i + 1]))
        home_cmp = (home or "").strip().split()[0][:4].lower() if (home or "").strip() else ""
        away_cmp = (away or "").strip().split()[0][:4].lower() if (away or "").strip() else ""
        letters = []
        for label, content in sections:
            seq = re.findall(r"FT\s*\n\s*([WDL])", content)
            if not seq:
                seq = re.findall(r"\b([WDL])\b", content.split("Fixtures")[0].split("Match Radar")[0])
            letters.append((label, seq))
        home_lbl_a = home.split()[0][:4].lower() if (home or "").strip() else ""
        away_lbl_a = away.split()[0][:4].lower() if (away or "").strip() else ""
        def _pick(idx_fallback):
            return None
        # position-based with sanity swap (first section = home normally)
        slist = letters[:2] if letters else []
        if len(slist) >= 2:
            l0, s0 = slist[0]
            l1, s1 = slist[1]
            if home_cmp and away_cmp and (home_cmp in l1.lower() and away_cmp in l0.lower()):
                l0, s0, l1, s1 = l1, s1, l0, s0
            res_h = "".join(s0)[:5]
            res_a = "".join(s1)[:5]
        elif len(slist) == 1:
            res_h = "".join(slist[0][1])[:5]
            res_a = ""
        else:
            # fallback: letters region after each team's Overall Form score
            blocks = re.split(r"Overall Form", text)
            res_h = res_a = ""
            if len(blocks) >= 3:
                # blocks[1] -> home zone ends at next 'Overall Form'
                res_h = "".join(re.findall(r"\b([WDL])\b", blocks[1][:300]))[:5]
                res_a = "".join(re.findall(r"\b([WDL])\b", blocks[2][:300]))[:5]
            # limited-coverage fallback: Betradar 'WDL Direction' regions. Only
            # accepted when BOTH sides yield >=3 letters — otherwise the page is
            # too sparse to trust and we keep the No-Form (tilt=0) outcome.
            if len(res_h) < 3 or len(res_a) < 3:
                regions = re.split(r"WDL Direction", text)
                if len(regions) >= 2:
                    r0 = "".join(re.findall(r"[WDL]", regions[0]))[:5]
                    r1 = "".join(re.findall(r"[WDL]", regions[1]))[:5]
                    if len(r0) >= 3 and len(r1) >= 3:
                        res_h, res_a = r0, r1
        h_score = scores[0] if scores else None
        a_score = scores[1] if len(scores) > 1 else None
        if res_h and len(res_h) >= 3:
            out["home"] = {"results": res_h, "n": len(res_h),
                           "form_score": int(h_score) if h_score else None,
                           "team": slist[0][0] if slist else "",
                           "ts": time.time()}
        if res_a and len(res_a) >= 3:
            out["away"] = {"results": res_a, "n": len(res_a),
                           "form_score": int(a_score) if a_score else None,
                           "team": slist[1][0] if len(slist) > 1 else "",
                           "ts": time.time()}
        return out

    # ── SIMILAR-OPPONENT HISTORY (2026-10-05, owner request) ───────────
    @staticmethod
    def _parse_recent_opponents(text: str, max_rows: int = 6):
        """Pull each team's recent fixtures WITH opponent, score and venue.

        The Betradar H2H overlay already renders a "Last Matches-<team>"
        section per side, laid out as:
            <date> | <league> | <round>
            TeamA
            TeamB
            <scoreA>
            <scoreB>
            FT
            <W|D|L>          <- from THIS team's perspective
            (optionally) "Home" / "Away" marker

        We keep the pieces that matter for "how does this team do against
        OPPONENTS LIKE THE ONE IT IS FACING": the opponent, whether it was at
        home or away, the goals for/against, and the result. Purely
        string-based and free — it reuses the page we already open, so this
        costs no extra API budget.
        """
        if not text:
            return {"home": [], "away": []}
        out = {"home": [], "away": []}
        parts = re.split(r"Last Matches-\s*([A-Za-z0-9 .'&\u2011-]{2,40})", text)
        sections = []
        for i in range(1, len(parts) - 1, 2):
            sections.append((parts[i].strip(), parts[i + 1]))
        if not sections:
            return out

        def _rows(blob, team_hint=""):
            rows = []
            # Each fixture block starts at a date header.
            chunks = re.split(r"\n(?=\s*\d{1,2}[/.]\d{1,2}[/.]\d{2,4})", blob)
            hint = re.split(r"\s+", str(team_hint or "").strip().lower())[0] \
                if team_hint else ""
            for ch in chunks:
                date_m = re.search(r"(\d{1,2}[/.]\d{1,2}[/.]\d{2,4})", ch)
                if not date_m:
                    continue
                rest = ch[date_m.end():]
                # The date and the "| League | Round" header share ONE line,
                # so the remainder of that line is still header text, not a
                # team name. Drop it before harvesting names.
                nl = rest.find("\n")
                rest = rest[nl:] if nl >= 0 else ""
                # Team-name lines: skip pure numbers, "FT", and result letters.
                names = []
                for l in rest.splitlines():
                    s = l.strip()
                    if not s or s.upper() == "FT":
                        continue
                    if re.fullmatch(r"[\d\s]{1,4}", s):
                        continue
                    if re.fullmatch(r"[WDL]", s):
                        continue
                    names.append(s)
                if len(names) < 2:
                    continue
                team_a, team_b = names[0], names[1]
                nums = [int(x) for x in re.findall(r"\b(\d{1,2})\b", rest)
                        if 0 <= int(x) <= 20]
                gf = ga = None
                if len(nums) >= 2:
                    a, b = nums[-2], nums[-1]
                    # The result letter is from OUR team's perspective, so use
                    # it to orient the fixture instead of guessing from an
                    # "Home"/"Away" marker the overlay often omits entirely.
                    if hint and hint in team_a.lower():
                        gf, ga = a, b
                    elif hint and hint in team_b.lower():
                        gf, ga = b, a
                    else:
                        gf, ga = a, b
                else:
                    continue
                res_m = re.search(r"\b([WDL])\b", rest)
                rows.append({
                    "date": date_m.group(1),
                    "opp": (team_b if (hint and hint in team_a.lower())
                            else team_a),
                    "venue": "home",
                    "gf": gf, "ga": ga,
                    "res": (res_m.group(1) if res_m else ""),
                })
                if len(rows) >= max_rows:
                    break
            return rows

        if len(sections) >= 1:
            out["home"] = _rows(sections[0][1], sections[0][0])
        if len(sections) >= 2:
            out["away"] = _rows(sections[1][1], sections[1][0])
        return out

    @staticmethod
    def _similar_opponent_k(recent: dict, opponent_name: str = "") -> float:
        """Multiplier in [0.90, 1.08] from results against SIMILAR opponents.

        OWNER REQUEST: weight past matches against similar opponents. A team's
        record against clubs of comparable strength/league level is a better
        predictor than its record against random opposition.

        Method: tokenise the opponent we're about to face and each recent
        opponent, score a crude similarity (shared significant name tokens,
        e.g. "united"/"city"/"rovers"), then compare the team's record in
        those comparable matches. Small samples are heavily damped — three
        games is not a trend — and no comparable matches means exactly
        neutral, never a silent penalty.
        """
        if not isinstance(recent, dict):
            return 1.0
        rows = recent.get("rows") or []
        if not isinstance(rows, list) or not rows:
            return 1.0
        if not opponent_name:
            return 1.0
        _stop = {"fc", "afc", "sc", "ac", "as", "ss", "ssc", "us", "cd", "ud",
                 "rc", "fk", "bk", "if", "aik", "bk", "if", "sv", "vfl", "vfb"}
        def _toks(n):
            return {w.lower() for w in re.split(r"[^A-Za-z]+", str(n or ""))
                    if len(w) >= 4 and w.lower() not in _stop}
        target = _toks(opponent_name)
        if not target:
            return 1.0
        sim_w = sim_l = 0
        for r in rows:
            ot = _toks(r.get("opp"))
            if not ot:
                continue
            shared = target & ot
            if not shared:
                continue
            # Require a meaningful overlap and weight by how specific it is.
            # An EXACT name match (every significant token shared) counts as
            # full evidence; a single shared token in a long name counts less.
            union = len(target | ot) or 1
            w = len(shared) / float(union)
            res = str((r or {}).get("res") or "").upper()
            if res == "W":
                sim_w += 1 + w
            elif res == "D":
                sim_l += 0.5 * (1 + w)
            else:
                sim_l += 1 + w
        total = sim_w + sim_l
        # SAMPLE-SIZE DAMPING. A single comparable match is a data point, not
        # a trend: at full weight one win would already pin the multiplier to
        # its cap, so a 2-game sample and an 8-game sample would look
        # identical. Confidence is ramped in over ~4 comparable matches so
        # the signal grows with evidence and stays small until it does.
        if total < 1.5:
            return 1.0
        _confidence = min(1.0, total / 4.0)
        p_win = sim_w / total
        # Map p_win around a neutral 0.45 baseline, scaled by evidence. The
        # 0.22 slope is deliberately gentle: even a perfect 6-0 record against
        # comparable opposition must not pin the multiplier to its cap on the
        # strength of a handful of games, and a 1-game sample lands at ~1.02.
        k = 1.0 + (p_win - 0.45) * 0.22 * _confidence
        return max(0.90, min(1.08, k))

    def _form_snapshot_map(self, pool, driver=None, gui_callback=None, budget=8) -> None:
        """Best-effort per-event form map: {index: {'home_adv','weight'}}.
        Uses ONE search + stats-overlay read per event (both teams at once) when a
        driver is available. Falls back to cache-only; never blocks the placement
        flow (returns {} on any problem)."""
        events = pool.get("events") or []
        if not events:
            return {}
        looked = 0
        result = {}
        for idx, ev in enumerate(events):
            home = (ev.get("home") or "").strip()
            away = (ev.get("away") or "").strip()
            if not home or not away:
                continue
            hf = self._fresh_form(home)
            af = self._fresh_form(away)
            if driver is not None and looked < budget and (hf is None or af is None):
                try:
                    h2, a2 = self._h2h_match_form(driver, home, away,
                                                  gui_callback=gui_callback)
                    if h2 is not None:
                        hf = h2
                    if a2 is not None:
                        af = a2
                    looked += 1
                except Exception:
                    pass
            tilt = {"home_adv": 0.0, "weight": 0.0}
            if hf and af and (hf.get("n") or 0) >= 3 and (af.get("n") or 0) >= 3:
                d1 = self._form_tilt_from_entries(hf, af)
                if d1.get("weight", 0) > 0:
                    tilt = d1
            result[idx] = tilt
        return result

    def _form_tilt_from_entries(self, he, ae):
        """Tilt from two cached form entries (shared with _form_tilt). Uses the
        W/D/L points AND the Betradar Overall Form rating (0-100) when present."""
        hrs, ars = (he.get("results") or ""), (ae.get("results") or "")
        if len(hrs) < 3 or len(ars) < 3:
            return {"home_adv": 0.0, "weight": 0.0}
        def pts(s):
            return sum(3 if c == "W" else (1 if c == "D" else 0)
                       for c in s.upper() if c in "WDL")
        hp = pts(hrs) / len(hrs)
        ap = pts(ars) / len(ars)
        # blend with the site's own 0-100 rating when available (equal weight)
        hsc = he.get("form_score")
        asc = ae.get("form_score")
        if isinstance(hsc, (int, float)) and isinstance(asc, (int, float)):
            hp = 0.5 * hp + 0.5 * (float(hsc) / 100.0)
            ap = 0.5 * ap + 0.5 * (float(asc) / 100.0)
        adv = min(1.0, max(-1.0, (hp - ap) / 3.0))
        minn = min(len(hrs), len(ars))
        weight = 0.30 if minn >= 5 else (0.22 if minn == 4 else (0.14 if minn == 3 else 0.0))
        if weight <= 0:
            return {"home_adv": 0.0, "weight": 0.0}
        return {"home_adv": round(adv, 4), "weight": weight}

    def _idle_prewindow_research(self, phone: str, password: str,
                                 gui_callback=None):
        """Crawl upcoming fixtures and pre-research top picks while the
        betting window is closed (idle mode).

        Strategy:
        1. Open a lightweight headless browser session
        2. Crawl today-games + upcoming-games pages
        3. Score all games by margin-corrected fair probability
        4. Run the analyst (APEX) on the top 4 candidates
        5. Cache picks so they're ready the instant betting resumes

        Runs at most once per 10 minutes — never blocks the agent thread.
        """
        _last_key = "_idle_research_ts"
        last = float(getattr(self, _last_key, 0))
        if time.time() - last < 600:
            return
        setattr(self, _last_key, time.time())

        driver = None
        owned = False
        try:
            now_h = datetime.now().hour
            now_m = datetime.now().minute
            self._emit_direct(
                gui_callback,
                f"🔬 [{now_h:02d}:{now_m:02d}] Pre-window research — "
                "analysing upcoming games while betting is paused...")

            driver, owned = self._borrow_account_browser(
                phone, gui_callback=None, force_visible=False, mobile=False,
                headless=True, capture_perf=False, minimize=True)
            self._ensure_bet_login(driver, phone, password, gui_callback=None)

            if not self._session_is_live(driver, deep_check=False):
                return

            # Crawl today + upcoming
            games = []
            for url in (self.TODAY_GAMES_PAGE_URL, self.POPULAR_GAMES_URL,
                    self.UPCOMING_GAMES_PAGE_URL, self.FOOTBALL_HOME_URL):
                try:
                    self._safe_get(driver, url)
                    time.sleep(1.2)
                    self._scroll_to_load_more_games(driver, gui_callback=None)
                    batch = self._extract_dom_games(driver) or []
                    known = {str(g.get("id")) for g in games}
                    games += [g for g in batch if str(g.get("id")) not in known]
                    if len(games) >= 40:
                        break
                except Exception:
                    continue

            if not games:
                self._emit_direct(gui_callback, "🔬 Pre-window: no upcoming games found.")
                return

            # Annotate minutes to kickoff
            now_dt = datetime.now()
            for g in games:
                if g.get("start"):
                    g["mins_to_start"] = round(
                        (g["start"] - now_dt).total_seconds() / 60.0)
                else:
                    g["mins_to_start"] = None

            # Score games by best fair probability
            self._load_stats()
            ranked = []
            for g in games:
                mins = g.get("mins_to_start")
                if mins is None or mins < 5:
                    continue   # already started or too close
                gid = str(g.get("id") or "")
                if not gid:
                    continue
                # Skip if already analysed recently
                if self._agent_hub and self._agent_hub.cache.fresh_pick(gid):
                    continue
                h3 = self._fair_win_probs(g.get("h3")) or []
                btts = self._fair_win_probs(g.get("btts")) or []
                ou = self._fair_win_probs(g.get("ou")) or []
                best_p = 0.0
                best_mk = None
                if h3 and h3[0] > best_p: best_p, best_mk = h3[0], "home"
                if btts and btts[0] > best_p: best_p, best_mk = btts[0], "btts"
                if ou and ou[0] > best_p: best_p, best_mk = ou[0], "over"
                if best_p >= self.MIN_LEG_CONF and best_mk:
                    ranked.append((best_p, gid, g.get("name", ""), g))

            ranked.sort(reverse=True)
            top = ranked[:4]

            if not top:
                self._emit_direct(
                    gui_callback,
                    f"🔬 Pre-window: {len(ranked)} candidates below threshold — "
                    "no high-confidence picks yet.")
                return

            self._emit_direct(
                gui_callback,
                f"🔬 Pre-window: {len(top)} top candidate(s) to research:")
            for p, gid, name, g in top:
                mins = g.get("mins_to_start") or 0
                self._emit_direct(
                    gui_callback,
                    f"   📌 {name} (kicks off in {mins}m) — "
                    f"best leg prob {p:.0%}")

            # Run analyst on top candidates (uses cached H2H form, no extra scrape)
            if self._agent_hub is not None and self._agent_hub.analyst.enabled():
                budget = 40.0
                t0 = time.time()
                studied = 0
                for p, gid, name, g in top:
                    if time.time() - t0 > budget:
                        break
                    if " vs " not in name:
                        continue
                    home = name.split(" vs ")[0].strip()
                    away = name.split(" vs ")[1].strip()
                    hf = self._fresh_form(home)
                    af = self._fresh_form(away)
                    try:
                        pick = self._agent_hub.analyst.analyze(gid, g, hf, af)
                        if pick.get("pick") and pick["pick"] != "skip":
                            self._emit_direct(
                                gui_callback,
                                f"   🧠 APEX: {name} → {pick['pick']} "
                                f"(P={pick.get('prob', 0):.0%} "
                                f"conf={pick.get('confidence', 0):.0%}) "
                                f"— {pick.get('reason', '')[:60]}")
                            studied += 1
                    except Exception:
                        continue
                if studied:
                    self._emit_direct(
                        gui_callback,
                        f"✅ Pre-window research done: {studied} pick(s) cached "
                        "— machine will use these when betting resumes.")
            else:
                self._emit_direct(
                    gui_callback,
                    f"🔬 Pre-window: picks scored by probability (no AI key — "
                    "analyst disabled). Top picks cached for bet selector.")

        except Exception as e:
            self._emit_direct(gui_callback,
                              f"🔬 Pre-window research error: {str(e)[:80]}")
        finally:
            try:
                # Only quit a browser THIS job created. Quitting a borrowed worker
                # browser would kill the account's live session mid-round.
                if driver is not None and owned:
                    driver.quit()
            except Exception:
                pass

    def _idle_jackpot_research(self, driver, phone: str, password: str,
                               gui_callback=None):
        """Silently research MEGA and MIDWEEK jackpot pools during idle time.

        Runs at most every 30 minutes per pool. Fetches the live pool,
        computes predictions, and caches them so the MEGA POT / MID POT
        buttons place instantly without any wait.  Never blocks the bet
        loop — any failure is swallowed.
        """
        now = time.time()
        for pool_key in ("mega", "mid"):
            _state_key = f"_idle_jp_{pool_key}_ts"
            last = getattr(self, _state_key, 0.0)
            if (now - last) < 1800.0:  # once per 30 min
                continue
            setattr(self, _state_key, now)
            try:
                pool = self._fetch_jackpot_pool(driver, gui_callback=None)
                if not pool:
                    continue
                detected = (pool.get("name") or "").upper()
                target = "MEGA" if pool_key == "mega" else "MIDWEEK"
                if detected not in ("MEGA", "MIDWEEK", "UNKNOWN"):
                    continue
                if detected != "UNKNOWN" and detected != target:
                    continue  # wrong pool is active
                picks = self._cached_jackpot_picks(pool)
                if picks:
                    self._emit_direct(gui_callback,
                                      f"🎰 Idle: {target} jackpot picks already fresh "
                                      f"({len(picks)} games) — ready to place instantly")
                    continue
                self._emit_direct(gui_callback,
                                  f"🎰 Idle: computing {target} jackpot picks now...")
                picks = self._analyze_jackpot_pool(pool, driver=driver,
                                                   gui_callback=gui_callback,
                                                   form_budget=4)
                if picks:
                    pname = target if detected != "UNKNOWN" else target
                    new_st = {"pool": pool, "picks": picks,
                              "pool_name": pname, "ts": now}
                    self._jackpot_states[pname] = new_st
                    self._jackpot_state = new_st
                    self._emit_direct(gui_callback,
                                      f"🎰 {target} jackpot: {len(picks)} picks cached "
                                      "— tap the button to place instantly")
            except Exception:
                pass

    def _cached_jackpot_picks(self, pool):
        """Return cached picks for THIS pool only (MEGA vs MIDWEEK are stored
        separately so research for one never leaks into the other)."""
        pname = (pool or {}).get("name") or ""
        st = (self._jackpot_states or {}).get(pname) or self._jackpot_state or {}
        if not st:
            return None
        if time.time() - (st.get("ts") or 0) > 45 * 60:
            return None
        if st.get("pool_name") != pname:
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

    def _record_jackpot_entry(self, phone, pool, picks, stake, res, pool_label):
        prod = float(res.get("product") or 0)
        entry = {
            "id": None,
            "phone": str(phone or ""),
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
        owned = False
        try:
            self._emit_direct(gui_callback, "🔎 Idle job: analysing current jackpot pool...")
            driver, owned = self._borrow_account_browser(
                phone, gui_callback=gui_callback, force_visible=False,
                mobile=False, headless=True, capture_perf=False, minimize=True)
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            pool = self._fetch_jackpot_pool(driver, gui_callback=gui_callback)
            if not pool:
                return
            pname = pool.get("name") or "UNKNOWN"
            st = (self._jackpot_states or {}).get(pname) or {}
            same = (st.get("pool_name") == pname and
                    time.time() - (st.get("ts") or 0) < 4 * 3600 and
                    [e.get("match_id") for e in (st.get("pool") or {}).get("events") or []]
                    == [e.get("match_id") for e in pool.get("events") or []])
            if same and st.get("picks"):
                self._emit_direct(gui_callback, self._jackpot_summary(st.get("picks"), pname))
                return
            self._emit_direct(gui_callback, f"🧠 {pname}: analysing games — Poisson model + "
                                            "Over/Under cross-market + team form (H2H stats)...")
            picks = self._analyze_jackpot_pool(pool, driver=driver, gui_callback=gui_callback,
                                           form_budget=40)
            if not picks:
                self._emit_direct(gui_callback, f"⚠️ No analysable games found in {pname}.")
                return
            new_st = {"pool": pool, "picks": picks, "pool_name": pname, "ts": time.time()}
            self._jackpot_states[pname] = new_st
            self._jackpot_state = new_st   # most recent pool for backward compat
            self._save_jackpot_ready(pool, picks)
            self._emit_direct(gui_callback, self._jackpot_summary(picks, pname))
            self._emit_direct(gui_callback,
                              f"🟢 {pname} jackpot research DONE — picks cached & READY to place")
        except Exception as e:
            self._emit_direct(gui_callback, f"ℹ️ Jackpot idle scan skipped: {str(e)[:90]}")
        finally:
            try:
                if driver is not None and owned:
                    driver.quit()
            except Exception:
                pass
            try:
                self._jackpot_lock.release()
            except Exception:
                pass

    def _save_jackpot_ready(self, pool, picks):
        """Persist a 'ready' indicator per pool (MEGA / MIDWEEK kept separately)
        so the GUI can show live alerts for each. Never raises."""
        try:
            path = Path(writable_path("sportsape_jackpot_ready.json"))
            old = self._load_jackpot_ready_raw()
            pools = (old or {}).get("pools") if isinstance(old, dict) else {}
            if not isinstance(pools, dict):
                pools = {}
            pools[(pool or {}).get("name") or "UNKNOWN"] = {
                "name": (pool or {}).get("name") or "UNKNOWN",
                "picks": len(picks or []),
                "ts": time.time(),
                "ready": bool(picks),
            }
            path.write_text(json.dumps({"pools": pools, "ts": time.time()}),
                            encoding="utf-8")
        except Exception:
            pass

    def _load_jackpot_ready_raw(self):
        """Raw JSON read for _save_jackpot_ready (both formats accepted)."""
        try:
            path = Path(writable_path("sportsape_jackpot_ready.json"))
            if not path.exists():
                return None
            return json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            return None

    def _load_jackpot_ready(self):
        """Return a per-pool readiness map for the GUI alert:
        {"pools": {"MEGA": {...}, "MIDWEEK": {...}}, "ts": ...}. Old single-pool
        files ({"name","picks","ts","ready"}) are upgraded to the same shape."""
        try:
            data = self._load_jackpot_ready_raw()
            if not isinstance(data, dict):
                return None
            if "pools" in data and isinstance(data.get("pools"), dict):
                return data
            if data.get("name"):
                return {"pools": {data.get("name"): data}, "ts": data.get("ts")}
            return None
        except Exception:
            return None

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
        owned = False
        try:
            self._emit_direct(gui_callback,
                              f"{emoji} {label} JACKPOT requested — KES {stake:,.0f} entry. "
                              "Opening dedicated session (machine keeps running untouched)...")
            # Wait until the accumulator engine is between rounds so the two flows
            # never place against each other on the same account.
            t0 = time.time()
            while getattr(self, "_engine_busy", False) and time.time() - t0 < 120:
                time.sleep(3)
            driver, owned = self._borrow_account_browser(
                phone, gui_callback=gui_callback, force_visible=False,
                mobile=False, headless=True, capture_perf=False, minimize=True)
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            try:
                balance = self._read_balance_patient(driver, wait=12.0)
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
                                  "(Poisson + cross-market + team form, not blind odds)...")
                picks = self._analyze_jackpot_pool(pool, driver=driver, gui_callback=gui_callback,
                                           form_budget=6)
            if not picks:
                self._emit_direct(gui_callback, "⚠️ Could not compute picks — no bet placed.")
                return {"status": "error", "message": "no picks"}
            self._emit_direct(gui_callback,
                              f"🌍 Placing KES {stake:,.0f} {active} JACKPOT "
                              f"({len(picks)} picks, entry 99-style) now...")
            res = self._place_jackpot_on_driver(driver, pool, picks, stake=stake,
                                                gui_callback=gui_callback)
            if res.get("status") == "ok":
                self._record_jackpot_entry(phone, pool, picks, stake, res, active)
                new_st = {"pool": pool, "picks": picks,
                          "pool_name": active, "ts": time.time()}
                self._jackpot_states[active] = new_st
                self._jackpot_state = new_st
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
                if driver is not None and owned:
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
        # Two workers mark+save concurrently — serialize it so one account's
        # save never clobbers the other's freshly-marked games.
        with self._used_lock:
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
        if getattr(self, "_ledger_archive", None) is None:
            self._ledger_archive = {"total": {"active": 0, "won": 0, "lost": 0, "void": 0,
                                              "staked": 0.0, "won_return": 0.0},
                                    "phones": {}}
        try:
            if self.LEDGER_ARCHIVE_PATH.exists():
                data = json.loads(self.LEDGER_ARCHIVE_PATH.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    self._ledger_archive = data
        except Exception:
            pass
        try:
            if self.LEDGER_PATH.exists():
                data = json.loads(self.LEDGER_PATH.read_text(encoding="utf-8"))
                if isinstance(data, list):
                    self._bets = data
        except Exception:
            pass
        self._daily_bucket_cache = {}
        self._prune_ledger()

    def _fresh_day_board(self, today=None, gui_callback=None, force: bool = False):
        """Start a clean board for *today*: archive the previous day's pending
        rows to a dated snapshot file (wins still settle via win-sync from the
        site), wipe the live ledger, and forget used-game memory so a NEW day
        begins from zero active slips on a full fresh board.
        Safe to call from any worker — only one account actually performs the wipe."""
        try:
            today = today or datetime.now().strftime("%Y-%m-%d")
            # Which day is the board already open for?
            marker = getattr(self, "_board_open_for", None)
            if marker == today and not force:
                return
            cutoff = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
            prev = []
            keep = []
            for b in getattr(self, "_bets", None) or []:
                try:
                    ts = self._ts(b.get("placed_at") or "")
                except Exception:
                    ts = 0.0
                if ts and ts < cutoff.timestamp():
                    prev.append(b)
                else:
                    keep.append(b)
            if prev:
                snap_path = self.LEDGER_PATH.parent / (
                    "sportsape_ledger_prev_"
                    + (datetime.now() - timedelta(days=1)).strftime("%Y-%m-%d")
                    + ".json")
                try:
                    snap_path.write_text(json.dumps(prev, indent=2), encoding="utf-8")
                except Exception:
                    pass
            # Keep today's bets — only wipe bets from previous days.
            # Never wipe active bets placed today even on force-restart.
            if prev:
                self._bets = keep
                self._save_ledger()
            elif force and not keep:
                # Force on an already-empty ledger — nothing to do
                pass
            self._used_games = {}
            try:
                self._save_usage()
            except Exception:
                pass
            try:
                self._account_buckets = {}
            except Exception:
                pass
            self._board_open_for = today
            self._emit_direct(gui_callback,
                              f"🆕 Fresh board for {today}: {len(prev)} old slip(s) "
                              "archived to a dated snapshot — the day starts at 0 "
                              "active. New slips settle normally via win-sync.")
        except Exception as e:
            self._emit_direct(gui_callback, f"⚠️ Fresh-day reset skip: {str(e)[:80]}")

    def _prune_ledger(self):
        """Move long-settled rows into the archive so the live ledger stays small
        (100 accounts x 20 bets/day would otherwise grow to ~60k rows/month, making
        every per-account cap scan O(rows)). Honest totals are preserved in the
        archive and still counted by _ledger_summary / _ledger_summary_phone."""
        bidx = 0
        try:
            cutoff = (datetime.now() - datetime.timedelta(
                days=int(getattr(self, "LEDGER_KEEP_SETTLED_DAYS", 14) or 14))).timestamp()
        except Exception:
            cutoff = 0
        pruned = 0
        keep = []
        for b in getattr(self, "_bets", []) or []:
            if b.get("status") in ("won", "lost", "void"):
                ts = 0.0
                try:
                    ts = self._ts(b.get("placed_at") or "")
                except Exception:
                    ts = 0.0
                if ts and 0 < ts < cutoff:
                    self._archive_one_row(b)
                    pruned += 1
                    continue
            keep.append(b)
        if pruned:
            self._bets = keep
            self._save_ledger()
            self._save_ledger_archive()

    def _archive_one_row(self, b: dict):
        st = b.get("status", "active")
        amt = float(b.get("won_amount") or (b.get("possible_win") if st == "won" else 0) or 0) if st == "won" else 0.0
        stake = float(b.get("stake") or 0)
        if st == "void":
            amt = stake
        arch = getattr(self, "_ledger_archive", None)
        if arch is None:
            arch = {"total": {"active": 0, "won": 0, "lost": 0, "void": 0,
                              "staked": 0.0, "won_return": 0.0}, "phones": {}}
            self._ledger_archive = arch
        tot = arch.setdefault("total",
                              {"active": 0, "won": 0, "lost": 0, "void": 0,
                               "staked": 0.0, "won_return": 0.0})
        tot[st] = int(tot.get(st, 0)) + 1
        tot["staked"] = float(tot.get("staked", 0)) + stake
        if st == "won" or st == "void":
            tot["won_return"] = float(tot.get("won_return", 0)) + amt
        ph = str(b.get("phone") or "")
        if ph:
            p = arch.setdefault("phones", {}).setdefault(
                ph, {"active": 0, "won": 0, "lost": 0, "void": 0,
                     "staked": 0.0, "won_return": 0.0})
            p[st] = int(p.get(st, 0)) + 1
            p["staked"] = float(p.get("staked", 0)) + stake
            if st == "won" or st == "void":
                p["won_return"] = float(p.get("won_return", 0)) + amt

    def _save_ledger_archive(self):
        try:
            self.LEDGER_ARCHIVE_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.LEDGER_ARCHIVE_PATH.write_text(
                json.dumps(getattr(self, "_ledger_archive", {}), indent=2), encoding="utf-8")
        except Exception:
            pass

    def _save_ledger(self):
        try:
            self.LEDGER_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.LEDGER_PATH.write_text(json.dumps(self._bets, indent=2), encoding="utf-8")
        except Exception:
            pass
        self._sb_push_ledger()

    def _sb_sync(self):
        """Return the shared Supabase sync singleton (or None). Thread-safe + cheap."""
        try:
            if _sb_get_sync is None:
                return None
            return _sb_get_sync()
        except Exception:
            return None

    def _sb_push_ledger(self):
        """Mirror the full ledger (placed + shadow bets) to Supabase, non-blocking."""
        try:
            sb = self._sb_sync()
            if sb is not None and getattr(self, "_bets", None) is not None:
                sb.push_bets(self._bets)
        except Exception:
            pass

    def _sb_push_games(self, games: list):
        """Mirror observed games (betted or not) to Supabase, non-blocking."""
        try:
            sb = self._sb_sync()
            if sb is not None and games:
                sb.push_games(games)
        except Exception:
            pass

    def _sb_push_observed_games(self, games: list):
        """Convert a crawl's game dicts into the Supabase game schema and mirror
        them (throttled — every game observed, betted or not, for calibration)."""
        try:
            sb = self._sb_sync()
            if sb is None or not games:
                return
            now = time.time()
            last = float(getattr(self, "_sb_games_last_ts", 0.0) or 0.0)
            if now - last < 60.0:
                return
            self._sb_games_last_ts = now
            betted_ids = set()
            for b in (getattr(self, "_bets", None) or []):
                for gid in (b.get("game_ids") or []):
                    if gid:
                        betted_ids.add(str(gid))
            rows = []
            hist = self._odds_history or {}
            for g in games or []:
                if not isinstance(g, dict):
                    continue
                gid = str(g.get("id") or "")
                if not gid:
                    continue
                rec = hist.get(gid) or {}
                rows.append({
                    "id": gid,
                    "game_id": gid,
                    "name": str(g.get("name") or ""),
                    "home": str(g.get("home") or ""),
                    "away": str(g.get("away") or ""),
                    "kickoff": g.get("start"),
                    "first_odds": rec.get("first") or {},
                    "last_odds": rec.get("last") or {},
                    "betted": gid in betted_ids,
                    "status": "seen",
                    "result": {},
                })
            sb.push_games(rows)
        except Exception:
            pass

    def _sb_push_stats(self):
        """Mirror the calibration/stats snapshot to Supabase, non-blocking."""
        try:
            sb = self._sb_sync()
            if sb is not None:
                self._load_stats()
                sb.push_stats(self._stats)
        except Exception:
            pass

    def _sb_push_results(self, results: list):
        """Mirror per-game settled results to Supabase, non-blocking."""
        try:
            sb = self._sb_sync()
            if sb is not None and results:
                sb.push_results(results)
        except Exception:
            pass

    def _sb_restore_ledger(self):
        """Pull the full ledger history back from Supabase into `_bets` (used when
        the local ledger is empty/corrupt and the cloud copy is authoritative)."""
        try:
            sb = self._sb_sync()
            if sb is None:
                return None
            restored = sb.restore_ledger()
            if restored:
                if getattr(self, "_bets", None) is None:
                    self._bets = []
                known_ids = {str(b.get("id")) for b in self._bets if b.get("id")}
                added = 0
                for b in restored:
                    if b.get("id") and str(b["id"]) in known_ids:
                        continue
                    self._bets.append(b)
                    if b.get("id"):
                        known_ids.add(str(b["id"]))
                    added += 1
                if added:
                    self._save_ledger()
                return added
            return 0
        except Exception:
            return None

    def _sb_restore_stats(self):
        """Pull the calibration/stats snapshot back from Supabase into `_stats`."""
        try:
            sb = self._sb_sync()
            if sb is None:
                return False
            cloud = sb.pull_stats()
            if cloud and isinstance(cloud, dict):
                self._load_stats()
                # Prefer the cloud copy only when it has more settled history.
                if int(cloud.get("settled") or 0) > int(self._stats.get("settled") or 0):
                    self._stats = cloud
                    self._save_stats()
                    return True
            return False
        except Exception:
            return False

    def _record_bet_from_result(self, res: dict, phone: str = None):
        if getattr(self, "_bets", None) is None:
            self._bets = []
        # A placement is not a bet until the bookmaker confirms it. Writing
        # "active" here made every unconfirmed slip look like real exposure
        # forever — overnight this invented 2 of 12 "bets" (KES 20) that never
        # existed. `unconfirmed` counts toward risk but settles either way: the
        # sync promotes it with the site id, or the reaper retires it.
        _placed_at = res.get("placed_at") or datetime.now().isoformat(timespec="seconds")
        self._bets.append({
            "id": None,
            "phone": phone or "",
            "placed_at": _placed_at,
            "legs": int(res.get("legs") or 0),
            "stake": round(float(res.get("stake") or 0), 2),
            "odds": round(float(res.get("odds") or 0), 2),
            "possible_win": round(float(res.get("possible_win") or 0), 2),
            "markets": list(res.get("markets") or []),
            "probs": [round(float(p), 4) for p in (res.get("probs") or [])],
            "game_ids": list(res.get("game_ids") or []),   # per-leg game IDs for analyst feedback
            "leg_names": list(res.get("leg_names") or []), # per-leg game name+suffix for league volatility
            "status": "unconfirmed",
            "unconfirmed_at": _placed_at,
            "settled_at": None,
            "won_amount": None,
            "recipe": {
                "legs": int(res.get("legs") or 0),
                "band": self._band_of(res.get("odds")),
                "lead": self._lead_bucket(res.get("lead_min")),
                "mix": "-".join(sorted(set(res.get("markets") or []))) or "-",
            },
        })
        getattr(self, "_daily_bucket_cache", {}).clear()
        self._save_ledger()

    def _today_placed_for(self, phone: str, today: str = None, include_orphans: bool = False) -> int:
        """Count ledger bets placed today for ONE account (per-phone daily caps).

        include_orphans also counts bets that have no phone recorded yet (legacy
        ledger rows written before the phone field existed) — used when the machine
        runs a SINGLE account so caps stay honest across restarts."""
        split = self._today_placed_split(phone, today, include_orphans)
        return split["day"] + split["night"]

    # ── Day / night betting split (user-approved: 10 day + 10 night) ─────────
    DAY_NIGHT_SPLIT_HOUR = 18

    # How long a placement may stay unconfirmed on the bookmaker before the
    # ledger stops treating it as real money. The site is polled roughly every
    # 2 min and bet history can lag a few minutes behind a submission, so this
    # is generous enough never to retire a bet that genuinely landed, and short
    # enough that a phantom cannot inflate exposure for the rest of the day.
    UNCONFIRMED_GRACE_SEC = 25 * 60

    # How close a local placement time must be to a site bet time before we let
    # the reconciliation attach a site id to it. The site timestamp has minute
    # resolution and can lag a submission by a couple of minutes, so this stays
    # comfortably wide for a genuine bet while refusing to bind a bet to a
    # neighbour that merely shares its stake (e.g. two KES 10 slips 34 min apart).
    LEDGER_MATCH_WINDOW_SEC = 15 * 60

    def _today_placed_split(self, phone: str, today: str = None,
                            include_orphans: bool = False) -> dict:
        """Split today's placed bets for one account into {'day': n, 'night': n}.
        Day = placed before 18:00 local, night = at/after 18:00. Restart-proof:
        driven entirely by ledger timestamps. The day's bucket is built in a single
        O(rows) pass and cached, so per-round cap checks are O(1) afterwards."""
        today = today or datetime.now().strftime("%Y-%m-%d")
        cache = getattr(self, "_daily_bucket_cache", None)
        if cache is None:
            cache = {}
            self._daily_bucket_cache = cache
        bucket = cache.get(today)
        if bucket is None:
            bucket = {"per": {}, "orphans": {"day": 0, "night": 0}}
            for b in getattr(self, "_bets", []) or []:
                pt = b.get("placed_at") or ""
                if not pt.startswith(today):
                    continue
                # Only count slips that actually landed on the site — a bet is only
                # "placed" once the site returns a real slip/bet id. Shadow research
                # rows and failed-then-recorded phantoms carry no site id and must
                # NOT burn today's cap budget (phantom-only inflation hit here).
                if not b.get("id"):
                    continue
                try:
                    t = self._ts(pt)
                    hr = datetime.fromtimestamp(t).hour if t else 0
                except Exception:
                    try:
                        hr = int(pt[11:13])
                    except Exception:
                        hr = 0
                key = "day" if hr < self.DAY_NIGHT_SPLIT_HOUR else "night"
                bp = b.get("phone") or ""
                if not bp:
                    bucket["orphans"][key] += 1
                else:
                    phone_bucket = bucket["per"].setdefault(bp, {"day": 0, "night": 0})
                    phone_bucket[key] += 1
            cache[today] = bucket
        per = bucket["per"].get(phone or "", {"day": 0, "night": 0})
        if include_orphans:
            day = per["day"] + bucket["orphans"]["day"]
            night = per["night"] + bucket["orphans"]["night"]
        else:
            day, night = per["day"], per["night"]
        return {"day": day, "night": night}

    def _period_caps(self, daily_bets) -> tuple:
        """(day_cap, night_cap) for the 18:00 day/night split. Halves the daily
        budget (day gets the extra bet when it's odd)."""
        d = int(daily_bets or 20)
        return ((d + 1) // 2, d // 2)

    def _period_remaining_for(self, phone: str, daily_bets, today: str = None,
                              include_orphans: bool = False):
        """How many bets this account can still place in the CURRENT period.
        Returns (remaining, period_name, cap, placed)."""
        day_cap, night_cap = self._period_caps(daily_bets)
        split = self._today_placed_split(phone, today, include_orphans)
        if datetime.now().hour < self.DAY_NIGHT_SPLIT_HOUR:
            return max(0, day_cap - split["day"]), "day", day_cap, split["day"]
        return max(0, night_cap - split["night"]), "night", night_cap, split["night"]

    def _ledger_summary(self, phone: str = None) -> dict:
        active = won = lost = void = unplaced = 0
        won_return = 0.0
        staked = 0.0
        if phone is not None:
            arch_p = (getattr(self, "_ledger_archive", {}) or {}).get("phones", {}).get(phone or "")
            if arch_p:
                won += int(arch_p.get("won", 0)); lost += int(arch_p.get("lost", 0))
                void += int(arch_p.get("void", 0))
                won_return += float(arch_p.get("won_return", 0)); staked += float(arch_p.get("staked", 0))
        else:
            arch_t = (getattr(self, "_ledger_archive", {}) or {}).get("total", {})
            if arch_t:
                won += int(arch_t.get("won", 0)); lost += int(arch_t.get("lost", 0))
                void += int(arch_t.get("void", 0))
                won_return += float(arch_t.get("won_return", 0)); staked += float(arch_t.get("staked", 0))
        for b in getattr(self, "_bets", []) or []:
            if phone is not None and (b.get("phone") or "") != (phone or ""):
                continue
            st = b.get("status", "active")
            # Shadow bets are learning-only entries — never count toward real stats
            if str(st).startswith("shadow"):
                continue
            # A reaped phantom was never accepted by the bookmaker: it counts as
            # neither settled nor live, and it must not inflate `active` (which
            # reads as "money at risk") or "placed".
            if st in ("not_placed", "phantom"):
                unplaced += 1
                continue
            staked += float(b.get("stake") or 0)
            if st == "won":
                won += 1
                won_return += float(b.get("won_amount") or b.get("possible_win") or 0)
            elif st == "lost":
                lost += 1
            elif st == "void":
                void += 1
                won_return += float(b.get("stake") or 0)
            elif st in ("unconfirmed", "active", ""):
                active += 1
            else:
                active += 1
        net_profit = round(won_return - staked, 2)
        return {"placed": len(self._bets),
                "active": active, "won": won,
                "lost": lost, "void": void, "unplaced": unplaced,
                "won_return": round(won_return, 2),
                "staked": round(staked, 2), "net_profit": net_profit,
                "per_phone": {
                    p: self._ledger_summary_phone(p)
                    for p in sorted(set(list((getattr(self, "_ledger_archive", {}) or {}).get("phones", {}).keys())
                                          + [b.get("phone") or "" for b in (getattr(self, "_bets", None) or [])]))
                    if p}
                }

    def _ledger_summary_phone(self, phone: str) -> dict:
        """Tiny per-account slice of the summary (used in the multi-phone view)."""
        active = won = lost = void = 0
        won_return = 0.0
        staked = 0.0
        arch_p = (getattr(self, "_ledger_archive", {}) or {}).get("phones", {}).get(phone or "")
        if arch_p:
            won += int(arch_p.get("won", 0)); lost += int(arch_p.get("lost", 0))
            void += int(arch_p.get("void", 0))
            won_return += float(arch_p.get("won_return", 0)); staked += float(arch_p.get("staked", 0))
        for b in getattr(self, "_bets", []) or []:
            if (b.get("phone") or "") != (phone or ""):
                continue
            st = b.get("status", "active")
            # Shadow bets are learning-only entries — never count toward real stats
            if str(st).startswith("shadow"):
                continue
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
        total_ph = sum(1 for b in (getattr(self, "_bets", None) or [])
                       if (b.get("phone") or "") == (phone or ""))
        return {"placed": int(arch_p.get("placed", 0)) + total_ph if arch_p else total_ph,
                "active": active, "won": won, "lost": lost, "void": void,
                "won_return": round(won_return, 2), "staked": round(staked, 2),
                "net_profit": round(won_return - staked, 2)}

    # ── Learning engine: the tool grows in intelligence the longer it runs ──
    # Core loop: every settled bet is filed into lifetime stats, per MARKET TYPE
    # (home / btts / over / double_chance / dnb / ...) AND per RECIPE (leg count,
    # odds band, lead-time bucket, market mix). Real hit-rates are compared against
    # the fair probabilities we predicted. Market types that beat prediction are
    # weighted up; ones that lose consistently are retired. Once enough bets have
    # settled, an epsilon-greedy bandit starts steering the odds band toward the
    # top-ROI recipes.
    MIN_BANDIT_SETTLED = 30
    # OWNER RULE (2026-09-26): hard ROI veto. The real-money ledger closed at
    # -43.6% ROI (KES 11,412 staked -> 6,439 returned) and the loop never once
    # said NO: recipes like 6L@gt6 (46 bets, -100%) and 5L@gt6 (78 bets, -55%)
    # were re-bet over and over because the bandit only ever STEERED the odds
    # band, it never refused a band that was losing every time. A recipe with
    # enough REAL bets behind it and a clearly negative ROI is now blocked
    # outright. Enough bets to be sure, and a real-money table only.
    VETO_MIN_TRIALS = 15
    VETO_ROI = -0.20
    # OWNER RULE (2026-09-26): concentration + skew floors.
    # MAX_MARKET_LEGS_PER_SLIP — no single market may fill more than 2 slots, so
    # the machine cannot build a 3-4x same-market slip (the correlated-bet trap:
    # those die together). MIN_SKEW_ODDS — refuse any slip whose combined odds
    # are below this. The historical "safe-looking" sub-3.0 accumulators
    # (2L@lt3 / 3L@lt3) were 431 bets at -43% ROI: stacking tiny-odds legs
    # multiplies the bookmaker's margin, not our edge.
    # OWNER RULE (2026-09-28 -> Option A): lowered to 2.5 to match
    # MIN_COMBINED_ODDS, and now to 1.60 to match the Option A floor. This value
    # is a backstop that tracks the owner floor, NOT an independent gate — when
    # MIN_COMBINED_ODDS moves, this must move with it or the higher of the two
    # silently wins and the owner's floor is dead code.
    # KNOWN RISK, accepted deliberately: the sub-3.0 accumulator family is 431
    # bets at -43% ROI. It was previously blamed on sub-x1.20 filler legs;
    # per-leg odds/confidence floors plus the 2-per-market cap now target that.
    # Watch the ROI of the sub-2.5 cohort after switching; if it does not
    # improve, the correct fix is to raise the per-leg floor, not to re-add a
    # blanket odds veto here.
    MAX_MARKET_LEGS_PER_SLIP = 2
    MIN_SKEW_ODDS = 1.6

    # Hard ceiling on legs in ONE slip, enforced at both placement funnels.
    # The ledger is unambiguous here: 14-leg and 25-leg shapes returned -100%
    # across every market tested. Those are not low-variance lottery tickets,
    # they are near-certain losses wearing a payout headline, and every one of
    # them also destroys the Kelly edge the sizing above depends on. Capping at
    # 6 keeps slips analysable (we can still attribute a result to a market)
    # and keeps any single mistake from wiping the bookroll.
    MAX_SLIP_LEGS_HARD = 6

    # ══════════════════════════════════════════════════════════════════════
    # PORTFOLIO LAYER (2026-09-26) — the missing piece above the accounts.
    # ══════════════════════════════════════════════════════════════════════
    # Every account previously bet independently from its own slice of the board.
    # That is N independent gamblers, not a portfolio: they can all be wrong the
    # same way, and nothing above them owned the total bankroll or the total risk.
    # With 2 accounts that is survivable; with 10 it is how a single bad read
    # (like the 4x-"over" correlated slip) wipes every account simultaneously.
    # These controls are what a 10-account operation actually needs.
    PORTFOLIO_PATH = Path(writable_path("sportsape_portfolio.json"))

    # Drawdown circuit breakers. Per-account freeze stops one account bleeding
    # alone; the portfolio halt is the portfolio-level kill switch that catches
    # the case where EVERY account is bleeding at once — the exact failure mode
    # that per-account checks structurally cannot see.
    ACCOUNT_DRAWDOWN_FREEZE = 0.40   # -40% from peak balance → freeze + review
    # A frozen account must still be able to climb back: after this long frozen
    # it may place REDUCED-stake recovery bets. Without it the breaker is a
    # deadlock - the account has to recover above the threshold to unfreeze,
    # but being frozen is what stops it betting to recover. The limit itself is
    # NOT widened; only the stake is reduced.
    DRAWDOWN_RECOVERY_AFTER_S = 900.0     # 15 min frozen → recovery mode allowed
    DRAWDOWN_RECOVERY_STAKE_PCT = 0.25   # recovery bets are 25% of normal stake
    # A peak may never be raised by a reading this many times the account's own
    # last balance. Catches another account's balance being recorded against
    # this one, which silently froze 0798810080 on 0706719388's money.
    PEAK_JUMP_SANITY_MULT = 2.5
    # DISABLED at user request (2026-09-30): the fleet-wide halt latched on a
    # drawdown that the per-account breakers already own, and it parked a
    # fully-funded account (0798810080, KES 94.73) with money idle purely
    # because the *other* account was bleeding. Set to 10.0 so
    # `pdd >= PORTFOLIO_DRAWDOWN_HALT` can never be true (drawdown is capped
    # at 1.0 by _portfolio_drawdown). Per-account freeze still applies.
    PORTFOLIO_DRAWDOWN_HALT = 10.0   # disabled: fleet-wide halt off
    # How long a bet may sit "active" before we stop counting it as money in
    # play. Football slips settle within a day; a row still marked active after
    # that is a settlement-sync artifact, and counting it inflates equity (and
    # therefore the recorded peak) forever.
    STALE_ACTIVE_BET_S = 36 * 3600.0
    # Fractional Kelly. Full Kelly is far too aggressive at the model's real
    # calibration quality — the ledger shows probabilities off by 6-9 points,
    # and full Kelly on a mispriced probability compounds that error straight
    # into ruin. 1/5 Kelly is the standard defence against model error.
    KELLY_FRACTION = 0.20
    MAX_KELLY_SHARE = 0.05           # never risk >5% of bankroll on ONE slip
    # Cross-account correlation caps. Ten accounts betting the same match or the
    # same market are not diversified — they are one position with the
    # bookmaker's margin counted ten times.
    MAX_ACCOUNTS_PER_LEAGUE = 2       # league-window spread across accounts
    MAX_ACCOUNTS_PER_MARKET = 3       # same market type across the fleet
    MAX_ACCOUNTS_PER_LEAGUE_WINDOW_H = 6

    # CLV (closing line value) — the measure that actually distinguishes skill
    # from luck. We record the price we took, then re-read the same market's
    # price shortly before kick-off. Positive CLV = the market moved in our
    # favour = we beat the closing price = long-run edge, even while results
    # read red in the short run. Negative CLV = we are paying up = bleed.
    CLV_RECHECK_LEAD_MIN = 30         # re-read the line 30 min before kick-off
    CLV_MAX_AGE_H = 26                 # forget lines from slips older than this
    CLV_PATH = Path(writable_path("sportsape_clv.json"))

    # ── Systematic cash-out policy (2026-09-26) ────────────────────────
    # The old rule took a bet only when the offer reached 75% of POSSIBLE WIN.
    # That is the wrong question for an accumulator. The offer is always a
    # fraction of a headline number that no longer exists: once two of six legs
    # are dead, "possible win" is fiction, so a 75%-of-fiction offer can still be
    # a total loss. Cash-out is about the ONE number that is real — the stake we
    # are down. So the policy is expressed in stake-recovery terms, with the
    # possible-win ratio kept only as a "the bet is running" bonus branch.
    CASHOUT_PROFIT_LOCK = 1.25   # take it if the offer banks stake + 25% profit
    CASHOUT_MIN_RECOVERY = 0.35  # NEVER crystallise below 35% of stake back
    CASHOUT_LATE_WINDOW_MIN = 20  # this long before the last leg kicks off...
    CASHOUT_LATE_RECOVERY = 0.60  # ...accept 60% of stake (variance now dominates)
    CASHOUT_WIN_FRACTION = 0.75   # running well: 75% of possible win is a good lock
    # BUGFIX (2026-10-01): was 50. No market in the ledger has ever reached 50
    # trials (the largest, `under`, has 66 but over1/under375/under575 sit at
    # 29/9/5), so this retirement path had NEVER once fired — `retired_markets`
    # was always empty and markets priced 20-37 points above their real hit rate
    # kept taking real stakes. 15 matches the calibrator's own threshold and is
    # enough signal for a 15-point calibration miss.
    RETIRE_TRIALS = 15         # 15+ trials before we trust a retirement decision
    RETIRE_HINTS = 0.15         # real hit-rate must fall this far below predicted to retire
    RETIRE_HINT  = 0.15         # alias used in _maybe_recalibrate
    RECHECK_DAYS = 1
    RECALIB_BET_STEP = 25          # redraw market weights after this many settled bets (Brier-informed)
    # League volatility filter (2026-09-24): per-league×market hit-rate tracking.
    # Leagues whose settled bets underperform prediction get downweighted once we
    # have enough trials to trust the signal; stable leagues get a small boost.
    LEAGUE_MIN_TRIALS = 20
    LEAGUE_VOLATILE_GAP = 0.10     # real hit-rate this far below predicted → volatile
    LEAGUE_DOWNWEIGHT_MULT = 0.88
    LEAGUE_UPWEIGHT_MULT = 1.08
    STATS_CACHE_TTL = 5.0       # seconds to trust in-memory stats before re-reading from disk

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
        # Cache: skip disk I/O if stats were loaded within TTL seconds.
        now = time.time()
        if (getattr(self, "_stats", None) is not None
                and hasattr(self, "_stats_cache_time")
                and (now - self._stats_cache_time) < self.STATS_CACHE_TTL):
            return
        if getattr(self, "_stats", None) is None:
            self._stats = {"market_types": {}, "recipes": {}, "retired_markets": [],
                           "team_stats": {},
                           "settled": 0, "last_recalib": None}
        try:
            if self.STATS_PATH.exists():
                data = json.loads(self.STATS_PATH.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    self._stats = data
        except Exception:
            pass
        self._stats_cache_time = now

    def _save_stats(self):
        self._stats_cache_time = time.time()
        try:
            self._stats["settled"] = int(self._stats.get("settled") or 0)
            # Real/shadow split (2026-09-25): back-fill the real count from the
            # real recipe table if a legacy stats file predates the split, so an
            # old file is never trusted as "all real".
            if not int(self._stats.get("settled_real") or 0):
                _r = self._stats.get("recipes")
                if isinstance(_r, dict):
                    self._stats["settled_real"] = sum(
                        int((v or {}).get("n") or 0) for v in _r.values())
            self._stats["settled_real"] = int(self._stats.get("settled_real") or 0)
            self._stats["settled_shadow"] = int(self._stats.get("settled_shadow") or 0)
            self.STATS_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.STATS_PATH.write_text(json.dumps(self._stats, indent=2), encoding="utf-8")
        except Exception:
            pass
        self._sb_push_stats()

    def nightly_learning(self, gui_callback=None) -> dict:
        """End-of-day learning pass — the "what did the tool learn today" step.

        Runs while the machine is PARKED waiting for the new betting day (the
        cap-hold window is hours of idle), so learning never competes with
        betting. It force-runs the market recalibration over the day's settled
        bets (retirements + signed weight adjustments + Brier check), then
        writes a plain-English journal entry: what was retired, which markets
        beat or lagged their own price, the best/worst teams by money, the
        recipe vetoes, and the day's P&L.

        Never raises, never bets. Returns the summary dict it journalled.
        """
        try:
            self._load_stats()
            st = self._stats
            # Force a full pass: drop the gate so the step/day timer cannot
            # skip a day just because few bets settled.
            st["last_recalib"] = None
            st["settled_at_last_recalib"] = 0
            self._maybe_recalibrate()
            self._save_stats()

            ledger = list(getattr(self, "_bets", None) or [])
            try:
                from betflow import _betting_day
                day = _betting_day()
            except Exception:
                day = datetime.now().strftime("%Y-%m-%d")
            todays = [b for b in ledger
                      if str(b.get("placed_at") or "").startswith(day)
                      and float(b.get("stake") or 0) > 0]
            staked = sum(float(b.get("stake") or 0) for b in todays)
            won = [b for b in todays if b.get("status") == "won"]
            lost = [b for b in todays if b.get("status") == "lost"]
            returned = sum(float(b.get("won_amount") or 0) for b in won)
            retired = list(st.get("retired_markets") or [])

            # Markets, ranked by realised hit-rate minus what the price implied
            mkt = []
            for mk, e in (st.get("market_types") or {}).items():
                n = int(e.get("trials") or 0)
                if n < 3:
                    continue
                real = float(e.get("won") or 0) / n
                pred = float(e.get("expected") or 0.0) / n
                mkt.append({"market": mk, "trials": n, "hit": round(real, 3),
                            "priced": round(pred, 3),
                            "edge": round(real - pred, 3)})
            mkt.sort(key=lambda m: -m["edge"])
            # Teams, ranked by money
            teams = []
            for team, mk_map in (st.get("team_stats") or {}).items():
                for mk, e in (mk_map or {}).items():
                    n = int(e.get("trials") or 0)
                    if n < 2:
                        continue
                    s = float(e.get("stake") or 0)
                    r = float(e.get("ret") or 0)
                    if s <= 0:
                        continue
                    teams.append({"team": team, "market": mk, "trials": n,
                                  "roi": round((r - s) / s, 3)})
            teams.sort(key=lambda t: -t["roi"])
            # Recipe vetoes (proven losing odds bands)
            vetoes = []
            for key, r in (st.get("recipes") or {}).items():
                n = int(r.get("trials") or 0)
                s = float(r.get("stake") or 0)
                if n < 15 or s <= 0:
                    continue
                roi = (float(r.get("ret") or 0) - s) / s
                if roi <= -0.20:
                    vetoes.append({"recipe": key, "trials": n,
                                   "roi": round(roi, 3)})

            # Hot patterns: what the recency-weighted reader says is working.
            # Advisory narration - the mechanical steering reads the same
            # tables live; this just names them in the journal.
            hot_rows = []
            try:
                import pick_filters as _pfh
                hot_rows = sorted(
                    (_pfh.load_hot_patterns() or {}).items(),
                    key=lambda kv: -float(kv[1].get("rec_roi") or 0.0))[:3]
            except Exception:
                hot_rows = []

            entry = {
                "day": day,
                "written_at": datetime.now().isoformat(timespec="seconds"),
                "bets": len(todays), "won": len(won), "lost": len(lost),
                "staked": round(staked, 2), "returned": round(returned, 2),
                "net": round(returned - staked, 2),
                "retired_markets": retired,
                "patterns_hot": [{"pattern": k, **v} for k, v in hot_rows],
                "markets_best": mkt[:3], "markets_worst": mkt[-3:],
                "teams_best": teams[:3], "teams_worst": teams[-3:],
                "vetoed_recipes": vetoes,
            }
            # ── AI post-mortem: honest analysis of the day's results ────────
            # The AI's new role (it no longer blocks games): analyze settled
            # results and tell us what worked, what failed, and why - no
            # sugarcoating. Advisory only.
            ai_insights = ""
            try:
                import json as _j, urllib.request as _ur
                from sportsape_grok import _detect_provider
                _key = ""
                try:
                    _cfg = _j.loads(
                        Path(writable_path("sportsape_settings.json")).read_text(encoding="utf-8"))
                    _key = str(_cfg.get("grok_api_key") or "").strip()
                except Exception:
                    _key = ""
                if _key:
                    _base, _model = _detect_provider(_key, None)
                    _prompt = (
                        "You are a brutally honest betting analyst. Below is today's "
                        "settled bet record. Analyze it with NO sugarcoating - tell "
                        "us what actually worked, what failed, and why. Identify "
                        "patterns in the losses (markets, leagues, odds bands, slip "
                        "size). Give 3 concrete, actionable recommendations. "
                        "Be specific, cite numbers. No fluff.\n\n"
                        "Day: %s\n"
                        "Bets: %d  Won: %d  Lost: %d  Staked: %.2f  Returned: %.2f  Net: %.2f\n"
                        "Markets (trials/hit/priced): %s\n"
                        "Vetoed recipes: %s\n"
                        "Retired markets: %s\n"
                        % (day, len(todays), len(won), len(lost), staked, returned,
                           returned - staked,
                           ", ".join("%s %d/%d (priced %.0f%%)" % (m["market"], int(m["hit"] * m["trials"]), m["trials"], m["priced"] * 100) for m in mkt[:8]),
                           ", ".join(v["recipe"] for v in vetoes),
                           ", ".join(retired) if retired else "none"))
                    _body = _j.dumps({"model": _model, "temperature": 0.3,
                                     "messages": [{"role": "user", "content": _prompt}]}).encode()
                    _req = _ur.Request(
                        _base + "/chat/completions", data=_body,
                        headers={"Content-Type": "application/json",
                                 "Authorization": "Bearer " + _key,
                                 "User-Agent": "BetFlow/1.0",
                                 "Accept": "application/json"})
                    with _ur.urlopen(_req, timeout=30) as _resp:
                        _data = _j.loads(_resp.read().decode("utf-8", "replace"))
                    ai_insights = str(((_data.get("choices") or [{}])[0].get("message") or {}).get("content") or "").strip()
                    if ai_insights:
                        self._emit_direct(gui_callback,
                            "AI POST-MORTEM: " + ai_insights[:400])
            except Exception as _e:
                try:
                    self._emit_direct(gui_callback,
                        "AI post-mortem skipped: " + str(_e)[:60])
                except Exception:
                    pass
            try:
                entry["ai_insights"] = ai_insights
            except Exception:
                pass
            try:
                jpath = Path(writable_path("sportsape_learning_journal.json"))
                hist = []
                if jpath.exists():
                    hist = json.loads(jpath.read_text(encoding="utf-8")) or []
                hist.append(entry)
                jpath.write_text(json.dumps(hist[-60:], indent=1),
                                 encoding="utf-8")
            except Exception:
                pass
            self._emit_direct(gui_callback,
                f"🧠 LEARNING ({day}): {len(todays)} bets, {len(won)} won, "
                f"net KES {entry['net']:+,.2f}")
            if retired:
                self._emit_direct(gui_callback,
                    f"🧠 retired markets (proven unpriceable): "
                    f"{', '.join(retired)}")
            if entry["markets_best"]:
                b = entry["markets_best"][0]
                self._emit_direct(gui_callback,
                    f"🧠 best market vs its price: {b['market']} "
                    f"(hit {b['hit']:.0%} vs priced {b['priced']:.0%}, "
                    f"n={b['trials']})")
            if entry["teams_best"]:
                t = entry["teams_best"][0]
                self._emit_direct(gui_callback,
                    f"🧠 best team by money: {t['team']} [{t['market']}] "
                    f"ROI {t['roi']:+.0%} over {t['trials']}")
            if vetoes:
                self._emit_direct(gui_callback,
                    f"🧠 odds bands the engine now refuses: "
                    f"{', '.join(v['recipe'] for v in vetoes)}")
            return entry
        except Exception as exc:
            try:
                self._emit_direct(gui_callback,
                                  f"⚠️ Learning pass error: {str(exc)[:90]}")
            except Exception:
                pass
            return {}

    @staticmethod
    def _team_pairs(b: dict, blame_markets: list, markets: list) -> list:
        """[(home, away, market, leg_index)] from a settled row.

        New-engine rows carry "games" ("Home vs Away [market]"); legacy ones
        carry leg_names + markets, or the market only in the game tag. Used
        for BOTH the team P&L table and (when no markets list exists) the
        per-leg scoring - the two must agree on leg order.
        """
        pairs = []
        games = b.get("games") or []
        if games:
            for i, gstr in enumerate(games):
                g = str(gstr)
                mk = str(markets[i]) if i < len(markets) else ""
                if not mk and g.endswith("]"):
                    mk = g.rsplit("[", 1)[1][:-1]
                nm = g.rsplit("[", 1)[0].strip()
                h, _s, a = nm.partition(" vs ")
                pairs.append((h.strip(), a.strip(), mk, i))
        else:
            for i, mk in enumerate(blame_markets):
                nm = str((b.get("leg_names") or [""])[i]
                         if i < len(b.get("leg_names") or []) else "")
                h, _s, a = nm.partition(" vs ")
                pairs.append((h.strip(), a.strip(), str(mk), i))
        return pairs

    def _score_legs_from_results(self, b: dict, markets: list) -> list:
        """Per-leg REAL outcomes: [True/False/None] for each market.

        MEASURED 2026-10-15: the book settles a SLIP, never its legs, so the
        per-market "truth" has to be scored from the day's final scores. The
        old scheme credited every leg of a lost slip with (1 - blame) - about
        0.67 "won" per leg - so 40 lost slips made all 17 markets look
        ~70%-accurate while the real slip win-rate was 13%, and every
        steering weight in the app was learned from that fiction.

        Each leg is now scored with the engine's own leg_won() against the
        API-Football day feed (cached; the parse bug that made it empty was
        fixed the same day). A leg with no decidable score gets None and NO
        trial is recorded for it: an absent trial is honest, a fabricated
        one poisons every weight downstream. Never raises - [] means 'no
        data' and the caller then records nothing per-market.
        """
        try:
            import betflow as _bf
            import model_data as _md
            # Score against the day the slip was PLACED, not blindly against
            # today: a bet placed late on D settles on D+1, and reading D+1's
            # feed made every one of its legs undecidable (measured
            # 2026-10-16 - 158 settled bets produced a handful of leg-trials).
            day = str(b.get("placed_at") or "")[:10]
            results = _md.fetch_all_results_on(day)
            names = b.get("leg_names") or []
            games = b.get("games") or []
            out = []
            for i, mk in enumerate(markets):
                g = ""
                if i < len(names) and " vs " in str(names[i]):
                    g = str(names[i])
                elif i < len(games):
                    g = str(games[i]).rsplit("[", 1)[0]
                h, _s, a = g.partition(" vs ")
                h, a = h.strip(), a.strip()
                if not h or not a:
                    out.append(None)
                    continue
                # Tolerant pairing: board names (Flashscore) vs the feed
                # (API-Football) differ often ("Pwd SC" vs "PWD Sports").
                # find_result only guesses when the match is unambiguous, so
                # an unreadable pairing is honestly undecidable, never wrong.
                res = _md.find_result(h, a, results)
                if (not res or int(res.get("hg", -1)) < 0
                        or int(res.get("ag", -1)) < 0):
                    out.append(None)
                    continue
                out.append(_bf.leg_won(str(mk), int(res["hg"]), int(res["ag"]),
                                       hth=res.get("hth"), hta=res.get("hta")))
            return out
        except Exception:
            return []

    def _record_settled_stats(self, b: dict):
        """File one settled bet into lifetime stats (market types + recipe).

        Per-leg probability-weighted outcome attribution:
        - WON slip  → all legs credited (they all had to win for the slip to win).
        - LOST slip → each leg is blamed proportionally to how likely it was to FAIL,
          i.e. leg_blame[i] = (1 - prob[i]) / sum(1 - prob[j]).  The weakest-expected
          leg absorbs the most blame.  This gives the learning engine honest signal
          about which market types / confidence levels are actually the weak links,
          rather than penalising every market equally on every loss.

        Analyst pick feedback:
        After settling, for each game ID in the bet we look up whether the analyst
        made a pick for that game and record the outcome against that pick's confidence
        level in the 'analyst_calibration' stats bucket.  This lets the system track
        whether the analyst's stated confidence actually correlates with wins.
        """
        self._load_stats()
        st = b.get("status", "active")
        if st not in ("won", "lost"):
            return
        markets = b.get("markets") or []
        probs   = b.get("probs") or []
        game_ids = b.get("game_ids") or []
        won = (st == "won")
        # No model probabilities on the row (the model layer is quota-gated and
        # records none when it is quiet). Fall back to the BOOK's own implied
        # probabilities from the per-leg odds - a real expectation available on
        # every bet. The old 0.5 placeholder fabricated a 50% expectation per
        # leg, which made the whole market table noise (measured 2026-10-11:
        # every market showed an identical "hit 75% vs priced 50%").
        if not probs:
            _lo = []
            for o in (b.get("leg_odds") or []):
                try:
                    o = float(o)
                except (TypeError, ValueError):
                    continue
                if o > 1.0:
                    _lo.append(o)
            if _lo:
                probs = [round(1.0 / o, 4) for o in _lo]

        # ── Per-leg probability-weighted blame / credit ─────────────────────
        mt = self._stats.setdefault("market_types", {})

        # OWNER RULE: shadow (zero-stake research) slips never touch the real
        # tables. They file into shadow_recipes below; mixing them into
        # market_types/league/team would inflate the real read with bets that
        # risked nothing (the exact sin the 2026-09-26 split exists to prevent).
        _is_research = (str(b.get("status") or "").startswith("shadow")
                        or float(b.get("stake") or 0.0) <= 0.0)
        blame_markets = [] if _is_research else markets

        # REAL per-leg outcomes from the day's scores (see the helper). The
        # old partial-credit scheme is what made every market look 70%
        # accurate - this replaces it with what actually happened, leg by leg.
        # Legacy rows may carry no "markets" list at all (the market lives in
        # the "[market]" game tag), so the team block below derives the
        # effective market list and the scorer is fed THAT.
        score_markets = blame_markets or [
            mk for _h, _a, mk, _i in self._team_pairs(b, blame_markets, markets)]
        leg_outcomes = (self._score_legs_from_results(b, score_markets)
                        if score_markets else [])
        for i, mk in enumerate(blame_markets):
            leg_ok = leg_outcomes[i] if i < len(leg_outcomes) else None
            if leg_ok is None:
                continue                  # undecidable leg: no honest trial
            p_i = float(probs[i]) if i < len(probs) else 0.5
            e = mt.setdefault(str(mk), {"trials": 0, "won": 0, "expected": 0.0,
                                        "bad_streak": 0, "weight": 1.0,
                                        "weighted_blame": 0.0,
                                        "brier": 0.0})
            e["trials"] = int(e.get("trials") or 0) + 1
            e["won"] = float(e.get("won") or 0) + (1.0 if leg_ok else 0.0)
            e["expected"] = float(e.get("expected") or 0.0) + p_i
            # Brier on the leg's own outcome (1 = the leg won).
            e["brier"] = float(e.get("brier") or 0.0) + (
                (1.0 - p_i) ** 2 if leg_ok else (0.0 - p_i) ** 2)
            # bad_streak: consecutive real losses this market's legs took.
            e["bad_streak"] = 0 if leg_ok else int(e.get("bad_streak") or 0) + 1

        # ── Per-league × market tracking (league volatility filter) ──────────
        # Attribute each leg to the league its game belongs to (rule-based team
        # name detection) and file the same probability-blame signal into a
        # league_markets table. After enough trials per league×market the
        # selector downweights volatile competitions (leagues whose bets
        # underperform their prediction) and upweights stable ones.
        try:
            _legs_meta = (b.get("shadow_legs") or []) if b.get("status") == "shadow" else []
            lm = self._stats.setdefault("league_markets", {})
            for i, mk in enumerate(blame_markets):
                leg_ok = leg_outcomes[i] if i < len(leg_outcomes) else None
                if leg_ok is None:
                    continue                  # undecidable leg: no honest trial
                meta = (b.get("legs_meta") or [{}])[i] if i < len(b.get("legs_meta") or []) else {}
                gname = ""
                if i < len(b.get("leg_names") or []):
                    gname = (b.get("leg_names") or [])[i]
                elif i < len(_legs_meta):
                    gname = _legs_meta[i].get("name") or ""
                # The engine records the REAL sport + competition per leg, so
                # league learning no longer depends on guessing the league from
                # a team name. Fall back to the rule-based detector only for
                # legacy rows.
                sport = str(meta.get("sport") or "").strip()
                league = str(meta.get("league") or "").strip()
                league = f"{sport}: {league}" if (sport and league) else self._league_name(gname)
                le = lm.setdefault(league, {}).setdefault(
                    str(mk), {"trials": 0, "won": 0, "expected": 0.0})
                p_i = float(probs[i]) if i < len(probs) else 0.5
                le["trials"] = int(le.get("trials") or 0) + 1
                le["expected"] = float(le.get("expected") or 0.0) + p_i
                le["won"] = float(le.get("won") or 0) + (1.0 if leg_ok else 0.0)
        except Exception:
            pass
        # ── Recipe stats (real money vs shadow, tracked SEPARATELY) ─────────
        # OWNER RULE (2026-09-26): shadow research slips used to be written into the
        # SAME "recipes" table as real bets, so the headline "1465 settled / learnt
        # a lot" was mostly the tool grading its own homework with no money at
        # risk. That flattered the sample and hid the truth: the real-money recipes
        # were -43.6% ROI over KES 11,412 staked. Shadow picks are still valuable
        # research, but they now land in "shadow_recipes" and can never inflate
        # the real-money read. A recipe is only "real" when stake > 0.
        key = (b.get("recipe") or
               {"legs": b.get("legs") or len(markets) or len(b.get("games") or []),
                "band": self._band_of(b.get("odds")),
                "lead": b.get("lead_bucket") or "-",
                "mix": "-".join(sorted(set(markets))) or "-"})
        # SIGNATURE FIX: a packaged recipe with mix "-" must not erase the real
        # market mix the row carries. Every settled row used to file as
        # "3L@5-6/-/[-]", so the engine could never learn WHICH market
        # combination pays (its only profitable signature - btts+away+draw -
        # sat hidden inside the same bucket as the -90% dnb/ml stacks).
        if str(key.get("mix") or "-") in ("", "-") and markets:
            key = dict(key)
            key["mix"] = "-".join(sorted(set(str(m) for m in markets)))
        key_s = f"{key.get('legs')}L@{key.get('band')}/{key.get('lead')}/[{key.get('mix')}]"
        _stake_this = float(b.get("stake") or 0.0)
        _is_real = _stake_this > 0.0
        _table = "recipes" if _is_real else "shadow_recipes"
        r = self._stats.setdefault(_table, {}).setdefault(
            key_s, {"trials": 0, "won": 0, "stake": 0.0, "ret": 0.0})
        r["trials"] = int(r.get("trials") or 0) + 1
        r["won"]    = int(r.get("won") or 0) + (1 if won else 0)
        r["stake"]  = float(r.get("stake") or 0.0) + _stake_this
        r["ret"]    = float(r.get("ret") or 0.0) + float(b.get("won_amount") or 0)
        # Keep the legacy combined counter for backwards compatibility, but the
        # bandit and every ROI read now use "recipes" (real only) — see
        # _recipe_roi_tables().

        # ── Pattern-slicing tables + recency ring (owner 2026-10-26) ────────
        # "Discover what works and stick with it" needs the data sliced by
        # everything we already know about a slip: its market SIGNATURE
        # (learned here per league too), the sport, the country and the
        # kick-off hour. Real money only - shadows never touch these tables.
        # bets_ring is the recency dataset: the last 90 real settles with
        # their descriptors, from which load_hot_patterns() reads the last
        # 30 for RECENT confirmation (patterns go stale; the ring knows).
        if _is_real:
            _metas = [m for m in (b.get("legs_meta") or []) if isinstance(m, dict)]
            _sig = "-".join(sorted(set(str(m) for m in markets))) or "-"
            _leagues = sorted({str(m.get("league") or "-") for m in _metas})
            _sports = sorted({str(m.get("sport") or "") for m in _metas} - {""})
            _countries = sorted({str(m.get("country") or "") for m in _metas} - {""})
            _hours = sorted({str(m.get("ko_hour") or "") for m in _metas} - {""})
            _won_amount = float(b.get("won_amount") or 0.0)
            try:
                _pat = self._stats.setdefault("bets_ring", [])
                _pat.append({
                    "day": str(b.get("placed_at") or "")[:10],
                    "legs": int(b.get("legs") or len(markets) or 0),
                    "band": self._band_of(b.get("odds")),
                    "sig": _sig,
                    "leagues": _leagues,
                    "sports": _sports,
                    "countries": _countries,
                    "hours": _hours,
                    "stake": _stake_this,
                    "ret": _won_amount,
                    "won": 1 if won else 0,
                })
                if len(_pat) > 90:
                    del _pat[:-90]
                # signature × league table: the AND of the two strongest
                # dimensions - a mix can be hot in one league, cold in another.
                # Multi-valued dimensions split the stake evenly (a 3-league
                # slip files 1/3 stake to each), matching the team table.
                for _lg in _leagues:
                    _share_s = _stake_this / max(1, len(_leagues))
                    _share_r = _won_amount / max(1, len(_leagues))
                    _e = (self._stats.setdefault("sig_league", {})
                          .setdefault(_sig, {})
                          .setdefault(_lg, {"trials": 0, "won": 0,
                                            "stake": 0.0, "ret": 0.0}))
                    _e["trials"] = int(_e.get("trials") or 0) + 1
                    _e["won"] = int(_e.get("won") or 0) + (1 if won else 0)
                    _e["stake"] = float(_e.get("stake") or 0.0) + _share_s
                    _e["ret"] = float(_e.get("ret") or 0.0) + _share_r
                for _table, _vals in (
                        ("sport_stats", _sports),
                        ("country_stats", _countries),
                        ("hour_stats", _hours)):
                    _share_s = _stake_this / max(1, len(_vals))
                    _share_r = _won_amount / max(1, len(_vals))
                    for _v in _vals:
                        _e = (self._stats.setdefault(_table, {}).setdefault(
                            _v, {"trials": 0, "won": 0, "stake": 0.0, "ret": 0.0}))
                        _e["trials"] = int(_e.get("trials") or 0) + 1
                        _e["won"] = int(_e.get("won") or 0) + (1 if won else 0)
                        _e["stake"] = float(_e.get("stake") or 0.0) + _share_s
                        _e["ret"] = float(_e.get("ret") or 0.0) + _share_r
            except Exception:
                pass

        # ── Per-team × market P&L ledger ("teams that always win") ─────────
        # The owner's ask. Every settled slip files the REAL per-leg outcome
        # into team_stats[team][market] (the old partial-credit scheme here
        # was the same fiction as market_types - fixed 2026-10-15), plus the
        # money: each team-game carries an even share of the stake and, on a
        # won slip, of the return - so a team's entry is its own P&L.
        # Games arrive as "Home vs Away [market]" strings on new-engine rows,
        # or as leg_names + markets on legacy ones.
        try:
            ts = self._stats.setdefault("team_stats", {})
            pairs = self._team_pairs(b, blame_markets, markets) \
                if not _is_research else []
            n_legs = max(1, len(pairs))
            stake_share = _stake_this / n_legs
            ret_share = (float(b.get("won_amount") or 0.0) / n_legs) if won else 0.0
            for h, a, mk, i in pairs:
                if not mk:
                    continue
                leg_ok = leg_outcomes[i] if i < len(leg_outcomes) else None
                if leg_ok is None:
                    continue                # undecidable leg: no honest trial
                p_i = float(probs[i]) if i < len(probs) else 0.5
                for team in (h, a):
                    if not team:
                        continue
                    e = ts.setdefault(team, {}).setdefault(
                        mk, {"trials": 0, "won": 0.0, "expected": 0.0,
                             "stake": 0.0, "ret": 0.0})
                    e["trials"] += 1
                    e["won"] += 1.0 if leg_ok else 0.0
                    e["expected"] += p_i
                    e["stake"] += stake_share
                    e["ret"] += ret_share
        except Exception:
            pass

        # ── Analyst calibration feedback ─────────────────────────────────────
        # For each game ID in this bet, check whether the analyst made a pick and
        # record whether the slip outcome matched the pick's stated confidence.
        # This builds an 'analyst_calibration' table: {confidence_bucket: {n, correct}}
        # that shows whether analyst confidence ≥0.7 actually wins more than 0.5.
        try:
            if game_ids and self._agent_hub is not None:
                ac = self._stats.setdefault("analyst_calibration", {})
                for gid in game_ids:
                    try:
                        pick = self._agent_hub.cache.fresh_pick(str(gid), ttl=86400.0)
                    except Exception:
                        pick = None
                    if not pick or pick.get("pick") == "skip":
                        continue
                    conf = float(pick.get("confidence") or 0)
                    # Round confidence to nearest 0.1 bucket (e.g. 0.65 → "0.6")
                    bucket = f"{int(conf * 10) / 10:.1f}"
                    entry = ac.setdefault(bucket, {"n": 0, "correct": 0, "wins": 0})
                    entry["n"] = int(entry.get("n") or 0) + 1
                    if won:
                        entry["wins"] = int(entry.get("wins") or 0) + 1
                    # "correct" = slip won AND analyst picked the market that was in this bet
                    # (a rough proxy; precise per-leg outcome isn't available without
                    # individual leg settlement data from the bookie)
                    if won and pick.get("pick") in (markets or []):
                        entry["correct"] = int(entry.get("correct") or 0) + 1
        except Exception:
            pass

        # Owner rule (2026-09-25): real and shadow learning must be counted
        # SEPARATELY. Shadow slips are free, so a flood of them could otherwise
        # push the "enough data to trust the bandit" threshold past while the
        # real-money sample behind that decision is still tiny. settled stays as
        # the legacy combined total for display; settled_real / settled_shadow are
        # what the learning gates and the ROI veto actually read.
        _is_shadow = str(b.get("status") or "").startswith("shadow") \
            or float(b.get("stake") or 0.0) <= 0.0
        if _is_shadow:
            self._stats["settled_shadow"] = int(self._stats.get("settled_shadow") or 0) + 1
        else:
            self._stats["settled_real"] = int(self._stats.get("settled_real") or 0) + 1
        self._stats["settled"] = int(self._stats.get("settled") or 0) + 1
        self._maybe_recalibrate()
        self._save_stats()
        self._sb_push_settled_results(b, won, markets, game_ids)

    def _new_engine_enrich(self, row_id: str) -> dict:
        """Markets / probs / games for a site bet id, from the engine's ledger.

        The bet-history page shows stake, status and leg count but NOT which
        markets were played. The import path used to write "markets": [] for
        every imported bet, so _record_settled_stats had nothing to file into
        market_types - which is exactly how the live stats file ended up with
        market_types: {} (an empty shell) while the belts ran on. The new
        engine's ledger records the games and markets per bet id, so cross-copy
        from there whenever the ids line up.
        """
        try:
            p = Path(writable_path("betflow_ledger.json"))
            if not p.exists():
                return {}
            cached = getattr(self, "_ne_ledger_cache", None)
            if (cached is None
                    or time.time() - float(cached[0]) > 60.0):
                with open(p, encoding="utf-8") as fh:
                    rows = json.load(fh) or []
                self._ne_ledger_cache = (time.time(), rows)
            for r in (getattr(self, "_ne_ledger_cache", (0, []))[1] or []):
                if not isinstance(r, dict):
                    continue
                ids = {str(r.get("bet_id") or ""), str(r.get("short_bet_id") or "")}
                if str(row_id) not in ids:
                    continue
                out = {}
                for k in ("markets", "probs", "games", "leg_names",
                          "leg_odds", "legs_meta"):
                    if r.get(k):
                        out[k] = r[k]
                return out
        except Exception:
            pass
        return {}

    def _sb_push_settled_results(self, b: dict, won: bool, markets: list, game_ids: list):
        """Mirror this slip's per-game settled results to Supabase so the cloud
        builds a calibration denominator across EVERY betted (and eventually
        unbetted) game. Won slip → every leg won. Lost slip → legs carry the
        slip's lost outcome (per-leg truth isn't available without bookie API)."""
        try:
            rows = []
            source = "shadow" if str(b.get("status") or "").startswith("shadow") else "bet"
            outcome = "won" if won else "lost"
            settled = b.get("settled_at") or datetime.now().isoformat(timespec="seconds")
            phone = str(b.get("phone") or "")
            for i, mk in enumerate(markets or []):
                gid = str(game_ids[i]) if i < len(game_ids or []) else ""
                if not gid:
                    continue
                rows.append({
                    "game_id": gid,
                    "market": mk,
                    "outcome": outcome,
                    "source": source,
                    "phone": phone,
                    "slip_status": outcome,
                    "settled_at": settled,
                })
            if rows:
                self._sb_push_results(rows)
        except Exception:
            pass

    def _maybe_recalibrate(self):
        """Daily OR after enough settled bets: recompute market weights/retirement.

        Retirement is now faster — one bad streak is enough (was two).
        Weight boosting is also more aggressive — markets that beat
        expectation by 3%+ get a material boost.

        2026-09-24: Brier-score calibration added — a market's weight now also
        reflects how well its forecast probabilities were calibrated, not just
        the win/loss rate. The daily gate is supplemented by a settled-count
        gate: once RECALIB_BET_STEP bets have settled since the last redraw the
        weights are recomputed even if a full day hasn't elapsed.
        """
        stats = self._stats
        try:
            last = stats.get("last_recalib")
            step_gate = (int(stats.get("settled") or 0) -
                         int(stats.get("settled_at_last_recalib") or 0)) >= self.RECALIB_BET_STEP
            if last and (datetime.now() - datetime.fromisoformat(last)).days < self.RECHECK_DAYS:
                if not step_gate:
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
            brier_avg = (e.get("brier") or 0.0) / trials
            # Brier benchmark: a perfectly calibrated forecast with hit-rate pred
            # has expected Brier = pred*(1-pred) (the best achievable forecast).
            brier_baseline = pred * (1.0 - pred)
            if brier_avg > brier_baseline + 0.045:
                # Forecast probabilities were substantially miscalibrated (the
                # market's confidence was worse than its win rate justifies).
                deficit = max(deficit, brier_avg - brier_baseline)
            if deficit >= self.RETIRE_HINT:
                e["bad_streak"] = int(e.get("bad_streak") or 0) + 1
                # Retire after ONE bad streak (was two) — faster learning
                if int(e.get("bad_streak") or 0) >= 1 and mk not in retired:
                    retired.add(mk)
                    self._emit_direct(None,
                                      f"🧠 RETIRING market '{mk}': real hit-rate {real:.0%} "
                                      f"vs predicted {pred:.0%} ({trials} bets)")
            else:
                e["bad_streak"] = 0
                # OWNER LEARNING (2026-09-25): the old code only ever boosted a
                # market in this branch — underperformers silently KEPT their last
                # boost. That is exactly how over kept its 1.22 / btts its 1.30
                # while losing. Now the adjustment is SIGNED: markets that beat
                # prediction get weighted up, markets that keep underperforming get
                # weighted DOWN toward their real hit-rate (never below 0.85 so a
                # cold streak can't zero a useful market overnight).
                perf = real - pred
                boost = 0.0
                if abs(perf) >= 0.03:
                    boost = round(perf * 6, 2)
                # Calibration bonus: a market whose Brier beats its own baseline
                # (forecast confident AND right) earns extra weight; a market
                # whose probabilities were sloppy gets its boost clawed back.
                calib_adj = (brier_baseline - brier_avg) * 2.0
                boost = round(boost + calib_adj, 2)
                # OWNER RULE (2026-09-26): the calibration bonus was OVERRIDING the
                # performance signal. In the live table btts ended up at weight 1.39
                # while its real hit-rate (72.7%) sat BELOW its predicted 73.1% —
                # a market that is losing still carrying the biggest boost in the
                # table, because a decent Brier score added +weight on top of a
                # small negative perf. "Nicely calibrated but wrong" is still wrong.
                # So a measured underperformance now DOMINATES: the bonus can only
                # ever REDUCE the penalty, never manufacture a boost, and the floor
                # is lowered to 0.60 so a persistent miss is actually reflected
                # instead of being flattened back to 0.85.
                if perf < 0:
                    boost = min(boost, perf * 6.0)  # never let calib_adj rescue a miss
                if abs(boost) >= 0.02:
                    e["weight"] = min(1.6, max(0.60, 1.0 + boost))
                    self._emit_direct(None,
                                      f"🧠 WEIGHT '{mk}': → {e['weight']:.2f} "
                                      f"(real {real:.0%} vs expected {pred:.0%}, "
                                      f"brier {brier_avg:.3f} vs base {brier_baseline:.3f})")
        stats["retired_markets"] = sorted(retired)
        stats["last_recalib"] = datetime.now().isoformat(timespec="seconds")
        stats["settled_at_last_recalib"] = int(stats.get("settled") or 0)

    def _market_type_weight(self, mk: str) -> float:
        self._load_stats()
        e = (self._stats.get("market_types") or {}).get(str(mk)) or {}
        w = float(e.get("weight") or 1.0)
        trials = int(e.get("trials") or 0)
        # OWNER LEARNING (2026-09-25): the market-weight table used to hold STALE
        # BOOSTS. On 09-24 over/btts/under were sitting at 1.22/1.30/1.18 while each
        # underperformed its predicted hit-rate by 6-9 points (over 74.8% vs 82.6%,
        # btts 74.8% vs 80.7%, under 78.9% vs 87.4%) — so selection literally ranked
        # the losing markets ABOVE the winning ones and the account bled. Once we
        # have enough evidence that a market underperforms, a stale boost can never
        # inflate it: cap its weight at 1.0 (neutral) until the recalibrator writes a
        # signed penalty. Applied on every read so the fix is live immediately.
        #
        # OWNER RULE (2026-09-26): the 50-bet threshold was too lax AND the "cap at
        # 1.0" was too weak. The LIVE stats showed btts sitting at weight 1.39 while
        # its real hit-rate (72.7%) was BELOW its predicted 73.1% — a losing market
        # carrying the biggest boost in the table, purely because 1.0 is still a
        # free pass. So: the guard now scales with evidence (from 25 bets, not 50)
        # and a proven underperformer is pushed BELOW neutral in proportion to how
        # far it missed, instead of merely being allowed to sit at 1.0. A market
        # that keeps missing its own forecast can never rank above an honest one.
        if trials >= 25:
            real = (e.get("won") or 0) / trials
            pred = (e.get("expected") or 0.0) / trials
            if pred > 0 and real < pred:
                miss = (pred - real) / pred  # fractional shortfall, 0..1
                # Neutral at a whiff, scaling down as the miss grows. Floor 0.60 so
                # a genuinely useful market is damped, not deleted (retirement is
                # the tool's job for hopeless markets, not this read guard).
                penalty = max(0.0, min(0.40, miss * 4.0))
                w = min(w, 1.0 - penalty)
        return w

    def _league_name(self, game_name: str) -> str:
        """Best-effort league label for a 'Home vs Away' row (rule-based, no API)."""
        try:
            if LeagueContextAgent is not None:
                league, _s = LeagueContextAgent.detect(str(game_name or ""))
                return league or "Unknown"
        except Exception:
            pass
        return "Unknown"

    def _league_k(self, mk: str, game_name: str) -> float:
        """League volatility multiplier: downweight legs from leagues whose
        settled bets keep underperforming prediction, upweight stable ones.

        Only engages after LEAGUE_MIN_TRIALS settled legs exist for that
        (league × market) pair; otherwise returns 1.0 so a cold league is never
        punished just because we haven't learned about it yet."""
        try:
            self._load_stats()
            league = self._league_name(game_name)
            le = ((self._stats.get("league_markets") or {}).get(league) or {}).get(str(mk))
            if not le:
                return 1.0
            trials = int(le.get("trials") or 0)
            if trials < self.LEAGUE_MIN_TRIALS:
                return 1.0
            real = (le.get("won") or 0) / trials
            pred = (le.get("expected") or 0.0) / trials
            deficit = pred - real
            if deficit >= self.LEAGUE_VOLATILE_GAP:
                # Volatile competition — bets there keep losing vs expectation
                return self.LEAGUE_DOWNWEIGHT_MULT
            if deficit <= -0.05 and real >= pred:
                return self.LEAGUE_UPWEIGHT_MULT
            return 1.0
        except Exception:
            return 1.0

    # Markets permanently blocked — never allowed in any slip regardless of stats.
    # over1 = Over 1.0 goals (too easy, bookmakers underprice it heavily)
    _PERMANENTLY_BLOCKED_MARKETS = frozenset({"over1"})

    def is_market_retired(self, mk: str) -> bool:
        if str(mk) in self._PERMANENTLY_BLOCKED_MARKETS:
            return True
        self._load_stats()
        return str(mk) in (self._stats.get("retired_markets") or [])

    # ══════════════════════════════════════════════════════════════════════
    # PORTFOLIO LAYER (2026-09-26)
    # ══════════════════════════════════════════════════════════════════════
    # Owns the TOTAL bankroll and the TOTAL risk for a fleet of accounts, and
    # sits above the per-account workers. Three jobs:
    #   1. Track peak balance per account + portfolio, so drawdown circuit
    #      breakers have a real reference point (a 40% loss off a KES 30 peak
    #      is a very different event from 40% off KES 5,000).
    #   2. Refuse placements that concentrate correlated risk across accounts
    #      (one game, one account; spread a league; cap a market across the fleet).
    #   3. Size each slip with fractional Kelly, scaled down by the variance of
    #      that account's own recent results, and hard-capped as a share of the
    #      PORTFOLIO total — not just the account balance.
    def _load_portfolio(self) -> dict:
        pf = getattr(self, "_portfolio", None)
        if pf is not None:
            return pf
        pf = {"peaks": {}, "portfolio_peak": 0.0, "frozen": {},
              "halted": False, "halt_reason": "", "refused": 0,
              "refused_reasons": {}}
        try:
            if self.PORTFOLIO_PATH.exists():
                data = json.loads(self.PORTFOLIO_PATH.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    pf.update({k: v for k, v in data.items()
                               if k in ("peaks", "portfolio_peak", "frozen",
                                        "halted", "halt_reason", "refused",
                                        "refused_reasons", "last_equity",
                                        # WHITELIST GAP (2026-10-05). These two
                                        # were written to disk but never read
                                        # back, which silently disabled the
                                        # features that depend on them:
                                        #   last_balance - the cross-account
                                        #     peak guard compares each reading
                                        #     to the account's own previous
                                        #     balance; with nothing loaded its
                                        #     reference was always 0, so the
                                        #     guard NEVER fired and another
                                        #     account's balance went straight
                                        #     back into this account's peak
                                        #     (0798810080 was re-frozen at
                                        #     "-47%" within hours of the repair).
                                        #   frozen_at - without it a frozen
                                        #     account always looked "frozen for
                                        #     0s", so recovery mode could never
                                        #     engage and the deadlock persisted.
                                        "last_balance", "frozen_at")})
        except Exception:
            pass
        pf.setdefault("peaks", {})
        pf.setdefault("frozen", {})
        pf.setdefault("refused_reasons", {})
        pf.setdefault("last_equity", {})
        pf.setdefault("last_balance", {})
        pf.setdefault("frozen_at", {})
        self._portfolio = pf
        return pf

    def _save_portfolio(self):
        try:
            self._load_portfolio()
            self.PORTFOLIO_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.PORTFOLIO_PATH.write_text(
                json.dumps(self._portfolio, indent=2), encoding="utf-8")
        except Exception:
            pass

    def _active_stake_for(self, phone: str) -> float:
        """Cash currently sitting in OPEN bets for one account.

        This is why drawdown cannot be measured on the cash balance alone.
        Placing a bet moves stake out of the cash balance and into the slip, so
        cash DROPS every time a bet is placed and only comes back if that bet
        wins. Judging drawdown on cash therefore books every bet as an instant
        loss, and a machine that places bets correctly looks like it is being
        slaughtered. Equity = cash + open stake, so only a genuinely lost bet
        reduces it.
        """
        total = 0.0
        now = time.time()
        for b in (getattr(self, "_bets", None) or []):
            if str(b.get("phone") or "") != str(phone or ""):
                continue
            # "unconfirmed" counts as at-risk on purpose. A slip we asked the
            # bookmaker for but have not yet seen acknowledged is, until proven
            # otherwise, money that may already be gone. Under-counting it here
            # would flatter equity exactly when a bet is silently missing —
            # and "not_placed" (reaped phantom) is excluded, which is the point.
            if str(b.get("status") or "") not in ("active", "unconfirmed", ""):
                continue
            # A bet that is still "active" long after kickoff is not money in
            # play, it is a row the settlement sync failed to close. Counting it
            # inflates equity, which inflates the recorded PEAK, and the fleet
            # can then never fall back to its true high-water mark -- so a
            # one-off stale row permanently poisons every future drawdown
            # calculation. Ignore anything older than a settled-football
            # window; if it is still unresolved by then, treat it as lost.
            _ts = 0.0
            for _k in ("ts", "placed_ts", "placed_at", "created_at", "time"):
                try:
                    _ts = float(b.get(_k) or 0.0)
                except (TypeError, ValueError):
                    _ts = 0.0
                if _ts > 0:
                    break
            if _ts <= 0:
                # unparseable/ISO timestamp: fall back to the string form
                _iso = str(b.get("placed_at") or b.get("ts") or "")
                try:
                    _ts = datetime.fromisoformat(_iso).timestamp()
                except Exception:
                    _ts = 0.0
            if _ts <= 0:
                # No usable timestamp: we cannot prove the row is stale, so
                # treat it as live. Only an explicitly OLD bet is excluded --
                # guessing "old" from a missing clock would silently zero out
                # real money in play.
                _ts = now
            if (now - _ts) > self.STALE_ACTIVE_BET_S:
                continue
            try:
                total += float(b.get("stake") or 0.0)
            except (TypeError, ValueError):
                continue
        return total

    def _equity_for(self, phone: str, balance: float) -> float:
        """True economic value of one account = spendable cash + money in play."""
        try:
            b = float(balance or 0.0)
        except (TypeError, ValueError):
            b = 0.0
        return max(0.0, b) + self._active_stake_for(phone)

    def _fleet_usable(self, balances: dict) -> dict:
        """The subset of `balances` that is actually a usable equity reading.

        _engine_state["balances"] stores None for a round that failed to read an
        account, and a stale/zeroed last_equity entry looks the same. Treating
        either as a real 0.0 makes a missing account indistinguishable from a
        bankrupt one, which manufactures a fleet-wide drawdown and latches the
        portfolio halt on nothing. Only positive numbers count as readings.
        """
        out = {}
        for phone, bal in (balances or {}).items():
            try:
                v = float(bal)
            except (TypeError, ValueError):
                continue
            if v > 0:
                out[str(phone)] = v
        return out

    def _fleet_equity(self, balances: dict) -> float:
        """Total equity across the WHOLE fleet.

        Accounts missing from `balances` (because only one account has been read
        this round) contribute their last known equity instead of being treated
        as zero. Without that, a single-account round reads as if every other
        account had vanished, which manufactures a huge fake drawdown and halts
        the fleet for no reason.

        A last-known equity that is missing, None, zero or negative is UNKNOWN,
        not zero: it is skipped rather than added. Adding it as 0.0 was the bug
        that latched this fleet at "-87% portfolio drawdown" while the real
        balances were exactly at their peaks.
        """
        pf = self._load_portfolio()
        last = pf.get("last_equity") or {}
        total = 0.0
        seen = set()
        for phone, bal in self._fleet_usable(balances).items():
            seen.add(phone)
            total += self._equity_for(phone, bal)
        for key, eq in last.items():
            if str(key) in seen:
                continue
            try:
                v = float(eq)
            except (TypeError, ValueError):
                continue
            if v <= 0:
                # Unknown equity, not a zero balance. Counting it as 0.0 is what
                # made the fleet look -87% down and pinned the halt on forever.
                continue
            total += v
        return total

    def _fleet_unknown(self, balances: dict) -> set:
        """Tracked accounts with no usable equity reading this round.

        The fleet drawdown cannot be judged while any tracked account is
        unpriced, because portfolio_peak includes that account's peak. Callers
        use this to refuse to HALT on an incomplete picture, and to refuse to
        trust a lift computed from one.
        """
        pf = self._load_portfolio()
        last = pf.get("last_equity") or {}
        peaks = pf.get("peaks") or {}
        usable = self._fleet_usable(balances)
        tracked = {str(k) for k in (list(last.keys()) + list(peaks.keys()))}
        tracked |= {str(p) for p in (balances or {}).keys()}
        unknown = set()
        for key in tracked:
            if key in usable:
                continue
            try:
                if float(last.get(key) or 0.0) > 0:
                    continue
            except (TypeError, ValueError):
                pass
            unknown.add(key)
        return unknown

    def _note_balances(self, balances: dict):
        """Update peak-EQUITY tracking for the drawdown breakers. `balances` maps
        phone -> current cash balance. Peaks only ever rise, so the reference
        point survives losses and a restart.

        A cash reading of exactly 0.0 is treated as UNKNOWN, not as an account
        that went broke. _read_balance_confirmed returns (0.0, False) when it
        cannot read an account or cannot prove which account the session belongs
        to, and a caller that re-checks with an estimate can still land on 0.0.
        Recording that 0.0 would write an equity of just the open stake (e.g.
        KES 15.00 for an account holding KES 70), which then reads as a ~50%
        fleet drawdown and latches a portfolio halt on a perfectly healthy
        account. The breakers already ignore unreadable accounts; this makes the
        recorded EQUITY agree with them instead of poisoning the peak reference.
        """
        try:
            pf = self._load_portfolio()
            last = pf.setdefault("last_equity", {})
            skipped_zero = 0
            for phone, bal in (balances or {}).items():
                key = str(phone)
                try:
                    fbal = float(bal)
                except (TypeError, ValueError):
                    continue
                if fbal <= 0.0:
                    # Keep the previously recorded equity for this account rather
                    # than overwriting it with a false zero.
                    if key not in last:
                        skipped_zero += 1
                    continue
                try:
                    eq = self._equity_for(key, fbal)
                except Exception:
                    continue
                last[key] = round(eq, 2)
                prev = float(pf["peaks"].get(key) or 0.0)
                # CROSS-ACCOUNT CONTAMINATION GUARD (2026-10-05).
                # A peak is the drawdown reference point: once polluted with
                # another account's balance, it silently freezes a healthy
                # account forever. Observed exactly that:
                #   peak['0798810080'] = 195.10  <- which is 0706719388's live
                # balance, not 0798810080's (KES 103.58). 0798810080 was then
                # frozen at "-47% from peak" on a peak it never had.
                #
                # The readings are stored per phone, but the VALUE comes from
                # whichever browser answered, so any helper that is not
                # strictly account-scoped can hand back the other account's
                # figure. A bookmaker payout cannot multiply an account's
                # balance several-fold inside one round, so an implausible jump
                # is far more likely to be a swapped reading than a windfall.
                # Never let one set the peak.
                _prev_bal = 0.0
                try:
                    _prev_bal = float((pf.get("last_balance") or {}).get(key) or 0.0)
                except Exception:
                    _prev_bal = 0.0
                if _prev_bal > 0 and fbal > _prev_bal * self.PEAK_JUMP_SANITY_MULT:
                    self._emit_direct(
                        None,
                        f"\U0001f7e2 REFUSED a peak update for {key}: reading "
                        f"KES {fbal:,.2f} is {fbal / _prev_bal:.1f}x its own last "
                        f"reading (KES {_prev_bal:,.2f}). That is not a payout — "
                        f"it is another account's balance. Peak left at "
                        f"KES {prev:,.2f}.")
                    continue
                try:
                    pf.setdefault("last_balance", {})[key] = round(fbal, 2)
                except Exception:
                    pass
                if eq > prev:
                    pf["peaks"][key] = round(eq, 2)
            if skipped_zero:
                self._emit_direct(
                    None,
                    f"⚠️ Ignored {skipped_zero} zero/unreadable balance reading(s) for "
                    f"equity tracking — kept the last known equity instead of "
                    f"recording a false zero (a false zero reads as a total loss "
                    f"and halts the fleet).")
            # The portfolio peak must be the peak of the FLEET total, and must be
            # compared against a fleet total computed the same way every time.
            # Only ratchet the peak up from a reading that actually covered the
            # fleet: seeding a fleet peak from one account's total would lock in
            # a high-water mark the real fleet can never reach, and every later
            # round would then look like a total loss.
            fleet = self._fleet_equity(balances)
            known = set(last.keys()) | {str(p) for p in (balances or {}).keys()}
            covered = len({str(p) for p in (balances or {}).keys()} & known)
            # A single account is not a fleet. Until we have seen more than one,
            # any "total" is one account's balance wearing a fleet's name.
            if fleet > 0 and len(known) > 1 and covered >= len(known):
                if fleet > float(pf.get("portfolio_peak") or 0.0):
                    pf["portfolio_peak"] = round(fleet, 2)
            self._save_portfolio()
        except Exception:
            pass

    def _account_drawdown(self, phone: str, balance: float) -> float:
        """Fractional drawdown from this account's peak EQUITY (0.0 = at peak)."""
        pf = self._load_portfolio()
        peak = float(pf["peaks"].get(str(phone)) or 0.0)
        if peak <= 0:
            return 0.0
        eq = self._equity_for(str(phone), balance)
        return max(0.0, (peak - eq) / peak)

    def _portfolio_drawdown(self, balances: dict) -> float:
        pf = self._load_portfolio()
        peak = float(pf.get("portfolio_peak") or 0.0)
        if peak <= 0:
            return 0.0
        total = self._fleet_equity(balances)
        if total <= 0:
            return 0.0
        return max(0.0, (peak - total) / peak)

    def _circuit_breaker_check(self, phone: str, balance: float, balances: dict = None):
        """Return (allowed: bool, reason: str). The portfolio-level halt is checked
        FIRST because it is the case per-account checks cannot see: every account
        bleeding at the same time."""
        pf = self._load_portfolio()
        # The halt latches on the way in, but it MUST be able to clear itself.
        # Otherwise one bad reading (a single-account round, a transient zero,
        # a slow balance read) halts the whole fleet permanently and the engine
        # can never recover without a manual file edit -- it just prints
        # "PORTFOLIO HALT" forever while the money sits idle. Re-evaluate the
        # live drawdown each round and release the latch once the fleet is
        # genuinely back inside the limit.
        if pf.get("halted"):
            _bal_map = balances if isinstance(balances, dict) and balances else None
            if _bal_map:
                # A lift may only be trusted when every tracked account has a real
                # reading this round. Judging the fleet from a partial picture
                # re-derives the same fake drawdown that set the halt, so it would
                # pin the latch on forever: the halt suppresses balance reads, and
                # without reads the picture never completes. Money sits idle with
                # "PORTFOLIO HALT" in the log and no way out but a manual edit.
                _unk = self._fleet_unknown(_bal_map)
                if _unk:
                    self._emit_direct(
                        None,
                        f"ℹ PORTFOLIO HALT still latched — {len(_unk)} account(s) "
                        f"have no usable balance this round ({', '.join(sorted(_unk))}), "
                        f"so the fleet drawdown cannot be re-checked. Waiting for a "
                        f"full reading to lift it honestly.")
                    return False, (f"PORTFOLIO HALT: {pf.get('halt_reason') or 'drawdown limit hit'} "
                                   f"(awaiting full balance reading)")
                _live_dd = self._portfolio_drawdown(_bal_map)
                if _live_dd < self.PORTFOLIO_DRAWDOWN_HALT:
                    _was = pf.get("halt_reason") or ""
                    pf["halted"] = False
                    pf["halt_reason"] = ""
                    self._save_portfolio()
                    self._emit_direct(None,
                                      f"🟢 PORTFOLIO HALT lifted — drawdown back to "
                                      f"-{_live_dd:.0%}, inside the "
                                      f"-{self.PORTFOLIO_DRAWDOWN_HALT:.0%} limit. "
                                      f"Previous: {_was}")
                else:
                    return False, (f"PORTFOLIO HALT: {pf.get('halt_reason') or 'drawdown limit hit'}")
            else:
                # No balance map to re-evaluate against, so the latch stands.
                return False, f"PORTFOLIO HALT: {pf.get('halt_reason') or 'drawdown limit hit'}"
        if float(balance or 0) <= 0:
            return False, "no funds"
        dd = self._account_drawdown(phone, balance)
        _ph = str(phone)
        # How long this account has been frozen (0 if never).
        _frozen_at = float((pf.get("frozen_at") or {}).get(_ph) or 0.0)
        _frozen_for = (time.time() - _frozen_at) if _frozen_at else 0.0
        if dd >= self.ACCOUNT_DRAWDOWN_FREEZE:
            pf["frozen"][_ph] = True
            _fa = pf.setdefault("frozen_at", {})
            if _ph not in _fa:
                _fa[_ph] = time.time()
                _frozen_for = 0.0
            self._save_portfolio()
            # ── DRAWDOWN RECOVERY MODE, NOT A DEADLOCK (2026-10-05) ───────
            # The freeze has to be escapable. An account must climb back above
            # the threshold to be released, but being frozen is exactly what
            # stops it betting to climb back - so a strict freeze is a deadlock
            # that only a manual file edit can clear. Observed: 0798810080 sat
            # frozen for hours at KES 103.58 with no route out.
            #
            # After DRAWDOWN_RECOVERY_AFTER_S frozen, allow the account to keep
            # betting at a REDUCED stake so it can recover on its own. The -40%
            # LIMIT is NOT widened and the freeze is NOT hidden - recovery mode
            # only shrinks the stake, and it stops the moment the drawdown is
            # back inside the limit.
            if _frozen_for >= self.DRAWDOWN_RECOVERY_AFTER_S:
                _rm = getattr(self, "_recovery_mode", None)
                if not isinstance(_rm, dict):
                    _rm = {}
                    self._recovery_mode = _rm
                _rm[_ph] = True
                return True, (f"drawdown recovery mode: -{dd:.0%} from peak, "
                              f"stake reduced to "
                              f"{self.DRAWDOWN_RECOVERY_STAKE_PCT:.0%} until the "
                              f"balance climbs back inside "
                              f"-{self.ACCOUNT_DRAWDOWN_FREEZE:.0%}")
            return False, (f"account frozen: -{dd:.0%} from peak "
                           f"(limit -{self.ACCOUNT_DRAWDOWN_FREEZE:.0%})")
        if pf["frozen"].get(_ph):
            # ── LATCH RECOVERY (2026-10-05) ──────────────────────────────
            # The breaker used to latch FOREVER: once `frozen` was set, this
            # branch returned "account frozen by drawdown breaker" on every
            # round and nothing ever cleared it - not even a balance that had
            # already recovered. A safety control that can never release is
            # not a safety control, it is an outage.
            pf["frozen"][_ph] = False
            try:
                (pf.get("frozen_at") or {}).pop(_ph, None)
                (getattr(self, "_recovery_mode", None) or {}).pop(_ph, None)
            except Exception:
                pass
            self._save_portfolio()
            self._emit_direct(
                None,
                f"🟢 {phone}: DRAWDOWN FREEZE LIFTED — back to -{dd:.0%} from peak, "
                f"inside the -{self.ACCOUNT_DRAWDOWN_FREEZE:.0%} limit.")
        # not frozen: clear any recovery flag for this account
        try:
            _rm2 = getattr(self, "_recovery_mode", None)
            if isinstance(_rm2, dict) and _rm2.pop(_ph, None):
                self._save_portfolio()
        except Exception:
            pass
        if balances:
            # Do NOT trip a fleet-wide halt off a partial reading. If this round
            # only managed to read ONE of the accounts, the total is not a fleet
            # total and comparing it to the fleet peak manufactures a huge fake
            # drawdown. _fleet_equity() substitutes last-known equity for
            # missing accounts, which is right most of the time, but if that
            # history is itself cold (first run, rotated state) there is nothing
            # to fall back on and the result is a fraction of the real fleet.
            # Require the total to be a genuine majority of the tracked fleet,
            # otherwise treat it as "not enough data" and do not halt.
            _unk = self._fleet_unknown(balances)
            if _unk:
                self._emit_direct(
                    None,
                    f"ℹ Portfolio drawdown check skipped — {len(_unk)} account(s) "
                    f"have no usable balance this round ({', '.join(sorted(_unk))}); "
                    f"not enough data to judge the fleet safely (no halt).")
            else:
                pdd = self._portfolio_drawdown(balances)
                if pdd >= self.PORTFOLIO_DRAWDOWN_HALT:
                    pf["halted"] = True
                    pf["halt_reason"] = (f"portfolio -{pdd:.0%} from combined peak "
                                         f"(limit -{self.PORTFOLIO_DRAWDOWN_HALT:.0%})")
                    self._save_portfolio()
                    try:
                        self._emit_direct(None,
                                          f"🛑 PORTFOLIO HALT: {pf['halt_reason']} — all accounts "
                                          "stopped. Review the market table before restarting.")
                    except Exception:
                        pass
                    # Never hand back an empty reason: the caller reports the
                    # message verbatim, and a blank one produces the useless
                    # "no bet this round ()" line that hides WHY the round was
                    # skipped. Falling through the lift above clears halt_reason,
                    # so fall back to a generic but truthful description.
                    return False, (pf.get("halt_reason")
                                   or "portfolio drawdown limit hit")
        return True, ""

    def _portfolio_metrics(self) -> dict:
        """The one-screen answer to "is this actually working?" — real results
        only, with the refusals and the CLV next to them.

        A strategy that places few bets and refuses the rest is not broken; it is
        working. Without the refusal count next to the profit count, a quiet week
        looks identical to a broken week, and the natural (wrong) reaction is to
        loosen the gates.
        """
        try:
            self._load_stats()
            pf = self._load_portfolio()
            real_stake = 0.0
            real_ret = 0.0
            real_n = 0
            cashed = 0.0
            for v in (self._recipe_roi_tables() or {}).values():
                real_stake += float(v.get("stake") or 0.0)
                real_ret += float(v.get("ret") or 0.0)
                real_n += int(v.get("trials") or 0)
            for b in (getattr(self, "_bets", None) or []):
                if b.get("status") == "cashed_out":
                    cashed += float(b.get("cashed_out_amount") or 0.0)
            roi = ((real_ret - real_stake) / real_stake) if real_stake > 0 else 0.0
            clv = self._clv_summary()
            clv_n = sum(e["n"] for e in clv.values())
            clv_avg = (sum(e["sum"] for e in clv.values()) / clv_n) if clv_n else None
            return {
                "real_bets": real_n,
                "real_staked": round(real_stake, 2),
                "real_returned": round(real_ret, 2),
                "real_roi": round(roi, 4),
                "cashed_out": round(cashed, 2),
                "settled_real": int(self._stats.get("settled_real") or 0),
                "settled_shadow": int(self._stats.get("settled_shadow") or 0),
                "refused": int(pf.get("refused") or 0),
                "refused_reasons": dict(pf.get("refused_reasons") or {}),
                "frozen_accounts": sorted(pf.get("frozen", {}).keys()),
                "halted": bool(pf.get("halted")),
                "halt_reason": pf.get("halt_reason") or "",
                "clv_samples": clv_n,
                "clv_avg": round(clv_avg, 4) if clv_avg is not None else None,
                "clv_by_market": {k: e["avg"] for k, e in sorted(clv.items())},
            }
        except Exception:
            return {}

    def _emit_portfolio_digest(self, gui_callback=None):
        """Print the honest state of the whole fleet. The CLV line is the one to
        read before anything else: if it is negative, the model is paying up and
        no amount of bet volume will fix it."""
        try:
            m = self._portfolio_metrics()
            if not m:
                return
            _clv_txt = (f"{m['clv_avg']:+.2%} over {m['clv_samples']} samples"
                        if m.get("clv_avg") is not None else "not enough closed lines yet")
            self._emit_direct(gui_callback,
                f"📊 PORTFOLIO DIGEST — real {m['real_bets']} bets, "
                f"KES {m['real_staked']:,.2f} staked, KES {m['real_returned']:,.2f} returned, "
                f"ROI {m['real_roi']:+.1%}"
                + (f", KES {m['cashed_out']:,.2f} banked via cash-out" if m.get("cashed_out") else ""))
            self._emit_direct(gui_callback,
                f"📐 CLV {_clv_txt}"
                + (f" | by market: " + ", ".join(
                    f"{k} {v:+.2%}" for k, v in m['clv_by_market'].items())
                   if m.get("clv_by_market") else ""))
            self._emit_direct(gui_callback,
                f"🚫 Refused {m['refused']} slip(s)"
                + (f" (" + ", ".join(f"{k}: {v}" for k, v in
                                     sorted(m['refused_reasons'].items(),
                                            key=lambda kv: -kv[1])[:5]) + ")"
                   if m.get("refused_reasons") else "")
                + f" | learning: {m['settled_real']} real / {m['settled_shadow']} shadow settled")
            if m.get("halted"):
                self._emit_direct(gui_callback, f"🛑 HALTED: {m['halt_reason']}")
            elif m.get("frozen_accounts"):
                self._emit_direct(gui_callback,
                                  f"❄️ Frozen accounts: {', '.join(m['frozen_accounts'])}")
        except Exception:
            pass

    def _reset_circuit_breakers(self):
        """Clear freeze/halts — used on a deliberate owner restart after review."""
        pf = self._load_portfolio()
        pf["frozen"] = {}
        pf["halted"] = False
        pf["halt_reason"] = ""
        self._save_portfolio()
        try:
            self._emit_direct(None, "🔓 Circuit breakers reset (owner restart).")
        except Exception:
            pass

    # ── Cross-account correlation engine ────────────────────────────────
    def _count_refusal(self, reason: str):
        pf = self._load_portfolio()
        pf["refused"] = int(pf.get("refused") or 0) + 1
        r = pf["refused_reasons"]
        r[reason] = int(r.get(reason) or 0) + 1
        self._save_portfolio()

    def _active_exposure(self, within_hours: float = None) -> dict:
        """Scan open real bets and index them for correlation checks.
        within_hours limits the window (default CLV_MAX_AGE_H)."""
        within_h = float(within_hours or self.CLV_MAX_AGE_H)
        cutoff = datetime.now().timestamp() - within_h * 3600.0
        out = {"games": {}, "markets": {}, "leagues": {}}
        for b in (getattr(self, "_bets", None) or []):
            if str(b.get("status") or "") not in ("active", "", None):
                continue
            try:
                if (b.get("placed_at") or "") and \
                        datetime.fromisoformat(b.get("placed_at")).timestamp() < cutoff:
                    continue
            except Exception:
                pass
            ph = str(b.get("phone") or "")
            for gid in (b.get("game_ids") or []):
                out["games"].setdefault(str(gid), set()).add(ph)
            for nm in (b.get("leg_names") or []):
                lg = self._league_name(nm)
                if lg and lg != "Unknown":
                    out["leagues"].setdefault(lg, set()).add(ph)
            for mk in (b.get("markets") or []):
                out["markets"].setdefault(str(mk), set()).add(ph)
        return out

    def _correlation_verdict(self, phone: str, game_ids, leg_names, markets) -> tuple:
        """Portfolio-level refusal test for a candidate slip.
        Returns (allowed, reason). Rules:
          * ONE game belongs to ONE account. If any game in this slip is already
            on a sibling account, refuse — two accounts on one match is one
            position with the margin counted twice.
          * Cap a league to MAX_ACCOUNTS_PER_LEAGUE accounts.
          * Cap one market type to MAX_ACCOUNTS_PER_MARKET accounts.
        """
        try:
            exp = self._active_exposure()
            ph = str(phone or "")
            for gid in (game_ids or []):
                owners = exp["games"].get(str(gid)) or set()
                others = owners - {ph}
                if others:
                    self._count_refusal("game already on another account")
                    return False, (f"game {gid} is already held by account(s) "
                                   f"{', '.join(sorted(others))} — one game, one account")
            lgs = {self._league_name(n) for n in (leg_names or [])}
            lgs = {l for l in lgs if l and l != "Unknown"}
            for lg in lgs:
                others = (exp["leagues"].get(lg) or set()) - {ph}
                if len(others) >= self.MAX_ACCOUNTS_PER_LEAGUE:
                    self._count_refusal("league spread cap")
                    return False, (f"league '{lg}' is already on {len(others)} accounts "
                                   f"(cap {self.MAX_ACCOUNTS_PER_LEAGUE})")
            for mk in set(markets or []):
                others = (exp["markets"].get(str(mk)) or set()) - {ph}
                if len(others) >= self.MAX_ACCOUNTS_PER_MARKET:
                    self._count_refusal("market concentration cap")
                    return False, (f"market '{mk}' is already on {len(others)} accounts "
                                   f"(cap {self.MAX_ACCOUNTS_PER_MARKET})")
        except Exception:
            return True, ""
        return True, ""

    # ── Variance-scaled fractional Kelly sizing ─────────────────────────
    def _account_variance(self, phone: str, lookback: int = 20) -> float:
        """Std-dev of per-bet RETURN FRACTION (not KES) for this account over its
        recent settled bets. Return-fraction keeps it scale-free, so an account
        with KES 30 and one with KES 5,000 are comparable."""
        pnls = []
        for b in (getattr(self, "_bets", None) or []):
            if str(b.get("phone") or "") != str(phone or ""):
                continue
            if b.get("status") not in ("won", "lost"):
                continue
            st = float(b.get("stake") or 0.0)
            if st <= 0:
                continue
            win = float(b.get("won_amount") or 0.0) if b.get("status") == "won" else 0.0
            pnls.append((win - st) / st)
        pnls = pnls[-int(lookback):]
        if len(pnls) < 3:
            return 1.0  # not enough data — assume typical accumulator variance
        mean = sum(pnls) / len(pnls)
        var = sum((x - mean) ** 2 for x in pnls) / max(1, len(pnls) - 1)
        return max(0.05, var ** 0.5)

    def _kelly_stake(self, phone: str, balance: float, joint_prob: float,
                     combined_odds: float, portfolio_total: float = None) -> float:
        """Fractional-Kelly stake, scaled down by the account's own volatility and
        hard-capped as a share of BOTH the account balance and the portfolio.

        f* = (b*p - q) / b  with b = decimal odds - 1, p = weighted joint win
        chance, q = 1 - p. The full-Kelly value is then multiplied by
        KELLY_FRACTION (0.20) because the model's own calibration error is
        material, and divided by the account's realised volatility so a
        high-variance account automatically bets smaller.
        """
        try:
            p = max(0.01, min(0.99, float(joint_prob or 0.0)))
            o = max(1.01, float(combined_odds or 1.0))
            b = o - 1.0
            q = 1.0 - p
            f = (b * p - q) / b
            if f <= 0:
                return 0.0
            # Order matters. The cap is applied to the EDGE-DRIVEN size first, and
            # volatility scaling comes after. Reversing these (scaling first, then
            # capping) silently nullified the volatility adjustment: whenever the
            # cap bound — which is most real edges — a high-variance account ended
            # up staking exactly the same as a calm one, which is the opposite of
            # the point. Capping first makes MAX_KELLY_SHARE a true safety rail on
            # the maximum, and guarantees volatility always scales the stake down.
            stake = float(balance or 0.0) * f * self.KELLY_FRACTION
            cap = float(balance or 0.0) * self.MAX_KELLY_SHARE
            if portfolio_total:
                cap = min(cap, float(portfolio_total) * self.MAX_KELLY_SHARE)
            stake = min(stake, cap)
            stake /= self._account_variance(phone)
            return max(0.0, stake)
        except Exception:
            return 0.0

    # ══════════════════════════════════════════════════════════════════════
    # CLV — closing line value (2026-09-26)
    # ══════════════════════════════════════════════════════════════════════
    # Results alone cannot tell skill from luck: a bettor who always takes the
    # pre-kickoff price can show a losing record while actually beating the
    # closing line (and therefore earning in expectation over thousands of bets).
    # So we snapshot the price we took, then re-read the same market's price
    # shortly before kick-off. CLV = (bet_odds / closing_odds) - 1. Positive
    # means the market moved against us, i.e. we took a better price than the
    # final one — the actual measure of edge.
    def _snapshot_clv(self, game_ids, markets, odds_by_market, phone: str = None):
        """Record the prices we took so they can be compared to the closing line."""
        try:
            store = self._clv_store()
            for gid, mk, o in (odds_by_market or []):
                key = f"{gid}|{mk}"
                store[key] = {
                    "bet_odds": round(float(o), 3),
                    "close_odds": None,
                    "clv": None,
                    "at": datetime.now().isoformat(timespec="seconds"),
                    "phone": str(phone or ""),
                }
            self._save_clv()
        except Exception:
            pass

    def _clv_store(self) -> dict:
        store = getattr(self, "_clv", None)
        if store is None:
            store = {}
            try:
                if self.CLV_PATH.exists():
                    loaded = json.loads(self.CLV_PATH.read_text(encoding="utf-8"))
                    if isinstance(loaded, dict):
                        store = loaded
            except Exception:
                store = {}
            self._clv = store
        return store

    def _save_clv(self):
        """Persist CLV records. CLV is measured over thousands of bets, so losing
        it on every restart would make the whole metric useless."""
        try:
            self.CLV_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.CLV_PATH.write_text(json.dumps(self._clv_store(), indent=2),
                                     encoding="utf-8")
        except Exception:
            pass

    def _record_closing_odds(self, gid, market, closing_odds):
        """Update one market's closing price. Returns the CLV fraction, or None."""
        try:
            store = self._clv_store()
            rec = store.get(f"{gid}|{market}")
            if not rec or rec.get("close_odds") is not None:
                return None
            bo, co = float(rec.get("bet_odds") or 0), float(closing_odds or 0)
            if bo <= 0 or co <= 0:
                return None
            clv = (bo / co) - 1.0
            rec["close_odds"] = round(co, 3)
            rec["clv"] = round(clv, 4)
            self._save_clv()
            return clv
        except Exception:
            return None

    def _clv_summary(self) -> dict:
        """Aggregate CLV per market so we can see whether the fleet is beating the
        closing line anywhere at all — the honest measure of long-run edge."""
        out = {}
        for key, rec in (self._clv_store() or {}).items():
            if rec.get("clv") is None:
                continue
            mk = str(key).split("|", 1)[1] if "|" in key else "?"
            e = out.setdefault(mk, {"n": 0, "sum": 0.0})
            e["n"] += 1
            e["sum"] += float(rec["clv"])
        for e in out.values():
            e["avg"] = round(e["sum"] / e["n"], 4) if e["n"] else 0.0
        return out

    def _recipe_roi_tables(self) -> dict:
        """Real-money recipe ROI table for learning decisions.

        OWNER RULE (2026-09-26): shadow research slips no longer pollute the
        learning signal. Pre-split, "recipes" mixed real bets with stake=0
        shadow research, so a recipe's ROI was diluted by tickets that never
        risked money and the "1465 settled" headline counted mostly homework.
        Now "recipes" holds real bets only and "shadow_recipes" holds the
        research. This returns the REAL table so the bandit and the veto learn
        from money actually at risk. Legacy entries (recorded before the split)
        that carry stake>0 are folded in automatically, because the split is
        keyed on stake and old rows already have their real stake recorded.
        """
        self._load_stats()
        real = dict(self._stats.get("recipes") or {})
        # A legacy row with zero stake is shadow research; a row with stake>0 is
        # real money and already sits in "recipes". Nothing else to migrate.
        return real

    def _recipe_vetoed(self, recipe_key: str) -> bool:
        """True when a recipe has enough REAL bets and a clearly negative ROI.

        OWNER RULE (2026-09-26): the learning loop had no way to say NO. The
        bandit only steered the odds window, so losing recipes were re-bet
        indefinitely (6L@gt6: 46 real bets, -100%). This is the refusal: with
        VETO_MIN_TRIALS real bets behind it and ROI under VETO_ROI, the recipe
        is blocked outright rather than merely down-weighted.
        """
        try:
            recs = self._recipe_roi_tables()
            v = recs.get(str(recipe_key))
            if not v:
                return False
            trials = int(v.get("trials") or 0)
            stake = float(v.get("stake") or 0.0)
            if trials < self.VETO_MIN_TRIALS or stake <= 0:
                return False
            roi = ((v.get("ret") or 0.0) - stake) / stake
            if roi <= self.VETO_ROI:
                if not getattr(self, "_veto_logged", None):
                    self._veto_logged = set()
                if recipe_key not in self._veto_logged:
                    self._veto_logged.add(recipe_key)
                    self._emit_direct(None,
                                      f"⛔ VETO recipe '{recipe_key}': {trials} real bets, "
                                      f"ROI {roi:+.0%} — not betting this shape again")
                return True
        except Exception:
            return False
        return False

    def _bandit_target_range(self, default_lo: float, default_hi: float) -> tuple:
        """Steer the combined-odds window toward the top-ROI band once enough bets
        have settled.

        Two-level bandit:
        1. Odds band (3-4 / 4-5 / 5-6) — epsilon-greedy on ROI as before.
        2. Market-mix preference — the machine also tracks which market combinations
           (e.g. btts-home-over, btts-over, over) hit best in the recipes table and
           records that as an advisory note in the engine state so the selector's
           weight system can be further guided. No hard filtering — just transparency.
        """
        self._load_stats()
        # Gate on the REAL-money sample only (2026-09-25). The bandit steers
        # real stakes, so it must not be unlocked by thousands of free shadow
        # slips — settled_real is the count that actually carries risk.
        settled = int(self._stats.get("settled_real") or 0)
        if settled < self.MIN_BANDIT_SETTLED:
            return float(default_lo), float(default_hi)
        bands = {"3-4": (3.0, 4.0), "4-5": (4.0, 5.0), "5-6": (5.0, 6.0),
                 "6-8": (6.0, 8.0), "8-12": (8.0, 12.0), "12-15": (12.0, 15.0)}
        recs = self._recipe_roi_tables()
        eligible = {}
        mix_roi: dict = {}
        leg_roi: dict = {}
        for k, v in recs.items():
            if "@" not in k:
                continue
            parts = k.split("@")
            band = parts[1].split("/")[0] if len(parts) > 1 else ""
            # extract market mix from key: "3L@3-4/lead/[btts-home-over]"
            mix_m = __import__("re").search(r"\[([^\]]+)\]", k)
            mix = mix_m.group(1) if mix_m else ""
            # extract leg count
            legs_m = __import__("re").match(r"(\d+)L@", k)
            legs = int(legs_m.group(1)) if legs_m else 0

            trials = int(v.get("trials") or 0)
            if trials < 5:
                continue
            stake = float(v.get("stake") or 0)
            roi = ((v.get("ret") or 0.0) - stake) / max(1e-9, stake)
            if band in bands:
                eligible.setdefault(band, []).append(roi)
            if mix:
                mix_roi.setdefault(mix, []).append(roi)
            if legs:
                leg_roi.setdefault(legs, []).append(roi)

        if not eligible:
            return float(default_lo), float(default_hi)

        import random
        eps = 0.15
        profitable_bands = [b for b in bands if bands[b][1] >= self.MIN_COMBINED_ODDS]
        if random.random() < eps and profitable_bands:
            band = random.choice(profitable_bands)
        else:
            band = max(eligible, key=lambda b: sum(eligible[b]) / len(eligible[b]))
        lo, hi = bands[band]

        # Advisory: best market mix and leg count — logged once per new settled count
        prev = getattr(self, "_bandit_banner", None)
        if prev != (band, settled):
            self._bandit_banner = (band, settled)
            self._emit_direct(None, f"🎰 Bandit steering to band {band} ({lo:g}-{hi:g}) "
                                    f"[{settled} settled bets learned]")
            if mix_roi:
                best_mix = max(mix_roi, key=lambda m: sum(mix_roi[m]) / len(mix_roi[m]))
                best_mix_roi = sum(mix_roi[best_mix]) / len(mix_roi[best_mix])
                self._emit_direct(None,
                    f"📊 Best market mix so far: [{best_mix}] "
                    f"(ROI {best_mix_roi:+.1%} over {len(mix_roi[best_mix])} slips)")
            if leg_roi:
                best_legs = max(leg_roi, key=lambda n: sum(leg_roi[n]) / len(leg_roi[n]))
                best_legs_roi = sum(leg_roi[best_legs]) / len(leg_roi[best_legs])
                self._emit_direct(None,
                    f"📊 Best leg count so far: {best_legs}-leg "
                    f"(ROI {best_legs_roi:+.1%} over {len(leg_roi[best_legs])} slips)")
            # Store advisory in engine state so other parts can read it
            self._engine_state["bandit_best_mix"] = (
                max(mix_roi, key=lambda m: sum(mix_roi[m]) / len(mix_roi[m]))
                if mix_roi else "")
            self._engine_state["bandit_best_legs"] = (
                max(leg_roi, key=lambda n: sum(leg_roi[n]) / len(leg_roi[n]))
                if leg_roi else 0)

        # never leave the caller's safe overall window, and keep it a
        # valid, profitable window: lo <= hi and combined odds >= floor
        hi = min(hi, 6.0)
        lo = max(self.MIN_COMBINED_ODDS, min(lo, hi - 1.0))
        if hi < self.MIN_COMBINED_ODDS:
            hi = self.MIN_COMBINED_ODDS
        if hi < lo:
            hi = max(lo + 1.0, self.MIN_COMBINED_ODDS)
        return lo, hi

    # ── Bet History scraping for win monitoring ─────────────────────────────
    def _extract_bet_history(self, driver, max_scroll: int = 8) -> list[dict]:
        """Parse the Bet History page (.bet-container rows) into normalized records.

        Scrolls the page up to *max_scroll* times to load older results via
        infinite-scroll so yesterday's bets don't stay "active" just because
        they've scrolled off the initial viewport.
        """
        # Wait for at least one bet row to render before starting
        for _ in range(10):
            try:
                count = self._exec_script(
                    driver,
                    "return document.querySelectorAll('.bet-container').length;",
                    default=0, timeout=8.0, label="bet-history rows")
                if count and count > 0:
                    break
            except Exception:
                pass
            time.sleep(0.5)

        # Scroll to load more rows (infinite-scroll pagination)
        last_count = 0
        for _s in range(max_scroll):
            try:
                cur = self._exec_script(
                    driver,
                    "return document.querySelectorAll('.bet-container').length;",
                    default=last_count, timeout=8.0, label="bet-history rows")
                if cur == last_count and _s > 0:
                    break   # no new rows loaded — we've hit the bottom
                last_count = cur or 0
                self._exec_script(
                    driver,
                    "if (document.body) window.scrollTo(0, document.body.scrollHeight);",
                    default=None, timeout=8.0, label="bet-history scroll")
                time.sleep(0.8)
            except Exception:
                break

        try:
            rows = self._exec_script(driver, r"""
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
""", default=[], timeout=10.0, refresh_on_hang=True, label="bet-history extract")
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
            raw_status = (r.get("status") or "").strip()
            parsed.append({
                "id": str(r.get("id") or "").strip(),
                "date": (r.get("date") or "").strip(),
                "legs": int(legs_m.group(1)) if legs_m else 0,
                "stake": money(r.get("amount")),
                "win": money(r.get("win")),
                "status": raw_status,
                "cashout_available": "cashout" in raw_status.lower(),
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
        """Return a match score (lower is better) when the site row plausibly IS
        our placed bet, else None.

        Time tolerance is 2 hours — the site timestamp has no seconds and can lag
        by several minutes; bets from yesterday that weren't synced yet may be
        several hours off from the local clock.  Stake is the primary hard
        discriminator; the time window just prevents false matches between
        different bets with identical amounts.

        possible_win is deliberately a SOFT signal, not a gate. On a settled bet
        the site reports the RETURN (what actually came back), not the
        pre-settlement potential the slip was priced with, so demanding equality
        here permanently blocked id assignment for exactly the bets that had
        already settled — which is how 8 of 10 real bets sat in the ledger with
        no site id forever.
        """
        try:
            # Try primary date format, then alternate formats
            drow = None
            for fmt in ("%d/%m/%y %H:%M", "%d/%m/%Y %H:%M", "%Y-%m-%d %H:%M"):
                try:
                    drow = datetime.strptime(row["date"], fmt)
                    break
                except (ValueError, KeyError):
                    continue
            if drow is None:
                return None
        except Exception:
            return None
        try:
            dplaced = datetime.fromisoformat(placed_at_iso)
        except Exception:
            return None
        diff = abs((dplaced - drow).total_seconds())
        # 2-hour window — wide enough for overnight / timezone drift but tight
        # enough to avoid matching completely different bets.
        if diff > 7200:
            return None
        row_stake = row.get("stake") if row.get("stake") is not None else 0
        row_win   = row.get("win")   if row.get("win")   is not None else 0
        if abs(float(row_stake) - float(stake)) > 0.05:
            return None
        # Soft penalty: prefer a row whose win agrees with what we priced, but
        # never exclude the candidate outright.
        penalty = 0.0
        if possible_win:
            penalty = 0.0 if abs(float(row_win) - float(possible_win)) <= 0.10 else 600.0
        return diff + penalty

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
        # A site bet may back at most ONE local row. Without this reservation
        # two local rows happily claimed the same site id (00:47 was stamped
        # with 8860, which actually belonged to the 01:45 bet), corrupting every
        # later status update for that id. Starts EMPTY and is filled as rows
        # below claim their match.
        claimed_site_ids = set()
        # Resolve ids GLOBALLY rather than row-by-row. A greedy per-row pass is
        # order-dependent: the 00:04 phantom grabbed the 00:38 site bet (both
        # KES 10, 34 min apart) purely by being processed first, which shifted
        # every later id by one and put 8860 on the wrong local row. Collect all
        # (local, site) candidates, then take the tightest pairs first so exact
        # matches always beat near-misses.
        pending = []
        for _i, _b in enumerate(getattr(self, "_bets", None) or []):
            if _b.get("id") or _b.get("status") not in ("unconfirmed", "active", None, ""):
                continue
            for _r in rows:
                _rid = str(_r.get("id") or "")
                if not _rid:
                    continue
                _score = self._match_ledger_bet(_r, _b.get("placed_at", ""),
                                               _b.get("stake") or 0,
                                               _b.get("possible_win") or 0)
                if _score is not None and _score <= self.LEDGER_MATCH_WINDOW_SEC:
                    pending.append((_score, _i, _rid))
        pending.sort(key=lambda t: (t[0], t[1], t[2]))
        _taken_local = set()
        for _score, _i, _rid in pending:
            if _i in _taken_local or _rid in claimed_site_ids:
                continue
            b = self._bets[_i]
            b["id"] = _rid
            _taken_local.add(_i)
            claimed_site_ids.add(_rid)
            # The SITE is authoritative about the slip that actually exists.
            # Adopt its leg count so a leg the site dropped is reflected locally
            # instead of being remembered forever, and align the payout field.
            _srow = next((r for r in rows if str(r.get("id")) == _rid), None)
            if _srow is not None:
                try:
                    if _srow.get("legs") is not None:
                        b["legs"] = int(_srow["legs"])
                except (TypeError, ValueError):
                    pass
                if _srow.get("win") is not None and not b.get("settled_at"):
                    b["possible_win"] = _srow.get("win")
            b.pop("unconfirmed_at", None)
            b.pop("reconcile_note", None)
            changed = True
        for b in getattr(self, "_bets", None) or []:
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
            # ── Analyst pick feedback: tell the cache how this slip came out
            # so the analyst_accuracy table stays current ──────────────────
            if self._agent_hub is not None:
                try:
                    for gid in (b.get("game_ids") or []):
                        self._agent_hub.cache.record_pick_outcome(str(gid), new_status)
                    # Emit an accuracy digest after every win/loss to the log
                    if new_status in ("won", "lost"):
                        acc = self._agent_hub.cache.analyst_accuracy_summary()
                        if acc:
                            best = max(acc.items(),
                                       key=lambda kv: int(kv[1].get("n") or 0), default=None)
                            if best and int(best[1].get("n") or 0) >= 3:
                                n = int(best[1].get("n") or 0)
                                w = int(best[1].get("wins") or 0)
                                self._emit_direct(
                                    gui_callback,
                                    f"🧠 Analyst accuracy (conf {best[0]}): "
                                    f"{w}/{n} correct ({w/n:.0%}) across {len(acc)} buckets")
                except Exception:
                    pass
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
                if self._agent_hub is not None:
                    try:
                        self._agent_hub.alert(
                            "win",
                            f"🏆 WON on {b.get('phone') or ''}: +KES {w:,.2f} "
                            f"(KES {profit:,.2f} profit) — Bet #{b.get('id')}",
                            gui_callback=gui_callback)
                    except Exception:
                        pass
                # Signal the engine worker that a win just landed — it should
                # re-read balance immediately and resume betting if funded.
                self._engine_state["_balance_refreshed"] = True
                self._engine_state["_win_just_landed"] = True
            elif new_status == "lost":
                self._emit_direct(gui_callback,
                                  f"❌ LOST Bet #{b.get('id')} (−KES {(b.get('stake') or 0):,.2f})")
            elif new_status == "void":
                self._emit_direct(gui_callback,
                                  f"♻️ {row.get('status')} Bet #{b.get('id')} (stake returned)")
        # ── Phantom reaper ───────────────────────────────────────────────
        # A placement we never saw confirmed on the site is NOT a live bet. If it
        # has stayed unconfirmed past the grace window (and the site history we
        # just read covers its timestamp), retire it as `not_placed` and release
        # the stake instead of counting it as exposure forever.
        if changed or rows:
            for b in getattr(self, "_bets", None) or []:
                if b.get("id") or b.get("status") not in ("unconfirmed", "active"):
                    continue
                stamp = b.get("unconfirmed_at") or b.get("placed_at") or ""
                try:
                    age = (datetime.now() - datetime.fromisoformat(stamp)).total_seconds()
                except Exception:
                    continue
                if age < self.UNCONFIRMED_GRACE_SEC:
                    continue
                b["status"] = "not_placed"
                b["reconcile_note"] = ("no matching bet on the bookmaker after "
                                       f"{self.UNCONFIRMED_GRACE_SEC // 60} min")
                try:
                    b["stake"] = 0.0
                except (TypeError, ValueError):
                    pass
                changed = True
                self._emit_direct(gui_callback,
                                  f"🧹 UNCONFIRMED → NOT PLACED (stake released): "
                                  f"KES {(b.get('stake') or 0):,.2f} at {b.get('placed_at', '')[:16]}")
        if changed:
            getattr(self, "_daily_bucket_cache", {}).clear()
            self._save_ledger()
        # ── Cash-out opportunity detection ────────────────────────────
        # Read per-leg status on every cash-out-eligible bet, log which games
        # are done/won/pending, and auto cash out under the owner's policy
        # (majority legs already won correctly + offer close to possible win).
        try:
            cashout_rows = [r for r in rows
                            if r.get("cashout_available")
                            and (r.get("legs") or 0) >= 2]
            for cr in cashout_rows:
                lid = str(cr.get("id") or "")
                local_b = next((b for b in (getattr(self, "_bets", None) or [])
                                if str(b.get("id") or "") == lid), None)
                if local_b is None:
                    pw = float(cr.get("win") or 0)
                    self._emit_direct(gui_callback,
                                      f"💱 CASHOUT AVAILABLE on Bet #{lid}: "
                                      f"stake KES {(cr.get('stake') or 0):,.0f} → "
                                      f"possible KES {pw:,.0f} (not in local ledger)")
            self._auto_cashout_pass(driver, rows, gui_callback=gui_callback)
        except Exception:
            pass
        # ── Shadow bet scoring: settle any no-funds planned slips whose games
        # have now finished. We use the site's live bet history rows to infer
        # results for each shadow leg by matching game IDs against our planned
        # slip, then record the outcome into stats for continuous learning.
        self._settle_shadow_bets(rows, gui_callback=gui_callback)
        summary = self._ledger_summary()
        self._emit_direct(gui_callback,
                          f"📊 Winnings: {summary['won']} won (+KES {summary['won_return']:,.2f}) | "
                          f"{summary['lost']} lost | {summary['void']} void | "
                          f"{summary['active']} active | net {summary['net_profit']:+,.2f}")
        return summary

    # ── Smart cash-out: per-leg reads + thresholded auto cash-out ─────────
    def _read_bet_leg_details(self, driver, bet_id: str, expand: bool = True,
                              expected_legs: int = 0) -> dict:
        """Expand the matching .bet-container card and read its per-leg rows.

        Returns leg_rows (game / date / odds / market / pick / results per leg),
        plus won / pending / finished_not_won counts and the possible win.
        READ-ONLY: never clicks the final cash-out confirm in here.
        The card is re-read until the expected number of leg rows are rendered.
        """
        result = {"leg_rows": [], "possible_win": None, "stake": None,
                  "won": 0, "pending": 0, "finished_not_won": 0}
        try:
            if expand:
                driver.execute_script(r"""
var id = arguments[0];
var cards = document.querySelectorAll('.bet-container');
for (var i = 0; i < cards.length; i++) {
    var el = cards[i].querySelector('.bet_id');
    var t = el ? (el.innerText || '') : '';
    if (t.indexOf(id) >= 0) {
        try { cards[i].click(); } catch (e) {}
        var o = cards[i].querySelector('.bet-details-opener');
        if (o) { try { o.click(); } catch (e2) {} }
        break;
    }
}
""", bet_id)
            ready = False
            for _ in range(12):
                time.sleep(0.5)
                try:
                    n = driver.execute_script(
                        "var c=null; var cards=document.querySelectorAll('.bet-container');"
                        "for(var i=0;i<cards.length;i++){var e=cards[i].querySelector('.bet_id');"
                        "if(e&&(e.innerText||'').indexOf(arguments[0])>=0){c=cards[i];break;}}"
                        "return c?(c.querySelectorAll('.bet-detail').length):0;", bet_id)
                    if n and n > 0:
                        ready = True
                        break
                except Exception:
                    pass
            if not ready:
                return result
            # Re-read the detail rows until the expected count is rendered so a
            # slow Angular render can't leave us half-empty per-leg data.
            rendered = []
            pw_val = stake_val = None
            for _attempt in range(4):
                time.sleep(0.9)
                info = driver.execute_script(r"""
var id = arguments[0];
var c = null;
var cards = document.querySelectorAll('.bet-container');
for (var i = 0; i < cards.length; i++) {
    var e = cards[i].querySelector('.bet_id');
    if (e && (e.innerText || '').indexOf(id) >= 0) { c = cards[i]; break; }
}
if (!c) return null;
function cell(d, sel, re) {
    var e = d.querySelector(sel);
    if (!e) return '';
    var s = (e.innerText || '').replace(/\s+/g, ' ').trim();
    return re ? s.replace(re, '') : s;
}
var rows = [];
c.querySelectorAll('.bet-detail').forEach(function(d) {
    var dot = d.querySelector('.bet-prizes-status .dot, .dot');
    var resTxt = cell(d, '.bet_results');
    rows.push({
        game: cell(d, '.bet_game'),
        game_id: cell(d, '.bet_id', /Game ID\s*:?\s*/i),
        date: cell(d, '.bet_date'),
        odds: cell(d, '.bet_odds', /Odds\s*:?\s*/i),
        market: cell(d, '.bet_market'),
        pick: cell(d, '.bet_pick'),
        results: resTxt,
        won: (dot && (dot.className || '').indexOf('green') >= 0) ? 1 : 0
    });
});
var pwEl = c.querySelector('.bet_winnings');
var amtEl = c.querySelector('.bet_amount');
return JSON.stringify({
    rows: rows,
    pw: pwEl ? (pwEl.innerText || '') : '',
    amount: amtEl ? (amtEl.innerText || '') : ''
});
""", bet_id)
                try:
                    data = json.loads(info or "null")
                except Exception:
                    data = None
                if not data:
                    continue

                def moneyz(s):
                    m = re.search(r"([0-9][0-9,]*\.?[0-9]{0,2})", s or "")
                    return round(float(m.group(1).replace(",", "")), 2) if m else None
                if pw_val is None:
                    pw_val = moneyz(data.get("pw"))
                if stake_val is None:
                    stake_val = moneyz(data.get("amount"))
                rendered = []
                for r in data.get("rows") or []:
                    leg = {
                        "game": r.get("game") or "",
                        "game_id": (r.get("game_id") or "").strip(),
                        "date": (r.get("date") or "").strip(),
                        "odds": r.get("odds") or "",
                        "market": r.get("market") or "",
                        "pick": r.get("pick") or "",
                        "results": r.get("results") or "",
                        "won": bool(r.get("won")),
                    }
                    # Skip rows that haven't rendered their text yet
                    if not (leg["game"] or leg["pick"] or leg["results"]):
                        continue
                    leg["finished"] = bool(leg["results"] and leg["results"] != "-")
                    rendered.append(leg)
                if rendered and (expected_legs <= 0 or len(rendered) >= expected_legs):
                    break
            result["possible_win"] = pw_val
            result["stake"] = stake_val
            for leg in rendered:
                result["leg_rows"].append(leg)
                if leg["won"]:
                    result["won"] += 1
                elif leg["finished"]:
                    result["finished_not_won"] += 1
                else:
                    result["pending"] += 1
        except Exception:
            pass
        return result

    def _probe_cashout_offer(self, driver, bet_id: str) -> float | None:
        """Click 'Request CashOut' on the card so the site exposes the current
        cash-out value, then return it as KES. Does NOT confirm the cash-out."""
        try:
            clicked = False
            for _ in range(10):
                try:
                    hit = driver.execute_script(r"""
var id = arguments[0];
var cards = document.querySelectorAll('.bet-container');
var c = null;
for (var i = 0; i < cards.length; i++) {
    var e = cards[i].querySelector('.bet_id');
    if (e && (e.innerText || '').indexOf(id) >= 0) { c = cards[i]; break; }
}
if (!c) return 'no-card';
var req = c.querySelector('.bet-btn--request-cashout');
if (!req) return 'no-request';
try { req.click(); } catch (e) { return 'click-fail'; }
return 'clicked';
""", bet_id)
                except Exception:
                    hit = 'err'
                if hit == 'no-request':
                    return None
                if hit == 'clicked':
                    clicked = True
                    break
                time.sleep(0.4)
            if not clicked:
                return None
            for _ in range(10):
                time.sleep(0.5)
                try:
                    val = driver.execute_script(r"""
var id = arguments[0];
var cards = document.querySelectorAll('.bet-container');
var c = null;
for (var i = 0; i < cards.length; i++) {
    var e = cards[i].querySelector('.bet_id');
    if (e && (e.innerText || '').indexOf(id) >= 0) { c = cards[i]; break; }
}
if (!c) return '';
var amt = c.querySelector('[data-qa="cashout-amount"]');
return amt ? (amt.innerText || '') : '';
""", bet_id)
                except Exception:
                    val = ''
                m = re.search(r"([0-9][0-9,]*\.?[0-9]{0,2})", val or "")
                if m:
                    return round(float(m.group(1).replace(",", "")), 2)
                try:
                    expired = driver.execute_script(r"""
var id = arguments[0];
var cards = document.querySelectorAll('.bet-container');
var c = null;
for (var i = 0; i < cards.length; i++) {
    var e = cards[i].querySelector('.bet_id');
    if (e && (e.innerText || '').indexOf(id) >= 0) { c = cards[i]; break; }
}
if (!c) return 1;
return c.querySelector('.bet-btn--cashout-countdown') ? 0 : 1;
""", bet_id)
                except Exception:
                    expired = 1
                if expired:
                    # countdown lapsed -> request a fresh quote and read again
                    try:
                        driver.execute_script(r"""
var id = arguments[0];
var cards = document.querySelectorAll('.bet-container');
for (var i = 0; i < cards.length; i++) {
    var e = cards[i].querySelector('.bet_id');
    if (e && (e.innerText || '').indexOf(id) >= 0) {
        var r = cards[i].querySelector('.bet-btn--request-cashout');
        if (r) r.click();
        break;
    }
}
""", bet_id)
                    except Exception:
                        pass
        except Exception:
            return None
        return None

    def _confirm_cashout(self, driver, bet_id: str) -> bool:
        """Click the exposed confirm-cash-out control (data-qa="cashout-confirm").
        Returns True when the cash-out was accepted (offer control disappears)."""
        try:
            from selenium.webdriver.common.alert import Alert
        except Exception:
            Alert = None
        try:
            for _ in range(3):
                try:
                    r = driver.execute_script(r"""
var id = arguments[0];
var cards = document.querySelectorAll('.bet-container');
var c = null;
for (var i = 0; i < cards.length; i++) {
    var e = cards[i].querySelector('.bet_id');
    if (e && (e.innerText || '').indexOf(id) >= 0) { c = cards[i]; break; }
}
if (!c) return 'no-card';
var cf = c.querySelector('[data-qa="cashout-confirm"]');
if (!cf) return 'no-confirm';
var amt = cf.querySelector('[data-qa="cashout-amount"]');
(amt || cf).click();
return 'clicked';
""", bet_id)
                except Exception:
                    r = 'err'
                if r == 'clicked':
                    time.sleep(2.0)
                    if Alert is not None:
                        try:
                            Alert(driver).accept()
                        except Exception:
                            pass
                    for _ in range(8):
                        time.sleep(0.75)
                        try:
                            gone = driver.execute_script(r"""
var id = arguments[0];
var cards = document.querySelectorAll('.bet-container');
var c = null;
for (var i = 0; i < cards.length; i++) {
    var e = cards[i].querySelector('.bet_id');
    if (e && (e.innerText || '').indexOf(id) >= 0) { c = cards[i]; break; }
}
if (!c) return 1;
return (c.querySelector('[data-qa="cashout-confirm"], [data-qa="cashout-amount"]')) ? 0 : 1;
""", bet_id)
                        except Exception:
                            gone = 1
                        if gone:
                            return True
                    return True   # processed even if the card stayed visible
                if r == 'no-confirm':
                    self._probe_cashout_offer(driver, bet_id)
                    time.sleep(1.0)
                else:
                    time.sleep(0.6)
        except Exception:
            pass
        return False

    def _cashout_decision(self, offer: float, stake: float, possible_win: float,
                          won: int, pending: int, bad: int,
                          mins_to_last_ko=None) -> tuple:
        """Systematic cash-out policy (2026-09-26). Returns (take, reason).

        Ordered from most to least defensive. The governing quantity is the
        STAKE, not the possible win:

        1. Below CASHOUT_MIN_RECOVERY of the stake → never take it. Selling at a
           70% loss to "stop the bleeding" converts a recoverable position into a
           certain loss, and the ledger's largest ROI drains started exactly
           this way.
        2. Offer banks stake x CASHOUT_PROFIT_LOCK or better → take it. This is
           the whole point of cash-out: a guaranteed profit on a bet that can
           still lose, on an accumulator, at any time.
        3. Last leg imminent and offer still returns most of the stake → take it.
           With kick-off this close the remaining legs' variance dominates any
           edge the model claims, so the risk premium we would demand is gone.
        4. The bet is running and the offer is a large slice of what is still
           achievable → bank it.
        """
        try:
            o = float(offer or 0.0)
            s = float(stake or 0.0)
            if o <= 0 or s <= 0:
                return False, "no value offered"
            rec = o / s
            if rec < self.CASHOUT_MIN_RECOVERY:
                return False, (f"only {rec:.0%} of stake back — refusing to "
                               f"crystallise a loss (floor "
                               f"{self.CASHOUT_MIN_RECOVERY:.0%})")
            if rec >= self.CASHOUT_PROFIT_LOCK:
                return True, (f"banks {rec:.0%} of stake "
                              f"(KES {o:,.2f} vs KES {s:,.2f}) — locked profit, "
                              f"the remaining {pending} leg(s) cannot improve on this")
            try:
                late = mins_to_last_ko is not None and \
                    float(mins_to_last_ko) <= self.CASHOUT_LATE_WINDOW_MIN
            except (TypeError, ValueError):
                late = False
            if late and rec >= self.CASHOUT_LATE_RECOVERY:
                return True, (f"last leg within {self.CASHOUT_LATE_WINDOW_MIN}m and "
                              f"{rec:.0%} of stake back — variance now dominates, "
                              f"locking {rec:.0%}")
            pw = float(possible_win or 0.0)
            if pw > 0:
                wr = o / pw
                if wr >= self.CASHOUT_WIN_FRACTION:
                    return True, (f"{wr:.0%} of the remaining possible win "
                                  f"(KES {o:,.2f}) with {won}/{won+pending+bad} legs won")
            return False, (f"{rec:.0%} of stake back, below the "
                           f"{self.CASHOUT_PROFIT_LOCK:.2f}x profit lock and not "
                           f"running enough — holding")
        except Exception:
            return False, "cash-out decision failed, holding"

    def _auto_cashout_pass(self, driver, rows: list, gui_callback=None):
        """Smart cash-out pass: for each active ledger bet where the site offers
        a cash-out, read per-leg status, then decide under owner policy:
          • any finished leg that didn't win → no cash-out (slip wounded)
          • need ≥1 won leg AND ≥1 leg still playing (won ≥ pending)
          • cash out when offer ≥ threshold × possible win
        Emits a per-game "done / won / pending" line for the log."""
        try:
            if not getattr(self, "auto_cashout_enabled", True):
                return
            cashout_rows = [r for r in rows
                            if r.get("cashout_available")
                            and (r.get("legs") or 0) >= 2]
            if not cashout_rows:
                return
            if not getattr(self, "_cashout_probed", None):
                self._cashout_probed = {}
            now = time.time()
            for lid, cr in list({str(r.get("id")): r
                                 for r in cashout_rows}.items())[:6]:
                local_b = next((b for b in (getattr(self, "_bets", None) or [])
                                if str(b.get("id") or "") == lid), None)
                if local_b is None or (local_b.get("status") or "") not in ("active", "unconfirmed"):
                    continue
                if now - (self._cashout_probed.get(lid, 0.0)) < 600:
                    continue     # don't hammer the account faster than once/10 min
                self._cashout_probed[lid] = now
                detail = self._read_bet_leg_details(driver, lid, expand=True,
                                                    expected_legs=int(cr.get("legs") or 0))
                if not detail.get("leg_rows"):
                    continue
                leg_line = " | ".join(
                    f"{l.get('game') or '?'}->{('WON' if l.get('won') else ('done' if l.get('finished') else 'pend'))}"
                    for l in detail.get("leg_rows"))
                self._emit_direct(gui_callback, f"💱 Bet #{lid}: " + leg_line)
                pw = detail.get("possible_win") or 0
                won, pending, bad = (detail.get("won") or 0,
                                     detail.get("pending") or 0,
                                     detail.get("finished_not_won") or 0)
                total = won + pending + bad
                if bad > 0 and pending == 0 and won == 0:
                    if (local_b.get("status") or "") != "lost":
                        local_b["status"] = "lost"
                        local_b["settled_at"] = datetime.now().isoformat(timespec="seconds")
                        self._save_ledger()
                        try:
                            self._record_settled_stats(local_b)
                        except Exception:
                            pass
                    self._emit_direct(gui_callback,
                        f"❌ Bet #{lid}: all legs finished, 0 wins — pre-settled LOST "
                        f"(stake KES {(cr.get('stake') or 0):,.2f})")
                    continue
                if bad > 0:
                    self._emit_direct(gui_callback,
                        f"⛔ Bet #{lid}: a finished leg did NOT win — cash-out abandoned "
                        f"(won {won}, playing {pending}, finished-lost {bad})")
                    continue
                if pending < 1 or won < 1 or won < pending:
                    self._emit_direct(gui_callback,
                        f"⏸ Bet #{lid}: {won} ok / {pending} still playing of {total} — "
                        f"holding off")
                    continue
                offer = self._probe_cashout_offer(driver, lid)
                if not offer:
                    self._emit_direct(gui_callback,
                        f"💱 Bet #{lid}: no cash-out value shown (won {won}, pending "
                        f"{pending}) — retry next pass")
                    continue
                ratio = offer / pw if pw else 0.0
                _stake = float(local_b.get("stake") or cr.get("stake") or 0.0)
                # Time pressure on the surviving legs — the cash-out policy needs
                # to know how close the last playable leg is, because near
                # kick-off the right move is to stop holding.
                _mins_left = None
                try:
                    _pend = [l for l in detail.get("leg_rows")
                             if not (l.get("won") or l.get("finished"))]
                    _ks = [l.get("ko_epoch") for l in _pend if l.get("ko_epoch")]
                    if _ks:
                        _mins_left = (min(float(k) for k in _ks) - time.time()) / 60.0
                except Exception:
                    _mins_left = None
                _take, _why = self._cashout_decision(
                    offer, _stake, pw, won, pending, bad, _mins_left)
                if _take:
                    self._emit_direct(gui_callback,
                        f"dY'� AUTO CASH-OUT Bet #{lid}: KES {offer:,.2f} on a KES {_stake:,.2f} "
                        f"stake — {_why}")
                    if self._confirm_cashout(driver, lid):
                        local_b["status"] = "cashed_out"
                        local_b["settled_at"] = datetime.now().isoformat(timespec="seconds")
                        local_b["cashed_out_amount"] = offer
                        self._save_ledger()
                        try:
                            self._record_settled_stats(local_b)
                        except Exception:
                            pass
                        self._emit_direct(gui_callback,
                            f"�o. CASHED OUT Bet #{lid}: +KES {offer:,.2f} banked "
                            f"after {won}/{total} legs won (left: {pending})")
                    else:
                        self._emit_direct(gui_callback,
                            f"�s��,? Cash-out confirm on Bet #{lid} FAILED — check the app")
                else:
                    self._emit_direct(gui_callback,
                        f"�?, Bet #{lid}: cash-out KES {offer:,.2f} — holding, {_why}")
        except Exception:
            pass

    def _settle_shadow_bets(self, site_rows: list, gui_callback=None):
        """Score shadow (no-funds planned) bets against the live bet-history rows.

        A shadow bet has a list of game IDs and market picks. We can't match it to
        a bet-history row (it was never placed), but we can check whether its legs
        would have won using the site rows as a proxy for settled results:

        - Any site row with the same leg count and odds product within ±5% gives
          us the overall outcome direction (won/lost).
        - That outcome is then scored into `_record_settled_stats` just like a real
          settled bet so the learning engine improves continuously.

        Shadow bets older than 24 h that still haven't been scorable are dropped
        (game is long over, no proxy row found — data not useful any more).
        """
        if not site_rows:
            return
        now_ts = time.time()
        cutoff = now_ts - 86400.0  # 24 h
        changed = False
        for b in getattr(self, "_bets", []) or []:
            if b.get("status") != "shadow":
                continue
            # Drop stale unscorable shadows
            try:
                placed_ts = datetime.fromisoformat(b.get("placed_at") or "").timestamp()
            except Exception:
                placed_ts = 0.0
            if placed_ts < cutoff:
                b["status"] = "shadow_expired"
                b["settled_at"] = datetime.now().isoformat(timespec="seconds")
                changed = True
                continue
            # Try to find a matching real-money row from another account with the
            # same leg count and a similar product odds value (±8%)
            shadow_odds = float(b.get("odds") or 0)
            shadow_legs = int(b.get("legs") or 0)
            best_row = None
            best_score = None
            for r in site_rows:
                if r.get("legs") != shadow_legs:
                    continue
                row_odds_approx = (r.get("win") or 0.0) / max(r.get("stake") or 1.0, 0.01)
                if shadow_odds > 0 and abs(row_odds_approx - shadow_odds) / shadow_odds > 0.08:
                    continue
                row_status = self._normalize_bet_status(r.get("status") or "")
                if row_status not in ("won", "lost"):
                    continue
                score = abs(row_odds_approx - shadow_odds)
                if best_score is None or score < best_score:
                    best_score = score
                    best_row = (r, row_status)
            if best_row is None:
                continue
            _r, outcome = best_row
            b["status"] = f"shadow_{outcome}"   # "shadow_won" or "shadow_lost"
            b["settled_at"] = datetime.now().isoformat(timespec="seconds")
            changed = True
            # Feed into the learning engine — convert to a pseudo-settled bet
            pseudo = dict(b)
            pseudo["status"] = outcome   # calibrator needs "won" or "lost"
            pseudo["stake"] = 0.0        # no real money — don't pollute ROI
            try:
                self._record_settled_stats(pseudo)
            except Exception:
                pass
            arrow = "🔮✅" if outcome == "won" else "🔮❌"
            self._emit_direct(gui_callback,
                              f"{arrow} Shadow bet ({shadow_legs}L @x{shadow_odds:.2f}) would have "
                              f"{'WON' if outcome == 'won' else 'LOST'} — outcome scored into "
                              "learning engine (no real money involved)")
        if changed:
            self._save_ledger()

    def fetch_bet_history_live(self, phone: str, password: str,
                               gui_callback=None, date_filter: str = None) -> dict:
        """Open the SportPesa Bet History page and surface a dated breakdown.

        Navigates to the history page, scrolls to load all rows, then groups
        by date and status so the user can see exactly what was placed today,
        how many are active, won, or lost — direct from the site.

        *date_filter*: 'YYYY-MM-DD'. Defaults to today.
        """
        driver = None
        owned = False
        today = date_filter or datetime.now().strftime("%Y-%m-%d")
        try:
            self._emit_direct(gui_callback,
                              f"📋 Fetching live bet history for {phone} (date: {today})...")
            driver, owned = self._borrow_account_browser(
                phone, gui_callback=gui_callback, force_visible=False,
                mobile=False, headless=True, capture_perf=False, minimize=True)
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            if not self._session_is_live(driver, deep_check=False):
                self._emit_direct(gui_callback, "⚠️ Login failed — cannot fetch live history.")
                return {"date": today, "error": "login_failed"}

            self._safe_get(driver, self.BETS_HISTORY_URL)
            time.sleep(1.5)
            rows = self._extract_bet_history(driver, max_scroll=10)

            if not rows:
                self._emit_direct(gui_callback, "📋 No bet rows returned from history page.")
                return {"date": today, "total": 0, "active": 0, "won": 0,
                        "lost": 0, "void": 0, "bets": [],
                        "summary_line": "No bets found."}

            # Filter to the requested date
            today_rows = []
            for r in rows:
                row_date = (r.get("date") or "")
                try:
                    for fmt in ("%d/%m/%y %H:%M", "%d/%m/%Y %H:%M"):
                        try:
                            d = datetime.strptime(row_date, fmt)
                            if d.strftime("%Y-%m-%d") == today:
                                today_rows.append(r)
                            break
                        except ValueError:
                            continue
                except Exception:
                    pass

            # Sync ledger while we have the browser open
            try:
                self._monitor_and_sync_winnings(driver, gui_callback=gui_callback)
            except Exception:
                pass

            active = won = lost = void_c = 0
            total_staked = possible_return = 0.0
            enriched = []
            for r in today_rows:
                st = self._normalize_bet_status(r.get("status") or "")
                stake = float(r.get("stake") or 0)
                win   = float(r.get("win") or 0)
                odds  = round(win / stake, 2) if stake > 0 and win > 0 else 0.0
                total_staked    += stake
                possible_return += win
                if st == "won":    won += 1
                elif st == "lost": lost += 1
                elif st == "void": void_c += 1
                else:              active += 1
                enriched.append({"id": r.get("id") or "—", "date": r.get("date") or "",
                                  "legs": r.get("legs") or 0, "stake": stake,
                                  "win": win, "odds": odds, "status": st})

            net = sum(r["win"] for r in enriched if r["status"] == "won") - total_staked
            summary = (
                f"📅 {today}: {len(today_rows)} bet(s) | "
                f"🏆 {won} won | ❌ {lost} lost | ↩️ {void_c} void | ⏳ {active} live | "
                f"staked KES {total_staked:,.2f} | net {net:+,.2f}"
            )
            self._emit_direct(gui_callback, summary)
            if enriched:
                self._emit_direct(gui_callback,
                                  "  Bet ID       Date              Legs  Stake      Odds  Status")
                for r in enriched:
                    icon = {"won": "🏆", "lost": "❌", "void": "↩️"}.get(r["status"], "⏳")
                    self._emit_direct(
                        gui_callback,
                        f"  {str(r['id']):<13} {r['date']:<17} "
                        f"{r['legs']:<5} KES {r['stake']:>6.0f}  "
                        f"x{r['odds']:>5.2f}  {icon} {r['status']}")
            return {"date": today, "total": len(today_rows), "active": active,
                    "won": won, "lost": lost, "void": void_c,
                    "total_staked": round(total_staked, 2),
                    "possible_return": round(possible_return, 2),
                    "net": round(net, 2), "bets": enriched, "summary_line": summary}
        except Exception as e:
            self._emit_direct(gui_callback, f"⚠️ Live history fetch failed: {str(e)[:120]}")
            return {"date": today, "error": str(e)[:80]}
        finally:
            try:
                if driver is not None and owned:
                    driver.quit()
            except Exception:
                pass

    def sync_winnings_now(self, phone, password, gui_callback=None) -> dict:
        """Manual win-sync: open Bet History, settle any finished bets, quit.

        Also force-settles any bet that is still 'active' but was placed
        more than 48 hours ago and appears nowhere in the bet history — those
        bets are almost certainly settled on the site but just weren't matched
        (ID mismatch, time format, etc.). They are marked 'lost' conservatively
        so the ledger doesn't fill up with stale active entries.
        """
        driver = None
        owned = False
        try:
            self._emit_direct(gui_callback, f"🔄 Syncing winnings for {phone}...")
            driver, owned = self._borrow_account_browser(
                phone, gui_callback=gui_callback, force_visible=False,
                mobile=False, headless=True, capture_perf=False, minimize=True)
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            if not self._session_is_live(driver, deep_check=False):
                self._emit_direct(gui_callback, "⚠️ Could not verify login for win-sync.")
                return {"status": "error", "summary": self._ledger_summary()}
            try:
                self._backfill_bet_ids(driver, gui_callback=gui_callback)
            except Exception as e:
                self._emit_direct(gui_callback, f"⚠️ ID backfill skip: {str(e)[:80]}")
            summary = self._monitor_and_sync_winnings(driver, gui_callback=gui_callback)

            # ── Import bets from site that don't exist in the local ledger ──
            # Happens when a previous session placed bets but didn't save to
            # ledger (e.g. crash, restart, ledger wipe). Finds them by matching
            # site Bet IDs against the ledger and imports the missing ones.
            try:
                site_rows = self._extract_bet_history(driver, max_scroll=5)
                existing_ids = {str(b.get("id") or "") for b in (getattr(self, "_bets", None) or []) if b.get("id")}
                imported = 0
                for r in site_rows:
                    row_id = str(r.get("id") or "").strip()
                    if not row_id or row_id in existing_ids:
                        continue
                    st = self._normalize_bet_status(r.get("status") or "")
                    stake = float(r.get("stake") or 0)
                    win   = float(r.get("win") or 0)
                    # Parse date
                    placed_at = ""
                    for fmt in ("%d/%m/%y %H:%M", "%d/%m/%Y %H:%M"):
                        try:
                            placed_at = datetime.strptime(r.get("date") or "", fmt).isoformat(timespec="seconds")
                            break
                        except ValueError:
                            continue
                    legs = int(r.get("legs") or 0)
                    # Markets/probs/games from the engine's own ledger when
                    # this site bet is one of ours (id match on bet_id /
                    # short_bet_id). Empty only when the engine never placed
                    # it (a genuinely manual bet from the phone app).
                    _enr = self._new_engine_enrich(row_id)
                    # Reconstruct a minimal ledger entry
                    import json as _js
                    entry = {
                        "id": row_id,
                        "phone": phone,
                        "placed_at": placed_at,
                        "legs": legs,
                        "stake": stake,
                        "odds": round(win / stake, 2) if stake > 0 and win > 0 else 0.0,
                        "possible_win": win,
                    }
                    # Legs fallback: the site history sometimes ships legs=0
                    # (measured 2026-10-26 on the singles) - the engine's own
                    # enrichment knows better, so the recipe key and every
                    # legs-counted table don't file a fake "0L" recipe.
                    if legs <= 0:
                        legs = int(len(_enr.get("leg_odds") or []) or
                                   len(_enr.get("markets") or []) or 0)
                        entry["legs"] = legs
                    # The real market mix must ride in the recipe key: with the
                    # hard-coded "-" the recorder could never tell WHICH market
                    # combination won or drained the account (measured: every
                    # real recipe filed as mix "-", signature learning was
                    # blind because the site rows WERE enriched above).
                    _ww_mix = "-".join(sorted(set(
                        _enr.get("markets") or []))) or "-"
                    entry["recipe"] = {
                        "legs": legs, "band": self._band_of(win / stake if stake > 0 and win > 0 else 0),
                        "lead": "-", "mix": _ww_mix}
                    entry.update({
                        "markets": _enr.get("markets") or [],
                        "probs": _enr.get("probs") or [],
                        "status": st,
                        "settled_at": placed_at if st in ("won", "lost", "void") else None,
                        "won_amount": win if st == "won" else None,
                        "imported": True,
                    })
                    if _enr.get("games"):
                        entry["games"] = _enr["games"]
                    if _enr.get("leg_names"):
                        entry["leg_names"] = _enr["leg_names"]
                    # leg_odds + legs_meta: MEASURED 2026-10-15 - the import
                    # dropped both, so every settled row hit the recorder's
                    # 0.5 probability placeholder and its league fell into
                    # "Unknown" even though the engine's ledger has them.
                    if _enr.get("leg_odds"):
                        entry["leg_odds"] = _enr["leg_odds"]
                    if _enr.get("legs_meta"):
                        entry["legs_meta"] = _enr["legs_meta"]
                    if getattr(self, "_bets", None) is None:
                        self._bets = []
                    self._bets.append(entry)
                    existing_ids.add(row_id)
                    imported += 1
                    if st in ("won", "lost"):
                        self._record_settled_stats(entry)
                if imported > 0:
                    getattr(self, "_daily_bucket_cache", {}).clear()
                    self._save_ledger()
                    summary = self._ledger_summary()
                    self._emit_direct(gui_callback,
                                      f"📥 Imported {imported} bet(s) from site that were missing from local ledger")
            except Exception as _ie:
                self._emit_direct(gui_callback, f"⚠️ Import skip: {str(_ie)[:80]}")

            # ── Stale active bet cleanup ──────────────────────────────────
            # Any bet still "active" that was placed 48+ hours ago is almost
            # certainly settled. If it has a bet ID we trust the site didn't
            # return it (probably expired from history view). Mark conservative.
            now = datetime.now()
            cutoff_hours = 48
            stale = []
            for b in getattr(self, "_bets", []) or []:
                if str(b.get("status") or "").startswith("shadow"):
                    continue
                if b.get("status") not in ("active", "unconfirmed", None, ""):
                    continue
                try:
                    placed = datetime.fromisoformat(b.get("placed_at") or "")
                    age_h = (now - placed).total_seconds() / 3600.0
                except Exception:
                    age_h = 0
                if age_h >= cutoff_hours:
                    stale.append(b)
            if stale:
                self._emit_direct(gui_callback,
                                  f"⚠️ {len(stale)} bet(s) still 'active' after {cutoff_hours}h "
                                  "— marking as lost (site history didn't show them settled).")
                for b in stale:
                    b["status"] = "lost"
                    b["settled_at"] = now.isoformat(timespec="seconds")
                    b["auto_settled"] = True   # flag so we know this was automatic
                    self._record_settled_stats(b)
                getattr(self, "_daily_bucket_cache", {}).clear()
                self._save_ledger()
                # Re-run summary after cleanup
                summary = self._ledger_summary()
                self._emit_direct(gui_callback,
                                  f"📊 After cleanup — won {summary['won']} | "
                                  f"lost {summary['lost']} | active {summary['active']} | "
                                  f"net {summary['net_profit']:+,.2f}")

            return {"status": "success", "summary": summary}
        except Exception as e:
            msg = str(e)
            if ("Timed out receiving message from renderer" in msg or "renderer" in msg.lower()
                    or "script timeout" in msg):
                self._emit_direct(gui_callback, "⏸️ Win-sync: renderer busy — skipped, will retry next cycle.")
            else:
                self._emit_direct(gui_callback, f"⚠️ Win-sync failed: {msg[:120]}")
            return {"status": "error", "summary": self._ledger_summary()}
        finally:
            try:
                if driver is not None and owned:
                    driver.quit()
            except Exception:
                pass

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

    def _near_term_cutoff(self) -> datetime:
        """Owner rule (2026-09-22): only today's + tomorrow's fixtures are bet.
        The extended board reaches 20+ days out; their lines get suspended or
        drift to garbage before kick-off, so far-future legs just burn rounds
        with 'Not valid (selection suspended/removed)'. A game whose start is
        past the end of tomorrow never enters the pick pool."""
        return datetime.now().replace(hour=23, minute=59, second=59, microsecond=0) + timedelta(days=1)

    def _is_recent_enough(self, g) -> bool:
        """True when g has no start time or is within the today+tomorrow window."""
        try:
            gst = g.get("start")
            return gst is None or gst <= self._near_term_cutoff()
        except Exception:
            return True

    def _mark_leg_suspended(self, gid, market, cooldown_s: int = 3600):
        """Remember a leg (gid+market) the book flagged suspended / 'Not valid'
        so rebuilders skip it until the cooldown clears. Never raises."""
        try:
            key = f"{gid}|{market}"
            until = time.time() + float(cooldown_s)
            cur = self._suspended_until.get(key, 0.0)
            if until > cur:
                self._suspended_until[key] = until
            # Prune so the dict never grows unbounded across hours of runs.
            now = time.time()
            stale = [k for k, v in self._suspended_until.items() if v <= now]
            for k in stale[:200]:
                self._suspended_until.pop(k, None)
        except Exception:
            pass

    def _leg_suspended_till(self, gid, market) -> float:
        """Epoch ts until which this leg is benched (0.0 = not benched)."""
        try:
            return float(self._suspended_until.get(f"{gid}|{market}", 0.0))
        except Exception:
            return 0.0

    def _bench_slip_legs(self, legs, cooldown_s: int = 3600):
        """Bench every leg in a slip the book just flagged 'Not valid'. legs is a
        list of (odds, name, gid, market, prob) tuples; gid/market keep the same
        gid|market key the option loop consults. Safe on partial tuples too."""
        try:
            if not legs:
                return
            for leg in legs:
                if not isinstance(leg, (tuple, list)) or len(leg) < 4:
                    continue
                gid = str(leg[2] or "")
                market = str(leg[3] or "")
                if gid and market:
                    self._mark_leg_suspended(gid, market, cooldown_s=cooldown_s)
        except Exception:
            pass

    def _ko_hhmm(self, dt) -> str:
        """'HH:MM' kick-off label, or '' when unknown."""
        try:
            return dt.strftime("%H:%M") if dt else ""
        except Exception:
            return ""

    def _ko_end_hhmm(self, dt) -> str:
        """Estimated full-time 'HH:MM' (kick-off + ~105 min: 90' + half-time + stoppage),
        or '' when unknown. An estimate, not a guaranteed finish time."""
        try:
            if not dt:
                return ""
            return (dt + timedelta(minutes=105)).strftime("%H:%M")
        except Exception:
            return ""

    def _ko_epoch(self, dt) -> int:
        """Kick-off unix epoch (0 when unknown)."""
        try:
            return int(dt.timestamp()) if dt else 0
        except Exception:
            return 0

    def _ko_session_bucket(self, dt) -> str:
        """'day' / 'night' kick-off session (used for the 10+10 day-night split)."""
        try:
            if not dt:
                return "day"
            h = dt.hour
            return "night" if h >= 18 else "day"
        except Exception:
            return "day"

    def _scroll_to_load_more_games(self, driver, max_scrolls: int = 6,
                                   gui_callback=None) -> int:
        """Crawl the listing: scroll the page + inner containers to trigger the
        infinite-scroll / pagination, so we capture as many placeable games as possible.

        Returns the number of .event-row rows visible after crawling.
        """
        for i in range(max_scrolls):
            driver.execute_script(r"""
if (document.body) window.scrollTo(0, document.body.scrollHeight);
var scr = document.querySelectorAll('.event-sports__row, .event-sports__sticky, [class*="event-list"], [class*="scroll"], .data-live-scroll, main, [role="main"], .container, .content, .event-tabs-holder__content');
for (var s = 0; s < scr.length; s++) {
    var el = scr[s];
    if (el && el.scrollHeight > el.clientHeight + 40) {
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
    // Team containers in the current template (.event-team / competitors QA).
    var teamEls = row.querySelectorAll('.event-team, [data-qa="prematch-event-competitors"]');
    var teamList = [];
    for (var t = 0; t < teamEls.length; t++) {
        var tv = (teamEls[t].innerText || teamEls[t].getAttribute('title') || '').replace(/\s+/g, ' ').trim();
        if (tv) teamList.push(tv);
    }
    var names = row.querySelectorAll('.event-names .event-text');
    var nameList = [];
    var skip = { '3 WAY': 1, '2 WAY': 1, '1X2': 1, 'MATCH': 1, 'MATCH WINNER': 1,
                 'OVER/UNDER': 1, 'OVER': 1, 'UNDER': 1, 'BOTH TEAMS TO SCORE': 1,
                 'HANDICAP': 1, 'DOUBLE CHANCE': 1, 'FIRST TEAM TO SCORE': 1,
                 'DRAW': 1, 'YES': 1, 'NO': 1, '1': 1, '2': 1, 'X': 1,
                 'HOME': 1, 'AWAY': 1 };
    function firstLine(v) { return (v || '').split(/[\n\r]+/)[0].trim(); }
    function isLabel(v) {
        var up = firstLine(v).toUpperCase();
        return skip[up] || up.indexOf('==') >= 0;
    }
    for (var n = 0; n < names.length; n++) {
        var v = (names[n].innerText || '').trim();
        if (v && !names[n].classList.contains('placeholder') && !isLabel(v)) nameList.push(v);
    }
    // Prefer real team containers; if a container's value looks like a market
    // outcome (e.g. "1 or X", "X or 2", "NEITHER") treat it as junk.
    function isOutcomeLike(v) {
        var up = String(v).toUpperCase().replace(/\s+/g, ' ');
        if (/^\d+$/.test(up) || up === 'X' || up === '1X' || up === 'X2' || up === '12') return true;
        if (up.indexOf(' OR ') >= 0 || up.indexOf('AND') >= 0) return true;
        if (up.indexOf('NEITHER') >= 0) return true;
        return false;
    }
    var realTeams = [];
    for (var t2 = 0; t2 < teamList.length; t2++) {
        if (!isOutcomeLike(teamList[t2])) realTeams.push(teamList[t2]);
    }
    var home = realTeams.length > 0 ? realTeams[0] : (nameList.length > 0 ? nameList[0] : '');
    var away = realTeams.length > 1 ? realTeams[1] : (nameList.length > 1 ? nameList[1] : '');
    if (!home && !away) {
        var filtered = [];
        var all = row.querySelectorAll('.event-text');
        for (var a = 0; a < all.length && filtered.length < 2; a++) {
            var el = all[a];
            var v2 = (el.innerText || '').trim();
            if (!v2 || el.classList.contains('placeholder')) continue;
            if (isLabel(v2)) continue;
            if (isOutcomeLike(v2)) continue;
            filtered.push(v2);
        }
        home = filtered.length > 0 ? filtered[0] : '';
        away = filtered.length > 1 ? filtered[1] : '';
    }
    if (!home && !away) continue;

    // Pull odds per market from the row's .event-market blocks
    var markets = row.querySelectorAll('.event-market');
    var homeOdds = '', bttsYes = '', over25 = '', over15 = '';
    var h3 = [], btts2 = [], ou2 = [], ou15 = [];
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
            // Also capture Over 1.5 if this is a different O/U line
            if (nm.indexOf('1.5') >= 0 && !over15) { over15 = oddAt(0); collect(ou15, 2); }
        } else if (nm.indexOf('1.5') >= 0 && nm.indexOf('OVER') >= 0) {
            if (!over15) over15 = oddAt(0);
            collect(ou15, 2);
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
        over15: over15,
        h3: h3,
        btts2: btts2,
        ou2: ou2,
        ou15: ou15
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
                "over_15": _f("over15"),
                "h3": _fl("h3"),
                "btts": _fl("btts2"),
                "ou": _fl("ou2"),
                "ou15": _fl("ou15"),
                # ── Extended markets derived from the same arrays ────────
                "draw_odds":    _fl("h3")[1] if len(_fl("h3")) > 1 else None,
                "away_odds":    _fl("h3")[2] if len(_fl("h3")) > 2 else None,
                "btts_no":      _fl("btts2")[1] if len(_fl("btts2")) > 1 else None,
                "under_25":     _fl("ou2")[1] if len(_fl("ou2")) > 1 else None,
                "under_15":     _fl("ou15")[1] if len(_fl("ou15")) > 1 else None,
                "start": self._parse_sportpesa_kickoff(g.get("rawTime")),
                "start_raw": g.get("rawTime") or "",
                # ── Kickoff-time presentation + grouping fields ──────────
                "ko_label":  self._ko_hhmm(self._parse_sportpesa_kickoff(g.get("rawTime"))),
                "ko_epoch":  self._ko_epoch(self._parse_sportpesa_kickoff(g.get("rawTime"))),
                "ko_session": self._ko_session_bucket(self._parse_sportpesa_kickoff(g.get("rawTime"))),
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

    def _open_stats_then_close(self, driver, game_id, home: str = "", away: str = "",
                               gui_callback=None, read_timeout: float = 6.0):
        """Per-leg Statistics routine: find the game row, open its H2H/Stats
        overlay, EXTRACT enrichment data (injuries, suspensions, weather, venue,
        referee) from the page, cache it for downstream pick quality, ALSO parse
        and cache both teams' form when team names are provided, then close the
        overlay and return to the market list. Fully guarded — a failure just
        skips stats and never blocks the market click.

        Returns True when stats were opened AND at least one useful field of
        enrichment was extracted; False on any miss/failure."""
        found_enrichment = False
        try:
            before = len(driver.window_handles)
            gid_str = str(game_id)
            clicked = driver.execute_script(r"""
var gid = arguments[0];
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
var row = null;
for (var r = 0; r < rows.length; r++) {
    if ((rows[r].innerText || '').indexOf('ID: ' + gid) >= 0 && rows[r].offsetParent !== null) {
        row = rows[r]; break;
    }
}
if (!row) return 'norow';
var cands = row.querySelectorAll('button, a, span, i, div, [ng-click]');
for (var i = 0; i < cands.length; i++) {
    var el = cands[i];
    var hay = (((el.getAttribute('ng-click') || '') + ' ' + (el.getAttribute('class') || '') + ' ' +
                (el.getAttribute('title') || '')).toLowerCase());
    if (/openbetradarh2h|stats|h2h|preview|analysis/.test(hay)) {
        try {
            if (el.offsetParent === null) continue;
            el.scrollIntoView({block: 'center'});
            el.click();
            return 'clicked';
        } catch (e) { continue; }
    }
}
return 'noicon';
""", gid_str)
            if clicked != "clicked":
                return False
            deadline = time.time() + read_timeout
            content = ""
            in_new_tab = False
            while time.time() < deadline:
                try:
                    handles = driver.window_handles
                    if len(handles) > before and not in_new_tab:
                        driver.switch_to.window(handles[-1])
                        in_new_tab = True
                        time.sleep(1.0)
                    txt = driver.execute_script(
                        "return (document.body && document.body.innerText) || '';") or ""
                    if ("Overall Form" in txt or re.search(r"\bForm\b", txt)
                            or "injury" in txt.lower() or "weather" in txt.lower()):
                        content = txt
                        if len(content) > 400:
                            break
                except Exception:
                    break
                time.sleep(0.7)
            if in_new_tab and not content:
                try:
                    content = driver.execute_script(
                        "return (document.body && document.body.innerText) || '';") or ""
                except Exception:
                    content = ""
            if not content:
                try:
                    content = driver.execute_script(
                        "return (document.body && document.body.innerText) || '';") or ""
                except Exception:
                    content = ""
            if content:
                enr = self._parse_enrichment_from_text(content, home_hint=home,
                                                    away_hint=away)
                if enr and (enr.get("injuries") or enr.get("suspensions")
                            or enr.get("weather") or enr.get("venue")
                            or enr.get("referee") or enr.get("lineups")
                            or enr.get("formations")):
                    self._set_enrichment(gid_str, enr)
                    found_enrichment = True
                    if enr.get("lineups") or enr.get("formations"):
                        try:
                            _lx = len((enr.get("lineups") or {}).get("home") or []) \
                                + len((enr.get("lineups") or {}).get("away") or [])
                            self._emit_direct(
                                None,
                                f"  \U0001f9d1 LINEUPS: {_lx} named player(s), "
                                f"formations {(enr.get('formations') or {})}")
                        except Exception:
                            pass
                # Form: parse + cache both teams from the same overlay text, so
                # the NEXT selection run can tilt markets by real recent results.
                if home and away:
                    try:
                        parsed = self._parse_h2h_form(content, home, away) or {}
                        # Similar-opponent history (2026-10-05): the same
                        # overlay lists each team's recent fixtures WITH their
                        # opponents, so this reuses the page already open and
                        # costs no extra request. Stored on the enrichment
                        # record so the selector can weigh it.
                        try:
                            _rec_opp = self._parse_recent_opponents(content)
                            if _rec_opp.get("home") or _rec_opp.get("away"):
                                # LATENT-BUG FIX (2026-10-05). This wrote into a local
                                # named `result`, which does not exist in this scope, so it raised
                                # NameError and the bare `except: pass` immediately below swallowed
                                # it. That is the whole reason `recent_opponents` had stayed at 0 in
                                # the enrichment cache since it was written: the parser worked (its
                                # unit tests passed) but the result was discarded on the very next
                                # line, so the similar-opponent factor never received a single real
                                # sample from a live run. The intended target was always this
                                # method's enrichment record (`enr`), which _set_enrichment
                                # REPLACES - so we mutate it and re-store to persist the new key.
                                enr["recent_opponents"] = {
                                    "home": _rec_opp.get("home") or [],
                                    "away": _rec_opp.get("away") or [],
                                }
                                # enr was already handed to _set_enrichment
                                # above and that helper REPLACES the cache entry,
                                # so the new key only survives if we store again.
                                self._set_enrichment(gid_str, enr)
                                self._emit_direct(
                                    None,
                                    f"  \U0001f517 SIMILAR-OPPONENT HISTORY cached: "
                                    f"home {len(enr['recent_opponents']['home'])} "
                                    f"fixture(s), away "
                                    f"{len(enr['recent_opponents']['away'])} fixture(s) "
                                    f"— {home} vs {away}")
                        except Exception:
                            pass
                        e_home = parsed.get("home") or {}
                        e_away = parsed.get("away") or {}
                        if (e_home.get("n") or 0) >= 3:
                            self._cache_form_entry(home, e_home)
                        if (e_away.get("n") or 0) >= 3:
                            self._cache_form_entry(away, e_away)
                    except Exception:
                        pass
            # Close the overlay page IMMEDIATELY after the read. Leaving it open
            # while we parse/cache made a stats tab sit visibly on screen for
            # seconds per game — the rapid open/close flicker the owner reported.
            # Close first, then parse, so nothing renders behind the round.
            self._close_analysis_pages(driver, gui_callback=gui_callback)
            return True
        except Exception:
            try:
                self._close_analysis_pages(driver, gui_callback=gui_callback)
            except Exception:
                pass
            return found_enrichment

    def _scrape_game_enrichment(self, driver, game_id: str,
                                home: str = "", away: str = "",
                                gui_callback=None) -> dict:
        """Open the stats/H2H overlay for a game and extract enrichment data
        (injuries, suspensions, weather note, venue, referees) that is NOT
        available on the main listings page. When *home* and *away* team names
        are given it ALSO parses and caches both teams' form (W/D/L + Betradar
        rating) from the same overlay, so one click does the whole due-diligence
        pass the owner asks for on every slip.

        Returns a dict with whatever was found:
          {"injuries": [...], "suspensions": [...], "weather": str,
           "venue": str, "referee": str, "raw_snippet": str}
        Empty dict on any failure — never blocks a bet.
        """
        result = {}
        try:
            before = len(driver.window_handles)
            clicked = driver.execute_script(r"""
var gid = arguments[0];
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
var row = null;
for (var r = 0; r < rows.length; r++) {
    if ((rows[r].innerText || '').indexOf('ID: ' + gid) >= 0
            && rows[r].offsetParent !== null) {
        row = rows[r]; break;
    }
}
if (!row) return 'norow';
var cands = row.querySelectorAll('button,a,span,i,div,[ng-click]');
for (var i = 0; i < cands.length; i++) {
    var el = cands[i];
    var hay = (((el.getAttribute('ng-click')||'')+' '+(el.getAttribute('class')||'')+' '+
                (el.getAttribute('title')||'')).toLowerCase());
    if (/openbetradarh2h|stats|h2h|preview|analysis/.test(hay)) {
        try { if (el.offsetParent===null) continue; el.scrollIntoView({block:'center'});
              el.click(); return 'clicked'; } catch(e){ continue; }
    }
}
return 'noicon';
""", str(game_id))
            if clicked != "clicked":
                return result

            # Wait for overlay / new tab to load
            deadline = time.time() + 6.0
            content = ""
            while time.time() < deadline:
                try:
                    handles = driver.window_handles
                    if len(handles) > before:
                        driver.switch_to.window(handles[-1])
                        time.sleep(1.2)
                        content = driver.execute_script(
                            "return (document.body && document.body.innerText) || '';") or ""
                        break
                    content = driver.execute_script(
                        "return (document.body && document.body.innerText) || '';") or ""
                    if "Form" in content or "injury" in content.lower():
                        break
                except Exception:
                    break
                time.sleep(0.6)

            if content:
                result = self._parse_enrichment_from_text(content)
                # Same form parse as _open_stats_then_close — one stats click
                # feeds both the enrichment cache and the form cache.
                if home and away:
                    try:
                        parsed = self._parse_h2h_form(content, home, away) or {}
                        # Similar-opponent history (2026-10-05): the same
                        # overlay lists each team's recent fixtures WITH their
                        # opponents, so this reuses the page already open and
                        # costs no extra request. Stored on the enrichment
                        # record so the selector can weigh it.
                        try:
                            _rec_opp = self._parse_recent_opponents(content)
                            if _rec_opp.get("home") or _rec_opp.get("away"):
                                result["recent_opponents"] = {
                                    "home": _rec_opp.get("home") or [],
                                    "away": _rec_opp.get("away") or [],
                                }
                        except Exception:
                            pass
                        e_home = parsed.get("home") or {}
                        e_away = parsed.get("away") or {}
                        if (e_home.get("n") or 0) >= 3:
                            self._cache_form_entry(home, e_home)
                        if (e_away.get("n") or 0) >= 3:
                            self._cache_form_entry(away, e_away)
                    except Exception:
                        pass

            self._close_analysis_pages(driver, gui_callback=gui_callback)
            if result.get("injuries") or result.get("weather"):
                self._set_enrichment(str(game_id), result)
        except Exception:
            try:
                self._close_analysis_pages(driver, gui_callback=gui_callback)
            except Exception:
                pass
        return result

    def _stats_per_leg(self, driver, legs, gui_callback=None):
        """Due-diligence for every chosen leg: open the H2H/Stats overlay, READ
        the page, cache both teams' recent form + injury/weather enrichment, then
        close. This is the owner's "are we actually reading the stats page" check
        — it fires on EVERY slip before placement so the machine never bets a leg
        it has not studied."""
        reviewed = 0
        missing = []
        hazards = []
        for _o, name, gid, _mkt, _pr in (legs or []):
            home = away = ""
            if name and " vs " in name:
                _parts = name.split(" vs ", 1)
                home, away = _parts[0].strip(), (_parts[1].strip().split(" ")[0] if len(_parts) > 1 else "").strip()
            try:
                if self._open_stats_then_close(driver, str(gid), home=home, away=away,
                                               gui_callback=gui_callback):
                    reviewed += 1
                    enr = self._enrichment_for(str(gid))
                    if enr and (enr.get("injuries") or enr.get("suspensions")):
                        hazards.append(f"{name}: "
                                       + " ".join((enr.get("injuries") or [])[:1])
                                       + (" " + " ".join((enr.get("suspensions") or [])[:1])).strip())
                else:
                    missing.append(name)
            except Exception:
                continue
        if hazards:
            self._emit_direct(gui_callback,
                              "🩺 Due diligence (stats read per leg): " + " ⚠️ ".join(hazards[:3]))
        self._emit_direct(gui_callback,
                          f"📊 Read stats for {reviewed}/{len(legs or [])} legs"
                          + (f" — no stats icon for {len(missing)}" if missing else ""))

    def _preflight_diligence(self, driver, games, gui_callback=None,
                             budget: int = 5, timeout: float = 40.0):
        """BEFORE selection: open the stats/H2H overlay for the most promising
        candidate games and truly READ the page — caching both teams' recent
        form, injuries, suspensions & weather. The selector then has fresh
        research (not just raw odds) to judge whether each game's pick actually
        has a chance to win. This is the "take your time, make sure every game
        has a real shot" pass the owner asked for. Bounded by budget + timeout;
        never blocks — a dead browser just ends the window early."""
        emit = self._emit_direct
        if games is None or not (driver is not None and self._driver_is_usable(driver)):
            return
        t0 = time.time()
        # Rank candidates by their single best margin-corrected win probability
        # (pure odds maths, no browser) so we study the most likely legs first.
        scored = []
        for g in (games or []):
            gid = str(g.get("id") or "")
            nm = str(g.get("name") or "")
            if not gid or " vs " not in nm:
                continue
            try:
                used = self._used_games or {}
                if gid in used and (used.get(gid) or {}):
                    continue
            except Exception:
                pass
            best = 0.0
            for odds_list in (g.get("h3"), g.get("btts"), g.get("ou"), g.get("ou15")):
                ps = self._fair_win_probs(odds_list) or []
                if ps:
                    best = max(best, max(ps))
            scored.append((best, gid, nm, g))
        scored.sort(key=lambda x: x[0], reverse=True)
        studied = 0
        studied_with_hazard = 0
        vetoed = 0
        for _p, gid, nm, g in scored:
            if time.time() - t0 > timeout:
                break
            if studied >= int(budget):
                break
            # Skip games already researched fresh this session — don't re-read the
            # same overlay every round; spend the budget on games not yet studied.
            if self._enrichment_for(gid) is not None:
                studied += 1  # already covered (counts as studied, no re-read)
                continue
            home = (g.get("home") or "").strip() or (nm.split(" vs ")[0].strip() if " vs " in nm else "")
            away = (g.get("away") or "").strip() or (nm.split(" vs ")[1].strip() if " vs " in nm else "")
            try:
                enr = self._scrape_game_enrichment(
                    driver, gid, home=home, away=away, gui_callback=gui_callback)
                if enr:
                    # Record "studied, no hazards" too — so an already-checked game
                    # with a clean sheet stays cached (and the selector's veto trusts
                    # that it was genuinely read, not silently skipped).
                    if not (enr.get("injuries") or enr.get("suspensions")):
                        self._set_enrichment(str(gid),
                                             {"injuries": [], "suspensions": [],
                                              "raw_snippet": (enr.get("raw_snippet") or "")[:120],
                                              "checked_clean": True})
                    _veto = self._enrichment_veto(enr)
                    if _veto:
                        vetoed += 1
                        emit(gui_callback, f"⛔ {nm}: pre-flight veto — {_veto}")
                    else:
                        studied_with_hazard += (1 if (enr.get("injuries") or enr.get("suspensions")) else 0)
                    studied += 1
            except Exception:
                continue
        if studied:
            emit(gui_callback,
                 f"🔎 Pre-flight researched {studied} candidate game(s) — form + injuries "
                 f"cached before pick-building"
                 + (f" | {studied_with_hazard} with hazard flags | {vetoed} vetoed"
                    if (studied_with_hazard or vetoed) else " — no injury flags."))


    def _research_between_bets(self, driver, gui_callback=None, timeout: float = 45.0,
                               max_lookups: int = 2):
        """Research-paced pacing: between betslips the machine does a REAL analysis
        pass instead of instant chaining. It reads the current fixtures, logs the
        strongest fair-probability value, then refreshes H2H team-form for the most
        promising still-open games (feeding the cache the next slip uses). Bounded
        by `timeout`; a dead browser or a failure just ends the window early."""
        emit = self._emit_direct
        emit(gui_callback, "🔬 Research window — studying games before the next slip...")
        t0 = time.time()
        try:
            if driver is None or not self._driver_is_usable(driver):
                emit(gui_callback, "🔬 (research skipped — browser unavailable)")
                return
            try:
                games = self._extract_dom_games(driver) or []
            except Exception:
                games = []
            # Home-page enrichment: study not only the today-games tab but the
            # whole football-1 home listing (live + upcoming feed) — fresh fixtures
            # there join the research pool, so the machine thinks in future games
            # too, exactly like checking the site's front page by hand.
            back_to = None
            try:
                back_to = driver.current_url
                self._safe_get(driver, LOGIN_URL)
                time.sleep(1.6)
                home_games = self._extract_dom_games(driver) or []
                known = {str(g.get("id")) for g in games}
                extra = [g for g in home_games if str(g.get("id")) not in known]
                if extra:
                    games = games + extra
                    emit(gui_callback,
                         f"🔬 Home feed adds {len(extra)} fixture(s) — research pool now "
                         "covers today-games + the football-1 home page.")
            except Exception:
                pass
            finally:
                try:
                    if back_to:
                        self._safe_get(driver, back_to)
                except Exception:
                    pass
            if not games:
                emit(gui_callback, "🔬 (no fixtures visible in this tab — reading fresh on next build)")
                return
            self._load_stats()
            ranked = []
            for name, gid, g in self._research_candidates(games):
                h3 = self._fair_win_probs(g.get("h3")) or []
                btts = self._fair_win_probs(g.get("btts")) or []
                ou = self._fair_win_probs(g.get("ou")) or []
                best = (0.0, None)
                if h3:
                    best = max(best, (h3[0], ("home", g.get("home_odds"))))
                if btts:
                    best = max(best, (btts[0], ("btts", g.get("btts_yes"))))
                if ou:
                    best = max(best, (ou[0], ("over", g.get("over_25"))))
                if best[0] >= self.MIN_LEG_CONF:
                    ranked.append((best[0], gid, name, best[1]))
            ranked.sort(reverse=True)
            if ranked:
                p, gid, name, (mkt, o) = ranked[0]
                emit(gui_callback, f"🔬 Best fair value now: {name} {mkt} @ {o} "
                                   f"(P≈{p:.0%})")
            else:
                emit(gui_callback, "🔬 (no fixture currently clears the confidence floor)")
            # 🔬 Analyst: have the LLM research the top un-researched games
            hub = self._agent_hub
            if hub is not None:
                hard_stop = t0 + timeout
                budget = max(5.0, min(float(timeout) - 5.0, hard_stop - time.time()))
                try:
                    gmap = {str(g.get("id")): g for g in games}
                    top_games = [gmap[str(gid)] for _, gid, _n, _m in ranked
                                 if str(gid) in gmap]
                    if top_games:
                        # Enrich top games with stats overlay data (injuries, weather, venue)
                        # before sending to the analyst — budget at most 2 lookups.
                        enrich_count = 0
                        for _g in top_games[:2]:
                            _gid = str(_g.get("id") or "")
                            if not _gid or enrich_count >= 2:
                                break
                            try:
                                _enr = self._scrape_game_enrichment(
                                    driver, _gid, gui_callback=gui_callback)
                                if _enr:
                                    _g["enrichment"] = _enr
                                    if _enr.get("injuries"):
                                        emit(gui_callback,
                                             f"🩺 {_g.get('name','?')}: "
                                             + " | ".join(_enr["injuries"][:2]))
                                    enrich_count += 1
                            except Exception:
                                pass

                        # Use API-Football real form when available (budget permitting),
                        # fall back to the local H2H form cache.
                        def _get_form(hh, aa):
                            api_f = self._agent_hub
                            if api_f is not None and api_f.api_football.enabled():
                                hf, af = api_f.api_football.get_game_form(hh, aa)
                                if hf or af:
                                    return hf or {}, af or {}
                            return self._fresh_form(hh), self._fresh_form(aa)

                        picks = hub.research_batch(
                            top_games[:8], limit=2, budget=budget,
                            gui_callback=gui_callback,
                            already_form=_get_form)
                        if picks:
                            emit(gui_callback,
                                 f"🧠 Analyst approved {len(picks)} game(s) for the next slip: "
                                 + "; ".join(f"{p.get('name','?')} → {p.get('pick','?')}"
                                             for p in picks[:3]))
                except Exception as e:
                    emit(gui_callback, f"🔬 analyst research skip: {str(e)[:80]}")
            lookups = 0
            hard_stop = t0 + timeout
            for p, gid, name, mkt in ranked:
                if lookups >= max_lookups:
                    break
                if time.time() > hard_stop:
                    break
                if " vs " not in name:
                    continue
                home = name.split(" vs ")[0].strip()
                away = name.split(" vs ")[1].strip()
                if not home or not away:
                    continue
                try:
                    if self._h2h_match_form(driver, home, away):
                        emit(gui_callback, f"🔬 Form researched: {home} vs {away}")
                        lookups += 1
                except Exception:
                    continue
            try:
                self._close_analysis_pages(driver, gui_callback=gui_callback)
            except Exception:
                pass
            if lookups:
                emit(gui_callback,
                     f"🔬 Research done in {time.time() - t0:.0f}s — form refreshed for "
                     f"{lookups} fixture(s); next slip builds on fresh data")
        except Exception as e:
            try:
                emit(gui_callback, f"🔬 research window ended early: {str(e)[:80]}")
            except Exception:
                pass

    def _research_candidates(self, games):
        """Yield (display_name, game_id, game_dict) for games that still have
        both team names and a playable market — used by the research window."""
        for g in (games or []):
            gid = g.get("id", "")
            name = str(g.get("name") or "")
            if not gid or " vs " not in name:
                continue
            try:
                used = self._used_games or {}
                if gid in used and (used.get(gid) or {}):
                    continue           # already bet today — not worth re-studying
            except Exception:
                pass
            yield name, gid, g

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
            # Already on a /markets page — still wait for REAL (non-placeholder)
            # selections to hydrate before parsing (placeholder shells appear
            # instantly, real odds take ~8-15s; parsing early yields no markets).
            deadline = time.time() + float(timeout)
            while time.time() < deadline:
                try:
                    real = driver.execute_script(
                        "return document.querySelectorAll('.event-selection:not(.placeholder)').length;") or 0
                    if real >= 2:
                        break
                except Exception:
                    break
                time.sleep(1)
        else:
            # The /en/games/{gid}/markets direct-URL guess is DISABLED: the display
            # gid (e.g. 2422) is NOT the real event id (e.g. 9286411) and the real
            # route omits the /en/ prefix, so direct navigation always lands on a
            # broken/blank page (0 boxes — seen 100+ times in the log, ~34s wasted
            # per leg). The only reliable entry to a game's full markets is the
            # row's .event-more-markets arrow — go straight there. Keep gid-based
            # arrow hunting (row id via data-id/href/`ID: <gid>` text) and NEVER
            # parse whichever game happens to be on screen (wrong-game slips).
            clicked = ""
            _tried = []
            _src_cands = [self.TODAY_GAMES_PAGE_URL]
            if gid:
                _src = self._gid_src.get(str(gid))
                if _src and _src not in _src_cands:
                    _src_cands.insert(0, _src)
                for _u in (self.POPULAR_GAMES_URL, self.UPCOMING_GAMES_PAGE_URL,
                           self.FOOTBALL_HOME_URL):
                    if _u not in _src_cands:
                        _src_cands.append(_u)
            for _page in _src_cands:
                if not getattr(self, "running", True):
                    break
                if _page == (driver.current_url or ""):
                    pass  # already there — run the search on this page
                elif _page not in _tried:
                    _tried.append(_page)
                    try:
                        self._safe_get(driver, _page)
                        time.sleep(1.3)
                        if gid:
                            self._scroll_to_load_more_games(driver, max_scrolls=2,
                                                            gui_callback=gui_callback)
                    except Exception:
                        pass
                try:
                    clicked = driver.execute_script(r"""
var gid = arguments[0] || null;
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
var target = null;
function hits(r) {
    var t = (r.innerText || '').replace(/\s+/g, ' ');
    if (gid) {
        if (t.indexOf('ID: ' + gid) >= 0) return true;
        if (r.querySelector('[data-id="' + gid + '"], [data-event-id="' + gid + '"], [data-game-id="' + gid + '"], [data-gid="' + gid + '"]')) return true;
        if (r.querySelector('a[href*="/games/' + gid + '"], a[href*="games/' + gid + '"]')) return true;
        return false;
    }
    return r.offsetHeight > 0;
}
for (var r = 0; r < rows.length; r++) { if (hits(rows[r])) { target = rows[r]; break; } }
if (!target) return 'norow';
var el = target.querySelector('.event-more-markets');
if (!el) return 'noarrow';
el.click();
return 'clicked';
""", gid)
                except Exception:
                    clicked = ""
                if clicked == "clicked":
                    break
            self._emit_direct(gui_callback,
                              f"↗ Full-markets opener: {clicked}"
                              if clicked != "clicked" else "")
            if clicked != "clicked":
                # The game's arrow could not be clicked on any listing. NEVER fall
                # through to parse whichever game happens to be on screen — that is
                # how wrong-game selections made it onto slips. Ask the caller to
                # skip/fallback instead.
                return {"status": "notfound", "url": "", "markets": []}
            # wait for the /markets route + REAL selections to render. The 89
            # .event-market shells appear instantly but are empty placeholders
            # for ~8-15s; trusting them starts the matcher on empty DOM every
            # time. Wait instead for hydrated non-placeholder selections.
            deadline = time.time() + float(timeout)
            while time.time() < deadline:
                try:
                    url = driver.current_url
                    if "/games/" in url and "/markets" in url:
                        n = driver.execute_script(
                            "return document.querySelectorAll('.event-market').length;") or 0
                        real = driver.execute_script(
                            "return document.querySelectorAll('.event-selection:not(.placeholder)').length;") or 0
                        if n and n >= 3 and real >= 2:
                            break
                except Exception:
                    pass
                time.sleep(1)
            time.sleep(1)
            self._close_analysis_pages(driver, gui_callback=gui_callback)
        markets = self._extract_full_markets(driver)
        return {"status": "ok", "url": url, "markets": markets}

    def _read_dc_odds_from_markets(self, markets) -> dict:
        """Pull the DOUBLE CHANCE panel (1X / X2 / 12) off a parsed full-market
        list. Returns {"dc_1x": float, "dc_x2": float, "dc_12": float} or {}.
        The full-market page's DC selections always appear in the order
        1X (idx 0), X2 (idx 1), 12 (idx 2)."""
        try:
            for m in (markets or []):
                nm = (m.get("name") or "").upper()
                if "DOUBLE CHANCE" not in nm:
                    continue
                dc = {}
                sels = m.get("selections") or []
                for key, idx in (("dc_1x", 0), ("dc_x2", 1), ("dc_12", 2)):
                    if len(sels) > idx and sels[idx].get("odds"):
                        dc[key] = float(sels[idx]["odds"])
                return dc
        except Exception:
            pass
        return {}

    def _scrape_dc_odds(self, driver, games, gui_callback=None, max_open: int = 4):
        """Open the full-market page of near-kickoff eligible games and read the
        DOUBLE CHANCE odds into the game dicts (dc_1x_odds / dc_x2_odds /
        dc_12_odds) so DC legs become selecatable from the main crawl — no
        opportunity scout required. Rate-limited per game (fresh for 15 min)."""
        try:
            now = time.time()
            cands = []
            for g in (games or []):
                gid = str(g.get("id") or "")
                if not gid:
                    continue
                # skip already-fresh games and games too far from kickoff
                if now - (self._dc_scrape_at or {}).get(gid, 0.0) < 900:
                    continue
                try:
                    ko = g.get("start")
                    mins = (ko - datetime.now()).total_seconds() / 60.0 if ko else 9999.0
                except Exception:
                    mins = 9999.0
                if mins > 12 * 60 or mins < -10:
                    continue
                cands.append((mins, g))
            cands.sort(key=lambda x: x[0])
            opened = 0
            deadline = time.time() + 45.0
            for mins, g in cands:
                if opened >= int(max_open) or time.time() > deadline \
                        or not getattr(self, "running", True):
                    break
                gid = str(g.get("id") or "")
                try:
                    res = self._open_game_full_markets(driver, gid=gid, timeout=20,
                                                       gui_callback=gui_callback)
                    dc = self._read_dc_odds_from_markets(res.get("markets") or [])
                    if dc and any(v for v in dc.values()):
                        for k, v in dc.items():
                            g[k + "_odds"] = v
                        g["dc_odds_present"] = True
                        self._emit_direct(
                            gui_callback,
                            f"↖ DC: {g.get('name', '')} 1X {dc.get('dc_1x')} | "
                            f"X2 {dc.get('dc_x2')} | 12 {dc.get('dc_12')}")
                    else:
                        g["dc_odds_present"] = False
                    # Read the DC odds AND the extra-market legs from this SAME
                    # open page. A second pass used to re-open every game just to
                    # fetch DNB/FTTS/O-U lines, so each candidate opened and closed
                    # a page twice per round — the rapid flicker the owner saw.
                    try:
                        _extras = self._parse_full_market_legs(res.get("markets") or [])
                        if _extras:
                            g["_fm"] = _extras
                            self._emit_direct(
                                gui_callback,
                                f"🧮 {g.get('name','')}: +{len(_extras)} extra markets "
                                f"(DNB/FTTS/O-U lines) exploitable")
                    except Exception:
                        pass
                    self._dc_scrape_at[gid] = now
                    opened += 1
                except Exception:
                    pass
            # Return to the listing ONCE at the end of this pass. Navigating back
            # after every single game caused the rapid "open and close" the user
            # complained about, and it also gave the page no time to actually
            # render the opened full-market tab's content before jumping away.
            try:
                self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                time.sleep(0.6)
            except Exception:
                pass
        except Exception:
            pass

    def _dump_full_markets_text(self, markets, max_markets: int = 40) -> list[str]:
        """Human-readable lines for the GUI log: 'MARKET — selection @ odds'."""
        lines = []
        for m in (markets or [])[:max_markets]:
            parts = ", ".join(
                f"{s.get('name', '')} @ {s.get('odds', '')}" for s in m.get("selections") or [])
            lines.append(f"▸ {m.get('name', '').upper()}: {parts}")
        return lines

    def _parse_full_market_legs(self, markets) -> list:
        """Convert a parsed full-market list into extra selector option tuples
        (odds, prob, market_key, suffix) for markets the listing page does NOT
        expose: Draw No Bet, First Team To Score, and every Over/Under line.
        Every leg is margin-corrected via _fair_win_probs so a short price never
        sneaks in as a "safe" pick — it is judged on honest probability."""
        extras = []
        for m in (markets or []):
            nm = (m.get("name") or "").upper()
            sels = m.get("selections") or []
            pairs = []
            for s in sels:
                o = s.get("odds")
                if isinstance(o, (int, float)) and o > 1.0:
                    pairs.append((str(s.get("name") or "").strip(), float(o)))
            if len(pairs) < 2:
                continue
            # ── Draw No Bet (2-way: home / away) ──
            if "DRAW NO BET" in nm or "DNB" in nm or "DRAW-NO-BET" in nm.replace(" ", ""):
                ps = self._fair_win_probs([p[1] for p in pairs[:2]]) or []
                if len(ps) >= 2:
                    extras.append((pairs[0][1], ps[0], "dnb_home", " DNB:HOME"))
                    extras.append((pairs[1][1], ps[1], "dnb_away", " DNB:AWAY"))
                continue
            # ── First Team To Score (home / away / no goal) ──
            if "FIRST TEAM TO SCORE" in nm or "1ST TEAM TO SCORE" in nm or "FIRST GOAL" in nm:
                ps = self._fair_win_probs([p[1] for p in pairs[:3]]) or []
                if len(ps) >= 3:
                    extras.append((pairs[0][1], ps[0], "ftts_home", " FTTS:HOME"))
                    extras.append((pairs[1][1], ps[1], "ftts_away", " FTTS:AWAY"))
                    extras.append((pairs[2][1], ps[2], "ftts_no", " FTTS:NO GOAL"))
                continue
            # ── Over/Under lines (any line except the 1.5/2.5 already covered) ──
            if "OVER" in nm or "UNDER" in nm or "TOTAL" in nm or "GOALS" in nm:
                line = None
                lm = re.search(r"(\d+(?:\.\d+)?)", nm)
                if lm:
                    line = lm.group(1)
                else:
                    for pn, _po in pairs:
                        lm = re.search(r"(\d+(?:\.\d+)?)", pn)
                        if lm:
                            line = lm.group(1)
                            break
                if line in (None, "1.5", "2.5"):
                    continue  # already covered by listing (over/under/over15)
                over_sel = under_sel = None
                for pn, po in pairs:
                    up = pn.upper()
                    if "OVER" in up and over_sel is None:
                        over_sel = po
                    elif "UNDER" in up and under_sel is None:
                        under_sel = po
                if over_sel and under_sel:
                    ps = self._fair_win_probs([over_sel, under_sel]) or []
                    keyline = line.replace(".", "")
                    if len(ps) >= 2:
                        extras.append((over_sel, ps[0], f"over{keyline}",
                                       f" O/U {line} OVER"))
                        extras.append((under_sel, ps[1], f"under{keyline}",
                                       f" O/U {line} UNDER"))
                continue
        return extras

    def _scrape_full_markets_all(self, driver, games, gui_callback=None,
                                 max_open: int = 15):
        """Open the full-market page for the most imminent playable games and read
        EVERY market type (Draw No Bet, First Team To Score, all O/U lines, …) into
        each game's `_fm` extra-legs list. This gives the selector a huge range of
        markets to exploit instead of just the 4 listing-row markets. Rate-limited
        per game (fresh for 15 min) and bounded by max_open + a running deadline.

        The DC-odds pass already opened these same pages and parsed the same
        `_fm` legs from the identical response, so skip any game it covered.
        Re-opening every game here was a second full round of page open/close —
        the flicker the owner reported."""
        try:
            now = time.time()
            deadline = time.time() + 90.0
            _dc_done = getattr(self, "_dc_scrape_at", {}) or {}
            cands = []
            for g in (games or []):
                gid = str(g.get("id") or "")
                if not gid:
                    continue
                if _dc_done.get(gid):
                    continue
                if now - (getattr(self, "_fm_scrape_at", {}) or {}).get(gid, 0.0) < 900:
                    continue
                try:
                    ko = g.get("start")
                    mins = (ko - datetime.now()).total_seconds() / 60.0 if ko else 9999.0
                except Exception:
                    mins = 9999.0
                if mins > 12 * 60 or mins < -10:
                    continue
                cands.append((mins, g))
            cands.sort(key=lambda x: x[0])
            opened = 0
            for _mins, g in cands:
                if opened >= int(max_open) or time.time() > deadline \
                        or not getattr(self, "running", True):
                    break
                gid = str(g.get("id") or "")
                try:
                    res = self._open_game_full_markets(driver, gid=gid, timeout=20,
                                                       gui_callback=gui_callback)
                    extras = self._parse_full_market_legs(res.get("markets") or [])
                    if extras:
                        g["_fm"] = extras
                        self._emit_direct(
                            gui_callback,
                            f"🧮 {g.get('name','')}: +{len(extras)} extra markets "
                            f"(DNB/FTTS/O-U lines) exploitable")
                    (self._fm_scrape_at or {})[gid] = now
                    if not getattr(self, "_fm_scrape_at", None):
                        self._fm_scrape_at = {}
                    opened += 1
                except Exception:
                    pass
            try:
                self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                time.sleep(0.5)
            except Exception:
                pass
        except Exception:
            pass

    def _implied_by_market(self, g: dict, h3_probs=None, btts_probs=None,
                           ou_probs=None, **_ignored) -> dict:
        """Margin-corrected implied probability for EVERY tracked market of one game.

        EDGE RANKING (2026-10-05): each leg is compared against the implied
        probability of ITS OWN market, never against one global number. That is
        what makes the comparison fair across markets. A Double Chance leg priced
        from fair 1X2 odds structurally carries ~6% DC margin, so a raw EV
        comparison permanently punished DC — the exact bug that made the
        machine refuse to draft the best-performing market in its own history.
        Comparing each leg to its own market means a fairly-priced leg scores
        ratio ~1.0 whichever market it came from, so only a genuine
        disagreement with the book registers as edge.

        Returns {market: implied_prob}.
        """
        out = {}
        try:
            g = g if isinstance(g, dict) else {}
            hp = list(h3_probs or [])
            bp = list(btts_probs or [])
            op = list(ou_probs or [])

            def _put(mk, odds_field, probs, idx):
                try:
                    prob = float(probs[idx])
                except (IndexError, TypeError, ValueError):
                    return
                if not (0.0 < prob < 1.0):
                    return
                try:
                    odds = float(g.get(odds_field) or 0)
                except (TypeError, ValueError):
                    odds = 0.0
                if odds > 1.0:
                    out[mk] = prob

            _put("home", "home_odds", hp, 0)
            _put("draw", "draw_odds", hp, 1)
            _put("away", "away_odds", hp, 2)
            _put("btts", "btts_yes", bp, 0)
            _put("btts_no", "btts_no", bp, 1)
            _put("over", "over_25", op, 0)
            _put("under", "under_25", op, 1)
            # O/U 1.5 has no margin-corrected array of its own here; the caller
            # calibrates it via Poisson. Fall back to the 2.5 OVER implied prob,
            # which is the closest honest prior for a higher-probability line.
            if "over15" not in out and op:
                try:
                    p15 = float(op[0])
                    if 0.0 < p15 < 1.0:
                        out["over15"] = min(0.97, p15 + 0.18)
                except (TypeError, ValueError):
                    pass
        except Exception:
            pass
        return out

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

    # ── Odds drift + kickoff-time awareness ──────────────────────────────
    _MARK_ODDS_FIELD = {
        "home": "home_odds", "away": "away_odds", "draw": "draw_odds",
        "btts": "btts_yes", "btts_no": "btts_no",
        "over": "over_25", "over15": "over_15", "under": "under_25",
        "dc_1x": "home_odds", "dc_12": "home_odds", "dc_x2": "away_odds",
        "dnb_home": "home_odds", "dnb_away": "away_odds",
        "ftts_home": "home_odds", "ftts_away": "away_odds", "ftts_no": "home_odds",
    }

    def _load_odds_history(self) -> dict:
        try:
            if self.ODDS_HISTORY_PATH.exists():
                return json.loads(self.ODDS_HISTORY_PATH.read_text(encoding="utf-8"))
        except Exception:
            pass
        return {}

    def _save_odds_history(self):
        try:
            self.ODDS_HISTORY_PATH.write_text(json.dumps(self._odds_history, indent=2),
                                              encoding="utf-8")
        except Exception:
            pass

    def _record_odds_ticks(self, games: list):
        """Snapshot every market's odds per game on each crawl so we can detect
        odds drift (early price vs current price) — a strong value signal once a
        kick-off approaches."""
        try:
            if self._odds_history is None:
                self._odds_history = self._load_odds_history()
            now = time.time()
            changed = False
            for g in games or []:
                gid = str(g.get("id") or "")
                if not gid:
                    continue
                rec = self._odds_history.get(gid)
                if rec is None:
                    rec = {"first": {}, "last": {}, "first_ts": now, "last_ts": now}
                    self._odds_history[gid] = rec
                kf = g.get("ko_epoch")
                if kf is not None:
                    rec["kickoff"] = int(kf)
                fields = ("home_odds", "btts_yes", "over_25", "over_15",
                          "draw_odds", "away_odds", "btts_no", "under_25")
                if not rec.get("first"):
                    for f in fields:
                        v = g.get(f)
                        if isinstance(v, (int, float)) and v > 1.0:
                            rec["first"][f] = round(float(v), 2)
                for f in fields:
                    v = g.get(f)
                    if isinstance(v, (int, float)) and v > 1.0:
                        v = round(float(v), 2)
                        prev = rec["last"].get(f)
                        if prev is None or abs(prev - v) >= 0.005:
                            rec["last"][f] = v
                            changed = True
                rec["last_ts"] = now
                # ── CLV recheck (2026-09-26) ──────────────────────────
                # This crawl sees the same market moments before kick-off. If we
                # hold a snapshot for this game/market, the price in this crawl IS
                # effectively the closing line, so settle the CLV right here.
                # We deliberately take the FIRST price we see inside the recheck
                # window and never overwrite it: the first sighting near kick-off
                # is a fairer "closing" reference than a later in-play scramble.
                try:
                    ko = rec.get("kickoff")
                    if ko and self._clv_store():
                        mins_left = (float(ko) - now) / 60.0
                        if 0.0 <= mins_left <= self.CLV_RECHECK_LEAD_MIN:
                            for _key in list(self._clv_store().keys()):
                                if not _key.startswith(f"{gid}|"):
                                    continue
                                # Latent-bug fix (2026-10-05): this read `_mk`,
                                # a name that exists nowhere. The surrounding
                                # try/except swallowed the NameError, so the
                                # entire CLV recheck died silently every time a
                                # kick-off entered the lead window - which is
                                # why closing-line data was almost never
                                # recorded, leaving the sharpest available
                                # measure of whether our prices were good
                                # completely absent.
                                _name = str(_key).split("|", 1)[1]
                                _field = self._MARK_ODDS_FIELD.get(_name)
                                if not _field:
                                    continue
                                _v = g.get(_field)
                                if isinstance(_v, (int, float)) and _v > 1.0:
                                    self._record_closing_odds(gid, _name, float(_v))
                except Exception:
                    pass
                # Prune: drop history for games that kicked off long ago
                try:
                    if rec.get("kickoff") and rec["kickoff"] < now - 4 * 3600:
                        self._odds_history.pop(gid, None)
                except Exception:
                    pass
            if changed:
                self._save_odds_history()
        except Exception:
            pass
        self._sb_push_observed_games(games)

    def _fishnet_pool_today(self) -> list:
        """Collect every (game_id, market, prob) the machine bet TODAY across ALL
        accounts — the 'fishnet': the union of every game the machine already liked,
        ready to be bundled into one long multi-leg lottery slip per account."""
        pool = []
        seen = set()
        today = datetime.now().strftime("%Y-%m-%d")
        for b in (getattr(self, "_bets", None) or []):
            if str(b.get("status") or "").startswith("shadow"):
                continue
            if float(b.get("stake") or 0) <= 0:
                continue
            if not str(b.get("placed_at") or "").startswith(today):
                continue
            gids = b.get("game_ids") or []
            mks = b.get("markets") or []
            probs = b.get("probs") or []
            for i, gid in enumerate(gids):
                gid = str(gid or "")
                if not gid:
                    continue
                mk = mks[i] if i < len(mks) else ""
                if (gid, mk) in seen:
                    continue
                seen.add((gid, mk))
                prob = float(probs[i]) if i < len(probs) else 0.5
                pool.append({"gid": gid, "market": mk, "prob": prob})
        return pool

    def _place_fishnet_bet(self, driver, phone: str, password: str, stake: float = 10,
                           gui_callback=None, max_legs: int = 14) -> dict:
        """Bundle every game the machine bet today (across all accounts) into ONE
        long multi-leg lottery slip for this account. This is the 'fishnet' — it
        catches a big payout on days when the individually-picked legs mostly land.

        Re-crawls the board, matches pooled (game_id, market) pairs to still-live
        games, clicks those exact legs, and places the long slip. Games already
        kicked off / gone are skipped so the slip only ever contains placeable legs.
        """
        try:
            pool = self._fishnet_pool_today()
            if len(pool) < 2:
                return {"status": "skipped", "skipped": True,
                        "message": "Fishnet pool too small (need 2+ games bet today)"}
            self._ensure_bet_login(driver, phone, password, gui_callback=gui_callback)
            self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
            time.sleep(0.8)
            games = self._extract_dom_games(driver) or []
            by_gid = {str(g.get("id")): g for g in games if str(g.get("id"))}
            legs = []
            for p in pool:
                g = by_gid.get(p["gid"])
                if not g:
                    continue
                mk = p["market"]
                field = self._MARK_ODDS_FIELD.get(mk)
                odds = g.get(field) if field else None
                if not isinstance(odds, (int, float)) or odds <= 1.0:
                    continue
                # OWNER RULE (2026-10-05): the fishnet is a separate leg builder
                # and did NOT go through the selector's MIN_LEG_ODDS gate, so it
                # was still free to take 1.01-1.09 dead filler. Apply the same
                # floor here so both builders obey one rule.
                if not (self.MIN_LEG_ODDS < odds):
                    continue
                start = g.get("start")
                if start and (start - datetime.now()).total_seconds() < 90:
                    continue  # about to kick off / in-play — skip
                legs.append((float(odds), str(g.get("name") or ""), p["gid"], mk, p["prob"]))
            if len(legs) < 3:
                return {"status": "skipped", "skipped": True,
                        "message": f"Only {len(legs)} pooled games still placeable"}
            # Hard leg ceiling (2026-09-26) — the caller may ask for 14, but the
            # 14/25-leg shapes came back -100% in the ledger, so the cap is
            # applied here at the last possible moment, not in the scheduler.
            if max_legs > self.MAX_SLIP_LEGS_HARD or max_legs <= 0:
                max_legs = self.MAX_SLIP_LEGS_HARD
            if len(legs) > max_legs:
                self._emit_direct(gui_callback,
                                  f"🐟 leg cap: {len(legs)} pooled games trimmed to "
                                  f"{max_legs} (14+ leg slips returned -100%)")
            legs = legs[:max_legs]
            self._emit_direct(gui_callback,
                              f"🐟 {phone} FISHNET LOTTERY: {len(legs)} pooled games → one long slip")
            picked = self._click_selected_legs(driver, legs, gui_callback=gui_callback)
            if picked < 2:
                return {"status": "error", "message": f"Only {picked} fishnet legs clicked"}
            product = 1.0
            for o, _, _, _, _ in legs:
                product *= o
            # ── Portfolio gates on the fishnet too (2026-09-26) ─────────
            # The fishnet pools games that were ALREADY bet on other accounts
            # (_fishnet_pool_today reads the ledger), so it is by construction the
            # most correlated slip the machine can build. Without this check it
            # would stack one account's positions straight onto its siblings'.
            _ok_c, _why_c = self._correlation_verdict(
                phone, [str(l[2]) for l in legs], [l[1] for l in legs],
                [l[3] for l in legs])
            if not _ok_c:
                self._count_refusal("cross-account correlation (fishnet)")
                self._emit_direct(gui_callback,
                                  f"🛑 portfolio refused the fishnet — {_why_c}")
                return {"status": "skipped", "skipped": True,
                        "circuit_breaker": True,
                        "message": f"correlation: {_why_c or 'account/league/market overlap'}",
                        "correlation_blocked": True}
            _vkey_f = "{0}L@{1}/{2}/[{3}]".format(
                len(legs), self._band_of(product), self._lead_bucket(None),
                "-".join(sorted(set(l[3] for l in legs))) or "-")
            if self._recipe_vetoed(_vkey_f):
                self._count_refusal("vetoed losing recipe (fishnet)")
                self._emit_direct(gui_callback,
                                  f"⛔ fishnet vetoed by real-money ROI: {_vkey_f}")
                return {"status": "skipped", "skipped": True,
                        "recipe_vetoed": True,
                        "message": f"vetoed recipe: {_vkey_f}",
                        "recipe_vetoed": True}
            res = self._open_betslip_and_place(driver, stake, phone, password,
                                               gui_callback=gui_callback,
                                               before_balance=0.0)
            placed = isinstance(res, bool) and res
            if not placed:
                self._clear_betslip(driver, gui_callback=gui_callback)
                return {"status": "error", "message": "Fishnet slip did not place"}
            self._mark_legs_used(legs)
            try:
                self._snapshot_clv([str(l[2]) for l in legs], [l[3] for l in legs],
                                   [(str(l[2]), l[3], l[0]) for l in legs],
                                   phone=phone)
            except Exception:
                pass
            return {"status": "success", "message": "Fishnet placed",
                    "legs": len(legs), "stake": stake,
                    "odds": round(product, 2),
                    "possible_win": round(float(stake) * product, 2),
                    "markets": [l[3] for l in legs],
                    "probs": [round(l[4], 4) for l in legs],
                    "game_ids": [str(l[2]) for l in legs],
                    "leg_names": [l[1] for l in legs],
                    "fishnet": True,
                    "placed_at": datetime.now().isoformat(timespec="seconds")}
        except Exception as exc:
            return {"status": "error", "message": str(exc)[:150]}

    def _drift_k(self, gid: str, mk: str, cur) -> float:
        """Tick multiplier based on how the market actually moved since we first
        saw the game: odds shortened (ratio > 1) = money/confidence coming in,
        odds drifted out (ratio < 1) = backing away. Capped so it never becomes
        the whole story — it nudges, it does not override."""
        try:
            rec = (self._odds_history or {}).get(str(gid))
            if not rec:
                return 1.0
            start = (rec.get("first") or {}).get(self._MARK_ODDS_FIELD.get(mk, ""))
            if not start or not cur or float(start) <= 1.0 or float(cur) <= 1.0:
                return 1.0
            ratio = float(start) / float(cur)
            return max(0.92, min(1.20, ratio))
        except Exception:
            return 1.0

    def _time_k(self, g) -> float:
        """Momentum multiplier for games near / at kick-off. Closer to start =
        more informed current prices (team news + weather are priced in). No
        minimum lead is required — an imminent game is fully eligible.

        2026-09-24: a match that has ALREADY kicked off is excluded outright
        (returns 0.0). A live/started leg is unsellable junk — the odds will be
        refused or re-graded before the slip submits, and it drags the rest of
        the ticket down. Only pre-kick-off games can be drafted."""
        try:
            start = g.get("start")
            if not start:
                return 1.0
            mins = (start - datetime.now()).total_seconds() / 60.0
            if mins < -5:
                return 0.0       # already underway — never draft a live leg
            if mins < 0:
                return 0.0       # kicked off in the last few minutes — equally dead
            if mins <= 60:
                return 1.06
            if mins <= 180:
                return 1.03
            if mins <= 360:
                return 1.01
            return 1.0
        except Exception:
            return 1.0

    def _select_football_legs(self, games, target_min: float = 3.0, target_max: float = 6.0,
                              odds_cap: float = 8.0, max_legs: int = 14,
                              min_legs: int = 2,
                              used=(), prefer_more_legs: bool = False, seed: int = 0,
                              conf_floor=None, no_odds_cap=False,
                              researched_only=False, gui_callback=None) -> tuple:
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
        min_legs defaults to 2 — SportPesa accepts 2-leg multis, so we never require
        3 legs and risk skipping a round for lack of candidates.

        Returns (legs, product) where legs is a list of
        (odds, display_name, game_id, market, win_prob) tuples, or (None, 0.0).
        """
        # Hard leg ceiling (2026-09-26). Applied HERE, inside the single selector
        # every caller shares, so no scheduling path can request a 14-leg slip any
        # more. The ledger showed 14-leg and 25-leg shapes returning -100%; beyond
        # ~6 legs the per-leg edge is no longer measurable and the variance
        # destroys any Kelly sizing applied afterwards.
        if max_legs is None or int(max_legs) <= 0 or int(max_legs) > self.MAX_SLIP_LEGS_HARD:
            max_legs = self.MAX_SLIP_LEGS_HARD
        else:
            max_legs = int(max_legs)
        # One most-likely selection per game (a game already bet today is SKIPPED
        # entirely — the same match must never appear again in a different slip.
        # Market types that beat prediction are weighted up; ones that keep losing
        # vs their predicted fair probability are retired by the learning engine.)
        used_set = set(used) if used else set()
        self._load_stats()
        per_game = {}
        _DIAG = {"games": 0, "veto": 0, "used": 0, "stale": 0, "no_opts": 0,
                 "cand": 0, "near": 0, "below_abs": 0, "trunc": 0,
                 "no_options": 0, "no_home": 0, "all_sub120": 0, "all_raw": 0,
                 "all_whitelist": 0, "all_cap": 0, "all_group_used": 0,
                 "all_combo_used": 0, "all_retired": 0, "all_btts": 0,
                 "only_btts_cap": 0, "res_only": 0}
        # OWNER RULE (per-SLIP, 2026-09-19): max ONE BTTS/GG leg per slip. The
        # slot must live OUTSIDE the games loop so a slip claims it exactly once.
        btts_used_in_slip = False
        # OWNER RULE (per-SLIP, 2026-09-26): the O/U "death trap" cap. Goals legs
        # are capped per slip exactly like BTTS, forcing 1X2 / DC / BTTS legs in.
        goals_used_in_slip = 0
        # Threshold census (2026-09-28): how many GAMES reach each gate, so the
        # live log can show WHY the board collapses to 3 legs instead of guessing.
        # Each game may contribute several market legs; we count a game ONCE per
        # threshold when at least one of its legs passes that threshold.
        _census = {"any_leg": 0}
        _seen_census_games = set()
        for g in games:
            _DIAG["games"] += 1
            gid = g.get("id", "")
            h3 = self._fair_win_probs(g.get("h3")) or []
            btts = self._fair_win_probs(g.get("btts")) or []
            ou = self._fair_win_probs(g.get("ou")) or []
            # Team-form tilt (cache-only — from the H2H research the machine already
            # did; never a live lookup here). A form-strong home side edges the home
            # market up and, weakly, BTTS/OVER (attack correlates); the stored win
            # probability itself is left untouched so calibration stays honest.
            tilt = 0.0
            nm = str(g.get("name") or "")
            home_n = ""
            away_n = ""
            if " vs " in nm:
                home_n = nm.split(" vs ")[0].strip()
                away_n = nm.split(" vs ")[1].strip()
                if home_n and away_n:
                    hf = self._fresh_form(home_n)
                    af = self._fresh_form(away_n)
                    if hf and af:
                        _t = self._form_tilt_from_entries(hf, af)
                        if _t.get("weight", 0.0) > 0:
                            tilt = _t.get("home_adv", 0.0) * _t.get("weight", 0.0)
            _enr = None
            try:
                _enr = self._enrichment_for(gid)
            except Exception:
                _enr = None
            # XI / formation weighting (2026-10-05). Computed per leg below,
            # because whether an attacking shape helps depends on the market:
            # a 4-3-3 vs 5-4-1 raises Over 2.5 but says little about 1X2.
            # Hard veto: a game with multiple injury/suspension flags or a stated
            # key absence is dropped ENTIRELY — never bet, never even considered.
            _veto = self._enrichment_veto(_enr or {})
            if _veto:
                _DIAG["veto"] += 1
                self._emit_direct(gui_callback,
                                  f"⛔ {g.get('name','')}: skipped — {_veto}")
                continue
            # Owner rule: no match repeats today, period. A game already bet in an
            # earlier slip — on this number or any other — is dropped ENTIRELY here,
            # before any market for it is even considered.
            if str(gid) in used_set:
                _DIAG["used"] += 1
                self._emit_direct(gui_callback,
                                  f"⏭ {g.get('name', '')}: already bet today — "
                                  "no match repeats across numbers")
                continue
            # Owner rule (2026-09-22): today+tomorrow only. Past that the book
            # suspends/voids the line before kick-off, so far-future legs just
            # burn the round with 'Not valid (selection suspended/removed)'.
            if not self._is_recent_enough(g):
                _DIAG["stale"] += 1
                continue
            e_k = self._enrichment_k(_enr or {}, home_n, away_n)
            options = []
            # h3[0] is a PRICE (e.g. 1.20), not a probability. Passing it as the
            # leg's fair prob made the raw veto compare 1.20 >= 0.50, so every
            # home favourite cleared the veto on its PRICE while the draw/away legs
            # built right beside it (which use h3_probs) were judged on a real
            # probability. The two branches were not measuring the same thing, and
            # the un-vetoed home legs were then the cheapest picks in the pool.
            # Use the margin-stripped fair probability, exactly as draw/away do.
            if h3 and isinstance(g.get("home_odds"), (int, float)):
                _h3p = self._fair_win_probs(h3) or []
                options.append((g["home_odds"], _h3p[0] if _h3p else h3[0],
                                "home", "", 1.0 + tilt))
            if btts and isinstance(g.get("btts_yes"), (int, float)):
                options.append((g["btts_yes"], btts[0], "btts", " BTTS:YES", 1.0 + 0.5 * tilt))
            # ── Goals markets with Poisson/O-U calibration (#5, 2026-09-24) ──
            # The over/under probabilities are calibrated against the book's own
            # real O/U line (plus a Poisson rescale from the 1X2 odds for the 1.5
            # line) so the goals legs are honest — never a raw price assumed to be
            # a "free win". Falls back to margin-stripped listing probs.
            _h3_for_cal = self._fair_win_probs(g.get("h3")) or []
            _ou_for_cal = (self._fair_win_probs(g.get("ou")) or []) or ou
            _cal_g = self._calibrated_goals_probs(g, _h3_for_cal, _ou_for_cal)
            if ou and isinstance(g.get("over_25"), (int, float)):
                p_over = (_cal_g or {}).get("over25") if _cal_g else None
                options.append((g["over_25"], p_over or ou[0], "over",
                                " O/U 2.5 OVER", 1.0 + 0.5 * tilt))
            # ── Over 1.5 — higher probability, lower odds ────────────────
            # If the listing page exposed an Over 1.5 line use it.  It has a
            # genuinely higher hit-rate than Over 2.5 and fills the slip when
            # Over 2.5 has too low a prob to clear the confidence floor.
            ou15_probs = self._fair_win_probs(g.get("ou15")) or []
            if isinstance(g.get("over_15"), (int, float)):
                p_over15 = (_cal_g or {}).get("over15") if _cal_g else (ou15_probs[0] if ou15_probs else None)
                if p_over15:
                    options.append((g["over_15"], p_over15, "over15",
                                    " O/U 1.5 OVER", 1.0 + 0.5 * tilt))
            # ── Extended markets: draw, away, under 2.5, BTTS:NO ─────────
            # These use margin-corrected probabilities from the same odds arrays
            # that are already scraped. They are subject to the same conf_floor
            # and retirement rules as the three legacy markets.
            # hub must be assigned here — BEFORE the DC block uses it
            hub = self._agent_hub
            h3_probs = self._fair_win_probs(g.get("h3")) or []
            btts_probs = self._fair_win_probs(g.get("btts")) or []
            ou_probs = self._fair_win_probs(g.get("ou")) or []
            if len(h3_probs) > 1 and isinstance(g.get("draw_odds"), (int, float)):
                # draw tends to be slightly anti-correlated with form tilt → reduce tilt half as much
                options.append((g["draw_odds"], h3_probs[1], "draw", " DRAW", 1.0 - 0.3 * tilt))
            if len(h3_probs) > 2 and isinstance(g.get("away_odds"), (int, float)):
                # strong away form (negative tilt) is a positive signal for away win
                options.append((g["away_odds"], h3_probs[2], "away", " AWAY", 1.0 - 0.5 * tilt))
            if len(btts_probs) > 1 and isinstance(g.get("btts_no"), (int, float)):
                options.append((g["btts_no"], btts_probs[1], "btts_no", " BTTS:NO", 1.0 - 0.3 * tilt))
            if len(ou_probs) > 1 and isinstance(g.get("under_25"), (int, float)):
                p_under = (_cal_g or {}).get("under25") if _cal_g else None
                options.append((g["under_25"], p_under or ou_probs[1], "under",
                                " U/O 2.5 UNDER", 1.0 - 0.3 * tilt))
            # ── Double Chance — 1X / X2 / 12 ────────────────────────────────
            # DC is only available from the full-market page (it's not reliably
            # visible on the listing row).  We compute the probability here for
            # when the scout has already opened the full-market page and cached
            # the real DC odds.  The listing-row click would fail (DC panel is
            # collapsed), so we only add these if we have scout data confirming
            # the odds are available.
            if len(h3_probs) >= 3:
                _ph, _pd, _pa = h3_probs[0], h3_probs[1], h3_probs[2]
                dc_1x_p = _ph + _pd   # home or draw
                dc_x2_p = _pd + _pa   # draw or away
                dc_12_p = _ph + _pa   # home or away
                # Only add DC legs if OpportunityScout found them with real odds
                scout_evs = {}
                if hub is not None:
                    try:
                        scout_evs = (hub.cache.scout_map().get(str(gid)) or {})
                    except Exception:
                        scout_evs = {}
                # Check if scout confirmed a DC option exists for this game
                # Owner rule (2026-09-18, ENFORCED): when the head-to-head winner
                # is genuinely a coin-flip (home vs away fair-prob gap is tiny),
                # betting that raw 1X2 toss is donating edge. In that case the
                # engine prefers the DOUBLE-CHANCE leg (1X / X2 / 12) — same
                # kick-off, ~2/3 of all outcomes win, and the combined slip still
                # clears the x2.50 owner floor. The boost scales smoothly with how
                # close the toss is: the tighter the gap, the harder DC wins the
                # selection vs the now-near-50/50 single-market bet.
                _gap = abs(_ph - _pa) if len(h3_probs) >= 3 else 1.0
                _dc_boost = 0.20 * max(0.0, 1.0 - min(1.0, _gap / 0.12))
                for dc_mk, dc_p, dc_suf in (
                    ("dc_1x", dc_1x_p, " DC: 1X (Home/Draw)"),
                    ("dc_x2", dc_x2_p, " DC: X2 (Draw/Away)"),
                    ("dc_12", dc_12_p, " DC: 12 (Home/Away)"),
                ):
                    if dc_p < 0.55:
                        continue
                    # Real DC odds come from the full-market page scrape. OWNER
                    # LEARNING (2026-09-25): that scrape has been unreliable
                    # ("renders 0 boxes"), so DC legs NEVER reached the selector —
                    # the book's DC market never got drafted even though dc_12
                    # (16/19) owns the best hit-rate in the stats table. When the
                    # real odds are missing, derive an honest DC price from the
                    # margin-corrected 1X2 probs with a small DC-market margin
                    # (~6%) — the engine's own fair value, priced as a closing
                    # line. Real scraped odds still win when present. The slip is
                    # placed at whatever the book displays, so a small deviation
                    # in our estimate only shifts the slip tail, never breaks it.
                    cached_odds = g.get(f"{dc_mk}_odds")
                    if cached_odds and isinstance(cached_odds, (int, float)):
                        dc_odds = float(cached_odds)
                    else:
                        _dc_margin = 0.06
                        dc_odds = 1.0 / (dc_p * (1.0 + _dc_margin))
                    if o := dc_odds:
                        options.append((float(o), dc_p, dc_mk, dc_suf,
                                        1.0 + _dc_boost))
            # ── Full-market expansion (DNB / FTTS / extra O-U lines) ──────
            # Every extra market the full-market scrape read off the game's
            # /markets page. Each already carries its margin-corrected probability,
            # so a low price is judged honestly — not treated as a free win.
            for _o, _p, _mk, _suf in (g.get("_fm") or []):
                if _mk in [o2[2] for o2 in options]:
                    continue
                options.append((_o, _p, _mk, _suf, 1.0))
            # ── Agent research injection ──
            pick_ok = False
            if hub is not None:
                try:
                    apick = hub.cache.fresh_pick(gid)
                except Exception:
                    apick = None
                if apick and isinstance(apick.get("pick"), str):
                    pick_ok = True
                    mk_a = apick["pick"]
                    conf_a = float(apick.get("confidence") or 0)
                    prob_a = float(apick.get("prob") or 0)
                    # Map analyst pick name to the game dict odds field
                    o_map = {
                        "home":    g.get("home_odds"),
                        "draw":    g.get("draw_odds"),
                        "away":    g.get("away_odds"),
                        "btts":    g.get("btts_yes"),
                        "btts_no": g.get("btts_no"),
                        "over":    g.get("over_25"),
                        "over15":  g.get("over_15"),
                        "under":   g.get("under_25"),
                    }
                    o_a = o_map.get(mk_a)
                    if (isinstance(o_a, (int, float)) and conf_a >= 0.45
                            and prob_a > 0 and mk_a not in [o2[2] for o2 in options]):
                        options.append((o_a, prob_a, mk_a, " BRAIN", 1.0))
            # Researched-only mode: only games with a fresh analyst pick qualify.
            if researched_only and not pick_ok:
                _DIAG["res_only"] += 1
                continue
            valid = []
            floor = self.MIN_LEG_CONF if conf_floor is None else float(conf_floor)

            # Market group mapping — once any market in a group is used for a game,
            # the ENTIRE group is blocked for that game in all future slips.
            # Rule: Chelsea home win used → Chelsea draw AND Chelsea away both blocked.
            # But Chelsea BTTS:YES is fine — different market category entirely.
            _MK_GROUPS = {
                "home":    "1x2",
                "draw":    "1x2",
                "away":    "1x2",
                "btts":    "btts",
                "btts_no": "btts",
                "over":    "goals",
                "over15":  "goals",
                "under":   "goals",
                "dnb_home": "dnb",
                "dnb_away": "dnb",
                "ftts_home": "ftts",
                "ftts_away": "ftts",
                "ftts_no":  "ftts",
                "dc_1x":   "dc",
                "dc_x2":   "dc",
                "dc_12":   "dc",
            }

            def _mk_group(mk: str):
                if mk in _MK_GROUPS:
                    return _MK_GROUPS[mk]
                if str(mk).startswith(("over", "under")):
                    return "goals"
                return str(mk)

            # Build the set of market groups already used for this game
            _used_groups_for_game = set()
            for _combo in used_set:
                if _combo.startswith(f"{gid}|"):
                    _used_mk = _combo.split("|", 1)[1]
                    _grp = _mk_group(_used_mk)
                    if _grp:
                        _used_groups_for_game.add(_grp)

            for o, p, mk, suf, form_k in options:
                # Suspended-at-PLACE memory: a leg the book flagged "Not valid"
                # (selection suspended/removed) blocks every later submit dead.
                # Skip it from the pool until its cooldown clears so the rebuild
                # picks fresh upcoming games instead of the same dead one.
                if self._leg_suspended_till(gid, mk) > time.time():
                    _DIAG["all_susp"] = _DIAG.get("all_susp", 0) + 1
                    continue
                # Owner rule: never a leg below x1.20 (drop 1.01/1.04 filler legs).
                if not (self.MIN_LEG_ODDS < o):
                    _DIAG["all_sub120"] += 1
                    continue
                # Owner's market whitelist toggles (Over 1.5 / Over 2.5 / BTTS / 1X2).
                if not self._market_ok(mk):
                    _DIAG["all_whitelist"] += 1
                    continue
                if not no_odds_cap and o > odds_cap:
                    _DIAG["all_cap"] += 1
                    continue
                # Hard raw veto — never bet a leg the model rates below the veto, no matter
                # how much a market weight or drift factor would pad it. In explicit
                # long-shot mode the veto relaxes slightly (0.40) so big-odds owner
                # tickets stay buildable, but 0.136/0.21 garbage never enters.
                raw_veto = 0.40 if prefer_more_legs else self.RAW_LEG_VETO
                if float(p) < raw_veto:
                    _DIAG["all_raw"] += 1
                    continue
                # Block if this market's GROUP was already used for this game
                _grp_here = _mk_group(mk)
                if _grp_here in _used_groups_for_game:
                    _DIAG["all_group_used"] += 1
                    continue
                # Also block exact combo (legacy safety net)
                if f"{gid}|{mk}" in used_set:
                    _DIAG["all_combo_used"] += 1
                    continue
                if self.is_market_retired(mk):
                    _DIAG["all_retired"] += 1
                    continue
                # v4+ OWNER RULE (ENFORCED 2026-09-19): max ONE BTTS/GG leg per
                # slip. GG sits at ~55-60% fair prob so raw probability picks it
                # for every game every kick-off, and the old engine let 3-4 GG
                # legs stack into a single slip — then GG killed the slip far more
                # often than it won it. This cap makes the machine diversify ON
                # PURPOSE: a second GG leg physically cannot join the same slip.
                if str(mk) in ("btts", "btts_no"):
                    # OWNER RULE (2026-09-19): BTTS stays legal but only a
                    # STRONGLY-BACKED BTTS ever gets drafted. BTTS fair prob sits
                    # at ~55-60% (a coin-flip), so a slip that rides a bare BTTS
                    # is a donation waiting to happen. The slip therefore only
                    # accepts a BTTS leg when the engine's weighted confidence
                    # clears a hard strong-support floor — anything below it is
                    # treated as "the data does NOT highly support this" and the
                    # leg is skipped (never a bare-dice BTTS). One BTTS max/slip.
                    if btts_used_in_slip or float(p or 0.0) < self.BTTS_STRONG_FLOOR:
                        _DIAG["all_btts"] += 1
                        continue
                # OWNER RULE (2026-09-26): O/U death-trap cap. Goals legs are the
                # ones that keep stacking (see goals_used_in_slip). Past the cap a
                # goals leg is skipped, which forces the next slot onto 1X2 / DC /
                # BTTS so the slip spans the whole board. MAX_GOALS_LEGS_PER_SLIP
                # is deliberately > 1: the owner wants O/U represented, just not
                # four times in one ticket.
                elif str(mk).startswith(("over", "under")):
                    if goals_used_in_slip >= self.MAX_GOALS_LEGS_PER_SLIP:
                        continue
                # value weighting from the Opportunity Scout
                v_k = 1.0
                if hub is not None:
                    v_k = hub.value_k(gid, mk)
# XI / formation lift (2026-10-05). Per-leg because it is market-aware:
                # a confirmed 4-3-3 vs 5-4-1 raises Over 2.5 but barely moves
                # 1X2. Neutral (1.0) when no lineup was parsed, so a missing XI
                # never silently punishes a game.
                _xi_k = 1.0
                try:
                    _xi_k = self._lineup_formation_k(_enr or {}, market=mk)
                except Exception:
                    _xi_k = 1.0
                # Similar-opponent record (2026-10-05). Compared against the
                # team on the OTHER side of this fixture, so each side is
                # judged on its own history against comparable clubs.
                _sim_k = 1.0
                try:
                    _opp = away_n if str(mk) in ("home", "dc_1x", "dnb_home") else (
                        home_n if str(mk) in ("away", "dc_x2", "dnb_away") else "")
                    if _opp:
                        _rec = (_enr or {}).get("recent_opponents") or {}
                        _side_rec = _rec.get(
                            "home" if str(mk) in ("home", "dc_1x", "dnb_home") else "away")
                        _sim_k = self._similar_opponent_k(
                            {"rows": _side_rec or []}, _opp)
                except Exception:
                    _sim_k = 1.0
# Due-diligence weight now drives selection: market hit-rate from
                # learning, form tilt, injury/weather, scout EV, live odds drift
                # and now the confirmed XI / formation all scale the probability
                # that actually ranks legs and slips.
                base_w = (float(p) * self._market_type_weight(mk) * form_k *
                          v_k * e_k * self._drift_k(gid, mk, o) * self._time_k(g) *
                          self._league_k(mk, nm) * _xi_k * _sim_k)
                # Per-game census: the HARD gates (raw veto + odds floor + market
                # whitelist + not retired) decide whether a game is bettable at all.
                # The weighted score base_w only ranks. Count how many games reach
                # the ranking step at all, so the live SEL DIAG shows where the
                # board actually thins out. (2026-09-28: every leg reaching here
                # has already cleared the raw veto and the odds floor, so the old
                # floor055/abs030 census split was noise — near-misses are admitted
                # like everyone else now.)
                if gid not in _seen_census_games:
                    _seen_census_games.add(gid)
                    _census["any_leg"] += 1
                # base_w is a RANKING score only. Every HARD gate has already been
                # applied above (raw-probability veto, x1.20 odds floor, market
                # whitelist, retired markets, injury/suspension, today+tomorrow
                # window, implied-confidence cap), so a leg reaching here has been
                # judged on its own merits and passed. base_w must NOT also bar
                # admission: multiplying sub-unity factors (form, scout value,
                # enrichment, drift, time, league) would delete a genuine favourite
                # in an unfamiliar league purely from unfamiliarity.
                #
                # (2026-09-28, simplification): the earlier near-miss ladder — hold
                # legs below MIN_LEG_CONF, then a top-up pass re-promotes them on the
                # raw veto alone — turned out to be dead weight. Every near-miss was
                # a sibling market of an already-claimed game, so the top-up could
                # never widen the pool; the raw-veto gate on the board is the real
                # constraint. Removed: every leg that clears the hard gates is a
                # candidate, and base_w only orders them.
                # Per-account spread factor — deterministic (no Python hash salt).
                # Used ONLY as a tiebreak so parallel accounts don't all bet the
                # identical slip when two options are truly equal.
                jitter_mult = 1.0
                if seed:
                    h = (int(hashlib.sha256(
                        f"{seed}|{gid}|{mk}".encode("utf-8")).hexdigest(), 16) % 1000)
                    jitter_mult = 1.0 + ((h / 1000.0) - 0.5) * 0.06
                # base_w is a RANKING score only.
                valid.append((o, base_w * jitter_mult, min(base_w, 0.98), mk, suf))
            if not valid:
                _DIAG["no_options"] += 1
                continue
            # ── OWNER LEARNING (2026-09-26): the over/under death-trap fix ──
            # The slip was collapsing into 4x "over" every round. Two causes, both
            # visible in the 09-26 ledger: every "over" leg carried prob 0.73-0.93
            # at odds 1.22-1.54, and the selector then ranked legs PURELY by that
            # confidence, so the most-inflated market won EVERY per-game slot and
            # the slip became a correlated goal-stack that dies together.
            #
            # 1) Confidence must never be allowed to exceed what the book implies.
            #    A leg at 1.22 cannot honestly be a 0.93 shot — that is the market
            #    weight (1.22) multiplied on top of a fair prob, i.e. double
            #    counting. Cap every leg's ranked confidence at its own implied
            #    probability (fair value, margin removed) plus a small edge
            #    allowance. Below that cap the market weights/form/league still
            #    decide; they just can't manufacture a 0.93.
            # 2) The slip must SPREAD across market groups. Even after the cap, a
            #    hot O/U line can top several slots. Cap goals-market legs per slip
            #    so 1X2, Double Chance, BTTS and O/U all get drafted — which is
            #    exactly what the owner asked for: bet the whole board, not one
            #    market. (BTTS already had a 1-per-slip cap; goals did not, and
            #    that absence is what produced 4x "over".)
            _implied_cap = {}
            for _c in valid:
                _oo = float(_c[0])
                # 1/odds is the raw implied prob; the book overround means the true
                # fair prob is slightly HIGHER, so allow a thin margin on top.
                _implied_cap[(_c[2], _c[3])] = min(0.97, (1.0 / _oo) * 1.06 + 0.02)
            valid = [(c[0], c[1], min(c[2], _implied_cap.get((c[2], c[3]), 0.97)), c[3], c[4])
                     for c in valid]
            # Pick the market with the best DILIGENCE-WEIGHTED EDGE per game —
            # form, injuries, market hit-rate, scout EV and odds drift decide the
            # winner, not raw price alone. OWNER LEARNING (2026-09-25): this used
            # to rank by KELLY FIRST (kelly = (p*odds-1)/(odds-1)), which divides by
            # (odds-1) and therefore STRUCTURALLY ANNIHILATES low-odds legs: a
            # "DC: 1X" at 1.18/p0.67 scored kelly ~ -1.16 while a 2.40/p0.42 home
            # scored +0.006 — so Double Chance (dc_12 = 16/19 history, the single
            # best market in the table) could NEVER be drafted, and the winning
            # low-odds recipe btts-no/under likewise lost to long-shots. Kelly/EV
            # decided staking, not leg choice. Now the RANKING KEY is the weighted
            # confidence itself (base_w already folds in market hit-rate, form,
            # injuries, scout EV, drift, time, league + the 09-25 underperform
            # penalization), so the machine drafts the most-likely-to-win leg per
            # game — the obvious win — and Kelly/EV only break ties between legs
            # of equal confidence.
            #
            # OWNER NOTE (2026-09-26): ranking stays CONFIDENCE-primary on purpose.
            # EV-primary was tried and is WRONG here: a Double Chance leg whose
            # odds are derived from the fair 1X2 probability carries the ~6% DC
            # margin, so its EV is always about -6% and it could never out-rank an
            # over/under leg — the very bias the owner complained about. The
            # over/under death-trap is instead fixed at the source: the implied
            # cap above (no leg may be rated above what its own price implies) plus
            # MAX_GOALS_LEGS_PER_SLIP, which forces 1X2 / DC / BTTS onto the rest
            # of the slip. Confidence-primary then simply picks the most-likely
            # leg within that already-diversified set.
            # ── EDGE-AWARE RANKING (2026-10-05, owner request) ──────────────
            # WHY: pure confidence-primary ranking guarantees the shortest
            # price on the board every time, and the bookmaker's margin is
            # WORST (as a percentage) exactly where the price is shortest —
            # ~6% at x1.20 vs ~10% at x1.70. Ranking by probability therefore
            # walks straight into the most expensive part of the book, which is
            # why every slip kept collapsing to x1.6-x1.9.
            #
            # WHAT: base_w is already our edge signal — it folds in team form,
            # injuries/weather, market hit-rate calibration, scout EV and odds
            # drift. The genuine edge on a leg is therefore how far base_w
            # EXCEEDS what that leg's own price already implies. A leg we rate
            # exactly in line with the book (ratio ~1.0) offers no edge at any
            # price; a leg we rate materially above the book offers edge.
            #
            # WHY NOT PURE EV (the trap the owner already hit): a DC leg whose
            # odds are DERIVED from fair 1X2 probabilities structurally carries
            # ~6% DC margin, so its raw EV is always about -6% and it could
            # never out-rank an over/under leg. Comparing each leg against ITS
            # OWN market removes that artefact, because a correctly-priced leg
            # scores ratio ~1.0 whatever market it came from.
            #
            # DAMPING: raw ratio rewards longshots, whose tiny implied
            # probabilities swing wildly on small absolute errors (a 0.42 est
            # vs 0.30 implied looks like a 40% edge when it is mostly rounding).
            # So the ratio is square-rooted (halves the spread, preserves order)
            # and hard-capped, keeping value-awareness without the variance.
            _f = self._implied_by_market(g, h3_probs=h3_probs,
                                      btts_probs=btts_probs,
                                      ou_probs=ou_probs)
            def _edge_key(c):
                o = float(c[0])
                _k0 = float(c[2])            # diligence-weighted confidence
                # This leg's OWN market implied prob, else the raw 1/odds.
                _implied = _f.get(c[3]) or (1.0 / o if o > 1.0 else 1.0)
                # How much we believe it beyond what the price implies.
                _ratio = (_k0 / _implied) if _implied > 1e-6 else 1.0
                _damped = (_ratio ** 0.5) if _ratio > 0 else 0.0
                _damped = max(0.0, min(_damped, self._EDGE_RATIO_CAP))
                _ev = _k0 * o - 1.0
                _kelly = _ev / (o - 1.0) if o > 1.01 else 0.0
                # CONFIDENCE-SCALED bonus, but applied on a BLENDED scale.
                #
                # Three shapes were implemented and MEASURED (see the table
                # below); only this one satisfies both required properties:
                #   (a) k0 * (1 + W*(damped-1))      -> penalised legs we agree
                #       with, needed W~2.5 to flip, and at that W a noisy 6.00
                #       longshot outranked a solid 1.40 favourite.
                #   (b) k0 + k0*W*max(0,damped-1)   -> longshot's tiny implied
                #       prob inflated its ratio (6.00 @0.42 vs implied 0.167 =
                #       ratio 2.52), so from W=0.6 it beat a 2.40 favourite.
                #   (c) (c) trust-scaled but still on the k0 scale -> safe, but
                #       a 0.78 leg needed a 22-point confidence gap to be
                #       overtaken, so edge could NEVER actually flip anything.
                #
                # The resolution: compare on a scale where the two quantities
                # are commensurable. Here k0 is compressed toward 1.0 by
                # _EDGE_CONF_BLEND, so the multiplicative edge term occupies a
                # comparable share of the score instead of being a rounding
                # error on top of a 0-1 probability.
                #
                #   score = k0*(1-B) + B*k0*damped      (B = blend)
                #
                # When a leg merely AGREES with the book (damped~1.0) the edge
                # term vanishes and the score is ~k0, so a solid favourite is
                # left essentially where it was. When we genuinely disagree
                # (damped 1.2-1.35) the edge term is a real, competitive share.
                # The _trust factor still scales the edge term down for
                # longshots, whose ratios are inflated by construction, so a
                # 6.00 shot can never displace a solid favourite.
                _trust = max(0.0, min(1.0, (_k0 - 0.45) / 0.30))
                _blend = self._EDGE_CONF_BLEND
                _edge_term = _k0 * (1.0 + self._EDGE_VALUE_WEIGHT * _trust * (_damped - 1.0))
                _score = _k0 * (1.0 - _blend) + _edge_term * _blend
                return (_score, _damped, _k0, _ev, _kelly, c[1], c[0])
            valid.sort(key=_edge_key, reverse=True)
            o, _w, p, mk, suf = valid[0]
            # DIAG: surface the winner's edge so the log shows whether the
            # machine is finding genuine value or just re-ranking favourites.
            try:
                _bk = _edge_key(valid[0])
                _DIAG["edge_best"] = round(float(_bk[1]), 3)
                _DIAG["edge_pos"] = _DIAG.get("edge_pos", 0) + 1
                if _bk[1] > 1.0:
                    _DIAG["edge_over_mkt"] = _DIAG.get("edge_over_mkt", 0) + 1
            except Exception:
                pass
            # Claim the slip's single BTTS slot only when a BTTS leg is actually
            # drafted for this game (walks the per-slip cap across games).
            if str(mk) in ("btts", "btts_no"):
                btts_used_in_slip = True
            # OWNER RULE (2026-09-26): O/U (goals) legs are capped per slip too.
            # Before this, "over" took every slot (4x over @ 0.93 confidence) —
            # a single correlated bet that dies all four legs at once. Spreading
            # O/U across a slip keeps some 1X2/DC/BTTS legs in the mix.
            elif str(mk).startswith(("over", "under")):
                goals_used_in_slip += 1
            per_game[gid] = (o, f"{g.get('name', '')}{suf}", gid, mk, p)

        cands = list(per_game.values())

        def _best_product(pool):
            """Highest combined odds reachable from `pool` within max_legs.

            This is the number that decides whether the round is buildable at all.
            Counting legs is not enough: four x1.23 legs is a legal-looking pool of
            four that can only ever reach x2.28, under the x2.50 minimum, so the
            round dies in the combination search with a pool that looks healthy.
            """
            top = sorted((float(c[0]) for c in pool), reverse=True)[:max_legs]
            p = 1.0
            for o in top:
                p *= o
            return p

        if len(cands) < min_legs:
            # Never sacrifice quality for quantity: a half-decent product of a
            # weak board is a donation. Skip the round instead of dropping the
            # confidence floor to include garbage legs.
            return None, 0.0
        # ── JEV second opinion ────────────────────────────────────────────
        # When a JEV key is present, ask the typed-decision model one batched
        # noul question per candidate leg and blend its probability into the
        # win-probability used for slip ranking.  Fail-open: any error keeps
        # the engine's own DU/PTN probabilities untouched.
        if self._jev is not None and self._jev.enabled():
            try:
                _nm = {c[2]: (c[1].split(" vs ")[0] if " vs " in (c[1] or "") else c[1])
                       for c in cands}
                _bl = self._jev.blend_legs(
                    [(c[2], c[3], c[0], c[4]) for c in cands], name_map=_nm)
                if _bl:
                    cands = [(_c[0], _c[1], _c[2], _c[3], _bl.get(f"{_c[2]}|{_c[3]}", _c[4]))
                             for _c in cands]
                    self._emit_direct(
                        gui_callback,
                        f"🧠 JEV: blended {len(_bl)} candidate leg(s) with "
                        "second-opinion probabilities")
                else:
                    self._emit_direct(gui_callback,
                                      f"🧠 JEV: no second opinions returned "
                                      f"({self._jev.last_error or 'empty responses'})")
            except Exception as _je:
                self._emit_direct(gui_callback,
                                  f"🧠 JEV blend error (ignored): {str(_je)[:70]}")
        cands.sort(key=lambda c: c[0])
        _DIAG["cand"] = len(cands)
        # Keep a working pool that spans the WHOLE odds range, not just the
        # cheapest few. The builder searches combinations for a product at or
        # above target_min, so it needs the higher-priced legs available: taking
        # only the max_legs+5 CHEAPEST candidates (9 legs at max_legs=4) meant a
        # board of 64 qualified games still could not reach the x2.50 floor,
        # because every leg it was allowed to combine was a short one. The pool
        # is now the full qualifying set, trimmed from the top-priced end so the
        # cheapest (least useful) legs drop first.
        _pool_cap = max(60, (int(max_legs) + 5) * 8)
        pool = cands[-_pool_cap:] if len(cands) > _pool_cap else list(cands)
        mid = (target_min + target_max) / 2.0
        # Use exactly the target window — no hard x3 floor since the window
        # itself is now x5-x15 which is always a decent payout.
        lo = max(self.MIN_COMBINED_ODDS, float(target_min))
        hi = target_max * 1.10

        import itertools

        self._emit_direct(gui_callback,
                          f"🔬 SEL DIAG: {games.__len__()} games in | "
                          f"dropped veto={_DIAG['veto']} used={_DIAG['used']} "
                          f"stale={_DIAG['stale']} | qualifying legs={_DIAG['cand']} "
                          f"| builder pool={len(pool)} "
                          f"| window x{lo:.2f}-x{target_max:.2f} | "
                          f"leg odds {pool[0][0]:.2f}..{pool[-1][0]:.2f}"
                          f" | games_reached_rank={_census['any_leg']} "
                          f"sub120={_DIAG['all_sub120']} veto={_DIAG['all_raw']} "
                          f"wl={_DIAG['all_whitelist']} cap={_DIAG['all_cap']} "
                          f"grp={_DIAG['all_group_used']} ret={_DIAG['all_retired']} "
                          f"btts={_DIAG['all_btts']} susp={_DIAG.get('all_susp', 0)} "
                          f"no_opts_games={_DIAG['no_options']} "
                          f"res_only_games={_DIAG['res_only']})"
                          if pool else
                          f"🔬 SEL DIAG: {games.__len__()} games in | "
                          f"dropped veto={_DIAG['veto']} used={_DIAG['used']} "
                          f"stale={_DIAG['stale']} | qualifying legs=0 "
                          f"| NO POOL — nothing cleared the gates"
                          f" | games_reached_rank={_census['any_leg']} "
                          f"sub120={_DIAG['all_sub120']} veto={_DIAG['all_raw']} "
                          f"wl={_DIAG['all_whitelist']} cap={_DIAG['all_cap']} "
                          f"grp={_DIAG['all_group_used']} ret={_DIAG['all_retired']} "
                          f"btts={_DIAG['all_btts']} susp={_DIAG.get('all_susp', 0)} "
                          f"no_opts_games={_DIAG['no_options']} "
                          f"res_only_games={_DIAG['res_only']})")

        def _joint(combo):
            prod_o = 1.0
            prod_p = 1.0
            for c in combo:
                prod_o *= c[0]
                prod_p *= c[4]
            return prod_o, prod_p

        def _cap_ok(combo) -> bool:
            """True when no single market holds more than MAX_MARKET_LEGS_PER_SLIP
            slots in this combo.

            The cap used to be checked only AFTER a slip was chosen, so the
            builder could spend a full crawl assembling a combo that the caller
            then threw away ("over15 held more than 2 legs") and the round was
            lost for nothing. Applying it here makes the search return a slip
            that is actually placeable."""
            counts: dict = {}
            for c in combo:
                mk = c[3]
                counts[mk] = counts.get(mk, 0) + 1
                if counts[mk] > self.MAX_MARKET_LEGS_PER_SLIP:
                    return False
            return True

        best = None
        best_rank = None
        for size in range(min_legs, max_legs + 1):
            if len(pool) < size:
                break
            for combo in itertools.combinations(pool, size):
                prod_o, prod_p = _joint(combo)
                if prod_o < lo or prod_o > hi:
                    continue
                if not _cap_ok(combo):
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
            # Near-miss fallback: find the closest combo to the target window,
            # but never below the owner's combined-odds floor (MIN_COMBINED_ODDS).
            floor = max(self.MIN_COMBINED_ODDS, float(target_min) * 0.85)
            for size in range(min_legs, max_legs + 1):
                if len(pool) < size:
                    break
                for combo in itertools.combinations(pool, size):
                    prod_o, prod_p = _joint(combo)
                    if prod_o > target_max * 1.1 or prod_o < floor:
                        continue
                    if not _cap_ok(combo):
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

        # ── 2-leg high-confidence shortcut ────────────────────────────────
        # When the normal window finds nothing, check if we have at least 2
        # legs with ≥72% weighted probability each.  A 2-leg slip at (0.72)² = 52%
        # win rate is genuinely profitable — kept above the combined-odds floor.
        if not prefer_more_legs and len(pool) >= 2:
            best_2 = None
            best_2_rank = None
            for combo in itertools.combinations(pool, 2):
                prod_o, prod_p = _joint(combo)
                # Both legs must be high-confidence and combined odds worthwhile
                if min(c[4] for c in combo) < 0.72:
                    continue
                if prod_o < self.MIN_COMBINED_ODDS or prod_o > 8.0:
                    continue
                if not _cap_ok(combo):
                    continue
                rank = (prod_p, prod_o)
                if best_2_rank is None or rank > best_2_rank:
                    best_2_rank = rank
                    best_2 = (combo, prod_o)
            if best_2:
                return best_2

        # ── Greedy minimum-odds build (owner rule 2026-09): a round must never
        # be skipped with a solid >= x2 pickable on the table. When every window
        # and fallback above finds nothing, ADD more games — the strongest
        # available legs — until the slip clears the combined-odds floor
        # (MIN_COMBINED_ODDS, which is >= x2.00). Order-agnostic so the added
        # games are simply the best-probability picks left; the confidence floor
        # is never lowered to include a weak leg.
        gsorted = sorted(cands, key=lambda c: (c[4], c[0]), reverse=True)
        g_chosen = []
        g_prod = 1.0
        for c in gsorted:
            g_chosen.append(c)
            g_prod *= c[0]
            if len(g_chosen) >= min_legs and g_prod >= self.MIN_COMBINED_ODDS:
                return g_chosen, g_prod
            if len(g_chosen) >= max_legs:
                break
        if len(g_chosen) >= min_legs and g_prod >= self.MIN_COMBINED_ODDS:
            return g_chosen, g_prod

        return None, 0.0

    def _click_selected_legs(self, driver, legs, gui_callback=None) -> int:
        """Click the chosen odd for every leg straight off the HYDRATED listing
        rows (the main pages — where the prices we priced the slip from actually
        live), then use the FULL-MARKET page only as a last-resort fallback.

        The betslip panel is persistent across navigation, so selections
        accumulate into one accumulator as the tool tours the games."""
        if not getattr(self, "running", True):
            return 0
        market_selected = 0
        listing_selected = 0
        skipped = 0
        # ── Slip-guard: the listing tour costs a full page load per page and is
        # exactly what wakes the SPA's silent ~7min empty re-mount. Once we already
        # have a payable slip (>=2 live selections), STOP touring other listing
        # pages and skip the market-page fallback — only the CURRENT page may top
        # up remaining stragglers, and a miss is a cheap skip, not a 4-page crawl.
        def _living(drv):
            try:
                return max(0, int(self._read_betslip_count(drv) or 0))
            except Exception:
                return -1
        for odds, name, gid, market, prob in legs:
            if not getattr(self, "running", True):
                break
            home = name.split(" vs ")[0].strip() if " vs " in name else str(name).strip()
            # ── Primary path: click the odd on a LISTING row (main page) ──
            # The board's own prices came off those hydrated rows, so the same
            # DOM has the click. Open the market page only if the row can't.
            _ls_cands = []
            _cur = ""
            try:
                _cur = driver.current_url or ""
            except Exception:
                _cur = ""
            if _cur and _cur not in _ls_cands:
                _ls_cands.append(_cur)
            _src = self._gid_src.get(str(gid))
            if _src and _src not in _ls_cands:
                _ls_cands.append(_src)
            for _u in (self.POPULAR_GAMES_URL, self.UPCOMING_GAMES_PAGE_URL,
                       self.FOOTBALL_HOME_URL, self.TODAY_GAMES_PAGE_URL):
                if _u not in _ls_cands:
                    _ls_cands.append(_u)
            # Search every candidate listing page for this leg. Narrowing to the
            # current page when the slip already held 2 legs was the other half
            # of the stop-short behaviour removed above: it abandoned the search
            # while legs were still available, which is how a round ended up
            # offering a x1.12 slip the floor then had to refuse.
            ok = False
            for _lpage in _ls_cands:
                if not getattr(self, "running", True):
                    break
                if _lpage != _cur:
                    try:
                        self._safe_get(driver, _lpage)
                        # Hydration wait: listing pages sit behind "Challenge
                        # Validation" walls / Angular hydration that render 0
                        # event-rows for 15-30s. Running the row matcher after a
                        # fixed 1.2s sleep only ever saw an empty DOM. Poll until
                        # real rows appear (or timeout).
                        _rw_deadline = time.time() + 15
                        while time.time() < _rw_deadline:
                            try:
                                _rows = driver.execute_script(
                                    "return document.querySelectorAll('.event-row:not(.event-row-header)').length;") or 0
                                if _rows > 0:
                                    break
                            except Exception:
                                pass
                            time.sleep(0.75)
                        self._scroll_to_load_more_games(driver, max_scrolls=2,
                                                        gui_callback=gui_callback)
                    except Exception:
                        pass
                ok = self._click_leg_on_listing_row(driver, home, gid, market)
                if ok:
                    listing_selected += 1
                    self._emit_direct(gui_callback,
                                      f"   ✅ {name} [{market}] @{odds:.2f} selected "
                                      "(listing row)")
                    break
            # ── Fallback: the FULL-MARKET page ──────────────────────────────────
            # ALWAYS reachable, even when the game's row is not on the board we
            # happen to be looking at: it is a per-game URL keyed on gid.
            #
            # STOP-SHORT FIX (2026-10-05). This used to give up as soon as the
            # slip held >= 2 legs ("slip already payable"). That is only true if
            # those 2 legs clear the odds floor - and very often they do not.
            # Live run: four legs chosen, two of them for games on tomorrow's
            # board that the current page cannot show, both dropped as "already
            # payable", leaving 1.10 x 1.10 = a x1.12 slip that the floor then
            # (correctly) refused. The round died with two legs it could have
            # used still available.
            #
            # So: keep working every leg we were given. The per-game page is
            # slower than a listing row, but losing the round costs far more
            # than a few seconds.
            if not ok:
                time.sleep(0.5)
                ok = self._click_leg_on_market_page(driver, gid, home, market,
                                                    odds, name, gui_callback=gui_callback)
                if not ok:
                    time.sleep(0.8)
                    ok = self._click_leg_on_market_page(driver, gid, home, market,
                                                        odds, name, gui_callback=gui_callback)
                if ok:
                    market_selected += 1
                else:
                    skipped += 1
                    self._emit_direct(gui_callback,
                                      f"   ❌ {name} [{market}] not clickable "
                                      f"(gid {gid}) — no listing row and no market page")
        total = market_selected + listing_selected
        # ── Owner rule: a "selected" click that never registered in the Angular
        # BetslipService is a phantom — the slip looks full to us but is empty or
        # short, which is exactly how a place step dies on "Total odds: None".
        # Cross-check against the live slip count; a mismatch re-sweeps the same
        # legs (the clickers skip 'picked' cells, so this only tops up the ones
        # the SPA never counted) and re-verifies before we ever call it done.
        real_count = self._read_betslip_count(driver)
        if isinstance(real_count, (int, float)) and 0 <= real_count < total and \
                getattr(self, "running", True):
            self._emit_direct(gui_callback,
                              f"   🧮 BetslipService shows {real_count} of {total} selections — "
                              "topping up the ones the SPA did not register...")
            for odds, name, gid, market, prob in legs:
                if not getattr(self, "running", True):
                    break
                rc = self._read_betslip_count(driver)
                if isinstance(rc, (int, float)) and rc >= len(legs):
                    break
                home = name.split(" vs ")[0].strip() if " vs " in name else str(name).strip()
                if self._click_leg_on_listing_row(driver, home, gid, market):
                    time.sleep(0.4)
            time.sleep(1.0)
            real_count = self._read_betslip_count(driver)
        if isinstance(real_count, (int, float)) and real_count >= 0 and total != real_count:
            total = real_count
            skipped = max(skipped, len(legs) - total)
        if isinstance(real_count, (int, float)) and real_count >= 0:
            self._emit_direct(gui_callback,
                              f"   🧮 BetslipService verified: {real_count} selection(s) live on the slip")
        if total:
            parts = []
            if listing_selected:
                parts.append(f"{listing_selected} on listing row")
            if market_selected:
                parts.append(f"{market_selected} on market page")
            self._emit_direct(gui_callback,
                f"   ✅ {total} leg(s) selected: {', '.join(parts)}"
                + (f" | {skipped} skipped" if skipped else ""))
        else:
            self._emit_direct(gui_callback,
                f"   ⚠️ No legs selected — {skipped} skipped, re-crawling in 300s")
        return total

    def _click_leg_on_market_page(self, driver, gid, home, market, odds, name,
                                  gui_callback=None) -> bool:
        """Open the game's FULL-MARKET page, click the tool-chosen odd there,
        then return to Today's Games (slip survives the navigation — that is how
        selections accumulate). Returns True when the odd was clicked."""
        try:
            # If we are still on a previous game's /markets page, come back to
            # the listing first so the right game's expander gets clicked.
            cur = ""
            try:
                cur = driver.current_url or ""
            except Exception:
                cur = ""
            if "/markets" in cur:
                try:
                    self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                    time.sleep(0.8)
                except Exception:
                    pass
            res = self._open_game_full_markets(driver, gid=gid, timeout=25,
                                               gui_callback=gui_callback)
            if res.get("status") != "ok" or not res.get("url"):
                self._emit_direct(gui_callback,
                                  f"   ❌ market page unavailable for {name} "
                                  f"[{market}] (gid {gid}) — status={res.get('status')!r}")
                return False
            # Page-settle wait: let the full-market DOM render before
            # attempting the execute_script click (prevents stale-element aborts).
            time.sleep(1.2)
            try:
                for _ in range(12):
                    if driver.execute_script("return document.readyState") == "complete":
                        break
                    time.sleep(0.15)
            except Exception:
                pass
            clicked = driver.execute_script(r"""
var market = arguments[0];
var boxes = document.querySelectorAll('.event-market');
function nmText(i) {
    var el = boxes[i].querySelector('.event-market-name');
    return el ? (el.innerText || '').trim().toUpperCase() : '';
}
var best = null;
for (var i = 0; i < boxes.length; i++) {
    if (!best) {
        var nm = nmText(i);
        var sels = boxes[i].querySelectorAll('.event-selection:not(.placeholder):not(.event-selection-disabled)');
        var selTxt = '';
        for (var s = 0; s < sels.length; s++) selTxt += ' ' + ((sels[s].innerText || '').replace(/\s+/g, ' ').trim());
        var U = (nm + ' ' + selTxt).toUpperCase();
        var isOver = market.indexOf('over') === 0;
        var isUnder = market.indexOf('under') === 0;
        var isFtts = market.indexOf('ftts_') === 0;
        var isDnb = market.indexOf('dnb_') === 0;
        if (market === 'home' || market === 'draw' || market === 'away') {
            if (U.indexOf('3 WAY') < 0 && U.indexOf('1X2') < 0 && U.indexOf('MATCH WINNER') < 0) continue;
        } else if (market === 'btts' || market === 'btts_no') {
            if (U.indexOf('BOTH TEAMS') < 0 && U.indexOf('BTTS') < 0) continue;
        } else if (market === 'dc_1x' || market === 'dc_x2' || market === 'dc_12') {
            if (U.indexOf('DOUBLE CHANCE') < 0) continue;
        } else if (isDnb) {
            if (U.indexOf('DRAW NO BET') < 0 && U.indexOf('DNB') < 0) continue;
        } else if (isFtts) {
            if (U.indexOf('FIRST TEAM TO SCORE') < 0 && U.indexOf('1ST TEAM') < 0 && U.indexOf('FIRST GOAL') < 0) continue;
        } else if (isOver || isUnder) {
            // line is encoded in the market key: over15 -> 1.5, over35 -> 3.5.
            // A bare 'over'/'under' means the 2.5 line (the tool default).
            // NOTE: for a bare key lineKey is '' — do NOT let that produce
            // "undefined." (old bug: always -1, so the box was never clicked).
            var lineKey = market.replace(/^(over|under)/, '');
            var lineDot = lineKey === '' ? '2.5' : (lineKey.length === 1 ? lineKey + '.0' : lineKey[0] + '.' + lineKey.slice(1));
            if (U.indexOf('OVER') < 0 && U.indexOf('UNDER') < 0 && U.indexOf('TOTAL') < 0) continue;
            if ((nm + ' ' + selTxt).indexOf(lineDot) < 0) continue;
        } else {
            if (U.indexOf('OVER') < 0 && U.indexOf('UNDER') < 0) continue;
            var has15 = (nm + ' ' + selTxt).indexOf('1.5') >= 0;
            var has25 = (nm + ' ' + selTxt).indexOf('2.5') >= 0;
            if (market === 'over15') {
                if (!has15 || has25) continue;
            } else {
                if (!has25) continue;
            }
        }
        best = boxes[i];
        break;
    }
}
if (!best) return false;
var sels = best.querySelectorAll('.event-selection:not(.placeholder):not(.event-selection-disabled)');
var idx = 0;
if (market === 'draw' || market === 'away') idx = market === 'draw' ? 1 : 2;
else if (market === 'btts_no' || market === 'under') idx = 1;
else if (market.indexOf('under') === 0) idx = 1;
else if (market === 'dc_x2') idx = 1;
else if (market === 'dc_12') idx = 2;
else if (market === 'dnb_away') idx = 1;
else if (market === 'ftts_away') idx = 1;
else if (market === 'ftts_no') idx = 2;
if (sels.length > idx) {
    if (!sels[idx].classList.contains('event-selection-picked')) {
        try { sels[idx].click(); } catch (e) { return false; }
    }
    return true;
}
return false;
""", market)
            if clicked:
                self._emit_direct(gui_callback,
                                  f"   ✅ {name} [{market}] @{odds:.2f} selected "
                                  "(full-market page)")
                try:
                    self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                    time.sleep(0.8)
                except Exception:
                    pass
                return True
            # "We have other options too" (owner rule): the exact market box was
            # not found on the game's full-market page. Retry the same market
            # FAMILY by alias (3 WAY / BOTH TEAMS / OVER·UNDER / DOUBLE CHANCE /
            # DNB / FIRST TEAM) so a renamed or recalibrated box still yields a
            # selection instead of the round losing a leg.
            clicked = driver.execute_script(r"""
var market = arguments[0];
var boxes = document.querySelectorAll('.event-market');
function nmText(i) {
    var el = boxes[i].querySelector('.event-market-name');
    return el ? (el.innerText || '').trim() : '';
}
var isOver = market.indexOf('over') === 0;
var isUnder = market.indexOf('under') === 0;
var want = null;
if (market === 'home' || market === 'draw' || market === 'away') want = ['3 WAY', '1X2', 'MATCH WINNER'];
else if (market === 'btts' || market === 'btts_no') want = ['BOTH TEAMS', 'BTTS'];
else if (market === 'over' || market === 'under') want = ['OVER', 'UNDER', 'TOTAL'];
else if (market === 'over15') want = ['OVER', 'UNDER', 'TOTAL'];
else if (market.indexOf('dc_') === 0) want = ['DOUBLE CHANCE'];
else if (market.indexOf('dnb_') === 0) want = ['DRAW NO BET', 'DNB'];
else if (market.indexOf('ftts_') === 0) want = ['FIRST TEAM TO SCORE', '1ST TEAM', 'FIRST GOAL'];
if (!want) return false;
var best = null;
var bestText = '';
for (var i = 0; i < boxes.length; i++) {
    var nm = nmText(i);
    var U = nm.toUpperCase();
    var okName = false;
    for (var w = 0; w < want.length; w++) {
        if (U.indexOf(want[w]) >= 0) { okName = true; break; }
    }
    if (!okName) continue;
    var sels = boxes[i].querySelectorAll('.event-selection:not(.placeholder):not(.event-selection-disabled)');
    if (sels.length === 0) continue;
    var selTxt = '';
    for (var s = 0; s < sels.length; s++) selTxt += ' ' + ((sels[s].innerText || '').replace(/\s+/g, ' ').trim());
    // CRITICAL for over/under: the aliased box MUST still be the SAME LINE the
    // selector priced. An unverified 'OVER' match can be Over 0.5 / Over 1.5 at
    // ~1.01 — a donation slip. Verify the line (and for over15, that it is NOT
    // the 2.5 line) exactly like the precise matcher does.
    if (isOver || isUnder) {
        var lineKey = market.replace(/^(over|under)/, '');
        var lineDot = lineKey === '' ? '2.5' : (lineKey.length === 1 ? lineKey + '.0' : lineKey[0] + '.' + lineKey.slice(1));
        var boxTxt = (nm + ' ' + selTxt).toUpperCase();
        if (market === 'over15') {
            if (boxTxt.indexOf('1.5') < 0 || boxTxt.indexOf('2.5') >= 0) continue;
        } else {
            if (boxTxt.indexOf(lineDot) < 0) continue;
        }
    }
    var idx = 0;
    if (market === 'draw' || market === 'away') idx = market === 'draw' ? 1 : 2;
    else if (market === 'btts_no' || market === 'under') idx = 1;
    else if (market.indexOf('under') === 0) idx = 1;
    else if (market === 'dc_x2') idx = 1;
    else if (market === 'dc_12') idx = 2;
    else if (market === 'dnb_away') idx = 1;
    else if (market === 'ftts_away') idx = 1;
    else if (market === 'ftts_no') idx = 2;
    if (sels.length > idx) { best = sels[idx]; break; }
}
if (best) {
    if (!best.classList.contains('event-selection-picked')) {
        try { best.click(); } catch (e) { return false; }
    }
    return true;
}
return false;
""", market)
            if clicked:
                self._emit_direct(gui_callback,
                                  f"   ✅ {name} [{market}] @{odds:.2f} selected "
                                  "(full-market page, aliased box)")
                try:
                    self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                    time.sleep(0.8)
                except Exception:
                    pass
                return True
            self._emit_direct(gui_callback,
                              f"   ⚠️ {name} [{market}] not found on its market page.")
            return False
        except Exception as e:
            self._emit_direct(gui_callback,
                              f"   ⚠️ Market-page pick failed for {name}: {str(e)[:80]}")
            return False

    def _click_leg_on_listing_row(self, driver, home, gid, market) -> bool:
        """Fast fallback: click the odd directly on the Today's Games listing row
        (by event ID, then by home-team name)."""
        try:
            return bool(driver.execute_script(r"""
var home = arguments[0];
var gid = arguments[1];
var market = arguments[2];
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
function marketTarget(row) {
    var query = '';
    if (market === 'home') query = '3 WAY';
    else if (market === 'draw') query = '3 WAY';
    else if (market === 'away') query = '3 WAY';
    else if (market === 'btts') query = 'BOTH TEAMS';
    else if (market === 'btts_no') query = 'BOTH TEAMS';
    else if (market === 'over') query = 'OVER/UNDER';
    else if (market === 'over15') query = '1.5';
    else if (market === 'under') query = 'OVER/UNDER';
    else if (market === 'dc_1x') query = 'DOUBLE CHANCE';
    else if (market === 'dc_x2') query = 'DOUBLE CHANCE';
    else if (market === 'dc_12') query = 'DOUBLE CHANCE';
    if (!query) return null;
    var markets = row.querySelectorAll('.event-market');
    for (var i = 0; i < markets.length; i++) {
        var m = markets[i];
        var nmEl = m.querySelector('.event-market-name');
        var nm = nmEl ? (nmEl.innerText || '').trim().toUpperCase() : '';
        if (nm.indexOf(query) < 0) continue;
        // For over/under variants, verify the correct line (2.5 vs 1.5)
        if (market === 'over' && nm.indexOf('1.5') >= 0) continue;
        if (market === 'over15' && nm.indexOf('1.5') < 0) continue;
        if (market === 'under' && nm.indexOf('1.5') >= 0) continue;
        var sels = m.querySelectorAll('.event-selection:not(.placeholder):not(.event-selection-disabled)');
        if (sels.length === 0) continue;
        // Selection index per market
        var idx = 0;
        if (market === 'draw')   idx = 1;
        else if (market === 'away')    idx = 2;
        else if (market === 'btts_no') idx = 1;
        else if (market === 'under')   idx = 1;
        else if (market === 'dc_1x')   idx = 0;  // 1X is always the first DC selection
        else if (market === 'dc_x2')   idx = 1;  // X2 is the second
        else if (market === 'dc_12')   idx = 2;  // 12 is the third
        if (sels.length > idx) return sels[idx];
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
function rowHits(row) {
    var t = (row.innerText || '').replace(/\s+/g, ' ');
    if (gid && t.indexOf('ID: ' + gid) >= 0) return true;
    if (gid && row.querySelector('[data-id="' + gid + '"], [data-event-id="' + gid + '"], [data-game-id="' + gid + '"], [data-gid="' + gid + '"]')) return true;
    if (gid && row.querySelector('a[href*="/games/' + gid + '"], a[href*="games/' + gid + '"]')) return true;
    if (!gid) return true;
    return false;
}
for (var r = 0; r < rows.length; r++) {
    var row = rows[r];
    if (rowHits(row)) {
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
""", home, gid, market))
        except Exception:
            return False

    def _read_balance_text(self, driver) -> float:
        """Read the wallet balance from the page (skip bet figures like POSSIBLE WIN)."""
        val = self._exec_script(driver, r"""
var b = (document.body && document.body.innerText) || '';
var re = /(?:KSH|KES)\s*([0-9][0-9,]*(?:\.[0-9]{1,2})?)/gi;
var ms = [];
var m;
while ((m = re.exec(b))) ms.push({ v: m[1].replace(/[, ]/g, ''), i: m.index });
for (var k = 0; k < ms.length; k++) {
var before = b.substring(Math.max(0, ms[k].i - 50), ms[k].i).toUpperCase();
if (/(?:POSSIBLE|TOTAL|STAKE|AMOUNT|WIN|ODDS|SELEC.?|BONUS|FREE|CASHBACK|PROMO|MINIMUM|MAXIMUM|ESTIMATED|REWARDS?|POINTS?|CASH\s*OUT|CASEOUT|DEPOSIT|WALLET|BANK|AVAILABLE|WITHDRAW|CASH|PAYOUT|RETURN|PAYBACK|REFUND|ACCOUNT|KES\.?\s*BAL|BALANCE|KES\.\s*KES|REMAINING|SPENDABLE|LIMIT)/i.test(before)) continue;
return ms[k].v;
}
return '';
""", default='', timeout=8.0, refresh_on_hang=True, label="balance text")
        try:
            return float(val or 0)
        except (TypeError, ValueError):
            return 0.0

    def _read_balance_patient(self, driver, wait: float = 20.0) -> float:
        """Patient balance read for headless rounds: the Angular header can lag the
        first paint by seconds, and after a research window the driver can sit on a
        stray tab. Waits for a real figure, re-anchoring to the main today-games
        tab when needed. Returns 0.0 only after `wait` seconds of no luck."""
        balance = self._read_balance_text(driver)
        if balance:
            return balance
        deadline = time.time() + max(4.0, wait)
        reanchored = False
        session_ok = False
        try:
            session_ok = self._session_is_live(driver, deep_check=False)
        except Exception:
            session_ok = False
        while time.time() < deadline:
            time.sleep(1.4)
            try:
                if not reanchored:
                    # After a crawl the driver can sit on a games sub-page whose
                    # header never shows the wallet — force a clean nav to the
                    # listing (the only page guaranteed to render "KSH ...").
                    driver.switch_to.window(driver.window_handles[0])
                    self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                    reanchored = True
                    time.sleep(1.0)
                balance = self._read_balance_text(driver)
                if balance:
                    return balance
                if len(driver.window_handles) > 1:
                    driver.switch_to.window(driver.window_handles[0])
                    self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
            except Exception:
                continue
        return 0.0

    def _read_balance_confirmed(self, driver, wait: float = 20.0,
                                phone: str = None, password: str = None) -> tuple:
        """Authoritative balance read. Returns (balance: float, confirmed: bool).

        confirmed=True  -> the SportPesa API or page definitively returned a figure
                           (including 0.0 if the account is genuinely empty).
        confirmed=False -> balance could not be read at all (page lag, stray tab,
                           stale DOM). The caller MUST NOT treat this as 'no funds'
                           — it should retry later without triggering deposit alerts.

        Tiers, cheapest first:
          1) direct API login with the account's own credentials — the SAME tier
             the GUI's "check balance" button uses, and the only tier that is
             guaranteed to belong to `phone` (see the session guard below)
          2) in-page /api/wallets/balance fetch (needs a live browser session)
          3) patient page-text read (re-anchor + reload)
          4) DOM wallet-snapshot extractor
          5) one last in-page API try

        ACCOUNT SAFETY: tiers 2-5 are all session-scoped — they report whatever
        account the driver happens to be logged into. When the caller names a
        different `phone`, trusting them returns ANOTHER ACCOUNT's balance as
        `confirmed=True`, which silently poisons fleet equity and every drawdown
        decision downstream. So when a specific account is requested we prove the
        session identity first and fall back to the per-account API rather than
        reporting the wrong number.
        """
        want = "".join(ch for ch in str(phone or "") if ch.isdigit())
        session_ok = True
        if want:
            who = ""
            try:
                who = self._who_is_logged_in(driver)
            except Exception:
                who = ""
            session_ok = bool(who) and who[-9:] == want[-9:]
        # 1) direct API login (browser-independent, authoritative, account-correct)
        if want and password:
            try:
                api = self._api_login(self._format_sportsape_login_phone(phone),
                                      password, retries=2)
                if api and api.get("ok"):
                    return float(api.get("balance") or 0), True
            except Exception:
                pass
        if not session_ok:
            # Refuse to answer for an account the session cannot prove it owns.
            # A false balance is worse than an unconfirmed one: the caller can
            # retry a "not confirmed" read, but cannot detect a wrong number.
            return 0.0, False
        # 2) in-page API endpoint — instant when the session is live
        try:
            snap = self._extract_wallet_snapshot_from_sportpesa_api(driver)
            if snap is not None:
                return float(snap.get("balance") or 0), True
        except Exception:
            pass
        # 3) Page-text patient read (re-anchor + reload logic)
        balance = self._read_balance_patient(driver, wait=wait)
        if balance:
            return balance, True
        # 4) DOM wallet-snapshot extractor (targets the balance widget labels)
        try:
            snap = self._extract_wallet_snapshot_from_page(driver)
            if snap and snap.get("balance") is not None:
                return float(snap["balance"]), True
        except Exception:
            pass
        # 5) One last API try after patient wait (page may have settled)
        try:
            snap = self._extract_wallet_snapshot_from_sportpesa_api(driver)
            if snap is not None:
                return float(snap.get("balance") or 0), True
        except Exception:
            pass
        return 0.0, False

    def _load_balance_cache(self) -> dict:
        try:
            if self.BALANCES_PATH.exists():
                data = json.loads(self.BALANCES_PATH.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    return data
        except Exception:
            pass
        return {}

    def _save_balance_cache(self):
        try:
            self.BALANCES_PATH.parent.mkdir(parents=True, exist_ok=True)
            self.BALANCES_PATH.write_text(
                json.dumps(getattr(self, "_balance_cache", {}), indent=2), encoding="utf-8")
        except Exception:
            pass

    def _est_balance_for(self, phone: str) -> tuple:
        """Estimated live balance WITHOUT a live read (owner's model):
        startup/launch sweep balance, MINUS every stake placed since (all active
        stakes deducted; settled wins added back through win-sync which updates
        `_bets`). Returns (balance, source_label); (0.0, "none") if no base
        balance is known at all. This is only a fallback for when the site's
        balance read is slow/unreachable — never blocks a bet or a deposit."""
        phone = str(phone or "")
        base = None
        source = "none"
        sb = getattr(self, "_start_balances", None) or {}
        ent = None
        if isinstance(sb, dict) and sb.get(phone):
            b = sb.get(phone) or {}
            if b.get("confirmed") and float(b.get("balance") or 0) > 0:
                base = float(b.get("balance") or 0)
                source = "launch sweep"
        if base is None:
            ent = self._cached_balance_for(phone, allow_stale=True)
            if ent and ent.get("confirmed"):
                base = float(ent.get("balance") or 0)
                source = "cached"
        # Last resort: ANY confirmed cache entry, no matter how old, is better
        # than shadow picks.  Only used when every live read has failed.
        if base is None:
            try:
                _raw = self._load_balance_cache().get(str(phone or ""))
                if _raw and _raw.get("confirmed"):
                    base = float(_raw.get("balance") or 0)
                    source = "old cache"
            except Exception:
                pass
        if base is None:
            return 0.0, "none"
        active_staked = sum(
            float(b.get("stake") or 0)
            for b in (getattr(self, "_bets", None) or [])
            if (b.get("phone") or "") == phone
            # "unconfirmed" is money that may already be gone from the wallet,
            # so the estimate must subtract it too — otherwise an unconfirmed
            # slip makes the projected balance read HIGH by its stake.
            and (b.get("status") or "active") in ("active", "unconfirmed")
            and not str(b.get("status") or "").startswith("shadow"))
        est = max(0.0, base - active_staked)
        return round(est, 2), source

    def _cached_balance_for(self, phone: str, allow_stale: bool = False) -> dict | None:
        """Return a cached balance if fresh enough, else None.
        allow_stale=True also returns a confirmed-but-old cache entry up to
        BALANCES_STALE_TTL_SECONDS (used as a fallback only when live reads fail)."""
        try:
            cache = getattr(self, "_balance_cache", {})
            ent = cache.get(str(phone or ""))
            if not ent:
                return None
            age = time.time() - float(ent.get("ts") or 0)
            if age < self.BALANCES_TTL_SECONDS:
                return ent
            if allow_stale and ent.get("confirmed") and age < self.BALANCES_STALE_TTL_SECONDS:
                return ent
        except Exception:
            pass
        return None

    def _startup_balance_sweep(self, acc_list, password, gui_callback=None,
                               visible: bool = True, headless: bool = False,
                               driver: webdriver.Chrome = None) -> dict:
        """On start, BEFORE the first bet, log into EVERY account and read its
        balance so the machine knows who has funds to spend. Prevents the false
        'deposit needed' on accounts that simply hadn't been checked yet.

        Uses the passed-in engine driver when available (avoids a second browser),
        otherwise opens a throwaway one for the sweep and quits it. Balances are
        cached with a 5-minute TTL so a restart doesn't re-login all accounts.
        Returns {phone: {"balance": float, "confirmed": bool}}."""
        results = {}
        self._balance_cache = getattr(self, "_balance_cache", None) or self._load_balance_cache()

        def _fresh_confirmed(p):
            """Only a CONFIRMED entry counts as 'already known'. A failed read
            (balance 0.0 / confirmed False) must never suppress a retry, or one
            bad sweep at startup disables that account for the whole session."""
            ent = self._cached_balance_for(p)
            return bool(ent and ent.get("confirmed"))

        pending = [p for p in acc_list if not _fresh_confirmed(p)]
        if not pending:
            self._emit_direct(gui_callback,
                              "💳 Balances already cached (fresh <5 min) — skipping re-check.")
            for p in acc_list:
                ent = self._cached_balance_for(p)
                results[p] = {"balance": float(ent.get("balance") or 0),
                              "confirmed": bool(ent.get("confirmed"))}
            return results
        # ROOT-CAUSE FIX (2026-10-04): NEVER share one browser across accounts.
        # The old sweep built ONE `sweep_driver` with no `phone=` (so it sat
        # outside the per-account ownership guard) and then logged EVERY account
        # in from that same browser. That minted a second live session per account
        # on top of the one the per-account worker already holds, which is exactly
        # what the bookmaker reports as "User logged from another device". The
        # conflict was self-inflicted: the tool was fighting its OWN second login,
        # which is why recovery kept failing with nothing else logged in anywhere.
        #
        # Each account is now read through ITS OWN browser, borrowed via
        # _borrow_account_browser so a live worker session is reused verbatim
        # (owned=False → never quit) and only a genuinely browser-less account
        # gets a temporary one (owned=True → quit right after this sweep).
        for i, p in enumerate(pending, start=1):
            ent = self._cached_balance_for(p)
            if ent is not None and ent.get("confirmed"):
                results[p] = {"balance": float(ent.get("balance") or 0),
                              "confirmed": True}
                continue
            bal = 0.0
            ok = False
            sweep_driver = None
            owned = False
            try:
                sweep_driver, owned = self._borrow_account_browser(
                    p, gui_callback=gui_callback, force_visible=False,
                    mobile=False, headless=True, capture_perf=False, minimize=True)
                # DOUBLE-LOGIN FIX (2026-10-05): the sweep must NEVER
                # authenticate. It runs on its own thread at the same moment the
                # per-account workers perform their own login, so a second
                # POST /login_check for the same account invalidates the first —
                # which is what produced the "invalid session id" +
                # "logged in from another device" storm at startup, along with
                # the 50%+ CPU from the dismiss/re-login thrash.
                # The sweep's only job is to read a balance. If a session is
                # already live it reads it; otherwise it defers to the worker,
                # which is already logging in and will read the balance itself.
                if self._session_is_live(sweep_driver, deep_check=True):
                    bal, ok = self._read_balance_confirmed(
                        sweep_driver, wait=10.0, phone=p, password=password)
                else:
                    ok = False
            except Exception as e:
                msg = str(e)
                if ("Timed out receiving message from renderer" in msg
                        or "renderer" in msg.lower() or "script timeout" in msg):
                    self._emit_direct(gui_callback,
                                      f"⏸️ Sweep {p}: renderer busy — skipped, will retry next cycle.")
                else:
                    self._emit_direct(gui_callback, f"⚠️ Sweep {p}: {msg[:70]}")
            finally:
                # Only ever quit a browser THIS sweep created. A borrowed worker
                # browser must be left running or the worker loses its session.
                if owned and sweep_driver is not None:
                    try:
                        sweep_driver.quit()
                    except Exception:
                        pass
                    try:
                        self._clear_account_driver(p)
                    except Exception:
                        pass
            self._balance_cache[str(p)] = {"balance": bal, "confirmed": ok,
                                           "ts": time.time()}
            results[p] = {"balance": bal, "confirmed": ok}
            if ok:
                self._emit_direct(gui_callback, f"💳 Start balance {p}: KES {bal:,.2f}")
            else:
                self._emit_direct(gui_callback,
                                  f"ℹ️ Start balance {p}: unreadable — will recheck at bet time")
        try:
            self._save_balance_cache()
        except Exception:
            pass
        self._emit_direct(gui_callback,
                          f"💳 Balance sweep done: {sum(1 for r in results.values() if r.get('confirmed'))}"
                          f"/{len(results)} accounts confirmed.")
        return results

    def _inject_xhr_capture(self, driver):
        """Inject a lightweight XHR/fetch capture layer into the page. Captured
        requests are stored in window.__sportsape_captured (list of dicts)."""
        try:
            driver.execute_script("""
            if (!window.__sportsape_captured) {
                window.__sportsape_captured = [];
                var origOpen = XMLHttpRequest.prototype.open;
                var origSend = XMLHttpRequest.prototype.send;
                XMLHttpRequest.prototype.open = function(method, url) {
                    this.__sp_method = method;
                    this.__sp_url = url;
                    return origOpen.apply(this, arguments);
                };
                XMLHttpRequest.prototype.send = function(body) {
                    window.__sportsape_captured.push({
                        t: Date.now(), type: 'xhr',
                        method: this.__sp_method, url: this.__sp_url,
                        body: (typeof body === 'string' ? body : null)
                    });
                    return origSend.apply(this, arguments);
                };
                var origFetch = window.fetch;
                window.fetch = function(url, opts) {
                    var u = (typeof url === 'string') ? url : (url && url.url) || '';
                    window.__sportsape_captured.push({
                        t: Date.now(), type: 'fetch',
                        method: (opts && opts.method) || 'GET', url: u,
                        body: (opts && typeof opts.body === 'string') ? opts.body : null
                    });
                    return origFetch.apply(this, arguments);
                };
            }
            window.__sportsape_captured = [];
            """)
        except Exception:
            pass

    def _read_xhr_capture(self, driver, path_filter: str = "") -> list:
        """Read captured XHR/fetch entries (optionally filtered by URL substring)."""
        try:
            data = driver.execute_script(
                "var c = window.__sportsape_captured || [];"
                + ("c = c.filter(function(e){return e.url.indexOf('" + path_filter.replace("'", "") + "') !== -1;});"
                   if path_filter else "")
                + "return c;")
            return data if isinstance(data, list) else []
        except Exception:
            return []

    def _save_captured_route(self, action: str, route: dict):
        """Persist a captured wallet route for future API-first replay.

        Uses writable_path() so a frozen build writes into the live workspace.
        Anchoring this on __file__ put it in the _MEIPASS scratch folder, where
        the write silently failed and every run had to re-capture from scratch.
        """
        try:
            cfg_path = writable_path(os.path.join("config",
                                                  "discovered_sportsape_routes.json"))
        except Exception:
            cfg_path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    "config", "discovered_sportsape_routes.json")
        try:
            existing = {}
            if os.path.exists(cfg_path):
                with open(cfg_path, encoding="utf-8") as f:
                    existing = json.load(f) or {}
        except Exception:
            existing = {}
        wallet = existing.setdefault("wallet", {})
        wallet[action] = route
        os.makedirs(os.path.dirname(cfg_path), exist_ok=True)
        with open(cfg_path, "w", encoding="utf-8") as f:
            json.dump(existing, f, indent=2)

    def _try_api_wallet_action(self, driver, action: str, payload: dict) -> dict:
        """Try a previously-discovered API route for deposit/withdraw.
        Returns {success: bool, response: dict|None}. Only fires if the route
        shape was captured from a successful real browser request."""
        try:
            with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                   "config", "discovered_sportsape_routes.json"),
                      encoding="utf-8") as f:
                routes = json.load(f).get("wallet", {}).get(action)
        except Exception:
            routes = None
        if not routes or not routes.get("url"):
            return {"success": False, "response": None}
        body_str = json.dumps(payload) if payload else "null"
        result = driver.execute_async_script(
            r"""
            var done = arguments[arguments.length - 1];
            var controller = new AbortController();
            var fired = false;
            function finish(payload) {
                if (fired) return;
                fired = true;
                clearTimeout(watchdog);
                done(payload);
            }
            // Self-abort far below the WebDriver script-timeout budget so a slow
            // wallet route can never surface as a raw "script timeout" error.
            var watchdog = setTimeout(function(){ finish({ok:false, status:0, data:null, error:'timeout'}); }, 9000);
            fetch(ROUTE_URL, {
                method: METHOD, credentials: 'include',
                headers: {'Content-Type': 'application/json'},
                body: BODY_STR,
                signal: controller.signal
            }).then(function(r){ return r.json().then(function(d){ finish({ok:r.ok, status:r.status, data:d}); },
                            function(){ finish({ok:r.ok, status:r.status, data:null}); }); })
              .catch(function(e){ finish({ok:false, status:0, data:null, error:(e && e.toString()) || 'fetch-error'}); });
            """.replace("ROUTE_URL", json.dumps(routes["url"]))
               .replace("METHOD", json.dumps(routes.get("method", "POST")))
               .replace("BODY_STR", body_str)
        )
        return {"success": bool(result and result.get("ok")), "response": result}

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
        Returns the verified REAL on-slip stake (float) when good, else False.
        """
        stake = max(self.MIN_STAKE, round(float(stake), 2))
        SANCTIONED = (10.0, 15.0, 20.0)

        # 1) type the exact amount into the real field (precise path)
        if self._type_stake(driver, stake, gui_callback=gui_callback):
            cur = self._read_stake_input(driver) or self._read_betslip_stake_derived(driver)
            self._emit_direct(gui_callback, f"   ✅ Stake typed = KES {cur:.2f}")
            return float(cur or stake)

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
                return float(cur)
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
            return float(cur or stake)

        cur = self._read_stake_input(driver) or self._read_betslip_stake_derived(driver)
        ok = cur is not None and abs(cur - stake) < 1.0
        if not ok and cur is not None and round(cur, 2) >= self.MIN_STAKE:
            # The site only steps in fixed units (10/15/20). Any sanctioned
            # amount is a safe on-slip stake >= the base minimum — including
            # a boost that the site snapped BACK to 10. The boost is optional,
            # so place the real amount rather than aborting (min-10 forever).
            ok = round(cur, 2) >= self.MIN_STAKE
            if ok:
                if round(cur, 2) < round(stake, 2) - 0.5:
                    self._emit_direct(gui_callback,
                                      f"   ↔ Site held stake at KES {cur:.2f} "
                                      f"(requested boost KES {stake:.2f}) — placing at the "
                                      f"sanctioned amount")
                else:
                    self._emit_direct(gui_callback,
                                      f"   ✅ Site stepped stake to KES {cur:.2f} "
                                      f"(requested KES {stake:.2f}) — placing at the real amount")
        if ok:
            self._emit_direct(gui_callback, f"   ✅ Stake = KES {cur:.2f}")
            return float(cur)
        else:
            self._emit_direct(gui_callback,
                              f"   ❌ Stake is KES {cur if cur is not None else '?'} — "
                              f"target was KES {stake:.2f}")
        return False

    def _type_stake(self, driver, stake: float, gui_callback=None) -> bool:
        """Select the real stake field content and type the requested amount.
        Uses a JS scroll+focus (a Selenium el.click() can be intercepted by the
        floating betslip overlay in headless), with the native React-safe setter
        as an immediate fallback."""
        el = self._locate_stake_input(driver)
        if not el:
            return False
        from selenium.webdriver.common.keys import Keys
        try:
            driver.execute_script(
                "arguments[0].scrollIntoView({block:'center',inline:'center'});"
                "arguments[0].focus();", el)
            time.sleep(0.2)
            el.send_keys(Keys.CONTROL, "a")
            el.send_keys(f"{stake:.2f}".rstrip("0").rstrip("."))
            time.sleep(0.3)
            el.send_keys(Keys.ENTER)
            time.sleep(0.4)
            el.send_keys(Keys.TAB)
            time.sleep(0.4)
        except Exception as e:
            # Overlay / interception made typing unreliable → use the click-free
            # native value setter instead (it verifies itself before returning).
            self._emit_direct(gui_callback,
                              f"   ⚖️ Field typing blocked ({str(e)[:60]}) — using native setter")
            if self._set_stake_direct(driver, stake, gui_callback=gui_callback):
                return True
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
            # If the SPA bounced us to /login (auth token lapsed during the long
            # listing tour), the bet POST died before any modal could appear.
            # Fast-detect instead of waiting the full timeout on a dead page.
            try:
                if "/login" in (driver.current_url or ""):
                    return "logged_out"
            except Exception:
                pass
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

    def _place_step_diagnostics(self, driver) -> str:
        """Snapshot the page the instant a placement step looks wrong, so the
        terminal shows whether PLACE BET took us to a logged-out page, a blank
        state, a modal we could not see, or a healthy-but-ignored slip."""
        try:
            snap = driver.execute_script(r"""
var out = { href: (location.href || '').slice(0, 120),
            title: (document.title || '').slice(0, 60) };
out.slip_form = !!document.querySelector('form.live-betslip');
out.amount_input = !!document.querySelector('#amount-prematch');
out.login_form = !!document.querySelector('input[type="password"], #userName, [name="username"], [name="password"]');
out.swal = (function(){ var s = document.querySelector('.sweet-alert, [class*="swal"]'); return s ? ((s.innerText||'').replace(/\s+/g,' ').trim().slice(0,120)) : ''; })();
var pc = 0, els = document.querySelectorAll('a, button, div, span');
for (var i = 0; i < els.length; i++) {
    if (els[i].offsetHeight <= 0) continue;
    if ((els[i].innerText || '').trim().toLowerCase() === 'place bet') pc++;
}
out.place_btns = pc;
out.body_len = (document.body && document.body.innerText) ? document.body.innerText.length : -1;
out.betslip_count = -2;
try { var app = document.querySelector('body');
      out.betslip_count = window.angular.element(app).injector().get('BetslipService').count() || 0; } catch (e) {}
var bt = (document.body && document.body.innerText || '').replace(/\s+/g, ' ').trim().toLowerCase();
out.login_tail = bt.includes('login') || bt.includes('sign in') || bt.includes('password') ? 1 : 0;
out.tail = bt.slice(-220);
var ph = document.querySelector('form.live-betslip');
out.slip_text = ph ? (ph.innerText || '').replace(/\s+/g, ' ').trim().slice(0, 260) : '';
return out;
""")
            if not snap:
                return "diagnostics failed"
            return ("href='%s' title='%s' slip=%s amount=%s login_form=%s "
                    "place_btns=%s count=%s swal='%s' body=%s tail='%s' "
                    "SLIP_TXT='%s'" % (
                        snap.get("href"), snap.get("title"),
                        snap.get("slip_form"), snap.get("amount_input"),
                        snap.get("login_form"), snap.get("place_btns"),
                        snap.get("betslip_count"), snap.get("swal"),
                        snap.get("body_len"), snap.get("tail"),
                        snap.get("slip_text")))
        except Exception as e:
            return f"diagnostics error: {str(e)[:80]}"

    def _place_via_spa_service(self, driver, gui_callback=None, timeout: int = 40) -> dict:
        """PRIMARY placement: call the SPA's own BetslipService.placeBet() in-page.

        This is the exact call the human PLACE button runs and it is the ONLY path
        observed to clear a real bet on SportPesa (verified live: slip emptied and
        KES 10 left the balance). It uses the SPA's restrictions/CSRF/session layer,
        so it also avoids the fragile DOM confirm dialog entirely.

        Returns {"placed": bool, "detail": str}. On success the prematch betslip is
        emptied (removeAllSelections by the SPA after a 2xx), which is how we verify."""
        result = {"placed": False, "detail": "not attempted"}
        try:
            before = self._read_betslip_count(driver)
            if not isinstance(before, (int, float)) or before < 1:
                result["detail"] = f"slip count {before} — nothing to place"
                return result
            try:
                driver.execute_script(r"""
var app = document.querySelector('body');
window.__spaPlace = window.__spaPlace || {state:'idle', detail:''};
window.__spaPlace.state = 'pending';
window.__spaPlace.detail = '';
window.__spaNet = [];
try {
  var hook = function(){
    var o = XMLHttpRequest.prototype.open, s = XMLHttpRequest.prototype.send;
    var store = function(x, when){
      try {
        var entry = window.__spaNet[window.__spaNet.length-1];
        if (entry) { entry[when + 'Status'] = x.status; entry[when + 'Url'] = (x.responseURL||x.url||'').slice(0,200);
          var body = x.responseText || '';
          entry[when + 'Body'] = String(body).slice(0,2000); }
      } catch(e){}
    };
    // ── CAPTURE REQUEST HEADERS (2026-10-05) ───────────────────────────
    // Diagnostic only - no behaviour is changed. The evidence so far says the
    // session is ACCEPTED for reads (wallet/balance returns 200) in the very
    // same round that /api/bets/place answers {"code":403,"message":"Forbidden"}.
    // A dead or superseded token fails both, so this is a control on the bet
    // write rather than on the login. The likeliest explanation is a header (or
    // a cookie the header signs) that the SPA's own placeBet() attaches and our
    // bare fetch() does not. Until we can see the headers, that is a guess - so
    // record them.
    var hdrDump = function(h){
      try {
        var out = {};
        if (!h) return out;
        if (typeof h.forEach === 'function' && typeof h.get === 'function') {
          h.forEach(function(v, k){ out[k] = String(v).slice(0,120); });
        } else {
          for (var k in h) { if (Object.prototype.hasOwnProperty.call(h, k))
            out[k] = String(h[k]).slice(0,120); }
        }
        return out;
      } catch(e){ return {}; }
    };
    // BROAD match: the real endpoint was never confirmed as matching the old
    // /placebet|place_bet|place-bet|betslip/ pattern, so silent misses looked
    // like "no request was made". Capture anything that mutates a betslip OR
    // any POST/PUT, and record non-matches too so we can see what was sent.
    var interesting = function(m, u){
      var mm = (m||'').toUpperCase();
      if (mm === 'POST' || mm === 'PUT') return true;
      return /place|bet|slip|order|ticket/i.test(u||'');
    };
    XMLHttpRequest.prototype.open = function(m, u){
      this.__m = m; this.__u = (u||'').slice(0,250);
      this.__hdrs = {};
      if (interesting(m, this.__u)) {
        window.__spaNet.push({method: this.__m, url: this.__u, reqStatus: null, reqBody: '', respStatus: null, respUrl: '', respBody: '', reqHeaders: {}, via: 'xhr'});
        this.addEventListener('loadend', function(){ store(this, 'resp'); });
      }
      return o.apply(this, arguments);
    };
    XMLHttpRequest.prototype.setRequestHeader = function(k, v){
      try { this.__hdrs = this.__hdrs || {}; this.__hdrs[String(k)] = String(v).slice(0,120); } catch(e){}
      return this.__origSetHeader ? this.__origSetHeader.apply(this, arguments)
                                  : XMLHttpRequest.prototype.setRequestHeader.apply(this, arguments);
    };
    XMLHttpRequest.prototype.send = function(body){
      var entry = window.__spaNet[window.__spaNet.length-1];
      if (entry && !entry.reqSent) {
        try { entry.reqBody = String(body).slice(0,2000); } catch(e){}
        try { entry.reqHeaders = hdrDump(this.__hdrs); } catch(e){}
        entry.reqStatus = this.status; entry.reqSent = true;
      }
      return s.apply(this, arguments);
    };
    // The SPA may use fetch() rather than XHR — hook it too so we never
    // miss the request just because it took the other transport.
    try {
      var of = window.fetch;
      window.fetch = function(input, init){
        var url = (typeof input === 'string') ? input : (input && input.url) || '';
        var m = (init && init.method) || (input && input.method) || 'GET';
        var rec = null;
        if (interesting(m, url)) {
          // `via` separates the SPA's own request from the one our fallback
          // issues. If the SPA's call succeeds and only ours 403s, the missing
          // piece is whatever we do not send - now captured in reqHeaders.
          rec = {method: m, url: String(url).slice(0,250), reqStatus: null,
                 reqBody: init && init.body ? String(init.body).slice(0,2000) : '',
                 respStatus: null, respUrl: '', respBody: '',
                 reqHeaders: hdrDump(init && init.headers),
                 credentials: (init && init.credentials) || 'omitted',
                 via: window.__spaOwnFetch ? 'ours' : 'spa'};
          window.__spaNet.push(rec);
        }
        return of.apply(this, arguments).then(function(resp){
          if (rec) {
            rec.respStatus = resp.status; rec.respUrl = String(resp.url||'').slice(0,200);
            try { resp.clone().text().then(function(t){ rec.respBody = String(t).slice(0,2000); }); } catch(e){}
          }
          return resp;
        });
      };
    } catch(e){}
  };
  try { hook(); } catch(e){}
  var svc = window.angular.element(app).injector().get('BetslipService');
  // ── DEEP PROBE OF THE SLIP SERVICE (2026-10-05) ────────────────────────
  // Diagnostic only - nothing here changes how we place.
  //
  // What we know: BetslipService.count() reports 2 live selections, but the
  // object we have always read (`svc.betslip`) is NULL, and the site's own
  // placeBet() then answers {"code":403,"message":"Forbidden"}. Reads of the
  // wallet succeed in the same round, so the login is fine. A place request
  // with no payload behind it would be refused exactly this way - so the
  // likeliest explanation is that we are reading the count from one place and
  // the actual bet from another that we have never found.
  //
  // Rather than guess the property name, enumerate everything the service
  // exposes (own + prototype, skipping Angular internals) and report which
  // property actually holds selections. That names the field to submit.
  try {
    var probe = {props: [], candidates: []};
    var seen = {};
    var push = function(name, val, depth){
      if (seen[name] && depth === 0) return;
      seen[name] = true;
      var t = (val === null) ? 'null' : (Array.isArray(val) ? 'array['+val.length+']' : typeof val);
      var prev = '';
      try {
        if (typeof val === 'string') prev = val.slice(0,60);
        else if (Array.isArray(val)) prev = JSON.stringify(val.slice(0,2)).slice(0,220);
        else if (val && typeof val === 'object') prev = JSON.stringify(val).slice(0,220);
        else if (typeof val === 'function') prev = '(fn ' + (val.length) + ' args)';
        else prev = String(val).slice(0,60);
      } catch(e){ prev = '(unreadable)'; }
      probe.props.push({n: name, t: t, v: prev});
      // Anything that looks like a collection of bets/legs/selections.
      if (/bet|slip|select|leg|choice|ticket|cart/i.test(name) && val &&
          (Array.isArray(val) || typeof val === 'object')) {
        probe.candidates.push({n: name, t: t, v: prev});
      }
    };
    // Own properties.
    for (var k in svc) {
      if (!Object.prototype.hasOwnProperty.call(svc, k)) continue;
      if (/^\$|^\$\$|^this$/.test(k)) continue;
      try { push(k, svc[k], 0); } catch(e){}
    }
    // Prototype chain (the real API often lives there).
    try {
      var proto = Object.getPrototypeOf(svc), lvl = 0;
      while (proto && lvl < 4) {
        for (var k2 in proto) {
          if (/^\$|^\$\$|^constructor$/.test(k2)) continue;
          try {
            var d = Object.getOwnPropertyDescriptor(proto, k2);
            if (d && typeof d.value !== 'function') push(k2, d.value, lvl+1);
            else if (d && !probe.props.some(function(x){return x.n === k2;}))
              probe.props.push({n: k2, t: 'function', v: '(fn ' + (d.value ? d.value.length : '?') + ' args)'});
          } catch(e){}
        }
        proto = Object.getPrototypeOf(proto); lvl++;
      }
    } catch(e){}
    // One level INTO the top candidates, to see the row shape.
    for (var ci = 0; ci < probe.candidates.length && ci < 4; ci++) {
      try {
        var c = svc[probe.candidates[ci].n];
        if (c && typeof c === 'object' && !Array.isArray(c)) {
          var inner = [];
          for (var k3 in c) { try { inner.push(k3 + ':' + (Array.isArray(c[k3]) ? 'array['+c[k3].length+']' : typeof c[k3])); } catch(x){} }
          probe.candidates[ci].inner = inner.slice(0, 14).join(', ');
        }
      } catch(e){}
    }
    window.__spaPlace.slipProbe = JSON.stringify(probe).slice(0, 4000);
  } catch(e){ window.__spaPlace.slipProbe = 'probe-failed: ' + String(e).slice(0, 300); }
  // Keep a snapshot for continuity, but read it the way the SITE reads it.
  // `svc.betslip` / `svc.betSlip` / `svc.slip` do not exist on this service, so
  // they have always evaluated to null and told us nothing - while count()
  // correctly reported the selections. The real accessors are METHODS, and the
  // dump above names them: getAllBetslips() and getBetslip(id). Calling those
  // is the only way to see whether the service genuinely holds the slip that
  // placeBet() is about to submit.
  try {
    var snap = null, how = '';
    if (typeof svc.getAllBetslips === 'function') {
      snap = svc.getAllBetslips(); how = 'getAllBetslips()';
    } else if (typeof svc.getBetslip === 'function') {
      snap = svc.getBetslip(0); how = 'getBetslip(0)';
    }
    var n = (snap && (snap.length !== undefined)) ? snap.length
          : (snap ? 1 : 0);
    window.__spaPlace.slipBefore = how + ' -> ' + n + ' item(s): '
                                  + JSON.stringify(snap).slice(0, 1200);
    window.__spaPlace.slipCount = n;
  } catch(e){
    window.__spaPlace.slipBefore = 'getAllBetslips threw: ' + String(e).slice(0,200);
    window.__spaPlace.slipCount = -1;
  }
  var p = svc.placeBet();
  if (p && p.then) {
    p.then(function(ok){
        window.__spaPlace.state = 'resolved';
        try { window.__spaPlace.detail = JSON.stringify(ok).slice(0,500) || String(ok); }
        catch(e){ window.__spaPlace.detail = String(ok).slice(0,500); }
      }, function(err){
        var d = '';
        try { d = (err && err.data ? JSON.stringify(err.data) : '')
                    || (err && err.message ? err.message : '') || String(err); } catch(x){ d = String(err); }
        window.__spaPlace.state = 'rejected';
        window.__spaPlace.detail = d.slice(0,500);
      });
  } else {
    window.__spaPlace.state = 'sync';
    window.__spaPlace.detail = String(p).slice(0,300);
  }
} catch(e){
  window.__spaPlace.state = 'threw';
  window.__spaPlace.detail = String(e).slice(0,300);
}
""")
            except Exception as exc:
                result["detail"] = f"inject error: {str(exc)[:120]}"
                return result
            deadline = time.time() + timeout
            state = "pending"
            detail = ""
            count_now = before
            while time.time() < deadline:
                time.sleep(2)
                try:
                    cur = driver.execute_script("return window.__spaPlace || {state:'pending', detail:''};")
                    if isinstance(cur, dict):
                        state = cur.get("state") or state
                        detail = cur.get("detail") or detail
                except Exception:
                    pass
                try:
                    count_now = self._read_betslip_count(driver)
                except Exception:
                    pass
                if count_now == 0 or state in ("resolved", "rejected", "threw", "sync"):
                    break
            # The slip can empty BEFORE the XHR loadend handler has written the
            # response body into __spaNet. Give the event loop a moment so the
            # capture is not read as blank.
            if count_now == 0:
                for _ in range(3):
                    time.sleep(1)
                    try:
                        if driver.execute_script(
                                "var a = window.__spaNet || []; "
                                "return a.length && a[a.length-1] && a[a.length-1].respBody;") :
                            break
                    except Exception:
                        break
            # WAIT FOR THE XHR TO ACTUALLY FINISH (2026-10-07).
            # We read the capture 1-3s after the click, which is often BEFORE
            # loadend fires - so respStatus stayed null and every place attempt
            # logged "httpNone". That is why the real server verdict on
            # /api/bets/place was never actually observed: we were inferring
            # "403" from an earlier sighting rather than reading it. Wait until
            # the request has a status, up to ~10s, so we finally see what the
            # book says.
            for _ in range(10):
                try:
                    _done = driver.execute_script(
                        "var a = window.__spaNet || []; "
                        "return !!(a.length && a[a.length-1] "
                        "&& a[a.length-1].respStatus !== null "
                        "&& a[a.length-1].respStatus !== undefined);")
                except Exception:
                    break
                if _done:
                    break
                time.sleep(1)
            # Read the captured XHR for BOTH outcomes. Previously this only ran
            # on failure, so a SUCCESSFUL bet (slip emptied) returned early
            # and never reported what the server actually said. That is why
            # "Not valid" was never visible: the rejections that mattered all
            # happened on the success-looking branch.
            net_detail = ""
            try:
                n = driver.execute_script(
                    "var a = window.__spaNet || []; return a.length ? a.length : 0;")
                last = driver.execute_script(
                    "var a = window.__spaNet || []; return a.length ? a[a.length-1] : null;")
                if isinstance(last, dict):
                    # 300 chars cut the payload off mid-bets array, hiding the
                    # very fields the API rejects. A generic {"message":"Forbidden"}
                    # is undiagnosable without the body the book was actually sent.
                    resp = str(last.get("respBody") or "").replace("\n", " ")[:1200]
                    req = str(last.get("reqBody") or "").replace("\n", " ")[:1200]
                    net_detail = (f" | NET {last.get('method')} {last.get('url')} "
                                  f"-> http{last.get('respStatus')} {resp}")
                    if req:
                        net_detail += f" | REQ {req}"
                    # Several exchanges can fire around one PLACE. Dump every
                    # captured request/response pair so a retry that failed
                    # differently is still visible.
                    try:
                        allx = driver.execute_script(
                            "var a = window.__spaNet || [];"
                            "return a.map(function(r){ return (r.method||'') + ' ' + "
                            "(r.url||'') + ' -> http' + (r.respStatus||'?') + ' ' + "
                            "String(r.respBody||'').replace(/\\s+/g,' ').slice(0,300); });")
                    except Exception:
                        allx = None
                    if isinstance(allx, list) and len(allx) > 1:
                        net_detail += " | ALL-XHR: " + " || ".join(str(x)[:400] for x in allx[-6:])
                    try:
                        snapb = driver.execute_script(
                            "return (window.__spaPlace && window.__spaPlace.slipBefore) || '';")
                    except Exception:
                        snapb = ""
                    if snapb:
                        net_detail += f" | SLIP-BEFORE: {str(snapb)[:800]}"
            except Exception:
                pass
            # ── REPORT THE SLIP-SERVICE PROBE (2026-10-05) ────────────────
            # Diagnostic only. We read the selection COUNT from one place and
            # the actual bet payload has always been null, so we enumerate what
            # the service really holds and name the field that carries the
            # selections. Print it whenever the place did not succeed - that is
            # exactly when we need to know.
            if not result.get("placed"):
                try:
                    _pj = self._exec_script(
                        driver,
                        "return (window.__spaPlace && window.__spaPlace.slipProbe) || '';",
                        default="", timeout=10.0, label="slip probe")
                    if _pj:
                        self._emit_direct(
                            gui_callback,
                            f"  \U0001f50e SLIP-SERVICE PROBE ({len(_pj)} chars): "
                            f"{_pj[:900]}")
                        try:
                            _po = json.loads(_pj)
                            _cands = _po.get("candidates") or []
                            if _cands:
                                self._emit_direct(
                                    gui_callback,
                                    f"  \U0001f3af CANDIDATE SLIP FIELDS: "
                                    + " | ".join(
                                        f"{c.get('n')}[{c.get('t')}]"
                                        + (f"{{{c.get('inner')}}}" if c.get("inner") else "")
                                        for c in _cands[:5]))
                            else:
                                self._emit_direct(
                                    gui_callback,
                                    "  \U0001f3af CANDIDATE SLIP FIELDS: none matched "
                                    "(count() works but no bet/leg/selection object "
                                    "is exposed on the service)")
                        except Exception:
                            pass
                except Exception:
                    pass
            if count_now == 0:
                result = {"placed": True,
                          "detail": f"slip emptied (was {before}); spa={state} "
                                    f"captured={n}".
                                    replace("\n", " ")[:200] + net_detail}
            else:
                result = {"placed": False,
                          "detail": f"count still {count_now}/{before}; spa={state} {detail} "
                                    f"captured={n}".
                                    replace("\n", " ")[:420] + net_detail}
        except Exception as exc:
            result = {"placed": False, "detail": f"place-via-spa error: {str(exc)[:140]}"}
        return result

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
            # JS fallback (2026-09-30): the DOM remove buttons are frequently
            # rendered OFF the live box (folded, renamed, or below the fold) so
            # the XPath sweep above clears nothing while BetslipService —
            # the SAME service _read_betslip_count uses — still holds every leg.
            # Drive the service directly: call every plausible bulk-clear method
            # it exposes (favourite/star/remove/clear/cancel/reset), then re-read
            # the service count like _read_betslip_count does.
            try:
                driver.execute_script(r"""
var app = document.querySelector('body');
try {
  var svc = window.angular.element(app).injector().get('BetslipService');
  var tried = [];
  var cands = ['removeAll','removeAllSelections','clearAll','clearAllSelections',
               'clear','empty','cancelAll','reset','remove'];
  for (var i=0; i<cands.length; i++){
    if (typeof svc[cands[i]] === 'function') {
      try { svc[cands[i]](); tried.push(cands[i]); } catch(e){ tried.push(cands[i]+':ERR'); }
    }
  }
  window.__spaClear = tried;
} catch(e){ window.__spaClear = ['no-svc']; }
""")
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

    def _open_betslip_and_place(self, driver, stake: float, phone: str = "",
                                password: str = "", gui_callback=None,
                                before_balance: float = 0.0,
                                max_attempts: int = 6,
                                legs: list = None) -> object:
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
        slip_count_at_open = self._read_betslip_count(driver)

        # ── ODDS FLOOR (2026-10-05) ─────────────────────────────────────
        # The site's periodic slip refresh silently strips selections whose
        # odds it no longer holds. The re-click above tops the legs back up,
        # but the SURVIVING odds can still be far below what we selected — a
        # slip targeting x2.50 was observed going out at x1.29, i.e. we paid
        # the accumulator margin for a fraction of the intended payout.
        # Placing a degraded slip is worse than not betting: it converts a
        # positive-EV ticket into a negative-EV one. So when the caller told us
        # the floor it insists on, we refuse anything under it.
        try:
            _floor = float(getattr(self, "_active_odds_floor", 0.0) or 0.0)
            _got = float(totals.get("odds") or 0.0)
            if _floor > 0 and 0 < _got < _floor:
                self._emit_direct(
                    gui_callback,
                    f"  ⛔ Slip odds {_got:.2f} are below the required floor x{_floor:.2f} "
                    "(legs were stripped by the site refresh) — declining rather than "
                    "placing a degraded accumulator.")
                try:
                    self._clear_betslip(driver, gui_callback=gui_callback)
                except Exception:
                    pass
                return {"needs_legs": True, "count": 0}
        except Exception:
            pass

        consec_invalid = 0
        minted = False
        # Bounds the "silent slip" recovery: without a cap the probe could
        # re-trigger on every iteration and burn all attempts (see the
        # _post_shell_recovers comment below).
        self._post_shell_recovers = 0
        for attempt in range(1, max_attempts + 1):
            # If the SPA is on /login (token lapse is invisible to slip counting),
            # re-login produces an empty betslip — hand back so the caller rebuilds.
            try:
                on_login = "/login" in (driver.current_url or "")
            except Exception:
                on_login = False
            if on_login:
                self._emit_direct(gui_callback,
                                  "  🔁 On /login before placing — returning slip for fresh "
                                  "re-login + quick rebuild (minted token).")
                if self._clear_betslip(driver, gui_callback=gui_callback):
                    return {"needs_legs": True, "count": 0}
                return False
            # ── Session-mint gate: the SPA drops a lapsed token into a silent
            # logged-out shell on the listing URL (no /login redirect) — slip
            # reads empty AND the page body shrinks to a bare shell (no rows).
            # Probe those two together (a live-slip or a full listing never
            # triggers); only then mint a fresh token, re-click the legs, and
            # re-enter the attempt (bounded to ONE mint per call).
            if phone and password and not minted and legs:
                mint_now = False
                try:
                    mint_now = bool(driver.execute_script(r"""
var c = -1;
try { var app = document.querySelector('body');
      c = window.angular.element(app).injector().get('BetslipService').count() || 0; } catch (e) {}
var bodyLen = (document.body && document.body.innerText || '').length;
return c === 0 && bodyLen < 40000;
"""))
                except Exception:
                    mint_now = False
                if mint_now:
                    # DO NOT MINT BLINDLY (fix 2026-10-05). Minting means POSTing
                    # credentials again, and that SUPERSEDES our own current
                    # token. The old code minted whenever the SPA showed a bare
                    # shell, even though its own comment admitted the wallet API
                    # was still live and only the hydrated slip had been lost.
                    # So a purely cosmetic SPA re-mount was answered by
                    # re-authenticating, which is the single best way to make an
                    # account collide with itself ('User logged from another
                    # device'). Live run: 9 such rejections and 6 failed gates in
                    # one hour, zero bets placed.
                    #
                    # We now ask the only question that matters - is the session
                    # actually dead? - and act accordingly:
                    #   session LIVE -> cheap navigation re-hydrates the SPA,
                    #                   no new token, no collision risk
                    #   session DEAD -> minting is the only way back, so do it
                    live = False
                    try:
                        live = bool(self._session_is_live(driver, deep_check=True))
                    except Exception:
                        live = False
                    if live:
                        self._emit_direct(
                            gui_callback,
                            "  🔒 SPA lost its slip but the session is still LIVE — "
                            "reloading the board instead of re-authenticating "
                            "(minting here would supersede our own token).")
                        try:
                            self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                            time.sleep(1.2)
                        except Exception:
                            pass
                    else:
                        self._emit_direct(
                            gui_callback,
                            "  🔒 Session shell AND wallet API dead — "
                            "forcing a fresh real-login POST before PLACE.")
                        if not self._hard_spa_login(driver, phone, password,
                                                    gui_callback=gui_callback, force=True):
                            self._emit_direct(
                                gui_callback,
                                "  🔒 Forced re-login did not confirm the session — aborting.")
                            return False
                        minted = True
                    # Same reasoning as the post-typing recovery: a
                    # listing-only re-click finds nothing once the SPA has
                    # re-mounted, so the slip stays empty and the round dies.
                    # Delegate to the robust path (listing rows + market pages).
                    try:
                        re_clicked = int(self._click_selected_legs(
                            driver, legs, gui_callback=gui_callback) or 0)
                    except Exception:
                        re_clicked = 0
                    time.sleep(0.8)
                    self._emit_direct(gui_callback,
                                      f"  🔒 Slip re-clicked {re_clicked} leg(s) on the fresh session")
                    continue
            slip_count = self._read_betslip_count(driver)
            # ── Owner rule: the site's periodic slip refresh silently strips
            # selections whose odds it no longer holds. Instead of handing back
            # for a costly 2-4 min board re-crawl, RE-CLICK any missing legs
            # straight off the page we're already on (rows are here; the clickers
            # skip already-picked cells, so this only tops up the stripped ones)
            # and place in the same breath — the fresh slip has ~no exposed idle.
            if legs and isinstance(slip_count, (int, float)) and 0 <= slip_count < len(legs):
                self._emit_direct(gui_callback,
                                  f"   🧮 Slip shrank to {slip_count} of {len(legs)} — "
                                  "re-clicking stripped legs on the current page...")
                for odds, name, gid, market, prob in legs:
                    if self._read_betslip_count(driver) >= len(legs):
                        break
                    home = name.split(" vs ")[0].strip() if " vs " in name else str(name).strip()
                    if self._click_leg_on_listing_row(driver, home, gid, market):
                        time.sleep(0.4)
                time.sleep(0.8)
                slip_count = self._read_betslip_count(driver)
                if isinstance(slip_count, (int, float)) and slip_count >= 0:
                    self._emit_direct(gui_callback,
                                      f"   🧮 BetslipService re-verified: {slip_count} selection(s)")
            # SLIP-STACKING GUARD (2026-09-30): a rebuild re-clicks its new legs
            # on top of whatever the previous failed attempt left in the slip.
            # _clear_betslip is best-effort and often returns False (legs below
            # the fold / renamed buttons), so the slip compounds 3 → 6 → 8 and
            # the extra selections are exactly what keeps the submit dead with
            # "Not valid". If the live slip holds MORE legs than we requested,
            # it is polluted: refuse to submit it, clear hard, and hand back so
            # the caller rebuilds from a genuinely empty slip.
            if legs and isinstance(slip_count, (int, float)) and slip_count > len(legs):
                self._emit_direct(gui_callback,
                                  f"   🧹 Slip has {slip_count} selections — {len(legs)} requested "
                                  "(stale legs stacked from a previous attempt) — clearing "
                                  "hard before the next rebuild.")
                self._bench_slip_legs(legs)
                try:
                    self._clear_betslip(driver, gui_callback=gui_callback)
                except Exception:
                    pass
                return {"needs_legs": True, "count": 0, "stacked": True}
            # The slip is empty or shrank below 2 selections. Empty means the
            # removal prompt stripped every selection without placing — rebuild.
            if slip_count == 0 or (slip_count > 0 and slip_count < 2):
                self._emit_direct(gui_callback,
                                  f"⚠️ {slip_count if slip_count > 0 else 'No'} selection(s) "
                                  "left on the slip (games removed/already in play) — "
                                  "need at least 2 to bet.")
                return {"needs_legs": True, "count": slip_count}

            stake_ok = self._set_stake_in_betslip(driver, stake, gui_callback=gui_callback)
            if not stake_ok:
                # Never place with an unverified stake. Placing anyway is what
                # surfaced as "insufficient funds" / oversized bets when the slip
                # kept its default or last-used amount instead of the requested one.
                self._emit_direct(gui_callback,
                                  f"  🛑 ABORT: could not set the stake to KES {stake:,.2f}. "
                                  "Not placing the bet with an unknown stake.")
                self._emit_direct(gui_callback,
                                  f"  🔬 PLACE-STATE: {self._place_step_diagnostics(driver)}")
                return False
            # The site can step the stake (10/15/20 units) onto a real, sanctioned
            # amount different from the requested one — place at THAT real value.
            stake = float(stake_ok)
            self._emit_direct(gui_callback,
                              f"  Placing at the real on-slip stake KES {stake:,.2f}")
            # ── Shell probe AFTER stake typing: the SPA's silent empty re-mount
            # (~7min after login) hits WHILE we type the stake — the mint gate above
            # ran pre-typing so it may have missed it. If the slip is now empty on a
            # bare page, force a REAL re-login POST and re-click the legs on the
            # fresh hydrated session, then restart this attempt (the fresh session's
            # page-load re-renders the whole shell away). Bounded: only one force
            # mint per attempt iteration via `minted`.
            if (phone and password and legs and not minted
                    and self._post_shell_recovers < 2):
                try:
                    post_shell = bool(driver.execute_script(r"""
var c = -1;
try { var app = document.querySelector('body');
      c = window.angular.element(app).injector().get('BetslipService').count() || 0; } catch (e) {}
var bodyLen = (document.body && document.body.innerText || '').length;
return c === 0 && bodyLen < 40000;
"""))
                except Exception:
                    post_shell = False
                if post_shell:
                    # SECOND OPINION BEFORE DESTROYING A GOOD SLIP (2026-10-05).
                    # The probe above reads the slip through one raw angular
                    # injector call. If that path is mid-re-mount it can report
                    # 0 while the slip is in fact intact - and we would then
                    # reload the board and throw away a fully priced
                    # accumulator. Cross-check with the robust reader and only
                    # treat this as a dead shell when BOTH agree it is empty.
                    try:
                        _live = self._read_betslip_count(driver)
                    except Exception:
                        _live = None
                    if isinstance(_live, (int, float)) and _live >= 1:
                        post_shell = False
                        self._emit_direct(
                            gui_callback,
                            f"  🔎 Slip probe reported empty but the betslip "
                            f"actually holds {_live} selection(s) — keeping it "
                            f"and NOT reloading the board.")
                if post_shell:
                    # CHEAP RECOVERY FIRST (2026-10-05). A "silent slip" is the
                    # SPA re-mounting its shell — the fix is to reload the page,
                    # NOT to mint a brand-new session. Forcing a login POST here
                    # was actively harmful: it superseded our own token, and
                    # the fresh session lost the slip, dropping it to 1 leg and
                    # falling under the 2-leg minimum, so every round ended in
                    # rebuild. Observed repeating every round with zero bets.
                    # We now re-hydrate by navigation and re-click the legs, and
                    # only escalate to a real login if the shell stays dead.
                    self._emit_direct(gui_callback,
                                      "  🔒 Slip went silent mid-typing (late SPA re-mount) — "
                                      "reloading the board and re-clicking the legs.")
                    # COUNT THIS RECOVERY (2026-10-05). This block never set a
                    # "recovered" flag, so on the very next loop iteration the
                    # same probe could fire again and send us round the whole
                    # reload-and-re-click cycle again - consuming every attempt
                    # and ending the round with "Bet not placed". Observed on
                    # essentially every round of a 4-hour run: the slip reached
                    # 3 legs and x1.62 with the stake typed, then died here and
                    # the account placed nothing for hours.
                    self._post_shell_recovers = int(
                        getattr(self, "_post_shell_recovers", 0) or 0) + 1
                    _revived = False
                    try:
                        self._safe_get(driver, self.TODAY_GAMES_PAGE_URL)
                        time.sleep(1.2)
                        _revived = True
                    except Exception:
                        _revived = False
                    if not _revived:
                        # Navigation itself failed — only now is a real re-login
                        # justified.
                        if not self._hard_spa_login(driver, phone, password,
                                                    gui_callback=gui_callback, force=True):
                            return False
                        minted = True
                    re_clicked = 0
                    # USE THE ROBUST SELECTION PATH, not a listing-only loop.
                    # After a re-mount the SPA needs a hydration wait before rows
                    # exist, and many legs simply are not on the board we land
                    # on - the per-game market page is the reliable fallback.
                    # The old listing-only loop re-clicked 0 legs every time
                    # ("Slip re-clicked 0 leg(s)"), so the slip stayed empty and
                    # the round placed nothing. _click_selected_legs does
                    # listing rows first and falls back to market pages.
                    try:
                        re_clicked = int(self._click_selected_legs(
                            driver, legs, gui_callback=gui_callback) or 0)
                    except Exception:
                        re_clicked = 0
                    time.sleep(0.8)
                    _now = self._read_betslip_count(driver)
                    self._emit_direct(gui_callback,
                                      f"  🔒 Re-clicked {re_clicked} leg(s) after the re-mount "
                                      f"(slip now {_now} of {len(legs)})")
                    if isinstance(_now, (int, float)) and _now >= 2:
                        # Slip is whole again — re-apply the stake on the fresh
                        # shell and carry on to PLACE instead of restarting.
                        continue
                    continue
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
            if not totals2.get("odds"):
                # Slip reads empty at the exact moment we are about to click PLACE.
                # Snapshot the page so we can tell a /login bounce from a logged-in
                # page whose Angular betslip re-mounted empty.
                self._emit_direct(gui_callback,
                                  f"  🔬 SLIP-STATE: {self._place_step_diagnostics(driver)}")

            # Final identity gate: if the session died or swapped accounts while
            # we prepared the slip, re-login. The betslip ALWAYS persists across
            # navigation (owner rule) — a momentary count of 0 right after a
            # re-login is the panel re-rendering, NOT a lost slip. Settle, reopen
            # the panel and re-count before ever concluding the slip is empty.
            if phone and password:
                if not self._assert_account_session(driver, phone, password,
                                                    gui_callback=gui_callback):
                    return False
                if self._read_betslip_count(driver) == 0:
                    time.sleep(1.2)
                    try:
                        driver.execute_script("""
var slip = document.querySelector('[data-qa="betslip-counter"]');
if (slip) { slip.click(); }
""")
                    except Exception:
                        pass
                    time.sleep(1.5)
                    if self._read_betslip_count(driver) == 0:
                        self._emit_direct(gui_callback,
                                          "  ↻ Betslip still empty after re-login — "
                                          "rebuilding from fresh games.")
                        if self._clear_betslip(driver, gui_callback=gui_callback):
                            return {"needs_legs": True, "count": 0}
                        return False

            if not getattr(self, "running", True):
                self._emit_direct(gui_callback,
                                  "🛑 Emergency stop during placement — aborting before submit.")
                return False

            self._emit_direct(gui_callback, "Placing bet...")
            spa_result = self._place_via_spa_service(driver, gui_callback=gui_callback)
            if spa_result.get("placed"):
                self._emit_direct(gui_callback,
                                  f"  ✅ SPA service submitted and cleared the betslip "
                                  f"({spa_result.get('detail', '')[:160]})")
                self._last_placed_stake = float(stake)
                after = self._read_balance_text(driver)
                if (before_balance > 0.0) and (after > 0.0) and (before_balance - after) >= 1.0:
                    self._emit_direct(gui_callback,
                                      f"✅ Balance reduced: KES {before_balance:,.2f} → "
                                      f"KES {after:,.2f} — bet placed")
                return True
            _detail_l = str(spa_result.get("detail", "") or "").lower()
            # "User logged from another device" is a SERVER-side session
            # invalidation: the SPA still *looks* logged in (logged="1") but
            # this browser's token has been superseded, so every submit is 403'd
            # and every DOM PLACE click dies with it. Without this branch the
            # account looped "Bet not placed" indefinitely — observed 95
            # consecutive rejections on 0798810080 while the slip itself was
            # built and verified fine ("BetslipService verified: 2 selection(s)").
            # Retrying the DOM button on a dead token is guaranteed to fail, so
            # re-login FIRST and keep the slip on the betslip for the retry.
            _session_dead = ("logged from another device" in _detail_l
                             or "invalid session" in _detail_l
                             or "session expired" in _detail_l
                             or ("http403" in _detail_l and "another device" in _detail_l))
            if _session_dead:
                self._emit_direct(gui_callback,
                                  "  🔐 SERVER REJECTED: 'User logged from another device' — "
                                  "clicking Okay and re-logging in before retrying the slip.")
                # BACKOFF (2026-10-05): count consecutive rejections and STOP
                # hammering. Every dismiss+re-login cycle mints a NEW token that
                # supersedes the last, which is how one 30-minute window produced
                # 33 failed logins, 34 dismissals, 31 gate failures and ZERO bets
                # placed. The book throttles back-to-back logins, so the only way
                # to actually recover is to leave the session alone. Cooldown
                # grows 5 -> 10 -> 20 -> 40 min (capped at 40).
                try:
                    _bo = getattr(self, "_auth_backoff", None)
                    if _bo is None:
                        _bo = {}
                        self._auth_backoff = _bo
                    _k = str(phone or "")
                    _n = int(_bo.get(_k + "_n") or 0) + 1
                    _bo[_k + "_n"] = _n
                    if _n >= 2:
                        _delay = min(2400.0, 300.0 * (2 ** min(_n - 1, 3)))
                        _bo[_k] = time.time() + _delay
                        self._emit_direct(
                            gui_callback,
                            f"⏸️ {phone}: {_n} consecutive session rejections — pausing login "
                            f"attempts for {_delay / 60:.0f} min so the session can settle. "
                            "Retrying sooner just supersedes our own token again.")
                        try:
                            if self._clear_betslip(driver, gui_callback=gui_callback):
                                return {"needs_legs": True, "count": 0}
                        except Exception:
                            pass
                        return False
                except Exception:
                    pass
                # Owner rule: dismiss the notice, then re-establish the session in
                # a bounded loop and only give up once it has genuinely failed
                # several times. Parking on the FIRST refusal just handed the
                # account away while a single Okay+re-login would have recovered it.
                _recovered = False
                for _attempt in range(3):
                    try:
                        self._dismiss_foreign_session_prompt(driver)
                    except Exception:
                        pass
                    try:
                        self._logout_current_session(driver)
                    except Exception:
                        pass
                    # INDUSTRIAL-GRADE FIX (2026-10-04): wait for the old session
                    # to clear on the server before attempting a new login. The
                    # server needs a moment to release the old token — without this
                    # wait, the new login attempt races the old session and fails
                    # with the same "another device" error.
                    time.sleep(5)
                    try:
                        with self._login_lock:
                            # force=True is ESSENTIAL. Without it _hard_spa_login
                            # returns early the moment logged="1" is on screen, and
                            # that attribute stays "1" after the server killed the
                            # token — so no credentials get posted and the retry
                            # submits on the token that was just rejected.
                            login_ok = False
                            try:
                                if self._hard_spa_login(driver, phone, password,
                                                         gui_callback=gui_callback,
                                                         force=True):
                                    login_ok = True
                            except Exception:
                                login_ok = False
                            if not login_ok:
                                try:
                                    if self._session_is_live(driver, deep_check=True):
                                        login_ok = True
                                except Exception:
                                    pass
                            if login_ok:
                                try:
                                    _recovered = self._confirm_session_ready(
                                        driver, phone, password, gui_callback=gui_callback)
                                except Exception:
                                    _recovered = False
                                if not _recovered:
                                    try:
                                        if self._session_is_live(driver, deep_check=True):
                                            _recovered = True
                                    except Exception:
                                        pass
                                if _recovered:
                                    break
                    except Exception:
                        pass
                    self._emit_direct(gui_callback,
                                      f"  🔁 re-login attempt {_attempt + 1}/3 did not "
                                      f"confirm a live session — trying again.")
                    time.sleep(3)
                if _recovered:
                    if self._clear_betslip(driver, gui_callback=gui_callback):
                        return {"needs_legs": True, "count": 0}
                    return False
                self._emit_direct(gui_callback,
                                  "  🅿️ PARKED: could not confirm a live session after "
                                  "3 dismiss+re-login attempts. Stopping the retry loop "
                                  "so we stop fighting the bookmaker; log this account "
                                  "out everywhere else, then restart the engine.")
                # Recovery failed above, so park rather than keep submitting on a
                # dead token. Parking is what stops the endless 300s re-crawl loop.
                try:
                    self._parked_until[str(phone)] = time.time() + 1800.0
                except Exception:
                    pass
                if self._agent_hub is not None:
                    try:
                        self._agent_hub.supervisor.beat_parked(phone)
                    except Exception:
                        pass
                # Hand the slip back to the caller to replay the selection later,
                # rather than clicking PLACE on a token the book already killed.
                if self._clear_betslip(driver, gui_callback=gui_callback):
                    return {"needs_legs": True, "count": 0}
                return False

            _spa_detail = str(spa_result.get("detail", "") or "")
            # ── DUMP WHAT WAS ACTUALLY SENT (2026-10-05) ──────────────────
            # Diagnostic only. Reads succeed (wallet 200) in the same round that
            # the bet write is Forbidden, so the login is fine and something
            # specific to the bet request is being refused. Print the captured
            # method/url/headers for every intercepted request so the next round
            # tells us what the SPA sends that our fallback does not.
            try:
                _net = self._exec_script(
                    driver,
                    "return JSON.stringify(window.__spaNet || []);",
                    default="[]", timeout=10.0, label="spa net dump")
                import json as _jn
                _rows = _jn.loads(_net or "[]")
            except Exception:
                _rows = []
            if isinstance(_rows, list) and _rows:
                self._emit_direct(
                    gui_callback,
                    f"  \U0001f50d CAPTURED {len(_rows)} bet-related request(s):")
                for _r in _rows[-4:]:
                    if not isinstance(_r, dict):
                        continue
                    try:
                        _h = _r.get("reqHeaders") or {}
                        _hk = sorted(_h.keys())
                        # Never print cookie values - only header NAMES.
                        self._emit_direct(
                            gui_callback,
                            f"     [{_r.get('via','?')}] {_r.get('method','?')} "
                            f"{str(_r.get('url',''))[:80]} -> resp "
                            f"{_r.get('respStatus')} | cred="
                            f"{_r.get('credentials','?')} | headers({len(_hk)}): "
                            f"{', '.join(_hk[:10])}")
                    except Exception:
                        pass
            # ── HTTP 403 ON /api/bets/place IS A SESSION REJECTION (2026-10-05)
            # A 403 here is not a slip problem: the slip is built, priced and
            # funded, and the book refuses the TOKEN at the place call. That is
            # the same condition as "logged in from another device", so falling
            # through to the DOM PLACE button and then "rebuilding from a fresh
            # login" just re-mints a token the book will reject again.
            #
            # We park the account with a message that names the one cause the
            # code cannot fix, instead of burning CPU on retries that are
            # guaranteed to fail:
            #   403 means another client holds the session for this account
            #   (phone app / another browser / another machine).
            if "403" in _spa_detail:
                self._emit_direct(
                    gui_callback,
                    f"  \U0001f6ab PLACE REFUSED WITH HTTP 403 — the bookmaker "
                    f"rejected our session token, not the slip. Detail: "
                    f"{_spa_detail[:130]}")
                self._emit_direct(
                    gui_callback,
                    "  ⚠️ 403 at PLACE means this account is signed in somewhere "
                    "ELSE — the phone app, another browser, or another machine. "
                    "SportPesa allows one active session, and the newest login "
                    "wins. Sign the account out everywhere else and the next "
                    "round will place normally.")
                try:
                    self._parked_until[str(phone)] = time.time() + 1800.0
                except Exception:
                    pass
                if self._agent_hub is not None:
                    try:
                        self._agent_hub.supervisor.beat_parked(phone)
                    except Exception:
                        pass
                try:
                    if self._clear_betslip(driver, gui_callback=gui_callback):
                        return {"needs_legs": True, "count": 0}
                except Exception:
                    pass
                return False

            self._emit_direct(gui_callback,
                              f"  ↻ SPA service did not place "
                              f"({_spa_detail[:160]}) — "
                              "falling back to the DOM PLACE BET button")
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
                self._emit_direct(gui_callback,
                                  f"  🔬 PLACE-STATE: {self._place_step_diagnostics(driver)}")
                # If PLACE BET bounced us to /login, the session token lapsed mid-tour.
                # Rebuilding re-logins with a minted token, so hand the slip back to
                # the caller instead of burning attempts on a dead page.
                try:
                    logged_out = "/login" in (driver.current_url or "")
                except Exception:
                    logged_out = False
                if logged_out:
                    self._emit_direct(gui_callback,
                                      "  🔁 Session lapsed to /login at PLACE — returning slip "
                                      "for fresh re-login + quick rebuild (minted token).")
                    if self._clear_betslip(driver, gui_callback=gui_callback):
                        return {"needs_legs": True, "count": 0}
                    return False
            elif act == "logged_out":
                self._emit_direct(gui_callback,
                                  "  🔁 Logged out mid-place — rebuilding from a fresh login "
                                  "so the next PLACE runs on a minted token.")
                if self._clear_betslip(driver, gui_callback=gui_callback):
                    return {"needs_legs": True, "count": 0}
                return False
            elif act == "confirmed":
                self._emit_direct(gui_callback, "  ✅ Confirm prompt accepted")
            elif act == "invalid":
                consec_invalid += 1
                now_count = self._read_betslip_count(driver)
                # A "Not valid" prompt means the bookmaker STRIPPED a suspended/in-play
                # leg. If the slip actually shrank, don't re-place the damaged (weaker)
                # slip — clear it and rebuild from fresh upcoming games immediately.
                if (isinstance(now_count, (int, float)) and now_count > 0 and
                        isinstance(slip_count_at_open, (int, float)) and
                        slip_count_at_open > 0 and now_count < slip_count_at_open):
                    self._emit_direct(gui_callback,
                                      "  ↻ \"Not valid\" removed a leg — rebuilding slip "
                                      "from fresh games instead of placing the weakened one.")
                    # Bench every leg currently on the slip — at least one of them
                    # just died at PLACE, and the same composite gets rebuilt forever
                    # otherwise (the observed LITHUANIA/ERITREA/MEXICO-USA loop).
                    self._bench_slip_legs(legs)
                    if self._clear_betslip(driver, gui_callback=gui_callback):
                        return {"needs_legs": True, "count": now_count}
                    return False
                self._emit_direct(gui_callback,
                                  "  ↻ \"Not valid\" prompt handled (selection suspended/removed) — re-checking")
            else:
                consec_invalid = 0
                self._emit_direct(gui_callback,
                                  f"  ↻ Prompt handled ({act}: odds changed / in-play / removed) — re-checking")
            time.sleep(2)

            if self._bet_succeeded(driver):
                self._emit_direct(gui_callback, "✅ Betslip emptied — bet placed")
                self._last_placed_stake = float(stake)
                return True
            after = self._read_balance_text(driver)
            dropped = (before_balance > 0.0) and (after > 0.0) and (before_balance - after) >= 1.0
            if dropped:
                self._emit_direct(gui_callback,
                                  f"✅ Balance reduced: KES {before_balance:,.2f} → "
                                  f"KES {after:,.2f} — bet placed")
                self._last_placed_stake = float(stake)
                return True
            # A suspended/removed leg keeps blocking submission → stop retrying the same
            # dead slip. Clear it so the caller rebuilds from fresh, upcoming games
            # instead of burning the remaining attempts on a slip that can't submit.
            if act == "invalid" and consec_invalid >= 2:
                self._emit_direct(gui_callback,
                                  "  ↻ Suspended selection keeps blocking submit — clearing slip, "
                                  "will rebuild from fresh games.")
                self._bench_slip_legs(legs)
                # Always signal a rebuild. The caller clears the persistent slip
                # itself ("Cleared the persistent betslip before rebuild"), so a
                # False from this local clear must NOT abort the rebuild path --
                # that was the bug that turned this into a dead round for the
                # account: "clearing slip" printed, then no "Rebuild #1" ever
                # appeared, then "no bet this round (Bet not placed)".
                try:
                    self._clear_betslip(driver, gui_callback=gui_callback)
                except Exception:
                    pass
                return {"needs_legs": True, "count": 0}
            self._emit_direct(gui_callback,
                              f"  Balance KES {after:,.2f} unchanged — will retry placement")
            time.sleep(1)

        self._emit_direct(gui_callback,
                          "⚠️ Could not place the bet after repeated attempts (odds kept changing "
                          "or games went in-play).")
        return False
