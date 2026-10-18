#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
BetFlow - a small, fast SportPesa auto-bettor.

WHY THIS FILE EXISTS
--------------------
The previous engine was ~17,000 lines and could not complete a single bet. Its
own logs explained why, and the reason was architectural rather than a missing
patch:

    [xhr] POST /api/bets/place -> resp None

The place request went out and NOTHING came back - no status, no body. That is
not a 403 and not a permissions problem. The site's Angular SPA silently
re-mounts its shell about 7 minutes after login and tears down any in-flight
request. The old engine spent 4-5 minutes touring board pages and per-game
market pages to build a slip, so by the time it clicked PLACE it was always at
the far end of that window, and the re-mount killed the request every time.

So this tool is built around ONE rule: login, pick, place, verify, logout - all
inside about three minutes. One board crawl. No page touring. No LLM. No
learning engine. No drawdown maths. Nothing that cannot be explained in a
sentence.

Everything here is deliberately simple. If a bet does not go in, the log says
exactly why.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
from datetime import datetime, timedelta
from pathlib import Path

try:                                     # independent model layer - optional
    from model_data import score_games as _score_games
except Exception:                        # missing/broken module -> neutral
    _score_games = None

try:
    from selenium import webdriver
    from selenium.webdriver.chrome.options import Options
    from selenium.webdriver.chrome.service import Service
    from selenium.webdriver.common.by import By
    from selenium.webdriver.common.keys import Keys
except ImportError:                                    # pragma: no cover
    print("selenium is required:  pip install selenium", file=sys.stderr)
    raise

def app_dir() -> Path:
    """The folder the app should read and write in.

    IMPORTANT for the packaged build. A PyInstaller ONE-FILE exe unpacks itself
    into a temporary folder, so __file__ points at scratch space that is deleted
    on exit. Anchoring on it would give the exe a private, throwaway copy of the
    settings and ledger - every run would forget every account and every bet.
    So when frozen, use the folder the exe actually sits in.
    """
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


HERE = app_dir()


def _live_dir() -> Path:
    """One canonical writable folder for every launch mode.

    The ledger, settings and cache must land in a folder BOTH the packaged exe
    and a source run can reach, or the same app ends up with two ledgers and
    two daily-cap clocks and which one wins depends on how it was launched
    (MEASURED 2026-10-08: Desktop\\betflow_ledger.json vs
    sportsape\\betflow_ledger.json disagreed; a cap enforced against one copy
    while bets are staked against the other is not a cap).

    The shipped exe lives on the Desktop, so the Desktop holds the real state.
    When it demonstrably does (a settings file lives there), that folder wins
    for every launch mode. Only when there is no Desktop state do we fall back
    to this build's own folder (e.g. a fresh dev checkout on another machine).
    """
    desk = Path.home() / "Desktop"
    if (desk / "sportsape_settings.json").exists():
        return desk
    return HERE


LIVE = _live_dir()
SETTINGS = LIVE / "sportsape_settings.json"
LEDGER = LIVE / "betflow_ledger.json"
CACHE = LIVE / "forebet_cache.json"

# ── Forebet second-opinion gate ─────────────────────────────────────────
# forebet_cache.py (run on its own schedule) writes CACHE as a plain JSON
# file; the picker reads it and drops a leg only when the independent model's
# probability is far below what the price implies (the book is *more*
# confident than an independent source - a spot to be suspicious of). A
# missing or stale cache is neutral: the picker behaves exactly like today.
FB_EDGE = 0.65        # keep a leg only if fb_prob >= implied_prob * FB_EDGE
FB_MAX_AGE = 30.0 * 3600.0
_FB_CACHE: dict = {"at": 0.0, "data": {}}

# Model EV gate (API-Football predictions). ev = model_prob * odds - 1; legs
# the independent model prices clearly below the book's price are dropped.
MODEL_MIN_EV = -0.10

TODAY_URL = "https://www.ke.sportpesa.com/en/sports-betting/football-1/today-games/"
LOGIN_URL = "https://www.ke.sportpesa.com/en/sports-betting/football-1/"

# Owner rule: never take odds in the 1.00-1.09 band.
MIN_LEG_ODDS = 1.09
# Slip we aim for. Small and quick beats clever and slow.
TARGET_LEGS = 2
MIN_LEGS = 2
MIN_SLIP_ODDS = 1.60
MAX_SLIP_ODDS = 6.00

# Stake sizing. The base is whatever the user set (usually 10). An account
# whose balance sits below the base still bets - the FULL balance - as long as
# it clears the book's practical minimum. A slip the model analysed well may be
# staked ABOVE the base, never above MAX_MODEL_STAKE.
MIN_FULL_BALANCE_STAKE = 1.0
MAX_MODEL_STAKE = 25.0
# Kick-off must be at least this far away so the book does not suspend the leg
# while we are filling the slip.
MIN_LEAD_MINUTES = 10.0
# Market preference order, shared by the DOM picker and the API picker. Markets
# that are less popular - and therefore mispriced more often - come first; the
# 3-way crowd is last.
PREF = ["dnb_away", "under", "btts_no", "over15", "over", "btts", "away", "draw", "home"]

# The whole point of this rewrite: finish before the SPA re-mounts.
DEADLINE_SECONDS = 165.0


def log(msg: str) -> None:
    line = f"[{datetime.now():%H:%M:%S}] {msg}"
    print(line, flush=True)
    # The shipped app is windowed (no stdout), so engine detail would be
    # invisible. When frozen, tee every line into the same terminal log the
    # GUI appends to, so board/pick/place/refusal/settle detail survives for
    # review. Dev runs and tests keep pure print - they must not pollute the
    # live log.
    if getattr(sys, "frozen", False):
        try:
            from resource_path import writable_path
            with open(writable_path("gui_terminal.log"), "a",
                      encoding="utf-8") as _f:
                _f.write(line + "\n")
        except Exception:
            pass


# ── settings ─────────────────────────────────────────────────────────────
def load_settings() -> dict:
    # When packaged we ship a default settings file inside the bundle; if there
    # is no settings file next to the exe, fall back to that rather than dying.
    path = SETTINGS
    if not path.exists():
        bundled = Path(getattr(sys, "_MEIPASS", "")) / "sportsape_settings.json"
        if bundled.exists():
            log(f"no settings next to the exe - using the bundled default")
            path = bundled
    cfg = json.loads(path.read_text(encoding="utf-8"))
    cfg.setdefault("stake", 10.0)
    cfg.setdefault("daily_bets", 20)
    return cfg


def normalise_phone(phone: str) -> str:
    """SportPesa wants 2547XXXXXXXX for Kenyan numbers."""
    digits = "".join(c for c in str(phone) if c.isdigit())
    if digits.startswith("254"):
        return digits
    if digits.startswith("0"):
        digits = digits[1:]
    return "254" + digits


# ── single instance ──────────────────────────────────────────────────────
class SingleInstance:
    """Refuse to start a second engine.

    Two engines means two sessions on one account, which is what produces
    'logged in from another device'.
    """

    def __init__(self, name: str = "Global\\SportsApeBetFlowSingleton"):
        self.name = name
        self.handle = None
        try:
            import ctypes
            self._ctypes = ctypes
            self._ctypes.windll.kernel32.CreateMutexW(None, False, name)
            self.handle = ctypes.windll.kernel32.GetLastError()
        except Exception:
            self.handle = None

    def acquired(self) -> bool:
        # ERROR_ALREADY_EXISTS = 183
        return self.handle != 183


# ── keep the machine awake ───────────────────────────────────────────────
def keep_awake() -> None:
    """Stop Windows sleeping while we bet. Screen may still blank."""
    ES_CONTINUOUS = 0x80000000
    ES_SYSTEM_REQUIRED = 0x00000001
    ES_DISPLAY_REQUIRED = 0x00000002
    try:
        import ctypes
        # Only ES_SYSTEM_REQUIRED: keep the machine alive, let the screen off.
        ctypes.windll.kernel32.SetThreadExecutionState(ES_CONTINUOUS | ES_SYSTEM_REQUIRED)
        log("keep-awake engaged (system awake, screen may blank)")
    except Exception as exc:
        log(f"keep-awake unavailable: {exc}")


# ── ledger ───────────────────────────────────────────────────────────────
def load_ledger() -> list:
    if LEDGER.exists():
        try:
            data = json.loads(LEDGER.read_text(encoding="utf-8"))
            return data if isinstance(data, list) else []
        except Exception:
            return []
    return []


def save_ledger(rows: list) -> None:
    try:
        LEDGER.write_text(json.dumps(rows, indent=2), encoding="utf-8")
    except Exception as exc:
        log(f"could not save ledger: {exc}")


def append_ledger_row(row: dict) -> None:
    """Append ONE row to the PERSISTED ledger, re-reading the file first.

    MEASURED 2026-10-13: this is the ledger-clobber bug. do_round() now writes
    the ledger itself - settlement reconciliations AND the zero-stake shadow
    research rows - while every caller kept a snapshot taken BEFORE those
    writes and saved IT back afterwards. Each round therefore overwrote the
    file with its stale copy: the round's shadow rows vanished (the learning
    multiplier was simulated, logged, saved, and erased minutes later), and
    settlement updates written seconds earlier could be reverted to "active".
    The cap check re-reads the file already (that is why the caps held); only
    the append needed the same treatment. One small JSON read per round buys
    a lossless write.
    """
    try:
        rows = load_ledger()
        rows.append(row)
        save_ledger(rows)
    except Exception as exc:
        log(f"ledger append failed: {str(exc)[:100]}")


def bets_today(rows: list, phone: str | None = None) -> int:
    """Real bets placed in the current betting day.

    Shadow research slips (zero stake) are deliberately excluded - they are
    not bets and must never consume the owner's daily cap.

    `phone=None` counts the whole machine (two locked accounts share the
    daily cap); a phone string counts just that account, which is what the
    per-account log lines must show so "BET ... on 0706719388 (10/20)" is
    honest about that phone.
    """
    day = _betting_day()
    out = 0
    for r in rows:
        if not str(r.get("placed_at", "")).startswith(day):
            continue
        if str(r.get("status", "")).startswith("shadow"):
            continue
        if phone is not None and str(r.get("phone") or "") != str(phone):
            continue
        out += 1
    return out


# ── betting-day boundary ───────────────────────────────────────────────────
# The cap is per betting DAY. That day used to roll at local midnight, which
# is fine for a machine that bets all evening and stops when the cap is spent -
# but it is arbitrary, so it is now a setting: betting_reset_hour (0-23,
# default 0 = midnight). A round placed at 23:30 counts against the day that
# started at 06:00 that morning, not against the one that starts at midnight.
def betting_day_start_hour() -> int:
    try:
        if SETTINGS.exists():
            cfg = json.loads(SETTINGS.read_text(encoding="utf-8"))
            return max(0, min(23, int(cfg.get("betting_reset_hour") or 0)))
    except Exception:
        pass
    return 0


def _betting_day(when=None) -> str:
    """The betting day a moment belongs to, as YYYY-MM-DD."""
    dt = when or datetime.now()
    if dt.hour < betting_day_start_hour():
        dt = dt - timedelta(days=1)
    return dt.strftime("%Y-%m-%d")


# ── Odds-band recipe veto (the owner's "odds that win more" ask) ───────────
# The legacy backend proved a slip SHAPE can be a repeat loser - 16L@gt6 went
# 9 real bets at -100%, 3L@lt3 34 bets at -96% - and every shape it ever
# priced is filed in sportsape_stats.json under "recipes" (trials / won /
# stake / ret per legs@odds-band key). The new engine now REFUSES a shape
# with enough real money behind it and clearly negative ROI instead of
# re-betting that band every round. A missing stats file = no evidence = no
# veto (exactly the pre-change behaviour).
VETO_MIN_TRIALS = 15        # same real-bet floor the legacy gate used
VETO_ROI = -0.20            # ... and the same "clearly losing" ROI
# Owner 2026-10-18: ease the veto for two recipes the user wants re-tested
# with the new per-leg scoring. They stay on the books (not hard-blocked)
# but the AI analyst + deliberation gate still gate them at draft time.
VETO_EXEMPTIONS = {"3L@5-6", "4L@4-5"}

# In load_vetoed_recipes, the veto condition:
#   if trials < VETO_MIN_TRIALS or staked <= 0: continue
#   roi = (ret - staked) / staked
#   if roi <= VETO_ROI: veto
# Add 0-win rule: a recipe with >= 5 trials and 0 wins is vetoed regardless of ROI
# (catches 4L@lt3: 7 trials, 0 wins, -100%).
VETO_ROI = -0.20            # ... and the same "clearly losing" ROI
# Research-only (shadow) evidence needs a much bigger sample and a much worse
# record before it may refuse a band - real money stays the honest signal.
SHADOW_VETO_MIN_TRIALS = 25
SHADOW_VETO_ROI = -0.35


def _band_of(odds: float) -> str:
    """Combined-odds band bins. IDENTICAL to the legacy recorder's
    SportsapeBackend._band_of so the recipe keys match the table the
    win-sync writes - otherwise nothing would ever veto."""
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


def load_vetoed_recipes() -> dict:
    """{"<legs>L@<band>": {"trials": n, "roi": r}} for losing real-money shapes.

    Reads the stats file the legacy win-sync writes (same LIVE folder as the
    ledger). Never reads the ledger itself - this is the settled record, not
    the pending one. Any failure is neutral and returns {}.

    Shadow (zero-stake research) recipes are a SECONDARY source with a much
    higher bar - real money is the honest signal, so research evidence has to
    be far stronger before it may refuse a band. Entries carry
    "kind": "shadow" so the log can say which evidence spoke.
    """
    try:
        p = LIVE / "sportsape_stats.json"
        if not p.exists():
            return {}
        with open(p, encoding="utf-8") as fh:
            st = json.load(fh)
        veto = {}
        # The recorder keys recipes as "<legs>L@<band>/<lead>/[<mix>]" (see
        # SportsapeBackend line ~11498), but the engine looks the shape up as
        # the bare "<legs>L@<band>". MEASURED 2026-10-16: copying the stored
        # key verbatim meant vetoed.get("4L@4-5") never matched the stored
        # "4L@4-5/-/[-]", so the losing-shape refusal NEVER fired - the tool
        # kept re-betting the exact bands the journal had flagged at -90% ROI.
        # Normalising to the shape prefix is what actually arms the gate.
        for key, r in (st.get("recipes") or {}).items():
            trials = int(r.get("trials") or 0)
            staked = float(r.get("stake") or 0.0)
            ret = float(r.get("ret") or 0.0)
            won = r.get("won")
            has_won_field = "won" in r
            won_int = int(won) if won is not None else None
            if staked <= 0:
                continue
            roi = (ret - staked) / staked if staked > 0 else -1.0
            # Veto if: enough trials AND clearly losing, OR 5+ trials with
            # zero wins (a recipe that never wins is dead regardless of ROI).
            # Only apply the zero-win rule when the recorder actually wrote a
            # "won" field, so legacy/partial records without it aren't
            # over-vetoed.
            zero_win = (has_won_field and won_int == 0 and trials >= 5)
            if trials < VETO_MIN_TRIALS and not zero_win:
                continue
            short = str(key).split("/", 1)[0].strip()
            if short in VETO_EXEMPTIONS:
                continue
            if roi <= VETO_ROI or zero_win:
                veto[str(key).split("/", 1)[0].strip()] = {
                    "trials": trials, "roi": roi, "kind": "real"}
        # Research-only evidence: more trials, worse ROI, never a substitute
        # for real money - it just stops the engine re-running a shape that
        # has failed 30+ times with nothing at stake.
        for key, r in (st.get("shadow_recipes") or {}).items():
            short = str(key).split("/", 1)[0].strip()
            if short in veto:
                continue
            trials = int(r.get("trials") or 0)
            if trials < SHADOW_VETO_MIN_TRIALS:
                continue
            stake = float(r.get("stake") or 0.0)
            ret = float(r.get("ret") or 0.0)
            roi = ((ret - stake) / stake) if stake > 0 else -1.0
            if stake <= 0 or roi <= SHADOW_VETO_ROI:
                veto[short] = {"trials": trials, "roi": roi, "kind": "shadow"}
        return veto
    except Exception:
        return {}


# ── Idle-time research (the pacing gap) ────────────────────────────────────
# The pacing loop used to sleep for the whole cadence and do NOTHING, so a
# round picked legs against a forebet cache last written whenever the fetch
# script happened to run and an API-Football cache that was never warmed.
# The gap between rounds is exactly where those feeds should be refreshed, so
# the next round gates legs against TODAY'S independent model odds.
def _fetch_with_browser(url: str) -> str | None:
    """Fetch a PUBLIC research page with a real headless Chrome.

    Needed because forebet blocks plain HTTP (403 since 2026-10-10 - measured).
    Never used for the bookmaker: no login, no session, no account. Always
    quits its own browser; returns None on any failure.
    """
    driver = None
    try:
        driver, _prof = build_driver(headless=True)
        goto(driver, url)
        time.sleep(2.5)
        return driver.execute_script("return document.documentElement.outerHTML")
    except Exception:
        return None
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass


def idle_research() -> dict:
    """Refresh the independent models during the pacing gap.

    Strictly best-effort - every failure is swallowed and reported in the
    return value, never raised, because research must not be able to delay,
    break or fail a betting round. Returns {"forebet": n, "fixtures": n}.
    """
    out = {"flashscore": 0, "fixtures": 0}
    # ── Flashscore head-to-head evidence: the day's pairings ─────────────
    # Replaces the forebet refresh (403-blocked and stale). The picker reads a
    # cache keyed "HOME|AWAY", so the feed needs the machine's last board -
    # do_round saves it, and the pacing gap turns it into the shortlist of
    # pairings whose H2H pages are worth a browser load.
    try:
        import flashscore_cache
        wanted = None
        try:
            board_file = LIVE / "last_board.json"
            if board_file.exists():
                board = json.loads(board_file.read_text(encoding="utf-8"))
                mtime = board_file.stat().st_mtime
                # MEASURED 2026-10-15: during a multi-hour cap-hold the
                # refresh kept crawling the MORNING's board (the snapshot
                # last_board.json holds), so the gates ran against 12-hour-
                # old H2H evidence for tonight's fixtures while the file's
                # fetched_at froze too. Once the snapshot is older than
                # 90 min, crawl flashscore's CURRENT board wholesale - the
                # pairings then line up with tonight's picks.
                stale = (time.time() - mtime) > 5400.0
                if not stale:
                    wanted = {f"{g.get('home')}|{g.get('away')}"
                              for g in board if g.get("home") and g.get("away")}
        except Exception:
            wanted = None
        games = flashscore_cache.refresh(wanted)
        out["flashscore"] = len(games)
    except Exception as exc:
        out["flashscore_error"] = str(exc)[:80]
    # ── FotMob news (injuries/rest/rotation) - RSS, cheap, no browser ─────
    try:
        import fotmob_news
        wanted_fm = None
        try:
            board_file = LIVE / "last_board.json"
            if board_file.exists():
                board = json.loads(board_file.read_text(encoding="utf-8"))
                wanted_fm = [(g.get("home"), g.get("away"))
                             for g in board if g.get("home") and g.get("away")]
        except Exception:
            wanted_fm = None
        fm = fotmob_news.refresh(wanted_fm)
        out["fotmob"] = len(fm) if isinstance(fm, dict) else 0
    except Exception as exc:
        out["fotmob_error"] = str(exc)[:80]
    # ── ESPN standings (free, no quota): pre-warm for the board's leagues ──
    # Standings don't change in 30 min, so fetching them during the pacing
    # gap means the deep check + standing_ok gate are instant at round time.
    try:
        import model_data
        board_file = LIVE / "last_board.json"
        if board_file.exists():
            board = json.loads(board_file.read_text(encoding="utf-8"))
            seen = set()
            for g in board:
                if g.get("sport", "Football") != "Football":
                    continue
                country = g.get("country") or ""
                league = g.get("league") or ""
                key = (country, league)
                if key in seen:
                    continue
                seen.add(key)
                try:
                    model_data.fetch_standings(country, league)
                except Exception:
                    pass
            out["standings"] = len(seen)
    except Exception as exc:
        out["standings_error"] = str(exc)[:80]
    # ── API-Football: today's not-started fixtures (one call, cached 6h) ──
    try:
        import model_data
        out["fixtures"] = len(model_data.fetch_fixtures_today())
    except Exception as exc:
        out["fixtures_error"] = str(exc)[:80]
    return out


# ── Shadow slips (zero-stake research: the daily learning multiplier) ───────
# 20 real bets a day is a tiny learning sample, so the engine also SIMULATES
# alternate slip shapes on the same board - no money, no bookmaker, no risk.
# Each shadow is settled against real final scores (API-Football) and filed
# into the shadow tables, so the recipe/market/band calibration sees ~10x
# more outcomes per day. Markets that cannot be decided from a final score
# (first scorer, half-time) are never shadowed.
# Markets that cannot be decided from a final score (first scorer) are never
# shadowed. HT markets CAN be settled - the results feed carries the
# half-time score.
SHADOW_MARKETS = {"home", "away", "draw", "btts", "btts_no",
                  "over15", "over25", "under", "under25",
                  "dnb_home", "dnb_away",
                  "ht_home", "ht_draw", "ht_away", "hfbtts", "hfbtts_no"}


def make_shadow_slips(games: list, real_legs: list, rotation: int,
                      want: int = 2) -> list:
    """Alternate slip shapes for the same board, zero stake.

    A shadow is a DIFFERENT combination from the real slip (different market
    rotation), so what-if questions get answered: would a DNB-led slip have
    cashed where the O/U-led one did not? Only score-decidable markets are
    simulated. Returns [] when nothing distinct is available.
    """
    shadows = []
    for shift in (2, 4):
        try:
            legs = api_pick_legs(games, rotation=rotation + shift, want=want)
        except Exception:
            continue
        if not legs:
            continue
        if len(legs) == len(real_legs) and all(
                any(l["gid"] == r["gid"] and l["market"] == r["market"]
                    for r in real_legs) for l in legs):
            continue                       # identical shape - nothing to learn
        if any(l["market"] not in SHADOW_MARKETS for l in legs):
            continue
        product = 1.0
        for l in legs:
            product *= l["odds"]
        shadows.append({
            "placed_at": datetime.now().isoformat(timespec="seconds"),
            "phone": "shadow",
            "stake": 0.0,
            "odds": round(product, 2),
            "legs": len(legs),
            "games": [f"{l['home']} vs {l['away']} [{l['market']}]" for l in legs],
            "leg_odds": [l["odds"] for l in legs],
            "legs_meta": [{"sport": l.get("sport") or "Football",
                           "league": l.get("league") or "-",
                           "country": l.get("country") or "",
                           "market": l["market"],
                           "home": l["home"], "away": l["away"]}
                          for l in legs],
            "markets": [l["market"] for l in legs],
            "leg_names": [f"{l['home']} vs {l['away']}" for l in legs],
            "status": "shadow",
            "shadow_of_rotation": rotation + shift,
        })
        if len(shadows) >= 2:
            break
    return shadows


def leg_won(market: str, hg: int, ag: int,
            hth: int | None = None, hta: int | None = None) -> bool | None:
    """Did this market's leg win on a final score? None when the market cannot
    be decided from a score alone (first scorer / half-time legs without a
    half-time score)."""
    m = str(market)
    # ── Half Time/Full Time combos (market 44). Both scores decide: the
    # half-time score gates the half-time leg of the combo, the full-time
    # score the second. Without the half-time score we cannot decide.
    if m.startswith("htft_"):
        if hth is None or hta is None:
            return None
        ht_home, ht_draw, ht_away = hth > hta, hth == hta, hta > hth
        ft_home, ft_draw, ft_away = hg > ag, hg == ag, ag > hg
        ht = {"h": ht_home, "x": ht_draw, "a": ht_away}[m[5]]
        ft = {"h": ft_home, "x": ft_draw, "a": ft_away}[m[6]]
        return ht and ft
    # ── first-half markets: decided by the HALF-TIME score ──────────────
    if m in ("ht_home", "ht_draw", "ht_away", "hfbtts", "hfbtts_no"):
        if hth is None or hta is None:
            return None
        if m == "ht_home":
            return hth > hta
        if m == "ht_draw":
            return hth == hta
        if m == "ht_away":
            return hta > hth
        if m == "hfbtts":
            return hth > 0 and hta > 0
        return not (hth > 0 and hta > 0)
    if m in ("home", "ml_home"):
        return hg > ag
    if m in ("away", "ml_away"):
        return ag > hg
    if m in ("dc_1x",):
        return hg >= ag                    # home OR draw
    if m in ("dc_x2",):
        return hg <= ag                    # draw OR away
    if m in ("dc_12",):
        return hg != ag                    # home OR away (no draw)
    if m == "draw":
        return hg == ag
    if m == "btts":
        return hg > 0 and ag > 0
    if m == "btts_no":
        return not (hg > 0 and ag > 0)
    if m == "over15":
        return hg + ag >= 2
    if m == "over25":
        return hg + ag >= 3
    if m == "under":
        return hg + ag <= 1
    if m == "under25":
        return hg + ag <= 2
    if m == "dnb_home":
        return None if hg == ag else hg > ag
    if m == "dnb_away":
        return None if hg == ag else ag > hg
    return None


def settle_shadows(rows: list | None = None) -> list:
    """Settle pending shadow slips against real final scores.

    Returns the rows that settled this call (status became won/lost). A slip
    wins only when EVERY leg won; a draw on a DNB leg is a push, so the leg
    does not lose the slip (the book returns the stake on a push, so the rest
    of the accumulator stands).
    """
    if rows is None:
        rows = load_ledger()
    try:
        import model_data
    except Exception:
        return []
    # Group pending shadows by the day they were placed: a slip settles
    # against the results of ITS OWN day (a 23:50 slip finishes after
    # midnight), and the model layer's day cache makes that free.
    pending: dict = {}
    for row in rows:
        if str(row.get("status") or "") != "shadow":
            continue
        if not (row.get("games") or []):
            continue
        day = str(row.get("placed_at") or "")[:10]
        pending.setdefault(day, []).append(row)
    if not pending:
        return []
    settled = []
    changed = False
    for day, group in pending.items():
        try:
            results = model_data.fetch_all_results_on(day)
        except Exception:
            results = []
        if not results:
            continue
        for row in group:
            outcomes, undecided = [], False
            for g in (row.get("games") or []):
                name = str(g).split("[")[0].strip()
                home, _, away = name.partition(" vs ")
                market = (str(g).rsplit("[", 1)[1].rstrip("]")
                          if "[" in str(g) else "")
                try:
                    res = model_data.find_result(home, away, results)
                except Exception:
                    res = None
                if (not res or int(res.get("hg", -1)) < 0
                        or int(res.get("ag", -1)) < 0):
                    undecided = True
                    break
                won = leg_won(market, int(res["hg"]), int(res["ag"]),
                              hth=res.get("hth"), hta=res.get("hta"))
                if won is None:
                    if market.startswith("dnb"):
                        outcomes.append(True)   # push: the leg does not lose
                    else:
                        undecided = True
                        break
                else:
                    outcomes.append(bool(won))
            if undecided or not outcomes:
                continue
            row["status"] = "won" if all(outcomes) else "lost"
            row["settled_at"] = datetime.now().isoformat(timespec="seconds")
            row["shadow_settled"] = True
            settled.append(row)
            changed = True
    if changed:
        save_ledger(rows)
    return settled


def reap_orphans(min_age_seconds: int = 300) -> int:
    """Kill ONLY browser leftovers THIS tool launched. Never the user's.

    MEASURED BUG 2026-10-10: this ran
        Get-Process chromedriver,chrome | ?{ $_.StartTime -lt $cut } | Stop-Process
    which killed EVERY chrome process older than five minutes - including the
    operator's own browser, on every start-up (they watched their personal
    Chrome close). The legacy tool's reaper is scoped to the throwaway profile
    marker, documented as "the ONLY thing we are allowed to match on"; this one
    must be too. chrome.exe counts only when its command line carries one of
    our markers (betflow_chrome_ / sportsape_chrome_), and chromedriver.exe
    only when THIS process spawned it (ParentProcessId == our pid).

    The age test stays: a browser the round currently running is younger than
    the cutoff and is never reaped out from under the session.
    """
    ps = (
        "$cut=(Get-Date).AddSeconds(-{age});"
        "$mine=@();"
        # chrome: ours only, matched on the throwaway profile marker
        "$mine += Get-CimInstance Win32_Process -Filter \"Name='chrome.exe'\" |"
        " Where-Object {{ $_.CommandLine -and"
        " ($_.CommandLine -like '*betflow_chrome_*'"
        " -or $_.CommandLine -like '*sportsape_chrome_*')"
        " -and $_.CreationDate -lt $cut }} |"
        " ForEach-Object {{ $_.ProcessId }};"
        # chromedriver: ours only - a child of THIS process
        "$mine += Get-CimInstance Win32_Process -Filter \"Name='chromedriver.exe'\" |"
        " Where-Object {{ $_.ParentProcessId -eq {me} -and $_.CreationDate -lt $cut }} |"
        " ForEach-Object {{ $_.ProcessId }};"
        "foreach($p in $mine){{ Stop-Process -Id $p -Force -ErrorAction SilentlyContinue }};"
        "@($mine).Count"
    ).format(age=int(min_age_seconds), me=os.getpid())
    try:
        out = subprocess.run(["powershell", "-NoProfile", "-Command", ps],
                             capture_output=True, text=True, timeout=60)
    except Exception as exc:
        log(f"  orphan reap failed: {str(exc)[:70]}")
        return 0
    n = 0
    try:
        n = int((out.stdout or "0").strip().splitlines()[-1])
    except Exception:
        n = 0
    if n:
        log(f"  reaped {n} orphaned tool browser process(es) "
            f"older than {min_age_seconds // 60} min")
    return n


# Chrome's major version, resolved once per process (it only changes when
# Chrome itself updates).
_CHROME_MAJOR: str | None = None


def _chrome_major_version() -> str:
    """Installed Chrome's major version as a string ("" when unreadable).

    Registry first (BLBeacon is what Chrome itself reports to its updater and
    to apps), then the executable's ProductVersion as a fallback. Cached after
    the first call: a browser launch must not spend a subprocess on version
    detection every round.
    """
    global _CHROME_MAJOR
    if _CHROME_MAJOR is not None:
        return _CHROME_MAJOR
    _CHROME_MAJOR = ""
    try:
        import winreg
        for hive, sub in ((winreg.HKEY_LOCAL_MACHINE,
                           r"SOFTWARE\Google\Chrome\BLBeacon"),
                          (winreg.HKEY_CURRENT_USER,
                           r"SOFTWARE\Google\Chrome\BLBeacon")):
            try:
                with winreg.OpenKey(hive, sub) as k:
                    ver, _vtype = winreg.QueryValueEx(k, "version")
                if ver and str(ver).strip().split(".")[0].isdigit():
                    _CHROME_MAJOR = str(ver).strip().split(".")[0]
                    return _CHROME_MAJOR
            except OSError:
                continue
    except Exception:
        pass
    for cand in (r"C:\Program Files\Google\Chrome\Application\chrome.exe",
                 r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
                 os.path.expandvars(
                     r"%LOCALAPPDATA%\Google\Chrome\Application\chrome.exe")):
        if not os.path.isfile(cand):
            continue
        try:
            out = subprocess.run(
                ["powershell", "-NoProfile", "-Command",
                 "(Get-Item -LiteralPath '{}').VersionInfo.ProductVersion"
                 .format(cand.replace("'", "''"))],
                capture_output=True, text=True, timeout=25)
            first = ((out.stdout or "").strip().splitlines() or [""])[0].strip()
            if first and first.split(".")[0].isdigit():
                _CHROME_MAJOR = first.split(".")[0]
                break
        except Exception:
            continue
    return _CHROME_MAJOR


def local_chromedriver() -> str:
    """Path to a cached chromedriver matching the installed Chrome, or "".

    MEASURED 2026-10-16 17:22+: every launch called webdriver.Chrome() with an
    EMPTY Service path, which makes Selenium Manager run and re-query
    https://googlechromelabs.github.io when its metadata TTL lapses. While that
    fetch was slow the manager raised and the launch died with the generic
    "Unable to obtain driver for chrome" - the tool then failed on EVERY
    win-sync for 40 minutes, twice a cycle, while a perfectly good
    chromedriver 155.0.8059.84 sat in the local cache (reproduced: the manager
    succeeded standalone, so the path itself is fine).

    DriverFinder checks Service.path FIRST and skips the manager entirely when
    it is a real file, so an explicit path removes the network dependency from
    browser launches altogether. Returns "" when nothing usable is cached (Chrome
    updated, for instance) and the caller then falls back to the manager, which
    may download the right driver as before.
    """
    major = _chrome_major_version()
    if not major:
        return ""
    roots = (os.path.expanduser(r"~\.cache\selenium"),
             os.path.expandvars(r"%LOCALAPPDATA%\SeleniumCache"),
             os.path.expandvars(r"%USERPROFILE%\.cache\selenium"))
    best, best_key = "", None
    for root in roots:
        base = os.path.join(root, "chromedriver", "win64")
        try:
            entries = os.listdir(base)
        except OSError:
            continue
        for entry in entries:
            exe = os.path.join(base, entry, "chromedriver.exe")
            if not os.path.isfile(exe):
                continue
            nums = [int(x) for x in re.findall(r"\d+", entry)]
            if not nums or str(nums[0]) != major:
                continue          # driver major must match Chrome's
            # Compare EVERY numeric part: Chrome versions are like
            # 155.0.8059.84, so comparing only the first three would tie
            # 155.0.8059.84 with 155.0.8059.79 and keep whichever came first.
            key = tuple(nums)
            if best_key is None or key > best_key:
                best, best_key = exe, key
    return best


def build_driver(headless: bool = True, profile: str | None = None):
    # Kill anything left over from a previous round BEFORE opening a new one.
    # Measured 2026-10-08: 34 chrome.exe and 4 chromedriver.exe were alive at
    # once, holding 3.5 GB, because every round launches a fresh browser and a
    # driver that does not always get reaped. Over a day of rounds that starves
    # the machine and a round dies mid-flight with no obvious cause.
    reap_orphans()
    opts = Options()
    if headless:
        opts.add_argument("--headless=new")
    # THE VIEWPORT WAS THE BUG (2026-10-08).
    # Measured: the real control is <a class="place-bet" ng-click="$ctrl.onPlaceBet($event)">
    # sitting at y=1070 in the document - while the window was only 1000px tall.
    # It was BELOW THE FOLD, so the hit test never reached it and the click went
    # nowhere: no request, no dialog, slip unchanged, every single time. Making
    # the window tall enough to contain the whole betslip footer is the fix.
    opts.add_argument("--window-size=1600,1800")
    opts.add_argument("--disable-gpu")
    opts.add_argument("--no-sandbox")
    opts.add_argument("--disable-dev-shm-usage")
    opts.add_argument("--disable-blink-features=AutomationControlled")
    opts.add_argument("--disable-notifications")
    opts.add_argument("--disable-background-networking")
    opts.add_argument("--disable-background-timer-throttling")
    opts.add_argument("--disable-renderer-backgrounding")
    opts.add_argument("--no-first-run")
    opts.add_argument("--no-default-browser-check")
    opts.add_experimental_option("excludeSwitches", ["enable-automation"])
    opts.add_experimental_option("useAutomationExtension", False)
    # Do not advertise a headless UA.
    opts.add_argument(
        "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")
    profile = profile or tempfile.mkdtemp(prefix="betflow_chrome_")
    opts.add_argument(f"--user-data-dir={profile}")
    # Pin the driver to the cached build that matches installed Chrome so the
    # launch has NO network dependency (an empty Service path makes Selenium
    # Manager phone home, and when that fetch is slow the session dies with
    # "Unable to obtain driver for chrome" - measured live 2026-10-16). An
    # empty string behaves exactly like Service(): DriverFinder then falls back
    # to the manager, which is also the retry path below.
    _drv = local_chromedriver()
    try:
        driver = webdriver.Chrome(service=Service(executable_path=_drv),
                                  options=opts)
    except Exception:
        if not _drv:
            raise
        driver = webdriver.Chrome(service=Service(), options=opts)
    driver.set_page_load_timeout(45)
    driver.set_script_timeout(20)
    return driver, profile


# ── session ──────────────────────────────────────────────────────────────
def goto(driver, url: str) -> bool:
    """Navigate with a hard cap; never raise."""
    try:
        driver.get(url)
        return True
    except Exception as exc:
        log(f"  navigation failed: {str(exc)[:90]}")
        return False


def session_live(driver) -> bool:
    """The wallet API is the only trustworthy proof of a live session.

    logged="1" survives server-side invalidation, so it proves nothing.
    """
    try:
        res = driver.execute_async_script(
            """
            var done = arguments[arguments.length - 1];
            var tid = setTimeout(function(){ done('timeout'); }, 8000);
            fetch('/api/wallets/balance', {credentials: 'include', cache: 'no-store'})
              .then(function(r){ clearTimeout(tid); done(r.status === 200 ? 'live' : 'http' + r.status); })
              .catch(function(){ clearTimeout(tid); done('neterr'); });
            """)
        return res == "live"
    except Exception:
        return False


def read_balance(driver) -> float | None:
    try:
        txt = driver.execute_async_script(
            """
            var done = arguments[arguments.length - 1];
            var tid = setTimeout(function(){ done(null); }, 8000);
            // The Accept header is NOT optional. Without it the server answers
            // the wallet route with the SPA's own HTML (status 200), so
            // r.json() throws and the balance reads as unreadable. With it the
            // route answers real JSON (MEASURED 2026-10-08):
            //   {"sportsbook":{"balance":"63.58","bonusBalance":"0"}, ...}
            fetch('/api/wallets/balance',
                  {credentials:'include', cache:'no-store',
                   headers:{'Accept':'application/json'}})
              .then(function(r){ return r.text(); })
              .then(function(t){
                   clearTimeout(tid);
                   var j = null;
                   try { j = JSON.parse(t); } catch (e) { return done(null); }
                   // Measured shape:
                   //   {"sportsbook":{"balance":"103.58","bonusBalance":"0"}, ...}
                   // The balance is a STRING and lives under sportsbook, so a
                   // top-level j.balance lookup silently returned nothing.
                   var b = null;
                   if (j.sportsbook && j.sportsbook.balance !== undefined)
                     b = j.sportsbook.balance;
                   else if (j.balance !== undefined) b = j.balance;
                   else if (j.data && j.data.balance !== undefined) b = j.data.balance;
                   var n = parseFloat(b);
                   done(isNaN(n) ? null : n);
                 })
              .catch(function(){ clearTimeout(tid); done(null); });
            """)
        return None if txt is None else float(txt)
    except Exception:
        return None


# ── SPA JSON API (all contracts MEASURED 2026-10-08) ──────────────────────
# The SPA talks JSON to these same-origin routes. Driving the DOM (clicking
# selections, typing stakes, answering SweetAlerts) placed the first six bets,
# but every step was a fragile selector. These functions issue the SAME
# requests the SPA makes, so they cannot rot from markup churn:
#
#   GET  /api/wallets/balance
#          -> {"sportsbook":{"balance":"63.58"},"casino":{...}}
#          (needs Accept: application/json or the server answers HTML)
#   GET  /api/todays/1/games?type=prematch&section=today&markets_layout=multiple&o=startTime&pag_count=80&pag_min=1
#          -> {0:{id,competitors:[{name}],dateTimestamp,markets:[...]}, ...}
#   GET  /api/games/markets?games=<gids>&markets=46,52-1.5,43,10
#          -> {"9343175":[{id,specValue,name,selections:[{id,name,odds}]}]}
#   POST /api/bets/place
#          -> {"return_code":0,"bet_id":14144897192,"short_bet_id":7682,
#              "balance":53.58,"possible_win":183.03,"msgtext":"BET:7682 ..."}
#   POST /api/bets/history
#          -> {"return_code":0,"bets":[{id,short_id,status,
#              possible_winnings,amount,time,stake}]}

API_MARKET_IDS = "46,52-1.5,43,10"   # Double Chance, O/U 1.50, BTTS, 1X2

# Market id -> the odds-dict keys for its selections, in the ORDER the book
# serves them (each response cell maps 1:1 to that position). Verified live on
# 2026-10-08 against /api/available/markets + /api/games/markets: 10=1X2,
# 42=1X2 first half, 46=Double Chance, 43=BTTS, 47=Draw No Bet, 45=Odd/Even,
# 328=BTTS first half, 41=First Team To Score (None/Home/Away),
# 207=Half with most goals. Market 52 (O/U) needs its line, so its keys are
# built per line: "OU1.5#0/#1" for the OVER/UNDER selections.
MARKET_CELLS = {
    10: ["1X2#0", "1X2#1", "1X2#2"],
    42: ["FH1X2#0", "FH1X2#1", "FH1X2#2"],
    46: ["DC#0", "DC#1", "DC#2"],
    43: ["BTTS#0", "BTTS#1"],
    47: ["DNB#0", "DNB#1"],
    45: ["OE#0", "OE#1"],
    328: ["HBTTS#0", "HBTTS#1"],
    41: ["FTS#0", "FTS#1", "FTS#2"],
    207: ["HMOST#0", "HMOST#1", "HMOST#2"],
    44: ["HTFT#0", "HTFT#1", "HTFT#2", "HTFT#3", "HTFT#4",
         "HTFT#5", "HTFT#6", "HTFT#7", "HTFT#8"],
}

# Half Time/Full Time (market 44) has NINE selections - the half-time result
# x full-time result grid, e.g. "1/X" = HT Home, FT Draw. The engine maps 1X2-
# style markets by position, but the book could re-order a 9-selection grid
# (letter order is NOT the same as popularity order), so id 44 is mapped by
# SELECTION NAME to these canonical cells instead. Verified live 2026-10-13:
# /api/games/markets with id 44 serves exactly this grid on every game.
HTFT_CELLS = ["1/1", "1/X", "1/2", "X/1", "X/X", "X/2",
              "2/1", "2/X", "2/2"]
HTFT_CELLS_52 = [f"HTFT#{i}" for i in range(len(HTFT_CELLS))]

# market label -> exact odds-dict key used by api_pick_legs()
LEG_KEY = {
    "home": "1X2#0", "draw": "1X2#1", "away": "1X2#2",
    "btts": "BTTS#0", "btts_no": "BTTS#1",
    "dc_1x": "DC#0", "dc_x2": "DC#1", "dc_12": "DC#2",
    "dnb_home": "DNB#0", "dnb_away": "DNB#1",
    "over15": "OU1.5#0", "over25": "OU2.5#0",
    "under": "OU1.5#1", "under25": "OU2.5#1",
    "first_away": "FTS#2", "first_home": "FTS#1",
    "hfbtts_no": "HBTTS#1",
    # ── first-half markets (SportPesa market ids 42 and 328, both confirmed
    # live in /api/available/markets on 2026-10-11). HT draw is a real edge
    # market: prices run 2.0-3.0 where full-time draw runs 3.0-4.5.
    "ht_home": "FH1X2#0", "ht_draw": "FH1X2#1", "ht_away": "FH1X2#2",
    "hfbtts": "HBTTS#0",
    # ── Half Time/Full Time combos (market 44, confirmed live 2026-10-13:
    # 1/1, 1/X, 1/2, X/1, X/X, X/2, 2/1, 2/X, 2/2). The book prices the
    # favorite-home combo 1/1 around 2.5-4.0 - inside the normal slip band -
    # and the double-draw X/X long (8+), which the longshot mode can take.
    # HTFT cells are mapped BY NAME to these indexes, so the label is
    # position-independent: "htft_hh" always means the "1/1" selection.
    "htft_hh": "HTFT#0", "htft_hx": "HTFT#1", "htft_ha": "HTFT#2",
    "htft_xh": "HTFT#3", "htft_xx": "HTFT#4", "htft_xa": "HTFT#5",
    "htft_ah": "HTFT#6", "htft_ax": "HTFT#7", "htft_aa": "HTFT#8",
    # ── two-way moneyline for the OTHER sports a slip may mix in
    # (basketball / tennis / hockey / volleyball...). Same 1X2 selections as
    # football's own, distinguished by label so the rotation can give them
    # their own slots without changing how football is drafted.
    "ml_home": "1X2#0", "ml_away": "1X2#2",
}

# The API picker's preference order: the same "less popular markets are
# mispriced more often" idea as PREF, extended with markets only the full
# market fetch can see (Draw No Bet is real here; the DOM listing never had it).
# The rotation deals one leg per market class per pass, so a slip mixes
# markets - and now sports: the two-way moneyline sits early so a basketball
# or tennis leg can open a slip next to football legs, and the first-half
# markets sit where the draft actually reaches them (a 3-4 leg slip never got
# as far as the last entries).
# The order below is load-bearing for WHICH markets land on a slip: a 2-4 leg
# slip only reaches the first ~6 classes, so a market that never gets drafted
# never gets learned either. The HTFT combos (44) therefore sit right after
# the O/U cluster, BEFORE the plain first-half markets - measured 2026-10-13:
# with them at slots 12-14, 39 real slips drafted zero HTFT legs; the double
# draw (X/X ~5-10) and the favourite/away combos are exactly the less-crowded
# prices the picker exists to reach.
# DOUBLE CHANCE rides early too: the owner asked for it (2026-10-15), and it
# is the two-outcome home market - 1X at 1.25-1.40 is the same job as
# dnb_home but WITHOUT the draw push, so a 1X leg keeps a slip alive.
API_PREF = ["ml_home", "ml_away", "dc_1x", "dc_x2", "dc_12", "dnb_away",
            "dnb_home", "under", "under25",
            "btts_no", "over15", "over25",
            "htft_xx", "htft_hh", "htft_aa",
            "ht_draw", "ht_home", "ht_away",
            "hfbtts", "btts", "away", "draw", "home",
            "first_away", "hfbtts_no"]

_MKT_PARAM_CACHE: dict = {"at": 0.0, "param": None}
_MKT_PARAM_TTL = 1800.0

# The board JSON carries each game's betradarId; the game's H2H stats modal is
# that plus BetRadar's own match URL (window.open from the SPA):
#   https://s5.sir.sportradar.com/sportpesa/<locale>/match/<betradarId>
BETRADAR_H2H = "https://s5.sir.sportradar.com/sportpesa/en/match/{}"


def _api(driver, script: str) -> object:
    """Run an async JSON API call in the SPA context. None on any failure."""
    try:
        return driver.execute_async_script(script)
    except Exception as exc:
        log(f"  api call failed: {str(exc)[:120]}")
        return None


def _market_param(driver) -> str:
    """The 'markets' whitelist = every definition /api/available/markets serves
    (market ids + their handicap/OU lines). Cached per process."""
    now = time.time()
    if _MKT_PARAM_CACHE["param"] and now - _MKT_PARAM_CACHE["at"] < _MKT_PARAM_TTL:
        return _MKT_PARAM_CACHE["param"]
    js = r"""
    var done = arguments[arguments.length - 1];
    fetch('/api/available/markets',
          {credentials:'include', headers:{'Accept':'application/json'}})
      .then(function(r){ return r.text(); })
      .then(function(t){
        var param = [];
        try {
          var j = JSON.parse(t);
          var mkts = (j && j[0] && j[0].markets) || [];
          for (var i=0;i<mkts.length;i++){
            var m = mkts[i];
            param.push(m.specValue ? (m.id + '-' + m.specValue) : String(m.id));
          }
        } catch(e) {}
        done(param.join(','));
      }).catch(function(){ done(''); });
    """
    param = _api(driver, js) or ""
    if param:
        # Market 44 (Half Time/Full Time) is NOT served by
        # /api/available/markets, yet /api/games/markets happily returns it
        # when asked (verified 2026-10-13). Append it so HTFT cells reach the
        # board. Never duplicate if the dictionary one day learns to serve it.
        for add in ("44",):
            if add not in [p.split("-")[0] for p in param.split(",") if p]:
                param = f"{add},{param}" if param else add
        _MKT_PARAM_CACHE.update(at=time.time(), param=param)
        log(f"  market dictionary: {param.count(',') + 1} definition(s) cached")
    return param


# ── Other sports (the owner's ask: a slip may mix sports) ───────────────────
# SportPesa runs one board per sport id on the same JSON feed. Non-football
# boards carry their markets INLINE (named selections with odds), so no market
# dictionary lookup is needed - and the league/country rides along, which is
# exactly what the league-learning tables want.
OTHER_SPORTS = {
    2: "Basketball", 4: "Ice Hockey", 5: "Tennis", 6: "Handball",
    12: "Rugby", 20: "Speedway", 23: "Volleyball", 8: "American Football",
    3: "Baseball", 7: "Boxing", 9: "Cricket", 10: "Cycling",
    15: "Darts", 18: "Golf", 22: "Snooker", 28: "Table Tennis",
    33: "Waterpolo", 34: "MMA", 35: "Futsal",
}
# The 1.10 leg floor stays: a basketball 1.02 moneyline is refused like any
# other sub-1.10 price.


def api_other_sports(driver, max_games: int = 10) -> list:
    """Today's games from every other sport the book offers, as engine rows.

    Each returned row matches the football board's shape (gid/home/away/ko/br
    plus odds/sel_ids keyed by the STANDARD labels), so the picker, the gates
    and the placer treat a tennis leg exactly like a football one. The
    moneyline (2-way or 3-way) is mapped from the board's own named
    selections. sport/league/country ride along for the learning tables.
    """
    js = r"""
    var done = arguments[arguments.length - 1];
    var ids = [%s];
    var out = [];
    var i = 0;
    function next(){
      if (i >= ids.length) { done(out); return; }
      var id = ids[i++];
      fetch('/api/todays/' + id + '/games?type=prematch&section=today'
            + '&markets_layout=multiple&o=startTime&pag_count=8&pag_min=1',
            {credentials:'include', headers:{'Accept':'application/json'}})
        .then(function(r){ return r.json(); })
        .then(function(arr){
          try {
            var games = Array.isArray(arr) ? arr : Object.values(arr || {});
            for (var k=0;k<games.length && out.length < %d;k++){
              var g = games[k];
              if (!g || !g.id || !g.competitors || g.competitors.length < 2) continue;
              var home = String((g.competitors[0]||{}).name||'');
              var away = String((g.competitors[1]||{}).name||'');
              if (!home || !away) continue;
              var mkts = g.markets || [];
              var odds = {}, sels = {}, found = null;
              for (var m=0;m<mkts.length;m++){
                var sel = mkts[m].selections || [];
                if (sel.length < 2) continue;
                // map by selection NAME to the competitor order
                var byName = {};
                for (var s=0;s<sel.length;s++) byName[sel[s].name] = sel[s];
                var h = byName[home], a = byName[away];
                if (!h || !a) continue;
                var hp = parseFloat(h.odds), ap = parseFloat(a.odds);
                if (!(hp > 0) || !(ap > 0)) continue;
                // Two-way moneyline keys: the picker's ml_home/ml_away labels,
                // so other sports get their own rotation slots without
                // disturbing how football is drafted. BOTH key families are
                // written: 'ML#n' (this board's own named selections) AND
                // '1X2#n' - because LEG_KEY resolves ml_home/ml_away to the
                // FOOTBALL cells "1X2#0"/"1X2#2", and MEASURED 2026-10-15 the
                // other-sports rows carried only ML#n: the picker looked for
                // 1X2#0 on a basketball row, found nothing, and NOT ONE
                // multi-sport leg was ever drafted (the "38 games across
                // sports" board was pure decoration).
                odds['ML#0'] = hp; sels['ML#0'] = h.id;
                odds['ML#2'] = ap; sels['ML#2'] = a.id;
                odds['1X2#0'] = hp; sels['1X2#0'] = h.id;
                odds['1X2#2'] = ap; sels['1X2#2'] = a.id;
                var d = null;
                for (var key in byName) if (key !== home && key !== away) d = byName[key];
                if (d && parseFloat(d.odds) > 0) {
                  odds['ML#1'] = parseFloat(d.odds); sels['ML#1'] = d.id;
                }
                found = {
                  gid: String(g.id), home: home, away: away,
                  ko: Number(g.dateTimestamp||0), br: Number(g.betradarId||0),
                  sport: (g.sport||{}).name || 'Other',
                  sport_id: Number((g.sport||{}).id || id),
                  league: (g.competition||{}).name || '?',
                  country: (g.country||{}).name || '',
                  odds: odds, sel_ids: sels,
                  markets_inline: true
                };
                break;
              }
              if (found) out.push(found);
            }
          } catch(e) {}
          next();
        }).catch(function(){ next(); });
    }
    next();
    """
    ids = ",".join(str(i) for i in OTHER_SPORTS if i != 1)
    data = _api(driver, js % (ids, int(max_games))) or []
    games = [g for g in data if g.get("home") and g.get("away")
             and g.get("odds")]
    if not games:
        return []
    # Kick-off guard, same as the football board.
    soon = time.time() + MIN_LEAD_MINUTES * 60
    games = [g for g in games
             if not (g.get("ko") and g["ko"] <= soon)]
    by_sport = {}
    for g in games:
        by_sport[g.get("sport", "?")] = by_sport.get(g.get("sport", "?"), 0) + 1
    log(f"  other sports: {len(games)} game(s) - " + ", ".join(
        f"{k} {v}" for k, v in sorted(by_sport.items())))
    return games


def api_board(driver) -> list:
    """Board from the JSON feeds, then every market each game offers.

    Feeds are tried in order: today -> upcoming -> populars. The 'today' window
    is genuinely empty late at night / just after midnight, so the engine must
    not stand down on an empty day feed (measured on 2026-10-08).
    """
    js = r"""
    var done = arguments[arguments.length - 1];
    var feeds = [
      '/api/todays/1/games?type=prematch&section=today&markets_layout=multiple&o=startTime&pag_count=30&pag_min=1',
      '/api/upcoming/games?type=prematch&o=startTime&pag_count=30&pag_min=1',
      '/api/populars/1/games?type=prematch&o=startTime&pag_count=30&pag_min=1'
    ];
    function grab(u){
      return fetch(u, {credentials:'include', headers:{'Accept':'application/json'}})
        .then(function(r){ return r.text(); })
        .then(function(t){
          var rows = [];
          try {
            var j = JSON.parse(t);
            var arr = Array.isArray(j) ? j : Object.values(j);
            for (var i=0;i<arr.length;i++){
              var g = arr[i];
              if (!g || !g.id || !g.competitors || g.competitors.length < 2) continue;
              rows.push({gid:String(g.id),
                         home:String(g.competitors[0].name||''),
                         away:String(g.competitors[1].name||''),
                         ko:Number(g.dateTimestamp||0),
                         br:Number(g.betradarId||0),
                         sport: (g.sport && g.sport.name) || 'Football',
                         league: (g.competition && g.competition.name) || '',
                         country: (g.country && g.country.name) || ''});
            }
          } catch(e) { rows = []; }
          return rows;
        })
        .catch(function(){ return []; });
    }
    grab(feeds[0])
      .then(function(a){ return a.length ? a : grab(feeds[1]); })
      .then(function(a){ return a.length ? a : grab(feeds[2]); })
      .then(done)
      .catch(function(){ done([]); });
    """
    data = _api(driver, js)
    games = [g for g in (data or []) if g.get("home") and g.get("away")]
    if not games:
        log("  board via API: 0 games across all feeds - DOM board will be used")
        return []
    log(f"  board via API: {len(games)} game(s)")

    # Kick-off guard: never pick a game already inside MIN_LEAD_MINUTES of
    # kick-off - the book suspends legs while the slip is being filled.
    soon = time.time() + MIN_LEAD_MINUTES * 60
    kept = []
    for g in games:
        ko = g.get("ko") or 0
        if ko > 0 and ko <= soon:
            continue
        kept.append(g)
    games = kept
    log(f"  {len(games)} game(s) after the {MIN_LEAD_MINUTES:.0f}-minute kick-off guard")

    # Fill every game's odds/sel_ids from the full-market call.
    param = _market_param(driver)
    ids = ",".join(str(g["gid"]) for g in games[:24])
    if not (param and ids):
        return games
    mjs = r"""
    var done = arguments[arguments.length - 1];
    fetch('/api/games/markets?games=%s&markets=%s',
          {credentials:'include', headers:{'Accept':'application/json'}})
      .then(function(r){ return r.text(); })
      .then(function(t){
        var j = {};
        try { j = JSON.parse(t); } catch(e) {}
        done(j);
      }).catch(function(){ done({}); });
    """ % (ids, param)
    mdata = _api(driver, mjs) or {}
    for g in games:
        rows = mdata.get(g["gid"]) or []
        odds, sels = {}, {}
        for m in rows:
            if not m.get("selections"):
                continue
            cells = MARKET_CELLS.get(m.get("id"))
            if m.get("id") == 52:
                line = m.get("specValue")
                cells = [f"OU{line}#0", f"OU{line}#1"] if line else None
            if not cells:
                continue
            # HTFT (44) is a 9-selection grid; map it by selection NAME
            # ("1/1", "X/X", ...) so a differently-ordered grid still lands
            # on the right cell.
            if m.get("id") == 44:
                for s in m["selections"]:
                    try:
                        key = "HTFT#%d" % HTFT_CELLS.index(str(s.get("name")))
                    except ValueError:
                        continue
                    try:
                        odds[key] = float(str(s["odds"]))
                    except (TypeError, ValueError):
                        continue
                    sels[key] = str(s["id"])
                continue
            for i, s in enumerate(m["selections"][:len(cells)]):
                key = cells[i]
                try:
                    odds[key] = float(str(s["odds"]))
                except (TypeError, ValueError):
                    continue
                sels[key] = str(s["id"])
        g["odds"] = odds
        g["sel_ids"] = sels
    return games


def _rotate_markets(markets: list, n: int) -> list:
    """Rotate a market preference list so different accounts lead with
    different market classes (account 1 DNB-lead, account 2 O/U-lead...)."""
    if not markets:
        return markets
    n = int(n) % len(markets)
    return markets[n:] + markets[:n] if n else list(markets)


def _confidence_stake(base: float, legs: list, cap: float = MAX_MODEL_STAKE) -> float:
    """Stake a slip the model analysed well ABOVE the base, capped at `cap`.

    Every leg must carry a model EV - one unscored leg means "half-analysed"
    and that is not well-analysed. Tiers on the lowest leg EV:
        >= 0.03  -> 1.5x     >= 0.08 -> 2.0x    >= 0.12 -> cap
    """
    evs = [float(l.get("ev")) for l in legs if l.get("ev") is not None]
    if len(evs) != len(legs) or not evs:
        return base
    mn = min(evs)
    if mn < 0.03:
        return base
    if mn < 0.08:
        return min(cap, base * 1.5)
    if mn < 0.12:
        return min(cap, base * 2.0)
    return min(cap, base * 2.5)


def _effective_stake(balance: float, base: float, legs: list) -> float | None:
    """Actual stake for this round. None => refuse to bet (below the floor).

    - balance below the base but at/above the floor -> BET THE FULL BALANCE
      (the "low balance bets full margin" rule, not sitting idle);
    - balance above the base -> confidence-sized stake, never above the cap;
    - balance below MIN_FULL_BALANCE_STAKE -> None (hard floor).
    """
    if balance < MIN_FULL_BALANCE_STAKE:
        return None
    planned = _confidence_stake(base, legs)
    return min(planned, balance)


def _draft_legs(cands: list, markets: list, want: int = TARGET_LEGS,
                require_sel_id: bool = True, max_legs: int = 4,
                league_w: dict | None = None) -> list:
    """Fill a slip from candidate legs, one market class at a time in rotation.

    The old greedy took every leg from the FIRST market class in preference
    order (dnb_away) because that class always had enough candidates - that is
    why every acca came out all-Draw-No-Bet. This draft instead deals one leg
    per market class per round, so a slip mixes markets (DNB + BTTS + O/U...).
    Within a market the cheapest candidate is still taken first, unless a
    league weight tips the balance (a league whose market beats its price is
    drafted before an equal-priced leg from a league that does not). One leg
    per game; the [MIN_SLIP_ODDS, MAX_SLIP_ODDS] band and the per-leg floor
    keep applying - the draft keeps adding legs until the band is reached or
    max_legs runs out, exactly like the code it replaces.
    """
    lw = league_w or {}
    buckets: dict = {}
    for c in cands:
        buckets.setdefault(c["market"], []).append(c)
    for b in buckets.values():
        # Value first within a market: scored legs sort by EV (best first),
        # then by league weight (proven leagues first), then cheapest-first so
        # "no model data" changes nothing.
        b.sort(key=lambda c: (
            0 if c.get("ev") is not None else 1,
            -(lw.get(c.get("league") or "", {}).get(c["market"], 0.0)),
            c["odds"]))

    chosen, product = [], 1.0
    used_gids = set()
    k = 0                                        # rotating market pointer
    while len(chosen) < max_legs:
        progressed = False
        for _ in range(len(markets)):
            bucket = buckets.get(markets[k % len(markets)])
            k += 1
            if not bucket:
                continue
            take = None
            newp = product
            while bucket:                        # consume skipped candidates
                c = bucket.pop(0)
                if c["gid"] in used_gids:        # one leg per game
                    continue
                if require_sel_id and not c.get("sel_id"):
                    continue
                # A leg priced above MAX/MIN_LEG_ODDS can never pair with the
                # cheapest possible partner inside the band - drop it for good.
                if c["odds"] > MAX_SLIP_ODDS / MIN_LEG_ODDS:
                    continue
                cand_newp = product * c["odds"]
                if len(chosen) >= 1 and cand_newp > MAX_SLIP_ODDS:
                    continue                     # too rich - try the next in this
                                                 # bucket before giving up on it
                take, newp = c, cand_newp
                break
            if take is None:
                continue
            chosen.append(take)
            used_gids.add(take["gid"])
            product = newp
            progressed = True
            if len(chosen) >= want and MIN_SLIP_ODDS <= product <= MAX_SLIP_ODDS:
                break
        if not progressed:
            break
    if len(chosen) < MIN_LEGS:
        return []
    if not (MIN_SLIP_ODDS <= product <= MAX_SLIP_ODDS):
        return []
    return chosen


def load_forebet(ttl: float = FB_MAX_AGE) -> dict:
    """Read the Forebet cache file (fresh only) -> {HOME|AWAY: prob dict}.

    Returns {} on any problem - a missing or stale cache must never block a
    round. Re-read is throttled so a round never spends time on I/O it does
    not need.
    """
    now = time.time()
    if now - _FB_CACHE["at"] < min(ttl, 3600.0):
        return _FB_CACHE["data"]
    data: dict = {}
    try:
        if CACHE.exists():
            payload = json.loads(CACHE.read_text(encoding="utf-8"))
            fet = float(payload.get("fetched_at") or 0)
            if now - fet <= ttl:
                data = payload.get("games") or {}
                age_min = (now - fet) / 60.0
                log(f"forebet: {len(data)} fixture(s) from cache "
                    f"({age_min:.0f} min old)")
    except Exception as exc:
        log(f"forebet: cache unreadable - {str(exc)[:90]}")
    _FB_CACHE["at"] = now
    _FB_CACHE["data"] = data
    return data


def _forebet_prob(market: str, fb: dict) -> float | None:
    """Map a leg market to a model probability, or None when the model does not
    price that market (BTTS / O/U / first-half legs stay neutral).

    ml_home/ml_away are the two-way moneyline used by the OTHER sports a slip
    may mix in (basketball, tennis, hockey...): same 1X2 probabilities, a
    different label, so they must score too."""
    h = fb.get("home") or 0.0
    d = fb.get("draw") or 0.0
    a = fb.get("away") or 0.0
    if market in ("home", "ml_home"):
        return h
    if market in ("draw",):
        return d
    if market in ("away", "ml_away"):
        return a
    if market == "dnb_home":
        s = h + a
        return h / s if s > 0 else None
    if market == "dnb_away":
        s = h + a
        return a / s if s > 0 else None
    return None


def api_pick_legs(games: list, want: int = TARGET_LEGS,
                  exclude: set | None = None, rotation: int = 0,
                  ai: bool = True) -> list:
    """Choose legs from API rows. Mirrors pick_legs()'s rules and band but over
    the FULL market surface (Draw No Bet, 1X2 first half, First Team To Score,
    odd/even, ...), not just the four markets the DOM listing shows.

    Each returned leg carries sel_id so the placement API can be called with
    the exact selection the book quoted, and br (betradarId) for the H2H link.

    Two layers on top of the legacy candidate list:
      * a Forebet disagreement gate - drop a leg the independent model rates
        far below what the price implies (neutral when no cache exists);
      * a market-mixed draft instead of the all-Draw-No-Bet greedy.
    """
    cands = []
    for g in games:
        if not g.get("gid"):
            continue
        if exclude:
            key = f"{str(g.get('home','')).strip().upper()}|{str(g.get('away','')).strip().upper()}"
            if key in exclude:
                continue
        od = g.get("odds") or {}
        for market in API_PREF:
            lkey = LEG_KEY.get(market)
            if not lkey or lkey not in od:
                continue
            o = od[lkey]
            if o <= MIN_LEG_ODDS:
                continue
            cands.append({"gid": g["gid"], "home": g["home"], "away": g["away"],
                          "market": market, "lkey": lkey, "odds": o,
                          "sel_id": (g.get("sel_ids") or {}).get(lkey),
                          "ko": g.get("ko", 0), "br": g.get("br", 0),
                          # sport|league key - the SAME string the league-
                          # learning table is keyed by, so the draft can steer
                          # toward leagues whose markets beat their price.
                          "league": f"{g.get('sport') or 'Football'}: "
                                    f"{g.get('league') or ''}",
                           "country": g.get("country") or ""})
    if not cands:
        return []

    # NOTE: forebet used to gate legs here. It is retired on this machine -
    # its site 403s plain HTTP and its cache had gone stale, so the gate had
    # been silently neutral for weeks. Its replacement (flashscore head-to-head
    # evidence) runs with the rest of the learning gates in pick_filters below.

    # ── STEER: everything the tool has learned, applied to candidates ────
    if not cands:
        return []

    # Model EV scoring (API-Football predictions). ev = p * odds - 1. Legs
    # with an EV materially below fair are dropped; the rest sort by EV
    # within their market (best value first). With no model data every leg
    # stays neutral and the picker is exactly the pre-model one.
    if _score_games is not None:
        try:
            scored = _score_games(games)
        except Exception:
            scored = {}
        if scored:
            ev_count = drop_count = 0
            for c in cands:
                p = scored.get(c["gid"])
                fp = _forebet_prob(c["market"], p) if p else None
                if fp is None:
                    continue
                c["ev"] = fp * c["odds"] - 1.0
                # The raw model probability rides along with the leg so the
                # ledger row can record it: the legacy recorder reads
                # "markets" + "probs" to feed market_types calibration, and
                # without them the live stats file stays an empty shell.
                c["prob"] = round(fp, 4)
                ev_count += 1
            gated = []
            for c in cands:
                if c.get("ev") is not None and c["ev"] < MODEL_MIN_EV:
                    drop_count += 1
                    continue
                gated.append(c)
            cands = gated
            if ev_count or drop_count:
                log(f"model: {ev_count} leg(s) scored for EV, "
                    f"{drop_count} dropped (EV < {MODEL_MIN_EV})")
    if not cands:
        return []

    # ── STEER: everything the tool has learned, applied to candidates ────
    # Retired markets, signed market weights, team x market vetoes, the
    # flashscore head-to-head evidence, and the AI analyst's red flags - one
    # fail-safe pass. With no learning data and no feeds it is a no-op and the
    # picker behaves exactly as before.
    try:
        import pick_filters
        cands, _gate_counts = pick_filters.apply_gates(cands, log, ai=ai)
    except Exception:
        pass
    if not cands:
        return []

    # Market weights: the ORDER the slip is drafted from is the steering.
    # MEASURED 2026-10-15: rotation_with_weights() existed but was never
    # called - the draft ran a blind rotation, so the learning tables'
    # "this market beats its price, that one lags" never moved a single pick.
    # A market with no data keeps weight 1.0 (no opinion = no reordering),
    # and the per-account rotation offset still differentiates accounts.
    try:
        import pick_filters
        weights = (pick_filters.load_learning() or {}).get("weights") or {}
    except Exception:
        weights = {}
    order = _rotate_markets(
        pick_filters.rotation_with_weights(API_PREF, weights), rotation)

    # League steering: a league whose market beats its price is drafted before
    # an equal-priced leg from a league that misses. Computed once per call and
    # fail-safe (missing stats = {} = the draft is unchanged).
    try:
        import pick_filters
        lw = pick_filters.league_weights()
    except Exception:
        lw = {}
    legs = _draft_legs(cands, order, want, league_w=lw)

    # ── DEEP CHECK (form + injuries) on the anchor leg ────────────────
    # Only the top leg is checked (quota: ~5 req per leg). Cached 24h so
    # repeated rounds on the same fixture cost nothing. A failure drops the
    # whole slip - "no BS" means a bad anchor kills the bet.
    if legs:
        try:
            import model_data as _mdq
            _left = _mdq._quota_left()
            _ok = (_left < 0 or _left >= 5)
        except Exception:
            _ok = True
        if _ok:
            try:
                import model_data as _md
                # Deep check ALL legs (not just the anchor). Cached data
                # (standings 12h, form 24h) makes this fast; quota is only
                # spent on the first uncached leg.
                all_ok = True
                fail_reason = "ok"
                for leg in legs:
                    ok, reason = _md.deep_check(leg)
                    if not ok:
                        all_ok = False
                        fail_reason = reason
                        break
                if not all_ok:
                    try:
                        log(f"  DEEP CHECK failed: {fail_reason} - slip dropped")
                    except Exception:
                        pass
                    return []
                try:
                    log(f"  DEEP CHECK ok: all {len(legs)} legs passed")
                except Exception:
                    pass
            except Exception:
                pass

    # ── THINK BEFORE PLACING (owner 2026-10-18): deliberation gate ────────
    # Before a slip leaves the picker it must pass a final sanity check: at
    # least two distinct market classes (no all-same-market accumulators), and
    # a logged rationale so the book can be audited. The AI analyst above is the
    # "no BS" filter; this is the "think" step that makes sure the slip is a
    # real, mixed, considered bet rather than a reflex.
    if legs:
        distinct = {l.get("market") for l in legs}
        available = {c.get("market") for c in cands} if 'cands' in dir() else distinct
        if len(distinct) < 2 and len(available) >= 2:
            try:
                log(f"  THINKING: slip rejected - only one market class "
                    f"({sorted(distinct)}) - not a considered bet")
            except Exception:
                pass
            return []
        try:
            mkts = ", ".join(sorted(distinct))
            odds = " x ".join(str(l.get("odds")) for l in legs)
            log(f"  THINKING: {len(legs)}-leg slip OK - markets=[{mkts}], "
                f"odds=[{odds}], AI cleared, recipe not vetoed")
        except Exception:
            pass

    return legs


def api_place(driver, legs: list, stake: float, accept_odds: bool = True) -> dict:
    """POST /api/bets/place - the exact call the SPA makes on confirm.

    Returns the parsed JSON, e.g.
      {"return_code":0,"bet_id":14144897192,"short_bet_id":7682,
       "balance":53.58,"possible_win":183.03,"msgtext":"BET:7682 ..."}
    """
    bets = [{"id": int(leg["sel_id"]),
             "odds": "{:.2f}".format(leg["odds"]),
             "coeff": "{:.2f}".format(leg["odds"])} for leg in legs]
    payload = {"amount": int(stake), "bets": bets,
               "acceptOdds": accept_odds, "betSpinner": True}
    js = r"""
    var done = arguments[arguments.length - 1];
    fetch('/api/bets/place',
          {method:'POST',
           credentials:'include',
           headers:{'Accept':'application/json',
                    'Content-Type':'application/json;charset=UTF-8',
                    'X-Requested-With':'XMLHttpRequest'},
           body: JSON.stringify(%s)})
      .then(function(r){ return r.text(); })
      .then(function(t){
        var j = null;
        try { j = JSON.parse(t); } catch(e) { j = {raw:t}; }
        done(j);
      }).catch(function(){ done(null); });
    """ % (json.dumps(payload))
    return _api(driver, js) or {}


def api_bet_history(driver, statuses: list, count: int = 60) -> list:
    """POST /api/bets/history -> list of {id, short_id, status, ...}."""
    dateTo = int(time.time())
    # Reach back three days: a bet placed last night can settle tomorrow, and
    # today-only queries would strand it as 'active' forever.
    dateFrom = int(time.time()) - 3 * 86400
    js = r"""
    var done = arguments[arguments.length - 1];
    fetch('/api/bets/history',
          {method:'POST',
           credentials:'include',
           headers:{'Accept':'application/json',
                    'Content-Type':'application/json;charset=UTF-8',
                    'X-Requested-With':'XMLHttpRequest'},
           body: JSON.stringify(%s)})
      .then(function(r){ return r.text(); })
      .then(function(t){
        var bets = [];
        try {
          var j = JSON.parse(t);
          if (j && j.return_code === 0 && Array.isArray(j.bets)) bets = j.bets;
        } catch(e) {}
        done(bets);
      }).catch(function(){ done([]); });
    """ % json.dumps({"dateFrom": dateFrom, "dateTo": dateTo,
                      "section": ["prematch"], "status": statuses,
                      "count": count, "offset": 0})
    return _api(driver, js) or []


def settle_from_history(driver, rows: list) -> dict:
    """Reconcile the local ledger against the book's own bet-history API.

    Rows we placed carry short_bet_id/bet_id (the ticket number shown as
    'BET:xxxx'). The book is authoritative: 'won'/'lost'/'void' statuses and
    the paid amount come from /api/bets/history, never from a guess. Rows with
    no ticket id cannot be matched reliably and are logged, not guessed.
    Returns {"settled": int, "changed": [descriptions]}.
    """
    hist = api_bet_history(driver, ["active", "won", "lost", "void"])
    by_short = {}
    by_long = {}
    for b in hist:
        if b.get("short_id"):
            by_short[str(b["short_id"])] = b
        if b.get("id"):
            by_long[str(b["id"])] = b
    changed = []
    settled = 0
    for r in rows:
        if not isinstance(r, dict) or r.get("status") not in ("active", "unconfirmed", None, ""):
            continue
        ticket = str(r.get("short_bet_id") or r.get("bet_id") or "")
        hb = by_short.get(ticket) or by_long.get(ticket)
        if hb is None:
            continue
        new_status = str(hb.get("status") or "").lower()
        if new_status in ("won", "lost", "void") and r.get("status") != new_status:
            r["status"] = new_status
            r["settled_at"] = datetime.now().isoformat(timespec="seconds")
            if new_status == "won":
                try:
                    r["won_amount"] = float(hb.get("possible_winnings") or 0)
                except (TypeError, ValueError):
                    r["won_amount"] = 0.0
            settled += 1
            changed.append(f"{r.get('placed_at')} {r.get('phone')} "
                           f"BET:{ticket} -> {new_status.upper()}"
                           + (f" +KES {r.get('won_amount', 0):,.2f}"
                              if new_status == "won" else ""))
    return {"settled": settled, "changed": changed}


def login(driver, phone: str, password: str) -> bool:
    """Submit the real login form.

    Clicking the word 'Login' and hoping was the original sin: the form was
    never submitted, so zero credential POSTs happened and every round died on
    'not authenticated'. Filling #username/#password and submitting
    # #secondary_login is what actually mints a session.
    """
    username = normalise_phone(phone)
    for attempt in range(1, 4):
        if not goto(driver, LOGIN_URL):
            continue
        time.sleep(2.0)

        # If the PREVIOUS account is still signed in, the login dialog never
        # mounts and #secondary_login is null - which is exactly how the second
        # account failed with "Cannot read properties of null (reading
        # 'submit')". Sign out first whenever we are already authenticated.
        try:
            if session_live(driver):
                log("  previous session still live - signing out before switching account")
                logout(driver)
                goto(driver, LOGIN_URL)
                time.sleep(1.5)
        except Exception:
            pass

        # Open the dialog (it may already be open).
        try:
            driver.execute_script("""
                var b = document.querySelector('#username');
                if (!b) {
                  var btns = document.querySelectorAll('button, a, [role=button]');
                  for (var i=0;i<btns.length;i++) {
                    if (/^(login|log in|sign in)$/i.test((btns[i].innerText||'').trim())) {
                      btns[i].click(); break;
                    }
                  }
                }
            """)
        except Exception:
            pass
        time.sleep(1.2)

        # Fill whatever mounted.
        try:
            driver.execute_script("""
                var u = document.querySelector('#username');
                var p = document.querySelector('#password');
                if (!u || !p) return false;
                function set(el, v){
                  var s = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype,'value').set;
                  s.call(el, v);
                  el.dispatchEvent(new Event('input', {bubbles:true}));
                  el.dispatchEvent(new Event('change', {bubbles:true}));
                }
                set(u, arguments[0]); set(p, arguments[1]);
                return true;
            """, username, password)
        except Exception:
            pass
        time.sleep(0.4)

        # Submit the real form.
        try:
            driver.execute_script("document.getElementById('secondary_login').submit();")
            log(f"  submitted login form for {phone} (attempt {attempt})")
        except Exception as exc:
            log(f"  login form submit failed: {str(exc)[:80]}")
            continue

        # Poll for a genuinely live session.
        deadline = time.time() + 25
        while time.time() < deadline:
            time.sleep(1.0)
            if session_live(driver):
                log(f"  logged in as {phone} - wallet API live")
                return True
        log(f"  attempt {attempt}: no live session yet")

    return False


def logout(driver) -> None:
    """Leave the account clean so the next login is never a 'new device'."""
    try:
        driver.execute_script("""
            var done = false;
            try {
              var a = document.querySelector('a[href*="logout"], a[href*="signout"]');
              if (a) { a.click(); done = true; }
            } catch(e){}
            if (!done) { try { sessionStorage.clear(); localStorage.clear(); } catch(e){} }
        """)
        time.sleep(1.5)
    except Exception:
        pass


# ── board ────────────────────────────────────────────────────────────────
# Read each row's teams, kick-off and the odds actually shown on it. Reading
# prices from the same row we later click means we never price a bet off a page
# we are not clicking.
EXTRACT_GAMES = r"""
var out = [];
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
for (var r = 0; r < rows.length; r++) {
  var row = rows[r];
  var id = row.getAttribute('data-event-id') || row.getAttribute('data-qa') || '';
  var m = String(id).match(/(\d{3,})/);
  if (!m) { var t = row.querySelector('[data-qa*="event-id"]'); if (t) m = String(t.textContent).match(/(\d{3,})/); }
  var gid = m ? m[1] : '';

  var teams = row.querySelectorAll('.event-team, [data-qa="prematch-event-competitors"]');
  var names = [];
  for (var t2 = 0; t2 < teams.length; t2++) {
    var v = (teams[t2].innerText || teams[t2].getAttribute('title') || '').replace(/\s+/g,' ').trim();
    if (v) names.push(v);
  }
  if (names.length < 2) continue;
  var home = names[0], away = names[1];
  // The listing rows carry NO event id (measured: gid came back empty on every
  // row), and an empty gid made the picker skip every game - which is why it
  // reported "no combination cleared the odds band" on a board full of prices.
  // The teams are a stable enough key for our purposes: we click by home-team
  // name anyway, and we only need uniqueness so two legs never share a game.
  if (!gid) gid = 'G:' + home + '|' + away;

  // kick-off: any element whose text is a clock time
  var ko = '';
  var koEls = row.querySelectorAll('[data-qa*="time"], .event-time, time');
  for (var k = 0; k < koEls.length; k++) {
    var txt = (koEls[k].innerText || koEls[k].getAttribute('datetime') || '').trim();
    if (/\d{1,2}:\d{2}/.test(txt)) { ko = txt; break; }
  }

  // Odds per market, read off the row itself.
  var odds = {};
  var mkts = row.querySelectorAll('.event-market');
  for (var i = 0; i < mkts.length; i++) {
    var mEl = mkts[i];
    var nmEl = mEl.querySelector('.event-market-name');
    var nm = nmEl ? (nmEl.innerText || '').replace(/\s+/g,' ').trim().toUpperCase() : '';
    var sels = mEl.querySelectorAll('.event-selection:not(.placeholder):not(.event-selection-disabled)');
    if (!sels.length) continue;
    var label = nm || 'UNKNOWN';
    for (var s = 0; s < sels.length; s++) {
      var o = parseFloat((sels[s].innerText || '').replace(',', '.'));
      if (o > 1.0) odds[label + '#' + s] = o;
    }
  }
  out.push({gid: gid, home: home, away: away, ko: ko, odds: odds});
}
return out;
"""

CLICK_LEG = r"""
var home = arguments[0], market = arguments[1];
var rows = document.querySelectorAll('.event-row:not(.event-row-header)');
function norm(s){ return (s||'').replace(/\s+/g,' ').trim().toUpperCase(); }
for (var r = 0; r < rows.length; r++) {
  var row = rows[r];
  var txt = norm(row.innerText);
  if (txt.indexOf(norm(home)) < 0) continue;

  var markets = row.querySelectorAll('.event-market');
  for (var i = 0; i < markets.length; i++) {
    var mEl = markets[i];
    var nmEl = mEl.querySelector('.event-market-name');
    var nm = nmEl ? norm(nmEl.innerText) : '';
    var match = false, idx = 0;
    if (market === 'home'  && /1X2|3 WAY/.test(nm)) { match = true; idx = 0; }
    else if (market === 'draw' && /1X2|3 WAY/.test(nm)) { match = true; idx = 1; }
    else if (market === 'away' && /1X2|3 WAY/.test(nm)) { match = true; idx = 2; }
    else if (market === 'btts' && /BOTH TEAMS/.test(nm)) { match = true; idx = 0; }
    else if (market === 'btts_no' && /BOTH TEAMS/.test(nm)) { match = true; idx = 1; }
    else if (market === 'dc_1x' && /DOUBLE CHANCE/.test(nm)) { match = true; idx = 0; }
    else if (market === 'dc_x2' && /DOUBLE CHANCE/.test(nm)) { match = true; idx = 1; }
    else if (market === 'dc_12' && /DOUBLE CHANCE/.test(nm)) { match = true; idx = 2; }
    // The listing serves the 1.50 goal line, so 'over'/'under'/'over15' all
    // mean the OVER/UNDER selection 0 (measured: no 2.5 line is offered here).
    else if (market === 'over' && /OVER\/UNDER/.test(nm)) { match = true; idx = 0; }
    else if (market === 'over15' && /OVER\/UNDER/.test(nm)) { match = true; idx = 0; }
    else if (market === 'under' && /OVER\/UNDER/.test(nm)) { match = true; idx = 1; }
    if (!match) continue;

    var sels = mEl.querySelectorAll('.event-selection:not(.placeholder):not(.event-selection-disabled)');
    if (sels.length > idx) {
      sels[idx].click();
      return true;
    }
  }
}
return false;
"""


def extract_games(driver) -> list:
    try:
        rows = driver.execute_script(EXTRACT_GAMES) or []
    except Exception as exc:
        log(f"  board read failed: {str(exc)[:90]}")
        return []
    games = []
    for g in rows:
        g["odds"] = {k: float(v) for k, v in (g.get("odds") or {}).items()}
        games.append(g)
    return games


def slip_count(driver) -> int:
    """Read the selection count from the site's own service."""
    try:
        n = driver.execute_script("""
            try {
              var app = document.querySelector('body');
              var c = window.angular.element(app).injector().get('BetslipService').count();
              return c || 0;
            } catch(e) { return -1; }
        """)
        return int(n)
    except Exception:
        return -1


# ── picking ──────────────────────────────────────────────────────────────
def games_bet_today(rows: list | None = None) -> set:
    """Fixtures already bet TODAY, as normalised match keys.

    Added because the engine kept picking the SAME two games round after round
    - three identical accumulators running, from a board carrying 50 games.
    That is not a strategy, it is one coin flip repeated. Reading the ledger is
    what makes excluding them possible at all.

    Keys are normalised to "HOME|AWAY" upper case, because the site's own
    rendering of a fixture is not guaranteed byte-identical between the board
    and the slip.
    """
    if rows is None:
        rows = load_ledger()
    today = _betting_day()
    used: set = set()
    for r in rows:
        if not isinstance(r, dict):
            continue
        # Shadow research slips are not bets: their fixtures stay available to
        # the real picker, and they must not shrink the board.
        if str(r.get("status") or "").startswith("shadow"):
            continue
        ts = str(r.get("placed_at") or "")
        if ts and not ts.startswith(today):
            continue                    # yesterday's bet is fair game again
        for g in r.get("games") or []:
            if not g:
                continue
            name = str(g).split("[")[0]
            home, _, away = name.partition(" vs ")
            if home.strip() and away.strip():
                used.add(f"{home.strip().upper()}|{away.strip().upper()}")
    return used


def pick_legs(games: list, want: int = TARGET_LEGS,
              exclude: set | None = None, rotation: int = 0) -> list:
    """Choose `want` single-game legs that together clear MIN_SLIP_ODDS.

    Rules that matter:
      - every leg must be priced ABOVE the 1.09 floor
      - every leg must come from a DIFFERENT game (no correlated accumulators)
      - combined odds must land inside [MIN_SLIP_ODDS, MAX_SLIP_ODDS]
      - the game must have at least MIN_LEAD_MINUTES before kick-off
    Preference order: markets that are less popular and therefore mispriced more
    often - DNB away, under 2.5, BTTS no - before the 3-way crowd.
    """
    MAX_LEGS = 4

    # Flatten (game, market, odds) with the floor applied.
    #
    # The listing rows were MEASURED, and they do not serve a 2.5 goal line -
    # they serve 1X2, BOTH TEAMS TO SCORE, DOUBLE CHANCE and OVER/UNDER 1.50.
    # So the 1.50 line is what "over"/"under" mean here. Market names arrive
    # with trailing junk ('1X2 X-UP " >'), so every test is a substring match.
    cands = []
    skipped_used = 0
    for g in games:
        if not g.get("gid"):
            continue
        # Never re-bet a fixture already used today. Skipped, not rejected: if
        # the board has nothing else, standing down beats a repeat.
        if exclude:
            key = f"{str(g.get('home','')).strip().upper()}|{str(g.get('away','')).strip().upper()}"
            if key in exclude:
                skipped_used += 1
                continue
        od = g.get("odds") or {}

        def find(pred, market):
            k = next((kk for kk in od if pred(kk)), None)
            if not k:
                return None
            o = od[k]
            return {"gid": g["gid"], "home": g["home"], "away": g["away"],
                    "market": market, "odds": o, "ko": g.get("ko", "")} if o > MIN_LEG_ODDS else None

        def idx_of(k):
            try:
                return int(str(k).split("#")[-1])
            except Exception:
                return -1

        for market in PREF:
            c = None
            if market == "home":
                c = find(lambda k: ("1X2" in k or "3 WAY" in k) and idx_of(k) == 0, market)
            elif market == "draw":
                c = find(lambda k: ("1X2" in k or "3 WAY" in k) and idx_of(k) == 1, market)
            elif market == "away":
                c = find(lambda k: ("1X2" in k or "3 WAY" in k) and idx_of(k) == 2, market)
            elif market == "btts":
                c = find(lambda k: "BOTH TEAMS" in k and idx_of(k) == 0, market)
            elif market == "btts_no":
                c = find(lambda k: "BOTH TEAMS" in k and idx_of(k) == 1, market)
            elif market == "dc_1x":
                c = find(lambda k: "DOUBLE CHANCE" in k and idx_of(k) == 0, "dc_1x")
            elif market == "dc_x2":
                c = find(lambda k: "DOUBLE CHANCE" in k and idx_of(k) == 1, "dc_x2")
            elif market == "dc_12":
                c = find(lambda k: "DOUBLE CHANCE" in k and idx_of(k) == 2, "dc_12")
            elif market in ("over", "under"):
                c = find(lambda k: "OVER/UNDER" in k and idx_of(k) == (0 if market == "over" else 1),
                         market)
            elif market == "over15":
                c = find(lambda k: "OVER/UNDER" in k and idx_of(k) == 0, "over15")
            if c:
                cands.append(c)

    if not cands:
        return []

    # Round-robin draft across markets (see _draft_legs). The DOM listing has
    # no selection ids, so require_sel_id is off here. MAX_LEGS is the cap.
    # The learned market weights steer the ORDER (same wiring as the API
    # picker - measured 2026-10-15: this rotation used to run blind, so the
    # learner's "this market beats its price" never moved a pick).
    try:
        import pick_filters
        weights = (pick_filters.load_learning() or {}).get("weights") or {}
        order = pick_filters.rotation_with_weights(PREF, weights)
    except Exception:
        order = list(PREF)
    return _draft_legs(cands, _rotate_markets(order, rotation), want,
                       require_sel_id=False, max_legs=MAX_LEGS)


# ── placing ──────────────────────────────────────────────────────────────
SET_STAKE = r"""
var want = arguments[0];
var el = document.querySelector('#amount-prematch')
        || document.querySelector('input[name="amount"]')
        || document.querySelector('.betslip-stake input');
if (!el) return 'no-input';
var s = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype,'value').set;
s.call(el, String(want));
el.dispatchEvent(new Event('input', {bubbles:true}));
el.dispatchEvent(new Event('change', {bubbles:true}));
el.blur();
return 'ok';
"""

READ_TOTALS = r"""
try {
  var app = document.querySelector('body');
  var inj = window.angular.element(app).injector();
  var slips = inj.get('BetslipService').getAllBetslips();
  return JSON.stringify({n: slips ? slips.length : 0});
} catch(e) { return null; }
"""


def set_stake(driver, amount: float) -> bool:
    """Set the bet amount.

    Typing into #amount-prematch does NOT update the site's Angular model - the
    field is bound to the controller, and the controller never hears about a
    programmatic value change. The slip's own amount chips are the real
    controls, so click the chip that matches the stake instead, and only fall
    back to typing if no chip exists.

    Symptom this fixes: PLACE BET was clicked on the correct element and the
    handler ran, but no request was ever made - the slip had no valid amount,
    so placement was silently refused.
    """
    want = str(int(amount)) if float(amount).is_integer() else str(amount)

    # 1) The site's own chip - preferred, because it updates the model properly.
    try:
        hit = driver.execute_script(r"""
            var want = arguments[0];
            var scope = document.querySelector('form.live-betslip')
                      || document.querySelector('.betslip-v2')
                      || document.body;
            var els = scope.querySelectorAll('button, a, div[ng-click], span[ng-click], li, label');
            for (var i = 0; i < els.length; i++) {
              var e = els[i];
              if (e.offsetHeight <= 0 || e.offsetWidth <= 0) continue;
              var t = ((e.innerText || e.textContent || '') + '').replace(/\s+/g,' ').trim();
              if (t !== want) continue;
              // Skip the total-odds/possible-win cells, which also contain digits.
              var cls = (typeof e.className === 'string') ? e.className : '';
              if (/total|payout|odds|win/i.test(cls)) continue;
              var ng = e.getAttribute('ng-click') || '';
              if (!ng && e.tagName !== 'BUTTON' && e.tagName !== 'A') continue;
              e.scrollIntoView({block: 'center'});
              e.click();
              return 'chip:' + t;
            }
            return 'none';
        """, want)
        if hit and str(hit).startswith("chip"):
            log(f"  amount set via the site's own {hit.split(':')[1]} chip")
            time.sleep(0.8)
            return True
    except Exception as exc:
        log(f"  chip click failed: {str(exc)[:70]}")

    # 2) Fallback: type it.
    for _ in range(3):
        try:
            res = driver.execute_script(SET_STAKE, amount)
            if res == "ok":
                log(f"  amount typed into the field ({want})")
                time.sleep(0.4)
                return True
            log(f"  stake field: {res}")
        except Exception:
            pass
        time.sleep(0.6)
    return False


def slip_totals(driver) -> tuple[float, float]:
    """Return (odds, possible_win) for the slip.

    Read from the site's own service, not from page text. A regex over innerText
    was matching the wrong number and reported a 2-leg x4.13 slip as x1.56, so
    the odds floor refused a perfectly good bet for no reason.
    """
    try:
        res = driver.execute_script(r"""
            try {
              var app = document.querySelector('body');
              var inj  = window.angular.element(app).injector();
              var svc  = inj.get('BetslipService');
              var slips = svc.getAllBetslips();
              var n = slips ? slips.length : 0;
              var prod = 1, seen = 0;
              for (var i = 0; i < n; i++) {
                var s = slips[i] || {};
                var o = s.odds || s.totalOdds || s.price;
                if (typeof o === 'string') o = parseFloat(o);
                if (o && o > 1) { prod *= o; seen++; }
              }
              if (!seen || !isFinite(prod) || prod <= 1) {
                var t = (document.body && document.body.innerText) || '';
                var ms = t.match(/TOTAL ODDS\s*[:]?\s*([\d.,]+)/i);
                if (ms) { prod = parseFloat(ms[1].replace(',', '.')); seen = 1; }
              }
              var st = document.querySelector('#amount-prematch');
              var stake = st ? parseFloat(st.value) : 0;
              return {odds: (seen ? prod : 0), win: (seen ? prod * (stake || 0) : 0)};
            } catch(e) { return {odds: 0, win: 0}; }
        """)
        if isinstance(res, dict):
            return float(res.get("odds") or 0), float(res.get("win") or 0)
    except Exception:
        pass
    return 0.0, 0.0


def place_and_confirm(driver, stake: float) -> dict:
    """Click PLACE BET and find out exactly what happened.

    The old engine clicked and then guessed, so a round that was rejected, a
    round that needed a confirmation tap, and a round that silently did nothing
    all produced the same log line. This reports the three signals that
    actually distinguish them:

      1. did the slip empty?        -> the book accepted it
      2. did a dialog appear, and what does it say?
      3. what HTTP status did /api/bets/place return?

    Returns a dict with placed/dialog/status/balance_after.
    """
    result = {"placed": False, "dialog": "", "status": None, "count_after": None}

    # Clear any promo popup first - it can silently swallow the click.
    dismiss_overlays(driver)

    # Report whether the control we are about to press is even enabled. A
    # disabled PLACE BET means Angular has not accepted the stake yet, which is
    # a completely different problem from "the click is not landing".
    try:
        info = driver.execute_script(r"""
            var out = [];
            var els = document.querySelectorAll('a, button, div, span');
            for (var i = 0; i < els.length; i++) {
              var e = els[i];
              if (e.offsetHeight <= 0 || e.offsetWidth <= 0) continue;
              var t = (e.innerText || '').replace(/\s+/g,' ').trim().toLowerCase();
              if (t.indexOf('place bet') < 0) continue;
              out.push({t: t.slice(0,40),
                        dis: (e.disabled === true) ? 1 : 0,
                        ng: (e.getAttribute('ng-click') || '').slice(0,60),
                        cls: (typeof e.className === 'string' ? e.className : '').slice(0,60),
                        aria: e.getAttribute('aria-disabled') || '',
                        area: e.offsetWidth * e.offsetHeight});
            }
            return out;
        """)
        if info:
            for r in info[:6]:
                log(f"    candidate '{r['t']}' disabled={r['dis']} "
                    f"aria-disabled={r['aria']!r} ng-click={r['ng'][:40]!r} cls={r['cls'][:40]!r}")
        else:
            log("    no visible element containing 'place bet'")
    except Exception as exc:
        log(f"    control inspection failed: {str(exc)[:80]}")

    # Watch the network while we click, so we capture the real status rather
    # than reading the capture before loadend has fired.
    driver.execute_script(r"""
        window.__placeNet = [];
        try {
          var of = window.fetch;
          window.fetch = function(input, init){
            var url = (typeof input === 'string') ? input : (input && input.url) || '';
            var m = (init && init.method) || 'GET';
            if (/place/i.test(String(url))) {
              var rec = {url: String(url).slice(0,150), status: null, body: ''};
              window.__placeNet.push(rec);
              return of.apply(this, arguments).then(function(r){
                rec.status = r.status;
                try { r.clone().text().then(function(t){ rec.body = String(t).slice(0,400); }); } catch(e){}
                return r;
              });
            }
            return of.apply(this, arguments);
          };
        } catch(e){}
    """)

    clicked = click_place(driver)
    log(f"  PLACE BET clicked: {clicked}")

    # ── STEP 2: answer the confirmation dialog ────────────────────────────
    # Measured on the live page: clicking PLACE BET does NOT submit the bet.
    # It opens a SweetAlert - DIV.sweet-alert.showSweetAlert, "Confirm your
    # bet", with <button class="confirm">OK</button>. The bet is only submitted
    # when that OK is pressed. Every earlier version clicked PLACE, saw no
    # request, and reported "not placed" - it was never failing to click PLACE,
    # it was failing to press CONFIRM.
    time.sleep(1.2)          # let the dialog mount
    confirmed = handle_prompts(driver, seconds=10.0)
    if "CONFIRMED" in confirmed:
        log("    confirmation dialog answered")
    else:
        log("    no confirmation dialog needed answering")

    # Poll for up to ~20s: the book either empties the slip, shows a dialog,
    # or answers the request. Watching all three at once means we report what
    # really happened instead of assuming.
    deadline = time.time() + 20
    while time.time() < deadline:
        time.sleep(1.0)
        try:
            cnt = slip_count(driver)
            result["count_after"] = cnt
            if cnt == 0:
                result["placed"] = True
                break
        except Exception:
            pass
        try:
            d = driver.execute_script(r"""
                var out = [];
                var sel = '.sweet-alert, .swal2-container, .swal2-popup, [role=dialog]:not([aria-hidden=true]), '
                        + '.modal.show, .modal-dialog, [class*=confirm]';
                var els = document.querySelectorAll(sel);
                for (var i = 0; i < els.length; i++) {
                  var e = els[i];
                  if (e.offsetHeight <= 0 || e.offsetWidth <= 0) continue;
                  // The dialog's own innerText is often just the button label
                  // ("OK"), which told us nothing. Pull the MESSAGE containers
                  // explicitly - that is what actually says why the bet was
                  // refused.
                  var msg = '';
                  var parts = e.querySelectorAll(
                      '.swal2-title, .swal2-content, .modal-title, .modal-body, '
                    + '.alert-message, [class*=message], [class*=content], p, h3, h4');
                  for (var m = 0; m < parts.length; m++) {
                    var t = ((parts[m].innerText || '') + '').replace(/\s+/g,' ').trim();
                    if (t && t.length > 2 && t.toUpperCase() !== 'OK') { msg += t + ' / '; }
                  }
                  if (!msg) {
                    var raw = ((e.innerText||'')+'').replace(/\s+/g,' ').trim();
                    if (raw && raw.toUpperCase() !== 'OK') msg = raw;
                  }
                  if (msg) out.push(msg.slice(0, 240));
                }
                return out.join(' || ');
            """)
            if d and d not in result["dialog"]:
                result["dialog"] = d
                log(f"    dialog: {d[:170]}")
                # Already answered above; handle_prompts is one-shot, so
                # calling it again here is harmless and catches a dialog that
                # only appeared later in the round.
                handle_prompts(driver, seconds=6.0)
        except Exception:
            pass
        try:
            st = driver.execute_script(r"""
                var a = window.__placeNet || [];
                if (!a.length) return null;
                var last = a[a.length-1];
                return last && last.status !== null ? last.status : null;
            """)
            if st:
                result["status"] = int(st)
        except Exception:
            pass

    try:
        body = driver.execute_script(r"""
            var a = window.__placeNet || [];
            return a.length ? (a[a.length-1].body || '') : '';
        """)
        if body:
            log(f"    place response body: {str(body)[:180]}")
            result["body"] = str(body)[:400]
    except Exception:
        pass

    return result


def dismiss_overlays(driver) -> int:
    """Close the real, measured popups before placing.

    Targeted at the actual structures. The previous generic [class*=popup]
    sweep reported 0 every time while the advert sat on screen the whole
    time - a false all-clear, which is worse than not checking. Measured off
    the live page:

      * advert  : div#menu-section__goal-rush-notice.custom-tooltip
                  closed by a.custom-tooltip__close (its label reads "OK")
      * cookies : div#cookies-law-info-content
                  accepted by the "ACCEPT" button ($ctrl.setCookieConsent)

    The betslip is never touched, and the confirmation SweetAlert is left
    alone - that dialog is how the bet is actually submitted.
    """
    try:
        n = driver.execute_script(r"""
            var closed = 0;
            function vis(e) { return e && e.offsetWidth > 0 && e.offsetHeight > 0; }

            // 1. The Goal Rush / Lucky Numbers advert tooltip.
            var tips = document.querySelectorAll(
                '.custom-tooltip, [id^=menu-section__], .custom-tooltip--deposit');
            for (var i = 0; i < tips.length; i++) {
                if (!vis(tips[i])) continue;
                if (tips[i].querySelector('form.live-betslip')) continue;
                var x = tips[i].querySelector(
                    'a.custom-tooltip__close, .custom-tooltip__close, [class*=close]');
                if (x && vis(x)) {
                    try { x.click(); closed++; } catch (e) {}
                }
            }

            // 2. The cookie-consent bar across the bottom of the page.
            var ck = document.getElementById('cookies-law-info-content')
                  || document.querySelector('[class*=cookie]');
            if (vis(ck)) {
                var bs = ck.querySelectorAll('button, a');
                for (var b = 0; b < bs.length; b++) {
                    var t = (bs[b].innerText || '').replace(/\s+/g, ' ').trim();
                    if (/^(accept|accept all|agree|i agree|got it|ok)$/i.test(t)) {
                        try { bs[b].click(); closed++; } catch (e) {}
                        break;
                    }
                }
            }
            return closed;
        """)
        if n:
            log(f"  dismissed {n} promotional overlay(s) (advert / cookies)")
            time.sleep(0.8)
        return int(n or 0)
    except Exception as exc:
        log(f"  overlay sweep failed: {str(exc)[:80]}")
        return 0


def click_place(driver) -> str:
    """Click the REAL PLACE BET control. Returns which strategy worked.

    Measured the hard way: the element whose visible text is exactly
    'place bet' is a LABEL. Clicking it does nothing at all - no request, no
    dialog, slip unchanged. So rather than guess again, try the plausible
    paths in order and report which one fired:

      1. the 'place bet' element that actually carries an ng-click handler
      2. any element inside the betslip form whose ng-click mentions 'place'
      3. the 'place bet' element's closest clickable ancestor
      4. submitting the betslip <form> (fires a plain HTML submit)
      5. the site's own service method, if it exposes one

    The strategy name is returned so the log says exactly what happened
    instead of a bare true/false.
    """
    strategies = [
        # The real control, measured: <a class="place-bet ..." ng-click="$ctrl.onPlaceBet($event)">
        ("a.place-bet (the site's own control)", r"""
            var els = document.querySelectorAll(
                'a.place-bet, .place-bet, [data-qa=betslip-actions-], a[ng-click*="onPlaceBet"]');
            for (var i = 0; i < els.length; i++) {
              var el = els[i];
              if (el.offsetHeight <= 0 || el.offsetWidth <= 0) continue;
              if (el.disabled) continue;
              // Bring it into view: it lives in the slip FOOTER and can sit
              // below the fold, which is why the click used to vanish.
              try { el.scrollIntoView({block: 'center', inline: 'center'}); } catch(e){}
              el.click();
              return 'ok';
            }
            return 'none';
        """),
        ("ng-click on the exact label", r"""
            var els = document.querySelectorAll('a, button, div, span');
            var best = null, bestArea = 1e12;
            for (var i = 0; i < els.length; i++) {
              var el = els[i];
              if (el.offsetHeight <= 0 || el.offsetWidth <= 0) continue;
              var t = (el.innerText || '').replace(/\s+/g,' ').trim().toLowerCase();
              if (t !== 'place bet') continue;
              if (!el.getAttribute('ng-click')) continue;
              var area = el.offsetWidth * el.offsetHeight;
              if (area < bestArea) { bestArea = area; best = el; }
            }
            if (!best) return 'none';
            try { best.scrollIntoView({block: 'center'}); } catch(e){}
            best.click(); return 'ok';
        """),
        ("ng-click mentioning 'place' inside the slip form", r"""
            var form = document.querySelector('form.live-betslip, [data-qa=unified-betslip], form');
            if (!form) return 'none';
            var els = form.querySelectorAll('[ng-click], button, a, div, span');
            for (var i = 0; i < els.length; i++) {
              var el = els[i];
              if (el.offsetHeight <= 0 || el.offsetWidth <= 0) continue;
              var ng = el.getAttribute('ng-click') || '';
              var t  = ((el.innerText||'') + ' ' + (typeof el.className === 'string' ? el.className : '')).toLowerCase();
              if (ng && /place/.test(ng) && /place/.test(t)) { el.click(); return 'ok'; }
              if (ng && /place/.test(ng) && /bet/.test(t))   { el.click(); return 'ok'; }
            }
            return 'none';
        """),
        ("clickable ancestor of the label", r"""
            var els = document.querySelectorAll('a, button, div, span');
            for (var i = 0; i < els.length; i++) {
              var el = els[i];
              if (el.offsetHeight <= 0 || el.offsetWidth <= 0) continue;
              if ((el.innerText || '').replace(/\s+/g,' ').trim().toLowerCase() !== 'place bet') continue;
              var p = el;
              for (var d = 0; d < 4 && p; d++) {
                p = p.parentElement;
                if (!p) break;
                var tag = p.tagName;
                if (tag === 'BUTTON' || tag === 'A' || p.getAttribute('ng-click') || p.onclick) {
                  p.click(); return 'ok';
                }
              }
              return 'none';
            }
            return 'none';
        """),
        ("submit the betslip form", r"""
            var f = document.querySelector('form.live-betslip, [data-qa=unified-betslip], form.betslip');
            if (!f) return 'none';
            if (typeof f.requestSubmit === 'function') { f.requestSubmit(); return 'ok'; }
            f.submit(); return 'ok';
        """),
        ("service place method", r"""
            try {
              var app = document.querySelector('body');
              var svc = window.angular.element(app).injector().get('BetslipService');
              var names = ['placeBet','place','placeBets','submit','confirmBet','sendBet'];
              for (var i = 0; i < names.length; i++) {
                if (typeof svc[names[i]] === 'function') {
                  svc[names[i]]();
                  return 'ok:' + names[i];
                }
              }
            } catch(e){}
            return 'none';
        """),
    ]

    for label, js in strategies:
        try:
            res = driver.execute_script(js)
        except Exception as exc:
            log(f"    strategy '{label}' errored: {str(exc)[:70]}")
            continue
        if res and str(res).startswith("ok"):
            time.sleep(0.6)
            return f"{label} -> {res}"
        log(f"    strategy '{label}': no match")
    return "none"


def handle_prompts(driver, seconds: float = 6.0) -> str:
    """Watch for and answer whatever the site throws after PLACE is clicked.

    Reports what it actually saw. The previous version clicked buttons blindly
    and returned a vague string, so a round that failed for any reason looked
    identical to a round that was still working - which is how weeks of blind
    retries happened.
    """
    deadline = time.time() + seconds
    seen: list[str] = []
    # Confirm exactly ONCE. The polling loop below can outlive the dialog's
    # close animation, and clicking confirm twice submits the bet twice - which
    # on a real balance is the worst possible bug to have.
    confirmed = {"done": False}
    while time.time() < deadline:
        try:
            res = driver.execute_script(r"""
                var msgs = [];

                // ── 1. THE ONE THAT MATTERS ────────────────────────────────────
                // A screenshot of the live page proved the real flow is:
                //     click PLACE BET  ->  a SweetAlert "Confirm your bet"
                //     ->  its OK button actually submits the bet.
                // The dialog is DIV.sweet-alert.showSweetAlert and the button is
                // <button class="confirm">OK</button>. The previous code looked
                // for .swal2-container, a class this site never emits, so the
                // dialog was found every time and never answered. That is why
                // rounds ended "clicked: ok / not placed" with no request.
                var sa = document.querySelector('.sweet-alert, .swal2-container');
                var alreadyConfirmed = arguments[0];
                if (sa && !alreadyConfirmed) {
                    var cap = ((sa.innerText || '') + '').replace(/\s+/g, ' ').trim();
                    if (cap) msgs.push('sweetalert: ' + cap.slice(0, 120));
                    var confirmBtn = sa.querySelector('button.confirm, .swal2-confirm');
                    if (confirmBtn) {
                        confirmBtn.click();
                        msgs.push('CONFIRMED:button.confirm');
                    } else {
                        var fallback = sa.querySelectorAll('button, .swal2-button');
                        for (var f = 0; f < fallback.length; f++) {
                            var ft = ((fallback[f].innerText || '') + '')
                                     .replace(/\s+/g, ' ').trim().toUpperCase();
                            if (ft === 'OK' || ft === 'YES' || ft === 'CONFIRM' ||
                                ft === 'CONTINUE' || ft === 'PLACE BET') {
                                fallback[f].click();
                                msgs.push('CONFIRMED:' + ft);
                                break;
                            }
                        }
                    }
                }

                // ── 2. Other dialogs, as before ──────────────────────────────
                var dialogs = document.querySelectorAll(
                    '.modal, [role=dialog], .alert, [class*=toast], [class*=notification]');
                for (var i = 0; i < dialogs.length; i++) {
                    var d = dialogs[i];
                    if (d.offsetHeight <= 0) continue;
                    if (sa && (d === sa || sa.contains(d) || d.contains(sa))) continue;
                    var txt = ((d.innerText || '') + '').replace(/\s+/g, ' ').trim();
                    if (!txt) continue;
                    msgs.push(txt.slice(0, 160));
                    var btns = d.querySelectorAll('button, [role=button], a');
                    for (var b = 0; b < btns.length; b++) {
                        var t = (btns[b].innerText || '').replace(/\s+/g,' ').trim().toUpperCase();
                        if (t === 'OK' || t === 'YES' || t === 'CONFIRM' ||
                            t === 'CONTINUE' || t === 'PLACE BET' || t === 'YES, PLACE BET') {
                            btns[b].click();
                            break;
                        }
                    }
                }
                return msgs.join(' || ');
            """, confirmed["done"])
            if res:
                for part in str(res).split(" || "):
                    if part and part not in seen:
                        seen.append(part)
                    if part.startswith("CONFIRMED:"):
                        confirmed["done"] = True
                        # The bet is submitted; give the site time to answer
                        # before we go back to looking for dialogs.
                        time.sleep(2.5)
                        break
                time.sleep(0.7)
                continue
        except Exception:
            pass
        if slip_count(driver) <= 0:
            break
        time.sleep(0.5)

    if seen:
        for m in seen[:4]:
            log(f"    site said: {m[:150]}")
    else:
        log("    no confirmation dialog appeared")
    return " | ".join(seen)[:400]


# ── one round ────────────────────────────────────────────────────────────
def settle_verdict(before: float | None, after: float | None,
                   res: dict) -> tuple[bool, bool]:
    """Decide whether a bet actually went in, and how much we trust that.

    Three signals: slip emptied, HTTP status, balance drop. Any one used to be
    enough - and that produced a FALSE POSITIVE, proven by arithmetic rather
    than assumption: the book showed KES 40 of stakes for one night (103.58 ->
    63.58, four bets), yet the ledger recorded five. So one row claimed
    "placed" while no money moved.

    The slip emptying is not proof on its own: an abandoned or reverted slip
    also empties. The HTTP status is not proof either: a 200 can carry an error
    body. The balance moving IS proof - it is the bookie's own arithmetic. So
    the money is the deciding signal and everything else is corroboration:
    when they disagree the bet is still recorded (the cap must never be
    optimistic) but flagged unconfirmed so an auditor can discount it.

    Returns (placed, row_unconfirmed).
    """
    slip_empty = res.get("count_after") == 0
    # A malformed status must not raise - this decides whether money moved,
    # and a crash here would lose the whole round after the bet was already
    # sent. Unknown is treated as "not corroborating".
    try:
        http_ok = res.get("status") is not None and int(res["status"]) < 400
    except (TypeError, ValueError):
        http_ok = False

    if before is not None and after is not None and after < before:
        return True, False
    if slip_empty or http_ok:
        log("  WARNING: slip/HTTP suggest the bet went in but the balance did "
            "not move. Recording it as uncertain - verify against Bet History.")
        return True, True
    return False, False


def do_round(driver, phone: str, password: str, stake: float,
             rotation: int = 0) -> dict | None:
    """Login -> board -> pick -> place -> verify. Returns the ledger row."""
    t0 = time.time()

    # Only log in if there is no live session. Logging in unconditionally was
    # actively harmful: login() signs a live session OUT first, so a round on
    # an already-authenticated browser tore the session down, re-navigated, and
    # then usually failed with "Cannot read properties of null (reading
    # 'submit')" because the login form had not remounted yet. That burned ~90s
    # per round and risked the SPA teardown for nothing.
    if session_live(driver):
        log(f"  session already live - continuing as {phone}")
    else:
        log(f"  logging in as {phone}")
        if not login(driver, phone, password):
            log("  LOGIN FAILED")
            return None

    # The floor lives here, NOT in a caller: by this point the driver has
    # navigated to the book and holds a live session, so
    # fetch('/api/wallets/balance') runs on the right origin. A caller-side
    # read used to run on a fresh about:blank driver and died immediately -
    # "unreadable (1/3)" forever, bets never placed (measured 2026-10-09).
    before = read_balance(driver)
    if before is None:
        log("  balance unreadable - refusing to bet blind this round")
        return {"unreadable": True}
    base_stake = float(stake)
    if before < MIN_FULL_BALANCE_STAKE:
        log(f"  balance KES {before:,.2f} is below the betting floor "
            f"KES {MIN_FULL_BALANCE_STAKE:,.2f} - not betting")
        return {"balance_floor": True, "balance": before}
    log(f"  balance: KES {before:,.2f}")

    # The book decides settlement; the ledger just reflects it. Reconcile
    # anything the book settled since the last round before doing new business.
    ledger = load_ledger()
    if ledger:
        st = settle_from_history(driver, ledger)
        if st["settled"]:
            save_ledger(ledger)
            for line in st["changed"]:
                log(f"  SETTLED: {line}")

    # Board: the JSON feeds first (real gids + every market + kickoff times),
    # and the DOM board only if every feed comes back empty.
    log("  reading the board (API)")
    games = api_board(driver)
    api_mode = bool(games)
    if not games:
        log("  board API empty - falling back to the DOM board")
        goto(driver, TODAY_URL)
        # Wait for real rows - these pages sit behind a hydration wall.
        deadline = time.time() + 20
        games = []
        while time.time() < deadline:
            games = extract_games(driver)
            if games:
                break
            time.sleep(1.0)
    log(f"  {len(games)} game(s) on the board")
    if not games:
        logout(driver)
        return None
    # Other sports on the same day: basketball/tennis/hockey/... boards, so a
    # slip can mix sports (the book accepts multi-sport accumulators). Added
    # after the football board so an empty football board never blocks them.
    try:
        extra = api_other_sports(driver, max_games=8)
        if extra:
            games = games + [g for g in extra
                             if g["gid"] not in {x.get("gid") for x in games}]
            log(f"  board now {len(games)} game(s) across sports")
    except Exception as exc:
        log(f"  other-sports board skipped: {str(exc)[:70]}")
    # Save the board so the idle research pass (flashscore H2H) knows which
    # pairings are worth a browser load. Best-effort: a failed write just means
    # a less focused research pass next gap.
    try:
        (LIVE / "last_board.json").write_text(json.dumps(games), encoding="utf-8")
    except Exception:
        pass

    # Never re-bet a fixture already used today. This is what stops the engine
    # from placing the same accumulator all day.
    used_today = games_bet_today(load_ledger())
    if used_today:
        log(f"  {len(used_today)} fixture(s) already bet today - excluded")

    # Pick legs. If the API board produced games but no combination cleared the
    # band - which happens when its markets call glitches and leaves games
    # without odds - fall back to the DOM board instead of standing down. The
    # DOM path is slower but proven; it must stay the floor of this engine.
    legs = api_pick_legs(games, exclude=used_today, rotation=rotation) if api_mode else []
    # SHARE THE SPOILS: if this account's rotation produced no slip, try the
    # other rotations before standing down - every phone should bet each round.
    if not legs and api_mode:
        for alt_rot in range(1, 6):
            legs = api_pick_legs(games, exclude=used_today, rotation=alt_rot)
            if legs:
                log(f"  rotation {rotation} found no slip - rotation {alt_rot} did")
                break
    if not legs and api_mode:
        log("  API pick found no playable combination - falling back to the DOM board")
        goto(driver, TODAY_URL)
        deadline = time.time() + 20
        games = []
        while time.time() < deadline:
            games = extract_games(driver)
            if games:
                break
            time.sleep(1.0)
        api_mode = False
        legs = pick_legs(games, exclude=used_today, rotation=rotation) if games else []
    if not legs:
        log("  no combination cleared the odds band - standing down this round")
        logout(driver)
        return None

    product = 1.0
    for leg in legs:
        product *= leg["odds"]

    # Odds-band calibration gate: a shape with enough REAL settled bets and a
    # proven negative ROI is not re-bet. The recipe table is written by the
    # legacy win-sync; the key uses the same band bins so it matches. Standing
    # down costs one round; re-betting a -90% band every round costs the
    # account. (No recipe has cleared 15 real bets yet - until then this gate
    # is silent and everything behaves exactly as before.)
    vetoed = load_vetoed_recipes()
    if vetoed:
        rkey = f"{len(legs)}L@{_band_of(product)}"
        ev = vetoed.get(rkey)
        if ev:
            log(f"  OMITTED: recipe {rkey} is a proven loser "
                f"({ev['trials']} real bets, ROI {ev['roi']:+.0%}) - "
                f"that odds band is not bet again")
            logout(driver)
            return None

    # Shadow research slips: alternate shapes on this same board, zero stake,
    # settled later against real scores. Pure learning - never a bet, never
    # counted against the cap, and their fixtures stay available to the real
    # picker (both ledger readers skip shadow rows).
    try:
        shadows = make_shadow_slips(games, legs, rotation)
        if shadows:
            ledger = load_ledger()
            ledger.extend(shadows)
            save_ledger(ledger)
            shapes = ", ".join(f"{s['legs']}L@{_band_of(s['odds'])}"
                               for s in shadows)
            log(f"  shadow research: {len(shadows)} alternate shape(s) "
                f"simulated at zero stake ({shapes})")
    except Exception as exc:
        log(f"  shadow research skipped: {str(exc)[:70]}")

    # Stake sizing AFTER the legs are known (confidence needs the model EVs):
    # an under-funded account bets the FULL balance; a well-modelled slip is
    # staked above the base, capped at MAX_MODEL_STAKE. The hard floor already
    # returned above, so this is only the sizing itself.
    stake = _effective_stake(before, base_stake, legs)
    if stake is None:
        log("  effective stake below the book's practical minimum - standing down")
        logout(driver)
        return None
    if abs(stake - base_stake) > 0.001:
        log(f"  stake sized to KES {stake:,.2f} (base KES {base_stake:,.2f})")

    log(f"  picked {len(legs)} leg(s) -> x{product:.2f}")
    for leg in legs:
        line = f"    - {leg['home']} vs {leg['away']} [{leg['market']}] @ {leg['odds']:.2f}"
        if leg.get("sel_id"):
            line += " (sel " + str(leg["sel_id"])
            if leg.get("br"):
                line += f", h2h {BETRADAR_H2H.format(leg['br'])}"
            line += ")"
        log(line)

    # Place the bet. The API path posts the exact selections the book quoted; the
    # DOM path is the fallback - used when the legs are not API-native and when
    # the book did not answer the API at all (a blip or dead session; the UI
    # path to the same server can still get through).
    placed, row_unconfirmed, res, odds = False, False, {}, product
    if api_mode and all(leg.get("sel_id") for leg in legs):
        log("  placing via API")
        res = api_place(driver, legs, stake, accept_odds=True)
        if res.get("return_code") is None:
            log("  API placement gave no answer - retrying through the DOM")
            api_mode = False
            res = {}
    if api_mode:
        if res.get("return_code") == 0:
            placed = True
            log(f"  API placed: {res.get('msgtext', '')[:170]}")
        else:
            log(f"  API refused: {json.dumps(res)[:220]}")
        after = read_balance(driver)
        if placed and before is not None and after is not None and after >= before:
            row_unconfirmed = True
            log("  WARNING: API says placed but the balance did not move - "
                "recording it as uncertain")
    else:
        log("  placing via DOM (fallback path)")
        clicked = 0
        for leg in legs:
            try:
                if driver.execute_script(CLICK_LEG, leg["home"], leg["market"]):
                    clicked += 1
                    time.sleep(0.5)
            except Exception:
                pass
        log(f"  clicked {clicked}/{len(legs)} leg(s); slip shows {slip_count(driver)}")
        if slip_count(driver) < MIN_LEGS:
            log("  slip did not take - abandoning round")
            logout(driver)
            return None

        # Open the slip panel so the stake field exists.
        try:
            driver.execute_script("""
                var p = document.querySelector('form.live-betslip, .betslip, [class*=betslip]');
                if (p && p.classList.contains('collapsed')) p.classList.remove('collapsed');
            """)
        except Exception:
            pass
        time.sleep(0.6)

        if not set_stake(driver, stake):
            log("  could not set the stake - not placing blind")
            logout(driver)
            return None

        odds, win = slip_totals(driver)
        log(f"  stake KES {stake:,.2f} set; slip totals x{odds:.2f} / win KES {win:,.2f}")
        if odds and odds < MIN_SLIP_ODDS:
            log(f"  slip priced below the x{MIN_SLIP_ODDS:.2f} floor - not placing")
            logout(driver)
            return None

        log("  placing the bet")
        res = place_and_confirm(driver, stake)

        after = read_balance(driver)
        placed, row_unconfirmed = settle_verdict(before, after, res)

    elapsed = time.time() - t0
    log(f"  round took {elapsed:.0f}s (budget {DEADLINE_SECONDS:.0f}s)")
    if res.get("count_after") is not None or res.get("status"):
        log(f"  slip after: {res.get('count_after')} | place HTTP: {res.get('status')}")
    if res.get("dialog"):
        log(f"  dialog: {res['dialog'][:170]}")
    if res.get("msgtext"):
        log(f"  book: {res['msgtext'][:170]}")
    log(f"  balance: KES {before:,.2f} -> KES {after:,.2f}"
        if before is not None and after is not None else "  balance: unreadable")

    row = None
    if placed:
        row = {"placed_at": datetime.now().isoformat(timespec="seconds"),
               "phone": phone, "stake": stake, "odds": odds or round(product, 2),
               "legs": len(legs),
               "games": [f"{l['home']} vs {l['away']} [{l['market']}]" for l in legs],
               # Per-leg odds: the calibration recorder turns these into the
               # book's own implied probabilities (1/odds) when no model
               # probability was recorded - a real expectation instead of the
               # placeholder that fabricated 50% for every leg.
               "leg_odds": [l["odds"] for l in legs],
               # Sport + league per leg: the league-learning tables need to
               # know WHICH competition and WHICH sport each leg came from
               # (slips can now mix sports).
               "legs_meta": [{"sport": l.get("sport") or "Football",
                              "league": l.get("league") or "-",
                              "country": l.get("country") or "",
                              "market": l["market"],
                              "home": l["home"], "away": l["away"]}
                             for l in legs],
               # markets/probs/leg_names are the calibration feed: the legacy
               # recorder (_record_settled_stats) files per-market, per-league
               # and per-team statistics from these. An empty "markets" list is
               # why the live stats file had market_types: {} - the win-sync
               # imported these bets with nothing to learn from.
               "markets": [l["market"] for l in legs],
               "leg_names": [f"{l['home']} vs {l['away']}" for l in legs],
               "status": "active"}
        if all(l.get("prob") is not None for l in legs):
            row["probs"] = [l["prob"] for l in legs]
        if res.get("status") is not None:
            row["http"] = res.get("status")
        if res.get("return_code") is not None:
            row["return_code"] = res.get("return_code")
        if res.get("short_bet_id"):
            row["short_bet_id"] = res["short_bet_id"]
        if res.get("bet_id"):
            row["bet_id"] = res["bet_id"]
        if res.get("possible_win"):
            row["possible_win"] = res["possible_win"]
        if row_unconfirmed:
            # Marked so an auditor can discount it. bets_today() still counts
            # it - the cap must never be optimistic - but it is visibly
            # different from a confirmed bet.
            row["status"] = "unconfirmed"
            row["confirmed_by_balance"] = False
        label = f"  BET PLACED - KES {stake:,.2f} @ x{row['odds']:.2f}"
        if res.get("short_bet_id"):
            label += f" ticket BET:{res['short_bet_id']}"
        if row_unconfirmed:
            label += "  [UNCONFIRMED - balance did not move]"
        log(label)
    else:
        log("  NOT placed")
        if res.get("status"):
            log(f"  the book answered HTTP {res['status']}")
        if res.get("return_code") is not None and res.get("return_code") != 0:
            log(f"  return_code {res['return_code']}: {str(res.get('msgtext'))[:170]}")
    return row


def main() -> int:
    guard = SingleInstance()
    if not guard.acquired():
        log("another BetFlow instance is already running - refusing to start")
        return 1

    cfg = load_settings()
    stake = float(cfg.get("stake", 10.0))
    daily = int(cfg.get("daily_bets", 20))
    headless = bool(cfg.get("headless", True))
    password = cfg.get("password", "")
    accounts = cfg.get("phones") or [cfg.get("phone")]

    # `--visible` runs the browser on screen. Worth testing: headless Chrome can
    # behave differently for overlay hit-testing and for some click handlers,
    # and seeing the real slip is the fastest way to tell whether the PLACE
    # control is enabled and what the page says.
    if "--visible" in sys.argv:
        headless = False
        log("running with a VISIBLE browser (--visible)")
    if "--only" in sys.argv:
        try:
            want = sys.argv[sys.argv.index("--only") + 1]
            accounts = [a for a in accounts if want in str(a)] or [want]
        except Exception:
            pass

    keep_awake()
    log(f"BetFlow starting - stake KES {stake:,.2f}, daily cap {daily}, "
        f"{len(accounts)} account(s), headless={headless}")

    # Each account round re-reads the ledger INSIDE the loop: do_round()
    # writes settlement updates and the zero-stake shadow rows itself, so a
    # single snapshot here would be stale by the time the round's row is
    # appended - and saving that stale copy erased every shadow slip until
    # 2026-10-13. append_ledger_row() does the re-read+append+save instead.

    # ONE FRESH BROWSER PER ACCOUNT.
    #
    # Signing out reliably proved harder than starting clean: the logout control
    # is not a link we can find, and while a previous account stayed signed in
    # the login dialog never mounted, so #secondary_login was null and the second
    # account failed with "Cannot read properties of null". A brand-new browser
    # has no session at all, which removes the whole problem - and since each
    # round is short, the cost is a few seconds.
    for phone in accounts:
        ledger = load_ledger()
        placed_today = bets_today(ledger)
        if placed_today >= daily:
            log(f"daily cap reached ({placed_today}/{daily}) - stopping")
            break
        log(f"--- {phone} ---")
        driver = None
        try:
            driver, _profile = build_driver(headless=headless)
            log("  browser ready (clean session)")
            row = do_round(driver, phone, password, stake)
        except Exception as exc:
            log(f"  round failed: {type(exc).__name__}: {str(exc)[:120]}")
            row = None
        finally:
            if driver is not None:
                try:
                    driver.quit()
                except Exception:
                    pass
        if row and row.get("placed_at"):
            append_ledger_row(row)
        time.sleep(3)

    log("done")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())