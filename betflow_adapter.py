# -*- coding: utf-8 -*-
"""
Adapter that lets the ORIGINAL main_gui.py drive the NEW engine.

WHY
---
The original GUI is good: it has the taskbar icon, the full settings screen, the
terminal pane, the colour rules, all of it. Throwing it away to ship a thin new
window was the wrong call. But it was wired to the old ~17,000-line backend,
which could reach the PLACE step and never finish a bet.

So we keep the GUI and swap only the ENGINE:

  * BETTING  -> betflow.py  (small, fast, completes a round in ~60s)
  * EVERYTHING ELSE (balances, jackpot, bet history, winnings sync, caches)
              -> the original SportsapeBackend, untouched

Anything the GUI asks for that the new engine does not provide falls through to
the old backend, so no feature disappears and nothing raises AttributeError.
"""
from __future__ import annotations

import random
import threading
import time
from datetime import datetime, timedelta

import betflow as new_engine

# When EVERY account is under the stake floor the machine STANDS BY instead
# of stopping, re-reading the balances at a randomised interval in this
# range. Randomised so the re-checks do not march in step with anything else
# on the box; long enough that a broke account is not hammered with logins,
# short enough that a deposit gets picked up promptly. Betting resumes
# automatically the moment an account clears the floor.
BALANCE_RECHECK_MIN_S = 8 * 60
BALANCE_RECHECK_MAX_S = 16 * 60

# How long the machine backs off after three consecutive unreadable-balance
# rounds before re-testing the accounts. A cooldown, not a stop: a stuck
# challenge (Akamai) used to dead-end the whole worker until a human came
# back. Owner rule 2026-10-26 - never prevent betting; the floor itself is
# untouched (no read, no bet, ever).
UNREADABLE_COOLDOWN = 15 * 60

# The original backend, if it can be imported. Optional on purpose: if it is
# broken we still want the GUI to launch and bet.
try:
    from sportsape_backend import SportsapeBackend as _Legacy
    _LEGACY_OK = True
except Exception as _e:                                   # pragma: no cover
    _Legacy = None
    _LEGACY_OK = False
    _LEGACY_ERR = str(_e)[:200]


class Backend:
    """What main_gui.py talks to.

    Presents the same surface the GUI already uses. `run_football_bet_schedule`
    is the one method that genuinely changes hands: everything else is passed
    straight through to the legacy backend.
    """

    # A couple of attributes the GUI reads directly.
    TODAY_GAMES_PAGE_URL = new_engine.TODAY_URL

    def __init__(self, *a, **kw):
        self.running = False
        self._engine_state: dict = {}
        self._balance_cache: dict = {}
        self._used_games: set = set()
        self._agent_hub = None
        self._stop = threading.Event()
        self._gui_stop = self._stop
        self._legacy = _Legacy(*a, **kw) if _LEGACY_OK else None

    # ── the new engine: the actual betting ──────────────────────────────
    def _set_cap_hold(self, on: bool) -> None:
        """Tell the backend whether a worker is only HOLDING (cap-hold).

        The cap-hold sleeps inside this worker thread for hours, so the
        backend's idle win-sync - which only settles when no worker is
        alive - would skip settlement for the whole window (measured
        2026-10-14: zero syncs during an 8-hour hold, and the learning
        journal wrote an empty day). Holding means no browser is open, so
        the sync is safe exactly then. Best-effort: a missing legacy backend
        must never be able to fail a betting round.
        """
        try:
            if self._legacy is not None:
                self._legacy._engine_state["cap_hold"] = bool(on)
        except Exception:
            pass

    def run_football_bet_schedule(self, phone, password, phones=None, stake=10.0,
                                  cadence_seconds=600.0, max_bets=0, daily_bets=20,
                                  stake_percent=0.0, chain_bets=True,
                                  gui_callback=None, stop_event=None, **kwargs):
        """Run betting rounds on the new engine.

        The GUI passes a large argument set describing behaviour the new engine
        does not implement (long-shot, roll-over, auto-withdraw, savings). Those
        are accepted and ignored rather than crashing the GUI. What the new
        engine does do is place a small, correctly-priced accumulator quickly -
        which is the part that was broken.
        """
        say = gui_callback or (lambda *_: None)
        accounts = [str(p) for p in (phones or [phone])]
        self._stop.clear()
        # Honour the GUI's emergency-stop button. Without this the GUI could
        # show "stopping" forever while the new engine kept placing bets.
        self._gui_stop = stop_event if stop_event is not None else self._stop

        say("BetFlow engine v2 engaged (fast path: one board read, place, verify).")
        if not _LEGACY_OK:
            say("note: the legacy backend is unavailable, so balance/history "
                "panels will read empty. Betting is unaffected.")

        # Say plainly, once, which of the settings the GUI offered are not
        # honoured. Silently dropping them is how you end up believing a
        # long-shot ran when nothing of the kind happened.
        _ignored = [k for k in ("longshot", "auto_withdraw", "cashout_enabled",
                                "market_whitelist", "grok_api_key")
                    if kwargs.get(k)]
        if _ignored:
            say(f"NOT HONOURED by this engine (switches are greyed out in "
                f"the GUI): {', '.join(_ignored)}. Betting continues without them.")

        def stopping() -> bool:
            return self._stop.is_set() or (
                self._gui_stop is not None and self._gui_stop.is_set())

        # Idle research: the machine used to sleep through the pacing gaps
        # AND the daily-cap hold doing nothing, while the picker gates on
        # the flashscore H2H evidence and the API-Football model. Refresh
        # them here, in a daemon thread, so the next round picks against
        # today's data. The thread is best-effort by design - a slow or
        # failing feed must never delay, break or fail a betting round.
        # Defined BEFORE the loop so the cap-hold branch can use it too.
        def _idle_research():
            try:
                # Settle yesterday's/this round's shadow research against
                # real final scores, and file them into the legacy shadow
                # tables - the learning multiplier that never risks money.
                settled_rows = []
                try:
                    settled_rows = new_engine.settle_shadows()
                    for row in settled_rows:
                        try:
                            if self._legacy is not None:
                                self._legacy._record_settled_stats(row)
                        except Exception:
                            pass
                except Exception:
                    pass
                if settled_rows:
                    say(f"shadow research: {len(settled_rows)} simulated "
                        f"slip(s) settled from real scores "
                        f"({sum(1 for r in settled_rows if r.get('status') == 'won')} "
                        f"would have won)")
                r = new_engine.idle_research()
                bits = []
                if r.get("flashscore"):
                    bits.append(f"{r['flashscore']} flashscore H2H signal(s)")
                if r.get("fixtures"):
                    bits.append(f"{r['fixtures']} API-Football fixture(s)")
                for err in (r.get("flashscore_error"), r.get("fixtures_error")):
                    if err:
                        bits.append(f"error {err}")
                say("idle research done: "
                    + (", ".join(bits) if bits else "no data returned"))
            except Exception as exc:
                say(f"idle research skipped: {type(exc).__name__}: {exc}")

        def _hold_idle():
            """Idle work DURING the daily-cap hold.

            The hold is hours of nothingness inside this worker thread.
            Measured 2026-10-14: an 8-hour hold with ZERO winnings syncs -
            the backend's idle sync only runs when no worker is alive, and
            this thread was alive the whole hold - so nothing settled and the
            learning journal wrote an empty day. No browser is open while
            holding, so syncing now is safe, and this loop provably runs.
            """
            try:
                if self._legacy is not None:
                    for _acct in accounts:
                        try:
                            self._legacy.sync_winnings_now(_acct, password, say)
                        except Exception:
                            pass
            except Exception:
                pass
            _idle_research()

        def _spawn_idle_research(name: str):
            try:
                threading.Thread(target=_idle_research, name=name,
                                 daemon=True).start()
            except Exception:
                pass

        placed_total = 0
        unreadable = 0
        while self.running and not stopping():
            blocked_this_pass = 0
            placed_this_pass = 0
            cap_reached = False
            for idx, acct in enumerate(accounts):
                if stopping() or not self.running:
                    break
                # max_bets must be checked INSIDE the loop too: the old check
                # only ran after every account, so with two accounts it could
                # place two bets when the user asked for one (caught by the
                # wiring harness, 2026-10-08).
                if max_bets and placed_total >= int(max_bets):
                    break

                # Enforce the cap against the PERSISTED ledger, not a counter in
                # memory. An in-memory counter resets when the app restarts, so
                # a daily cap that resets is no cap at all.
                ledger = new_engine.load_ledger()
                already = new_engine.bets_today(ledger)
                if daily_bets and already >= int(daily_bets):
                    # The cap is per betting DAY, not per app-lifetime. Stopping
                    # the machine here used to leave it dead until a human
                    # pressed Start again - which is how a 24/7 tool spends its
                    # whole evening idle. Hold until the betting day rolls over
                    # (in slices, so STOP stays responsive) and carry on: the
                    # next pass re-counts against the NEW day, so the cap is
                    # honoured exactly as before, just without the babysitting.
                    cap_reached = True
                    say(f"daily cap reached ({already}/{daily_bets}) - "
                        f"waiting for the new betting day.")
                    # The hold below sleeps INSIDE this worker thread - see
                    # _set_cap_hold: without the flag the backend's idle
                    # win-sync skips settlement for the whole window.
                    self._set_cap_hold(True)
                    break
                if already:
                    say(f"bets today: {already}/{daily_bets}")

                # A GUI deposit shares the legacy per-account lock. Hold it for
                # the account's whole round so a deposit waits its turn instead
                # of racing this browser on the same SportPesa account (measured
                # 2026-10-09: deposit + round on one account churned the SPA
                # session and the deposit froze on /en/deposit).
                _lock = None
                if self._legacy is not None:
                    try:
                        _lock = self._legacy._account_session_lock(str(acct))
                        if not _lock.acquire(timeout=120):
                            say(f"deposit in progress on {acct} - leaving it "
                                f"alone this round")
                            continue
                    except Exception:
                        _lock = None
                driver = None
                try:
                    driver, _prof = new_engine.build_driver(
                        headless=bool(kwargs.get("headless", True)))

                    # ── BALANCE FLOOR ──────────────────────────────────────
                    # The machine must never bet blind. do_round() owns the
                    # floor: it navigates + logs in first (so /api/wallets/
                    # balance runs on the right origin with a live session),
                    # then refuses to place when the balance is unreadable or
                    # below the stake, signalling via {"unreadable": True} /
                    # {"balance_floor": True}. A caller-side read used to run
                    # on a fresh about:blank driver, always failed, and stopped
                    # the machine before a single bet (measured 2026-10-09).
                    # Each account drafts from a DIFFERENT market rotation
                    # (account 0 leads DNB, account 1 leads O/U...), so two
                    # accounts never share the same bet profile.
                    row = new_engine.do_round(driver, acct, password, float(stake),
                                              rotation=idx * (len(new_engine.API_PREF) // 2))
                    if isinstance(row, dict) and row.get("unreadable"):
                        # Without a balance we cannot honour the floor, and
                        # betting blind is how a cap gets blown. Fail the round
                        # loudly instead of placing. OWNER RULE 2026-10-26 -
                        # "do not prevent betting": three unreadable rounds used
                        # to STOP the machine until a human came back, dead for
                        # hours (measured through the 2026-10-24 Akamai day).
                        # Now: cooldown instead of stop. The engine keeps
                        # cycling, re-reads every round, skips any account
                        # whose balance stays unreadable, and betting resumes
                        # automatically the moment the challenge clears. The
                        # floor itself is untouched - no read, no bet, ever.
                        unreadable += 1
                        say(f"could not read the balance on {acct} "
                            f"({unreadable}/3) - skipping this round.")
                        if unreadable >= 3:
                            _cool = UNREADABLE_COOLDOWN
                            say("balance unreadable three times in a row - "
                                "cooling down 15 min and retrying instead of "
                                "stopping (resumes betting as soon as the "
                                "challenge clears).")
                            unreadable = 0
                            self._set_cap_hold(True)   # no browser open; lets
                                                       # idle settlement run
                            try:
                                _deadline2 = time.time() + _cool
                                while time.time() < _deadline2 and self.running and not stopping():
                                    time.sleep(5.0)
                            finally:
                                self._set_cap_hold(False)
                        continue
                    unreadable = 0
                    if isinstance(row, dict) and row.get("balance_floor"):
                        bal = row.get("balance", 0)
                        # Per-account, not per-machine: one account being under
                        # the stake floor must not halt betting for the others
                        # (measured 2026-10-09: 0706719388 at KES 7.88 stopped
                        # the whole machine). Skip the account this round and
                        # keep the solvent accounts running. The machine only
                        # stops when EVERY account is blocked.
                        say(f"balance KES {bal:,.2f} on {acct} is below the "
                            f"betting floor KES {new_engine.MIN_FULL_BALANCE_STAKE:,.2f} "
                            f"- skipping this account this round (the balance "
                            f"is re-read every round; betting resumes on it "
                            f"automatically once funds land).")
                        blocked_this_pass += 1
                        continue
                    if row:
                        # Persist immediately. If the app is killed right after a
                        # bet lands, the money is already spent - the ledger has
                        # to know, or the next run bets past the cap.
                        # append_ledger_row RE-READS the file first: do_round()
                        # saved this round's settlement updates + shadow rows
                        # after this loop took its `ledger` snapshot, so a save
                        # of that snapshot would wipe them (measured 2026-10-13).
                        new_engine.append_ledger_row(row)
                        placed_total += 1
                        placed_this_pass += 1
                        # Re-read the ledger for the counts instead of reusing
                        # `already` + placed_total: `already` was computed per
                        # account BEFORE this round, so summing the two would
                        # double-count an earlier account in the same pass.
                        # The CAP is machine-wide (both locked accounts share
                        # it), but the line names one phone - so show that
                        # phone's own count, or "on 0706719388 (19/20)" lies
                        # about a phone that has bet 9 times.
                        rows_now = new_engine.load_ledger()
                        now = new_engine.bets_today(rows_now, phone=acct)
                        across = new_engine.bets_today(rows_now)
                        say(f"BET PLACED - KES {float(stake):,.2f} @ "
                            f"x{row.get('odds', 0):.2f} on {acct} "
                            f"({now} on this phone, {across}/{daily_bets} "
                            f"cap today)")
                except Exception as exc:
                    say(f"round failed: {type(exc).__name__}: {exc}")
                finally:
                    if driver is not None:
                        try:
                            driver.quit()
                        except Exception:
                            pass
                    if _lock is not None:
                        try:
                            _lock.release()
                        except Exception:
                            pass
            if max_bets and placed_total >= int(max_bets):
                break
            # ── Cap reached: hold for the new betting day, then carry on ──
            if cap_reached:
                # The day's betting is done and the machine is about to sit
                # idle for hours. Spend the top of that window LEARNING: force
                # a recalibration over today's settled bets (retirements,
                # signed weight moves, Brier) and write the daily journal.
                # Best-effort - learning must never be able to stall betting.
                if self._legacy is not None:
                    try:
                        self._legacy.nightly_learning(say)
                    except Exception as exc:
                        say(f"learning pass skipped: {type(exc).__name__}: {exc}")
                now = datetime.now()
                reset_h = new_engine.betting_day_start_hour()
                nxt = now.replace(hour=reset_h, minute=0, second=0,
                                  microsecond=0)
                if nxt <= now:
                    nxt += timedelta(days=1)
                wait = max(1.0, (nxt - now).total_seconds())
                say(f"holding until the new betting day at {nxt:%H:%M} "
                    f"({wait / 60:.0f} min) - the daily cap resets then")
                _end = time.time() + wait
                _next_idle = time.time() + 300.0
                while time.time() < _end and not stopping() and self.running:
                    time.sleep(min(30.0, max(1.0, _end - time.time())))
                    # The hold is hours long: settle the day's bets and keep
                    # researching every 5 minutes instead of sleeping through
                    # the window (the empty-journal bug, 2026-10-14). Runs in
                    # daemon threads so STOP stays responsive.
                    if time.time() >= _next_idle:
                        _next_idle = time.time() + 300.0
                        try:
                            threading.Thread(target=_hold_idle,
                                             name="cap-hold-idle",
                                             daemon=True).start()
                        except Exception:
                            pass
                if stopping() or not self.running:
                    break
                self._set_cap_hold(False)
                say("new betting day - resuming betting")
                continue
            # Every account under the stake floor and nothing placed: do NOT
            # stop (the old behaviour was a dead end - the worker returned and
            # never looked again, so a deposit could never revive the machine:
            # measured 2026-10-15, 0706719388 sat at KES 0.34 forever). STAND
            # BY instead and re-read the balances on a randomised timer
            # (BALANCE_RECHECK_MIN_S..MAX_S) until money lands. The moment an
            # account clears the floor, the next pass places its bets again -
            # fully automatic, no restart needed.
            if placed_this_pass == 0 and blocked_this_pass == len(accounts):
                gap = random.uniform(BALANCE_RECHECK_MIN_S,
                                     BALANCE_RECHECK_MAX_S)
                say(f"every account is below the stake floor - standing by, "
                    f"re-checking balances in {gap / 60:.0f} min "
                    f"(randomised); betting resumes automatically once funds "
                    f"land.")
                _end = time.time() + gap
                _next_idle = time.time() + 300.0
                while time.time() < _end and not stopping() and self.running:
                    time.sleep(min(5.0, max(1.0, _end - time.time())))
                    # Standby can stretch for days on a broke account. Keep
                    # settling shadows and refreshing the research feeds every
                    # 5 min (same ticker as the cap-hold) so the learning
                    # never freezes while waiting for a deposit.
                    if time.time() >= _next_idle:
                        _next_idle = time.time() + 300.0
                        try:
                            threading.Thread(target=_hold_idle,
                                             name="balance-standby-idle",
                                             daemon=True).start()
                        except Exception:
                            pass
                if stopping() or not self.running:
                    break
                say("balance check due - re-testing the accounts")
                continue
            # Pace between passes, using the cadence the user actually set.
            # The previous version did cadence_seconds // 10 capped to 60s,
            # so a configured 600s ran as 60s - which is not a slow setting
            # being ignored, it is a fast one being substituted.
            #
            # Sleep against a WALL-CLOCK deadline, not by stacking sleep()
            # calls: Windows pauses sleep() timers while the system is asleep
            # (measured 2026-10-09: the box slept 12 min at 01:05 and the
            # next round came late by exactly that long). time.time() keeps
            # ticking through sleep/resume, so the next pass lands at the
            # intended wall time - or immediately, when the deadline was
            # already past on resume. Slices keep STOP responsive.
            say(f"pacing {cadence_seconds:.0f}s until "
                f"{datetime.now() + timedelta(seconds=cadence_seconds):%H:%M:%S}")
            # Settle shadows + refresh the research feeds in the gap between
            # rounds so the next round picks against today's data.
            _spawn_idle_research("idle-research")
            deadline = time.time() + cadence_seconds
            while True:
                if stopping():
                    break
                remaining = deadline - time.time()
                if remaining <= 0:
                    break
                time.sleep(min(5.0, remaining))
            say("pacing done - next pass")
        return {"placed": placed_total, "stopped": True}

    def stop_bet_machine(self):
        self._stop.set()
        if getattr(self, "_gui_stop", None) is not None:
            self._gui_stop.set()
        self.running = False

    # ── everything else falls through to the legacy backend ─────────────
    def __getattr__(self, name):
        # Private-ish names used BY THE GUI themselves: _load_ledger, _bets,
        # _save_ledger, _ledger_summary... The GUI genuinely calls these (it
        # is the original front-end for the original backend), so they must
        # reach the legacy backend too. This guard used to reject every
        # underscore name, which surfaced in the log as:
        #     [..] Win-sync error: _load_ledger
        # i.e. AttributeError("_load_ledger") raised here, not by the legacy
        # code. The distinction that matters is not underscore vs no-underscore
        # but EXISTS on the legacy backend vs NOT: present names are handed
        # through regardless of underscore; genuinely missing names raise so a
        # bug is never silently swallowed.
        legacy = self.__dict__.get("_legacy")
        if legacy is not None and hasattr(legacy, name):
            return getattr(legacy, name)
        if name.startswith("_"):
            raise AttributeError(name)
        # Unknown on the legacy backend too: return a harmless no-op rather
        # than crash a background thread in the GUI.
        def _noop(*a, **kw):
            return None
        return _noop