# -*- coding: utf-8 -*-
"""Offline wiring harness for the adapter + engine, no browser required.

Covers: routing to do_round, max_bets cap, emergency stop, balance floor,
unreadable-balance abort, daily cap against the PERSISTED ledger, legacy
fallback (including the private _load_ledger pass-through that fixed the
"Win-sync error: _load_ledger"), cadence pacing, and settle_verdict.
"""
import os
import sys
import threading
import time
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
os.chdir(ROOT)

import betflow as new_engine
import betflow_adapter
from betflow_adapter import Backend


class FakeDriver:
    def quit(self):
        pass


def make_backend(calls, real_ledger_rows):
    """Backend armed with stubs; returns (backend, rows)."""

    def fake_build_driver(headless=True, profile=None):
        calls.append("build_driver")
        return FakeDriver(), None

    rows = [dict(r) for r in real_ledger_rows]

    def fake_load_ledger():
        return rows

    def fake_save_ledger(r):
        rows[:] = r

    patch = mock.patch.multiple(
        new_engine,
        build_driver=fake_build_driver,
        read_balance=mock.MagicMock(return_value=100.0),
        do_round=mock.MagicMock(side_effect=lambda d, p, w, s, **kw: {
            "placed_at": new_engine.datetime.now().isoformat(timespec="seconds"),
            "phone": p, "stake": s, "odds": 3.92, "legs": 2,
            "games": ["X vs Y [away]"], "http": 200, "status": "active"}),
        load_ledger=fake_load_ledger,
        save_ledger=fake_save_ledger,
        # bets_today is intentionally NOT patched: it is pure over the rows the
        # test owns, and wrapping it with a passthrough is an infinite loop.
        # idle_research IS stubbed: the pacing loop fires it in a thread, and a
        # real pass falls back to launching a headless Chrome when forebet 403s
        # - that turns the offline harness into a browser test. settle_shadows
        # is stubbed for the same reason (it spends an API-Football call).
        idle_research=mock.MagicMock(return_value={}),
        settle_shadows=mock.MagicMock(return_value=[]),
    )
    patch.start()
    b = Backend()
    b.running = True
    return b, rows


class TestWiring(unittest.TestCase):
    LEGACY_ROWS = [
        {"placed_at": "2026-10-08T09:00:00", "phone": "0798810080",
         "stake": 10.0, "games": ["A vs B [away]"], "status": "active"},
    ]

    def test_places_and_persists(self):
        calls = []
        b, rows = make_backend(calls, self.LEGACY_ROWS)
        try:
            res = b.run_football_bet_schedule(
                "0798810080", "pw", phones=["0798810080"], stake=10.0,
                cadence_seconds=0.5, max_bets=1, daily_bets=20, headless=True)
            self.assertEqual(res["placed"], 1)
            self.assertIn("build_driver", calls)
            self.assertEqual(len(rows), 2)          # persisted straight away
            self.assertEqual(rows[-1]["status"], "active")
        finally:
            mock.patch.stopall()

    def test_max_bets_stops_after_limit(self):
        calls = []
        b, _r = make_backend(calls, self.LEGACY_ROWS)
        try:
            res = b.run_football_bet_schedule(
                "0798810080", "pw", phones=["0798810080", "0706719388"],
                stake=10.0, cadence_seconds=0.5, max_bets=1, daily_bets=20)
            self.assertEqual(res["placed"], 1)
        finally:
            mock.patch.stopall()

    def test_emergency_stop_never_bets(self):
        calls = []
        b, _r = make_backend(calls, self.LEGACY_ROWS)
        stop = threading.Event()
        stop.set()
        try:
            res = b.run_football_bet_schedule(
                "0798810080", "pw", phones=["0798810080"], stake=10.0,
                cadence_seconds=0.5, max_bets=0, daily_bets=20,
                stop_event=stop)
            self.assertEqual(res["placed"], 0)
            self.assertNotIn("build_driver", calls)   # never even started a browser
        finally:
            mock.patch.stopall()

    def test_balance_floor_stands_by_instead_of_stopping(self):
        # MEASURED 2026-10-15: the run used to return {"reason":
        # "balance_floor"} the moment every account was broke - a dead end, so
        # a deposit could never revive the machine without a manual restart.
        # It must stand by and RE-CHECK the balance instead; with the recheck
        # interval zeroed the second check sees the same floor and the STOP
        # event ends the run - no bet, no hard-stop reason.
        calls = []
        notes = []
        b, _r = make_backend(calls, self.LEGACY_ROWS)
        b._legacy = None                      # no live sync from the ticker
        checks = []

        def floors_then_stop(*a, **kw):
            checks.append(1)
            if len(checks) >= 2:              # second balance read: still broke
                b.stop_bet_machine()
            return {"balance_floor": True, "balance": 3.0}

        with mock.patch.object(new_engine, "do_round",
                               mock.MagicMock(side_effect=floors_then_stop)), \
             mock.patch.object(betflow_adapter, "BALANCE_RECHECK_MIN_S", 0), \
             mock.patch.object(betflow_adapter, "BALANCE_RECHECK_MAX_S", 0):
            res = b.run_football_bet_schedule(
                "0798810080", "pw", phones=["0798810080"], stake=10.0,
                cadence_seconds=0.5, max_bets=0, daily_bets=20,
                gui_callback=notes.append)
            self.assertEqual(res["placed"], 0)
            self.assertNotEqual(res.get("reason"), "balance_floor",
                                "a broke account must never hard-stop the run")
            self.assertGreaterEqual(len(checks), 2,
                                    "the balance must be re-checked, not "
                                    "abandoned")
            self.assertTrue(any("standing by" in n for n in notes))
            self.assertTrue(any("re-testing the accounts" in n for n in notes))
        mock.patch.stopall()

    def test_unreadable_balance_cools_down_instead_of_stopping(self):
        # OWNER RULE 2026-10-26 - "do not prevent betting". Three consecutive
        # unreadable rounds used to STOP the machine until a human came back,
        # dead for hours through a stuck challenge (measured 2026-10-24). Now
        # it cools down, keeps cycling, and re-reads the balance every round;
        # with the cooldown zeroed, later rounds still run after the 3
        # strikes, and the stop event (not a hard-stop reason) ends the run.
        # No read, no bet, ever - the floor itself is untouched.
        calls = []
        notes = []
        b, _r = make_backend(calls, self.LEGACY_ROWS)
        b._legacy = None                    # no live sync from the ticker
        round_calls = []

        def unreadable_then_stop(*a, **kw):
            round_calls.append(1)
            if len(round_calls) >= 5:       # two cooldown cycles later
                b.stop_bet_machine()
            return {"unreadable": True}

        with mock.patch.object(new_engine, "do_round",
                               mock.MagicMock(side_effect=unreadable_then_stop)), \
             mock.patch.object(betflow_adapter, "UNREADABLE_COOLDOWN", 0):
            res = b.run_football_bet_schedule(
                "0798810080", "pw", phones=["0798810080"], stake=10.0,
                cadence_seconds=0.5, max_bets=0, daily_bets=20,
                gui_callback=notes.append)
            self.assertEqual(res["placed"], 0)
            self.assertNotIn("reason", res,
                             "an unreadable balance must never hard-stop "
                             "the machine anymore")
            self.assertGreaterEqual(len(round_calls), 5,
                                    "the engine must keep re-testing after "
                                    "the 3 strikes, not stop")
            self.assertTrue(
                any("cooling down" in n for n in notes),
                "the cooldown must be announced; got: " + " | ".join(notes))
        mock.patch.stopall()

    def test_deposit_in_progress_skips_account_but_bets_others(self):
        calls = []
        notes = []
        b, rows = make_backend(calls, self.LEGACY_ROWS)

        class _HeldLock:                     # a deposit owns 0798810080
            def acquire(self, timeout=0.0):
                return False
            def release(self):
                pass

        held = _HeldLock()
        free = threading.Lock()              # 0706719388 is untouched
        try:
            with mock.patch.object(
                    b._legacy, "_account_session_lock",
                    side_effect=lambda ph: held if str(ph) == "0798810080"
                    else free):
                res = b.run_football_bet_schedule(
                    "0798810080", "pw", phones=["0798810080", "0706719388"],
                    stake=10.0, cadence_seconds=0.5, max_bets=1, daily_bets=20,
                    gui_callback=notes.append)
            self.assertEqual(res["placed"], 1)   # only the free account bet
            self.assertEqual(calls.count("build_driver"), 1)
            self.assertTrue(any("deposit in progress" in n for n in notes),
                            "the held account must be skipped, not raced")
        finally:
            mock.patch.stopall()
            try:
                held.release()
            except Exception:
                pass

    def test_daily_cap_reads_persisted_ledger(self):
        rows = {"placed_at": new_engine.datetime.now().isoformat(
                    timespec="seconds"), "phone": "0798810080", "stake": 10.0,
                "games": []}                    # today's row: cap already used
        calls = []
        b, _r = make_backend(calls, [rows, rows])

        class _StopOnHold:
            """STOP the instant the machine announces it is holding for the
            new betting day - a spent cap must park the machine, never kill
            it, but a test must not actually wait until midnight."""
            def __init__(self):
                self.hold = False

            def is_set(self):
                return self.hold

            def set(self):
                self.hold = True

        stopper = _StopOnHold()
        notes = []

        def note(m):
            notes.append(m)
            if "holding until the new betting day" in str(m):
                stopper.set()

        try:
            res = b.run_football_bet_schedule(
                "0798810080", "pw", phones=["0798810080"], stake=10.0,
                cadence_seconds=0.5, max_bets=0, daily_bets=2,
                stop_event=stopper, gui_callback=note)
            self.assertEqual(res["placed"], 0)
            self.assertNotIn("build_driver", calls)
            self.assertTrue(any("waiting for the new betting day" in n
                                for n in notes))
        finally:
            mock.patch.stopall()

    def test_ignored_settings_are_said_not_silent(self):
        b, _r = make_backend([], self.LEGACY_ROWS)
        notes = []
        try:
            b.run_football_bet_schedule(
                "0798810080", "pw", phones=["0798810080"], stake=10.0,
                cadence_seconds=0.5, max_bets=1, daily_bets=20,
                gui_callback=notes.append, longshot=True,
                cashout_enabled=True, auto_withdraw=True)
            self.assertTrue(any("NOT HONOURED" in n for n in notes))
        finally:
            mock.patch.stopall()

    def test_legacy_fallback_and_constants(self):
        b = Backend()
        self.assertEqual(b.TODAY_GAMES_PAGE_URL, new_engine.TODAY_URL)
        # Unknown names must NOT raise AttributeError out of the GUI threads.
        self.assertIsNone(b.definitely_not_a_real_method("x"))
        b.stop_bet_machine()          # no-op-safe too
        self.assertFalse(b.running)

    def test_legacy_private_api_reaches_legacy_backend(self):
        # The GUI calls backend._load_ledger() and reads backend._bets directly.
        # The adapter used to reject every underscore name, which spat
        # "Win-sync error: _load_ledger" into the log (that exact string IS the
        # AttributeError("_load_ledger") raised here, not by the legacy code).
        # Private names that EXIST on the legacy backend must pass through;
        # only genuinely unknown private names may raise.
        b = Backend()
        self.assertIsNotNone(b._legacy, "legacy backend must be importable")
        try:
            b._load_ledger()                  # must not raise
        except Exception as e:
            self.fail(f"_load_ledger() raised {type(e).__name__}: {e}")
        self.assertIsInstance(getattr(b, "_bets", None), list)
        with self.assertRaises(AttributeError):
            b._no_such_private_method

    def test_cadence_is_honoured_not_halved(self):
        # Old code slept cadence//10 capped to 60s, so a 600s setting ran as
        # 60s. The adapter must sleep in small slices summing to the real value.
        b, _r = make_backend([], self.LEGACY_ROWS)
        calls = []
        real_sleep = time.sleep

        def spy_sleep(seconds):
            calls.append(seconds)
            real_sleep(min(seconds, 0.01))      # don't actually wait

        stop = threading.Event()

        def late_stop():
            start = time.time()
            while not stop.is_set() and time.time() - start < 2.0:
                wait_until = time.time() + 0.2
                while time.time() < wait_until:
                    real_sleep(0.01)
            stop.set()

        with mock.patch.object(time, "sleep", spy_sleep):
            t = threading.Thread(target=late_stop)
            t.start()
            b.run_football_bet_schedule(
                "0798810080", "pw", phones=["0798810080"], stake=10.0,
                cadence_seconds=600.0, max_bets=0, daily_bets=20,
                stop_event=stop)
            t.join()
        self.assertTrue(calls, "expected paced sleeps")
        self.assertLessEqual(max(calls), 5.0, "slices must be <= 5s")
        total = sum(calls)
        self.assertGreater(total, 300.0, f"cadence not honoured: slept {total:.1f}s")
        mock.patch.stopall()


class TestSettleVerdict(unittest.TestCase):
    def test_money_moved_is_confirmed(self):
        self.assertEqual(new_engine.settle_verdict(100.0, 90.0, {}),
                         (True, False))

    def test_slip_empty_without_move_is_suspicious(self):
        self.assertEqual(
            new_engine.settle_verdict(100.0, 100.0, {"count_after": 0}),
            (True, True))

    def test_http_ok_without_move_is_suspicious(self):
        self.assertEqual(
            new_engine.settle_verdict(100.0, 100.0, {"status": "200"}),
            (True, True))

    def test_nothing_corroborates_is_not_placed(self):
        self.assertEqual(
            new_engine.settle_verdict(100.0, 100.0, {"count_after": 2}),
            (False, False))

    def test_malformed_status_does_not_crash(self):
        self.assertEqual(
            new_engine.settle_verdict(100.0, 100.0, {"status": "abc",
                                                     "count_after": 1}),
            (False, False))

    def test_unreadable_balance_is_not_placed(self):
        self.assertEqual(new_engine.settle_verdict(None, None, {}),
                         (False, False))

    def test_unreadable_but_slip_empty_is_suspicious(self):
        self.assertEqual(
            new_engine.settle_verdict(None, None, {"count_after": 0}),
            (True, True))


class TestLedgerLocation(unittest.TestCase):
    def test_ledger_resolves_to_one_shared_file(self):
        p = new_engine.LEDGER
        self.assertTrue(str(p).lower().endswith("betflow_ledger.json"))
        self.assertTrue(p.exists(), f"canonical ledger missing: {p}")
        # THE fix: a source run and the exe must read THE SAME file.
        self.assertEqual(
            str(p).lower(),
            r"c:\users\administrator\desktop\betflow_ledger.json".lower())
        rows = new_engine.load_ledger()
        # Real rows carry a stake > 0; a shadow research row carries stake 0
        # by definition (zero-stake slip, phone "shadow") - complete, just
        # free. Settled shadows keep stake 0 but gain a won/lost status.
        def _complete(r):
            if not (isinstance(r, dict) and r.get("games") and r.get("phone")):
                return False
            if str(r.get("phone")) == "shadow":
                return True
            if str(r.get("status", "")).startswith("shadow"):
                return True
            return bool(r.get("stake"))
        self.assertTrue(all(_complete(r) for r in rows),
                        "canonical ledger must have complete rows")
        self.assertTrue(any(str(r.get("status", "")).startswith("shadow")
                            for r in rows),
                        "shadow rows must be present - they are the learning "
                        "multiplier and were silently erased by the ledger "
                        "clobber until 2026-10-13")


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)