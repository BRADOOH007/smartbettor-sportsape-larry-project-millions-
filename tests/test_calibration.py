# -*- coding: utf-8 -*-
"""Offline tests for the calibration feed the owner asked for:

  1. the startup reaper is SCOPED to this tool's browsers - a blanket
     chrome kill used to close the operator's own browser;
  2. the odds-band recipe veto uses the SAME band bins as the legacy
     recorder (otherwise the keys never match and nothing ever vetoes);
  3. settled bets file a per-team x market P&L ledger (team_stats);
  4. the win-sync import carries markets/probs/games over from the new
     engine's ledger instead of writing empty lists.
"""
import json
import os
import sys
import tempfile
import threading
import time
import unittest
from datetime import datetime
from pathlib import Path
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
os.chdir(ROOT)

import betflow as new_engine
from sportsape_backend import SportsapeBackend


class TestReaperScoped(unittest.TestCase):
    """The startup sweep must kill OUR browsers only."""

    def setUp(self):
        self.calls = []

        def fake_run(cmd, **kw):
            self.calls.append(cmd)

            class _R:
                stdout = "0"
                stderr = ""
            return _R()

        self._p = mock.patch("subprocess.run", fake_run)
        self._p.start()

    def tearDown(self):
        self._p.stop()

    def test_reaper_targets_only_our_profiles(self):
        new_engine.reap_orphans(300)
        cmd = "\n".join(" ".join(str(x) for x in c) for c in self.calls)
        self.assertIn("betflow_chrome_", cmd,
                      "chrome must be matched on the throwaway profile marker")
        self.assertIn("sportsape_chrome_", cmd)
        self.assertIn("ParentProcessId", cmd,
                      "chromedriver must be matched by parent, not by name")
        self.assertNotIn("Get-Process chromedriver,chrome", cmd,
                         "a blanket Get-Process chrome kill closes the "
                         "operator's own browser - this was the live bug")
        self.assertIn(str(os.getpid()), cmd)

    def test_reaper_swallows_failures(self):
        # A reaper crash must never break a driver build (it runs inside one).
        self._p.stop()
        with mock.patch("subprocess.run",
                        side_effect=OSError("powershell missing")):
            self.assertEqual(new_engine.reap_orphans(300), 0)
        self._p.start()


class TestDriverReaperNeverTakesOthersBrowser(unittest.TestCase):
    """Owner requirement 2026-10-16: closing/restarting this tool must not
    alter the user's browser.

    Every chromedriver on the box runs from the SAME selenium cache, so the exe
    path cannot tell ours from theirs. The old rule spared only drivers owning
    chrome children that carried OUR profile marker - a driver attached to
    somebody else's browser matched none of them, so after 180s it was killed
    out from under them. Use is the only honest discriminator.
    """

    CHROME_MARKED = None  # filled per test

    def _backend(self):
        b = SportsapeBackend.__new__(SportsapeBackend)
        b._worker_drivers = {}
        return b

    def _run(self, backend, probe_rows, taskkill_cmds):
        import json
        raw = json.dumps(probe_rows)

        def fake_run(cmd, *a, **kw):
            class _R:
                stdout = raw if isinstance(cmd, str) else ""
                stderr = ""
                returncode = 0

            if not isinstance(cmd, str):
                taskkill_cmds.append(cmd)
            return _R()

        with mock.patch("subprocess.run", fake_run), \
             mock.patch.object(SportsapeBackend, "_proc_creation_epoch",
                               return_value=0), \
             mock.patch.object(SportsapeBackend, "_emit_direct"):
            return backend._reap_stale_chromedrivers()

    def test_driver_with_a_live_browser_is_spared(self):
        # A foreign browser (NO our-marker in its command line) hangs off a
        # driver from the selenium cache: it must never be reaped.
        rows = [
            {"Name": "chromedriver.exe", "ProcessId": 100,
             "ParentProcessId": 50,
             "ExecutablePath": r"C:\Users\me\.cache\selenium\chromedriver"
                               r"\win64\155.0.8059.84\chromedriver.exe"},
            {"Name": "chrome.exe", "ProcessId": 200, "ParentProcessId": 100,
             "CommandLine": r"chrome.exe --user-data-dir=C:\Users\me\projects"
                            r"\myapp-selenium"},
        ]
        killed = []
        out = self._run(self._backend(), rows, killed)
        self.assertEqual(killed, [],
                         "a driver attached to a live browser is in use")
        self.assertIn(100, out.get("live") or [])

    def test_childless_driver_is_still_reaped(self):
        # The leak this reaper exists for: a driver whose browser is gone.
        rows = [
            {"Name": "chromedriver.exe", "ProcessId": 100,
             "ParentProcessId": 50,
             "ExecutablePath": r"C:\Users\me\.cache\selenium\chromedriver"
                               r"\win64\155.0.8059.84\chromedriver.exe"},
        ]
        killed = []
        out = self._run(self._backend(), rows, killed)
        self.assertEqual(len(killed), 1, "an idle orphan must still be reaped")
        self.assertEqual(out.get("killed"), 1)

    def test_driver_with_our_marker_browser_is_always_live(self):
        rows = [
            {"Name": "chromedriver.exe", "ProcessId": 100,
             "ParentProcessId": 50,
             "ExecutablePath": r"C:\Users\me\.cache\selenium\chromedriver"
                               r"\win64\155.0.8059.84\chromedriver.exe"},
            {"Name": "chrome.exe", "ProcessId": 300, "ParentProcessId": 100,
             "CommandLine": r"chrome.exe --user-data-dir=C:\Temp"
                            r"\sportsape_chrome_0798810080_x"},
        ]
        killed = []
        out = self._run(self._backend(), rows, killed)
        self.assertEqual(killed, [])
        self.assertIn(100, out.get("live") or [])


class TestRecipeVeto(unittest.TestCase):
    def test_bands_match_legacy_recorder(self):
        # betflow._band_of vs SportsapeBackend._band_of - a mismatch means the
        # veto key never matches the recipe table and the gate never fires.
        for o in (0, 1.12, 2.99, 3.0, 3.5, 4.0, 4.01, 5.0, 5.01, 6.0, 6.01, 60):
            self.assertEqual(new_engine._band_of(o),
                             SportsapeBackend._band_of(o), f"band mismatch @ {o}")

    def test_veto_loads_only_proven_losers(self):
        with tempfile.TemporaryDirectory() as td:
            (Path(td) / "sportsape_stats.json").write_text(json.dumps({
                "recipes": {
                    # 20 real bets, -50% ROI -> veto
                    "2L@lt3": {"trials": 20, "stake": 200.0, "ret": 100.0},
                    # 20 real bets, -10% ROI -> not bad enough
                    "2L@3-4": {"trials": 20, "stake": 200.0, "ret": 180.0},
                    # -100% ROI but only 5 bets -> sample too thin
                    "3L@lt3": {"trials": 5, "stake": 50.0, "ret": 0.0},
                    # stake<=0 means shadow/research rows are ignored
                    "4L@gt6": {"trials": 50, "stake": 0.0, "ret": 0.0},
                }}), encoding="utf-8")
            with mock.patch.object(new_engine, "LIVE", Path(td)):
                v = new_engine.load_vetoed_recipes()
        self.assertIn("2L@lt3", v)
        self.assertEqual(v["2L@lt3"]["trials"], 20)
        self.assertNotIn("2L@3-4", v)
        self.assertNotIn("3L@lt3", v)
        self.assertNotIn("4L@gt6", v)

    def test_veto_is_silent_without_evidence(self):
        with tempfile.TemporaryDirectory() as td:
            with mock.patch.object(new_engine, "LIVE", Path(td)):
                self.assertEqual(new_engine.load_vetoed_recipes(), {})
            (Path(td) / "sportsape_stats.json").write_text("{ broken",
                                                            encoding="utf-8")
            with mock.patch.object(new_engine, "LIVE", Path(td)):
                self.assertEqual(new_engine.load_vetoed_recipes(), {})


class TestTeamStats(unittest.TestCase):
    """Per-team money + the REAL per-leg outcome.

    Since 2026-10-15 the recorder decides each leg from the day's final
    scores (the old partial-credit scheme fabricated a ~70% hit rate for
    every market), so every test below patches the results feed with the
    fixture it describes - exactly like the live path.
    """

    def _recorder(self):
        b = SportsapeBackend.__new__(SportsapeBackend)   # no heavy __init__
        b._stats = {"market_types": {}, "recipes": {}, "retired_markets": [],
                    "team_stats": {}, "settled": 0, "last_recalib": None}
        b._stats_cache_time = time.time()
        b._agent_hub = None
        b._gui_lock = threading.Lock()
        b._bets = []
        b._maybe_recalibrate = lambda: None
        b._save_stats = lambda: None
        b._sb_push_settled_results = lambda *a, **k: None
        return b

    def _results(self, *rows):
        # rows: (home_norm, away_norm, hg, ag, hth, hta)
        return [{"hn": h, "an": a, "hg": hg, "ag": ag,
                 "hth": hth, "hta": hta} for h, a, hg, ag, hth, hta in rows]

    def test_lost_slip_files_real_team_records(self):
        # Alpha 2-1 -> over25 WON; Gamma 1-0 -> btts LOST. A lost slip now
        # records each leg's real outcome: the winning leg still counts, the
        # losing one does not (the old code credited BOTH with 0.5).
        res = self._results(("ALPHA", "BETA", 2, 1, 1, 0),
                            ("GAMMACITY", "DELTATOWN", 1, 0, 0, 0))
        with mock.patch("model_data.fetch_all_results_on", return_value=res):
            b = self._recorder()
            b._record_settled_stats({
                "status": "lost", "stake": 10.0, "won_amount": None,
                "markets": ["over25", "btts"], "probs": [0.8, 0.8],
                "games": ["Alpha FC vs Beta United [over25]",
                          "Gamma City vs Delta Town [btts]"]})
        ts = b._stats["team_stats"]
        self.assertIn("Alpha FC", ts)
        e = ts["Alpha FC"]["over25"]
        self.assertEqual(e["trials"], 1)
        self.assertAlmostEqual(e["won"], 1.0)          # the leg really won
        self.assertAlmostEqual(e["expected"], 0.8)
        self.assertAlmostEqual(e["stake"], 5.0)      # even share of the stake
        self.assertAlmostEqual(e["ret"], 0.0)         # lost slip returns nothing
        self.assertAlmostEqual(ts["Beta United"]["over25"]["won"], 1.0)
        self.assertAlmostEqual(ts["Gamma City"]["btts"]["won"], 0.0)
        self.assertEqual(b._stats["settled_real"], 1)

    def test_won_slip_files_money(self):
        res = self._results(("ALPHA", "BETA", 2, 1, 1, 0))
        with mock.patch("model_data.fetch_all_results_on", return_value=res):
            b = self._recorder()
            b._record_settled_stats({
                "status": "won", "stake": 10.0, "won_amount": 27.0,
                "markets": ["over25"], "probs": [0.9],
                "games": ["Alpha FC vs Beta United [over25]"]})
        e = b._stats["team_stats"]["Alpha FC"]["over25"]
        self.assertAlmostEqual(e["won"], 1.0)
        self.assertAlmostEqual(e["stake"], 10.0)
        self.assertAlmostEqual(e["ret"], 27.0)
        # ROI at team level: +170%
        self.assertAlmostEqual((e["ret"] - e["stake"]) / e["stake"], 1.7)

    def test_market_parsed_from_game_tag_when_missing(self):
        res = self._results(("ALPHA", "BETA", 2, 1, 1, 0))
        with mock.patch("model_data.fetch_all_results_on", return_value=res):
            b = self._recorder()
            b._record_settled_stats({
                "status": "lost", "stake": 12.0, "won_amount": None,
                "probs": [0.7],
                "games": ["Alpha FC vs Beta United [dnb_home]"]})
        self.assertIn("dnb_home", b._stats["team_stats"]["Alpha FC"])
        # one leg -> that game carries the whole stake
        self.assertAlmostEqual(
            b._stats["team_stats"]["Alpha FC"]["dnb_home"]["stake"], 12.0)

    def test_legacy_rows_use_leg_names(self):
        res = self._results(("ALPHA", "BETA", 1, 1, 0, 0))
        with mock.patch("model_data.fetch_all_results_on", return_value=res):
            b = self._recorder()
            b._record_settled_stats({
                "status": "lost", "stake": 10.0, "won_amount": None,
                "markets": ["btts"], "probs": [0.5],
                "leg_names": ["Alpha FC vs Beta United"]})
        self.assertIn("btts", b._stats["team_stats"]["Alpha FC"])
        self.assertIn("btts", b._stats["team_stats"]["Beta United"])

    def test_implied_probs_from_leg_odds_when_model_absent(self):
        # Model quota-off rounds record no probs. The recorder must then use
        # the BOOK's implied probabilities (1/leg_odds) - the old 0.5
        # placeholder fabricated a 50% expectation for every leg and made the
        # whole market table read "hit 75% vs priced 50%" for every market.
        res = self._results(("ALPHA", "BETA", 2, 1, 1, 0),
                            ("GAMMACITY", "DELTATOWN", 1, 0, 0, 0))
        with mock.patch("model_data.fetch_all_results_on", return_value=res):
            b = self._recorder()
            b._record_settled_stats({
                "status": "lost", "stake": 10.0, "won_amount": None,
                "markets": ["over25", "btts"], "leg_odds": [1.5, 4.0],
                "games": ["Alpha FC vs Beta United [over25]",
                          "Gamma City vs Delta Town [btts]"]})
        mt = b._stats["market_types"]
        self.assertAlmostEqual(mt["over25"]["expected"], 1.0 / 1.5, places=3)
        self.assertAlmostEqual(mt["btts"]["expected"], 0.25, places=3)
        # real outcomes: over25 (3 goals) won, btts (1-0) lost
        self.assertAlmostEqual(mt["over25"]["won"], 1.0)
        self.assertAlmostEqual(mt["btts"]["won"], 0.0)


class TestImportEnrichment(unittest.TestCase):
    def test_import_copies_engine_ledger_fields(self):
        b = SportsapeBackend.__new__(SportsapeBackend)
        with tempfile.TemporaryDirectory() as td:
            (Path(td) / "betflow_ledger.json").write_text(json.dumps([
                {"bet_id": 14361434286, "short_bet_id": 4161,
                 "markets": ["over25", "btts"], "probs": [0.71, 0.62],
                 "games": ["FC Tokyo vs Urawa [over25]", "Sangju vs Anyang [btts]"],
                 "leg_names": ["FC Tokyo vs Urawa", "Sangju vs Anyang"],
                 "leg_odds": [1.80, 1.90],
                 "legs_meta": [{"sport": "Football", "league": "J1 League",
                                "market": "over25"},
                               {"sport": "Football", "league": "K League 1",
                                "market": "btts"}],
                 "status": "active"}]), encoding="utf-8")
            with mock.patch("sportsape_backend.writable_path",
                            lambda name: str(Path(td) / name)):
                got = b._new_engine_enrich("4161")      # site short id
                self.assertEqual(got["markets"], ["over25", "btts"])
                self.assertEqual(got["probs"], [0.71, 0.62])
                self.assertEqual(got["leg_names"][0], "FC Tokyo vs Urawa")
                self.assertEqual(got["leg_odds"], [1.80, 1.90])
                self.assertEqual(got["legs_meta"][0]["league"], "J1 League")
                self.assertEqual(b._new_engine_enrich("999"), {})  # unknown id

    def test_league_learning_uses_the_real_league(self):
        # With legs_meta present the recorder must file under the REAL
        # league, not the "Unknown" guess from a team name.
        b = SportsapeBackend.__new__(SportsapeBackend)
        b._stats = {"market_types": {}, "recipes": {}, "retired_markets": [],
                    "league_markets": {}, "team_stats": {}, "settled": 0,
                    "last_recalib": None}
        b._stats_cache_time = __import__("time").time()
        b._agent_hub = None
        b._gui_lock = __import__("threading").Lock()
        b._bets = []
        b._maybe_recalibrate = lambda: None
        b._save_stats = lambda: None
        b._sb_push_settled_stats = lambda *a, **k: None
        res = [{"hn": "TOKYO", "an": "URAWA", "hg": 2, "ag": 1,
                "hth": 1, "hta": 0}]
        with mock.patch("model_data.fetch_all_results_on", return_value=res):
            b._record_settled_stats({
                "status": "lost", "stake": 10.0, "won_amount": None,
                "markets": ["over25"], "probs": [0.7], "leg_odds": [1.8],
                "games": ["FC Tokyo vs Urawa [over25]"],
                "legs_meta": [{"sport": "Football", "league": "J1 League",
                               "market": "over25"}]})
        self.assertIn("Football: J1 League",
                      b._stats["league_markets"],
                      "legs_meta must name the real league")

    def test_enrichment_survives_a_missing_ledger(self):
        b = SportsapeBackend.__new__(SportsapeBackend)
        with tempfile.TemporaryDirectory() as td:
            with mock.patch("sportsape_backend.writable_path",
                            lambda name: str(Path(td) / name)):
                self.assertEqual(b._new_engine_enrich("4161"), {})


class TestIdleResearch(unittest.TestCase):
    """The pacing-gap research must be best-effort: feed failures are
    reported, never raised - research cannot break a betting round. Stubs the
    flashscore browser pass (a real one loads pages for every pairing)."""

    def test_feed_failures_are_contained(self):
        with mock.patch("flashscore_cache.refresh",
                        side_effect=OSError("net down")), \
             mock.patch("model_data.fetch_fixtures_today", return_value=[]):
            r = new_engine.idle_research()
        self.assertEqual(r["flashscore"], 0)
        self.assertEqual(r["fixtures"], 0)
        self.assertTrue(r.get("flashscore_error"))

    def test_model_failure_is_contained(self):
        with mock.patch("flashscore_cache.refresh", return_value={}), \
             mock.patch("model_data.fetch_fixtures_today",
                        side_effect=OSError("api down")):
            r = new_engine.idle_research()
        self.assertEqual(r["fixtures"], 0)
        self.assertTrue(r.get("fixtures_error"))


class TestForebetParser(unittest.TestCase):
    """Forebet redesigned on 2026-10-10: the old <tr> tables became schema.org
    SportsEvent blocks. A parser that silently returns {} disables the whole
    second-opinion gate, so both markups are pinned here."""

    NEW_HTML = (
        '<div itemtype="http://schema.org/SportsEvent">'
        '<span itemprop="homeTeam"><span itemprop="name">Alpha FC</span></span>'
        '<span itemprop="awayTeam"><span itemprop="name">Beta United</span></span>'
        '<div class="fprc"><span class="fpr">48</span><span>27</span>'
        '<span>25</span></div>'
        '<div class="avg_sc tabonly">2.51</div></div>'
        '<div itemtype="http://schema.org/SportsEvent">'
        '<span itemprop="homeTeam"><span itemprop="name">Gamma City</span></span>'
        '<span itemprop="awayTeam"><span itemprop="name">Delta Town</span></span>'
        '<div class="fprc"><span class="fpr">10</span><span>20</span>'
        '<span>70</span></div></div>'
    )

    def test_new_schema_markup_parses(self):
        import forebet_cache as fc
        got = fc.parse(self.NEW_HTML)
        self.assertIn("Alpha FC|Beta United", got)
        self.assertAlmostEqual(got["Alpha FC|Beta United"]["home"], 0.48)
        self.assertAlmostEqual(got["Alpha FC|Beta United"]["draw"], 0.27)
        self.assertAlmostEqual(got["Alpha FC|Beta United"]["away"], 0.25)
        self.assertEqual(got["Alpha FC|Beta United"]["avg_goals"], 2.51)
        self.assertAlmostEqual(got["Gamma City|Delta Town"]["away"], 0.70)

    def test_implausible_and_garbage_return_empty(self):
        import forebet_cache as fc
        self.assertEqual(fc.parse("<html><body>nothing</body></html>"), {})
        bad = ('<div itemtype="http://schema.org/SportsEvent">'
               '<span itemprop="homeTeam"><span itemprop="name">A</span></span>'
               '<span itemprop="awayTeam"><span itemprop="name">B</span></span>'
               '<div class="fprc"><span>40</span><span>40</span>'
               '<span>40</span></div></div>')
        self.assertEqual(fc.parse(bad), {})


class TestBettingDayBoundary(unittest.TestCase):
    """When does the betting day (and so the cap) roll over? Configured via
    betting_reset_hour, default midnight."""

    def test_midnight_boundary(self):
        from datetime import datetime as dt
        with mock.patch.object(new_engine, "betting_day_start_hour",
                               return_value=0):
            self.assertEqual(new_engine._betting_day(dt(2026, 10, 11, 23, 30)),
                             "2026-10-11")
            self.assertEqual(new_engine._betting_day(dt(2026, 10, 11, 0, 5)),
                             "2026-10-11")

    def test_custom_boundary_rolls_early_hours_into_previous_day(self):
        from datetime import datetime as dt
        with mock.patch.object(new_engine, "betting_day_start_hour",
                               return_value=6):
            # 03:00 belongs to the betting day that started at 06:00 yesterday
            self.assertEqual(new_engine._betting_day(dt(2026, 10, 11, 3, 0)),
                             "2026-10-10")
            self.assertEqual(new_engine._betting_day(dt(2026, 10, 11, 6, 0)),
                             "2026-10-11")
            self.assertEqual(new_engine._betting_day(dt(2026, 10, 11, 18, 0)),
                             "2026-10-11")

    def test_bets_today_uses_the_boundary(self):
        with mock.patch.object(new_engine, "betting_day_start_hour",
                               return_value=6), \
             mock.patch.object(new_engine, "_betting_day",
                               return_value="2026-10-10"):
            rows = [{"placed_at": "2026-10-10T23:30:00"},
                    {"placed_at": "2026-10-10T02:00:00"},
                    {"placed_at": "2026-10-09T23:30:00"}]
            self.assertEqual(new_engine.bets_today(rows), 2)


class TestMachineResumesAfterCap(unittest.TestCase):
    """A spent cap must park the machine, not kill it: it waits for the new
    betting day and carries on with no human pressing Start."""

    def test_cap_hit_waits_then_resumes(self):
        import itertools

        from betflow_adapter import Backend
        from tests.test_wiring import make_backend

        calls, notes = [], []
        b, rows = make_backend(calls, [])
        today = new_engine._betting_day()
        rows.append({"placed_at": f"{today}T00:30:00", "phone": "0798810080",
                     "stake": 10.0, "odds": 3.0, "status": "active"})
        try:
            with mock.patch.object(new_engine, "bets_today",
                                   side_effect=[1, 0]), \
                 mock.patch.object(new_engine, "betting_day_start_hour",
                                   return_value=11), \
                 mock.patch("betflow_adapter.datetime") as fake_dt, \
                 mock.patch("betflow_adapter.time.sleep", lambda s: None), \
                 mock.patch("betflow_adapter.time.time",
                            side_effect=itertools.count(step=3600)):
                fake_dt.now.return_value = datetime(2026, 1, 1, 10, 0, 0)
                res = b.run_football_bet_schedule(
                    "0798810080", "pw", phones=["0798810080"], stake=10.0,
                    cadence_seconds=0.5, max_bets=1, daily_bets=1,
                    gui_callback=notes.append)
            self.assertEqual(res["placed"], 1)
            self.assertTrue(any("waiting for the new betting day" in n
                                for n in notes))
            self.assertTrue(any("new betting day - resuming" in n
                                for n in notes),
                            "the machine must resume on its own")
        finally:
            mock.patch.stopall()

    def test_balance_floor_stands_by_and_resumes(self):
        """A broke account must never kill the run.

        Measured 2026-10-15: when EVERY account was under the stake floor the
        worker returned {"reason": "balance_floor"} and never looked again, so
        a deposit could not revive the machine without a manual restart. It
        must stand by, re-read the balances on a randomised timer, and bet
        again the moment funds land.
        """
        import itertools

        from betflow_adapter import Backend
        from tests.test_wiring import make_backend

        calls, notes = [], []
        b, _rows = make_backend(calls, [])
        b._legacy = None                  # no live sync from the idle ticker
        floors = [
            {"balance_floor": True, "balance": 0.34},
            {"placed_at": new_engine.datetime.now().isoformat(
                timespec="seconds"), "phone": "0706719388", "stake": 10.0,
             "odds": 3.92, "legs": 2, "games": ["X vs Y [away]"],
             "http": 200, "status": "active"},
        ]
        try:
            with mock.patch.object(new_engine, "do_round",
                                   side_effect=floors), \
                 mock.patch("betflow_adapter.time.sleep", lambda s: None), \
                 mock.patch("betflow_adapter.time.time",
                            side_effect=itertools.count(step=3600)):
                res = b.run_football_bet_schedule(
                    "0706719388", "pw", phones=["0706719388"], stake=10.0,
                    cadence_seconds=0.5, max_bets=1, daily_bets=20,
                    gui_callback=notes.append)
            self.assertEqual(res["placed"], 1,
                             "the machine must survive the floor and bet again")
            self.assertNotEqual(res.get("reason"), "balance_floor",
                                "a broke account must never hard-stop the run")
            self.assertTrue(any("standing by" in n for n in notes),
                            "the standby must be announced")
            self.assertTrue(any("resumes automatically" in n for n in notes))
            self.assertTrue(any("re-testing the accounts" in n for n in notes),
                            "the balance must actually be re-checked")
        finally:
            mock.patch.stopall()


class TestNightlyLearning(unittest.TestCase):
    """The end-of-day pass must journal what the tool learned: retirements,
    best/worst markets vs their price, team money, and recipe vetoes."""

    def test_journals_the_day(self):
        b = SportsapeBackend.__new__(SportsapeBackend)
        today = new_engine._betting_day()
        b._stats = {
            "market_types": {"over25": {"trials": 10, "won": 7.5,
                                        "expected": 5.0}},
            "recipes": {"2L@lt3": {"trials": 20, "stake": 200.0, "ret": 100.0}},
            "retired_markets": ["over1"],
            "team_stats": {"Alpha FC": {"btts": {"trials": 4, "won": 3.0,
                                                 "expected": 2.0, "stake": 20.0,
                                                 "ret": 50.0}}},
            "settled": 40}
        b._stats_cache_time = time.time()
        b._agent_hub = None
        b._gui_lock = threading.Lock()
        b._bets = [{"placed_at": f"{today}T20:00:00", "stake": 10.0,
                    "status": "lost", "games": []}]
        b._maybe_recalibrate = lambda: None      # stubbed: no real re-draw
        b._save_stats = lambda: None
        notes = []
        with tempfile.TemporaryDirectory() as td:
            with mock.patch("sportsape_backend.writable_path",
                            lambda name: str(Path(td) / name)):
                entry = b.nightly_learning(notes.append)
                journal = Path(td) / "sportsape_learning_journal.json"
                self.assertTrue(journal.exists(), "journal must be written")
                hist = json.loads(journal.read_text(encoding="utf-8"))
                self.assertEqual(len(hist), 1)
        self.assertEqual(entry["bets"], 1)
        self.assertEqual(entry["net"], -10.0)
        self.assertIn("over1", entry["retired_markets"])
        self.assertEqual(entry["markets_best"][0]["market"], "over25")
        self.assertEqual(entry["teams_best"][0]["team"], "Alpha FC")
        self.assertEqual(entry["vetoed_recipes"][0]["recipe"], "2L@lt3")
        self.assertTrue(any("LEARNING" in n for n in notes))

    def test_failure_is_contained(self):
        b = SportsapeBackend.__new__(SportsapeBackend)
        b._gui_lock = threading.Lock()
        b._load_stats = lambda: (_ for _ in ()).throw(OSError("disk gone"))
        entry = b.nightly_learning(lambda m: None)
        self.assertEqual(entry, {})


class TestRealLegAccounting(unittest.TestCase):
    """The 2026-10-15 fix: per-market truth comes from REAL leg outcomes.

    The old partial-credit scheme credited every leg of a lost slip with
    ~0.67 "won", so 40 lost slips made all 17 markets look ~70% accurate
    while the real slip win-rate was 13% - and every steering weight in the
    app (market weights, retirements, league and team vetoes) was learned
    from that fiction.
    """

    def _backend(self):
        import threading
        import time
        b = SportsapeBackend.__new__(SportsapeBackend)
        b._stats = {"market_types": {}, "recipes": {}, "retired_markets": [],
                    "league_markets": {}, "team_stats": {}, "settled": 0,
                    "last_recalib": None}
        b._stats_cache_time = time.time()
        b._agent_hub = None
        b._gui_lock = threading.Lock()
        b._bets = []
        b._maybe_recalibrate = lambda: None
        b._save_stats = lambda: None
        b._sb_push_settled_results = lambda *a, **k: None
        return b

    def test_per_leg_outcomes_are_real_not_fabricated(self):
        b = self._backend()
        results = [
            {"hn": "ALPHA", "an": "BETA", "hg": 2, "ag": 1, "hth": 1, "hta": 0},
            {"hn": "GAMMA", "an": "DELTA", "hg": 2, "ag": 0, "hth": 1, "hta": 0},
        ]
        with mock.patch("model_data.fetch_all_results_on",
                        return_value=results):
            b._record_settled_stats({
                "status": "lost", "stake": 10.0, "won_amount": None,
                "markets": ["ml_home", "dnb_away"],
                "leg_odds": [2.0, 1.5],
                "games": ["Alpha vs Beta [ml_home]", "Gamma vs Delta [dnb_away]"],
                "leg_names": ["Alpha vs Beta", "Gamma vs Delta"],
                "legs_meta": [{"sport": "Football", "league": "Liga Test",
                               "market": "ml_home"},
                              {"sport": "Football", "league": "Liga Test",
                               "market": "dnb_away"}],
            })
        mt = b._stats["market_types"]
        # ml_home: Alpha WON 2-1 -> the leg won; dnb_away: Gamma won 2-0 at
        # home -> the away leg lost. A lost slip must NOT credit either leg.
        self.assertEqual(mt["ml_home"]["trials"], 1)
        self.assertEqual(mt["ml_home"]["won"], 1.0)
        self.assertAlmostEqual(mt["ml_home"]["expected"], 0.5)   # 1/2.0
        self.assertEqual(mt["dnb_away"]["won"], 0.0)
        self.assertAlmostEqual(mt["dnb_away"]["expected"], 0.6667, places=3)  # 1/1.5, rounded to 4dp
        self.assertEqual(mt["dnb_away"]["bad_streak"], 1)
        self.assertEqual(mt["ml_home"]["bad_streak"], 0)

    def test_undecidable_leg_records_no_trial(self):
        b = self._backend()
        with mock.patch("model_data.fetch_all_results_on", return_value=[]):
            b._record_settled_stats({
                "status": "lost", "stake": 10.0, "won_amount": None,
                "markets": ["ht_draw"], "leg_odds": [3.0],
                "games": ["Alpha vs Beta [ht_draw]"],
                "leg_names": ["Alpha vs Beta"],
                "legs_meta": [{"sport": "Football", "league": "Liga Test",
                               "market": "ht_draw"}],
            })
        self.assertEqual(b._stats["market_types"].get("ht_draw", {}).get("trials", 0), 0)
        self.assertEqual(b._stats["league_markets"], {})


if __name__ == "__main__":
    unittest.main(verbosity=2)
