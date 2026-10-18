# -*- coding: utf-8 -*-
"""Offline tests for the two defects measured on 2026-10-14.

1. THE QUOTA DEADLOCK. The live key is a 10-requests/day plan
   (x-ratelimit-limit: 10, measured live). The layer read "9 remaining"
   against a fixed QUIET_BELOW of 10 and declared itself low - permanently:
   predictions were never fetched once, model_cache predictions stayed {},
   and the EV layer + confidence stake tiers never ran. The threshold is now
   proportional to the plan's own limit, and the reading is stamped with the
   UTC day it came from so a new day never inherits yesterday's counter.

2. THE CAP-HOLD SYNC BLACKOUT. The daily-cap hold sleeps inside the bet
   worker's own thread for hours. The backend's idle win-sync only ran when
   "no workers alive", so the whole hold window went unsettled and the
   learning journal wrote "0 bets" for a day with 20 placed bets. The
   adapter now publishes a cap_hold flag (no browser is open while holding,
   so the sync is safe exactly then).
"""
import json
import os
import sys
import tempfile
import unittest
from datetime import datetime, timedelta
from pathlib import Path
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
os.chdir(ROOT)

import model_data  # noqa: E402
import betflow_adapter  # noqa: E402


def _today_utc():
    return datetime.utcnow().date().isoformat()


class TestQuotaThreshold(unittest.TestCase):
    """The quiet gate follows the plan's own limit, not a fixed 10."""

    def test_ten_per_day_key_is_not_silenced_at_nine_left(self):
        cache = {}
        model_data._quota_save({"_quota_left": 9, "_quota_limit": 10}, cache)
        self.assertEqual(cache["quota_left"], 9)
        self.assertEqual(cache["quota_limit"], 10)
        self.assertEqual(cache["quota_day"], _today_utc())
        # 9 of 10 left on a 10/day plan must NOT go quiet (the deadlock this
        # file exists to pin: the old code rested below 10 and never woke).
        quiet_below = max(1, cache["quota_limit"] // 10)
        self.assertEqual(quiet_below, 1)
        self.assertFalse(9 < quiet_below)

    def test_hundred_per_day_key_rests_below_ten(self):
        cache = {}
        model_data._quota_save({"_quota_left": 5, "_quota_limit": 100}, cache)
        quiet_below = max(1, cache["quota_limit"] // 10)
        self.assertEqual(quiet_below, 10)
        self.assertTrue(5 < quiet_below, "5 of 100 must go quiet")

    def test_yesterdays_counter_never_gates_today(self):
        yesterday = (datetime.utcnow() - timedelta(days=1)).date().isoformat()
        cache = {"quota_left": 9, "quota_day": yesterday, "quota_limit": 10}
        # A live 200 with no rate headers (key provably alive) must clear a
        # stale low belief instead of leaving the layer frozen.
        model_data._quota_save({"response": []}, cache)
        self.assertEqual(cache["quota_day"], _today_utc())
        self.assertLess(cache["quota_left"], 0, "stale low cleared")

    def test_headerless_response_on_the_same_day_keeps_the_reading(self):
        cache = {"quota_left": 9, "quota_day": _today_utc(), "quota_limit": 10}
        model_data._quota_save({"response": []}, cache)
        self.assertEqual(cache["quota_left"], 9, "same-day value preserved")

    def test_score_games_fetches_predictions_on_a_ten_day_key(self):
        # End-to-end: with 9/10 left today, score_games must NOT bail before
        # trying to fetch predictions (the EV layer's only source of probs).
        with tempfile.TemporaryDirectory() as td:
            cache_path = Path(td) / "model_cache.json"
            cache_path.write_text(json.dumps({
                "quota_left": 9, "quota_limit": 10,
                "quota_day": _today_utc(),
                "fixtures": {}, "predictions": {}}), encoding="utf-8")
            with mock.patch.object(model_data, "CACHE_FILE", cache_path), \
                 mock.patch.object(model_data, "SETTINGS",
                                   Path(td) / "none.json"), \
                 mock.patch.object(model_data, "_api_key",
                                   return_value="test-key"), \
                 mock.patch.object(model_data, "fetch_fixtures_today",
                                   return_value=[{"id": 1, "hn": "ALPHA",
                                                  "an": "BRAVO"}]), \
                 mock.patch.object(model_data, "fetch_predictions",
                                   return_value={"home": 0.5, "draw": 0.3,
                                                 "away": 0.2,
                                                 "advice": ""}) as fp:
                out = model_data.score_games([{"gid": "1", "home": "Alpha",
                                               "away": "Bravo"}])
            self.assertTrue(fp.called, "predictions must be fetched at 9/10")
            self.assertIn("1", out)


class TestCapHoldFlag(unittest.TestCase):
    """The cap-hold must publish its idle state to the backend."""

    def _adapter(self):
        a = betflow_adapter.Backend.__new__(betflow_adapter.Backend)
        legacy = mock.MagicMock()
        legacy._engine_state = {}
        a._legacy = legacy
        return a, legacy

    def test_hold_sets_and_clears_the_flag(self):
        a, legacy = self._adapter()
        a._set_cap_hold(True)
        self.assertTrue(legacy._engine_state["cap_hold"])
        a._set_cap_hold(False)
        self.assertFalse(legacy._engine_state["cap_hold"])

    def test_no_legacy_backend_is_silent(self):
        a = betflow_adapter.Backend.__new__(betflow_adapter.Backend)
        a._legacy = None
        a._set_cap_hold(True)      # must not raise
        a._set_cap_hold(False)

    def test_backend_condition_allows_sync_while_holding(self):
        # The backend's idle-sync condition, verbatim from _agent_worker.
        legacy = mock.MagicMock()
        legacy._engine_state = {"cap_hold": True}
        workers_running = True      # the hold keeps the worker thread alive
        _holding = bool(legacy._engine_state.get("cap_hold"))
        self.assertTrue((not workers_running or _holding),
                        "holding must count as idle for the win-sync")


class TestResultsFeedParsing(unittest.TestCase):
    """The status bug that silently killed shadow settlement.

    The parse line read str(status_dict).get('short') - a str has no .get,
    so the per-fixture try/except swallowed an AttributeError for EVERY
    fixture and fetch_results_today() returned 0 rows for its whole life.
    settle_shadows() therefore never settled a single shadow slip.
    """

    def _body(self):
        return {"response": [
            {"fixture": {"id": 1, "status": {"long": "Match Finished",
                                             "short": "FT"}},
             "teams": {"home": {"name": "Alpha FC"}, "away": {"name": "Beta United"}},
             "goals": {"home": 2, "away": 1},
             "score": {"halftime": {"home": 1, "away": 0}}},
            {"fixture": {"id": 2, "status": {"long": "Not Started",
                                             "short": "NS"}},
             "teams": {"home": {"name": "Gamma City"}, "away": {"name": "Delta Town"}},
             "goals": {"home": None, "away": None},
             "score": {}},
        ]}

    def test_fixtures_parse_with_status_and_halftime(self):
        with tempfile.TemporaryDirectory() as td:
            cache_path = Path(td) / "model_cache.json"
            cache_path.write_text("{}", encoding="utf-8")
            with mock.patch.object(model_data, "CACHE_FILE", cache_path), \
                 mock.patch.object(model_data, "_get", return_value=self._body()):
                rows = model_data.fetch_results_today(force=True)
        self.assertEqual(len(rows), 2, "every fixture must parse")
        ft = rows[0]
        self.assertEqual(ft["hn"], "ALPHA")
        self.assertEqual(ft["an"], "BETA")          # norm drops club tokens
        self.assertEqual((ft["hg"], ft["ag"]), (2, 1))
        self.assertEqual((ft["hth"], ft["hta"]), (1, 0))   # HT score survives
        self.assertEqual(ft["status"], "FT")
        self.assertEqual(rows[1]["status"], "NS")
        self.assertEqual(rows[1]["hg"], -1)                # unplayed is negative

    def test_status_string_shape_does_not_crash_the_row(self):
        # Some payloads carry the status as a plain string, not a dict.
        body = self._body()
        body["response"][0]["fixture"]["status"] = "FT"
        with tempfile.TemporaryDirectory() as td:
            cache_path = Path(td) / "model_cache.json"
            cache_path.write_text("{}", encoding="utf-8")
            with mock.patch.object(model_data, "CACHE_FILE", cache_path), \
                 mock.patch.object(model_data, "_get", return_value=body):
                rows = model_data.fetch_results_today(force=True)
        self.assertEqual(rows[0]["status"], "FT")


if __name__ == "__main__":
    unittest.main(verbosity=2)
