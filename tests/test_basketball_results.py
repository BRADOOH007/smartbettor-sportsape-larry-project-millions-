"""Tests for the basketball results layer (ESPN, free, key-less)."""
import json
import unittest
from unittest import mock

import model_data


class TestBasketballResults(unittest.TestCase):

    def test_fetch_basketball_results_on_never_raises(self):
        with mock.patch("urllib.request.urlopen",
                        side_effect=Exception("no network")), \
             mock.patch("model_data._load_cache", return_value={}):
            rows = model_data.fetch_basketball_results_on("2026-10-17")
        self.assertEqual(rows, [])

    def test_fetch_basketball_results_today_parses_espn_rows(self):
        body = {
            "events": [{
                "status": {"type": {"name": "STATUS_FINAL"}},
                "competitions": [{
                    "competitors": [
                        {"homeAway": "home", "score": "110",
                         "team": {"displayName": "Foo Phoenix"}},
                        {"homeAway": "away", "score": "98",
                         "team": {"displayName": "Bar Taipans"}},
                    ]
                }]
            }, {
                # not finished -> skipped
                "status": {"type": {"name": "STATUS_IN_PROGRESS"}},
                "competitions": [{"competitors": []}],
            }]
        }
        class _R:
            def __enter__(self): return self
            def __exit__(self, *a): return False
            def read(self): return json.dumps(body).encode()
        with mock.patch("urllib.request.urlopen", return_value=_R()), \
             mock.patch("model_data._load_cache", return_value={}), \
             mock.patch("model_data._save_cache"):
            rows = model_data.fetch_basketball_results_today(force=True)
        self.assertEqual(len(rows), 1)
        r = rows[0]
        self.assertEqual(r["hn"], model_data.norm("Foo Phoenix"))
        self.assertEqual(r["an"], model_data.norm("Bar Taipans"))
        self.assertEqual(r["hg"], 110)
        self.assertEqual(r["ag"], 98)
        self.assertIsNone(r["hth"])
        self.assertEqual(r["_sport"], "basketball")

    def test_fetch_all_results_on_merges_football_and_basketball(self):
        fb = [{"hn": "A", "an": "B", "hg": 2, "ag": 1}]
        bb = [{"hn": "C", "an": "D", "hg": 100, "ag": 90, "_sport": "basketball"}]
        with mock.patch("model_data.fetch_results_on", return_value=fb), \
             mock.patch("model_data.fetch_basketball_results_on", return_value=bb):
            out = model_data.fetch_all_results_on("2026-10-17")
        self.assertEqual(len(out), 2)
        self.assertIn(fb[0], out)
        self.assertIn(bb[0], out)

    def test_fetch_all_results_on_survives_either_side_failing(self):
        with mock.patch("model_data.fetch_results_on", side_effect=Exception("boom")), \
             mock.patch("model_data.fetch_basketball_results_on", return_value=[]):
            self.assertEqual(model_data.fetch_all_results_on("2026-10-17"), [])
        with mock.patch("model_data.fetch_results_on", return_value=[{"hn": "A", "an": "B", "hg": 1, "ag": 0}]), \
             mock.patch("model_data.fetch_basketball_results_on", side_effect=Exception("boom")):
            out = model_data.fetch_all_results_on("2026-10-17")
        self.assertEqual(len(out), 1)


if __name__ == "__main__":
    unittest.main()