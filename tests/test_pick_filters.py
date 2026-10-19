# -*- coding: utf-8 -*-
"""Offline tests for pick_filters - the STEER layer.

The gates consume the learner's output (retired markets, weights, team P&L),
the flashscore head-to-head evidence and the AI analyst. The one property that
matters above all: every gate is fail-safe - a missing file, a stale feed or a
dead AI edge must return the candidates UNTOUCHED, never zero legs.
"""
import os
import sys
import unittest
from pathlib import Path
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
os.chdir(ROOT)

import pick_filters


def _cand(gid, home, away, market, odds):
    return {"gid": gid, "home": home, "away": away,
            "market": market, "odds": odds, "sel_id": 123, "ko": 0, "br": 0}


CANDS = [_cand("1", "Alpha FC", "Beta United", "over25", 1.80),
         _cand("2", "Gamma City", "Delta Town", "btts", 1.75)]


class TestSteerGates(unittest.TestCase):
    def setUp(self):
        # Every apply_gates test runs with the AI call stubbed - otherwise a
        # live key in the settings turns the offline suite into network calls
        # with 40s timeouts. The two AI tests override this.
        self._ai = mock.patch.object(pick_filters, "ai_verdicts",
                                     return_value={})
        self._ai.start()

    def tearDown(self):
        self._ai.stop()

    def _patch_stats(self, stats: dict):
        import tempfile
        d = tempfile.mkdtemp()
        p = Path(d) / "sportsape_stats.json"
        p.write_text(__import__("json").dumps(stats), encoding="utf-8")
        return mock.patch.object(pick_filters, "STATS", p)

    def test_no_learning_data_means_no_change(self):
        with mock.patch.object(pick_filters, "STATS", Path("/nope/missing.json")):
            kept, counts = pick_filters.apply_gates(list(CANDS), log=lambda m: None)
        self.assertEqual(len(kept), 2, "a missing stats file must not drop legs")
        self.assertEqual(counts["retired"], 0)

    def test_retired_markets_are_removed(self):
        with self._patch_stats({"retired_markets": ["over25"],
                                "market_types": {"over25": {"trials": 40,
                                                            "won": 12,
                                                            "expected": 34,
                                                            "weight": 0.5}},
                                "team_stats": {}}):
            kept, counts = pick_filters.apply_gates(list(CANDS), log=lambda m: None)
        markets = [c["market"] for c in kept]
        self.assertNotIn("over25", markets)
        self.assertIn("btts", markets)
        self.assertEqual(counts["retired"], 1)

    def test_team_market_veto_removes_both_sides(self):
        # Alpha FC on over25: 6 trials, stake 60, returned 0 -> vetoed
        stats = {"retired_markets": [], "market_types": {},
                 "team_stats": {"Alpha FC": {"over25": {"trials": 6,
                                                        "won": 2.0,
                                                        "expected": 4.0,
                                                        "stake": 60.0,
                                                        "ret": 0.0}}}}
        with self._patch_stats(stats):
            kept, counts = pick_filters.apply_gates(list(CANDS), log=lambda m: None)
        self.assertNotIn("Alpha FC", [c["home"] for c in kept])
        self.assertEqual(counts["vetoed_teams"], 1)

    def test_thin_team_sample_is_not_vetoed(self):
        stats = {"retired_markets": [], "market_types": {},
                 "team_stats": {"Alpha FC": {"over25": {"trials": 2,
                                                        "stake": 20.0,
                                                        "ret": 0.0}}}}
        with self._patch_stats(stats):
            kept, _ = pick_filters.apply_gates(list(CANDS), log=lambda m: None)
        self.assertEqual(len(kept), 2)

    def test_flashscore_blocks_when_evidence_is_below_the_price(self):
        # H2H says over25 happens 20% of the time; the leg pays 1.80 (implied
        # 56%) -> evidence far below the price -> blocked.
        games = {"Alpha FC|Beta United": {"n": 3, "avg_goals": 2.0,
                                          "over25": 0.2, "over15": 0.8,
                                          "btts": 0.8, "home_win": 0.2,
                                          "draw": 0.8, "away_win": 0.2}}
        with mock.patch.object(pick_filters, "_flash_table", return_value=games):
            kept, counts = pick_filters.apply_gates(list(CANDS), log=lambda m: None)
        markets = [c["market"] for c in kept]
        self.assertNotIn("over25", markets)
        self.assertEqual(counts["flash_blocked"], 1)

    def test_flashscore_keeps_a_well_priced_leg(self):
        games = {"Alpha FC|Beta United": {"n": 4, "avg_goals": 3.2,
                                          "over25": 0.85, "over15": 0.9,
                                          "btts": 0.6}}
        with mock.patch.object(pick_filters, "_flash_table", return_value=games), \
             mock.patch.object(pick_filters, "STATS", Path("/nope/missing.json")):
            kept, counts = pick_filters.apply_gates(list(CANDS), log=lambda m: None)
        self.assertIn("over25", [c["market"] for c in kept])
        self.assertEqual(counts["flash_blocked"], 0)

    def test_no_flashscore_cache_means_no_opinion(self):
        with mock.patch.object(pick_filters, "_flash_table", return_value={}), \
             mock.patch.object(pick_filters, "STATS", Path("/nope/missing.json")):
            kept, counts = pick_filters.apply_gates(list(CANDS), log=lambda m: None)
        self.assertEqual(len(kept), 2)
        self.assertEqual(counts["flash_blocked"], 0)

    def test_ai_failure_is_contained(self):
        # A dead AI edge must not raise, and must not drop legs either.
        with mock.patch.object(pick_filters, "STATS", Path("/nope/missing.json")), \
             mock.patch.object(pick_filters, "_flash_table", return_value={}), \
             mock.patch.object(pick_filters, "ai_verdicts",
                               side_effect=RuntimeError("503 high demand")):
            kept, counts = pick_filters.apply_gates(list(CANDS), log=lambda m: None)
        self.assertEqual(len(kept), 2)
        self.assertEqual(counts["ai_blocked"], 0)

    def test_ai_flags_are_honoured_when_present(self):
        # AI is now ADVISORY ONLY: it flags risky legs but never drops them.
        # The mechanical gates (retired, veto, odds, flashscore, standing,
        # movement) are the real filters; the AI just reports its opinion.
        verdicts = {"1|over25": True, "2|btts": False}
        with mock.patch.object(pick_filters, "STATS", Path("/nope/missing.json")), \
             mock.patch.object(pick_filters, "_flash_table", return_value={}), \
             mock.patch.object(pick_filters, "ai_verdicts", return_value=verdicts):
            kept, counts = pick_filters.apply_gates(list(CANDS), log=lambda m: None)
        self.assertEqual([c["market"] for c in kept], ["over25", "btts"])
        self.assertEqual(counts["ai_blocked"], 0)

    def test_rotation_orders_by_learned_weight(self):
        markets = ["dnb_away", "under", "btts"]
        out = pick_filters.rotation_with_weights(
            markets, {"btts": 1.2, "under": 0.9, "dnb_away": 1.0})
        self.assertEqual(out[0], "btts")            # best weight first
        self.assertEqual(out[-1], "under")
        self.assertEqual(pick_filters.rotation_with_weights(markets, {}), markets)


class TestFlashprob(unittest.TestCase):
    def test_market_mapping(self):
        sig = {"over25": 0.2, "over15": 0.8, "btts": 0.8,
               "home_win": 0.2, "away_win": 0.8, "draw": 0.8}
        with mock.patch.object(pick_filters, "_flash_table",
                               return_value={"A|B": sig}):
            self.assertAlmostEqual(pick_filters.flash_prob("over25", "A", "B"), 0.2)
            self.assertAlmostEqual(pick_filters.flash_prob("under25", "A", "B"), 0.8)
            self.assertAlmostEqual(pick_filters.flash_prob("btts_no", "A", "B"), 0.2)
            self.assertAlmostEqual(pick_filters.flash_prob("away", "A", "B"), 0.8)
            # DNB is deliberately left alone (H2H win share ignores pushes)
            self.assertIsNone(pick_filters.flash_prob("dnb_home", "A", "B"))

    def test_unknown_pairing_is_neutral(self):
        with mock.patch.object(pick_filters, "_flash_table",
                               return_value={"X|Y": {"over25": 0.5}}):
            self.assertIsNone(pick_filters.flash_prob("over25", "A", "B"))


class TestNewsGuard(unittest.TestCase):
    """The 'obvious win' guard: a headline naming an injury/rest/rotation on a
    short-priced leg blocks it."""

    def test_flag_blocks_the_leg(self):
        games = {"Alpha FC|Beta United": {"n": 3, "over25": 0.2, "btts": 0.8,
                                          "news_flags": ["Alpha FC star "
                                                         "striker out injured"]}}
        with mock.patch.object(pick_filters, "_flash_table",
                               return_value=games), \
             mock.patch.object(pick_filters, "STATS", Path("/nope/x.json")):
            kept, counts = pick_filters.apply_gates(
                [_cand("1", "Alpha FC", "Beta United", "over25", 1.80)],
                log=lambda m: None)
        self.assertEqual(kept, [])
        self.assertEqual(counts["news_blocked"], 1)

    def test_no_news_means_no_opinion(self):
        games = {"Alpha FC|Beta United": {"n": 3, "over25": 0.8, "btts": 0.6,
                                          "news": ["routine preview piece"]}}
        with mock.patch.object(pick_filters, "_flash_table",
                               return_value=games), \
             mock.patch.object(pick_filters, "STATS", Path("/nope/x.json")), \
             mock.patch.object(pick_filters, "ai_verdicts", return_value={}):
            kept, counts = pick_filters.apply_gates(
                [_cand("1", "Alpha FC", "Beta United", "over25", 1.80)],
                log=lambda m: None)
        self.assertEqual(len(kept), 1)
        self.assertEqual(counts["news_blocked"], 0)


class TestOddsMovement(unittest.TestCase):
    """The market-consensus gate: when the consensus pays more than our book,
    the leg is underpaid for its risk."""

    def test_rows_are_averaged_across_bookmakers(self):
        import flashscore_cache
        rows = ["Bet365 1.90 3.40 4.20",
                "Unibet 1.88 3.45 4.10",
                "not a price row 42%"]
        o = flashscore_cache.parse_odds_rows(rows)
        self.assertAlmostEqual(o["home"], 1.89, places=2)
        self.assertAlmostEqual(o["draw"], 3.425, places=2)
        self.assertAlmostEqual(o["away"], 4.15, places=2)
        self.assertEqual(o["books"], 2)

    def test_empty_when_nothing_rendered(self):
        import flashscore_cache
        self.assertEqual(flashscore_cache.parse_odds_rows([]), {})
        self.assertEqual(flashscore_cache.parse_odds_rows(["1.90", "Bet365"]), {})

    def test_consensus_above_book_blocks(self):
        sig = {"odds": {"home": 2.00, "draw": 3.40, "away": 4.20}}
        self.assertTrue(pick_filters.odds_underpaid(sig, "home", 1.75))
        self.assertTrue(pick_filters.odds_underpaid(sig, "ml_home", 1.75))

    def test_consensus_at_or_below_book_stands(self):
        sig = {"odds": {"home": 1.60, "draw": 3.40, "away": 4.20}}
        self.assertFalse(pick_filters.odds_underpaid(sig, "home", 1.80))
        self.assertFalse(pick_filters.odds_underpaid(sig, "home", 1.60))

    def test_no_consensus_is_neutral(self):
        self.assertFalse(pick_filters.odds_underpaid({}, "home", 1.75))
        self.assertFalse(pick_filters.odds_underpaid({"odds": {}}, "home", 1.75))
        self.assertFalse(pick_filters.odds_underpaid({"odds": {"home": 1.9}},
                                                     "home", None))


class TestLeagueSteering(unittest.TestCase):
    def _patch_stats(self, stats):
        import tempfile
        from pathlib import Path
        import json
        d = tempfile.mkdtemp()
        p = Path(d) / "sportsape_stats.json"
        p.write_text(json.dumps(stats), encoding="utf-8")
        return mock.patch.object(pick_filters, "STATS", p)

    def test_weights_follow_realized_vs_priced(self):
        stats = {"league_markets": {
            "Football: Premier League": {
                # beats its price: hit 80% vs priced 65% -> boost
                "over25": {"trials": 20, "won": 16.0, "expected": 13.0},
                # misses: hit 40% vs 60% -> weight down
                "btts": {"trials": 20, "won": 8.0, "expected": 12.0},
                # too thin to steer on
                "under": {"trials": 3, "won": 2.0, "expected": 2.0},
            }}}
        with self._patch_stats(stats):
            w = pick_filters.league_weights()
        self.assertGreater(w["Football: Premier League"]["over25"], 1.0)
        self.assertLess(w["Football: Premier League"]["btts"], 1.0)
        self.assertNotIn("under", w["Football: Premier League"])

    def test_no_stats_is_neutral(self):
        with mock.patch.object(pick_filters, "STATS", Path("/nope/x.json")):
            self.assertEqual(pick_filters.league_weights(), {})

    def test_draft_favours_proven_leagues_at_equal_price(self):
        import betflow as bf
        cands = [
            {"gid": "1", "home": "Team A", "away": "Team B", "market": "over25",
             "odds": 1.70, "sel_id": 1, "league": "Football: La Liga"},
            {"gid": "2", "home": "Team C", "away": "Team D", "market": "over25",
             "odds": 1.70, "sel_id": 2, "league": "Football: Faroese"},
        ]
        lw = {"Football: La Liga": {"over25": 1.15},
              "Football: Faroese": {"over25": 0.90}}
        out = bf._draft_legs(cands, ["over25"], want=1, league_w=lw)
        self.assertEqual(out[0]["league"], "Football: La Liga")


if __name__ == "__main__":
    unittest.main(verbosity=2)