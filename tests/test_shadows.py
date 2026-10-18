# -*- coding: utf-8 -*-
"""Offline tests for shadow (zero-stake research) slips.

The shadow system has one job: multiply the learning sample without risking a
shilling. Two invariants are load-bearing and pinned here:
  * shadows NEVER consume the daily cap and never shrink the real board
  * shadows never pollute the REAL market/team tables - they file separately
"""
import os
import sys
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
os.chdir(ROOT)

import betflow as bf
import model_data
from sportsape_backend import SportsapeBackend


def _norm(name: str) -> str:
    return model_data.norm(name)


class TestHtftLegs(unittest.TestCase):
    """The Half Time/Full Time combos (market 44) decide on BOTH scores.

    A shadow/result row only decides an htft_* leg once the half-time score
    arrives (like the ht_* markets already pin here).
    """

    def test_all_nine_combos_decide_correctly(self):
        # Truth table through every HT x FT pairing.
        cases = [
            # (market, homeFT, awayFT, homeHT, awayHT, expected)
            ("htft_hh", 2, 1, 1, 0, True),    # HT home & FT home
            ("htft_hh", 1, 1, 1, 0, False),   # FT draw kills it
            ("htft_hh", 1, 2, 1, 0, False),   # FT away kills it
            ("htft_hx", 1, 1, 1, 0, True),    # HT home & FT draw
            ("htft_ha", 1, 2, 1, 0, True),    # HT home & FT away (comeback)
            ("htft_xh", 2, 1, 0, 0, True),    # HT draw & FT home
            ("htft_xx", 1, 1, 0, 0, True),    # double draw
            ("htft_xx", 2, 1, 0, 0, False),   # FT home kills it
            ("htft_xa", 1, 2, 0, 0, True),    # HT draw & FT away
            ("htft_ah", 2, 1, 0, 1, True),    # HT away & FT home (turnaround)
            ("htft_ax", 1, 1, 0, 1, True),    # HT away & FT draw
            ("htft_aa", 1, 2, 0, 1, True),    # HT away & FT away
            ("htft_aa", 2, 1, 0, 1, False),   # FT home kills it
        ]
        for m, hg, ag, hth, hta, want in cases:
            got = bf.leg_won(m, hg, ag, hth=hth, hta=hta)
            self.assertEqual(got, want, f"{m} {hg}:{ag} HT {hth}:{hta}")

    def test_undecided_without_halftime_score(self):
        self.assertIsNone(bf.leg_won("htft_hh", 2, 1))
        self.assertIsNone(bf.leg_won("htft_xx", 1, 1, hth=None, hta=None))

    def test_shadow_settles_htft_once_ht_score_arrives(self):
        # A pending shadow with an htft leg must stay pending when only the
        # full-time score is known, then settle when both are.
        from pathlib import Path
        import json
        import tempfile
        rows = [{
            "bet_id": 99, "short_bet_id": 9999, "stake": 0.0,
            "status": "shadow",
            "games": ["FC Alpha vs SC Beta [htft_hh]"],
            "markets": ["htft_hh"], "probs": [0.45], "leg_odds": [2.9],
            "created_at": "2026-10-13T02:00:00",
        }]
        results_no_ht = [{"hn": _norm("FC Alpha"), "an": _norm("SC Beta"),
                          "hg": 2, "ag": 1}]
        results_ht = [{"hn": _norm("FC Alpha"), "an": _norm("SC Beta"),
                       "hg": 2, "ag": 1, "hth": 1, "hta": 0}]
        with tempfile.TemporaryDirectory() as td:
            lp = Path(td) / "betflow_ledger.json"
            lp.write_text(json.dumps(rows), encoding="utf-8")
            with mock.patch("betflow.load_ledger", lambda: rows), \
                 mock.patch("betflow.save_ledger", lambda r: rows) as sv, \
                 mock.patch("model_data.fetch_all_results_on",
                            lambda *a, **k: results_no_ht):
                out = bf.settle_shadows()
                self.assertEqual(out, [], "no HT score yet -> stays pending")
            with mock.patch("betflow.load_ledger", lambda: rows), \
                 mock.patch("betflow.save_ledger", lambda r: rows) as sv, \
                 mock.patch("model_data.fetch_all_results_on",
                            lambda *a, **k: results_ht):
                out = bf.settle_shadows()
                self.assertEqual(len(out), 1)
                self.assertEqual(out[0]["status"], "won")


class TestHtftWiring(unittest.TestCase):
    """Market 44 is a 9-selection grid mapped by NAME, not position."""

    def test_wiring_is_consistent(self):
        self.assertEqual(len(bf.HTFT_CELLS), 9)
        self.assertEqual(len(bf.HTFT_CELLS_52), 9)
        self.assertEqual(bf.MARKET_CELLS[44], bf.HTFT_CELLS_52)
        names = {"hh": "1/1", "hx": "1/X", "ha": "1/2", "xh": "X/1",
                 "xx": "X/X", "xa": "X/2", "ah": "2/1", "ax": "2/X",
                 "aa": "2/2"}
        for label, cell in bf.LEG_KEY.items():
            if not label.startswith("htft_"):
                continue
            idx = int(cell.split("#")[1])
            self.assertIn(label[5:], names)
            self.assertEqual(bf.HTFT_CELLS[idx], names[label[5:]])

    def test_market_param_appends_44(self):
        # /api/available/markets does NOT list id 44; the whitelist must add
        # it so /api/games/markets returns the HTFT cells.
        with mock.patch.object(bf, "_api", return_value="46,52-1.5,43,10,42,328"), \
             mock.patch.object(bf, "_MKT_PARAM_CACHE",
                               {"at": 0.0, "param": None}):
            p = bf._market_param(None)
        self.assertTrue(p.startswith("44,"), f"44 must be FIRST: {p}")
        self.assertIn("46", p)

    def test_parse_htft_cells_by_name(self):
        # Replicate the api_board name-mapping on a shuffled grid: the cells
        # must land by selection NAME regardless of book order.
        odds, sels = {}, {}
        m = {"id": 44, "selections": [
            {"name": "X/X", "odds": 9.0, "id": 701},
            {"name": "1/1", "odds": 3.1, "id": 700},
            {"name": "2/1", "odds": 14.0, "id": 707},
            {"name": "1/X", "odds": 15.0, "id": 702},
            {"name": "X/1", "odds": 12.0, "id": 704},
            {"name": "1/2", "odds": 21.0, "id": 703},
            {"name": "X/2", "odds": 9.5, "id": 706},
            {"name": "2/X", "odds": 16.0, "id": 708},
            {"name": "2/2", "odds": 6.5, "id": 709},
        ]}
        for s in m["selections"]:
            try:
                key = "HTFT#%d" % bf.HTFT_CELLS.index(str(s.get("name")))
            except ValueError:
                continue
            odds[key] = float(str(s["odds"]))
            sels[key] = str(s["id"])
        self.assertEqual(odds["HTFT#0"], 3.1)     # 1/1 even though it was not first
        self.assertEqual(odds["HTFT#4"], 9.0)     # X/X
        self.assertEqual(odds["HTFT#8"], 6.5)     # 2/2
        self.assertEqual(sels["HTFT#4"], "701")


class TestLegScoring(unittest.TestCase):
    """Every market a shadow can use must be decidable from a final score."""

    def test_score_decidable_markets(self):
        # 2-1 home win
        self.assertTrue(bf.leg_won("home", 2, 1))
        self.assertFalse(bf.leg_won("away", 2, 1))
        self.assertFalse(bf.leg_won("draw", 2, 1))
        self.assertTrue(bf.leg_won("over15", 2, 1))
        self.assertTrue(bf.leg_won("over25", 2, 1))
        self.assertTrue(bf.leg_won("btts", 2, 1))
        self.assertFalse(bf.leg_won("btts_no", 2, 1))
        self.assertFalse(bf.leg_won("under", 2, 1))
        self.assertTrue(bf.leg_won("dnb_home", 2, 1))
        self.assertFalse(bf.leg_won("dnb_away", 2, 1))
        # 1-0: exactly one goal
        self.assertFalse(bf.leg_won("over15", 1, 0))    # over 1.5 needs 2 goals
        self.assertFalse(bf.leg_won("over25", 1, 0))
        self.assertTrue(bf.leg_won("under25", 1, 0))
        self.assertTrue(bf.leg_won("btts_no", 1, 0))
        self.assertTrue(bf.leg_won("under", 1, 0))

    def test_pushes_and_undecidable_markets_return_none(self):
        self.assertIsNone(bf.leg_won("dnb_home", 1, 1))   # push
        self.assertIsNone(bf.leg_won("dnb_away", 1, 1))   # push
        self.assertIsNone(bf.leg_won("first_home", 2, 1))  # not score-decidable
        self.assertIsNone(bf.leg_won("first_away", 0, 1))
        # HT markets need the half-time score
        self.assertIsNone(bf.leg_won("ht_draw", 2, 1))

    def test_first_half_markets_use_the_half_time_score(self):
        # FT 2-1, HT 0-0
        self.assertTrue(bf.leg_won("ht_draw", 2, 1, hth=0, hta=0))
        self.assertFalse(bf.leg_won("ht_home", 2, 1, hth=0, hta=0))
        self.assertFalse(bf.leg_won("hfbtts", 2, 1, hth=0, hta=0))
        self.assertTrue(bf.leg_won("hfbtts_no", 2, 1, hth=0, hta=0))
        # FT 2-1, HT 1-0
        self.assertTrue(bf.leg_won("ht_home", 2, 1, hth=1, hta=0))
        self.assertTrue(bf.leg_won("hfbtts", 2, 2, hth=1, hta=1))
        self.assertTrue(bf.leg_won("ht_draw", 3, 3, hth=2, hta=2))

    def test_only_decidable_markets_are_shadowed(self):
        # HT markets ARE shadowable now (the results feed carries the
        # half-time score); first-scorer markets are not.
        self.assertIn("ht_draw", bf.SHADOW_MARKETS)
        self.assertIn("hfbtts", bf.SHADOW_MARKETS)
        self.assertNotIn("first_home", bf.SHADOW_MARKETS)
        self.assertNotIn("first_away", bf.SHADOW_MARKETS)


class TestShadowSettlement(unittest.TestCase):
    ROWS = [{
        "placed_at": "2026-10-11T12:00:00", "phone": "shadow", "stake": 0.0,
        "legs": 2, "odds": 3.2,
        "games": ["Alpha FC vs Beta United [over25]",
                  "Gamma City vs Delta Town [btts]"],
        "leg_odds": [1.8, 1.8], "markets": ["over25", "btts"],
        "status": "shadow"}]

    def _results(self, hg1, ag1, hg2, ag2):
        return [{"hn": _norm("Alpha FC"), "an": _norm("Beta United"),
                 "hg": hg1, "ag": ag1},
                {"hn": _norm("Gamma City"), "an": _norm("Delta Town"),
                 "hg": hg2, "ag": ag2}]

    def test_all_legs_won_settles_won(self):
        import copy
        rows = copy.deepcopy(self.ROWS)
        with mock.patch.object(bf, "save_ledger"), \
             mock.patch("model_data.fetch_all_results_on",
                        return_value=self._results(2, 1, 1, 1)):
            settled = bf.settle_shadows(rows)
        self.assertEqual(len(settled), 1)
        self.assertEqual(settled[0]["status"], "won")

    def test_one_lost_leg_settles_lost(self):
        import copy
        rows = copy.deepcopy(self.ROWS)
        with mock.patch.object(bf, "save_ledger"), \
             mock.patch("model_data.fetch_all_results_on",
                        return_value=self._results(1, 0, 1, 1)):   # no over 2.5
            settled = bf.settle_shadows(rows)
        self.assertEqual(len(settled), 1)
        self.assertEqual(settled[0]["status"], "lost")

    def test_missing_results_leave_the_slip_pending(self):
        import copy
        rows = copy.deepcopy(self.ROWS)
        with mock.patch.object(bf, "save_ledger"), \
             mock.patch("model_data.fetch_all_results_on", return_value=[]):
            self.assertEqual(bf.settle_shadows(rows), [])
        self.assertEqual(rows[0]["status"], "shadow")

    def test_dnb_push_does_not_lose_the_slip(self):
        import copy
        rows = copy.deepcopy(self.ROWS)
        rows[0]["games"][0] = "Alpha FC vs Beta United [dnb_home]"
        rows[0]["markets"][0] = "dnb_home"
        with mock.patch.object(bf, "save_ledger"), \
             mock.patch("model_data.fetch_all_results_on",
                        return_value=self._results(1, 1, 1, 1)):   # draw + btts
            settled = bf.settle_shadows(rows)
        self.assertEqual(len(settled), 1)
        self.assertEqual(settled[0]["status"], "won")   # push + btts won

    def test_real_rows_are_never_touched(self):
        import copy
        rows = copy.deepcopy(self.ROWS)
        rows[0]["status"] = "active"
        with mock.patch("model_data.fetch_all_results_on",
                        return_value=self._results(2, 1, 1, 1)):
            self.assertEqual(bf.settle_shadows(rows), [])
        self.assertEqual(rows[0]["status"], "active")

    def test_scored_against_its_own_day_not_today(self):
        # MEASURED 2026-10-16: a slip placed late on D settles on D+1, and the
        # old code always read TODAY's feed - so every leg came back
        # undecidable and the slip sat pending forever. The slip must be read
        # against the day it was placed.
        import copy
        rows = copy.deepcopy(self.ROWS)
        seen = []

        def feed(day):
            seen.append(day)
            return self._results(2, 1, 1, 1)

        with mock.patch.object(bf, "save_ledger"), \
             mock.patch("model_data.fetch_all_results_on", side_effect=feed):
            settled = bf.settle_shadows(rows)
        self.assertEqual(seen, ["2026-10-11"])
        self.assertEqual(len(settled), 1)

    def test_fuzzy_name_match_settles_a_provider_spelling_difference(self):
        # Flashscore names the club "Pwd SC"; API-Football calls it "PWD
        # Sports". Exact matching threw the leg away; the tolerant matcher
        # must decide it (bangladesh league actuals, 2026-10-16).
        import copy
        rows = copy.deepcopy(self.ROWS)
        rows[0]["games"] = ["Pwd SC vs Mohammedan Sporting Club Dhaka [over25]",
                            "Manchester United vs Liverpool [btts]"]
        rows[0]["markets"] = ["over25", "btts"]
        feed = [{"hn": _norm("PWD Sports"),
                 "an": _norm("Mohammedan Sporting Club Dhaka"),
                 "hg": 3, "ag": 1},
                {"hn": _norm("Manchester United"), "an": _norm("Liverpool"),
                 "hg": 1, "ag": 1}]
        with mock.patch.object(bf, "save_ledger"), \
             mock.patch("model_data.fetch_all_results_on", return_value=feed):
            settled = bf.settle_shadows(rows)
        self.assertEqual(len(settled), 1,
                         "the spelling difference must not block settlement")
        self.assertEqual(settled[0]["status"], "won")

    def test_ambiguous_pairing_is_left_undecided(self):
        # Two feed rows both fuzzily match one leg (two different Gimnasia
        # clubs): guessing would poison the table, so the slip stays pending.
        import copy
        rows = copy.deepcopy(self.ROWS)
        rows[0]["games"] = ["Gimnasia vs River Plate [over25]",
                            "Gamma City vs Delta Town [btts]"]
        rows[0]["markets"] = ["over25", "btts"]
        feed = [{"hn": _norm("Gimnasia L.P."), "an": _norm("River Plate"),
                 "hg": 3, "ag": 0},
                {"hn": _norm("Gimnasia M."), "an": _norm("River Plate"),
                 "hg": 1, "ag": 1},
                {"hn": _norm("Gamma City"), "an": _norm("Delta Town"),
                 "hg": 1, "ag": 1}]
        with mock.patch.object(bf, "save_ledger"), \
             mock.patch("model_data.fetch_all_results_on", return_value=feed):
            self.assertEqual(bf.settle_shadows(rows), [])
        self.assertEqual(rows[0]["status"], "shadow")


class TestLedgerAppend(unittest.TestCase):
    """The 2026-10-13 ledger-clobber regression.

    do_round() writes the ledger itself (settlement updates + zero-stake
    shadow rows) DURING a round, while the caller had taken its snapshot
    BEFORE those writes. Saving that snapshot afterwards wiped the round's
    shadow rows - and could revert settlement statuses. append_ledger_row()
    re-reads before appending, which is what this pins.
    """

    def test_shadow_rows_survive_a_placed_bet_append(self):
        import json
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as td:
            lp = Path(td) / "betflow_ledger.json"
            lp.write_text(json.dumps([
                {"placed_at": "2026-10-12T10:00:00", "phone": "0706719388",
                 "stake": 10.0, "status": "won", "short_bet_id": 101},
                {"placed_at": "2026-10-12T11:00:00", "phone": "0798810080",
                 "stake": 10.0, "status": "active", "short_bet_id": 102}]),
                encoding="utf-8")
            with mock.patch.object(bf, "LEDGER", lp):
                # What do_round saves MID-ROUND: a settled row + two shadows.
                mid = bf.load_ledger()
                mid[1]["status"] = "lost"
                mid.append({"placed_at": "2026-10-13T15:16:00", "phone": "shadow",
                            "stake": 0.0, "status": "shadow",
                            "games": ["A vs B [htft_hh]"]})
                mid.append({"placed_at": "2026-10-13T15:16:00", "phone": "shadow",
                            "stake": 0.0, "status": "shadow",
                            "games": ["C vs D [htft_xx]"]})
                bf.save_ledger(mid)

                # The caller (adapter/main) appends the REAL bet afterwards.
                bf.append_ledger_row(
                    {"placed_at": "2026-10-13T15:46:00", "phone": "0706719388",
                     "stake": 10.0, "status": "active"})

                rows = bf.load_ledger()
            shadows = [r for r in rows if r.get("phone") == "shadow"]
            self.assertEqual(len(shadows), 2,
                             "shadow rows must survive the caller's append")
            self.assertEqual(rows[1]["status"], "lost",
                             "in-round settlement must not be reverted")
            self.assertEqual(rows[-1]["phone"], "0706719388")
            self.assertEqual(len(rows), 5)

    def test_bets_today_counts_machine_and_single_phone(self):
        today = bf._betting_day()
        rows = [
            {"placed_at": f"{today}T10:00:00", "phone": "0706719388",
             "status": "active", "stake": 10},
            {"placed_at": f"{today}T11:00:00", "phone": "0706719388",
             "status": "lost", "stake": 10},
            {"placed_at": f"{today}T12:00:00", "phone": "0798810080",
             "status": "active", "stake": 10},
            # shadow never counts, and yesterday never counts
            {"placed_at": f"{today}T13:00:00", "phone": "shadow",
             "status": "shadow", "stake": 0},
            {"placed_at": "2026-10-12T13:00:00", "phone": "0706719388",
             "status": "active", "stake": 10},
        ]
        self.assertEqual(bf.bets_today(rows), 3)
        self.assertEqual(bf.bets_today(rows, phone="0706719388"), 2)
        self.assertEqual(bf.bets_today(rows, phone="0798810080"), 1)



    def test_shadows_do_not_consume_the_daily_cap(self):
        today = bf._betting_day()
        rows = [{"placed_at": f"{today}T10:00:00", "status": "active"},
                {"placed_at": f"{today}T10:00:00", "status": "shadow",
                 "stake": 0.0}]
        self.assertEqual(bf.bets_today(rows), 1)

    def test_shadows_do_not_shrink_the_real_board(self):
        today = bf._betting_day()
        rows = [{"placed_at": f"{today}T10:00:00", "status": "shadow",
                 "games": ["Alpha FC vs Beta United [over25]"]}]
        self.assertEqual(bf.games_bet_today(rows), set())

    def test_recorder_keeps_shadows_out_of_real_tables(self):
        b = SportsapeBackend.__new__(SportsapeBackend)
        b._stats = {"market_types": {}, "recipes": {}, "retired_markets": [],
                    "team_stats": {}, "settled": 0, "last_recalib": None}
        b._stats_cache_time = __import__("time").time()
        b._agent_hub = None
        b._gui_lock = __import__("threading").Lock()
        b._bets = []
        b._maybe_recalibrate = lambda: None
        b._save_stats = lambda: None
        b._sb_push_settled_results = lambda *a, **k: None
        b._record_settled_stats({
            "status": "lost", "stake": 0.0, "won_amount": None,
            "markets": ["over25"], "leg_odds": [1.8],
            "games": ["Alpha FC vs Beta United [over25]"],
            "leg_names": ["Alpha FC vs Beta United"]})
        self.assertEqual(b._stats["market_types"], {},
                         "shadow legs must not enter the real market table")
        self.assertEqual(b._stats["team_stats"], {})
        self.assertTrue(any(k.startswith("1L@lt3")
                            for k in b._stats["shadow_recipes"]),
                        "shadow shapes must file into shadow_recipes")
        self.assertEqual(b._stats["settled_shadow"], 1)
        self.assertEqual(b._stats.get("settled_real") or 0, 0)


class TestShadowVeto(unittest.TestCase):
    def test_shadow_evidence_vetoes_at_a_much_higher_bar(self):
        import tempfile
        from pathlib import Path
        import json
        with tempfile.TemporaryDirectory() as td:
            (Path(td) / "sportsape_stats.json").write_text(json.dumps({
                # real money: 20 bets at -50% -> vetoed (real evidence)
                "recipes": {"2L@lt3": {"trials": 20, "stake": 200, "ret": 100}},
                # research only: 30 trials at -40% -> vetoed as research
                "shadow_recipes": {"3L@3-4": {"trials": 30, "stake": 300,
                                              "ret": 180}},
                # research only: thin sample -> NOT vetoed
                "shadow_recipes2": {"4L@4-5": {"trials": 5, "stake": 50,
                                               "ret": 10}}}), encoding="utf-8")
            with mock.patch.object(bf, "LIVE", Path(td)):
                v = bf.load_vetoed_recipes()
        self.assertIn("2L@lt3", v)
        self.assertEqual(v["2L@lt3"]["kind"], "real")
        self.assertIn("3L@3-4", v)
        self.assertEqual(v["3L@3-4"]["kind"], "shadow")
        self.assertNotIn("4L@4-5", v)


if __name__ == "__main__":
    unittest.main(verbosity=2)
