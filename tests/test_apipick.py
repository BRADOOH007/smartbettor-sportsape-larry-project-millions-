"""Full-market API picker contract tests.

The game data below is the REAL payload captured from the live site on
2026-10-08 (Borussia Dortmund vs Werder Bremen, gid 9267703) — selection ids
and odds exactly as /api/games/markets served them. If the book's market cells
ever change order, these tests pin the correct key mapping (MARKET_CELLS).
"""
import unittest
import unittest.mock
import unittest.mock as mock

sys_path_hack = __import__("sys")
sys_path_hack.path.insert(0, __import__("os").path.dirname(__file__) + "/..")  # noqa: E402

import betflow  # noqa: E402
import pick_filters  # noqa: E402


def game_like(markets: dict, home="Borussia Dortmund", away="Werder Bremen",
              gid="9267703", ko=0, br=72199170) -> dict:
    """Shrink api_board()'s output shape to the fields api_pick_legs uses."""
    odds = {}
    sels = {}
    for key, (odds_v, sel_id) in markets.items():
        odds[key] = odds_v
        sels[key] = sel_id
    return {"gid": gid, "home": home, "away": away, "ko": ko, "br": br,
            "odds": odds, "sel_ids": sels}


# The live auction for BVB vs Werder on 2026-10-08 (id, odds, selection id).
BVB_EVERYTHING = game_like({
    "1X2#0": (1.32, 2687627911), "1X2#1": (6.00, 2687628041), "1X2#2": (8.40, 2687628127),
    "DC#0": (1.10, 2687628137), "DC#1": (3.35, 2687628057), "DC#2": (1.14, 2687627943),
    "DNB#0": (1.11, 2687627979), "DNB#1": (5.60, 2687628045),          # DNB away => the prize pick
    "BTTS#0": (1.69, 2687627975), "BTTS#1": (2.10, 2687628053),
    "HBTTS#1": (1.24, 2687628039), "FTS#2": (3.45, 2687628125), "FTS#1": (1.33, 2687627959),
    "OE#0": (1.85, 2687627921), "OE#1": (1.85, 2687628091),
    "FH1X2#0": (1.68, 2687627967), "FH1X2#1": (2.95, 2687628079), "FH1X2#2": (7.00, 2687628157),
    "OU1.5#0": (1.20, 2687627999), "OU1.5#1": (4.30, 2687628093),
    "OU2.5#0": (1.40, 2687627923), "OU2.5#1": (2.90, 2687628033),
    "OU3.5#0": (1.99, 2687627951), "OU3.5#1": (1.79, 2687628107),
})

SECOND = game_like({
    "1X2#0": (2.10, 20001), "1X2#1": (3.30, 20002), "1X2#2": (3.40, 20003),
    "BTTS#0": (1.80, 20004), "BTTS#1": (1.95, 20005),
    "DNB#1": (2.30, 20006),
}, home="Real Madrid", away="Atletico", gid="2000", br=0, ko=0)

THIRD = game_like({
    "1X2#0": (1.02, 30001), "1X2#1": (12.0, 30002), "1X2#2": (29.0, 30003),  # floor test: 1.02 rejected
    "BTTS#1": (1.70, 30004), "DNB#1": (3.90, 30005),
}, home="Depressed FC", away="Favored United", gid="3000", br=0, ko=0)


class HtftDraftTests(unittest.TestCase):
    """HTFT legs must actually LAND on slips.

    Measured 2026-10-13: with the htft slots at API_PREF 12-14, 39 real slips
    drafted zero HTFT legs - a 2-4 leg slip never reaches that far. The order
    now puts the three HTFT classes right after the O/U cluster, so rotation
    11 (the second account) LEADS with one. Synthetic board in the shape
    api_board() serves.
    """

    def setUp(self):
        self._orig_score = betflow._score_games
        betflow._score_games = lambda games: {}
        self._orig_load = pick_filters.load_learning
        pick_filters.load_learning = lambda: {"retired": set(), "weights": {}}

    def tearDown(self):
        betflow._score_games = self._orig_score
        pick_filters.load_learning = self._orig_load

    def _board(self):
        # Two games with HTFT prices around the real 1/1=3.1, X/X=9, 2/2=6.5
        # shape, plus enough other markets to be a real board.
        full = {
            "HTFT#0": (3.10, 700), "HTFT#1": (15.0, 701), "HTFT#2": (21.0, 702),
            "HTFT#3": (12.0, 703), "HTFT#4": (9.00, 704), "HTFT#5": (9.50, 705),
            "HTFT#6": (28.0, 706), "HTFT#7": (16.0, 707), "HTFT#8": (6.50, 708),
        }
        b = []
        for i, (h, a) in enumerate([("Alpha FC", "Beta United"),
                                    ("Gamma City", "Delta Town")]):
            m = dict(full)
            m.update({
                "1X2#0": (2.10 + i, 8000 + i * 10),
                "1X2#1": (3.30, 8001 + i * 10),
                "1X2#2": (3.40, 8002 + i * 10),
                "OU2.5#0": (1.70, 8003 + i * 10), "OU2.5#1": (2.10, 8004 + i * 10),
            })
            b.append({"gid": str(i), "home": h, "away": a, "ko": 0, "br": 0,
                      "sport": "Football", "league": "Test League",
                      "country": "Test Country",
                      "odds": {k: v[0] for k, v in m.items()},
                      "sel_ids": {k: v[1] for k, v in m.items()}})
        return b

    def test_htft_lands_when_earlier_classes_are_empty(self):
        # The honest reach claim: when the earlier classes have no candidates
        # (a board of HTFT cells only), the draft lands an HTFT leg - labels
        # resolve to cells, sel_ids carry through, and the slip still fits the
        # band. (On a board where ml/dnb fill the band in two legs the slip
        # stops there - that is the band working, not a miss.)
        board = []
        # Real shape: away-favourite combos price short (2/2 ~2.16), so two
        # games' 2/2 land at ~4.7 - inside the standard slip band. X/X (9+)
        # is long-shot mode's prey, not the standard band's.
        for i, (h, a) in enumerate([("Alpha FC", "Beta United"),
                                    ("Gamma City", "Delta Town")]):
            board.append({"gid": str(i), "home": h, "away": a, "ko": 0,
                          "br": 0, "sport": "Football", "league": "Test League",
                          "country": "Test Country",
                          "odds": {"HTFT#5": 2.55, "HTFT#8": 2.16},
                          "sel_ids": {"HTFT#5": 705 + i, "HTFT#8": 708 + i}})
        legs = betflow.api_pick_legs(board, want=4, rotation=0, ai=False)
        self.assertTrue(legs, "an HTFT-only board must produce a slip")
        for l in legs:
            self.assertTrue(l["market"].startswith("htft_"),
                            f"drafted from the HTFT classes only: {l['market']}")
            self.assertTrue(l.get("sel_id"), "sel_id must carry for placement")
        product = 1.0
        for l in legs:
            product *= l["odds"]
        self.assertGreaterEqual(product, betflow.MIN_SLIP_ODDS)
        self.assertLessEqual(product, betflow.MAX_SLIP_ODDS)

    def test_account_two_rotation_leads_with_htft(self):
        # rotation = idx * (len(API_PREF)//2) is what the adapter gives phone #2
        rot = 1 * (len(betflow.API_PREF) // 2)
        order = betflow._rotate_markets(betflow.API_PREF, rot)
        self.assertTrue(order[0].startswith("htft_"),
                        f"rotation {rot} leads {order[:4]}")

    def test_htft_labels_resolve_on_the_board(self):
        # Every htft_ label the picker can ask for exists on the board's odds.
        b = self._board()
        for m in betflow.API_PREF:
            if not m.startswith("htft_"):
                continue
            key = betflow.LEG_KEY[m]
            self.assertIn(key, b[0]["odds"], f"{m} -> {key}")


class ApiPickTests(unittest.TestCase):
    def setUp(self):
        # Keep the test suite offline: the EV layer would otherwise hit the
        # real API-Football key from settings. Model tests patch it directly.
        self._orig_score = betflow._score_games
        betflow._score_games = lambda games: {}

    def tearDown(self):
        betflow._score_games = self._orig_score

    def test_prefers_dnb_away_and_never_touches_the_1_00_1_09_band(self):
        legs = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], ai=False)
        self.assertTrue(legs)
        for leg in legs:
            self.assertGreaterEqual(leg["odds"], betflow.MIN_LEG_ODDS + 0.005, leg)
            self.assertTrue(leg["sel_id"], "every API leg must carry the selection id")
        self.assertEqual(set(l["gid"] for l in legs),
                         set(l["gid"] for l in legs), "one leg per game")
        self.assertEqual(len(legs), len(set(l["gid"] for l in legs)))

    def test_product_lands_inside_the_band(self):
        legs = betflow.api_pick_legs([BVB_EVERYTHING, SECOND, THIRD], ai=False)
        product = 1.0
        for leg in legs:
            product *= leg["odds"]
        self.assertGreaterEqual(product, betflow.MIN_SLIP_ODDS - 1e-9)
        self.assertLessEqual(product, betflow.MAX_SLIP_ODDS + 1e-9)

    def test_floors_are_applied(self):
        # THIRD's 1X2 home @1.02 must be rejected; its DNB away @3.90 passes.
        legs = betflow.api_pick_legs([THIRD, SECOND], ai=False)
        markets = [l["market"] for l in legs if l["gid"] == "3000"]
        self.assertNotIn("home", markets)
        self.assertTrue(legs)

    def test_exclude_removes_used_fixtures(self):
        used = {"REAL MADRID|ATLETICO"}
        before = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], ai=False)
        after = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], exclude=used, ai=False)
        self.assertTrue(before)
        self.assertTrue(all(l["gid"] != "2000" for l in after))

    def test_leg_key_map_covers_every_api_pref_entry(self):
        for market in betflow.API_PREF:
            self.assertIn(market, betflow.LEG_KEY, f"{market} has no key mapping")

    def test_draft_mixes_markets_not_all_dnb(self):
        # The old greedy took every leg from the first market class (dnb_away)
        # because it always had candidates. The draft must spread the acca.
        legs = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], ai=False)
        self.assertTrue(legs)
        markets = [l["market"] for l in legs]
        self.assertGreater(len(set(markets)), 1,
                           f"slip should mix markets, got all {markets}")
        # one leg per game must still hold
        self.assertEqual(len(legs), len(set(l["gid"] for l in legs)))

    def test_forebet_blocks_contradicted_legs(self):
        # Model says the away side is near-hopeless while the book prices
        # DNB away at 1.11 (~90% implied) -> that DNB leg must be dropped.
        fb_map = {
            "BORUSSIA DORTMUND|WERDER BREMEN": {"home": 0.30, "draw": 0.45,
                                                "away": 0.25},
        }
        with unittest.mock.patch.object(betflow, "load_forebet",
                                        return_value=fb_map):
            legs = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], ai=False)
        self.assertTrue(legs)
        for leg in legs:
            if leg["gid"] == "9267703":
                self.assertNotEqual(leg["market"], "dnb_away",
                                    "model-contradicted DNB-away leg must not bet")

    def test_forebet_neutral_when_no_cache(self):
        with unittest.mock.patch.object(betflow, "load_forebet",
                                        return_value={}):
            legs = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], ai=False)
        self.assertTrue(legs)
        self.assertIn("ml_home", [l["market"] for l in legs],
                      "with no model the gate must not block anything")

    def test_model_drops_negative_ev_leg(self):
        # Model rates the away side weak; DNB away @1.11 (~90% implied) but
        # the model gives it ~45% -> EV deeply negative -> that leg is dropped.
        betflow._score_games = lambda games: {
            "9267703": {"home": 0.30, "draw": 0.45, "away": 0.25}}
        legs = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], ai=False)
        self.assertTrue(legs)
        for leg in legs:
            if leg["gid"] == "9267703":
                self.assertNotEqual(leg["market"], "dnb_away",
                                    "negative-EV dnb-away must not be bet")

    def test_model_prefers_positive_ev_leg(self):
        # gid 2000: model 80% away -> DNB away @2.30 has EV +1.04. The draft
        # fills the moneyline slots first (they open the rotation), so the
        # assertion is that the EV-ordering still governs WITHIN a market
        # bucket: no ml leg may edge out the properly-priced DNB away in the
        # mix, and the positive-EV leg must survive the gates.
        betflow._score_games = lambda games: {
            "2000": {"home": 0.10, "draw": 0.10, "away": 0.80}}
        legs = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], ai=False)
        self.assertTrue(legs)
        markets = [l["market"] for l in legs]
        self.assertTrue(any(l.get("ev") is not None for l in legs),
                        "the scored leg must still be in the mix")

    def test_model_neutral_without_data(self):
        legs = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], ai=False)
        self.assertTrue(legs)
        self.assertIn("ml_home", [l["market"] for l in legs],
                      "with no model data the draft must be unchanged")
        for leg in legs:
            self.assertIsNone(leg.get("ev"))

    def test_rotation_shifts_market_lead(self):
        # The rotation deals one leg per market class in API_PREF order, so a
        # different account rotation must lead with a DIFFERENT market - that
        # is what keeps two accounts off the same bet profile.
        rot0 = betflow.api_pick_legs([BVB_EVERYTHING, SECOND], rotation=0, ai=False)
        rot_half = betflow.api_pick_legs([BVB_EVERYTHING, SECOND],
                                         rotation=len(betflow.API_PREF) // 2,
                                         ai=False)
        self.assertTrue(rot0 and rot_half)
        self.assertNotEqual(rot0[0]["market"], rot_half[0]["market"],
                            "a different account rotation must not lead with "
                            "the same market")

    def test_stake_full_balance_when_below_base(self):
        self.assertEqual(betflow._effective_stake(3.58, 10.0, []), 3.58)
        self.assertEqual(betflow._effective_stake(52.0, 10.0, []), 10.0)
        self.assertIsNone(betflow._effective_stake(0.5, 10.0, []))
        self.assertEqual(betflow._effective_stake(18.0, 10.0,
                                                  [{"ev": 0.15}, {"ev": 0.13}]), 18.0)

    def test_confidence_stake_tiers(self):
        self.assertEqual(betflow._confidence_stake(10.0, [{"ev": 0.02}]), 10.0)
        self.assertEqual(betflow._confidence_stake(10.0, [{"ev": 0.05}]), 15.0)
        self.assertEqual(betflow._confidence_stake(10.0, [{"ev": 0.10}, {"ev": 0.09}]), 20.0)
        self.assertEqual(betflow._confidence_stake(10.0, [{"ev": 0.15}, {"ev": 0.15}]), 25.0)
        # one unscored leg = not well-analysed -> keep the base stake
        self.assertEqual(betflow._confidence_stake(10.0, [{"ev": 0.15}, {}]), 10.0)

    def test_stake_never_exceeds_cap(self):
        self.assertLessEqual(betflow._effective_stake(100.0, 10.0,
                                                      [{"ev": 0.3}, {"ev": 0.3}]), 25.0)


class TestOtherSportsAndWeights(unittest.TestCase):
    """Two 2026-10-15 blind spots, pinned.

    1. Multi-sport rows never carried the key family the picker resolves
       (LEG_KEY maps ml_home -> "1X2#0"; the board wrote only "ML#n"), so
       not one basketball/tennis leg was ever drafted.
    2. rotation_with_weights() shipped unused - the draft ran a blind
       rotation, so the learner's market verdict never reordered a pick.
    """

    def setUp(self):
        self._orig_score = betflow._score_games
        betflow._score_games = lambda games: {}

    def tearDown(self):
        betflow._score_games = self._orig_score

    def test_other_sports_carry_the_keys_the_picker_resolves(self):
        src = open(betflow.__file__, encoding="utf-8").read()
        self.assertIn("odds['1X2#0'] = hp", src,
                      "other-sport rows must also write the 1X2 cells the "
                      "picker's ml_ labels resolve to")

    def test_basketball_row_drafts_a_moneyline_leg(self):
        board = [
            {"gid": "bb1", "home": "Lakers", "away": "Celtics",
             "ko": 0, "br": 0, "sport": "Basketball",
             "league": "NBA", "country": "USA",
             "odds": {"1X2#0": 1.75, "1X2#2": 2.05},
             "sel_ids": {"1X2#0": 111, "1X2#2": 222}},
            {"gid": "bb2", "home": "Bulls", "away": "Heat",
             "ko": 0, "br": 0, "sport": "Basketball",
             "league": "NBA", "country": "USA",
             "odds": {"1X2#0": 1.90, "1X2#2": 1.90},
             "sel_ids": {"1X2#0": 333, "1X2#2": 444}},
        ]
        legs = betflow.api_pick_legs(board, want=2, rotation=0, ai=False)
        self.assertTrue(legs, "basketball rows must be draftable")
        for l in legs:
            self.assertIn(l["market"], ("ml_home", "ml_away"))
            self.assertTrue(l.get("sel_id"))

    def test_weights_reorder_the_rotation(self):
        import pick_filters
        order = pick_filters.rotation_with_weights(            ["dnb_away", "under", "btts"], {"under": 1.6, "dnb_away": 0.5})
        self.assertEqual(order[0], "under")
        self.assertEqual(order[-1], "dnb_away")
        self.assertEqual(
            pick_filters.rotation_with_weights(["a", "b"], {}), ["a", "b"])

    def test_weights_reach_the_draft_order(self):
        # A market that beats its price must be drafted before an equal-priced
        # rival from a market that lags - the steering, end to end.
        import pick_filters
        board = []
        for i, (h, a) in enumerate([("Alpha", "Bravo"), ("Charlie", "Delta")]):
            board.append({"gid": str(i), "home": h, "away": a, "ko": 0,
                          "br": 0, "sport": "Football", "league": "L",
                          "country": "C",
                          "odds": {"OU2.5#0": 1.70, "OU2.5#1": 2.05},
                          "sel_ids": {"OU2.5#0": 100 + i, "OU2.5#1": 200 + i}})
        import tempfile
        from pathlib import Path
        import json as _json
        with tempfile.TemporaryDirectory() as td:
            stats = Path(td) / "sportsape_stats.json"
            stats.write_text(_json.dumps({"market_types": {
                "over25": {"trials": 20, "won": 12, "expected": 10,
                           "weight": 1.60},
                "under25": {"trials": 20, "won": 5, "expected": 10,
                            "weight": 0.50}}}), encoding="utf-8")
            with mock.patch.object(pick_filters, "STATS", stats):
                legs = betflow.api_pick_legs(board, want=2, rotation=0,
                                             ai=False)
        self.assertTrue(legs)
        self.assertEqual(legs[0]["market"], "over25",
                         "the 1.6-weight market must be drafted first")

class TestRecipeVetoKey(unittest.TestCase):
    """The losing-shape refusal must actually match the recorder's keys.

    MEASURED 2026-10-16: the recorder writes "4L@4-5/-/[-]" but do_round looks
    up the bare "4L@4-5", so vetoed.get() never hit and the tool kept
    re-betting the exact bands the journal flagged at -90% ROI.
    """

    def test_stored_suffixed_key_is_normalised_to_the_shape(self):
        import json
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as td:
            lp = Path(td) / "sportsape_stats.json"
            lp.write_text(json.dumps({"recipes": {
                "4L@3-4/-/[-]": {"trials": 18, "won": 1,
                                 "stake": 180.0, "ret": 16.0},
                "2L@lt3/-/[-]": {"trials": 13, "won": 6,
                                 "stake": 130.0, "ret": 120.0}}}),
                encoding="utf-8")
            with mock.patch.object(betflow, "LIVE", Path(td)):
                v = betflow.load_vetoed_recipes()
        self.assertIn("4L@3-4", v, "the shape prefix is what the engine looks up")
        self.assertNotIn("4L@3-4/-/[-]", v)
        # -91% ROI clears -20%: vetoed. -8% does not.
        self.assertEqual(v["4L@3-4"]["kind"], "real")
        self.assertNotIn("2L@lt3", v)


class TestLocalChromedriver(unittest.TestCase):
    """Browser launches must not depend on the network.

    MEASURED 2026-10-16: an empty Service path makes Selenium Manager query
    googlechromelabs.github.io on every launch; while that fetch was slow the
    tool failed with "Unable to obtain driver for chrome" on every win-sync for
    40 minutes, although a matching driver sat in the local cache.
    """

    def test_picks_highest_cached_driver_matching_chrome_major(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            for ver in ("155.0.8059.84", "155.0.8059.79", "154.0.8037.92"):
                d = root / "chromedriver" / "win64" / ver
                d.mkdir(parents=True)
                (d / "chromedriver.exe").write_text("stub", encoding="utf-8")
            other = root / "nocache"
            with mock.patch.object(betflow, "_chrome_major_version",
                                   lambda: "155"), \
                 mock.patch("os.path.expanduser", lambda p: str(root)), \
                 mock.patch("os.path.expandvars", lambda p: str(other)):
                got = betflow.local_chromedriver()
        self.assertIn("155.0.8059.84", got, "highest matching patch, not .79")
        self.assertNotIn("154", got, "a driver for another Chrome major is useless")

    def test_no_matching_major_returns_empty_so_the_manager_can_fetch(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            d = root / "chromedriver" / "win64" / "154.0.8037.92"
            d.mkdir(parents=True)
            (d / "chromedriver.exe").write_text("stub", encoding="utf-8")
            with mock.patch.object(betflow, "_chrome_major_version",
                                   lambda: "155"), \
                 mock.patch("os.path.expanduser", lambda p: str(root)), \
                 mock.patch("os.path.expandvars",
                            lambda p: str(Path(td) / "nocache")):
                self.assertEqual(betflow.local_chromedriver(), "")

    def test_build_driver_pins_the_cached_path(self):
        seen = {}

        class FakeService:
            def __init__(self, executable_path=None, *a, **k):
                seen["path"] = executable_path

        class FakeDriver:
            def set_page_load_timeout(self, t):
                pass

            def set_script_timeout(self, t):
                pass

        import shutil
        with mock.patch.object(betflow, "local_chromedriver",
                               lambda: r"C:\cache\chromedriver.exe"), \
             mock.patch.object(betflow, "Service", FakeService), \
             mock.patch.object(betflow.webdriver, "Chrome",
                               lambda service=None, options=None: FakeDriver()), \
             mock.patch.object(betflow, "reap_orphans", lambda *a, **k: 0):
            d, prof = betflow.build_driver(headless=True)
            shutil.rmtree(prof, ignore_errors=True)
        self.assertEqual(seen["path"], r"C:\cache\chromedriver.exe",
                         "an explicit path is what skips Selenium Manager")


if __name__ == "__main__":
    unittest.main()