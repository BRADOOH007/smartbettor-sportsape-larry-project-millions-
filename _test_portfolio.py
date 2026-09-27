"""Focused checks on the portfolio layer added 2026-09-26.

These are the money-path functions, so they get real assertions rather than a
compile check: a stake formula that silently returns 0 would quietly stop
betting, and a breaker that never trips would quietly lose the bankroll.
"""
import importlib.util
import pathlib as _pl
import json
import os
import sys
import tempfile

# Synthetic account numbers. Real MSISDNs must never reach version control.
PHONE_A = "0700000001"
PHONE_B = "0790000002"
import time

os.environ.setdefault("SPORTSAPE_TEST", "1")

spec = importlib.util.spec_from_file_location("sb", "sportsape_backend.py")
sb = importlib.util.module_from_spec(spec)
sys.modules["sb"] = sb
spec.loader.exec_module(sb)

tmp = tempfile.mkdtemp(prefix="pf_test_")
fails = []


def check(name, cond, extra=""):
    if cond:
        print(f"  PASS  {name}")
    else:
        print(f"  FAIL  {name} {extra}")
        fails.append(name)


print("== Kelly sizing ==")
e = sb.SportsapeBackend.__new__(sb.SportsapeBackend)
e._bets = []

# A genuinely good bet: p=0.60 at x3.00 -> f* = (2*0.6-0.4)/2 = 0.40
# 1/5 Kelly would be 8% of bankroll, but MAX_KELLY_SHARE=5% is a hard safety
# rail, so 5% of 1000 = 50 is the correct answer. The cap is meant to bind.
s = e._kelly_stake("070", 1000.0, 0.60, 3.0, 1000.0)
check("good bet is staked", s > 0, f"got {s}")
check("strong edge is capped at 5% of bankroll",
      abs(s - 1000.0 * 0.05) < 1.0, f"expected 50, got {s:.2f}")

# A thin but real edge must NOT be clipped to the cap — it should come out
# proportionally below it, proving Kelly (not the cap) is driving the size.
thin = e._kelly_stake("070", 10000.0, 0.38, 3.0, 100000.0)
check("thin edge sizes below the cap", 0 < thin < 10000.0 * 0.05, f"got {thin:.2f}")
# f* = (2*0.38-0.62)/2 = 0.07 ; 1/5 Kelly = 1.4% of 10000 = 140
check("thin edge matches 1/5 Kelly", abs(thin - 140.0) < 2.0, f"expected ~140, got {thin:.2f}")

# A bet priced at its own fair value has zero edge -> must be refused.
fair_p = 1.0 / 3.0
check("fair-priced bet refused", e._kelly_stake("070", 1000.0, fair_p, 3.0, 1000.0) == 0.0)

# Negative edge must be refused.
check("negative-EV bet refused", e._kelly_stake("070", 1000.0, 0.20, 3.0, 1000.0) == 0.0)

# Hard cap: MAX_KELLY_SHARE=5% of balance, even on a huge edge.
huge = e._kelly_stake("070", 1000.0, 0.95, 10.0, 1000.0)
check("stake capped at 5% of bankroll", huge <= 1000.0 * 0.05 + 1e-6, f"got {huge:.2f}")

# Portfolio cap binds when the portfolio is smaller than the account.
tiny_pf = e._kelly_stake("070", 100000.0, 0.95, 10.0, 1000.0)
check("portfolio cap binds", tiny_pf <= 1000.0 * 0.05 + 1e-6, f"got {tiny_pf:.2f}")

print("== Variance scaling ==")
# Same signal, but a volatile account must bet less than a calm one.
calm = [{"phone": "A", "status": "won", "stake": 100.0, "won_amount": 120.0} for _ in range(10)]
wild = [{"phone": "B", "status": "won" if i % 2 == 0 else "lost", "stake": 100.0,
         "won_amount": 300.0} for i in range(10)]
e._bets = calm
v_calm = e._account_variance("A")
e._bets = wild
v_wild = e._account_variance("B")
check("volatile account scores higher", v_wild > v_calm, f"calm={v_calm:.3f} wild={v_wild:.3f}")
e._bets = []
s_calm = e._kelly_stake("A", 10000.0, 0.38, 3.0, 100000.0)
e._bets = wild
s_wild = e._kelly_stake("B", 10000.0, 0.38, 3.0, 100000.0)
check("volatile account stakes less on same signal", s_wild < s_calm,
      f"calm={s_calm:.2f} wild={s_wild:.2f}")
check("calm account at full 1/5 Kelly", abs(s_calm - 140.0) < 2.0, f"got {s_calm:.2f}")

print("== Drawdown circuit breakers ==")
# A three-account fleet, so the per-account breaker and the portfolio breaker can
# be exercised independently. With a single account the two thresholds are the
# same number, which would hide whether each one actually works.
e._portfolio = {"peaks": {"A": 1000.0, "B": 1000.0, "C": 1000.0},
                "portfolio_peak": 3000.0, "last_equity": {},
                "frozen": {}, "halted": False, "halt_reason": "",
                "refused": 0, "refused_reasons": {}}
e.PORTFOLIO_PATH = __import__("pathlib").Path(tmp) / "pf.json"
fleet = lambda a: {"A": a, "B": 1000.0, "C": 1000.0}

ok, why = e._circuit_breaker_check("A", 950.0, fleet(950.0))
check("5% account drawdown passes", ok, why)

ok, why = e._circuit_breaker_check("A", 700.0, fleet(700.0))
check("30% account drawdown passes (below 40% freeze)", ok, why)

ok, why = e._circuit_breaker_check("A", 600.0, fleet(600.0))
check("40% account drawdown freezes the account",
      (not ok) and e._portfolio["frozen"].get("A"), why)
check("40% on one account did NOT halt the whole portfolio",
      not e._portfolio["halted"], "one sick account should not stop the fleet")

ok, why = e._circuit_breaker_check("A", 1000.0, fleet(1000.0))
check("frozen account stays frozen even after a recovery", not ok, why)

e._reset_circuit_breakers()
ok, _ = e._circuit_breaker_check("A", 1000.0, fleet(1000.0))
check("reset clears the freeze", ok and not e._portfolio["frozen"])

# Portfolio halt: every account down ~20% together, so no single account is near
# its own -40% freeze. This is precisely the case per-account checks cannot see.
allbad = {"A": 790.0, "B": 790.0, "C": 780.0}
ok, why = e._circuit_breaker_check("A", 790.0, allbad)
check("portfolio halt trips when every account bleeds together",
      (not ok) and e._portfolio["halted"], why)
check("portfolio halt stops an account that is barely down itself",
      not e._circuit_breaker_check("A", 790.0, allbad)[0], "halt must persist")
e._reset_circuit_breakers()

print("== Drawdown must NOT read cash as equity (2026-09-27 regression) ==")
# The real bug: a bet moves stake out of cash and into the slip, so cash drops
# on placement and returns only if the bet WINS. Measuring drawdown on cash
# booked every bet as an instant loss and halted the whole fleet at -85% while
# the accounts were in fact healthy.
e._bets = [{"id": "1", "phone": "A", "status": "active", "stake": 60.0,
            "placed_at": sb.datetime.now().isoformat(timespec="seconds"),
            "game_ids": [], "leg_names": [], "markets": []},
           {"id": "2", "phone": "B", "status": "active", "stake": 30.0,
            "placed_at": sb.datetime.now().isoformat(timespec="seconds"),
            "game_ids": [], "leg_names": [], "markets": []}]
e._portfolio = {"peaks": {}, "portfolio_peak": 0.0, "last_equity": {},
                "frozen": {}, "halted": False, "halt_reason": "",
                "refused": 0, "refused_reasons": {}}
# Both accounts hold 100 of equity, but A has spent 60 into an open slip so only
# 40 is spendable. Cash alone would read A as -60% and halt everything.
e._note_balances({"A": 40.0, "B": 100.0})
pf = e._portfolio
check("open stake counts toward equity", abs(pf["peaks"]["A"] - 100.0) < 0.01,
      f"peak A = {pf['peaks'].get('A')} (expected 100)")
# A equity = 40 cash + 60 in play = 100. B equity = 100 cash + 30 in play = 130.
check("portfolio peak is the fleet total", abs(pf["portfolio_peak"] - 230.0) < 0.01,
      f"peak = {pf.get('portfolio_peak')} (expected 230)")
ok, why = e._circuit_breaker_check("A", 40.0, {"A": 40.0, "B": 100.0})
check("open bets do NOT trip the portfolio halt", ok, why)
check("no account frozen just for having stake in play",
      not e._portfolio["frozen"], str(e._portfolio["frozen"]))

# A genuinely LOST bet must still register: stake leaves play and cash does not
# return, so equity really is 40 and the drop is real.
e._bets[0]["status"] = "lost"
ok, why = e._circuit_breaker_check("A", 40.0, {"A": 40.0, "B": 100.0})
check("a real loss is still measured", (not ok) and e._portfolio["frozen"].get("A"),
      f"expected A frozen at 40/100 equity, ok={ok} {why}")
e._reset_circuit_breakers()
e._bets = []

print("== Single-account round must not fake a fleet crash (2026-09-27 regression) ==")
# Only one account is read per round. If peaks/drawdown are computed from that
# single entry, the other accounts read as zero and the fleet looks destroyed.
e._bets = []
e._portfolio = {"peaks": {}, "portfolio_peak": 0.0, "last_equity": {},
                "frozen": {}, "halted": False, "halt_reason": "",
                "refused": 0, "refused_reasons": {}}
e._note_balances({"PHONE_B": 104.14, "PHONE_A": 15.40})
pk = float(e._portfolio["portfolio_peak"])
check("first full read sets peak to combined total", abs(pk - 119.54) < 0.01,
      f"peak = {pk} (expected 119.54)")
# Next round only reads one account; the other must carry its last known equity.
ok, why = e._circuit_breaker_check("PHONE_A", 15.40, {"PHONE_A": 15.40})
check("one-account round does not halt the fleet", ok, why)
dd = e._portfolio_drawdown({"PHONE_A": 15.40})
check("drawdown stays ~0 when nothing was lost", dd < 0.01, f"drawdown = {dd:.1%}")
e._portfolio = {"peaks": {}, "portfolio_peak": 0.0, "last_equity": {},
                "frozen": {}, "halted": False, "halt_reason": "",
                "refused": 0, "refused_reasons": {}}

print("== Cross-account correlation ==")
e._portfolio = {"peaks": {}, "portfolio_peak": 0.0, "frozen": {}, "halted": False,
                "halt_reason": "", "refused": 0, "refused_reasons": {}}
e._bets = [{
    "id": "1", "phone": "B", "status": "active", "stake": 10.0,
    "placed_at": sb.datetime.now().isoformat(timespec="seconds"),
    "game_ids": ["g1", "g2"], "leg_names": ["Arsenal v Chelsea->over", "Liverpool v City->home"],
    "markets": ["over", "home"],
}]
ok, why = e._correlation_verdict("A", ["g1"], ["Arsenal v Chelsea->over"], ["over"])
check("same game on another account is refused", not ok, why)
ok, why = e._correlation_verdict("A", ["g9"], ["Everton v Villa->home"], ["home"])
check("different game is allowed", ok, why)
ok, why = e._correlation_verdict("B", ["g1"], ["Arsenal v Chelsea->over"], ["over"])
check("own game is allowed (idempotent re-check)", ok, why)

# Market cap across the fleet: MAX_ACCOUNTS_PER_MARKET = 3
e._bets = [{"id": str(i), "phone": f"P{i}", "status": "active", "stake": 10.0,
            "placed_at": sb.datetime.now().isoformat(timespec="seconds"),
            "game_ids": [f"x{i}"], "leg_names": [f"Game {i} v Other->over"],
            "markets": ["over"]} for i in range(3)]
ok, why = e._correlation_verdict("NEW", ["x99"], ["New v Other->over"], ["over"])
check("market cap refuses a 4th account", not ok, why)
ok, _ = e._correlation_verdict("NEW", ["x99"], ["New v Other->under"], ["under"])
check("unused market is still fine", ok)

# Exposure window must ignore old bets.
old = sb.datetime.now() - sb.timedelta(hours=40)
e._bets = [{"id": "1", "phone": "B", "status": "active", "stake": 10.0,
            "placed_at": old.isoformat(timespec="seconds"),
            "game_ids": ["g1"], "leg_names": ["Old v Old->over"], "markets": ["over"]}]
ok, _ = e._correlation_verdict("A", ["g1"], ["New v Other->home"], ["home"])
check("stale bet outside window is ignored", ok)

print("== Cash-out policy ==")
e._portfolio = {"peaks": {}, "portfolio_peak": 0.0, "frozen": {}, "halted": False,
                "halt_reason": "", "refused": 0, "refused_reasons": {}}
take, why = e._cashout_decision(offer=5.0, stake=100.0, possible_win=500.0,
                                won=1, pending=3, bad=0)
check("never crystallise a big loss", not take, why)

take, why = e._cashout_decision(offer=130.0, stake=100.0, possible_win=500.0,
                                won=2, pending=2, bad=0)
check("take a locked 30% profit", take, why)

take, why = e._cashout_decision(offer=80.0, stake=100.0, possible_win=500.0,
                                won=2, pending=1, bad=0, mins_to_last_ko=5)
check("take 80% back with the last leg 5m away", take, why)

take, why = e._cashout_decision(offer=55.0, stake=100.0, possible_win=500.0,
                                won=2, pending=1, bad=0, mins_to_last_ko=180)
check("hold 55% back with plenty of time left", not take, why)

take, why = e._cashout_decision(offer=400.0, stake=100.0, possible_win=500.0,
                                won=3, pending=1, bad=0)
check("take 80% of remaining possible win", take, why)

take, why = e._cashout_decision(offer=0.0, stake=100.0, possible_win=500.0,
                                won=1, pending=2, bad=0)
check("no offer means no action", not take, why)

print("== Leg cap ==")
check("hard leg cap is 6", e.MAX_SLIP_LEGS_HARD == 6)

print("== Refusal counter ==")
e._portfolio = {"peaks": {}, "portfolio_peak": 0.0, "frozen": {}, "halted": False,
                "halt_reason": "", "refused": 0, "refused_reasons": {}}
e.PORTFOLIO_PATH = __import__("pathlib").Path(tmp) / "pf2.json"
e._count_refusal("kelly says no edge")
e._count_refusal("kelly says no edge")
e._count_refusal("game already on another account")
m = e._portfolio_metrics()
check("refusals counted", m.get("refused") == 3, str(m.get("refused")))
check("refusal reasons itemised",
      m.get("refused_reasons", {}).get("kelly says no edge") == 2,
      str(m.get("refused_reasons")))

print("== Benign declines must NOT look like session failures ==")
# 2026-09-27: every "nothing worth betting" exit used to return status
# "aborted". The supervisor counted those as a broken session and rebuilt
# drivers 18+ times an hour, manufacturing the selenium instability it was
# warning about. Guard the classification itself so it cannot silently revert.
_SRC = e.__file__ if hasattr(e, "__file__") else "sportsape_backend.py"
_src_text = open(_SRC, encoding="utf-8").read() if os.path.exists(_SRC) else ""
if _src_text:
    import re as _re
    # every skipped return must carry the skipped flag
    _skipped_rets = _re.findall(r'return \{"status": "skipped"(.{0,80})', _src_text)
    check("every skipped return sets skipped=True",
          all("skipped" in r for r in _skipped_rets),
          "%d returns" % len(_skipped_rets))
    # "aborted" is reserved for real technical faults only
    _aborted = [m for m in _re.finditer(
        r'return \{"status": "aborted", "message": "([^"]*)"', _src_text)]
    _bad = [m.group(1) for m in _aborted
            if m.group(1) != "Balance unreadable — retry next round"]
    check("only genuine faults still report aborted", not _bad, str(_bad))
    # the scheduler must branch declines away from beat_abort
    check("declines clear the abort streak instead of raising it",
          "clear_aborts" in _src_text and "note_skip" in _src_text)
    # and the supervisor must only judge accounts it actually trades
    _sup_src = open("sportsape_agents.py", encoding="utf-8").read()
    check("parked-account check filters to configured accounts",
          "_known and str(acct).strip() not in _known" in _sup_src)

print("== Portfolio halt must not latch forever ==")
# 2026-09-27: the halt was one-way. A single bad reading (partial fleet, a
# slow zero, a stale 'active' bet inflating equity) tripped it and the engine
# then refused every round forever, printing "PORTFOLIO HALT" while the fleet
# was in fact healthy. There was no way back short of hand-editing the file.


def _fresh_engine():
    eng = sb.SportsapeBackend.__new__(sb.SportsapeBackend)
    eng._bets = []
    return eng


e2 = _fresh_engine()
e2.PORTFOLIO_PATH = _pl.Path(tmp) / "pf3.json"
e2._portfolio = {"peaks": {"A": 100.0, "B": 100.0}, "portfolio_peak": 200.0,
                 "frozen": {}, "halted": False, "halt_reason": "",
                 "refused": 0, "refused_reasons": {}, "last_equity": {}}
e2._portfolio["last_equity"] = {"A": 100.0, "B": 100.0}
e2._bets = []
# 1) a partial reading (only A visible) must NOT trip the fleet halt
ok, why = e2._circuit_breaker_check("A", 100.0, {"A": 100.0})
check("partial fleet read does not halt", ok, why)
check("partial read leaves halted False", not e2._portfolio.get("halted"))

# 2) a genuine fleet-wide loss DOES halt. Both accounts fall by the same
#    proportion so the PER-ACCOUNT breaker (-40%) stays quiet and the
#    portfolio breaker (-20% of the combined peak) is the one under test.
e2._portfolio["peaks"] = {"A": 100.0, "B": 100.0}
e2._portfolio["frozen"] = {}
e2._portfolio["halted"] = False
e2._portfolio["halt_reason"] = ""
e2._portfolio["last_equity"] = {"A": 70.0, "B": 70.0}
ok, why = e2._circuit_breaker_check("A", 70.0, {"A": 70.0, "B": 70.0})
check("real fleet loss halts", not ok, why)
check("halt flag set", e2._portfolio.get("halted") is True, str(why))

# 3) once the fleet recovers, the latch MUST release on its own
e2._portfolio["last_equity"] = {"A": 100.0, "B": 100.0}
ok, why = e2._circuit_breaker_check("A", 100.0, {"A": 100.0, "B": 100.0})
check("halt releases automatically after recovery", ok, why)
check("halted flag cleared", not e2._portfolio.get("halted"))
check("halt_reason cleared", not e2._portfolio.get("halt_reason"))

print("== Partial reads must not seed the fleet peak ==")
e3 = _fresh_engine()
e3.PORTFOLIO_PATH = _pl.Path(tmp) / "pf4.json"
e3._portfolio = {"peaks": {}, "portfolio_peak": 0.0, "frozen": {},
                 "halted": False, "halt_reason": "", "refused": 0,
                 "refused_reasons": {}, "last_equity": {}}
e3._bets = []
# only one account ever seen -> no fleet peak may be locked in
e3._note_balances({"A": 100.0})
check("single-account read sets no fleet peak",
      float(e3._portfolio.get("portfolio_peak") or 0.0) == 0.0,
      str(e3._portfolio.get("portfolio_peak")))
# now both accounts are known: the peak may be established
e3._note_balances({"A": 100.0, "B": 100.0})
check("full-fleet read does set the peak",
      abs(float(e3._portfolio.get("portfolio_peak") or 0.0) - 200.0) < 0.01,
      str(e3._portfolio.get("portfolio_peak")))

print("== A refusal must always carry a reason ==")
# 2026-09-27: the halt-lift path cleared halt_reason and then fell through,
# so a later refusal could return (False, "") -- and the scheduler printed
# "no bet this round ()", hiding the actual cause. A blank reason is worse
# than no logging at all: it looks like a bug and tells the operator nothing.
for _pf, _bal, _label in (
        ({"peaks": {"A": 100.0}, "portfolio_peak": 100.0, "frozen": {},
          "halted": True, "halt_reason": "", "refused": 0,
          "refused_reasons": {}, "last_equity": {"A": 100.0}}, 100.0,
         "halted with blank reason"),
        ({"peaks": {"A": 100.0}, "portfolio_peak": 100.0, "frozen": {},
          "halted": True, "halt_reason": "", "refused": 0,
          "refused_reasons": {}, "last_equity": {}}, 100.0,
         "halted, no balance map")):
    e4 = _fresh_engine()
    e4.PORTFOLIO_PATH = _pl.Path(tmp) / "pf5.json"
    e4._portfolio = dict(_pf)
    e4._bets = []
    _allowed, _why = e4._circuit_breaker_check("A", _bal, {"A": _bal}
                                               if _label.endswith("reason") else None)
    if not _allowed:
        check(f"refusal states a reason ({_label})", bool(str(_why).strip()), repr(_why))
    else:
        check(f"blank halt_reason does not block a healthy fleet ({_label})", True)

print("== Stale 'active' rows must not inflate equity ==")
# A row the settlement sync never closed used to keep counting as money in
# play forever, which inflated equity, which inflated the recorded PEAK. The
# fleet could then never return to that fake high-water mark, so every later
# round looked like a catastrophic drawdown.
e5 = _fresh_engine()
e5._bets = [{"phone": "A", "stake": 40.0, "status": "active",
             "ts": time.time() - 72 * 3600}]
check("72h-old active row ignored", e5._active_stake_for("A") == 0.0,
      str(e5._active_stake_for("A")))
e5._bets = [{"phone": "A", "stake": 40.0, "status": "active",
             "ts": time.time() - 2 * 3600}]
check("2h-old active row still counts", abs(e5._active_stake_for("A") - 40.0) < 0.01)
e5._bets = [{"phone": "A", "stake": 40.0, "status": "active"}]
check("row with no timestamp treated as live",
      abs(e5._active_stake_for("A") - 40.0) < 0.01)
e5._bets = [{"phone": "A", "stake": 40.0, "status": "lost",
             "ts": time.time() - 60}]
check("settled row never counts", e5._active_stake_for("A") == 0.0)

# ── Structural guard: an "if refused: return skipped" must actually be
# conditional (2026-09-27). The portfolio-gate return sat at the same indent as
# its `if`, so it fired on EVERY round — including the rounds where the gates
# PASSED. `_open_betslip_and_place` was unreachable, so the engine reported
# "no bet this round ()" forever and placed nothing. A behavioural test needs a
# live browser, so assert the structure instead: every skipped-return in the bet
# path must live inside a negation guard.
print("== A refusal may only return from inside its guard ==")
import ast

_tree = ast.parse((_pl.Path(__file__).parent / "sportsape_backend.py").read_text(encoding="utf-8"))
_place = next((n for n in ast.walk(_tree)
               if isinstance(n, ast.FunctionDef) and n.name == "_place_one_bet"), None)
check("found _place_one_bet for structural check", _place is not None)
if _place is not None:
    guarded = set()
    for node in ast.walk(_place):
        if isinstance(node, ast.If):
            for sub in ast.walk(node):
                guarded.add(id(sub))
    loose = []
    for node in ast.walk(_place):
        if not isinstance(node, ast.Return) or id(node) in guarded:
            continue
        v = node.value
        if not isinstance(v, ast.Dict):
            continue
        keys = [k.value for k in v.keys if isinstance(k, ast.Constant)]
        if "skipped" in keys and "message" in keys:
            loose.append(node.lineno)
    check("no unguarded skipped-return can discard an approved slip",
          not loose, f"unguarded at lines {loose}")

print()
if fails:
    print(f"{len(fails)} FAILED: {fails}")
    sys.exit(1)
print("ALL PORTFOLIO CHECKS PASSED")
