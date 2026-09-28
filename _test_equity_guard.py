"""Regression: a zero/unreadable balance must never become an equity reading.
Before the fix this wrote equity = 0 + open_stake, which reads as a ~50% fleet
drawdown and latches a portfolio halt on a healthy account.
"""
import json
import os
import shutil
import sys
import time

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, r"C:\Users\Home\Desktop\ALL FILES\sportsape")
import sportsape_backend as sb

fails = []


def check(name, cond, detail=""):
    print(("  PASS  " if cond else "  FAIL  ") + name + ("" if cond else "  <- " + str(detail)))
    if not cond:
        fails.append(name)


TMP = r"C:\Users\Home\AppData\Local\Temp\opencode\eqtest"
shutil.rmtree(TMP, ignore_errors=True)
os.makedirs(TMP, exist_ok=True)
PF = os.path.join(TMP, "pf.json")


def fresh(equity, peak):
    json.dump({"peaks": {"A": peak, "B": 100.0}, "portfolio_peak": peak + 100.0,
               "frozen": {}, "halted": False, "halt_reason": "", "refused": 0,
               "refused_reasons": {}, "last_equity": dict(equity)}, open(PF, "w"))
    e = sb.SportsapeBackend(headless=True, verbose=False)
    e.PORTFOLIO_PATH = __import__("pathlib").Path(PF)
    return e


A, B = "A", "B"
NOW = "2026-09-28T11:00:00"

print("== a zero reading must not overwrite a good equity ==")
e = fresh({"A": 90.0, "B": 100.0}, 90.0)
e._bets = [{"id": "1", "phone": A, "stake": 15.0, "status": "active", "placed_at": NOW}]
e._note_balances({A: 0.0, B: 100.0})   # A unreadable
pf = json.load(open(PF))
check("A's equity kept at 90.00 (not rewritten to 15.00)",
      pf["last_equity"]["A"] == 90.0, pf["last_equity"])
check("A's peak untouched", pf["peaks"]["A"] == 90.0, pf["peaks"])
check("no halt latched from the false zero", not pf["halted"], pf.get("halt_reason"))

print("\n== a genuine low-but-positive reading IS recorded ==")
e = fresh({"A": 90.0, "B": 100.0}, 90.0)
e._bets = []
e._note_balances({A: 12.5, B: 100.0})
pf = json.load(open(PF))
check("A equity tracks the real 12.50", pf["last_equity"]["A"] == 12.5, pf["last_equity"])

print("\n== an account with NO prior reading and a zero is skipped, not zeroed ==")
e = fresh({"B": 100.0}, 90.0)
e._bets = [{"id": "1", "phone": A, "stake": 15.0, "status": "active", "placed_at": NOW}]
e._note_balances({A: 0.0, B: 100.0})
pf = json.load(open(PF))
check("no false 15.00 equity written for a never-read account",
      pf["last_equity"].get("A") is None, pf["last_equity"])

print("\n== end-to-end: a false zero no longer manufactures a halt ==")
e = fresh({"A": 90.0, "B": 100.0}, 90.0)
e._bets = [{"id": "1", "phone": A, "stake": 15.0, "status": "active", "placed_at": NOW}]
# Round 1: A reads fine.
e._note_balances({A: 90.0, B: 100.0})
ok1, _ = e._circuit_breaker_check(A, 90.0, {A: 90.0, B: 100.0})
check("healthy round places", ok1)
good_eq = json.load(open(PF))["last_equity"]["A"]
# Round 2: A's read fails -> must NOT look like a 50% loss.
e._note_balances({A: 0.0, B: 100.0})
ok2, why2 = e._circuit_breaker_check(A, 90.0, {A: 90.0, B: 100.0})
check("failed read does not halt the fleet", ok2, why2)
pf = json.load(open(PF))
check("still not halted", not pf["halted"], pf.get("halt_reason"))
check("A equity preserved across the failed read (not reset to open-stake-only)",
      pf["last_equity"]["A"] == good_eq, (pf["last_equity"], good_eq))

print("\n== peak still ratchets up on a real gain ==")
e = fresh({"A": 90.0, "B": 100.0}, 90.0)
e._bets = []
e._note_balances({A: 120.0, B: 100.0})
pf = json.load(open(PF))
check("peak ratcheted to 120.00", pf["peaks"]["A"] == 120.0, pf["peaks"])

shutil.rmtree(TMP, ignore_errors=True)
print("\n" + ("ALL EQUITY-GUARD CHECKS PASSED" if not fails else f"{len(fails)} FAILED: {fails}"))
sys.exit(1 if fails else 0)
