"""Verify the GUI tag mapping + summary paths for the new unconfirmed/not_placed
states using the same fake objects the fleet test builds, without a display.
"""
import sys
import time
from datetime import datetime, timedelta

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, r"C:\Users\Home\Desktop\ALL FILES\sportsape")
import sportsape_backend as sb

fails = []


def check(name, cond, detail=""):
    print(("  PASS  " if cond else "  FAIL  ") + name + ("" if cond else "  <- " + str(detail)))
    if not cond:
        fails.append(name)


PH = "0700000001"
now = datetime.now().isoformat(timespec="seconds")
old = (datetime.now() - timedelta(hours=3)).isoformat(timespec="seconds")

bk = sb.SportsapeBackend(headless=True, verbose=False)
bk._bets = [
    {"id": "1", "phone": PH, "placed_at": now, "legs": 2, "stake": 10.0, "status": "won",
     "won_amount": 14.0, "possible_win": 14.0, "markets": []},
    {"id": "2", "phone": PH, "placed_at": now, "legs": 2, "stake": 10.0, "status": "lost",
     "possible_win": 14.0, "markets": []},
    {"id": "3", "phone": PH, "placed_at": now, "legs": 2, "stake": 10.0,
     "status": "unconfirmed", "unconfirmed_at": now, "possible_win": 20.0, "markets": []},
    {"id": None, "phone": PH, "placed_at": old, "legs": 2, "stake": 0.0,
     "status": "not_placed", "reconcile_note": "no match", "possible_win": 20.0, "markets": []},
]

s = bk._ledger_summary()
check("won counted", s["won"] == 1, s)
check("lost counted", s["lost"] == 1, s)
check("unconfirmed counted as active (at risk)", s["active"] == 1, s)
check("not_placed counted separately, not active", s.get("unplaced") == 1, s)
check("staked excludes reaped phantom", abs(s["staked"] - 30.0) < 0.01, s["staked"])
check("net = 14 return - 30 staked", abs(s["net_profit"] - (14.0 - 30.0)) < 0.01, s["net_profit"])
check("exposure == the 1 unconfirmed stake", abs(bk._active_stake_for(PH) - 10.0) < 0.01,
      bk._active_stake_for(PH))

print("\n== stale-exposure guard still forces old 'active' rows out of equity ==")
bk2 = sb.SportsapeBackend(headless=True, verbose=False)
stale = (datetime.now() - timedelta(hours=48)).isoformat(timespec="seconds")
bk2._bets = [
    {"phone": PH, "stake": 40.0, "status": "active", "placed_at": stale, "possible_win": 50.0},
    {"phone": PH, "stake": 10.0, "status": "unconfirmed",
     "unconfirmed_at": now, "placed_at": now, "possible_win": 20.0},
]
exp = bk2._active_stake_for(PH)
check("36h+ stale 'active' row excluded, fresh unconfirmed kept",
      abs(exp - 10.0) < 0.01, exp)

print("\n== projected balance subtracts unconfirmed stake ==")
# _est_balance_for works off the cash cache, so seed one at KES 100. Use only the
# unconfirmed row: a settled/lost row's stake is already reflected in cash, while
# an unconfirmed slip's money is still in flight.
bk3 = sb.SportsapeBackend(headless=True, verbose=False)
bk3._bets = [
    {"phone": PH, "stake": 10.0, "status": "unconfirmed",
     "unconfirmed_at": now, "placed_at": now, "possible_win": 20.0},
]
bk3._balance_cache = {PH: {"balance": 100.0, "ts": time.time(), "confirmed": True}}
est, src = bk3._est_balance_for(PH)
check("estimate reduces the base by the unconfirmed stake",
      abs(est - (100.0 - 10.0)) < 0.01, (est, src))

print("\n== grace constant is a sane, non-zero window ==")
g = sb.SportsapeBackend.UNCONFIRMED_GRACE_SEC
check("grace > 0 and <= 60 min", 0 < g <= 3600, g)
check("match window is tighter than the legacy 2h window",
      sb.SportsapeBackend.LEDGER_MATCH_WINDOW_SEC <= 7200,
      sb.SportsapeBackend.LEDGER_MATCH_WINDOW_SEC)

print("\n" + ("ALL STATE CHECKS PASSED" if not fails else f"{len(fails)} FAILED: {fails}"))
sys.exit(1 if fails else 0)
