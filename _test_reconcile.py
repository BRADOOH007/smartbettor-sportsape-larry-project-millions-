"""Offline regression for the four money-integrity fixes, replaying the real
2026-09-28 overnight ledger rows against the real site history snapshot.

1. phantom writes are unconfirmed, not active
2. reconciliation claims each site id once (no duplicate id)
3. reconciliation adopts the SITE's leg count
4. stale unconfirmed rows are reaped to not_placed and release stake
5. exposure counts unconfirmed conservatively; reaped phantoms release it
6. settlement/ROI ignore unconfirmed and not_placed
"""
import json
import os
import shutil
import sys
import time
from datetime import datetime, timedelta

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, r"C:\Users\Home\Desktop\ALL FILES\sportsape")
import sportsape_backend as sb

TMP = r"C:\Users\Home\AppData\Local\Temp\opencode\regress"
if os.path.isdir(TMP):
    shutil.rmtree(TMP, ignore_errors=True)
os.makedirs(TMP, exist_ok=True)

SITE = [
    {"id": "5623", "date": "28/09/26 00:38", "legs": 2, "stake": 10.0, "win": 12.34, "status": "WON"},
    {"id": "5871", "date": "28/09/26 00:47", "legs": 2, "stake": 10.0, "win": 20.49, "status": "NOT WON"},
    {"id": "4915", "date": "28/09/26 00:55", "legs": 3, "stake": 10.0, "win": 30.03, "status": "NOT WON"},
    {"id": "8860", "date": "28/09/26 01:45", "legs": 3, "stake": 10.0, "win": 12.48, "status": "WON"},
    {"id": "9328", "date": "28/09/26 01:53", "legs": 2, "stake": 5.0,  "win": 8.00,  "status": "WON"},
    {"id": "8892", "date": "28/09/26 02:00", "legs": 2, "stake": 5.0,  "win": 6.39,  "status": "ACTIVE"},
    {"id": "2292", "date": "28/09/26 02:08", "legs": 2, "stake": 5.0,  "win": 6.28,  "status": "ACTIVE"},
    {"id": "1420", "date": "28/09/26 02:14", "legs": 3, "stake": 5.0,  "win": 9.17,  "status": "ACTIVE"},
    {"id": "9522", "date": "28/09/26 02:22", "legs": 3, "stake": 10.0, "win": 15.83, "status": "CashOut ACTIVE"},
    {"id": "2233", "date": "28/09/26 02:30", "legs": 3, "stake": 10.0, "win": 20.81, "status": "ACTIVE"},
]

fails = []


def check(name, cond, detail=""):
    print(("  PASS  " if cond else "  FAIL  ") + name + ("" if cond else "  <- " + str(detail)))
    if not cond:
        fails.append(name)


def new_bk():
    return sb.SportsapeBackend(headless=True, verbose=False)


def run_sync(bk, rows, monkey_rows=True):
    """Drive _monitor_and_sync_winnings' body with a fixed history."""
    import sportsape_backend as M
    orig_get = M.SportsapeBackend._safe_get
    orig_ext = M.SportsapeBackend._extract_bet_history
    orig_emit = M.SportsapeBackend._emit_direct
    M.SportsapeBackend._safe_get = lambda *a, **k: None
    M.SportsapeBackend._extract_bet_history = lambda self, d=None, **k: list(rows)
    M.SportsapeBackend._emit_direct = lambda *a, **k: None
    M.SportsapeBackend._auto_cashout_pass = lambda *a, **k: None
    try:
        bk._bets_dir = TMP
        bk._monitor_and_sync_winnings(None)
    finally:
        M.SportsapeBackend._safe_get = orig_get
        M.SportsapeBackend._extract_bet_history = orig_ext
        M.SportsapeBackend._emit_direct = orig_emit


PHONE = "0706719388"
D = "2026-09-28"


def local_row(hm, stake, legs, possible_win, status, bid=None):
    return {
        "id": bid, "phone": PHONE,
        "placed_at": f"{D}T{hm}:00",
        "legs": legs, "stake": stake, "odds": 2.0,
        "possible_win": possible_win, "markets": [], "probs": [], "game_ids": [],
        "leg_names": [], "status": status, "unconfirmed_at": f"{D}T{hm}:00",
        "settled_at": None,
    }


print("\n=== 1. phantom write is unconfirmed, not active ===")
bk = new_bk()
bk._bets = []
bk._record_bet_from_result({"placed_at": f"{D}T03:00:00", "legs": 2, "stake": 10.0,
                            "odds": 2.0, "possible_win": 20.0, "markets": [],
                            "probs": [], "game_ids": [], "leg_names": []}, PHONE)
r0 = bk._bets[0]
check("fresh placement status == unconfirmed", r0["status"] == "unconfirmed", r0["status"])
check("fresh placement carries unconfirmed_at", bool(r0.get("unconfirmed_at")))
check("exposure counts unconfirmed (conservative)",
      abs(bk._active_stake_for(PHONE) - 10.0) < 0.01, bk._active_stake_for(PHONE))
s = bk._ledger_summary()
check("unconfirmed is not counted as settled", s["won"] == 0 and s["lost"] == 0, s)

print("\n=== 2/3. reconciliation: one id per site row, site legs adopted ===")
# 12 local rows exactly like the real ledger: 10 real, 2 phantoms.
bk2 = new_bk()
rows = [
    local_row("00:04", 10.0, 3, 30.0, "unconfirmed"),   # phantom
    local_row("00:38", 10.0, 3, 12.34, "unconfirmed"),  # site says legs=2 (we remembered 3)
    local_row("00:17", 10.0, 3, 25.0, "unconfirmed"),   # phantom
    local_row("00:47", 10.0, 3, 20.49, "unconfirmed"),
    local_row("00:55", 10.0, 3, 30.03, "unconfirmed"),
    local_row("01:45", 10.0, 3, 12.48, "unconfirmed"),
    local_row("01:53", 5.0, 3, 8.00, "unconfirmed"),
    local_row("02:00", 5.0, 3, 6.39, "unconfirmed"),
    local_row("02:08", 5.0, 3, 6.28, "unconfirmed"),
    local_row("02:14", 5.0, 3, 9.17, "unconfirmed"),
    local_row("02:22", 10.0, 3, 15.83, "unconfirmed"),
    local_row("02:30", 10.0, 3, 20.81, "unconfirmed"),
]
bk2._bets = rows
run_sync(bk2, SITE)

ids = [str(b.get("id")) for b in bk2._bets if b.get("id")]
check("all 10 real site rows claimed", len(ids) == 10, ids)
check("no site id claimed twice", len(ids) == len(set(ids)), ids)
check("exactly the 2 phantoms unmatched", len(bk2._bets) - len(ids) == 2)
m = {str(b["id"]): b for b in bk2._bets if b.get("id")}
check("8860 now belongs to the 01:45 bet",
      m.get("8860", {}).get("placed_at", "").endswith("01:45:00"), m.get("8860", {}).get("placed_at"))
check("5871 now belongs to the 00:47 bet",
      m.get("5871", {}).get("placed_at", "").endswith("00:47:00"), m.get("5871", {}).get("placed_at"))
check("site leg count adopted (5623 -> 2 legs, local remembered 3)",
      int(m.get("5623", {}).get("legs", 0)) == 2, m.get("5623", {}).get("legs"))
check("site leg count adopted (2233 -> 3 legs)",
      int(m.get("2233", {}).get("legs", 0)) == 3, m.get("2233", {}).get("legs"))
check("settled rows take the site status (5871 lost)",
      m.get("5871", {}).get("status") == "lost", m.get("5871", {}).get("status"))
check("settled rows take the site status (5623 won)",
      m.get("5623", {}).get("status") == "won", m.get("5623", {}).get("status"))
check("live row keeps an open status (2233)",
      m.get("2233", {}).get("status") in ("active", "unconfirmed"), m.get("2233", {}).get("status"))
check("unconfirmed_at cleared once confirmed",
      all("unconfirmed_at" not in m[k] for k in m))
exp = bk2._active_stake_for(PHONE)
check("exposure == only the 5 live site bets (35.0)", abs(exp - 35.0) < 0.01, exp)
s2 = bk2._ledger_summary()
check("summary excludes reaped phantoms from active",
      s2.get("unplaced", 0) == 2, s2)
check("summary won == 3", s2["won"] == 3, s2)
check("summary lost == 2", s2["lost"] == 2, s2)
check("summary net excludes phantom stake (staked 80)", abs(s2["staked"] - 80.0) < 0.01, s2["staked"])

print("\n=== 4. stale unconfirmed rows are reaped ===")
bk3 = new_bk()
old = (datetime.now() - timedelta(minutes=40)).isoformat(timespec="seconds")
bk3._bets = [
    {"id": None, "phone": PHONE, "placed_at": old, "unconfirmed_at": old, "legs": 3,
     "stake": 10.0, "odds": 2.0, "possible_win": 25.0, "status": "unconfirmed"},
    {"id": None, "phone": PHONE,
     "placed_at": datetime.now().isoformat(timespec="seconds"), "legs": 3,
     "stake": 10.0, "odds": 2.0, "possible_win": 25.0, "status": "unconfirmed"},
]
# A non-empty history that simply does NOT contain these two slips: proof the
# bookmaker never accepted them.
run_sync(bk3, SITE)
stale = bk3._bets[0]
check("stale unconfirmed -> not_placed", stale["status"] == "not_placed", stale["status"])
check("reaped row releases its stake", float(stale["stake"]) == 0.0, stale["stake"])
check("reaped row keeps an audit note", bool(stale.get("reconcile_note")))
check("fresh unconfirmed is NOT reaped", bk3._bets[1]["status"] == "unconfirmed",
      bk3._bets[1]["status"])
check("exposure after reaping == 10 (fresh only)",
      abs(bk3._active_stake_for(PHONE) - 10.0) < 0.01, bk3._active_stake_for(PHONE))
check("reaped row absent from summary active",
      bk3._ledger_summary()["active"] == 1, bk3._ledger_summary())

print("\n=== 5. settle-once guard: re-running sync does not double-count ===")
bk4 = new_bk()
bk4._bets = [local_row("00:38", 10.0, 3, 12.34, "unconfirmed")]
before = bk4._ledger_summary()
run_sync(bk4, SITE)
first = bk4._ledger_summary()
run_sync(bk4, SITE)
second = bk4._ledger_summary()
check("first sync settles 1 win", first["won"] == 1, first)
check("re-sync does not double count", second["won"] == 1 and second["staked"] == first["staked"],
      (first, second))

print("\n=== 6. balance guard: never answer for the wrong account ===")
bal = new_bk()
check("_read_balance_confirmed documents the account-safety guard",
      "ACCOUNT SAFETY" in (bal._read_balance_confirmed.__doc__ or ""))

# Drive the guard for real: ask for an account while the session is provably
# someone else, and confirm it refuses rather than returning that other number.
calls = {"session_reads": 0}


class _FakeDrv:
    """A live session belonging to 0706719388 that reports 55.29."""


bkbal = new_bk()
bkbal._who_is_logged_in = lambda d: "0706719388"
bkbal._api_login = lambda ph, pw, retries=2: {"ok": True, "balance": 94.73}
bkbal._extract_wallet_snapshot_from_sportpesa_api = lambda d: {"balance": 55.29}
bkbal._read_balance_patient = lambda d, wait=0: 55.29
bkbal._extract_wallet_snapshot_from_page = lambda d: {"balance": 55.29}

same, ok_same = bkbal._read_balance_confirmed(_FakeDrv(), 5, phone="0706719388",
                                              password="x")
check("session's own account is read correctly", ok_same and abs(same - 94.73) < 0.01 or
      (ok_same and abs(same - 55.29) < 0.01), (same, ok_same))

other, ok_other = bkbal._read_balance_confirmed(_FakeDrv(), 5, phone="0798810080",
                                                password="x")
check("different account gets ITS OWN balance (94.73), not 55.29",
      ok_other and abs(other - 94.73) < 0.01, (other, ok_other))

# Now the dangerous case: the per-account API fails (network down) while the
# session is logged into someone else. Returning 55.29 here is the bug.
bkbal2 = new_bk()
bkbal2._who_is_logged_in = lambda d: "0706719388"
bkbal2._api_login = lambda ph, pw, retries=2: {"ok": False}
bkbal2._extract_wallet_snapshot_from_sportpesa_api = lambda d: {"balance": 55.29}
bkbal2._read_balance_patient = lambda d, wait=0: 55.29
bkbal2._extract_wallet_snapshot_from_page = lambda d: {"balance": 55.29}
v, ok_v = bkbal2._read_balance_confirmed(_FakeDrv(), 5, phone="0798810080",
                                         password="x")
check("refuses rather than reporting another account's balance",
      (not ok_v) and v == 0.0, (v, ok_v))

print("\n" + ("ALL REGRESSION CHECKS PASSED" if not fails else f"{len(fails)} FAILED: {fails}"))
sys.exit(1 if fails else 0)
