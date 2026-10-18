# -*- coding: utf-8 -*-
"""Prove the fixture exclusion works against the real seeded ledger.

The old behaviour is shown side by side so the difference is visible, not
asserted.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
os.chdir(ROOT)

import betflow as bf

LEDGER = os.path.join(os.path.expanduser("~"), "Desktop",
                      "betflow_ledger.json")
rows = json.load(open(LEDGER, encoding="utf-8"))

print("=" * 70)
print("CANONICAL LEDGER")
print("=" * 70)
print(f"  {LEDGER}")
print(f"  {len(rows)} rows, KES {sum(r.get('stake', 0) for r in rows):,.2f} staked")
for r in rows:
    print(f"    {r['placed_at']}  {r['phone']}  KES {r['stake']:.2f}  "
          f"x{r.get('odds')}  {r.get('status')}")

used = bf.games_bet_today(rows)
print()
print("=" * 70)
print("  EXCLUSION SET BUILT FROM IT")
print("=" * 70)
for k in sorted(used):
    print(f"    {k}")

# A board that deliberately leads with the two already-bet fixtures, which is
# exactly what the live board does - they sort to the top.
board = [
    {"gid": "1", "home": "FC AGUABLANCA", "away": "REAL CARTAGENA",
     "odds": {"1X2#2": 1.58, "OVER#1": 1.30, "OVER#2": 1.44}, "ko": ""},
    {"gid": "2", "home": "FLAMENGO RJ U20", "away": "VASCO DA GAMA RJ U20",
     "odds": {"1X2#0": 2.45, "OVER#1": 1.38, "OVER#2": 1.44}, "ko": ""},
    {"gid": "3", "home": "PORTMORE UNITED", "away": "WATERHOUSE FC",
     "odds": {"1X2#2": 2.45, "OVER#1": 1.45, "OVER#2": 1.37}, "ko": ""},
    {"gid": "4", "home": "SAO PAULO U20", "away": "ATLETICO PR U20",
     "odds": {"1X2#0": 1.82, "OVER#1": 1.23, "OVER#2": 1.83}, "ko": ""},
    {"gid": "5", "home": "MAGHREB FES", "away": "RAJA CASABLANCA",
     "odds": {"1X2#0": 2.24, "OVER#1": 1.30, "OVER#2": 1.60}, "ko": ""},
    {"gid": "6", "home": "VARGAS TORRES", "away": "LDU PORTOVIEJO",
     "odds": {"1X2#0": 1.96, "OVER#1": 1.22, "OVER#2": 1.71}, "ko": ""},
]


def keys(legs):
    # Same format the engine builds in games_bet_today(): "HOME|AWAY" upper.
    return {f"{l['home'].strip().upper()}|{l['away'].strip().upper()}"
            for l in legs}


print()
print("=" * 70)
print("OLD BEHAVIOUR  -  pick_legs(games, 2)")
print("=" * 70)
old = bf.pick_legs(board, 2)
for l in old:
    print(f"    {l['home']} vs {l['away']}  [{l['market']}] @ {l['odds']}")
old_keys = keys(old)
repeats_old = old_keys & used
print(f"  repeats a fixture already bet today: {bool(repeats_old)}"
      + (f"  -> {sorted(repeats_old)}" if repeats_old else ""))

print()
print("=" * 70)
print("NEW BEHAVIOUR  -  pick_legs(games, 2, exclude=games_bet_today())")
print("=" * 70)
new = bf.pick_legs(board, 2, exclude=used)
for l in new:
    print(f"    {l['home']} vs {l['away']}  [{l['market']}] @ {l['odds']}")
new_keys = keys(new)
repeats_new = new_keys & used
print(f"  repeats a fixture already bet today: {bool(repeats_new)}")

print()
print("=" * 70)
verdict = (not repeats_new) and (bool(repeats_old) or bool(new))
print("VERDICT: " + ("exclusion works - it changed the pick and no repeats"
                     if verdict else "check the output above"))
print("=" * 70)

# Also prove it stands down rather than repeating when nothing else is left.
print()
print("=" * 70)
print("EXHAUSTION: only already-bet fixtures on the board")
print("=" * 70)
only_used = [board[0], board[2]]
none = bf.pick_legs(only_used, 2, exclude=used)
print(f"  legs returned: {len(none)}")
print(f"  {'PASS - stands down instead of repeating' if not none else 'FAIL - it repeated'}")

# And prove settle_verdict refuses to call a bet placed when nothing moved.
print()
print("=" * 70)
print("SETTLE VERDICT (no browser):")
print("=" * 70)
cases = [("money moved  -> confirmed",
          (100.0, 90.5, {"count_after": 0, "status": "200"}), (True, False)),
         ("slip emptied, no move -> SUSPICIOUS",
          (100.0, 100.0, {"count_after": 0}), (True, True)),
         ("http 200, no move -> SUSPICIOUS",
          (100.0, 100.0, {"count_after": 1, "status": "200"}), (True, True)),
         ("nothing corroborates -> NOT placed",
          (100.0, 100.0, {"count_after": 1}), (False, False)),
         ("malformed status -> no crash",
          (100.0, 100.0, {"count_after": 1, "status": "abc"}), (False, False))]
for name, (before, after, res), want in cases:
    got = bf.settle_verdict(before, after, res)
    ok = got == want
    print(f"  {'PASS' if ok else 'FAIL'}  {name}: got {got}, want {want}")
    if not ok:
        raise SystemExit(1)
print("  all settle_verdict checks PASS")