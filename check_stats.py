import json, os, time
from datetime import datetime

base = os.path.dirname(os.path.abspath(__file__))

def load(f):
    p = os.path.join(base, f)
    if os.path.exists(p):
        return json.load(open(p, encoding='utf-8'))
    return {}

st  = load('sportsape_stats.json')
led = load('sportsape_ledger.json') or []
cal = load('sportsape_calibration.json')
sup = load('sportsape_supervisor.json')
cache = load('sportsape_agent_cache.json')

print("="*60)
print("STATS FILE")
print("="*60)
print(f"  Settled (stats): {st.get('settled', 0)}")
print(f"  Savings pool:    KES {st.get('savings_pool', 0)}")
print(f"  Last recalib:    {st.get('last_recalib', 'never')}")
print(f"  Retired markets: {st.get('retired_markets', [])}")

mt = st.get('market_types') or {}
if mt:
    print("\n  Market performance:")
    for mk, e in sorted(mt.items(), key=lambda x: float(x[1].get('won',0))/max(1,int(x[1].get('trials',1))), reverse=True):
        t = int(e.get('trials', 0))
        w = float(e.get('won', 0))
        if t == 0:
            continue
        hit  = w / t
        pred = float(e.get('expected', 0)) / t
        wt   = float(e.get('weight', 1.0))
        ret  = mk in (st.get('retired_markets') or [])
        print(f"    {mk:12}: {t:3} trials  hit {hit:.0%}  pred {pred:.0%}  weight {wt:.2f}  {'RETIRED' if ret else ''}")

recs = [(k, v) for k, v in (st.get('recipes') or {}).items() if int(v.get('trials', 0)) >= 1]
recs.sort(key=lambda x: (float(x[1].get('ret', 0)) - float(x[1].get('stake', 0))) / max(0.01, float(x[1].get('stake', 0))), reverse=True)
if recs:
    print("\n  Top recipes by ROI:")
    for k, v in recs[:5]:
        t = int(v.get('trials', 0))
        w = int(v.get('won', 0))
        stk = float(v.get('stake', 0))
        ret = float(v.get('ret', 0))
        roi = (ret - stk) / stk if stk else 0
        print(f"    {k}: {w}/{t} won  ROI {roi:+.0%}  staked KES {stk:.0f}")

print("\n" + "="*60)
print("LEDGER")
print("="*60)
real   = [b for b in led if not str(b.get('status', '')).startswith('shadow') and float(b.get('stake', 0)) > 0]
shadow = [b for b in led if str(b.get('status', '')).startswith('shadow')]
won    = [b for b in real if b.get('status') == 'won']
lost   = [b for b in real if b.get('status') == 'lost']
active = [b for b in real if b.get('status') == 'active']
staked   = sum(float(b.get('stake', 0)) for b in real)
returned = sum(float(b.get('won_amount') or b.get('possible_win', 0)) for b in won)
net = returned - staked
print(f"  Total entries:  {len(led)}")
print(f"  Real bets:      {len(real)}")
print(f"  Won:            {len(won)}")
print(f"  Lost:           {len(lost)}")
print(f"  Active:         {len(active)}")
print(f"  Shadow (learn): {len(shadow)}")
print(f"  Staked:         KES {staked:.2f}")
print(f"  Returned:       KES {returned:.2f}")
print(f"  Net P&L:        KES {net:+.2f}")
if staked > 0:
    print(f"  ROI:            {net/staked:+.1%}")

print("\n" + "="*60)
print("CALIBRATION")
print("="*60)
print(f"  Settled: {cal.get('settled', 0)}")
print(f"  Generated: {cal.get('generated_at', 'never')}")
for bk, bv in (cal.get('buckets') or {}).items():
    n = bv.get('n')
    if n:
        print(f"  bucket {bk}: n={n}  hit={bv.get('hit')}  expected={bv.get('avg_expected')}  delta={bv.get('delta')}")

pm = cal.get('per_market') or {}
if pm:
    print("  Per market:")
    for mk, mv in pm.items():
        n = mv.get('n', 0)
        if n:
            print(f"    {mk:12}: n={n}  hit_pct={mv.get('hit_pct')}%  pred_pct={mv.get('pred_pct')}%")

print("\n" + "="*60)
print("ANALYST ACCURACY (cache)")
print("="*60)
aa = cache.get('analyst_accuracy') or {}
if aa:
    for bucket, e in sorted(aa.items()):
        n = e.get('n', 0)
        w = e.get('wins', 0)
        rate = w/n if n else 0
        print(f"  conf {bucket}: {w}/{n} = {rate:.0%}")
else:
    print("  No analyst accuracy data yet.")

games = cache.get('games') or {}
fresh = [g for g in games.values() if isinstance(g, dict) and g.get('pick') and g.get('pick') != 'skip']
print(f"  Fresh analyst picks in cache: {len(fresh)}")
for g in fresh[:5]:
    print(f"    {g.get('name', '?')[:40]} -> {g.get('pick')} (prob {g.get('prob'):.0%} conf {g.get('confidence'):.0%})")

print("\n" + "="*60)
print("SUPERVISOR / FIBI")
print("="*60)
lp = float(sup.get('last_placed_ts', 0))
lr = float(sup.get('last_round_ts', 0))
if lp:
    print(f"  Last bet placed: {round((time.time()-lp)/60)} min ago")
if lr:
    print(f"  Last round:      {round((time.time()-lr)/60)} min ago")
print(f"  Consec aborts:   {sup.get('consecutive_aborts', 0)}")
print(f"  Parked:          {sup.get('parked_since', {})}")

hb = sup.get('agent_heartbeats') or {}
if hb:
    print("  Agent heartbeats (min ago):")
    for agent, ts in sorted(hb.items()):
        age_min = round((time.time() - float(ts)) / 60)
        print(f"    {agent:20}: {age_min} min ago")
