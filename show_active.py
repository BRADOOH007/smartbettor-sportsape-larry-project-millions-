import json
led = json.load(open('sportsape_ledger.json'))
active = [b for b in led if b.get('status')=='active' and float(b.get('stake',0))>0]
print(f'Active bets: {len(active)}')
for b in active:
    mk = ','.join(b.get('markets',[])[:5])
    probs = [round(p*100) for p in (b.get('probs') or [])[:5]]
    bid = b.get('id') or '?'
    odds = b.get('odds', 0)
    stake = b.get('stake', 0)
    pw = b.get('possible_win', 0)
    pa = str(b.get('placed_at',''))[:16]
    combined_p = 1.0
    for p in (b.get('probs') or []):
        combined_p *= float(p)
    print(f"  #{bid} {pa} x{odds} stake=KES{stake} win=KES{pw:.0f} legs={len(b.get('markets',[]))} combined_prob={combined_p:.0%}")
    print(f"    markets: {mk}")
    print(f"    probs:   {probs}%")
