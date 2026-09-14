"""
Run a win-sync for all saved phone numbers to import missing bets from the site.
This fixes the empty ledger problem by pulling the 10 bets that exist on SportPesa
but weren't saved locally.

Run ONCE: python run_sync.py
Then restart the GUI normally.
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

settings_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sportsape_settings.json")
s = json.load(open(settings_path, encoding="utf-8"))
phones   = s.get("phones") or [s.get("phone", "")]
password = s.get("password", "")
phones   = [p for p in phones if str(p).strip()]

if not phones or not password:
    print("No phone/password saved. Enter them in the GUI first.")
    sys.exit(1)

print(f"Running win-sync for {len(phones)} account(s): {', '.join(phones)}")
print()

from sportsape_backend import SportsapeBackend

b = SportsapeBackend()
b._load_ledger()

def log(m):
    print(f"  {m}")

for phone in phones:
    print(f"\n{'='*50}")
    print(f"Syncing: {phone}")
    print(f"{'='*50}")
    result = b.sync_winnings_now(phone, password, gui_callback=log)
    print(f"\nResult: {result.get('status')}")
    s2 = result.get("summary") or {}
    if isinstance(s2, dict):
        print(f"  Ledger: {s2.get('placed')} bets | won {s2.get('won')} | lost {s2.get('lost')} | active {s2.get('active')} | net KES {s2.get('net_profit', 0):+.2f}")

print("\n\nDone. Restart the GUI — the Ledger tab will now show the imported bets.")
