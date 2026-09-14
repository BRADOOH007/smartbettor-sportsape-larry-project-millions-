"""
Quick diagnostic: opens the SportPesa Bet History page in a VISIBLE browser,
waits for it to load, and prints what CSS selectors are actually present on the page.
Run: python test_bet_history.py
"""
import sys, os, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# Load credentials from saved settings
settings_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sportsape_settings.json")
try:
    settings = json.load(open(settings_path, encoding="utf-8"))
    phones = settings.get("phones") or [settings.get("phone", "")]
    password = settings.get("password", "")
    phone = phones[0] if phones else ""
except Exception as e:
    print(f"Could not read settings: {e}")
    sys.exit(1)

if not phone or not password:
    print("No phone/password in settings — please enter them in the GUI first")
    sys.exit(1)

print(f"Testing bet history for: {phone}")
print(f"URL: https://www.ke.sportpesa.com/bets/history")
print()

from sportsape_backend import SportsapeBackend

b = SportsapeBackend()

def log(m):
    print(f"  {m}")

# Build a visible driver
driver = b._build_driver(gui_callback=log, force_visible=True,
                          mobile=False, headless=False,
                          capture_perf=False, minimize=False)
try:
    b._ensure_bet_login(driver, phone, password, gui_callback=log)
    print()
    print("Navigating to bet history page...")
    b._safe_get(driver, b.BETS_HISTORY_URL)
    time.sleep(3.0)

    # Check what DOM elements are present
    result = driver.execute_script("""
var info = {
    url: window.location.href,
    title: document.title,
    bet_containers: document.querySelectorAll('.bet-container').length,
    bet_id: document.querySelectorAll('.bet_id').length,
    bet_date: document.querySelectorAll('.bet_date').length,
    bet_status: document.querySelectorAll('.bet_status').length,
    bet_amount: document.querySelectorAll('.bet_amount').length,
    bet_winnings: document.querySelectorAll('.bet_winnings').length,
    bet_description: document.querySelectorAll('.bet_description').length,
    // Try alternate selectors in case SportPesa changed their CSS
    slip_item: document.querySelectorAll('[class*="slip"]').length,
    ticket_item: document.querySelectorAll('[class*="ticket"]').length,
    history_item: document.querySelectorAll('[class*="history-item"]').length,
    bet_item: document.querySelectorAll('[class*="bet-item"]').length,
    // Sample the first few class names to see what's on the page
    sample_classes: Array.from(document.querySelectorAll('[class]'))
        .slice(0, 30)
        .map(function(el){ return el.className; })
        .filter(function(c){ return c && c.indexOf('bet') >= 0; })
        .slice(0, 10)
};
return info;
""")

    print()
    print("=== PAGE DIAGNOSTIC ===")
    print(f"URL:              {result.get('url')}")
    print(f"Title:            {result.get('title')}")
    print()
    print("=== EXPECTED SELECTORS ===")
    print(f".bet-container:   {result.get('bet_containers')} found")
    print(f".bet_id:          {result.get('bet_id')} found")
    print(f".bet_date:        {result.get('bet_date')} found")
    print(f".bet_status:      {result.get('bet_status')} found")
    print(f".bet_amount:      {result.get('bet_amount')} found")
    print(f".bet_winnings:    {result.get('bet_winnings')} found")
    print(f".bet_description: {result.get('bet_description')} found")
    print()
    print("=== ALTERNATE SELECTORS ===")
    print(f"[class*=slip]:         {result.get('slip_item')} found")
    print(f"[class*=ticket]:       {result.get('ticket_item')} found")
    print(f"[class*=history-item]: {result.get('history_item')} found")
    print(f"[class*=bet-item]:     {result.get('bet_item')} found")
    print()
    print("=== CLASSES CONTAINING 'bet' ON PAGE ===")
    for cls in (result.get('sample_classes') or []):
        print(f"  {cls}")

    # If the expected selectors returned 0, try scraping anyway
    if result.get('bet_containers', 0) == 0:
        print()
        print("⚠️  .bet-container not found — trying to read raw page structure...")
        # Get the first 2000 chars of inner text to see what's actually there
        body_sample = driver.execute_script(
            "return (document.body && document.body.innerText || '').substring(0, 2000);")
        print("Page text sample:")
        print(body_sample[:1000])
    else:
        print()
        print("✅  .bet-container found — running full extraction...")
        rows = b._extract_bet_history(driver, max_scroll=3)
        print(f"Extracted {len(rows)} bet rows:")
        for r in rows[:10]:
            print(f"  ID={r.get('id')}  Date={r.get('date')}  "
                  f"Status={r.get('status')}  "
                  f"Stake=KES{r.get('stake')}  Win=KES{r.get('win')}")

    input("\nPress Enter to close the browser...")
finally:
    try:
        driver.quit()
    except Exception:
        pass
