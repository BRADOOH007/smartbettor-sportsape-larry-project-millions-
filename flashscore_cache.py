# -*- coding: utf-8 -*-
"""flashscore_cache.py - Flashscore head-to-head / form layer for BetFlow.

WHY THIS REPLACES FOREBET
-------------------------
Forebet's site hardened against plain HTTP (403, measured 2026-10-10) and then
redesigned, so its local cache had gone stale and the "second opinion" gate had
been silently neutral - no cache means no opinion means every leg sails
through. Flashscore renders the same class of independent data in a
browser-reachable DOM, and for the markets this engine actually bets
(over/under, btts, 1x2/DNB) its HEAD-TO-HEAD rows are a signal on the pairing
itself rather than a generic league average.

COST SHAPE: the site is JS-rendered and Cloudflare-fronted, so every page comes
through a real headless Chrome. That is only affordable for a SHORTLIST - the
pairings from the machine's last board - fetched inside the pacing gap, one
page per pairing. A missing/stale cache is neutral: the picker behaves exactly
as if no second opinion existed.

Cache: Desktop/flashscore_cache.json, keyed "HOME|AWAY" with the derived
expectations. Any failure leaves the previous cache untouched.
"""
from __future__ import annotations

import json
import re
import time
from datetime import datetime
from pathlib import Path

BOARD_URL = "https://www.flashscore.com/football/"
MAX_TTL = 30.0 * 3600.0          # same staleness budget forebet had
H2H_MIN_MEETINGS = 2             # below this a pairing is neutral
LAPLACE = 2.0                    # smoothing strength toward 0.5
DEEP_CRAWL_LIMIT = 6             # pairings that also get standings + news


def _live_dir() -> Path:
    desk = Path.home() / "Desktop"
    if (desk / "sportsape_settings.json").exists():
        return desk
    return Path(__file__).resolve().parent


LIVE = _live_dir()
OUT = LIVE / "flashscore_cache.json"
_CACHE: dict = {"at": 0.0, "data": None}


def log(msg: str) -> None:
    print(f"[{datetime.now():%H:%M:%S}] flashscore: {msg}", flush=True)


def _norm(name: str) -> str:
    s = re.sub(r"[^A-Za-z0-9 ]", " ", str(name or "").upper())
    return " ".join(s.split())


# A head-to-head row: "01.02.26 PL Nottingham Crystal Palace 1 1"
# date, competition, <both names>, home goals, away goals.
_H2H_ROW = re.compile(r"^\s*(\d{2}\.\d{2}\.\d{2})\s+(.+?)\s+(\d+)\s+(\d+)\s*$")


def parse_h2h_rows(texts, home: str, away: str) -> list:
    """Turn rendered H2H row texts into [{hg, ag, home, away}] for THIS pairing.

    `texts` are the row innerTexts; `home`/`away` are the pairing's team names
    from our board. A row only counts when both names appear in it - that is
    what aligns the score columns, whatever the row's own ordering.
    """
    out = []
    h_key, a_key = _norm(home), _norm(away)
    for t in texts or []:
        m = _H2H_ROW.match(str(t))
        if not m:
            continue
        mid = m.group(2)
        ih, ia = mid.upper().find(h_key), mid.upper().find(a_key)
        if ih < 0 or ia < 0:
            continue                       # a meeting between other teams
        try:
            s1, s2 = int(m.group(3)), int(m.group(4))
        except ValueError:
            continue
        row_home = home if ih < ia else away
        out.append({"hg": s1 if ih < ia else s2,
                    "ag": s2 if ih < ia else s1,
                    "home": row_home, "away": away if ih < ia else home})
    return out


def meetings_to_signal(meetings: list) -> dict | None:
    """Historical meetings -> the expectations the picker gates on.

    Everything is smoothed toward 0.5 (Laplace) so three old 1-1s cannot swing
    a leg on their own. Returns None when there is not enough history.
    """
    n = len(meetings or [])
    if n < H2H_MIN_MEETINGS:
        return None
    totals = [m["hg"] + m["ag"] for m in meetings]
    btts = sum(1 for m in meetings if m["hg"] > 0 and m["ag"] > 0)
    over25 = sum(1 for t in totals if t >= 3)
    over15 = sum(1 for t in totals if t >= 2)
    home_wins = sum(1 for m in meetings if m["home"] == _row_home_winner(m))
    draws = sum(1 for m in meetings if m["hg"] == m["ag"])

    def smooth(k: int) -> float:
        return (k + LAPLACE / 2) / (n + LAPLACE)

    return {
        "n": n,
        "avg_goals": round(sum(totals) / n, 2),
        "over25": round(smooth(over25), 3),
        "over15": round(smooth(over15), 3),
        "btts": round(smooth(btts), 3),
        "home_win": round(smooth(home_wins), 3),
        "draw": round(smooth(draws), 3),
        "away_win": round(smooth(n - home_wins - draws), 3),
    }


def _row_home_winner(m: dict) -> str | None:
    if m["hg"] > m["ag"]:
        return m["home"]
    if m["hg"] < m["ag"]:
        return m["away"]
    return None


# ── browser fetching ────────────────────────────────────────────────────────
def _driver():
    """A headless Chrome for flashscore only. Never used for the bookmaker:
    no login, no session, no account."""
    import betflow
    drv, _prof = betflow.build_driver(headless=True)
    return drv


_ROW_JS = (
    "var rows = document.querySelectorAll('[class*=event__match]');"
    "var out = [];"
    "for (var i = 0; i < rows.length; i++) {"
    "  var r = rows[i];"
    "  var h = r.querySelector('[class*=home]');"
    "  var a = r.querySelector('[class*=away]');"
    "  var t = r.querySelector('[class*=time]');"
    "  var l = r.querySelector('a.eventRowLink');"
    "  if (h && a) out.push([h.innerText.trim(), a.innerText.trim(),"
    "    l ? l.href : '', t ? t.innerText.trim() : '']);"
    "}"
    "return out;"
)

_H2H_JS = (
    "var rows = document.querySelectorAll('[class*=h2h__row]');"
    "var out = [];"
    "for (var i = 0; i < rows.length; i++) {"
    "  var t = (rows[i].innerText||'').replace(/\\s+/g,' ').trim();"
    "  if (t) out.push(t);"
    "}"
    "return out;"
)


def fetch_pairing_ids(driver) -> dict:
    """"HOME|AWAY" -> flashscore match id, for today's football page."""
    try:
        driver.get(BOARD_URL)
        time.sleep(6.0)
        rows = driver.execute_script(_ROW_JS) or []
    except Exception as exc:
        log(f"board fetch failed: {str(exc)[:80]}")
        return {}
    out = {}
    for r in rows or []:
        try:
            home, away, href = str(r[0]).strip(), str(r[1]).strip(), str(r[2]).strip()
        except Exception:
            continue
        if home and away and href:
            out[f"{home}|{away}"] = href
    log(f"board: {len(out)} pairing(s) on the day page")
    return out


def _wait_for(driver, js: str, min_count: int = 1, timeout: float = 12.0):
    """Poll a JS extractor until it returns min_count items or time runs out.

    Fixed sleeps were the bug (measured: the same tab returned 0 rows at 4s
    and 20 rows at 9s). Returns [] on timeout - never raises.
    """
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            rows = driver.execute_script(js) or []
            if len(rows) >= min_count:
                return rows
        except Exception:
            return []
        time.sleep(1.0)
    try:
        return driver.execute_script(js) or []
    except Exception:
        return []


# Odds-tab rows: "Bet365 1.90 3.40 4.20" (bookmaker + 1X2 prices).
_ODDS_JS = r"""
var rows = document.querySelectorAll('[class*=ui-table__row]');
var out = [];
for (var i = 0; i < rows.length; i++) {
  var t = (rows[i].innerText||'').replace(/\s+/g,' ').trim();
  if (t) out.push(t);
}
return out;
"""


def parse_odds_rows(rows) -> dict:
    """Average 1X2 prices across the bookmakers the tab lists.

    Empty dict when the tab shows nothing (live/finished matches have their
    prices pulled - that is normal and neutral). Never raises.

    Bookmaker names can carry digits ("Bet365", "1xBet"), so rows are read by
    collecting their DECIMAL prices rather than parsing the name.
    """
    prices = []
    for r in rows or []:
        try:
            nums = [float(x) for x in re.findall(r"\d+\.\d+", str(r))]
        except ValueError:
            continue
        if len(nums) >= 3 and all(n > 1.01 for n in nums[:3]):
            prices.append(nums[:3])
    if not prices:
        return {}
    n = len(prices)
    return {"home": sum(p[0] for p in prices) / n,
            "draw": sum(p[1] for p in prices) / n,
            "away": sum(p[2] for p in prices) / n,
            "books": n}
    """Poll a JS extractor until it returns min_count items or time runs out.

    Fixed sleeps were the bug (measured: the same tab returned 0 rows at 4s
    and 20 rows at 9s). Returns [] on timeout - never raises.
    """
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            rows = driver.execute_script(js) or []
            if len(rows) >= min_count:
                return rows
        except Exception:
            return []
        time.sleep(1.0)
    try:
        return driver.execute_script(js) or []
    except Exception:
        return []


def fetch_h2h(driver, url: str, home: str, away: str) -> list:
    """Meetings between these two teams from their flashscore match page."""
    try:
        driver.get(url if "#/" in url else url + "#/h2h/overall")
        rows = _wait_for(driver, _H2H_JS, min_count=1, timeout=20.0)
    except Exception:
        return []
    return parse_h2h_rows(rows, home, away)


# Standings rows come back as row TEXT: "1. Manchester City 6 5 1 0 13:5 8 16 W W W W W"
_STANDINGS_JS = r"""
var out = [];
var rows = document.querySelectorAll('[class*=ui-table__row], [class*=table__row]');
for (var i = 0; i < rows.length; i++) {
  var t = (rows[i].innerText||'').replace(/\s+/g,' ').trim();
  if (t) out.push(t);
}
return out;
"""

# News: return the page text and let Python find the headline/source pairs.
_NEWS_JS = r"""
var t = (document.body.innerText||'').replace(/\s+/g,' ');
return [t.substring(0, 6000)];
"""

# A headline sits before its source marker: "... Palace comeback to defeat
# Forest on Glasner's return to Selhurst Park skysports.com" or
# "... Flashscore News , 3 min ago".
_NEWS_ITEM = re.compile(
    r"([A-Z][A-Za-z0-9 ,'\u2019\-():]{25,150}?)\s+"
    r"(?:Flashscore News\s*,?\s*\d+\s*(?:min|hour)s?\s*ago|[\w.-]+\.(?:com|net|org|co\.uk))")

# Words that make a "short-priced favourite" leg suspicious - the reason a
# cheap price is cheap.
_NEWS_FLAGS = ("injur", "out ", "doubt", "miss ", "suspend", "banned", "rest",
               "rotation", "sidelined", "doubtful", "fitness", "illness",
               "red card", "ban", "return", "lineup", "line-up", "squad")

# "1. Manchester City 6 5 1 0 13:5 8 16 W W W W W"
# pos. team MP W D L GF:GA GD PTS FORM
_STANDINGS_ROW = re.compile(
    r"^\s*(\d+)\.\s+(.+?)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+"
    r"(\d+):(\d+)\s+(-?\d+)\s+(\d+)\s+((?:[WDL?]\s*)+)$")


def _parse_standings(rows, home: str, away: str) -> dict:
    """Find our two teams in the standings table -> position/points/form/goals."""
    out = {}
    for label, team in (("home", home), ("away", away)):
        key = _norm(team)
        best = None
        for r in rows:
            m = _STANDINGS_ROW.match(r)
            if not m:
                continue
            name = _norm(m.group(2))
            if key and (key in name or name in key):
                best = m
                break
        if not best:
            continue
        out[label] = {
            "pos": int(best.group(1)),
            "played": int(best.group(3)),
            "wins": int(best.group(4)),
            "draws": int(best.group(5)),
            "losses": int(best.group(6)),
            "goals_for": int(best.group(7)),
            "goals_against": int(best.group(8)),
            "gd": int(best.group(9)),
            "pts": int(best.group(10)),
            "form": best.group(11).strip().replace(" ", ""),
        }
    return out


def fetch_odds(driver, url: str, mid: str, first_seen: dict | None) -> dict:
    """Current 1X2 consensus from the odds tab + movement vs the first sight.

    `first_seen` is the previously stored consensus (may be {}). Movement is
    the signed % change since then - a price SHORTENING means money is
    shortening it (the market is more confident than when we first looked).
    Odds are pulled for live/finished matches, so {} here is normal.
    """
    try:
        driver.get(f"{url.split('#')[0].split('?')[0].rstrip('/')}/odds/?mid={mid}")
        rows = _wait_for(driver, _ODDS_JS, min_count=1, timeout=10.0)
        now = parse_odds_rows(rows)
        if not now:
            return {}
        if first_seen and all(first_seen.get(k) for k in ("home", "draw", "away")):
            movement = {}
            for k in ("home", "draw", "away"):
                base = float(first_seen[k])
                movement[k] = round(now[k] / base - 1.0, 4) if base else 0.0
            now["movement"] = movement
        now["books"] = int(now.get("books") or 0)
        return now
    except Exception:
        return {}


def fetch_match_detail(driver, url: str, home: str, away: str,
                       deep: bool = True, first_odds: dict | None = None) -> dict:
    """Everything crawlable for one pairing: H2H, standings, news, odds.

    Tab URLs are path-based (the owner's note: on Flashscore you open the game
    card first - these are the tabs that card exposes). Odds are pulled for
    live/finished matches, so an empty odds list is normal and neutral.

    `deep=False` collects H2H only: standings/news are two more page loads per
    pairing, so the pacing gap deep-crawls a shortlist and H2H-crawls the rest.
    """
    out = {"h2h": fetch_h2h(driver, url, home, away)}
    # The stored URL is ".../match/football/<slug>/<slug>/?mid=<mid>" - strip
    # BOTH the hash and the query before appending a tab path, or the result
    # is ".../?mid=X/standings/?mid=X" and Flashscore serves its error page
    # (measured 2026-10-11).
    base = url.split("#")[0].split("?")[0].rstrip("/")
    mid = url.split("mid=")[-1] if "mid=" in url else ""
    if not mid or not deep:
        return out
    # Odds consensus + movement vs the first sight (the odds-drop signal)
    odds = fetch_odds(driver, url, mid, first_odds)
    if odds:
        out["odds"] = odds
    try:
        driver.get(f"{base}/standings/?mid={mid}")
        rows = _wait_for(driver, _STANDINGS_JS, min_count=2, timeout=12.0)
        st = _parse_standings(rows, home, away)
        if st:
            out["standings"] = st
    except Exception:
        pass
    try:
        driver.get(f"{base}/news/?mid={mid}")
        # The tab lazy-loads its items below the fold - scroll to trigger it,
        # then extract (measured 2026-10-11: without the scroll the page text
        # is navigation only).
        try:
            driver.execute_script(
                "window.scrollTo(0, document.body.scrollHeight / 2);")
        except Exception:
            pass
        chunks = _wait_for(driver, _NEWS_JS, min_count=1, timeout=12.0)
        try:
            driver.execute_script("window.scrollTo(0, document.body.scrollHeight);")
        except Exception:
            pass
        time.sleep(2.0)
        chunks = _wait_for(driver, _NEWS_JS, min_count=1, timeout=8.0) or chunks
        raw = " ".join(chunks)
        items = [m.group(1).strip() for m in _NEWS_ITEM.finditer(raw)]
        # de-duplicate, keep order
        seen, uniq = set(), []
        for s in items:
            if s.lower() not in seen:
                seen.add(s.lower())
                uniq.append(s)
        flags = [s for s in uniq if any(f in s.lower() for f in _NEWS_FLAGS)]
        out["news"] = uniq[:8]
        out["news_flags"] = flags[:5]
    except Exception:
        pass
    return out


def load_signals(ttl: float = MAX_TTL) -> dict:
    try:
        now = time.time()
        if _CACHE["data"] is not None and now - _CACHE["at"] < 300.0:
            return _CACHE["data"]
        data = {}
        if OUT.exists():
            data = json.loads(OUT.read_text(encoding="utf-8"))
        _CACHE["at"] = now
        _CACHE["data"] = data
        return data
    except Exception:
        return {}


def refresh(wanted_keys=None) -> dict:
    """Full pass: day board -> H2H for the pairings we care about.

    `wanted_keys` is the set of "HOME|AWAY" pairings from the machine's last
    board (None = every pairing on the page, which is slower). Merges into the
    existing cache, keeping fresh entries, and returns the new games dict.
    """
    driver = None
    try:
        driver = _driver()
        ids = fetch_pairing_ids(driver)
        if not ids:
            return {}
        if wanted_keys:
            picked = {k: v for k, v in ids.items() if k in wanted_keys}
            if not picked:               # names may differ in case/spacing
                wn = {_norm(k) for k in wanted_keys}
                picked = {k: v for k, v in ids.items()
                          if _norm(k) in wn}
        else:
            picked = ids
        old = (load_signals() or {}).get("games") or {}
        games = dict(old)
        fresh = 0
        # H2H is one page load per pairing; standings+news are two more. Deep
        # -crawl a shortlist so a pacing gap stays minutes, not half an hour.
        for i, (key, mid) in enumerate(list(picked.items())[:40]):
            home, _, away = key.partition("|")
            prev = games.get(key) or {}
            detail = fetch_match_detail(driver, mid, home, away,
                                        deep=(i < DEEP_CRAWL_LIMIT),
                                        first_odds=prev.get("odds"))
            sig = meetings_to_signal(detail.get("h2h") or [])
            if sig is None:
                continue
            if detail.get("standings"):
                sig["standings"] = detail["standings"]
            if detail.get("news"):
                sig["news"] = detail["news"]
                sig["news_flags"] = detail.get("news_flags") or []
            if detail.get("odds"):
                sig["odds"] = detail["odds"]
            games[key] = sig
            fresh += 1
        if fresh:
            payload = {"fetched_at": time.time(),
                       "fetched_at_iso": datetime.now().isoformat(timespec="seconds"),
                       "source": "flashscore",
                       "games": games}
            OUT.write_text(json.dumps(payload, indent=2), encoding="utf-8")
            log(f"wrote {fresh} pairing signal(s) -> {OUT.name}")
        return games
    except Exception as exc:
        log(f"refresh failed: {str(exc)[:90]}")
        return {}
    finally:
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass


if __name__ == "__main__":
    raise SystemExit(0 if refresh() else 1)
