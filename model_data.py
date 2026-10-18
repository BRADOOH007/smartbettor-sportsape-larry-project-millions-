#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
model_data.py - API-Football model layer for BetFlow.

WHY THIS EXISTS
---------------
The book's odds are one opinion; API-Football's prediction percentages are an
independent one. Where they DISAGREE is the only place value can exist:
    implied_prob = 1 / odds
    ev = model_prob * odds - 1
A leg with positive ev is the book paying more than an independent model
thinks it is worth. That is the entire edge this layer provides.

RELIABILITY RULES (they keep the machine safe, not cleverer):
  * Reads api_football_key from sportsape_settings.json; no key => no calls.
  * Plain HTTPS with the key header - no browser, no scraping, no CAPTCHA.
  * Everything cached in Desktop/model_cache.json (fixtures 6h, predictions
    6h) so a round rarely spends more than a couple of HTTP calls.
  * Every fetch is capped (max 3 NEW predictions/round, 15s each) and every
    failure degrades to "no model data" - the picker then behaves exactly as
    it did before this file existed.
  * The free plan is ~100 requests/day. quota_left is tracked and the layer
    goes quiet when it runs low.

Matching SportPesa names to API-Football names is fuzzy on purpose
("Alebrijes de Oaxaca" == "ALEBRIJES OAXACA"); unmatched games are neutral.
"""
from __future__ import annotations

import json
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.request
from datetime import date, datetime
from pathlib import Path

API_HOST = "https://v3.football.api-sports.io"
FIXTURES_TTL = 6.0 * 3600.0
PRED_TTL = 6.0 * 3600.0
MAX_NEW_PREDICTIONS = 3          # per round, so a round cannot blow the budget
FETCH_TIMEOUT = 15.0              # predictions that are slow are skipped
QUIET_BELOW = 10                  # remaining requests/day at which we stop
# Club tokens / filler words dropped when normalising team names. A drop list
# this broad would over-match in a 30-team league, but the board is worldwide,
# so fixtures are matched per-day and unusual names collide rarely.
DROP_TOKENS = re.compile(
    r"\b(FC|CF|AF|AFC|SC|UTD|UNITED|CD|CA|SD|DC|AC|AS|SS|SK|FK|RC|NK|CE|SAD|"
    r"DE|DI|DO|DA|THE|EL|LOS|LAS|SAN|SAO|SPORT|CLUB)\b", re.I)
JUNK = re.compile(r"[^A-Z0-9]")


def _live_dir() -> Path:
    desk = Path.home() / "Desktop"
    if (desk / "sportsape_settings.json").exists():
        return desk
    return Path(__file__).resolve().parent


LIVE = _live_dir()
SETTINGS = LIVE / "sportsape_settings.json"
CACHE_FILE = LIVE / "model_cache.json"

_CACHE: dict = {"at": 0.0, "data": None}


def log(msg: str) -> None:
    line = f"[{datetime.now():%H:%M:%S}] model: {msg}"
    print(line, flush=True)
    if getattr(sys, "frozen", False):
        try:
            with open(LIVE / "gui_terminal.log", "a", encoding="utf-8") as f:
                f.write(line + "\n")
        except Exception:
            pass


def _api_key() -> str:
    try:
        cfg = json.loads(SETTINGS.read_text(encoding="utf-8"))
        return str(cfg.get("api_football_key") or "").strip()
    except Exception:
        return ""


def _load_cache() -> dict:
    now = time.time()
    if _CACHE["data"] is not None and now - _CACHE["at"] < 300.0:
        return _CACHE["data"]
    data = {}
    try:
        if CACHE_FILE.exists():
            data = json.loads(CACHE_FILE.read_text(encoding="utf-8"))
    except Exception:
        data = {}
    _CACHE["at"] = now
    _CACHE["data"] = data
    return data


def _save_cache(data: dict) -> None:
    try:
        CACHE_FILE.write_text(json.dumps(data, indent=1), encoding="utf-8")
    except Exception:
        pass


def _get(url: str) -> dict | None:
    """GET the API with the key header; None on any failure."""
    key = _api_key()
    if not key:
        return None
    req = urllib.request.Request(url, headers={
        "x-apisports-key": key, "Accept": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT) as r:
            body = json.loads(r.read().decode("utf-8", "replace"))
            try:
                body["_quota_left"] = int(r.headers.get("x-ratelimit-remaining"))
            except (TypeError, ValueError):
                pass
            try:
                body["_quota_limit"] = int(r.headers.get("x-ratelimit-limit"))
            except (TypeError, ValueError):
                pass
            return body
    except Exception:
        return None


def norm(name: str) -> str:
    """Canonical team key: uppercase, accent-stripped, junk removed, club
    tokens dropped ('Alebrijes de Oaxaca' -> 'ALEBRIJESOAXACA')."""
    s = unicodedata.normalize("NFKD", str(name or "").upper())
    s = "".join(ch for ch in s if not unicodedata.combining(ch))
    s = DROP_TOKENS.sub(" ", s)
    return JUNK.sub("", s)


def _ratio(a: str, b: str) -> float:
    from difflib import SequenceMatcher
    return SequenceMatcher(None, a, b).ratio()


def fetch_fixtures_today(force: bool = False) -> list:
    """Not-started fixtures for today -> [{id, hn, an, kickoff}]. Cached 6h.
    Empty list on any failure (never raises)."""
    cache = _load_cache()
    fixtures = cache.get("fixtures") or {}
    day = date.today().isoformat()
    if not force:
        ent = fixtures.get(day)
        if ent and time.time() - ent.get("at", 0) < FIXTURES_TTL:
            return ent.get("rows") or []
    body = _get(f"{API_HOST}/fixtures?date={day}&status=NS")
    if not body or not body.get("response"):
        return []
    rows = []
    for fx in body["response"]:
        try:
            rows.append({
                "id": int(fx["fixture"]["id"]),
                "hn": norm(fx["teams"]["home"]["name"]),
                "an": norm(fx["teams"]["away"]["name"]),
                "kickoff": (fx.get("fixture", {}).get("date") or "")[:16],
            })
        except Exception:
            continue
    fixtures[day] = {"at": time.time(), "rows": rows}
    cache["fixtures"] = fixtures
    _quota_save(body, cache)
    _save_cache(cache)
    log(f"fixtures: {len(rows)} not-started game(s) today "
        f"(quota {cache.get('quota_left', '?')} left)")
    return rows


def _quota_save(body: dict, cache: dict) -> None:
    """Record the plan's own rate-limit headers, stamped with the UTC day.

    MEASURED 2026-10-14: the live key is a 10-requests/day plan. The layer
    read "9 remaining" against a FIXED QUIET_BELOW of 10, declared itself
    low, and then never fetched a prediction again (model_cache.json held
    predictions: {} for its whole life) - the EV layer and every confidence
    stake tier were dead on arrival. Two fixes live here:
      * record the plan's own LIMIT so the quiet threshold can be
        proportional to it (see score_games);
      * stamp the reading with the UTC day it came from, so a new day never
        inherits yesterday's exhausted counter, and a live 200 response with
        no headers (key provably alive) clears a stale low belief.
    """
    today = datetime.utcnow().date().isoformat()
    lim = body.get("_quota_limit")
    if lim is not None:
        cache["quota_limit"] = int(lim)
    left = body.get("_quota_left")
    if left is not None:
        cache["quota_left"] = int(left)
        cache["quota_day"] = today
    elif cache.get("quota_day") != today:
        cache["quota_left"] = -1
        cache["quota_day"] = today


def fetch_results_today(force: bool = False) -> list:
    """TODAY's finished fixtures -> [{hn, an, hg, ag, status}] (norm names).

    The settlement source for shadow slips: research bets are never placed at
    the book, so nothing can import them from bet history - they are settled
    against real final scores here. One call per day (cached 6h); empty list on
    any failure.
    """
    cache = _load_cache()
    results = cache.get("results") or {}
    day = date.today().isoformat()
    if not force:
        ent = results.get(day)
        if ent and time.time() - ent.get("at", 0) < FIXTURES_TTL:
            return ent.get("rows") or []
    body = _get(f"{API_HOST}/fixtures?date={day}")
    if not body or not body.get("response"):
        return []
    rows = []
    for fx in body["response"]:
        try:
            goals = fx.get("goals") or {}
            score = fx.get("score") or {}
            ht = score.get("halftime") or {}
            status = (fx.get("fixture") or {}).get("status") or {}
            rows.append({
                "hn": norm(fx["teams"]["home"]["name"]),
                "an": norm(fx["teams"]["away"]["name"]),
                "hg": int(goals.get("home") if goals.get("home") is not None else -1),
                "ag": int(goals.get("away") if goals.get("away") is not None else -1),
                # Half-time score: needed to settle HT-draw / HT-BTTS legs
                "hth": int(ht.get("home")) if ht.get("home") is not None else None,
                "hta": int(ht.get("away")) if ht.get("away") is not None else None,
                # Status: the book's own short code ("FT", "HT", "1H"...).
                # THIS LINE WAS THE BUG, measured 2026-10-14: it read
                # str(status_dict).get("short") - a str has no .get, so the
                # AttributeError was swallowed by the per-fixture try/except
                # and EVERY fixture was skipped. fetch_results_today()
                # returned 0 rows for its whole life, which is why not one
                # shadow slip ever settled against a real score.
                "status": status.get("short", "")
                          if isinstance(status, dict) else str(status),
            })
        except Exception:
            continue
    results[day] = {"at": time.time(), "rows": rows}
    cache["results"] = results
    _quota_save(body, cache)
    _save_cache(cache)
    log(f"results: {len(rows)} fixture(s) on the day feed "
        f"(quota {cache.get('quota_left', '?')} left)")
    return rows


def fetch_results_on(day: str) -> list:
    """Finished fixtures for a SPECIFIC day -> same rows as fetch_results_today.

    MEASURED 2026-10-16: both the shadow settlement and the per-leg scoring
    read fetch_results_today() only. A slip placed late on day D settles after
    its matches finish - very often on D+1 - so it was scored against the WRONG
    day's feed and every leg came back undecidable. That is why 158 settled
    bets produced barely a handful of leg-trials. The cache already keeps the
    results of every day that has ever been fetched, so a slip can be scored
    against its OWN day at zero quota cost. Only TODAY may hit the API.
    """
    today = date.today().isoformat()
    if day == today or not day:
        return fetch_results_today()
    try:
        cache = _load_cache()
        ent = (cache.get("results") or {}).get(day) or {}
        return ent.get("rows") or []
    except Exception:
        return []


# Basketball results via ESPN's free, key-less scoreboard API.
#
# WHY THIS EXISTS (2026-10-17): the results layer was football-only, so legs on
# basketball games (NBL, BJ League, KBL, B.League, WNBL...) could be drafted
# but never per-leg scored - they contributed zero trials to market_types /
# league_markets and the steering weights learned from football alone. This
# extends the same row schema to basketball so those legs can be graded.
#
# HONEST COVERAGE (report it, do not overclaim): ESPN's free scoreboard only
# answers for a handful of leagues. As of this writing the slugs below return
# data; everything else (BJ League, KBL, B.League, WNBL Women, ...) 400s and
# those legs stay undecidable (None -> no trial recorded), which is the honest
# outcome rather than a fabricated one. Full coverage needs a broader source -
# API-Basketball (free tier, 100 req/day, needs a key) or a Flashscore results
# scraper - and is a separate, user-opt-in step.
BASKETBALL_SLUGS = ("nba", "wnba", "nbl", "euroleague", "fiba", "acb")
_BALL_TTL = 6.0 * 3600.0


def fetch_basketball_results_today(force: bool = False) -> list:
    """Today's finished basketball fixtures -> same row schema as football.

    Free, key-less (ESPN scoreboard). Cached 6h for today; past days are
    permanent cache entries. Returns [] on any failure - never raises.
    """
    cache = _load_cache()
    bb = cache.setdefault("basketball_results", {})
    day = date.today().isoformat()
    if not force:
        ent = bb.get(day)
        if ent and time.time() - ent.get("at", 0) < _BALL_TTL:
            return ent.get("rows") or []
    dstr = day.replace("-", "")
    rows = []
    seen = set()
    for slug in BASKETBALL_SLUGS:
        url = ("https://site.api.espn.com/apis/site/v2/sports/basketball/"
               "%s/scoreboard?dates=%s" % (slug, dstr))
        try:
            with urllib.request.urlopen(url, timeout=8) as resp:
                body = json.loads(resp.read().decode("utf-8", "replace"))
        except Exception:
            continue
        for ev in (body.get("events") or []):
            try:
                comp = (ev.get("competitions") or [{}])[0]
                status = (ev.get("status") or {}).get("type") or {}
                if status.get("name") != "STATUS_FINAL":
                    continue
                comps = comp.get("competitors") or []
                home = next((x for x in comps
                             if x.get("homeAway") == "home"), None)
                away = next((x for x in comps
                             if x.get("homeAway") == "away"), None)
                if not home or not away:
                    continue
                hg = home.get("score")
                ag = away.get("score")
                if hg is None or ag is None:
                    continue
                hn = norm(home["team"]["displayName"])
                an = norm(away["team"]["displayName"])
                if not hn or not an:
                    continue
                key = (hn, an)
                if key in seen:
                    continue
                seen.add(key)
                rows.append({
                    "hn": hn, "an": an,
                    "hg": int(hg), "ag": int(ag),
                    # Basketball has quarters, not halves - no HT score. HT
                    # markets on a basketball leg are left undecidable (None),
                    # which is honest: the engine never drafts HT draw on
                    # basketball anyway.
                    "hth": None, "hta": None,
                    "status": "FT",
                    "_sport": "basketball",
                })
            except Exception:
                continue
    bb[day] = {"at": time.time(), "rows": rows}
    cache["basketball_results"] = bb
    _save_cache(cache)
    log("basketball results: %d fixture(s) on the day feed "
        "(covered leagues: %s)" % (len(rows), ", ".join(BASKETBALL_SLUGS)))
    return rows


def fetch_basketball_results_on(day: str, force: bool = False) -> list:
    """Finished basketball fixtures for a SPECIFIC day.

    Same caching discipline as fetch_results_on: only TODAY may hit the API
    unless force=True (used for one-off backfills); historical days come from
    the cache (populated when they were 'today').
    """
    today = date.today().isoformat()
    if force or day == today or not day:
        return fetch_basketball_results_today(force=force)
    try:
        cache = _load_cache()
        ent = (cache.get("basketball_results") or {}).get(day) or {}
        return ent.get("rows") or []
    except Exception:
        return []


def fetch_all_results_on(day: str) -> list:
    """Football + basketball results for a day, merged.

    The per-leg scorer and the shadow settler both need to grade legs from
    every sport the engine drafts. find_result() already requires an
    UNAMBIGUOUS match, so a basketball pairing that collides with a
    football one on the same day is left undecidable rather than guessed -
    merging the two feeds is safe. A merged miss simply yields None (no
    trial recorded), which is the honest outcome.
    """
    out = []
    try:
        out.extend(fetch_results_on(day) or [])
    except Exception:
        pass
    try:
        out.extend(fetch_basketball_results_on(day) or [])
    except Exception:
        pass
    return out


def find_result(home: str, away: str, rows: list):
    """The feed row for a pairing, exact first then unambiguous-fuzzy.

    The board names come from Flashscore; the results feed is API-Football.
    MEASURED 2026-10-16: exact normalised matching threw away most legs -
    "Pwd SC" (PWD) never equalled API's "PWD Sports" (PWDSPORTS), so the
    per-leg tables and the shadow slips learned from almost nothing. This
    falls back to a prefix/fuzzy match, but ONLY when exactly one feed row
    qualifies, so an ambiguous name ("Manchester" for both clubs) is left
    undecided rather than guessed.
    """
    if not rows:
        return None
    h, a = norm(home), norm(away)
    if not h or not a:
        return None
    for r in rows:
        hn, an = r.get("hn") or "", r.get("an") or ""
        if (hn == h and an == a) or (hn == a and an == h):
            return r

    def close(x: str, y: str) -> bool:
        if not x or not y:
            return False
        if x == y:
            return True
        if len(x) >= 3 and len(y) >= 3 and (x.startswith(y) or y.startswith(x)):
            return True
        return _ratio(x, y) >= 0.84

    cands = [r for r in rows
             if (close(r.get("hn") or "", h) and close(r.get("an") or "", a))
             or (close(r.get("hn") or "", a) and close(r.get("an") or "", h))]
    if len(cands) == 1:
        return cands[0]
    return None


def fetch_predictions(fixture_id: int) -> dict | None:
    """1X2 percentages + advice for one fixture. Cached 6h. None on any
    failure. Returns {'home','draw','away','advice'} with 0..1 floats."""
    cache = _load_cache()
    preds = cache.get("predictions") or {}
    ent = preds.get(str(fixture_id))
    if ent and time.time() - ent.get("at", 0) < PRED_TTL:
        return {k: ent[k] for k in ("home", "draw", "away", "advice")}
    body = _get(f"{API_HOST}/predictions?fixture={fixture_id}")
    if not body or not body.get("response"):
        return None
    try:
        p = body["response"][0]["predictions"]
        pct = p.get("percent") or {}
        to_f = lambda s: float(str(s).replace("%", "").strip()) / 100.0
        out = {"home": to_f(pct.get("home")), "draw": to_f(pct.get("draw")),
               "away": to_f(pct.get("away")), "advice": str(p.get("advice") or "")}
    except Exception:
        return None
    preds[str(fixture_id)] = dict(out, at=time.time())
    cache["predictions"] = preds
    _quota_save(body, cache)
    _save_cache(cache)
    return out


def score_games(games: list) -> dict:
    """Map SportPesa board games to model 1X2 probabilities.

    games: api_board rows (each with home/away names).
    Returns {gid: {'home','draw','away','advice'}} for matched games only.
    Never raises; never fetches more than MAX_NEW_PREDICTIONS per call."""
    out: dict = {}
    try:
        key = _api_key()
        if not key:
            return out
        fixtures = fetch_fixtures_today()
        if not fixtures:
            return out
        cache = _load_cache()
        # Quiet threshold is proportional to the plan's OWN limit: the live
        # key is a 10/day plan (measured 2026-10-14 - x-ratelimit-limit: 10),
        # so a fixed QUIET_BELOW of 10 silenced it permanently. max(1, limit
        # // 10): a 100/day key rests below 10 left, a 10/day key rests at 0.
        # A reading from an earlier UTC day is stale and never gates today.
        left = int(cache.get("quota_left", -1) or -1)
        limit = int(cache.get("quota_limit") or 100)
        quiet_below = max(1, limit // 10)
        today_utc = datetime.utcnow().date().isoformat()
        if (left >= 0 and left < quiet_below
                and str(cache.get("quota_day") or "") == today_utc):
            log(f"quota low ({left}/{limit} left today) - model scoring off")
            return out
        preds = cache.get("predictions") or {}
        by_id = {f["id"]: f for f in fixtures}
        new_tries = 0
        for g in games:
            gid = g.get("gid")
            if not gid:
                continue
            hn, an = norm(g.get("home") or ""), norm(g.get("away") or "")
            if len(hn) < 4 or len(an) < 4:
                continue
            fid = None
            for f in fixtures:                       # small N, linear is fine
                if f["hn"] == hn and f["an"] == an:
                    fid = f["id"]
                    break
            if not fid:                              # fuzzy fallback
                best, br = None, 0.82
                for f in fixtures:
                    r = min(_ratio(f["hn"], hn), _ratio(f["an"], an))
                    if r > br:
                        best, br = f["id"], r
                fid = best
            if not fid:
                continue
            ent = preds.get(str(fid))
            if not ent:
                if new_tries >= MAX_NEW_PREDICTIONS:
                    continue
                new_tries += 1
                ent = fetch_predictions(fid)
            if ent:
                out[gid] = {"home": ent["home"], "draw": ent["draw"],
                            "away": ent["away"], "advice": ent.get("advice", "")}
        if out:
            log(f"{len(out)} game(s) matched with model odds "
                f"(new prediction calls this round: {new_tries})")
    except Exception as exc:
        log(f"scoring disabled this round - {str(exc)[:80]}")
    return out
