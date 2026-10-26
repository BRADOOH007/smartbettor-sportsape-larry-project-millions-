# -*- coding: utf-8 -*-
"""pick_filters.py - everything that decides whether a CANDIDATE leg may be bet.

WHY THIS FILE EXISTS
--------------------
The engine used to keep its gates as ad-hoc blocks inside api_pick_legs(), and
the learning layer (retired markets, signed market weights, per-team P&L) was
never wired in at all - the calibration recorded, nothing consumed. This module
holds every candidate-level decision in one readable place, so "what stops this
leg being bet" is answerable in one screen:

  * retired markets    - the learner proved the market unpriceable
  * market weights     - signed, Brier-aware weight from _maybe_recalibrate
  * team x market veto - a pairing that keeps losing money
  * flashscore         - head-to-head evidence vs the price (forebet replaced)
  * AI analyst (Gemini)- red-flag veto on shortlisted legs, batched per round

EVERY gate is fail-safe: a missing cache, a dead feed, a 503 AI edge or any
exception returns "no opinion" and the leg stands exactly as before. Intelligence
must never be able to reduce the machine to zero bets by accident - it only ever
removes legs it has real evidence against.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

# ── thresholds (same shapes as the legacy gates they replace) ───────────────
TEAM_VETO_MIN_TRIALS = 5      # pairings with fewer are noise
TEAM_VETO_ROI = -0.20         # a pairing this bad is not bet again
MARKET_WEIGHT_FLOOR = 0.85    # below this a market is effectively retired
FLASH_EDGE = 0.85             # keep a leg only if evidence >= implied * this
AI_ENABLED = True
AI_TIMEOUT = 12.0             # single-shot: an AI stall must not cost a round
AI_MIN_INTERVAL = 600.0       # 10 min between analyst calls (free-tier limit)
from sportsape_grok import BROWSER_UA  # noqa: E402  (defined after constants)


def _live_dir() -> Path:
    desk = Path.home() / "Desktop"
    if (desk / "sportsape_settings.json").exists():
        return desk
    return Path(__file__).resolve().parent


LIVE = _live_dir()
STATS = LIVE / "sportsape_stats.json"
SETTINGS = LIVE / "sportsape_settings.json"


def _norm_team(name: str) -> str:
    s = re.sub(r"[^A-Z0-9 ]", " ", str(name or "").upper())
    return " ".join(s.split())


def load_learning() -> dict:
    """The learner's output: retired markets + signed market weights.

    Written by sportsape_backend._maybe_recalibrate on every settle (and by
    the nightly pass). Missing/corrupt file = nothing learned yet = {}.
    """
    try:
        if not STATS.exists():
            return {}
        st = json.loads(STATS.read_text(encoding="utf-8"))
    except Exception:
        return {}
    retired = set(st.get("retired_markets") or [])
    weights = {}
    for mk, e in (st.get("market_types") or {}).items():
        try:
            w = float(e.get("weight") or 1.0)
        except (TypeError, ValueError):
            continue
        weights[mk] = w
    return {"retired": retired, "weights": weights}


# ── HOT PATTERNS (prize the winners, not just punish the losers) ────────────
# A pattern is "hot" only when BOTH hold:
#   1. FULL-history evidence floor:  >= HOT_MIN_TRIALS real settled bets in its
#      own stats table (10 - a 3-bet fluke must never steer the machine);
#   2. RECENT money confirmation: over the last HOT_RING_N settled real bets
#      (30), the pattern's ROI >= HOT_MIN_ROI (+20%).
# Recency matters because books adjust and seasons turn: the full table proves
# the pattern is real, the ring proves it is STILL real. Missing stats = no
# opinion = the draft runs unchanged (same fail-safe as every other gate).
HOT_MIN_TRIALS = 10
HOT_MIN_ROI = 0.20
HOT_RING_N = 30


def load_hot_patterns() -> dict:
    """Patterns worth following right now.

    Returns a flat dict: {"sig:away-btts-draw": {...}, "league:Football: KPL":
    {...}, "country:Kenya": ..., "sport:Basketball": ..., "hour:14": ...}.
    Empty dict = nothing qualifies = no steering.
    """
    try:
        st = json.loads(STATS.read_text(encoding="utf-8"))
    except Exception:
        return {}
    ring = [r for r in (st.get("bets_ring") or []) if isinstance(r, dict)][-HOT_RING_N:]

    def _roll(sel):
        agg = {}
        for r in ring:
            keys = sel(r)
            if not keys:
                continue
            for k in (keys if isinstance(keys, list) else [keys]):
                e = agg.setdefault(k, {"stake": 0.0, "ret": 0.0, "n": 0})
                e["stake"] += float(r.get("stake") or 0.0)
                e["ret"] += float(r.get("ret") or 0.0)
                e["n"] += 1
        return agg

    def _rec_roi(e):
        if not e or e["stake"] <= 0:
            return None
        return (e["ret"] - e["stake"]) / e["stake"]

    sig_ring = _roll(lambda r: [r.get("sig")] if r.get("sig") else [])
    lg_ring = _roll(lambda r: r.get("leagues") or [])
    ct_ring = _roll(lambda r: r.get("countries") or [])
    sp_ring = _roll(lambda r: r.get("sports") or [])
    hr_ring = _roll(lambda r: r.get("hours") or [])

    hot: dict = {}

    # Signatures: full floor from the recipes table (mix part of the key).
    sig_full: dict = {}
    for key, r in (st.get("recipes") or {}).items():
        mix = str(key).rsplit("/[", 1)[-1].strip("[]")
        if not mix or mix == "-":
            continue
        e = sig_full.setdefault(mix, {"trials": 0, "stake": 0.0, "ret": 0.0})
        e["trials"] += int(r.get("trials") or 0)
        e["stake"] += float(r.get("stake") or 0.0)
        e["ret"] += float(r.get("ret") or 0.0)
    for mix, e in sig_full.items():
        if int(e["trials"]) < HOT_MIN_TRIALS:
            continue
        r = sig_ring.get(mix)
        rr = _rec_roi(r)
        if rr is None or rr < HOT_MIN_ROI:
            continue
        hot["sig:" + mix] = {"trials": int(e["trials"]), "rec_roi": round(rr, 3),
                             "rec_n": int(r["n"])}

    # Leagues: full floor from sig_league[(mix, league)] money rollup.
    lg_full: dict = {}
    for lgs in (st.get("sig_league") or {}).values():
        for lg, e in lgs.items():
            a = lg_full.setdefault(lg, {"trials": 0, "stake": 0.0, "ret": 0.0})
            a["trials"] += int(e.get("trials") or 0)
            a["stake"] += float(e.get("stake") or 0.0)
            a["ret"] += float(e.get("ret") or 0.0)
    for lg, e in lg_full.items():
        if int(e["trials"]) < HOT_MIN_TRIALS:
            continue
        r = lg_ring.get(lg)
        rr = _rec_roi(r)
        if rr is None or rr < HOT_MIN_ROI:
            continue
        hot["league:" + lg] = {"trials": int(e["trials"]), "rec_roi": round(rr, 3),
                               "rec_n": int(r["n"])}

    # Sport / country / hour slices from their own tables.
    _ring_by = {"sport": sp_ring, "country": ct_ring, "hour": hr_ring}
    for table, tag in (("sport_stats", "sport"),
                       ("country_stats", "country"),
                       ("hour_stats", "hour")):
        for kk, e in (st.get(table) or {}).items():
            if int(e.get("trials") or 0) < HOT_MIN_TRIALS:
                continue
            r = _ring_by[tag].get(kk)
            rr = _rec_roi(r)
            if rr is None or rr < HOT_MIN_ROI:
                continue
            hot[f"{tag}:{kk}"] = {"trials": int(e.get("trials") or 0),
                                  "rec_roi": round(rr, 3), "rec_n": int(r["n"])}
    return hot


def team_vetoes() -> dict:
    """Pairings the money says no to: {(team, market): {'trials', 'roi'}}.

    Read from the per-team ledger _record_settled_stats files. Real money only
    (stake > 0) and a real sample (>= TEAM_VETO_MIN_TRIALS).
    """
    try:
        if not STATS.exists():
            return {}
        st = json.loads(STATS.read_text(encoding="utf-8"))
    except Exception:
        return {}
    out = {}
    for team, mk_map in (st.get("team_stats") or {}).items():
        for mk, e in (mk_map or {}).items():
            try:
                n = int(e.get("trials") or 0)
                s = float(e.get("stake") or 0.0)
                r = float(e.get("ret") or 0.0)
            except (TypeError, ValueError):
                continue
            if n < TEAM_VETO_MIN_TRIALS or s <= 0:
                continue
            roi = (r - s) / s
            if roi <= TEAM_VETO_ROI:
                out[(_norm_team(team), str(mk))] = {"trials": n, "roi": roi}
    return out


LEAGUE_MIN_TRIALS = 8


def league_weights() -> dict:
    """{(sport, league): {market: weight}} - which leagues price which markets.

    The league_markets table (written by the recorder from the real sport +
    competition on every leg) measures hit-rate vs priced probability per
    league x market. A league that consistently beats its price is weighted up
    (capped 1.15); one that keeps missing is weighted down (floor 0.85), same
    ratio the market weights use. Empty stats = {} = no steering.
    """
    try:
        if not STATS.exists():
            return {}
        st = json.loads(STATS.read_text(encoding="utf-8"))
    except Exception:
        return {}
    out = {}
    for league, mk_map in (st.get("league_markets") or {}).items():
        for mk, e in (mk_map or {}).items():
            try:
                n = int(e.get("trials") or 0)
                w = float(e.get("won") or 0.0)
                x = float(e.get("expected") or 0.0)
            except (TypeError, ValueError):
                continue
            if n < LEAGUE_MIN_TRIALS:
                continue
            hit, pred = w / n, x / n
            ratio = hit / max(pred, 0.05)
            out.setdefault(str(league), {})[str(mk)] = round(
                max(0.85, min(1.15, ratio)), 3)
    return out


# ── flashscore evidence (forebet's replacement) ────────────────────────────
def _flash_table():
    try:
        import flashscore_cache as fc
        data = fc.load_signals() or {}
        games = data.get("games") or {}
        if not games:
            return {}
        now = __import__("time").time()
        if now - float(data.get("fetched_at") or 0) > fc.MAX_TTL:
            return {}                          # stale = neutral
        return games
    except Exception:
        return {}


def _flash_key(home: str, away: str) -> str:
    return f"{home}|{away}"


def news_blocked(sig: dict) -> bool:
    """True when the crawl found a headline that makes a leg suspicious.

    This is the "obvious win" guard: a short price is short for a reason, and
    the reason is usually an injury, a rest, or a rotation call. No news =
    no opinion = the leg stands.
    """
    try:
        return bool((sig or {}).get("news_flags"))
    except Exception:
        return False


def odds_underpaid(sig: dict, market: str, book_odds: float | None) -> bool:
    """True when the market consensus pays materially MORE than our book.

    The crawl's 1X2 consensus is an average of the bookmakers the odds tab
    lists. When the consensus sits above the book we are actually using, this
    leg is underpaid for what the market thinks it is worth - the price is
    suspicious, not generous. When the consensus is at or below the book, we
    are paying at or above market: fine.

    Missing consensus (live/finished matches have prices pulled, or the tab
    rendered nothing) = no opinion = False.
    """
    o = (sig or {}).get("odds") or {}
    if not o or not book_odds:
        return False
    m = str(market)
    if m in ("home", "ml_home"):
        consensus = o.get("home")
    elif m in ("away", "ml_away"):
        consensus = o.get("away")
    elif m == "draw":
        consensus = o.get("draw")
    elif m == "ht_home":
        consensus = o.get("home")
    elif m == "ht_away":
        consensus = o.get("away")
    elif m == "ht_draw":
        consensus = o.get("draw")
    else:
        return False
    try:
        consensus = float(consensus)
        book = float(book_odds)
    except (TypeError, ValueError):
        return False
    if consensus <= 0 or book <= 0:
        return False
    return consensus > book * 1.10          # 10% underpaid = suspicious (was 5%)


def odds_drifted(sig: dict, market: str) -> bool:
    """True when the market has moved AGAINST our selection since first sight.

    Movement is the signed % change (now/base - 1). A positive movement on
    our side means the price has drifted up - the market is less confident
    than when we first looked, i.e. money is moving away from our pick. A
    drift beyond 5% is a sharp signal that we should not take the price.

    Missing movement data (first sight, or live/finished match) = no opinion.
    """
    o = (sig or {}).get("odds") or {}
    mv = o.get("movement") or {}
    if not mv:
        return False
    m = str(market)
    if m in ("home", "ml_home", "ht_home"):
        side = "home"
    elif m in ("away", "ml_away", "ht_away"):
        side = "away"
    elif m == "draw":
        side = "draw"
    else:
        return False
    try:
        drift = float(mv.get(side, 0.0))
    except (TypeError, ValueError):
        return False
    # drifted up by more than 5% = market against us
    return drift > 0.05


def flash_prob(market: str, home: str, away: str):
    """Evidence-based probability for `market`, or None when we have none.

    Uses the smoothed head-to-head signal (Laplace toward 0.5, so 3 meetings
    cannot swing a leg alone). None = no opinion = the leg stands.
    """
    sig = _flash_table().get(_flash_key(home, away))
    if not sig:
        return None
    m = str(market)
    if m in ("over15",):
        return sig.get("over15")
    if m in ("over25",):
        return sig.get("over25")
    if m in ("under", "under25"):
        return (1.0 - sig["over25"]) if m == "under25" and sig.get("over25") is not None else (
            1.0 - sig["over15"] if m == "under" and sig.get("over15") is not None else None)
    if m == "btts":
        return sig.get("btts")
    if m == "btts_no":
        return (1.0 - sig["btts"]) if sig.get("btts") is not None else None
    if m in ("home", "ml_home"):
        return sig.get("home_win")
    if m in ("away", "ml_away"):
        return sig.get("away_win")
    if m == "draw":
        return sig.get("draw")
    if m == "dnb_home":
        return None          # H2H win share ignores pushes; leave DNB alone
    if m == "dnb_away":
        return None
    return None


# ── AI analyst (Gemini / Groq / OpenAI / xAI - key decides) ────────────────
_AI_CACHE: dict = {"at": 0.0, "data": {}}


def _ai_key() -> str:
    try:
        cfg = json.loads(SETTINGS.read_text(encoding="utf-8"))
        return str(cfg.get("grok_api_key") or "").strip()
    except Exception:
        return ""


def ai_verdicts(cands: list) -> dict:
    """Batch the shortlisted legs to the AI analyst; {gid|market: bool}.

    True = the analyst raises a red flag and the leg is dropped. Any failure
    (no key, rate limit, 503, unparseable reply) returns {} = no opinion.

    Deliberately a SINGLE short-timeout request, not the governor's _chat with
    its 15/45/90s 429 backoff: this runs inside a betting round with a 165s
    budget, so an AI stall must never cost a round. A per-process minimum
    interval keeps the free tier from being hammered.
    """
    if not AI_ENABLED or not cands:
        return {}
    try:
        import time as _t
        if _t.time() - _AI_CACHE["at"] < AI_MIN_INTERVAL:
            return _AI_CACHE["data"]
    except Exception:
        pass
    key = _ai_key()
    if not key:
        return {}
    try:
        from sportsape_grok import _detect_provider
    except Exception:
        return {}
    base, model = _detect_provider(key, None)
    lines = []
    for c in cands[:25]:
        lines.append(
            f"{c.get('home')} vs {c.get('away')} | market={c.get('market')} "
            f"| odds={c.get('odds')}")
    prompt = (
        "You are a strict betting risk analyst. NO sugarcoating, NO hedging - "
        "call it as you see it. Below are football bet legs with the bookmaker's "
        "odds. Reply ONE line per leg, exactly in the form "
        "'<index> FLAG' when the leg is clearly risky (a key player reported out, "
        "rotation-heavy team, market mismatched to the fixture, price far from "
        "fair, or any reason a sharp bettor would pass), otherwise "
        "'<index> OK'. If in doubt, FLAG. No commentary, no headers.\n"
        "Legs:\n" + "\n".join(f"{i + 1}. {ln}" for i, ln in enumerate(lines)))
    body = json.dumps({"model": model, "temperature": 0.0,
                       "messages": [{"role": "user", "content": prompt}]}).encode()
    text = ""
    try:
        import urllib.request
        req = urllib.request.Request(
            base + "/chat/completions", data=body,
            headers={"Content-Type": "application/json",
                     "Authorization": "Bearer " + key,
                     "User-Agent": BROWSER_UA,
                     "Accept": "application/json"})
        with urllib.request.urlopen(req, timeout=AI_TIMEOUT) as resp:
            data = json.loads(resp.read().decode("utf-8", "replace"))
        text = str(((data.get("choices") or [{}])[0].get("message") or {}).get("content") or "")
    except Exception:
        return {}
    flagged = {}
    for m in re.finditer(r"(\d+)\s+(FLAG|OK)", text, re.I):
        idx = int(m.group(1)) - 1
        if 0 <= idx < len(cands[:25]):
            c = cands[:25][idx]
            flagged[f"{c.get('gid')}|{c.get('market')}"] = (m.group(2).upper() == "FLAG")
    try:
        _AI_CACHE["at"] = __import__("time").time()
        _AI_CACHE["data"] = flagged
    except Exception:
        pass
    return flagged


def apply_gates(cands: list, log=print, ai: bool = True) -> tuple:
    """Filter candidate legs through every gate. Returns (kept, counts).

    Kept order is preserved. Every gate is fail-safe: with no learning data and
    no feeds, `cands` comes back untouched. `ai=False` skips the network call
    (offline tests, and shadow picks that should reuse this round's verdicts).
    """
    kept = list(cands)
    retired, weights = [], {}
    vetoes = {}
    flash_blocked = 0
    ai_blocked = 0
    news_blocked_n = 0
    odds_blocked_n = 0

    # ── learning: retired markets + market weights ──────────────────────
    try:
        learning = load_learning()
        retired = learning.get("retired") or set()
        weights = learning.get("weights") or {}
        vetoes = team_vetoes()
    except Exception:
        pass

    if retired:
        before = len(kept)
        kept = [c for c in kept if c.get("market") not in retired]
        if len(kept) < before:
            try:
                log(f"  learning: retired markets removed "
                    f"{before - len(kept)} leg(s) ({', '.join(sorted(retired))})")
            except Exception:
                pass

    if vetoes:
        before = len(kept)
        kept = [c for c in kept
                if (_norm_team(c.get("home", "")), c.get("market")) not in vetoes
                and (_norm_team(c.get("away", "")), c.get("market")) not in vetoes]
        if len(kept) < before:
            try:
                log(f"  learning: team x market veto removed "
                    f"{before - len(kept)} leg(s) on pairings that lose money")
            except Exception:
                pass

    # ── flashscore head-to-head evidence vs the price ───────────────────
    gated = []
    for c in kept:
        sig = None
        try:
            sig = _flash_table().get(_flash_key(c.get("home"), c.get("away")))
        except Exception:
            sig = None
        p = None
        try:
            p = flash_prob(c.get("market"), c.get("home"), c.get("away"))
        except Exception:
            p = None
        # A headline naming an injury/rest/rotation blocks the leg outright -
        # the "obvious win" guard. Standing data (position vs position) rides
        # along in the cache for the analyst and the league tables.
        if news_blocked(sig):
            news_blocked_n += 1
            continue
        # FotMob RSS news (injuries/rest/rotation) - a second, independent
        # news source. Conservative: only blocks when a flag keyword is present
        # AND the team name is unambiguously matched in a preview.
        try:
            import fotmob_news as _fm
            if _fm.team_has_bad_news(c.get("home")) or _fm.team_has_bad_news(c.get("away")):
                news_blocked_n += 1
                continue
        except Exception:
            pass
        if odds_underpaid(sig, c.get("market"), c.get("odds")):
            odds_blocked_n += 1
            continue
        if odds_drifted(sig, c.get("market")):
            odds_blocked_n += 1
            continue
        # Standing/position gate (ESPN, free, no quota): block extreme
        # mismatches - e.g. betting away win when home is 8+ places higher
        # with significantly better PPG. None data = no opinion (pass).
        try:
            import model_data as _md
            country = c.get("country") or ""
            league = c.get("league") or ""
            if league.startswith("Football: "):
                league = league[len("Football: "):].strip()
            if country and league and not _md.standing_ok(
                    c.get("home"), c.get("away"), country, league):
                odds_blocked_n += 1
                continue
        except Exception:
            pass
        if p is None:
            gated.append(c)
            continue
        implied = 1.0 / float(c.get("odds") or 0) if c.get("odds") else 0.0
        if implied and p < implied * FLASH_EDGE:
            flash_blocked += 1
            continue
        gated.append(c)
    kept = gated
    if news_blocked_n:
        try:
            log(f"  flashscore news: {news_blocked_n} leg(s) blocked - "
                f"injury/rest/rotation headline on a short price")
        except Exception:
            pass
    if odds_blocked_n:
        try:
            log(f"  flashscore odds: {odds_blocked_n} leg(s) blocked - "
                f"market consensus pays more than the book")
        except Exception:
            pass
    if flash_blocked:
        try:
            log(f"  flashscore: {flash_blocked} leg(s) blocked - head-to-head "
                f"evidence well below the price")
        except Exception:
            pass

    # ── AI analyst (ADVISORY ONLY - no BS, but does NOT block) ──────────
    # The AI was blocking 20-25 legs/round but the survivors still lost, so
    # blocking was not improving outcomes - it was just shrinking the pool and
    # forcing worse substitutes. The AI now reports its opinion (logged) but
    # never drops a leg. The mechanical gates (retired, veto, odds, flashscore,
    # standing, movement) remain the real filters.
    if AI_ENABLED and ai and kept:
        try:
            verdicts = ai_verdicts(kept)
        except Exception:
            verdicts = {}
        if verdicts:
            flagged = sum(1 for c in kept
                          if verdicts.get(f"{c.get('gid')}|{c.get('market')}"))
            if flagged:
                try:
                    log(f"  AI analyst: {flagged} leg(s) flagged (advisory, not dropped)")
                except Exception:
                    pass

    counts = {"retired": len(retired), "vetoed_teams": len(vetoes),
              "flash_blocked": flash_blocked, "ai_blocked": ai_blocked,
              "news_blocked": news_blocked_n, "odds_blocked": odds_blocked_n,
              "weights": weights}
    return kept, counts


def rotation_with_weights(markets: list, weights: dict) -> list:
    """Order the market rotation by learned weight (best first).

    The rotation still starts at a different offset per account, so the two
    accounts never share a profile - the steering only changes the ORDER, and
    a market with no data keeps weight 1.0 (no opinion = no reordering).
    """
    if not weights:
        return list(markets)
    return sorted(markets, key=lambda m: -(float(weights.get(m, 1.0) or 1.0)))


if __name__ == "__main__":
    print(json.dumps(load_learning(), indent=1)[:400])
