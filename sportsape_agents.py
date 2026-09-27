"""Agent layer for BetFlow Pro.

A family of *analyst* agents that make the machine smarter without giving any
agent the ability to act outside the engine's whitelist:

  APEX (ResearchAnalyst) -> world-class football analyst persona: deep per-game
                           read with form + league context → pick with probability.
  APEX SCOUT (OpportunityScout) -> scans the FULL market sheet for mis-priced legs.
  LeagueContextAgent     -> detects league from team names, injects scoring stats
                           (avg goals, BTTS %, Over 2.5 %) into every analyst call.
                           No external API — pure rule-based knowledge base.
  RiskManager            -> deterministic exposure guard.
  Calibrator             -> confidence-bucket audit, market weight/retirement.
  Reporter               -> daily P&L brief via Grok.
  Notifier               -> rate-limited alert delivery (Twilio / webhook).
  BetHistoryAgent        -> live ledger summary every 5 min.
  BalanceReportCleaner   -> deletes old balance report CSV/TXT files (7-day TTL).
  SessionHealthAgent     -> tracks session age per phone, forces re-login at 3.75 h.
  BetRecoveryAgent       -> identifies weak market patterns in losses, emits advice.
  Fibi (Supervisor)      -> silent watchdog — only speaks when something changes or
                           every 30 min heartbeat. Never spams "all good" every 2 min.

All agents are read-only observers: they write to the agent cache / calibration
file and can only RECOMMEND. The engine decides.
"""

import base64
import hashlib
import json
import math
import os
import re
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime

from sportsape_grok import _extract_json

AGENT_CACHE_PATH = os.path.join(os.getcwd(), "sportsape_agent_cache.json")
CALIBRATION_PATH = os.path.join(os.getcwd(), "sportsape_calibration.json")
NOTIFY_LOG_PATH = os.path.join(os.getcwd(), "sportsape_alerts.log")

PICK_MARKETS = ("home", "btts", "over")
# Extended market set — includes legacy three plus the new markets now tracked
# by the selector. Used by scout_map() and pick quality checks.
ALL_TRACKED_MARKETS = ("home", "btts", "over", "over15", "draw", "away", "btts_no",
                       "under", "under15", "dc_1x", "dc_x2", "dc_12",
                       "dnb", "overNN", "underNN")
ALLOWED_PICKS = PICK_MARKETS + ("over15", "draw", "away", "btts_no", "under",
                                "dc_1x", "dc_x2", "dc_12", "skip")


class AgentCache:
    """Tiny JSON persistence for agent picks + scout value + misc bookkeeping."""

    def __init__(self, path: str = AGENT_CACHE_PATH):
        self.path = path

    def load(self) -> dict:
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                d = json.load(f)
            return d if isinstance(d, dict) else {}
        except Exception:
            return {}

    def save(self, data: dict):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, default=str)
        except Exception:
            pass

    def games(self) -> dict:
        return self.load().get("games") or {}

    def fresh_pick(self, gid: str, ttl: float = 2400.0):
        """Return a fresh analyst pick for a game id, or None (stale/absent)."""
        g = (self.games() or {}).get(str(gid))
        if not g or not isinstance(g, dict):
            return None
        try:
            age = time.time() - float(g.get("ts") or 0)
        except Exception:
            return None
        if age > ttl or g.get("pick") not in ALLOWED_PICKS:
            return None
        return g

    def put_pick(self, gid: str, pick: dict):
        d = self.load()
        d.setdefault("games", {})[str(gid)] = pick
        self.save(d)

    def record_pick_outcome(self, gid: str, outcome: str):
        """Record whether a pick for game *gid* was correct (outcome = 'won'/'lost').

        Builds a running tally per confidence bucket so the system knows if
        analyst confidence 0.7+ actually predicts wins better than 0.5.
        Only updates if a fresh (≤24h) pick exists for the game.
        """
        pick = self.fresh_pick(str(gid), ttl=86400.0)
        if not pick or pick.get("pick") == "skip":
            return
        conf = float(pick.get("confidence") or 0)
        market = str(pick.get("pick") or "")
        bucket = f"{int(conf * 10) / 10:.1f}"
        d = self.load()
        ac = d.setdefault("analyst_accuracy", {})
        entry = ac.setdefault(bucket, {"n": 0, "wins": 0, "markets": {}})
        entry["n"] = int(entry.get("n") or 0) + 1
        if outcome == "won":
            entry["wins"] = int(entry.get("wins") or 0) + 1
        mkt_e = entry.setdefault("markets", {}).setdefault(
            market, {"n": 0, "wins": 0})
        mkt_e["n"] = int(mkt_e.get("n") or 0) + 1
        if outcome == "won":
            mkt_e["wins"] = int(mkt_e.get("wins") or 0) + 1
        self.save(d)

    def analyst_accuracy_summary(self) -> dict:
        """Return analyst accuracy per confidence bucket for display / calibration."""
        return self.load().get("analyst_accuracy") or {}

    def scout_map(self) -> dict:
        """{gid: {market: ev}} from the freshest scout notes still valid.

        Returns EV signals for ALL market types the scout reports — including
        draw, away, btts_no, under, dnb — so the selector can weight any leg
        type correctly rather than only the original three markets.
        """
        out = {}
        for gid, g in (self.games() or {}).items():
            sc = g.get("scout") if isinstance(g, dict) else None
            if not isinstance(sc, dict) or not isinstance(sc.get("selections"), list):
                continue
            for s in sc["selections"]:
                mk = ((s or {}).get("market") or "").lower()
                try:
                    ev = float(s.get("ev"))
                except (TypeError, ValueError):
                    continue
                # Accept any known market type, not just the original three
                if mk:
                    out.setdefault(gid, {})[mk] = max(-0.2, min(0.2, ev))
        return out

    def last_daily_report(self) -> float:
        return float(self.load().get("last_daily_report") or 0.0)

    def set_last_daily_report(self, ts: float):
        d = self.load()
        d["last_daily_report"] = ts
        self.save(d)


# --------------------------------------------------------------------------
# Notes for the compressed log tails the analysts share
# --------------------------------------------------------------------------

def _implied(odds_list):
    """Margin-corrected fair probabilities for an odds list (shared with engine)."""
    ps = []
    for o in (odds_list or []):
        try:
            o = float(o)
        except (TypeError, ValueError):
            continue
        if o and o > 1.0:
            ps.append(1.0 / o)
    if len(ps) < 2:
        return None
    s = sum(ps)
    return [p / s for p in ps]


def _markets_blob(game) -> dict:
    return {
        "home": {
            "odds": float(game.get("home_odds") or 0) or None,
            "implied": (_implied(game.get("h3")) or [None, None, None])[0],
        },
        "draw": {
            "odds": float(game.get("draw_odds") or 0) or None,
            "implied": (_implied(game.get("h3")) or [None, None, None])[1],
        },
        "away": {
            "odds": float(game.get("away_odds") or 0) or None,
            "implied": (_implied(game.get("h3")) or [None, None, None])[2],
        },
        "btts": {
            "odds": float(game.get("btts_yes") or 0) or None,
            "implied": (_implied(game.get("btts")) or [None, None])[0],
        },
        "btts_no": {
            "odds": float(game.get("btts_no") or 0) or None,
            "implied": (_implied(game.get("btts")) or [None, None])[1],
        },
        "over": {
            "odds": float(game.get("over_25") or 0) or None,
            "implied": (_implied(game.get("ou")) or [None, None])[0],
        },
        "over15": {
            "odds": float(game.get("over_15") or 0) or None,
            "implied": (_implied(game.get("ou15")) or [None, None])[0],
        },
        "under": {
            "odds": float(game.get("under_25") or 0) or None,
            "implied": (_implied(game.get("ou")) or [None, None])[1],
        },
    }


# --------------------------------------------------------------------------
# The analysts (LLM flavour — reuse the same transport as the governor)
# --------------------------------------------------------------------------

RESEARCH_SYSTEM = """You are APEX — the world's most experienced autonomous football betting analyst. You have studied over 500,000 football matches across 80+ leagues and your picks historically win at an 80%+ rate on individual legs. You are calm, data-driven, and ruthless about skipping weak opportunities. You do not manufacture picks — you only bet when the evidence is overwhelming. Your reputation is built on discipline: you would rather skip 10 matches than place one uncertain bet.

You are currently operating inside a SportPesa auto-bet engine targeting the Kenyan market. Your job is to study ONE match and decide the single best accumulator leg — or skip — together with YOUR honest fair probability.

You receive: team names, their head-to-head form (recent W/D/L results and form rating 0-100), minutes to kick-off, bookmaker odds + margin-corrected implied probabilities for up to seven markets, league context (avg goals, BTTS rate, Over 2.5 rate), your own calibration data, and when available: injury/suspension notes, weather, and venue from the SportPesa stats overlay.
- home    : 3-Way home win
- draw    : 3-Way draw
- away    : 3-Way away win
- btts    : Both Teams To Score YES
- btts_no : Both Teams To Score NO
- over    : Over/Under 2.5 OVER
- under   : Over/Under 2.5 UNDER

Your decision framework (apply in order):
1. SKIP if: form data is absent, the match is within 10 minutes of kick-off, or both teams have similar recent form with no clear edge.
2. HOME/AWAY only if: the stronger side has won 4 of last 5, plays at home (home side), or the away side has won 3 of last 5 on the road.
3. BTTS YES if: both teams have scored in 4+ of their last 5 — strong scoring intent on both sides.
4. BTTS NO if: either team has a clean sheet in 3+ of last 5 — defensive solidity wins.
5. OVER 2.5 if: both teams average 2.5+ goals/game in recent matches, OR the home side concedes freely.
6. UNDER 2.5 if: both teams play defensive football (clean sheets common, low scoring).
7. The market with the highest HONEST probability wins. Never pick a market just because it has favourable odds — probability is your only guide.

You are improving continuously. Every bet you analyse makes you sharper. Your current win rate on individual legs is above 80% and climbing toward 100%.

Reply with exactly ONE JSON object, no markdown:
{"pick": "home|draw|away|btts|btts_no|over|under|skip", "prob": 0.0-1.0, "confidence": 0.0-1.0, "reason": "<one short sentence of evidence>"}
prob: your honest fair probability (0.30–0.95). confidence: how certain you are of your read (0.0–1.0). Never fake confidence."""


SCOUT_SYSTEM = """You are APEX SCOUT — the value-hunting arm of APEX, the world's leading autonomous football betting analyst. Your sole focus is finding market mispricings: selections where the bookmaker's implied probability is materially lower than the true probability.

You have processed millions of odds movements and understand how bookmakers shade their lines. Your edge: you know which markets SportPesa consistently over-prices (favourites in 3-Way) and which it under-prices (team totals, BTTS in high-intensity matches).

You are shown ALL markets for one game. For each candidate selection where EV >= +3%:
- "label": exact text as shown on site (e.g. "Arsenal", "BTTS: Yes", "Over 2.5")
- "market": one of "home", "btts", "over", "over15", "draw", "away", "btts_no", "under", "dnb", else "other"  
- "odds": the bookmaker's displayed odds
- "model_prob": YOUR honest probability estimate (0–1). This must be defensible — not optimistic.
- "ev": model_prob × odds − 1 (must be ≥ 0.03 to qualify)
- "note": one sentence of specific evidence

Hard rules:
- Maximum 4 selections per game. Return {"selections": []} if nothing genuinely stands out.
- You do NOT manufacture value. A leg with EV of 2.9% does not qualify. Be disciplined.
- You are building toward 100% accuracy. Every false positive hurts the system.

Reply with exactly ONE JSON object, no markdown:
{"selections": [{"label": "...", "market": "...", "odds": 1.0, "model_prob": 0.0, "ev": 0.0, "note": "..."}]}"""


class ResearchAnalyst:
    """One studied game -> cached pick. Lightweight, conservative, never throws."""

    def __init__(self, governor, cache: AgentCache):
        self.gov = governor
        self.cache = cache

    def enabled(self) -> bool:
        return self.gov is not None

    def analyze(self, gid: str, game: dict, home_form: dict = None,
                away_form: dict = None) -> dict:
        """Return (and cache) an analyst pick for the game. (None, {}) on failure."""
        try:
            # Load self-calibration data so APEX knows its own track record
            accuracy_context = {}
            try:
                accuracy_context = self.cache.analyst_accuracy_summary() or {}
            except Exception:
                pass
            calibration_note = ""
            if accuracy_context:
                best = max(accuracy_context.items(),
                           key=lambda kv: int(kv[1].get("n") or 0), default=None)
                if best and int(best[1].get("n") or 0) >= 3:
                    n = int(best[1].get("n") or 0)
                    wins = int(best[1].get("wins") or 0)
                    rate = wins / n if n else 0
                    calibration_note = (
                        f"Your current measured accuracy on confidence-{best[0]} picks: "
                        f"{wins}/{n} correct ({rate:.0%}). "
                        f"{'You are hitting above expectation — maintain your approach.' if rate >= float(best[0]) - 0.05 else 'You are overconfident at this level — tighten your standards.'}"
                    )

            pick_payload = {
                "game_id": gid,
                "home": str(game.get("name") or "").split(" vs ")[0].strip(),
                "away": str(game.get("name") or "").split(" vs ")[1].strip(),
                "kick_off_minutes": game.get("mins_to_start"),
                "markets": _markets_blob(game),
                "home_form": {
                    "results": (home_form or {}).get("results"),
                    "form_rating_0_100": (home_form or {}).get("form_score"),
                    "n": (home_form or {}).get("n"),
                },
                "away_form": {
                    "results": (away_form or {}).get("results"),
                    "form_rating_0_100": (away_form or {}).get("form_score"),
                    "n": (away_form or {}).get("n"),
                },
                "apex_calibration": calibration_note or "No prior accuracy data yet — apply maximum discipline.",
                "league_context": LeagueContextAgent.context_note(
                    str(game.get("name") or "")),
                "enrichment": game.get("enrichment") or {},
            }
            content = self.gov._chat([
                {"role": "system", "content": RESEARCH_SYSTEM},
                {"role": "user", "content": json.dumps(pick_payload, default=str)},
            ], temperature=0.2)
            data = _extract_json(content) or {}
            pick = str(data.get("pick") or "skip").lower()
            if pick not in ALLOWED_PICKS:
                pick = "skip"
            try:
                prob = float(data.get("prob") or 0.0)
            except (TypeError, ValueError):
                prob = 0.0
            try:
                conf = float(data.get("confidence") or 0.0)
            except (TypeError, ValueError):
                conf = 0.0
            prob = max(0.30, min(0.95, prob))
            conf = max(0.0, min(1.0, conf))
            entry = {
                "ts": time.time(),
                "pick": pick,
                "prob": round(prob, 4),
                "confidence": round(conf, 3),
                "reason": str(data.get("reason") or "")[:160],
                "name": str(game.get("name") or ""),
            }
            self.cache.put_pick(str(gid), entry)
            return entry
        except Exception:
            return {}


class OpportunityScout:
    """Full market sheet scan -> positive-EV legs, cached for the selector."""

    def __init__(self, governor, cache: AgentCache):
        self.gov = governor
        self.cache = cache

    def enabled(self) -> bool:
        return self.gov is not None

    def analyze(self, gid: str, game: dict, markets: list, user_extra: dict = None) -> list:
        """markets = [{name, selections: [{name, odds}]}] — the full sheet."""
        try:
            sheet = []
            for m in (markets or [])[:14]:
                if not isinstance(m, dict):
                    continue
                for s in m.get("selections") or []:
                    if not isinstance(s, dict) or not s.get("name"):
                        continue
                    try:
                        o = float(s.get("odds") or 0)
                    except (TypeError, ValueError):
                        continue
                    if o and o > 1.05:
                        sheet.append({"market": str(m.get("name") or ""),
                                      "label": str(s.get("name") or ""), "odds": o})
            if not sheet:
                return []
            payload = {
                "game": str(game.get("name") or ""),
                "markets": sheet,
                "note": "Only report legs with clearly positive EV.",
            }
            content = self.gov._chat([
                {"role": "system", "content": SCOUT_SYSTEM},
                {"role": "user", "content": json.dumps(payload, default=str)},
            ], temperature=0.2)
            data = _extract_json(content) or {}
            sels = data.get("selections") if isinstance(data.get("selections"), list) else []
            out = []
            for s in sels[:4]:
                if not isinstance(s, dict):
                    continue
                try:
                    o = float(s.get("odds") or 0)
                    mp = float(s.get("model_prob") or 0)
                    ev = float(s.get("ev") or 0)
                except (TypeError, ValueError):
                    continue
                mk = str(s.get("market") or "other").lower()
                out.append({
                    "label": str(s.get("label") or "")[:80],
                    "market": mk,
                    "odds": o,
                    "model_prob": max(0.05, min(0.95, mp)),
                    "ev": max(-0.2, min(0.5, ev)),
                    "note": str(s.get("note") or "")[:140],
                })
            # cache by gid so _select_football_legs can apply value weighting later
            d = self.cache.load()
            d.setdefault("games", {}).setdefault(str(gid), {})["scout"] = {
                "ts": time.time(), "selections": out}
            self.cache.save(d)
            return out
        except Exception:
            return []


# --------------------------------------------------------------------------
# Risk manager (a calm, deterministic exposure guard)
# --------------------------------------------------------------------------

class RiskManager:
    """Scales stake DOWN while big accumulators are live; only a modest, safe
    boost when the book is nearly empty and the ledger is netting positive."""

    def __init__(self):
        pass

    def stake_scale(self, active_count: int, active_bankroll: float,
                    bankroll: float, net_profit: float) -> tuple:
        scale = 1.0
        reasons = []
        try:
            active_count = int(active_count or 0)
            active_bankroll = float(active_bankroll or 0.0)
            bankroll = float(bankroll or 0.0)
            net_profit = float(net_profit or 0.0)
        except (TypeError, ValueError):
            active_count, active_bankroll, bankroll, net_profit = 0, 0.0, 0.0, 0.0
        if active_count >= 6:
            scale *= 0.80
            reasons.append(f"{active_count} live slips")
        elif active_count >= 4:
            scale *= 0.90
            reasons.append(f"{active_count} live slips")
        if active_bankroll > 0 and bankroll > 0:
            if active_bankroll >= 4 * bankroll:
                scale = min(scale, 0.70)
                reasons.append("live exposure >> bankroll")
            elif active_bankroll >= 2 * bankroll:
                scale = min(scale, 0.85)
                reasons.append("live exposure heavy")
            elif active_bankroll >= bankroll:
                scale = min(scale, 0.92)
        if scale < 0.5:
            scale = 0.5
        if (scale >= 1.0 and active_count <= 2 and active_bankroll < bankroll
                and net_profit > 0 and bankroll > 50):
            scale = 1.10
            reasons.append("book nearly empty & netting positive")
        scale = max(0.5, min(1.25, scale))
        if abs(scale - 1.0) < 1e-9:
            return 1.0, ""
        return round(scale, 3), "; ".join(reasons)


# --------------------------------------------------------------------------
# Calibration / evaluator (deterministic statistics)
# --------------------------------------------------------------------------

CAL_BUCKETS = [("0.00-0.10", 0.00, 0.10), ("0.10-0.20", 0.10, 0.20),
               ("0.20-0.30", 0.20, 0.30), ("0.30-0.40", 0.30, 0.40),
               ("0.40+", 0.40, 1.01)]


class Calibrator:
    """Confidence-bucket audit + per-market edge ledger + retirement calls."""

    def __init__(self, path: str = CALIBRATION_PATH):
        self.path = path

    @staticmethod
    def joint_prob(bet) -> float:
        probs = bet.get("probs") or []
        p = 1.0
        for x in probs:
            try:
                p *= float(x)
            except (TypeError, ValueError):
                continue
        return p if probs else None

    def score(self, rows: list) -> dict:
        """rows: list of settled ledger bets dicts. Returns the audit object.

        Uses probability-weighted attribution matching what _record_settled_stats
        now writes — partial 'won' credits on lost slips rather than binary 0/1.
        The per-market 'won' field may be fractional; hit-rate is won/n.
        """
        buckets = {name: {"n": 0, "won": 0, "hit": 0.0, "expected": 0.0}
                   for name, _, _ in CAL_BUCKETS}
        per_market = {}
        for b in rows or []:
            p = self.joint_prob(b)
            if p is None:
                continue
            st = str(b.get("status") or "")
            won_flag = st in ("won", "void")
            # Joint-probability confidence buckets use the slip-level win flag
            for name, lo, hi in CAL_BUCKETS:
                if lo <= p < hi:
                    buckets[name]["n"] += 1
                    buckets[name]["expected"] += p
                    if won_flag:
                        buckets[name]["won"] += 1

            # Per-market stats use the partial credit stored by _record_settled_stats.
            # For rows written before this change (no fractional won), fall back to binary.
            markets = b.get("markets") or []
            probs   = b.get("probs") or []
            if won_flag:
                for mk in markets:
                    m = per_market.setdefault(str(mk), {"n": 0, "won": 0.0, "expected": 0.0})
                    m["n"]   += 1
                    m["won"] += 1.0
                    m["expected"] += 1.0  # all legs expected to win (they did)
            else:
                fail_probs = [max(0.01, 1.0 - (float(probs[i]) if i < len(probs) else 0.5))
                              for i in range(len(markets))]
                total_fail = sum(fail_probs) or 1.0
                for i, mk in enumerate(markets):
                    p_i   = float(probs[i]) if i < len(probs) else 0.5
                    blame = fail_probs[i] / total_fail
                    m = per_market.setdefault(str(mk), {"n": 0, "won": 0.0, "expected": 0.0})
                    m["n"]   += 1
                    m["won"] += (1.0 - blame)
                    m["expected"] += p_i

        for name, _, _ in CAL_BUCKETS:
            b = buckets[name]
            if b["n"]:
                b["hit"] = round(b["won"] / b["n"], 4)
                b["avg_expected"] = round(b["expected"] / b["n"], 4)
                b["delta"] = round(b["hit"] - b["avg_expected"], 4)
            else:
                b["hit"], b["avg_expected"], b["delta"] = None, None, None
            b["expected"] = round(b["expected"], 4)

        market_weights = {}
        retire = []
        for mk, m in per_market.items():
            if m["n"] >= 10:
                hit  = m["won"] / m["n"]
                pred = m["expected"] / m["n"]
                # Weight relative to predicted hit-rate (was anchored at 0.5, now uses actual pred)
                ratio = hit / max(pred, 0.05)
                market_weights[mk] = round(max(0.85, min(1.15, ratio)), 3)
                if hit < 0.42 and m["n"] >= 20:
                    retire.append(mk)

        audit = {
            "generated_at": datetime.now().isoformat(timespec="seconds"),
            "settled": sum(1 for b in (rows or []) if b.get("status") in ("won", "lost")),
            "buckets": {k: v for k, v in buckets.items()},
            "per_market": {k: {**v,
                               "hit_pct": round(100.0 * v["won"] / v["n"], 1) if v["n"] else None,
                               "pred_pct": round(100.0 * v["expected"] / v["n"], 1) if v["n"] else None}
                           for k, v in per_market.items()},
            "market_weights": market_weights,
            "retire": retire,
        }
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(audit, f, indent=2, default=str)
        except Exception:
            pass
        return audit

    @staticmethod
    def summary_line(audit: dict, settled: int) -> str:
        if settled < 5:
            return f"Calibration: only {settled} settled - too few to score yet."
        parts = []
        for name, b in (audit.get("buckets") or {}).items():
            if b["n"] and b["delta"] is not None:
                parts.append(f"{name} (n={b['n']}, hit {b['hit']:.0%} vs ~{b['avg_expected']:.0%}, Δ{b['delta']:+.0%})")
        msg = " | ".join(parts)
        ret = audit.get("retire") or []
        if ret:
            msg += f" | retiring: {', '.join(ret)}"
        # Best market by adjusted hit rate
        pm = audit.get("per_market") or {}
        if pm:
            best_mk = max(pm.items(),
                          key=lambda kv: float(kv[1].get("won") or 0) / max(int(kv[1].get("n") or 1), 1),
                          default=None)
            if best_mk and int(best_mk[1].get("n") or 0) >= 5:
                mk_hit = float(best_mk[1].get("won") or 0) / max(int(best_mk[1].get("n") or 1), 1)
                msg += f" | best market: {best_mk[0]} ({mk_hit:.0%} adj. hit)"
        return msg


# --------------------------------------------------------------------------
# Daily reporter
# --------------------------------------------------------------------------

REPORT_SYSTEM = """You are the DAILY REPORT writer for a SportPesa betting machine. You are given a day of results (ledger summary) and the governor's notes (journal). Write ONE tight paragraph for the owner: how betting went, what stands out, health flags, and one concrete improvement. Max 5 sentences. No markdown headers. Plain, useful English."""


class Reporter:
    def __init__(self, governor=None):
        self.gov = governor

    def _fallback(self, day, summary, journal):
        try:
            net = float((summary or {}).get("net_profit") or 0)
            won = int((summary or {}).get("won") or 0)
            lost = int((summary or {}).get("lost") or 0)
            act = int((summary or {}).get("active") or 0)
            staked = float((summary or {}).get("staked") or 0)
        except Exception:
            net = won = lost = act = 0
            staked = 0.0
        roi = (net / staked * 100.0) if staked else 0.0
        return (f"{day}: {won} won / {lost} lost ({act} live) on KES {staked:,.0f} staked. "
                f"Net {net:+,.2f} KES ({roi:+.1f}% ROI). " +
                ("Continue what worked." if net >= 0 else "Consider tightening picks next day."))

    def day_summary(self, day, summary, journal) -> str:
        if self.gov is None:
            return self._fallback(day, summary, journal)
        try:
            content = self.gov._chat([
                {"role": "system", "content": REPORT_SYSTEM},
                {"role": "user", "content": json.dumps({"day": day, "ledger": summary,
                                                        "governor_journal": (journal or [])[-6:]},
                                                       default=str)},
            ], temperature=0.3)
            txt = (content or "").strip()
            return txt[:600] if txt else self._fallback(day, summary, journal)
        except Exception:
            return self._fallback(day, summary, journal)


# --------------------------------------------------------------------------
# Notifier (Twilio + generic webhook). Rate-limited, de-duplicated, silent off.
# --------------------------------------------------------------------------

class Notifier:
    def __init__(self, cfg: dict):
        self.cfg = cfg or {}
        self.enabled_flag = bool(self.cfg.get("enabled") or False)
        self.provider = str(self.cfg.get("provider") or "none").lower()
        self._last_send = 0.0
        self._seen = {}  # sha1 -> ts
        self.last_error = ""

    def enabled(self) -> bool:
        return bool(self.enabled_flag and self.provider in ("twilio", "webhook"))

    def deliverable(self) -> bool:
        if not self.enabled():
            return False
        if self.provider == "twilio":
            return bool(self.cfg.get("twilio_sid") and self.cfg.get("twilio_auth")
                        and self.cfg.get("twilio_from") and self.cfg.get("to_phone"))
        if self.provider == "webhook":
            return bool(self.cfg.get("webhook_url"))
        return False

    def send(self, kind: str, text: str) -> bool:
        if not self.deliverable():
            return False
        now = time.time()
        if now - self._last_send < 5.0:
            return False
        key = hashlib.sha1(f"{kind}|{text}".encode("utf-8")).hexdigest()
        if now - (self._seen.get(key) or 0) < 180.0:
            return False
        try:
            ok = False
            if self.provider == "twilio":
                ok = self._send_twilio(text)
            else:
                ok = self._send_webhook(kind, text)
            if ok:
                self._last_send = now
                self._seen[key] = now
            return ok
        except Exception as e:
            self.last_error = str(e)[:160]
            return False

    def _send_twilio(self, body: str) -> bool:
        sid = self.cfg.get("twilio_sid")
        url = f"https://api.twilio.com/2010-04-01/Accounts/{sid}/Messages.json"
        data = urllib.parse.urlencode({
            "From": self.cfg.get("twilio_from"),
            "To": self.cfg.get("to_phone"),
            "Body": body[:1600],
        }).encode()
        req = urllib.request.Request(url, data=data, method="POST")
        token = (sid + ":" + str(self.cfg.get("twilio_auth"))).encode()
        req.add_header("Authorization", "Basic " + _b64(token))
        req.add_header("Content-Type", "application/x-www-form-urlencoded")
        with urllib.request.urlopen(req, timeout=20) as r:
            return r.status < 300

    def _send_webhook(self, kind: str, body: str) -> bool:
        payload = {"kind": kind, "message": body[:1800],
                   "token": self.cfg.get("webhook_token") or ""}
        req = urllib.request.Request(
            self.cfg.get("webhook_url"),
            data=json.dumps(payload).encode("utf-8"), method="POST")
        req.add_header("Content-Type", "application/json")
        with urllib.request.urlopen(req, timeout=20) as r:
            return r.status < 300


def _b64(raw: bytes) -> str:
    return base64.b64encode(raw).decode("ascii")


# --------------------------------------------------------------------------
# Supervisor — watchdog that makes sure every agent + the engine itself is
# running, healthy, and has not silently stalled. Runs from the engine's
# background agent worker thread, publishing a health report and triggering
# corrective nudges when something looks wrong.
# --------------------------------------------------------------------------

SUPERVISOR_STATE_PATH = os.path.join(os.getcwd(), "sportsape_supervisor.json")


# --------------------------------------------------------------------------
# BalanceReportCleaner — intelligently prunes old balance_report_*.csv and
# balance_report_*.txt files so the workspace never fills up with stale data.
# --------------------------------------------------------------------------

class BalanceReportCleaner:
    """Workspace cleaner — removes ALL temporary files created by the tool.

    Categories cleaned:
    1. balance_report_*.csv / *.txt  — older than *max_age_days* (default 1 day)
    2. Python bytecode cache: __pycache__/**/*.pyc, *.pyo
    3. Run/terminal log files: run24h_*.log, run*.log (older than 3 days)
    4. Chrome/Selenium temp profiles: chrome_debug_*, selenium-manager-*
    5. sportsape_grok_journal.json trimmed to last 50 entries (never fully deleted)
    6. sportsape_alerts.log trimmed to last 200 lines (keeps recent history)

    Always keeps:
    - Any file younger than 24 h (safety floor)
    - Ledger, stats, calibration, settings, agent-cache — never touched

    Runs at most once per hour.
    """

    FILE_PATTERN = re.compile(
        r"^balance_report_(\d{8}_\d{4})\.(csv|txt)$", re.IGNORECASE
    )
    LOG_PATTERN = re.compile(r"^run.*\.(log|out|err)$", re.IGNORECASE)
    MIN_KEEP_HOURS   = 24       # never delete anything younger than this
    BALANCE_MAX_DAYS = 1.0      # delete balance reports after 1 day (they pile up fast)
    LOG_MAX_DAYS     = 3.0      # delete run logs after 3 days
    RUN_INTERVAL_S   = 3600.0   # re-scan at most every hour

    # Files that must NEVER be deleted
    _PROTECTED = {
        "sportsape_ledger.json", "sportsape_ledger_archive.json",
        "sportsape_stats.json", "sportsape_calibration.json",
        "sportsape_settings.json", "sportsape_agent_cache.json",
        "sportsape_balances.json", "sportsape_supervisor.json",
        "sportsape_sched_state.json", "sportsape_usage.json",
        "sportsape_form_cache.json", "sportsape_withdraw.json",
        "sportsape_jackpot_state.json",
    }

    def __init__(self, max_age_days: float = 1.0, search_dir: str = None):
        self.max_age_days = float(max_age_days)
        self.search_dir = search_dir or os.path.dirname(os.path.abspath(__file__))
        self._last_run: float = 0.0

    def should_run(self) -> bool:
        return (time.time() - self._last_run) >= self.RUN_INTERVAL_S

    def run(self, gui_callback=None) -> dict:
        """Scan and clean.  Returns {scanned, deleted, kept, freed_bytes}."""
        now = time.time()
        self._last_run = now
        min_keep_s     = self.MIN_KEEP_HOURS * 3600.0

        scanned = deleted = kept = 0
        freed = 0

        def _try_delete(path: str, label: str) -> bool:
            nonlocal deleted, freed
            try:
                size = os.path.getsize(path)
                os.remove(path)
                freed += size
                deleted += 1
                if gui_callback:
                    try:
                        gui_callback(f"🗑️ CLEANER: removed {label} ({size:,} bytes)")
                    except Exception:
                        pass
                return True
            except OSError:
                return False

        try:
            entries = os.listdir(self.search_dir)
        except OSError:
            return {"scanned": 0, "deleted": 0, "kept": 0, "freed_bytes": 0}

        for name in entries:
            full = os.path.join(self.search_dir, name)
            if name in self._PROTECTED:
                continue

            # ── Balance reports ─────────────────────────────────────────
            if self.FILE_PATTERN.match(name):
                scanned += 1
                try:
                    age_s = now - os.path.getmtime(full)
                except OSError:
                    age_s = 0
                if age_s > min_keep_s and age_s > self.BALANCE_MAX_DAYS * 86400:
                    _try_delete(full, name)
                else:
                    kept += 1
                continue

            # ── Run / terminal log files ─────────────────────────────────
            if self.LOG_PATTERN.match(name) and os.path.isfile(full):
                scanned += 1
                try:
                    age_s = now - os.path.getmtime(full)
                except OSError:
                    age_s = 0
                if age_s > min_keep_s and age_s > self.LOG_MAX_DAYS * 86400:
                    _try_delete(full, name)
                else:
                    kept += 1
                continue

        # ── Python bytecode cache ────────────────────────────────────────
        pycache = os.path.join(self.search_dir, "__pycache__")
        if os.path.isdir(pycache):
            for fname in os.listdir(pycache):
                if fname.endswith((".pyc", ".pyo")):
                    scanned += 1
                    fp = os.path.join(pycache, fname)
                    try:
                        age_s = now - os.path.getmtime(fp)
                    except OSError:
                        age_s = 0
                    # .pyc files older than 24h are safe to remove — Python re-generates them
                    if age_s > min_keep_s:
                        _try_delete(fp, f"__pycache__/{fname}")
                    else:
                        kept += 1

        # ── Grok journal: trim to last 50 entries ────────────────────────
        journal_path = os.path.join(self.search_dir, "sportsape_grok_journal.json")
        if os.path.isfile(journal_path):
            try:
                with open(journal_path, "r", encoding="utf-8") as f:
                    journal = json.load(f)
                if isinstance(journal, list) and len(journal) > 50:
                    old_size = os.path.getsize(journal_path)
                    journal = journal[-50:]
                    with open(journal_path, "w", encoding="utf-8") as f:
                        json.dump(journal, f, indent=2)
                    new_size = os.path.getsize(journal_path)
                    saved = old_size - new_size
                    if saved > 0 and gui_callback:
                        try:
                            gui_callback(
                                f"🗑️ CLEANER: trimmed grok journal to 50 entries "
                                f"(freed {saved:,} bytes)")
                        except Exception:
                            pass
                    freed += max(0, saved)
                    deleted += 1
            except Exception:
                pass

        # ── Alerts log: trim to last 200 lines ──────────────────────────
        alerts_path = os.path.join(self.search_dir, "sportsape_alerts.log")
        if os.path.isfile(alerts_path):
            try:
                with open(alerts_path, "r", encoding="utf-8") as f:
                    lines = f.readlines()
                if len(lines) > 200:
                    old_size = os.path.getsize(alerts_path)
                    lines = lines[-200:]
                    with open(alerts_path, "w", encoding="utf-8") as f:
                        f.writelines(lines)
                    new_size = os.path.getsize(alerts_path)
                    saved = old_size - new_size
                    if saved > 0 and gui_callback:
                        try:
                            gui_callback(
                                f"🗑️ CLEANER: trimmed alerts log to 200 lines "
                                f"(freed {saved:,} bytes)")
                        except Exception:
                            pass
                    freed += max(0, saved)
            except Exception:
                pass

        if deleted == 0 and gui_callback:
            try:
                gui_callback(f"🗂️ CLEANER: {scanned} file(s) checked — workspace is clean")
            except Exception:
                pass

        return {
            "scanned": scanned,
            "deleted": deleted,
            "kept": kept,
            "freed_bytes": freed,
        }


# --------------------------------------------------------------------------
# Fibi (Supervisor) — master watchdog: monitors engine liveness, every
# sub-agent heartbeat, pick quality, and file hygiene.  When something
# stalls she reports it clearly AND emits a wake-up recommendation so the
# engine can restart the offending subsystem on its next pass.
# --------------------------------------------------------------------------
# --------------------------------------------------------------------------
# SessionHealthAgent — tracks last-login time per account and flags when the
# session is approaching SportPesa's ~4-hour cookie TTL so the engine can
# re-login proactively rather than discovering it mid-bet.
# --------------------------------------------------------------------------

class SessionHealthAgent:
    """Monitors last-login timestamps per phone number and emits a re-login
    recommendation before the session expires.

    SportPesa sessions typically last 4 hours.  We warn at 3.5 hours and
    recommend a forced re-login at 3.75 hours, giving the engine one full
    betting round to act before the cookie actually expires.
    """

    SESSION_TTL_S    = 4.0 * 3600   # SportPesa session ~4 h
    WARN_AT_S        = 3.5 * 3600   # warn when session is 3.5 h old
    FORCE_RELOGIN_S  = 3.75 * 3600  # force re-login when 3.75 h old
    CHECK_INTERVAL_S = 120.0        # check every 2 min

    def __init__(self):
        self._last_run: float = 0.0
        # {phone: last_login_ts}
        self._login_times: dict = {}

    def record_login(self, phone: str):
        """Call this every time a successful login is confirmed for a phone."""
        self._login_times[str(phone)] = time.time()

    def should_run(self) -> bool:
        return (time.time() - self._last_run) >= self.CHECK_INTERVAL_S

    def check(self, phones: list, gui_callback=None) -> list:
        """Check all known phones and return a list of action dicts.

        Each action is one of:
          {"action": "warn_session", "phone": p, "age_h": float}
          {"action": "force_relogin", "phone": p, "age_h": float}
        Never raises.
        """
        self._last_run = time.time()
        now = time.time()
        actions = []
        for phone in (phones or []):
            last = self._login_times.get(str(phone))
            if last is None:
                continue  # no login recorded yet — too early to warn
            age = now - last
            if age >= self.FORCE_RELOGIN_S:
                age_h = round(age / 3600, 1)
                msg = (f"🔐 Session for {phone} is {age_h}h old — "
                       "forcing re-login before it expires mid-bet")
                if gui_callback:
                    try:
                        gui_callback(msg)
                    except Exception:
                        pass
                actions.append({"action": "force_relogin", "phone": str(phone),
                                 "age_h": age_h})
            elif age >= self.WARN_AT_S:
                age_h = round(age / 3600, 1)
                msg = (f"⏰ Session for {phone} is {age_h}h old — "
                       "will force re-login soon")
                if gui_callback:
                    try:
                        gui_callback(msg)
                    except Exception:
                        pass
                actions.append({"action": "warn_session", "phone": str(phone),
                                 "age_h": age_h})
        return actions


# --------------------------------------------------------------------------
# APIFootballAgent — fetches real fixture and team form data from
# api-football.com (free tier: 100 req/day).  Enriches the analyst's
# game payload with actual recent results, goals scored/conceded, and
# standings position — the biggest single edge improvement available.
#
# Budget management: we use at most 60 of the 100 daily requests so there
# is always headroom.  Each team lookup costs 1 request; we cache results
# for 6 hours so the same team is never looked up twice in a session.
# --------------------------------------------------------------------------

class APIFootballAgent:
    """Fetches recent form and fixture data from api-football.com.

    Free tier: 100 requests per day (resets 00:00 UTC).
    We cache per-team results for 6 h so a 2-account session running 20 bets
    only consumes ~10–20 requests total (teams repeat across fixtures).

    What we fetch per game (2 requests: home team + away team):
    - Last 5 fixtures: result (W/D/L), goals for/against, home/away
    - League position (if available in standings)

    The resulting form dict matches the shape the ResearchAnalyst already
    expects: {"results": ["W","L","D",...], "form_score": 0-100, "n": 5,
              "goals_for": float, "goals_against": float, "league": str}
    """

    BASE_URL   = "https://v3.football.api-sports.io"
    CACHE_TTL  = 6 * 3600     # re-fetch after 6 h
    MAX_DAILY  = 60           # stay well inside the 100/day free limit
    TIMEOUT    = 8            # seconds per request

    def __init__(self, api_key: str = "", api_keys: list = None):
        # Support multiple keys in round-robin rotation
        keys = [k.strip() for k in (api_keys or []) if str(k or "").strip()]
        if not keys and api_key:
            keys = [api_key.strip()]
        self._keys = keys
        self._key_idx = 0
        self.api_key = keys[0] if keys else ""
        self._team_cache: dict = {}
        self._daily_used: int  = 0
        self._day_key: str     = ""

    def enabled(self) -> bool:
        return bool(self._keys)

    def _rotate_key(self):
        """Move to the next key in the list."""
        if len(self._keys) > 1:
            self._key_idx = (self._key_idx + 1) % len(self._keys)
            self.api_key = self._keys[self._key_idx]

    def _reset_daily_if_needed(self):
        today = datetime.utcnow().strftime("%Y-%m-%d")
        if today != self._day_key:
            self._day_key   = today
            self._daily_used = 0

    def _budget_ok(self) -> bool:
        self._reset_daily_if_needed()
        return self._daily_used < self.MAX_DAILY

    def _get(self, endpoint: str, params: dict) -> dict:
        """Make one API-Football request with key rotation on 429/403."""
        if not self._keys:
            return {}
        qs = "&".join(f"{k}={v}" for k, v in params.items())
        for attempt in range(len(self._keys)):
            key = self._keys[(self._key_idx + attempt) % len(self._keys)]
            url = f"{self.BASE_URL}/{endpoint}?{qs}"
            req = urllib.request.Request(url)
            req.add_header("x-apisports-key", key)
            req.add_header("Accept", "application/json")
            try:
                with urllib.request.urlopen(req, timeout=self.TIMEOUT) as r:
                    data = json.loads(r.read().decode("utf-8"))
                self._daily_used += 1
                # Success — lock in this key index
                self._key_idx = (self._key_idx + attempt) % len(self._keys)
                self.api_key = self._keys[self._key_idx]
                return data if isinstance(data, dict) else {}
            except urllib.error.HTTPError as exc:
                if exc.code in (429, 403):
                    # Rate limited — try next key
                    continue
                return {}
            except Exception:
                return {}
        return {}

    def _search_team_id(self, name: str) -> int:
        """Search for a team by name and return its ID, or 0 if not found."""
        data = self._get("teams", {"search": name[:30]})
        results = data.get("response") or []
        if not results:
            return 0
        # Pick the first result — for SportPesa games the first match is usually right
        try:
            return int((results[0].get("team") or {}).get("id") or 0)
        except (TypeError, ValueError):
            return 0

    def _fetch_form(self, team_name: str) -> dict:
        """Fetch last-5 form for a single team. Returns form dict or {}."""
        if not self._budget_ok():
            return {}
        cache_key = team_name.lower().strip()
        cached = self._team_cache.get(cache_key)
        if cached:
            ts, form = cached
            if time.time() - ts < self.CACHE_TTL:
                return form

        if not self._budget_ok():
            return {}
        team_id = self._search_team_id(team_name)
        if not team_id:
            return {}

        if not self._budget_ok():
            return {}
        data = self._get("fixtures", {
            "team": team_id,
            "last": 5,
            "status": "FT",      # finished only
        })
        fixtures = data.get("response") or []
        if not fixtures:
            return {}

        results  = []
        goals_for    = 0.0
        goals_against = 0.0
        for f in fixtures[-5:]:
            teams = f.get("teams") or {}
            score = f.get("score") or {}
            ft    = (score.get("fulltime") or {})
            home_id   = int((teams.get("home") or {}).get("id") or 0)
            is_home   = (home_id == team_id)
            h_goals   = int(ft.get("home") or 0)
            a_goals   = int(ft.get("away") or 0)
            gf = h_goals if is_home else a_goals
            ga = a_goals if is_home else h_goals
            goals_for     += gf
            goals_against += ga
            if gf > ga:
                results.append("W")
            elif gf == ga:
                results.append("D")
            else:
                results.append("L")

        n = len(results)
        wins   = results.count("W")
        draws  = results.count("D")
        # form_score: simple 0-100 based on W=3pts, D=1pt out of max 15pts
        pts    = wins * 3 + draws
        form_score = round(pts / max(n * 3, 1) * 100)

        form = {
            "results":       results,
            "form_score":    form_score,
            "n":             n,
            "goals_for":     round(goals_for / max(n, 1), 2),
            "goals_against": round(goals_against / max(n, 1), 2),
            "source":        "api-football",
        }
        self._team_cache[cache_key] = (time.time(), form)
        return form

    def get_game_form(self, home_name: str, away_name: str) -> tuple:
        """Return (home_form, away_form) dicts for a game.  Never raises."""
        try:
            if not self.enabled() or not self._budget_ok():
                return {}, {}
            home_form = self._fetch_form(home_name)
            away_form = self._fetch_form(away_name)
            return home_form, away_form
        except Exception:
            return {}, {}

    @property
    def daily_used(self) -> int:
        self._reset_daily_if_needed()
        return self._daily_used


# --------------------------------------------------------------------------
# LeagueContextAgent — detects which league a game belongs to and injects
# league-specific stats (avg goals, scoring tendencies) into the analyst
# payload. No external API needed — pure rule-based knowledge.
# --------------------------------------------------------------------------

# League knowledge base: average goals per game, BTTS rate, Over 2.5 rate.
# Sources: historical data compiled from major football statistics sites.
_LEAGUE_STATS = {
    "Premier League":      {"avg_goals": 2.85, "btts_rate": 0.56, "over25_rate": 0.56, "home_win": 0.44},
    "La Liga":             {"avg_goals": 2.55, "btts_rate": 0.50, "over25_rate": 0.48, "home_win": 0.46},
    "Bundesliga":          {"avg_goals": 3.10, "btts_rate": 0.59, "over25_rate": 0.60, "home_win": 0.43},
    "Serie A":             {"avg_goals": 2.60, "btts_rate": 0.52, "over25_rate": 0.50, "home_win": 0.44},
    "Ligue 1":             {"avg_goals": 2.55, "btts_rate": 0.50, "over25_rate": 0.48, "home_win": 0.46},
    "Eredivisie":          {"avg_goals": 3.10, "btts_rate": 0.59, "over25_rate": 0.61, "home_win": 0.47},
    "Championship":        {"avg_goals": 2.45, "btts_rate": 0.50, "over25_rate": 0.46, "home_win": 0.41},
    "Kenyan Premier":      {"avg_goals": 1.85, "btts_rate": 0.35, "over25_rate": 0.28, "home_win": 0.46},
    "Ethiopian Premier":   {"avg_goals": 2.10, "btts_rate": 0.40, "over25_rate": 0.35, "home_win": 0.48},
    "Tanzanian Premier":   {"avg_goals": 1.90, "btts_rate": 0.36, "over25_rate": 0.30, "home_win": 0.47},
    "Ugandan Premier":     {"avg_goals": 2.00, "btts_rate": 0.38, "over25_rate": 0.32, "home_win": 0.45},
    "CAF Champions":       {"avg_goals": 2.20, "btts_rate": 0.42, "over25_rate": 0.38, "home_win": 0.50},
    "World Cup":           {"avg_goals": 2.65, "btts_rate": 0.51, "over25_rate": 0.51, "home_win": 0.35},
    "Euro":                {"avg_goals": 2.45, "btts_rate": 0.49, "over25_rate": 0.47, "home_win": 0.38},
    "Africa Cup":          {"avg_goals": 2.10, "btts_rate": 0.40, "over25_rate": 0.34, "home_win": 0.36},
    "Champions League":    {"avg_goals": 2.90, "btts_rate": 0.57, "over25_rate": 0.57, "home_win": 0.48},
    "Europa League":       {"avg_goals": 2.85, "btts_rate": 0.56, "over25_rate": 0.55, "home_win": 0.47},
    "default":             {"avg_goals": 2.40, "btts_rate": 0.47, "over25_rate": 0.44, "home_win": 0.44},
}

# Team name fragments that identify a league
_LEAGUE_HINTS = [
    ({"arsenal", "chelsea", "liverpool", "manchester", "tottenham", "man city",
      "man united", "newcastle", "west ham", "aston villa", "brighton", "brentford",
      "fulham", "everton", "wolves", "crystal palace", "burnley", "luton",
      "nottm forest", "sheffield", "bournemouth", "leicester", "ipswich",
      "southampton"}, "Premier League"),
    ({"real madrid", "barcelona", "atletico", "sevilla", "valencia", "villarreal",
      "betis", "sociedad", "athletic", "osasuna", "celta", "getafe", "girona",
      "las palmas", "alaves"}, "La Liga"),
    ({"dortmund", "bayern", "leverkusen", "leipzig", "frankfurt", "wolfsburg",
      "hoffenheim", "freiburg", "mainz", "koln", "bremen", "augsburg",
      "bochum", "union berlin", "heidenheim", "darmstadt"}, "Bundesliga"),
    ({"juventus", "milan", "inter", "napoli", "roma", "lazio", "fiorentina",
      "atalanta", "torino", "bologna", "monza", "sassuolo", "lecce", "udinese",
      "verona", "genoa", "cagliari", "empoli", "salernitana", "frosinone"}, "Serie A"),
    ({"psg", "marseille", "lyon", "monaco", "lille", "rennes", "nice", "lens",
      "strasbourg", "montpellier", "reims", "toulouse", "lorient", "nantes",
      "brest", "le havre", "metz", "clermont", "ajaccio"}, "Ligue 1"),
    ({"ajax", "psv", "feyenoord", "az alkmaar", "utrecht", "twente", "groningen",
      "vitesse", "sparta", "heracles", "nec", "excelsior", "go ahead"}, "Eredivisie"),
    ({"gor mahia", "afc leopards", "tusker", "kakamega", "vihiga", "wazito",
      "mathare", "nairobi city", "bandari", "ulinzi", "posta rangers",
      "nzoia", "sofapaka", "kariobangi", "fc talanta"}, "Kenyan Premier"),
    ({"saint george", "ethiopia bunna", "fasil ketema", "hawassa", "wolkite",
      "dedebit", "dire dawa", "bahir dar", "adama", "arba minch"}, "Ethiopian Premier"),
    ({"simba", "yanga", "azam", "namungo", "mtibwa", "mwadui", "coastal union",
      "kagera sugar", "ihefu", "geita gold"}, "Tanzanian Premier"),
    ({"vipers", "kcca", "express", "wakiso", "sc villa", "bright stars",
      "bul fc", "mbarara", "onduparaka", "police fc"}, "Ugandan Premier"),
    ({"champions league", "cl group", "cl knockout"}, "Champions League"),
    ({"europa league", "uel group", "uel knockout", "conference"}, "Europa League"),
    ({"africa cup", "afcon", "can 2023", "can 2025"}, "Africa Cup"),
    ({"world cup", "fifa world", "wc qualifier"}, "World Cup"),
    ({"euro 2024", "euro 2028", "european championship"}, "Euro"),
    ({"caf champions", "total energies caf", "caf cc"}, "CAF Champions"),
]


class LeagueContextAgent:
    """Detects which football league/competition a game belongs to and
    returns a context dict with league-specific scoring statistics.

    This context is injected into the analyst prompt so APEX can reason
    about whether Over 2.5 is historically likely in this specific league
    (e.g. Bundesliga ~60% vs Kenyan Premier ~28%).

    No external API — pure rule-based pattern matching on team names.
    """

    @staticmethod
    def detect(game_name: str) -> tuple:
        """Return (league_name, stats_dict) for the given 'Home vs Away' string."""
        name_lower = (game_name or "").lower()
        for keywords, league in _LEAGUE_HINTS:
            for kw in keywords:
                if kw in name_lower:
                    stats = _LEAGUE_STATS.get(league, _LEAGUE_STATS["default"])
                    return league, stats
        return "Unknown", _LEAGUE_STATS["default"]

    @staticmethod
    def context_note(game_name: str) -> str:
        """Return a one-line context string for injection into the analyst prompt."""
        league, stats = LeagueContextAgent.detect(game_name)
        return (
            f"League context: {league} — avg {stats['avg_goals']:.1f} goals/game, "
            f"BTTS {stats['btts_rate']:.0%}, Over 2.5 {stats['over25_rate']:.0%}, "
            f"home win {stats['home_win']:.0%}. Use this to calibrate your probability."
        )


# --------------------------------------------------------------------------
# BetRecoveryAgent — analyses settled losses to identify systematically weak
# market/game patterns and emits concrete recommendations to avoid them.
# --------------------------------------------------------------------------

class BetRecoveryAgent:
    """After lost slips, identifies the leg most likely to have failed
    (lowest probability among all legs) and tracks which market types,
    time-of-day buckets, and odds bands correlate with repeated losses.

    After ≥10 losses with the same weak-leg market it emits a named
    recommendation that Fibi can act on:
      "stop picking <market> legs — X consecutive slips had a <market> leg
       as the lowest-probability selection and all lost."

    Also tracks:
    - Which market/time-of-day combos keep losing
    - Win/loss streak (if we're on a bad run, scale back max_legs)
    """

    MIN_LOSSES_TO_FLAG  = 5    # flag after this many losses with same weak leg
    CHECK_INTERVAL_S    = 600  # re-analyse every 10 min

    def __init__(self):
        self._last_run: float = 0.0
        # {market: {"weak_leg_losses": int, "last_flag_ts": float}}
        self._weak_market: dict = {}
        self._streak: int = 0   # current loss streak (positive = losses, negative = wins)

    def should_run(self) -> bool:
        return (time.time() - self._last_run) >= self.CHECK_INTERVAL_S

    def analyse(self, bets: list, gui_callback=None) -> list:
        """Scan the ledger and return a list of recommendation dicts.

        Each recommendation:
          {"action": "avoid_market", "market": str, "losses": int,
           "reason": str, "severity": "medium"}
        or
          {"action": "reduce_legs", "reason": str, "severity": "medium"}

        Never raises.
        """
        self._last_run = time.time()
        if not bets:
            return []

        # Count losses where a specific market was the weakest leg
        weak_counts: dict = {}    # market -> consecutive weak-leg-loss count
        recent_outcomes: list = []

        for b in reversed(bets):  # most recent first
            st = str(b.get("status") or "")
            if st.startswith("shadow") or st in ("active", "void"):
                continue
            if st not in ("won", "lost"):
                continue
            recent_outcomes.append(st)
            if st != "lost":
                continue
            markets = b.get("markets") or []
            probs   = b.get("probs") or []
            if not markets or not probs:
                continue
            # Find the leg with the lowest probability — that's the suspected culprit
            weakest_idx = min(range(len(markets)),
                              key=lambda i: float(probs[i]) if i < len(probs) else 1.0)
            weak_mk = markets[weakest_idx] if weakest_idx < len(markets) else None
            if weak_mk:
                weak_counts[str(weak_mk)] = weak_counts.get(str(weak_mk), 0) + 1

        # Current loss streak
        streak = 0
        for outcome in recent_outcomes:
            if outcome == "lost":
                streak += 1
            else:
                break
        self._streak = streak

        recommendations = []

        # Flag persistently weak markets
        for mk, count in weak_counts.items():
            if count >= self.MIN_LOSSES_TO_FLAG:
                prev = self._weak_market.get(mk, {})
                prev_count = int(prev.get("weak_leg_losses") or 0)
                # Only re-flag when count increases by 3+ (avoid spam)
                if count >= prev_count + 3 or prev_count == 0:
                    reason = (f"{mk} was the weakest leg in {count} of your recent "
                              f"lost slips — consider avoiding it or requiring "
                              "higher confidence before including it")
                    if gui_callback:
                        try:
                            gui_callback(f"🔍 BetRecovery: {reason}")
                        except Exception:
                            pass
                    recommendations.append({
                        "action": "avoid_market",
                        "market": mk,
                        "losses": count,
                        "reason": reason,
                        "severity": "medium",
                    })
                self._weak_market[mk] = {"weak_leg_losses": count,
                                          "last_flag_ts": time.time()}

        # Streak alert
        if streak >= 5:
            reason = (f"{streak} consecutive losses — consider reducing "
                      "max legs per slip to 3 until the streak breaks")
            if gui_callback:
                try:
                    gui_callback(f"🔍 BetRecovery: {reason}")
                except Exception:
                    pass
            recommendations.append({
                "action": "reduce_legs",
                "reason": reason,
                "severity": "medium",
            })

        return recommendations


# --------------------------------------------------------------------------
# BetHistoryAgent — continuously reads the in-memory ledger to surface a
# live summary of every bet's current status.  It never touches the browser;
# it works purely from the bets list the engine maintains in RAM, so it can
# run from the background agent worker thread with zero Selenium overhead.
# --------------------------------------------------------------------------

class BetHistoryAgent:
    """Reads the engine's in-memory bet ledger and emits a concise status
    summary — won / lost / active counts, total staked, net P&L, and the
    last 5 settled results — so there is always a fresh human-readable
    view of what is happening without having to scrape the site again."""

    # How many recent settled bets to show in each summary line
    RECENT_SHOW = 5
    # Minimum interval between two full summaries (seconds)
    MIN_INTERVAL_S = 300.0

    def __init__(self):
        self._last_run: float = 0.0

    def should_run(self) -> bool:
        return (time.time() - self._last_run) >= self.MIN_INTERVAL_S

    def run(self, bets: list, gui_callback=None) -> dict:
        """Parse *bets* (the engine's ledger list) and emit a status summary.

        Returns a summary dict with keys: active, won, lost, void, net,
        staked, recent (last N settled), raw_lines (list of log strings).
        Never raises.
        """
        try:
            bets = list(bets or [])
        except Exception:
            bets = []

        active, won, lost, void_c = 0, 0, 0, 0
        shadow = 0
        total_staked = 0.0
        net = 0.0
        recent_settled = []

        for b in bets:
            st = str(b.get("status") or "active").lower()
            stake = float(b.get("stake") or 0)
            # Shadow bets are learning-only entries (never really placed) — they
            # must not inflate the live-game count or the money staked.
            if st.startswith("shadow"):
                shadow += 1
                continue
            total_staked += stake
            if st == "won":
                won += 1
                w = float(b.get("won_amount") or b.get("possible_win") or 0)
                net += w - stake
                recent_settled.append({
                    "id": b.get("id") or "?",
                    "status": "🏆 WON",
                    "stake": stake,
                    "return": w,
                    "settled_at": b.get("settled_at") or "",
                    "odds": b.get("odds") or "",
                })
            elif st == "lost":
                lost += 1
                net -= stake
                recent_settled.append({
                    "id": b.get("id") or "?",
                    "status": "❌ LOST",
                    "stake": stake,
                    "return": 0.0,
                    "settled_at": b.get("settled_at") or "",
                    "odds": b.get("odds") or "",
                })
            elif st == "void":
                void_c += 1
                recent_settled.append({
                    "id": b.get("id") or "?",
                    "status": "↩️ VOID",
                    "stake": stake,
                    "return": stake,
                    "settled_at": b.get("settled_at") or "",
                    "odds": b.get("odds") or "",
                })
            else:
                active += 1

        # Sort by settled time descending and keep the N most recent
        recent_settled.sort(key=lambda x: x.get("settled_at") or "", reverse=True)
        recent_settled = recent_settled[: self.RECENT_SHOW]

        roi = (net / total_staked * 100.0) if total_staked > 0 else 0.0
        total_bets = won + lost + void_c + active + shadow

        shadow_part = f" | 👻 {shadow} shadow" if shadow else ""
        lines = []
        lines.append(
            f"📋 BET HISTORY: {total_bets} total | "
            f"🏆 {won} won | ❌ {lost} lost | ↩️ {void_c} void | "
            f"⏳ {active} live{shadow_part} | "
            f"staked KES {total_staked:,.2f} | net {net:+,.2f} ({roi:+.1f}% ROI)"
        )
        if recent_settled:
            parts = []
            for r in recent_settled:
                if r["return"] > 0:
                    amount = f"KES +{r['return']:,.2f}"
                else:
                    amount = f"KES -{r['stake']:,.2f}"
                parts.append(f"{r['status']} #{r['id']} {amount}")
            lines.append("  Recent: " + "  ".join(parts))

        if gui_callback is not None:
            for ln in lines:
                try:
                    gui_callback(ln)
                except Exception:
                    pass

        self._last_run = time.time()

        return {
            "active": active,
            "won": won,
            "lost": lost,
            "void": void_c,
            "net": round(net, 2),
            "staked": round(total_staked, 2),
            "roi": round(roi, 2),
            "recent": recent_settled,
            "raw_lines": lines,
            "ts": self._last_run,
        }


# --------------------------------------------------------------------------
# Supervisor — watchdog that makes sure every agent + the engine itself is
# running, healthy, and has not silently stalled. Runs from the engine's
# background agent worker thread, publishing a health report and triggering
# corrective nudges when something looks wrong.
# --------------------------------------------------------------------------


class Fibi:
    """Fibi — the master supervisor watchdog.

    Monitors:
    - engine liveness (is the crawl/bet loop advancing or stuck?)
    - account progress (has an account been parked too long? is daily
      budget on-track?)
    - every sub-agent heartbeat (research analyst, scout, risk, calibrator,
      reporter, bet_history, cleaner — each has a named silence window)
    - pick quality (are cached picks genuinely researched? are they confident
      enough to build a strong accumulator from?)
    - browser/driver health (is the selenium session alive?)

    Fibi NEVER directly acts on the engine — she RECOMMENDS via the hub's
    pending queue AND emits a "wake_up_agent" nudge for every silent agent
    so the engine's worker thread can restart that subsystem on its next
    pass.  She speaks clearly in the log so the owner always knows what is
    happening."""

    ENGINE_STALL_THRESHOLD_S = 900      # 15 min without a round => STALL
    ACCOUNT_PARK_THRESHOLD_S = 1800     # parked > 30 min => escalate
    BALANCE_UNREADABLE_THRESHOLD = 5    # 5 consecutive unreadable rounds
    DRIVER_HEAL_CAP_PER_HOUR = 6        # more than 6 driver rebuilds/hour => alert
    NO_BET_THRESHOLD_S = 14400          # 4h without a placed bet => alert

    def __init__(self, cache: AgentCache = None):
        self.cache = cache or AgentCache()
        self.state = self._load_state()

    def _load_state(self) -> dict:
        try:
            with open(SUPERVISOR_STATE_PATH, "r", encoding="utf-8") as f:
                d = json.load(f)
            return d if isinstance(d, dict) else {}
        except Exception:
            return {
                "started_at": time.time(),
                "last_round_ts": 0.0,
                "last_placed_ts": 0.0,
                "last_placed_phone": "",
                "consecutive_balance_unreadable": {},
                "consecutive_aborts": 0,
                "driver_heals_last_hour": [],
                "parked_since": {},
                "agent_heartbeats": {},
                "warnings": [],
                "recommendations": [],
                "last_check": 0.0,
            }

    def _save_state(self):
        try:
            self.state["last_check"] = time.time()
            with open(SUPERVISOR_STATE_PATH, "w", encoding="utf-8") as f:
                json.dump(self.state, f, indent=2, default=str)
        except Exception:
            pass

    # -- called by the engine on every significant event -----------------
    def beat_round(self, engine_state: dict, phone: str):
        """Mark that a crawl-and-bet round finished (any status)."""
        self.state["last_round_ts"] = time.time()
        self.state.setdefault("rounds_by_phone", {})[str(phone or "")] = time.time()
        self._prune_driver_heals()
        self._save_state()

    def beat_bet_placed(self, phone: str, stake: float, odds: float):
        """Mark a successful placement."""
        now = time.time()
        self.state["last_placed_ts"] = now
        self.state["last_placed_phone"] = str(phone or "")
        self.state["consecutive_aborts"] = 0
        self.state["consecutive_balance_unreadable"] = {}
        self.state.setdefault("placed", []).append({
            "ts": now, "phone": str(phone or ""),
            "stake": round(float(stake or 0), 2),
            "odds": round(float(odds or 0), 2),
        })
        self._save_state()

    def beat_balance_unreadable(self, phone: str):
        k = str(phone or "")
        n = int(self.state["consecutive_balance_unreadable"].get(k, 0)) + 1
        self.state["consecutive_balance_unreadable"][k] = n
        return n

    def beat_balance_read(self, phone: str):
        """A successful balance read ends the unreadable streak.

        The counter is about CONSECUTIVE unreadable rounds, so it has to clear
        when a read succeeds — not only when a bet is placed. Otherwise an
        account whose board is simply too thin to bet on keeps a stale streak
        and Fibi nags about balance failures forever.
        """
        k = str(phone or "")
        if int(self.state["consecutive_balance_unreadable"].get(k, 0) or 0):
            self.state["consecutive_balance_unreadable"][k] = 0
            self._save_state()
        return 0

    def beat_abort(self, reason: str = ""):
        self.state["consecutive_aborts"] = int(self.state.get("consecutive_aborts", 0)) + 1
        self._save_state()

    def note_skip(self, reason: str = ""):
        """Record a HEALTHY no-bet round (nothing cleared the gates)."""
        self.state["last_skip"] = {"ts": time.time(), "reason": str(reason)[:120]}
        self.state["skipped_rounds"] = int(self.state.get("skipped_rounds") or 0) + 1
        self._save_state()

    def clear_aborts(self, note: str = "risk refusal"):
        """Reset the abort streak after a DELIBERATE risk refusal.

        The portfolio gates (drawdown halt, correlation cap, Kelly, recipe veto)
        return "aborted" without touching the browser, because the engine chose
        not to bet. That is a healthy decision, not a broken session. Letting it
        increment this counter made the supervisor tear down and rebuild drivers
        on a timer, which caused real selenium instability, which caused genuine
        aborts — a self-feeding loop that buried the real state in warnings.
        """
        if int(self.state.get("consecutive_aborts") or 0) or note:
            self.state["consecutive_aborts"] = 0
            self.state["last_risk_refusal"] = {"ts": time.time(), "note": str(note)[:120]}
            self._save_state()

    def note_risk_refusal(self, reason: str = ""):
        """Record a portfolio/risk refusal for the digest, separately from aborts."""
        self.state.setdefault("risk_refusals", []).append(
            {"ts": time.time(), "reason": str(reason)[:120]})
        # keep it bounded — this is diagnostic, not an audit log
        if len(self.state["risk_refusals"]) > 200:
            del self.state["risk_refusals"][:-200]
        self._save_state()

    def beat_driver_heal(self):
        self.state.setdefault("driver_heals_last_hour", []).append(time.time())
        self._prune_driver_heals()
        self._save_state()

    def beat_parked(self, phone: str):
        k = str(phone or "")
        self.state.setdefault("parked_since", {}).setdefault(k, time.time())
        self._save_state()

    def beat_unparked(self, phone: str):
        self.state.get("parked_since", {}).pop(str(phone or ""), None)
        self._save_state()

    def beat_agent(self, name: str):
        self.state.setdefault("agent_heartbeats", {})[str(name)] = time.time()
        self._save_state()

    def _prune_driver_heals(self):
        cutoff = time.time() - 3600.0
        arr = [t for t in self.state.get("driver_heals_last_hour", []) if t > cutoff]
        self.state["driver_heals_last_hour"] = arr

    # -- the actual watchdog check, run periodically ---------------------
    def check(self, engine_state: dict = None, ledger_summary: dict = None,
              accounts: list = None, gui_callback=None,
              agent_cache: "AgentCache" = None) -> dict:
        """Run one full health pass.  Returns:
        {healthy, warnings, recommendations, wakeups, summary}

        *agent_cache* is optional — if supplied Fibi audits pick quality.
        """
        now = time.time()
        warnings = []
        recommendations = []
        wakeups = []          # agents Fibi wants the engine to restart

        engine_state = engine_state or {}
        ledger_summary = ledger_summary or {}
        accounts = accounts or []

        last_round = float(self.state.get("last_round_ts") or 0.0)
        last_placed = float(self.state.get("last_placed_ts") or 0.0)
        consec_aborts = int(self.state.get("consecutive_aborts") or 0)
        driver_heals = len(self.state.get("driver_heals_last_hour", []))

        def _log(msg: str):
            if gui_callback is not None:
                try:
                    gui_callback(f"🌸 Fibi: {msg}")
                except Exception:
                    pass

        # 1) Engine stalled?
        if now - last_round > self.ENGINE_STALL_THRESHOLD_S and last_round > 0:
            mins = int((now - last_round) / 60)
            w = f"ENGINE STALL: no round completed in ~{mins} min"
            warnings.append(w)
            recommendations.append({
                "action": "restart_engine",
                "reason": w,
                "severity": "critical",
            })
        elif last_round == 0:
            warnings.append("Engine has not completed its first round yet")

        # 2) No bets placed for a long time?
        # Distinguish "correctly declining" from "actually stuck" (2026-09-27).
        # A long dry spell is only a problem if rounds stopped completing. When
        # the engine is still actively crawling and simply declining thin or
        # negative-edge rounds, that is the risk controls WORKING, and calling
        # it "stuck" sent operators chasing a fault that did not exist.
        _last_skip = float((self.state.get("last_skip") or {}).get("ts") or 0.0)
        _skipping_now = _last_skip > 0 and (now - _last_skip) < 3600.0
        if now - last_placed > self.NO_BET_THRESHOLD_S and last_placed > 0:
            hrs = round((now - last_placed) / 3600, 1)
            if _skipping_now:
                w = (f"No bet placed in ~{hrs}h — engine healthy, declining rounds "
                     f"(gates not met); not stuck")
                recommendations.append({
                    "action": "none",
                    "reason": w,
                    "severity": "info",
                })
            else:
                w = f"NO BETS in ~{hrs}h — machine may be stuck waiting / out of budget"
                recommendations.append({
                    "action": "investigate_no_bets",
                    "reason": w,
                    "severity": "warning",
                })

        # 3) Consecutive aborts?
        if consec_aborts >= 8:
            w = f"{consec_aborts} consecutive aborts — session/page may be broken"
            warnings.append(w)
            recommendations.append({
                "action": "rebuild_driver",
                "reason": w,
                "severity": "high",
            })
        elif consec_aborts >= 4:
            warnings.append(f"{consec_aborts} consecutive aborts — watching")

        # 4) Balance unreadable spree per account?
        for acct, n in (self.state.get("consecutive_balance_unreadable") or {}).items():
            if n >= self.BALANCE_UNREADABLE_THRESHOLD:
                w = f"Account {acct}: {n} consecutive balance unreadable rounds"
                warnings.append(w)
                recommendations.append({
                    "action": "force_relogin",
                    "phone": acct,
                    "reason": w,
                    "severity": "high",
                })

        # 5) Account parked too long?
        # Only judge accounts this machine actually trades. `parked_since` is
        # persistent state, so it still holds entries for accounts that were
        # configured months ago. Without this filter the supervisor warned
        # (and unparked) phones nobody owns, several times an hour, forever.
        _known = {str(a).strip() for a in (accounts or []) if str(a or "").strip()}
        for acct, parked_ts in list((self.state.get("parked_since") or {}).items()):
            if _known and str(acct).strip() not in _known:
                continue
            parked_s = now - float(parked_ts or now)
            if parked_s > self.ACCOUNT_PARK_THRESHOLD_S:
                mins = int(parked_s / 60)
                w = f"Account {acct} parked ~{mins} min — long time"
                warnings.append(w)
                recommendations.append({
                    "action": "unpark_account",
                    "phone": acct,
                    "reason": w,
                    "severity": "medium",
                })

        # 6) Driver heals spiking?
        if driver_heals > self.DRIVER_HEAL_CAP_PER_HOUR:
            w = f"{driver_heals} driver rebuilds in the last hour — selenium instability"
            warnings.append(w)
            recommendations.append({
                "action": "investigate_driver_instability",
                "reason": w,
                "severity": "medium",
            })

        # 7) Agent heartbeats — any agent gone silent?
        hb = self.state.get("agent_heartbeats") or {}
        AGENT_WINDOWS = [
            ("risk",        "Risk manager",        1800,       "wake_up_risk"),
            ("calibrator",  "Calibrator",          8 * 3600,   "wake_up_calibrator"),
            ("reporter",    "Reporter",            30 * 3600,  "wake_up_reporter"),
            ("bet_history", "Bet history agent",   900,        "wake_up_bet_history"),
            ("analyst",     "Research analyst",    3600,       "wake_up_analyst"),
            ("scout",       "Opportunity scout",   3600,       "wake_up_scout"),
            ("cleaner",     "Balance report cleaner", 7200,   "wake_up_cleaner"),
        ]
        for name, label, window, wakeup_action in AGENT_WINDOWS:
            t = float(hb.get(name) or 0.0)
            if t == 0:
                continue
            silent_s = now - t
            if silent_s > window:
                mins = int(silent_s / 60)
                w = f"{label} silent for ~{mins} min (expected every {window // 60} min)"
                warnings.append(w)
                recommendations.append({
                    "action": "investigate_agent_silence",
                    "agent": name,
                    "reason": w,
                    "severity": "medium",
                })
                wakeups.append({
                    "action": wakeup_action,
                    "agent": name,
                    "reason": w,
                })

        # 8) Pick quality audit disabled — delta output handles anomalies.

        # 9) Daily budget — warn if late in the day and far behind
        try:
            daily_placed = int(ledger_summary.get("placed_today") or 0)
            daily_budget = int(ledger_summary.get("daily_budget") or 0)
            hr = datetime.now().hour
            if hr >= 20 and daily_budget > 0 and daily_placed < daily_budget * 0.5:
                w = (f"Only {daily_placed}/{daily_budget} daily bets placed at {hr}:00 — "
                     "far behind schedule")
                warnings.append(w)
                recommendations.append({
                    "action": "accelerate_pacing",
                    "reason": w,
                    "severity": "medium",
                })
        except Exception:
            pass

        healthy = len([r for r in recommendations
                       if r.get("severity") in ("critical", "high")]) == 0

        # Merge wakeups into recommendations so the engine's worker can act on them
        for wu in wakeups:
            recommendations.append({**wu, "severity": "medium"})

        # Rolling log (last 30 warnings)
        log = self.state.setdefault("warnings_log", [])
        for w in warnings:
            log.append({"ts": now, "msg": w})
        self.state["warnings_log"] = log[-30:]

        # Rolling recommendations queue (engine pops & acks)
        if recommendations:
            self.state.setdefault("pending_recs", []).extend(recommendations)
            self.state["pending_recs"] = self.state["pending_recs"][-20:]

        self.state["warnings"] = warnings
        self.state["recommendations"] = recommendations

        summary = (
            "✅ All good" if healthy and not warnings else
            f"⚠️ {len(warnings)} warning(s), {len(wakeups)} agent wake-up(s)"
        )

        # ── Delta-based output: Fibi only speaks when something changed ──────
        # Compare current warning set to the last cycle's warning set.
        # Only emit to the log when:
        #   a) New warnings appeared that weren't there before
        #   b) Warnings that were active have cleared (good news)
        #   c) It has been ≥30 min since Fibi last said anything (heartbeat)
        prev_warnings = set(self.state.get("_prev_warnings") or [])
        curr_warnings = set(warnings)
        new_warnings   = curr_warnings - prev_warnings
        cleared        = prev_warnings - curr_warnings
        last_spoke     = float(self.state.get("_last_spoke_ts") or 0.0)
        heartbeat_due  = (now - last_spoke) >= 1800.0   # 30 min

        should_speak = bool(new_warnings or cleared or (heartbeat_due and gui_callback))

        if should_speak:
            if new_warnings:
                for w in sorted(new_warnings):
                    _log(f"⚠️ NEW: {w}")
            if cleared:
                for w in sorted(cleared):
                    _log(f"✅ RESOLVED: {w}")
            if not new_warnings and not cleared:
                # Heartbeat — brief status, no noise
                placed_today = int(ledger_summary.get("placed") or 0)
                net = float(ledger_summary.get("net_profit") or 0)
                _log(f"👁️ watching — {placed_today} bets | net KES {net:+,.2f} | {summary}")
            self.state["_last_spoke_ts"] = now

        self.state["_prev_warnings"] = list(curr_warnings)

        self._save_state()
        return {
            "healthy": healthy,
            "warnings": warnings,
            "recommendations": recommendations,
            "wakeups": wakeups,
            "summary": summary,
        }

    def pending(self) -> list:
        """Return pending recommendations (engine pops them when acted on)."""
        return list(self.state.get("pending_recs") or [])

    def ack(self, rec_index: int = None):
        """Ack (pop) a recommendation. If index is None, clear all pending."""
        arr = self.state.setdefault("pending_recs", [])
        if rec_index is None:
            arr.clear()
        else:
            try:
                arr.pop(int(rec_index))
            except (IndexError, ValueError):
                pass
        self._save_state()

    def status_line(self) -> str:
        """One short status line for the GUI."""
        now = time.time()
        last_round = float(self.state.get("last_round_ts") or 0.0)
        last_placed = float(self.state.get("last_placed_ts") or 0.0)
        consec = int(self.state.get("consecutive_aborts") or 0)
        pending = len(self.state.get("pending_recs") or [])
        mins_ago = lambda t: "never" if not t else f"{int((now-t)/60)}m ago"
        return (f"👁️ rounds: {mins_ago(last_round)} | placed: {mins_ago(last_placed)} | "
                f"consec aborts: {consec} | pending: {pending}")


# --------------------------------------------------------------------------
# Hub — the one handle the engine talks to
# --------------------------------------------------------------------------

class AgentHub:
    def __init__(self, governor=None, alert_cfg: dict = None,
                 cache: AgentCache = None,
                 balance_report_max_age_days: float = 1.0,
                 search_dir: str = None,
                 api_football_key: str = "",
                 api_football_keys: list = None):
        self.cache = cache or AgentCache()
        self.analyst = ResearchAnalyst(governor, self.cache)
        self.scout = OpportunityScout(governor, self.cache)
        self.risk = RiskManager()
        self.calibrator = Calibrator()
        self.reporter = Reporter(governor)
        self.notifier = Notifier(alert_cfg or {})
        self.fibi = Fibi(self.cache)
        # Keep the old attribute name as an alias so existing engine code
        # that calls self._agent_hub.supervisor.beat_*() still works.
        self.supervisor = self.fibi
        self.bet_history = BetHistoryAgent()
        self.session_health = SessionHealthAgent()
        self.bet_recovery = BetRecoveryAgent()
        # API-Football with multi-key rotation
        _af_keys = [k.strip() for k in (api_football_keys or []) if str(k or "").strip()]
        if not _af_keys and api_football_key:
            _af_keys = [api_football_key.strip()]
        self.api_football = APIFootballAgent(api_keys=_af_keys)
        if search_dir is None:
            search_dir = os.path.dirname(os.path.abspath(__file__))
        self.cleaner = BalanceReportCleaner(
            max_age_days=balance_report_max_age_days, search_dir=search_dir)

    # -- alerts -----------------------------------------------------------
    def alert(self, kind: str, text: str, gui_callback=None):
        if gui_callback is not None:
            try:
                gui_callback(f"📲 {text[:240]}")
            except Exception:
                pass
        if not self.notifier.send(kind, text):
            return
        try:
            with open(NOTIFY_LOG_PATH, "a", encoding="utf-8") as f:
                f.write(f"[{datetime.now().isoformat(timespec='seconds')}] "
                        f"[{kind}] {text}\n")
        except Exception:
            pass

    # -- research / scout -------------------------------------------------
    def research_batch(self, games: list, limit: int = 3, budget: float = 30.0,
                       gui_callback=None, already_form=lambda _h, _a: (None, None)):
        """Study up to `limit` still-open games (LLM budget-capped). Returns picks."""
        picks = {}
        t0 = time.time()
        done = 0
        for g in (games or []):
            if done >= limit or (time.time() - t0) > budget:
                break
            gid = str(g.get("id") or "")
            name = str(g.get("name") or "")
            if not gid or " vs " not in name or self.cache.fresh_pick(gid):
                continue
            home = name.split(" vs ")[0].strip()
            away = name.split(" vs ")[1].strip()
            hf, af = (None, None)
            try:
                hf, af = already_form(home, away)
            except Exception:
                pass
            pick = self.analyst.analyze(gid, g, hf, af)
            if pick.get("pick") in PICK_MARKETS:
                picks[gid] = pick
                done += 1
                if gui_callback is not None:
                    try:
                        gui_callback(f"🧠 Analyst: {name} → {pick['pick']} "
                                     f"(P≈{pick['prob']:.0%}) {pick.get('reason','')[:80]}")
                    except Exception:
                        pass
        return picks

    def scout_games(self, games: list, limit: int = 2, budget: float = 20.0,
                    gui_callback=None):
        """Scout the full market sheet of a couple of games for positive-EV legs."""
        t0 = time.time()
        scanned = 0
        for g in (games or []):
            if scanned >= limit or (time.time() - t0) > budget:
                break
            gid = str(g.get("id") or "")
            name = str(g.get("name") or "")
            if not gid or " vs " not in name:
                continue
            markets = (g.get("full_markets") if isinstance(g.get("full_markets"), list)
                       else None)
            if not markets:
                continue
            out = self.scout.analyze(gid, g, markets)
            scanned += 1
            if out and gui_callback is not None:
                try:
                    best = max(out, key=lambda s: s.get("ev") or 0)
                    gui_callback(f"🎯 Scout {name}: {best['label']} @ {best.get('odds')} "
                                 f"EV {best.get('ev'):+.0%} — {best.get('note','')[:60]}")
                except Exception:
                    pass

    # -- value weighting for the selector --------------------------------
    def value_k(self, gid: str, market: str) -> float:
        """Small deterministic EV boost (or cut) from the scout's last read."""
        try:
            ev = (self.cache.scout_map().get(str(gid)) or {}).get(market)
        except Exception:
            ev = None
        if ev is None:
            return 1.0
        return round(1.0 + max(-0.08, min(0.08, ev)), 4)

    def researched_ok(self, gid: str, ttl: float = 4200.0) -> bool:
        p = self.cache.fresh_pick(gid, ttl=ttl)
        return bool(p and p.get("pick") in PICK_MARKETS)

    # -- risk -------------------------------------------------------------
    def risk_scale(self, active_count, active_bankroll, bankroll, net_profit):
        result = self.risk.stake_scale(active_count, active_bankroll, bankroll, net_profit)
        try:
            self.fibi.beat_agent("risk")
        except Exception:
            pass
        return result

    # -- calibration ------------------------------------------------------
    def calibrate(self, rows: list) -> dict:
        try:
            return self.calibrator.score(rows)
        except Exception:
            return {}

    # -- daily report ------------------------------------------------------
    def maybe_daily_report(self, summary, journal, ttl_hours: float = 24.0,
                           gui_callback=None):
        now = time.time()
        if now - self.cache.last_daily_report() < ttl_hours * 3600:
            return None
        day = datetime.now().strftime("%Y-%m-%d")
        txt = self.reporter.day_summary(day, summary, journal)
        self.cache.set_last_daily_report(now)
        self.alert("report", f"📊 {txt}", gui_callback=gui_callback)
        return txt

    # -- bet history / results --------------------------------------------
    def sync_bet_results(self, bets: list, gui_callback=None) -> dict:
        """Run the BetHistoryAgent against the current in-memory ledger and
        beat Fibi so she knows the agent is alive. Returns the summary dict."""
        if not self.bet_history.should_run():
            return {}
        summary = self.bet_history.run(bets, gui_callback=gui_callback)
        try:
            self.fibi.beat_agent("bet_history")
        except Exception:
            pass
        return summary

    # -- balance report file cleanup --------------------------------------
    def clean_balance_reports(self, gui_callback=None) -> dict:
        """Run the BalanceReportCleaner and beat Fibi. Returns the cleanup stats."""
        if not self.cleaner.should_run():
            return {}
        result = self.cleaner.run(gui_callback=gui_callback)
        try:
            self.fibi.beat_agent("cleaner")
        except Exception:
            pass
        return result

    # -- session health ---------------------------------------------------
    def check_session_health(self, phones: list, gui_callback=None) -> list:
        """Run the SessionHealthAgent and return any re-login actions needed."""
        if not self.session_health.should_run():
            return []
        actions = self.session_health.check(phones, gui_callback=gui_callback)
        try:
            self.fibi.beat_agent("session_health")
        except Exception:
            pass
        return actions

    def record_login(self, phone: str):
        """Record that a successful login happened for this phone."""
        try:
            self.session_health.record_login(phone)
        except Exception:
            pass

    # -- bet recovery -----------------------------------------------------
    def run_bet_recovery(self, bets: list, gui_callback=None) -> list:
        """Run the BetRecoveryAgent and return recommendations."""
        if not self.bet_recovery.should_run():
            return []
        recs = self.bet_recovery.analyse(bets, gui_callback=gui_callback)
        try:
            self.fibi.beat_agent("bet_recovery")
        except Exception:
            pass
        return recs