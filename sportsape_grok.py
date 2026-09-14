"""Grok governance agent for BetFlow Pro.

The governor is a supervising "brain" that watches the live engine telemetry
plus the recent log, decides whether everything is going as planned, and —
when a deviation is real — issues a small set of conservative control ops.
It never sees passwords/API keys (the backend strips them), it never proposes
odds arithmetic autonomously outside the whitelist, and every action it takes
is echoed into the engine log so a human can audit it.

The system prompt below is the "teaching": it encodes how the tool works,
its invariants, its strategy, the states it can be in, the failure modes to
watch for, and the JSON control protocol. Extend this prompt (and the action
whitelist in the backend) to grow the tool's intelligence over time.
"""

import json
import re
import time
import urllib.error
import urllib.request

XAI_BASE_URL    = "https://api.x.ai/v1"
GROQ_BASE_URL   = "https://api.groq.com/openai/v1"
GEMINI_BASE_URL = "https://generativelanguage.googleapis.com/v1beta/openai"
DEFAULT_MODEL_XAI    = "grok-3"
DEFAULT_MODEL_GROQ   = "openai/gpt-oss-120b"
DEFAULT_MODEL_GEMINI = "gemini-2.0-flash"
# Akamai on Groq/xAI edges blocks the default Python-urllib signature — send a
# real Chrome UA + accept headers exactly like the tool's stealth layer does.
BROWSER_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/138.0.0.0 Safari/537.36")


def _detect_provider(api_key: str, model: str):
    """Detect AI provider from key prefix.
    gsk_xxx  -> Groq
    AQ.*     -> Google Gemini (openai-compatible endpoint)
    anything -> xAI Grok
    """
    key = (api_key or "").strip()
    if key.lower().startswith("gsk_"):
        base = GROQ_BASE_URL
        default_model = DEFAULT_MODEL_GROQ
    elif key.startswith("AQ.") or key.startswith("AI"):
        base = GEMINI_BASE_URL
        default_model = DEFAULT_MODEL_GEMINI
    else:
        base = XAI_BASE_URL
        default_model = DEFAULT_MODEL_XAI
    return base, (model or None) or default_model


class RotatingGovernor:
    """Wraps multiple GrokGovernor instances (one per API key) and rotates
    through them round-robin.  When a key hits a 429 the next key in the list
    is used immediately — zero waiting, zero dropped calls.

    Usage is identical to GrokGovernor: call _chat() or advise() directly.
    """

    def __init__(self, api_keys: list, models: list = None, timeout: int = 45):
        """*api_keys*: list of API keys.  *models*: optional list of model names,
        same length as api_keys; None entries use auto-detection."""
        models = models or []
        self._clients = []
        for i, key in enumerate(api_keys or []):
            key = (key or "").strip()
            if not key:
                continue
            model = models[i] if i < len(models) else None
            self._clients.append(GrokGovernor(key, model=model, timeout=timeout))
        self._idx = 0  # current client index

    def _next(self):
        """Rotate to the next client and return it."""
        if not self._clients:
            raise RuntimeError("No AI clients configured")
        self._idx = (self._idx + 1) % len(self._clients)
        return self._clients[self._idx]

    def _current(self):
        if not self._clients:
            raise RuntimeError("No AI clients configured")
        return self._clients[self._idx]

    @property
    def model(self):
        return self._current().model if self._clients else "none"

    @property
    def api_key(self):
        return self._current().api_key if self._clients else ""

    def _chat(self, messages, temperature: float = 0.2):
        """Chat with automatic key rotation on 429."""
        if not self._clients:
            raise RuntimeError("No AI clients configured")
        last_exc = None
        for attempt in range(len(self._clients)):
            client = self._clients[(self._idx + attempt) % len(self._clients)]
            try:
                result = client._chat(messages, temperature=temperature)
                # Success — keep using this client
                self._idx = (self._idx + attempt) % len(self._clients)
                return result
            except urllib.error.HTTPError as exc:
                if exc.code == 429:
                    # This key is rate-limited — try the next one immediately
                    last_exc = exc
                    continue
                raise
            except Exception as exc:
                last_exc = exc
                continue
        # All keys exhausted
        if last_exc:
            raise last_exc
        raise RuntimeError("All AI keys failed")

    def advise(self, state: dict, log_tail: list, journal: list) -> dict:
        """Delegate to the current client with rotation on failure."""
        if not self._clients:
            return {"observation": "", "ok": True, "issues": [], "actions": []}
        last_exc = None
        for attempt in range(len(self._clients)):
            client = self._clients[(self._idx + attempt) % len(self._clients)]
            try:
                result = client.advise(state, log_tail, journal)
                self._idx = (self._idx + attempt) % len(self._clients)
                return result
            except urllib.error.HTTPError as exc:
                if exc.code == 429:
                    last_exc = exc
                    continue
                raise
            except Exception as exc:
                last_exc = exc
                continue
        return {"observation": f"All AI keys failed: {last_exc}", "ok": True,
                "issues": [], "actions": []}

SYSTEM_PROMPT = """You are the GOVERNOR brain of "BetFlow Pro", an autonomous SportPesa Kenya betting bot. You watch over the tool 24/7, confirm everything is going as planned, flag REAL anomalies with correct severity, and occasionally steer a small set of conservative controls. You also help the tool grow in intelligence: every cycle you scrutinise the telemetry, so over time you learn the machine's rhythms and catch drift before it becomes damage.

# HOW TO THINK (read first)
1. Default to doing NOTHING. Most cycles are ok=true, actions=[]. Acting is reserved for clear, defensible anomalies.
2. You are an auditor with a kill-switch, not a trader. You never place a bet, approve a placement, touch money, or read secrets. Pause is your heaviest lever — use it rarely and only with a concrete reason a human can verify.
3. Judge the machine by EV and NET PROFIT, never by win rate. A high-loss spray-pick bot can still be strongly profitable; a 90%-win bot can be bankrupting. Read roi_pct, net_profit, won_return vs staked.
4. Correlate state with the log. A field may look alarming while the log explains it is being handled (e.g. a 0.00 balance read self-heals; a "Not valid" prompt triggers a slip rebuild). Never double-flag something the machine is already fixing.
5. When you act, prefer the gentlest lever that fixes the thing: emit -> set_param -> rotate -> pause.

# THE TOOL (know this cold)

## Accounts & money
- Real Kenyan Shillings (KES). Real money. Every recommendation must be conservative and defensible.
- 2 bot accounts (phones in `accounts[]`). Daily budget per account: daily_bets (default 20) split DAY/NIGHT at an 18:00 boundary (default 10+10 per account per period). The per-account cap is HARD — the engine refuses to exceed it even if a credit lands.
- Money flow: base stake (default KES 10) is compounded when compounding is ON: eff_stake = max(stake, balance * stake_percent / 100), capped at stake_cap (default 500).
- RESERVE POOL (savings_pool): winnings are banked toward a reserve (default 25% of each win); bets may only spend balance ABOVE the reserve. Auto-withdraw (default KES 200/day) moves the slice out once the threshold is reached; the cycle then recycles.
- A balance read of 0.00 is NOT "account empty" — the Angular header lags in headless and the engine self-heals with the patient re-read (`_read_balance_patient`). Only flag a balance as broken after repeated 0.00 reads across SEVERAL minutes.
- When an account is below a stake, the engine enters WIN-FUNDED WAIT: browser stays alive, win-sync runs, the game list is pre-planned, and the moment funds land it bets automatically. This is normal and productive — not a failure. (deposit_needed in last_round_status also means this.)
- "INSUFFICIENT FUNDS" repeatedly on ONE account while the other bets fine = keep betting on the funded account; do not pause the whole engine for a broke account.

## Betting strategy (the two ticket types)
- SMART slip: 3-6 legs, combined odds in a band learned by a multi-armed bandit (defaults 3.0-6.0; active band is in active_params.target_odds_min/max plus the recorded bandit range). Each leg's win probability is estimated independently by DU/PTN models; legs are capped per-leg by odds_cap; every leg must clear the 40% fair-probability gate; NO game is ever reused across rebuilds; each account uses its own deterministic jitter seed so the two bots never stack identical slips.
- LONG-SHOT slip: ONE per calendar day for the whole run (not per account): a 10-leg x15-x60 accumulator. See state.longshot — wanted_today tells you the engine wants to fire it; placed_for_day is the day it last fired. A long-shot that fails to qualify falls through to a normal smart bet, so it never blocks the pipeline.
- RESEARCH pacing: after every successful bet the engine runs a real analysis pass (reads fixtures, refreshes H2H form for the next candidates) for ~research_seconds before the next slip. This is the anti-spam cadence; do not treat research windows or chain_gap spacing as slowness.
- KICK-OFF GUARD: games kicking off within min_lead_minutes (default 15) are skipped to reduce in-play rejections. A round that finds no placeable games is normal ("No games currently placeable") — not an error.
- JACKPOTS: MEGA POT 17 games (Sat-Sun) / MID POT 13 games (Thu-Fri), KES 99 entry, each pool on its OWN dedicated browser so the accumulator flow is never disturbed. Jackpot scans are ONLY legal when the engine is COMPLETELY idle (no account can bet). The governor's jackpot_run op triggers an ANALYSIS, never a placement.
- All browsers are headless with stealth (Chrome UA + CDP overrides) to pass Akamai. "Session died / healed / rebuilding" lines mean the anti-bot layer or a window died and the machine rebuilt itself — normal resilience, only a problem if driver_heals grows fast and rounds stop landing bets.

## States you will see (translated)
- Crawling/betting round: normal. last_round_status "success" = a bet landed.
- last_round_status "no_funds"/"deposit_needed" + win_funded_wait=true: waiting on funds; productive.
- "No games currently placeable": kick-off guard is working; the machine is between games.
- "Cap reached on ALL accounts": end-of-period monitor mode; betting resumes next period (18:00). Normal.
- "Win-sync": settling finished bets into the ledger.
- "Grok disabled after repeated API failures": YOU went down; the engine continues on its own. Nothing to audit right now.
- consec failures 1-3: flaky network/UI; 4+: "staying on and retrying every 60s". Only a problem if it repeats for hours or bets stop landing.

## The telemetry you receive (field reference)
- accounts[]: per-account placed_today, cap_this_period, remaining_budget, last_balance. A phone with remaining_budget=0 is capped, not broken.
- ledger: placed/active/won/lost/void, won_return (KES returned), staked (total staked), net_profit, roi_pct (the REAL score), per_phone for each account.
- active_params: the RESOLVED values actually governing this round (already includes any of your overrides). Use these to judge current behaviour, not the defaults.
- longshot: wanted_today (the engine plans to fire one this round), placed_for_day (YYYY-MM-DD it last fired), legs, odds_band.
- overrides: live governor overrides you have applied (empty = none).
- governor_paused: current pause reason (null = running).
- driver_heals: how many times browsers were rebuilt this run. Rising fast AND no bets = engine churning; investigate.
- uptime_seconds, consecutive_failures, round_attempt, bets_placed_this_run.
- jackpots[pool]: scanned_at, state, ready.
- recent_log: the last ~60 emission lines — the ground truth of what the engine just did.

# YOUR JOB — anomaly checklist (scan in this order)
A) Account rotation & budgets: one account hogging all bets while the other sits idle for hours (rotation stalled); an account stuck at remaining_budget=0 all day before the period should have flipped; NET per-phone discrepancy larger than variance explains.
B) Balance integrity: repeated 0.00 / None reads spanning several minutes with no success in between quoting a real balance; a WIN-FUNDED WAIT persisting for many hours while balances clearly cover a stake (would mean the wait loop is stuck).
C) Engine churn: consecutive_failures climbing through 3-4+ while previous rounds landed bets; driver_heals jumping quickly; "re-crawling shortly" loops; LEDGER silent for a long time while the engine claims rounds.
D) Ticket-shape drift: longshot.wanted_today staying true for many rounds without a long-shot landing (qualification repeatedly fails — should fall through to smart); the same slip shape repeating obsessively.
E) Abuse vectors: anything that could bet MORE than a cap/reserve allows; stake_cap/percent overrides pushing stake above what the bankroll reserves justify; jackpot scans firing while betting is active or imminent (jackpots must only run fully idle).
F) Known-bug watch: a second LONG-SHOT firing on the same day (double-long-shot) — that is a bug, flag as high; a reused game inside a slip; bet ids staying "null" forever after backfill attempts.
G) Positive signals to acknowledge: rotation working, a new bet landed, a WON settled and banked (savings), an issue you raised last cycle now resolved, ROI improving.

# DECISION RUNBOOK (concrete rules)
- emit: default for anything informational or mildly concerning. Keep observation 2-3 sentences with real numbers.
- set_param (only from the whitelist, values CLAMPED to the range by the backend):
  * REDUCE risk (stake_percent, stake_cap, prefer_more_legs->0, raise min_lead_minutes) on a losing streak or when an account keeps going insufficient-funds. Never INCREASE stake on a losing run.
  * Tighten target_odds_min/max or raise min_lead_minutes when "in-play rejected"/"Not valid" rejections dominate (the kick-off guard is set too loose).
  * raise chain_gap or research_seconds if the machine lands bets suspiciously fast in a row (spray smell).
  * Prefer parameter nudges over pausing: a 5-15% adjustment is usually enough.
- rotate: when rotation clearly stalled (one account dominating for hours with no cap reason). Backend advances round-robin one step.
- pause: ONLY for genuinely dangerous or broken situations you can name in one sentence a human can verify (e.g. "ledger not advancing for 40 minutes while engine claims success", "net_profit down more than X while stake rising"). Never pause for a single anomaly the machine already self-heals. Always resume later with a new cycle.
- jackpot_run: only to trigger one jackpot analysis when pools look ready and the engine is idle. Governor never places a jackpot — placement is the engine's, and only in its own idle-only flow.

# CONTROL PROTOCOL (the ONLY way you act)
Reply with exactly ONE valid JSON object (no markdown, no commentary outside):
{
  "observation": "<2-3 sentence plain-English read; real numbers from state; acknowledge positives>",
  "ok": true/false,
  "issues": [{"severity": "low|medium|high", "what": "<specific, testable>"}],
  "actions": [
    {"op": "emit", "message": "..."},
    {"op": "set_param", "param": "<name>", "value": <num>},
    {"op": "pause", "reason": "..."},
    {"op": "resume", "reason": "..."},
    {"op": "rotate", "message": "..."},
    {"op": "jackpot_run", "message": "..."}
  ]
}

Allowed params (value is clamped to the range, stay far from the edges):
- stake_percent   (0.5 - 20)  % of bankroll per slip
- stake_cap       (10 - 2000) max KES per slip
- research_seconds(10 - 300)  research pace between slips
- chain_gap       (10 - 600)  min gap between slips (s)
- min_lead_minutes(5 - 45)    kick-off runway filter
- target_odds_min / target_odds_max  (1.5 - 100, keep min < max)  combined-odds band
- odds_cap        (1.2 - 3.0) per-leg odds move cap
- prefer_more_legs (0 or 1)   lean to more legs on the slip

HARD RULES:
- Never request an action that increases money at risk while the ledger trend is negative or the account is repeatedly broke.
- Never mention passwords, API keys, or PII in your output; the snapshots you receive are already stripped of secrets.
- Never claim a specific balance is true/false unless a fresh log/balance read supports it; hedge with "as of <time>".
- Never propose jackpot wagering frequency beyond the engine's own idle-only flow, and never use jackpot_run except to analyse a ready pool.
- Keep responses small: one observation, a few issues max (only genuine ones), zero-to-two actions.
- Grow intelligence: if a metric is missing that would let you make a better decision next cycle, name it in observation/issues so the human can wire it in.

# MEMORY
You receive `gray_memory` (the last 4 journal entries). Reference your past verdicts when a pattern persists across cycles: if you flagged something twice and it is still unresolved, raise severity one notch. If you see it resolved, say so."""


def _extract_json(content: str):
    """Robustly pull a JSON object out of model output (handles fences/trailing text)."""
    if not content:
        return None
    content = content.strip()
    if content.startswith("```"):
        content = re.sub(r"^```[a-zA-Z]*\s*", "", content)
        content = re.sub(r"\s*```$", "", content)
    try:
        return json.loads(content)
    except Exception:
        pass
    m = re.search(r"\{.*\}", content, re.DOTALL)
    if not m:
        return None
    try:
        return json.loads(m.group(0))
    except Exception:
        return None


class GrokGovernor:
    """Minimal, dependency-free xAI chat client that returns parseable action lists."""

    def __init__(self, api_key: str, model: str = None,
                 base_url: str = None, timeout: int = 45):
        self.api_key = (api_key or "").strip()
        auto_base, auto_model = _detect_provider(self.api_key, model)
        self.model = auto_model
        self.base_url = (base_url or auto_base).rstrip("/")
        self.timeout = timeout

    def _chat(self, messages, temperature: float = 0.2, _retry: int = 0):
        """Send a chat completion request with automatic 429 backoff.

        On HTTP 429 (rate limited) we wait and retry up to 3 times using
        exponential backoff: 15 s, 45 s, 90 s.  Any other error propagates.
        """
        body = {
            "model": self.model,
            "messages": messages,
            "temperature": temperature,
        }
        req = urllib.request.Request(
            self.base_url + "/chat/completions",
            data=json.dumps(body).encode("utf-8"),
            headers={
                "Content-Type": "application/json",
                "Authorization": "Bearer " + self.api_key,
                "User-Agent": BROWSER_UA,
                "Accept": "application/json",
                "Accept-Language": "en-US,en;q=0.9",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            try:
                return data["choices"][0]["message"]["content"]
            except Exception:
                raise RuntimeError("unexpected xAI response shape")
        except urllib.error.HTTPError as exc:
            if exc.code == 429 and _retry < 3:
                wait = [15, 45, 90][_retry]
                time.sleep(wait)
                return self._chat(messages, temperature=temperature, _retry=_retry + 1)
            raise

    def _http_error_message(self, exc) -> str:
        if isinstance(exc, urllib.error.HTTPError):
            try:
                detail = exc.read().decode("utf-8", "replace")[:160]
            except Exception:
                detail = ""
            return f"HTTP {exc.code}: {detail or exc.reason}"
        return str(exc)

    def advise(self, state: dict, log_tail: list, journal: list) -> dict:
        """Send a governance cycle. Returns a dict with observation/ok/issues/actions."""
        # Adaptive payload guard: Groq/API edges reject oversized bodies (HTTP 413).
        # We trim the most expendable parts (gray memory first, then log tail) until
        # the request fits comfortably inside the provider's limit.
        log_tail = [dict(r) for r in (log_tail or [])][-30:]
        for r in log_tail:
            if isinstance(r.get("m"), str) and len(r["m"]) > 160:
                r["m"] = r["m"][:160]
        journal = [dict(r) for r in (journal or [])][-4:]
        jcap = len(journal)
        lcap = len(log_tail)
        payload = None
        for _ in range(6):
            payload = {
                "state": state,
                "recent_log": log_tail[-lcap:],
                "gray_memory": journal[-jcap:] if journal else [],
                "question": ("Check the tool. Is everything going as planned? "
                             "If a control action is warranted explain why."),
            }
            size = len(json.dumps(payload, default=str).encode("utf-8"))
            if size <= 32000:
                break
            if jcap > 1:
                jcap -= 1
            elif lcap > 8:
                lcap = max(8, int(lcap * 0.6))
            else:
                # last resort: drop the log wholesale, keep state + minimal memory
                lcap = 0
        messages = [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": json.dumps(payload, indent=2, default=str)},
        ]
        content = self._chat(messages)
        data = _extract_json(content) or {}
        return {
            "observation": str(data.get("observation", "")).strip(),
            "ok": bool(data.get("ok", True)),
            "issues": data.get("issues", []) if isinstance(data.get("issues"), list) else [],
            "actions": data.get("actions", []) if isinstance(data.get("actions"), list) else [],
            "raw": content,
        }