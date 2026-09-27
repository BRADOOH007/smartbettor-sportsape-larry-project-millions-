"""JEV leg validator for BetFlow Pro.

JEV (TypeSafe System One, https://jevapi.org/) is a fast typed-decision model:
you send a program state plus typed questions and get structured answers back
in 70-500ms.  This tool uses JEV as an independent second opinion on the
candidate legs the DU/PTN model ranked highest: for each leg we ask one `noul`
question ("will this selection win?") and blend JEV's probability with the
engine's own estimate before the slip is ranked.

Strictly optional and fail-open: no key, a timeout, or a malformed response all
just fall back to the engine's own probabilities — betting never waits on JEV.
"""

import json
import threading
import time
import urllib.error
import urllib.request

JEV_API_URL = "https://tokenra.io/v1/decisions"
JEV_MODEL = "jev-latest"
JEV_TIMEOUT = 6.0
DEFAULT_BLEND = 0.35          # weight given to JEV's probability when blending
_MAX_QUESTIONS = 14           # noul questions per call (speculative fan-out)
_MAX_CONSEC_FAIL = 3          # circuit breaker after this many failures
_COOLDOWN_SECONDS = 1800.0    # stay disabled this long after repeated failures


def _blend(model_prob: float, jev_prob: float, weight: float) -> float:
    w = max(0.0, min(0.9, float(weight or 0)))
    p = (1.0 - w) * float(model_prob) + w * float(jev_prob)
    return max(0.01, min(0.99, p))


class JevLegValidator:
    """Fail-open noul scorer for candidate legs. Never raises into the engine."""

    def __init__(self, api_key: str = "", weight: float = DEFAULT_BLEND,
                 timeout: float = JEV_TIMEOUT):
        self.api_key = (api_key or "").strip()
        self.weight = max(0.0, min(0.9, float(weight or DEFAULT_BLEND)))
        self.timeout = float(timeout or JEV_TIMEOUT)
        self._lock = threading.Lock()
        self._consec_fail = 0
        self._disabled_until = 0.0
        self.last_error = ""
        self.last_query_ts = 0.0

    def enabled(self) -> bool:
        return bool(self.api_key) and time.time() >= self._disabled_until

    def _post(self, state: str, questions: dict) -> dict:
        payload = {"model": JEV_MODEL, "state": state,
                   "questions": questions}
        req = urllib.request.Request(
            JEV_API_URL,
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "Authorization": "Bearer " + self.api_key,
                "Content-Type": "application/json",
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=self.timeout) as resp:
            return json.loads(resp.read().decode("utf-8") or "{}") or {}

    def reset_circuit(self):
        with self._lock:
            self._consec_fail = 0
            self._disabled_until = 0.0

    def _tap_fail(self):
        with self._lock:
            self._consec_fail += 1
            if self._consec_fail >= _MAX_CONSEC_FAIL:
                self._disabled_until = time.time() + _COOLDOWN_SECONDS
                self._consec_fail = 0

    @staticmethod
    def _question_for(name: str, market: str, odds: float, prob: float) -> dict:
        team = (name or "").strip()
        q_text = (
            f"Match: {team}. The selection is '{market}' priced at {odds:.2f} "
            f"with a margin-corrected model probability of {prob:.0%}. "
            "Estimate the TRUE probability this selection wins this exact match.")
        return {
            "type": "noul",
            "instructions": q_text,
            "criteria": {
                "true": "The selection wins the match",
                "false": "The selection does not win the match",
            },
        }

    def blend_legs(self, legs, name_map=None):
        """Blend JEV probability into each candidate leg.

        *legs*: list of (gid, market, odds, prob) tuples.  *name_map*: optional
        {gid: "HOME vs AWAY"} for the question text.

        Returns a dict {gid|market: blended_prob} for the legs JEV answered.
        Any failure returns {} — the caller keeps its own probabilities.
        """
        if not self.enabled():
            return {}
        legs = list(legs)[:_MAX_QUESTIONS]
        if not legs:
            return {}
        questions = {}
        for i, (gid, mk, o, p) in enumerate(legs):
            q = self._question_for((name_map or {}).get(gid, ""), mk, o, p)
            questions[f"leg_{i}"] = q
        state = (
            "You are validating accumulator legs for football betting. "
            "For every question give the honest probability the selection wins, "
            "based only on the odds and model probability shown. "
            "Probability 0 means it certainly loses, 1 means it certainly wins.")
        try:
            body = self._post(state, questions)
            answers = body.get("answers") or {}
            self.last_query_ts = time.time()
            with self._lock:
                self._consec_fail = 0
            out = {}
            for i, (gid, mk, o, p) in enumerate(legs):
                ans = answers.get(f"leg_{i}") or {}
                raw = ans.get("noul")
                try:
                    jp = float(raw)
                except (TypeError, ValueError):
                    continue
                if not (0.0 <= jp <= 1.0):
                    continue
                out[f"{gid}|{mk}"] = _blend(p, jp, self.weight)
            return out
        except urllib.error.HTTPError as exc:
            self.last_error = f"HTTP {exc.code}"
            if exc.code == 401:
                self._disabled_until = time.time() + _COOLDOWN_SECONDS
            self._tap_fail()
            return {}
        except Exception as exc:
            self.last_error = str(exc)[:120]
            self._tap_fail()
            return {}