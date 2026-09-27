"""Supabase cloud sync for the Sportsape engine.

Fire-and-forget mirror of every bet, shadow/planned slip, settled result, and
game observation to a Supabase Postgres project so history survives a local
temp-folder wipe and a new machine can inherit the full calibration dataset.

Design rules:
  * Non-blocking: a single background worker thread drains a queue; the engine
    NEVER waits on the network. If Supabase is down the sync just drops the
    message and retries the full-state push later.
  * Idempotent: every row carries a deterministic natural key so re-pushing the
    same data upserts instead of duplicating.
  * Safe: all requests use the SERVICE-ROLE key (bypasses RLS) and are capped
    with short timeouts. Secrets live in sportsape_secrets.json (git-ignored).
"""

from __future__ import annotations

import hashlib
import json
import os
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from queue import Empty, Queue

import requests

SECRETS_PATH = Path(__file__).with_name("sportsape_secrets.json")

# PostgREST upsert header values
_MERGE = {"Prefer": "resolution=merge-duplicates,return=minimal", "Content-Type": "application/json"}
_MINIMAL = {"Prefer": "return=minimal", "Content-Type": "application/json"}


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _stable_id(*parts) -> str:
    """Deterministic 32-char hex id so re-pushes upsert instead of duplicating."""
    h = hashlib.sha256("|".join(str(p) for p in parts).encode("utf-8")).hexdigest()
    return h


class SupabaseSync:
    """Thin, non-blocking mirror to Supabase PostgREST.

    Also keeps the Supabase project ALIVE: a heartbeat thread pings the REST API
    on a fixed interval so a free-tier project never pauses from inactivity, and
    exposes pull_* methods so any machine can read the full history back at any
    time (calibration restore / new-machine onboarding).
    """

    HEARTBEAT_INTERVAL = 240.0  # seconds — ping ~every 4 min (free tier pauses after ~7 days idle)

    def __init__(self, url: str, service_key: str):
        self.url = (url or "").rstrip("/")
        self.key = service_key
        self._headers = {
            "apikey": service_key,
            "Authorization": "Bearer " + service_key,
        }
        self._q: Queue = Queue()
        self._stop = threading.Event()
        self._t = threading.Thread(target=self._worker, name="supabase-sync", daemon=True)
        self._hb = threading.Thread(target=self._heartbeat, name="supabase-heartbeat", daemon=True)
        self._last_error_logged = 0.0
        self._last_heartbeat_ts = 0.0
        self.enabled = bool(self.url and self.key)
        if self.enabled:
            self._t.start()
            self._hb.start()

    # ── heartbeat: keep the project from sleeping ──────────────────────────
    def _heartbeat(self):
        while not self._stop.is_set():
            try:
                # Cheap authenticated read that also proves the connection is live.
                requests.get(
                    self.url + "/rest/v1/sportsape_stats?select=id&limit=1",
                    headers=self._headers,
                    timeout=10,
                )
                self._last_heartbeat_ts = time.time()
            except Exception:
                pass
            # Renew our single-writer lease (if we own one) so the board does
            # not look abandoned while this build keeps placing.
            try:
                if self.lease_holder and self.enabled:
                    self.claim_lease(self.lease_holder)
            except Exception:
                pass
            self._stop.wait(self.HEARTBEAT_INTERVAL)

    def last_heartbeat_ago(self) -> float:
        """Seconds since the last successful heartbeat (inf if never)."""
        if not self._last_heartbeat_ts:
            return float("inf")
        return time.time() - self._last_heartbeat_ts

    # ── pull: read the full history back from the cloud ────────────────────
    def _get_all(self, table: str, order: str = "placed_at") -> list:
        """Fetch every row of a table. Returns [] on any failure (never raises)."""
        if not self.enabled:
            return []
        try:
            r = requests.get(
                f"{self.url}/rest/v1/{table}?select=*&order={order}",
                headers=self._headers,
                timeout=20,
            )
            if r.status_code != 200:
                return []
            data = r.json()
            return data if isinstance(data, list) else []
        except Exception:
            return []

    def pull_bets(self) -> list:
        return self._get_all("sportsape_bets")

    def pull_games(self) -> list:
        return self._get_all("sportsape_games", order="kickoff")

    def pull_stats(self) -> dict:
        rows = self._get_all("sportsape_stats", order="updated_at")
        if not rows:
            return {}
        try:
            return json.loads(rows[0].get("payload") or "{}")
        except Exception:
            return {}

    def pull_results(self) -> list:
        return self._get_all("sportsape_results", order="settled_at")

    def restore_ledger(self) -> list:
        """Rebuild the local bet ledger from the cloud (bets + results merged into
        the same shape the engine's _bets list uses). Returns [] when empty."""
        bets = self.pull_bets()
        out = []
        for b in bets:
            try:
                out.append({
                    "id": b.get("id"),
                    "phone": b.get("phone") or "",
                    "placed_at": b.get("placed_at"),
                    "legs": int(b.get("legs") or 0),
                    "stake": float(b.get("stake") or 0),
                    "odds": float(b.get("odds") or 0),
                    "possible_win": float(b.get("possible_win") or 0),
                    "markets": json.loads(b.get("markets") or "[]"),
                    "probs": json.loads(b.get("probs") or "[]"),
                    "game_ids": json.loads(b.get("game_ids") or "[]"),
                    "status": b.get("status") or "active",
                    "settled_at": b.get("settled_at"),
                    "won_amount": b.get("won_amount"),
                    "recipe": json.loads(b.get("recipe") or "{}"),
                    "imported": True,
                })
            except Exception:
                continue
        return out


    # ── public API (call from the engine; all return immediately) ──────────
    def push_bets(self, bets: list):
        """Upsert the full placed+shadow ledger into `sportsape_bets`."""
        if not self.enabled:
            return
        rows = []
        for i, b in enumerate(bets or []):
            if not isinstance(b, dict):
                continue
            phone = str(b.get("phone") or "")
            placed = b.get("placed_at") or _now_iso()
            kind = "shadow" if str(b.get("status") or "").startswith("shadow") else "placed"
            rows.append({
                "id": _stable_id("bet", phone, placed, i),
                "phone": phone,
                "kind": kind,
                "placed_at": placed,
                "legs": int(b.get("legs") or 0),
                "stake": float(b.get("stake") or 0),
                "odds": float(b.get("odds") or 0),
                "possible_win": float(b.get("possible_win") or 0),
                "markets": json.dumps(b.get("markets") or []),
                "probs": json.dumps(b.get("probs") or []),
                "game_ids": json.dumps(b.get("game_ids") or []),
                "status": str(b.get("status") or "active"),
                "settled_at": b.get("settled_at"),
                "won_amount": b.get("won_amount"),
                "recipe": json.dumps(b.get("recipe") or {}),
            })
        if rows:
            self._q.put(("bets", rows))

    def push_games(self, games: list):
        """Upsert game observations (betted or not) into `sportsape_games`."""
        if not self.enabled:
            return
        rows = []
        for g in games or []:
            if not isinstance(g, dict):
                continue
            gid = str(g.get("id") or g.get("gid") or "")
            if not gid:
                continue
            rows.append({
                "id": _stable_id("game", gid),
                "game_id": gid,
                "name": str(g.get("name") or ""),
                "home": str(g.get("home") or ""),
                "away": str(g.get("away") or ""),
                "kickoff": g.get("kickoff") or g.get("start"),
                "first_odds": json.dumps(g.get("first") or g.get("first_odds") or {}),
                "last_odds": json.dumps(g.get("last") or g.get("last_odds") or {}),
                "betted": bool(g.get("betted")),
                "status": str(g.get("status") or "seen"),
                "result": json.dumps(g.get("result") or {}),
                "updated_at": _now_iso(),
            })
        if rows:
            self._q.put(("games", rows))

    def push_stats(self, stats: dict):
        """Upsert the calibration/stats mirror into `sportsape_stats`."""
        if not self.enabled or not isinstance(stats, dict):
            return
        rows = [{
            "id": _stable_id("stats"),
            "payload": json.dumps(stats, default=str),
            "updated_at": _now_iso(),
        }]
        self._q.put(("stats", rows))

    def push_results(self, results: list):
        """Upsert per-game settled results (betted or not) into `sportsape_results`.
        Each row: game_id, market, outcome, source, slip_status, settled_at."""
        if not self.enabled:
            return
        rows = []
        for r in results or []:
            if not isinstance(r, dict):
                continue
            gid = str(r.get("game_id") or "")
            if not gid:
                continue
            mk = str(r.get("market") or "")
            rows.append({
                "id": _stable_id("result", gid, mk, r.get("source") or "",
                                 r.get("settled_at") or ""),
                "game_id": gid,
                "market": mk,
                "outcome": str(r.get("outcome") or "unknown"),
                "source": str(r.get("source") or "bet"),
                "phone": str(r.get("phone") or ""),
                "slip_status": str(r.get("slip_status") or ""),
                "settled_at": r.get("settled_at"),
            })
        if rows:
            self._q.put(("results", rows))

    # ── internals ──────────────────────────────────────────────────────────
    def _worker(self):
        while not self._stop.is_set():
            try:
                kind, rows = self._q.get(timeout=2.0)
            except Empty:
                continue
            try:
                self._send(kind, rows)
            except Exception as e:
                now = time.time()
                if now - self._last_error_logged > 300:
                    self._last_error_logged = now
                    print(f"[supabase] sync dropped {kind} ({len(rows)} rows): {e}", flush=True)

    def _send(self, kind, rows):
        if kind == "bets":
            self._post("/rest/v1/sportsape_bets", rows)
        elif kind == "games":
            self._post("/rest/v1/sportsape_games", rows)
        elif kind == "stats":
            self._post("/rest/v1/sportsape_stats", rows)
        elif kind == "results":
            self._post("/rest/v1/sportsape_results", rows)

    def _post(self, path, rows):
        # Chunk large batches to keep request bodies sane.
        for i in range(0, len(rows), 200):
            chunk = rows[i:i + 200]
            requests.post(
                self.url + path,
                headers={**self._headers, **_MERGE},
                data=json.dumps(chunk, default=str),
                timeout=15,
            )

    def stop(self):
        self._stop.set()
        self._hb.join(timeout=2)
        self._t.join(timeout=2)


    # ── single-writer lease (owned board) ────────────────────────────────────
    # Only ONE running instance may own the same 4 phones / board at a time.
    # The lease row lives in `sportsape_stats` (id = "lease") and is renewed by
    # the existing heartbeat thread; any second instance sees the live owner and
    # refuses to bet (surfaced in the GUI as "board held by <other build>").
    LEASE_ID  = "lease"
    LEASE_TTL = 150.0          # seconds; heartbeat renews well inside this

    def claim_lease(self, holder: str) -> bool:
        """Try to take the board for this build. Returns True if we are (or
        already are) the current leader — False if another live holder is."""
        if not self.enabled:
            return True
        try:
            resp = requests.get(
                f"{self.url}/rest/v1/sportsape_stats?id=eq.{_stable_id('stats')}",
                headers=self._headers, timeout=15)
            owner = None
            if resp.status_code == 200 and isinstance(resp.json(), list):
                for row in resp.json():
                    p = json.loads(row.get("payload") or "{}")
                    if p.get("lease") and p["lease"].get("holder"):
                        owner = p["lease"]["holder"]
            now = time.time()
            if owner and owner != holder:
                try:
                    exp = float(owner_ts.get("expires") or 0)
                except Exception:
                    exp = 0.0
                if exp > now:
                    return False   # another live build holds the board
            rows = [{
                "id": _stable_id("stats"),
                "payload": json.dumps({
                    **(self.get_last_payload() or {}),
                    "lease": {"holder": holder, "expires": now + self.LEASE_TTL},
                }, default=str),
                "updated_at": _now_iso(),
            }]
            self._post("/rest/v1/sportsape_stats", rows)
            return True
        except Exception:
            return True   # cloud unreachable → never block the owner's own bets

    def lease_owner(self) -> str:
        """Return the currently-holding build id ("" when none / no cls)."""
        if not self.enabled:
            return ""
        try:
            resp = requests.get(
                f"{self.url}/rest/v1/sportsape_stats?id=eq.{_stable_id('stats')}",
                headers=self._headers, timeout=15)
            if resp.status_code == 200 and isinstance(resp.json(), list):
                for row in resp.json():
                    p = json.loads(row.get("payload") or "{}")
                    if p.get("lease") and p["lease"].get("holder"):
                        return str(p["lease"]["holder"])
        except Exception:
            pass
        return ""


    def lease_holder(self) -> str:
        """Who currently holds the single-writer lease ("" when none / disabled).

        Lets the GUI show "board held by v4" the moment a second, newer build
        claims the same phones — the visible cowriter guard.
        """
        try:
            if not self.enabled:
                return ""
            rows = self.pull_stats() or {}
            return str(rows.get("lease_holder") or self._lease_holder or "")
        except Exception:
            return str(getattr(self, "_lease_holder", "") or "")


# ── singleton loader used by the backend ────────────────────────────────────
_sync = None
_sync_lock = threading.Lock()


def get_sync() -> "SupabaseSync | None":
    """Return the shared sync (or None when not configured / secrets missing)."""
    global _sync
    with _sync_lock:
        if _sync is not None:
            return _sync
        url, key = _load_secrets()
        _sync = SupabaseSync(url, key) if (url and key) else SupabaseSync("", "")
        return _sync


def _load_secrets():
    try:
        data = json.loads(SECRETS_PATH.read_text(encoding="utf-8"))
        return data.get("SUPABASE_URL") or "", data.get("SUPABASE_SECRET_KEY") or ""
    except Exception:
        return "", ""
