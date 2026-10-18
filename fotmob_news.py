# -*- coding: utf-8 -*-
"""fotmob_news.py - FotMob RSS news/injury layer for BetFlow."""
from __future__ import annotations

import json
import re
import time
import urllib.request
from datetime import datetime
from pathlib import Path

RSS_URL = "https://www.fotmob.com/topnews/feed?format=rss"
TTL = 2.0 * 3600.0
MAX_ITEMS = 40

_NEWS_FLAGS = ("injur", "out ", "doubt", "miss ", "suspend", "banned", "rest",
               "rotation", "sidelined", "doubtful", "fitness", "illness",
               "red card", "ban", "return", "lineup", "line-up", "squad",
               "absent", "unavailable", "ruled out", "knock", "strain",
               "hamstring", "crisis")


def _live_dir() -> Path:
    desk = Path.home() / "Desktop"
    if (desk / "sportsape_settings.json").exists():
        return desk
    return Path(__file__).resolve().parent


LIVE = _live_dir()
OUT = LIVE / "fotmob_news_cache.json"
_CACHE = {"at": 0.0, "data": None}


def log(msg: str) -> None:
    line = "[{}] fotmob: {}".format(datetime.now().strftime("%H:%M:%S"), msg)
    print(line, flush=True)
    try:
        with open(LIVE / "gui_terminal.log", "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:
        pass


def _norm(name: str) -> str:
    s = re.sub(r"[^A-Za-z0-9 ]", " ", str(name or "").upper())
    return " ".join(s.split())


def _fetch_rss() -> list:
    try:
        req = urllib.request.Request(RSS_URL, headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                          "AppleWebKit/537.36 (KHTML, like Gecko) "
                          "Chrome/120.0.0.0 Safari/537.36",
            "Accept": "application/rss+xml, application/xml, text/xml, */*"})
        with urllib.request.urlopen(req, timeout=15) as resp:
            body = resp.read().decode("utf-8", "replace")
    except Exception as e:
        log("fetch failed: " + str(e)[:60])
        return []
    items = re.findall(r"<item>(.*?)</item>", body, re.S)
    out = []
    for it in items[:MAX_ITEMS]:
        t = re.search(r"<title>(.*?)</title>", it, re.S)
        d = re.search(r"<description>(.*?)</description>", it, re.S)
        title = t.group(1) if t else ""
        desc = d.group(1) if d else ""
        title = re.sub(r"<!\[CDATA\[(.*?)\]\]>", r"\1", title, flags=re.S)
        desc = re.sub(r"<!\[CDATA\[(.*?)\]\]>", r"\1", desc, flags=re.S)
        title = re.sub(r"<[^>]+>", "", title).strip()
        desc = re.sub(r"<[^>]+>", "", desc).strip()
        out.append((title, desc))
    return out


def _team_mentioned(text: str, team: str) -> bool:
    t = _norm(text)
    n = _norm(team)
    if not n or len(n) < 5:
        return False
    # Require the FULL normalised name as a substring. The earlier last-token
    # fallback produced false positives ("Atletico" matched previews about
    # other Atletico sides). Honest: a miss is better than a false block.
    return n in t


def _has_flag(text: str) -> bool:
    low = (text or "").lower()
    return any(f in low for f in _NEWS_FLAGS)


def refresh(wanted_pairs=None) -> dict:
    try:
        items = _fetch_rss()
    except Exception:
        items = []
    if not items:
        try:
            if OUT.exists():
                return json.loads(OUT.read_text(encoding="utf-8"))
        except Exception:
            return {}
        return {}

    result = {}
    if wanted_pairs:
        for wp in wanted_pairs:
            if isinstance(wp, dict):
                home = wp.get("home") or wp.get("home_team") or ""
                away = wp.get("away") or wp.get("away_team") or ""
            else:
                try:
                    home, away = wp[0], wp[1]
                except Exception:
                    continue
            flags = []
            h, a = _norm(home), _norm(away)
            for title, desc in items:
                text = title + " " + desc
                if not _has_flag(text):
                    continue
                # Require BOTH teams in the same item to avoid cross-match
                # false positives (a team appears in many previews).
                if not (_team_mentioned(text, home) and _team_mentioned(text, away)):
                    continue
                snippet = (desc[:160] if desc else title[:160])
                if snippet and snippet not in flags:
                    flags.append(snippet)
            result["{}|{}".format(h, a)] = flags[:5]
    else:
        result["__items__"] = len(items)

    try:
        OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2),
                       encoding="utf-8")
    except Exception:
        pass

    flagged = sum(1 for v in result.values() if v)
    log("refresh: {} item(s), {} pair(s) flagged".format(len(items), flagged))
    return result


def load_signals(ttl: float = TTL) -> dict:
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


def news_flags(home: str, away: str) -> list:
    data = load_signals()
    key = "{}|{}".format(_norm(home), _norm(away))
    return data.get(key) or []


def team_has_bad_news(team: str) -> bool:
    data = load_signals()
    n = _norm(team)
    for key, flags in data.items():
        if key.startswith("__"):
            continue
        try:
            h, a = key.split("|", 1)
        except ValueError:
            continue
        if n == h or n == a:
            if flags:
                return True
    return False


if __name__ == "__main__":
    res = refresh()
    print(json.dumps(res, indent=1, ensure_ascii=False)[:2000])