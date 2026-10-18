#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Forebet predictions -> a local cache the bet flow can read in zero time.

WHY THIS IS A SEPARATE OFF-FILE JOB
-----------------------------------
The one thing that finally made this bot work is that a round finishes in under
three minutes. The site's SPA tears down any in-flight request about seven
minutes after login, so there is a hard budget and spending it on HTTP fetches
to a third-party site would be reckless. This script therefore runs on its own
schedule (cron / Task Scheduler) and writes a plain JSON file. betflow.py reads
that file with a local read - microseconds - and if the file is stale or
missing it simply carries on unchanged.

HOW TO USE THE NUMBERS
-----------------------
Not as tips. As an independent opinion to compare against the book:

  * the board already gives us the book's implied probability
    (1 / decimal odds, minus the margin)
  * Forebet gives a model probability for the same outcome
  * where the two DISAGREE is the only place value can exist

If Forebet agrees with the book, there is nothing to do. If Forebet says 60%
and the book prices it at 45%, that is the bet.

That is most likely to be useful on the smaller leagues, where SportPesa's
prices are least sharp - which is exactly where a free model has the best
chance of being better than the market, and worst overall liquidity.

Output: forebet_cache.json
    {"fetched_at": epoch, "source": "forebet",
     "games": {"<home>|<away>": {"home":0.42,"draw":0.28,"away":0.30,
                                 "avg_goals":2.6, "n": 143}}}
"""
from __future__ import annotations

import json
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Mirrors betflow._live_dir(): when the app state lives on the Desktop (the
# shipped machine) write there too, so betflow.py's CACHE finds the file.
def _live_dir() -> Path:
    desk = Path.home() / "Desktop"
    if (desk / "sportsape_settings.json").exists():
        return desk
    return HERE

OUT = _live_dir() / "forebet_cache.json"
# Predictions are only worth reading for a day or so.
MAX_AGE_HOURS = 30

# Forebet reworked its URLs in 2026: /ke/ and /int/kenya now 404, and the
# site is Cloudflare-walled for plain HTTP (403). Predictions are dated
# global pages - /en/football-predictions/predictions-1x2/YYYY-MM-DD - only
# servable through a real browser session. This job tries the direct fetch
# first (cheap); get a browser fetch in front of it (or run it inside the
# engine's stealth Chrome) before expecting data. Every failure degrades to
# 'carry on unchanged'.
def _today_url() -> str:
    from datetime import date
    return ("https://www.forebet.com/en/football-predictions"
            f"/predictions-1x2/{date.today().isoformat()}")

FOREBET_COUNTRY_PAGES = {
    "1x2_today": _today_url(),
}

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")


def log(msg: str) -> None:
    print(f"[{datetime.now():%H:%M:%S}] forebet: {msg}", flush=True)


def fetch(url: str, timeout: int = 25) -> str:
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": "text/html,application/xhtml+xml",
        "Accept-Language": "en-GB,en;q=0.9",
    })
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8", "replace")


# Forebet's tables carry the fixture and three percentages. Rows look like:
#   ... <a href="/ke/...">Team A</a> ... Team B ... 42% 28% 30% ...
ROW = re.compile(
    r"<tr[^>]*>(?:(?!</tr>).)*?"
    r"(\d{1,2})\s*%[^<]*</td>.*?"
    r"(\d{1,2})\s*%[^<]*</td>.*?"
    r"(\d{1,2})\s*%",
    re.I | re.S)
TEAM = re.compile(r'title="([^"]{2,40})"|<td[^>]*>([A-Z][A-Za-z0-9 .\'\-]{2,30})</td>')


# Forebet redesigned (page seen 2026-10-10): the old <tr> tables are gone.
# Each fixture is now a schema.org SportsEvent block:
#   <span itemprop="homeTeam" ...><span itemprop="name">Team A</span></span>
#   <span itemprop="awayTeam" ...><span itemprop="name">Team B</span></span>
#   <div class="fprc"><span class="fpr">48</span><span>27</span><span>25</span></div>
#   <div class="avg_sc tabonly">2.51</div>
# The three fprc spans are home/draw/away percentages.
EVENT_BLOCK = re.compile(
    r'itemtype="http://schema\.org/SportsEvent"(.*?)'
    r'(?=itemtype="http://schema\.org/SportsEvent"|$)',
    re.I | re.S)
TEAM_NAME = re.compile(r'itemprop="name"[^>]*>\s*([^<>]{2,45})\s*<', re.I)
FPRC = re.compile(r'<div class="fprc">(.*?)</div>', re.I | re.S)
PCT_SPAN = re.compile(r'<span[^>]*>\s*(\d{1,2})\s*</span>', re.I)
AVG_GOALS = re.compile(r'<div class="avg_sc[^"]*"[^>]*>\s*([\d.]+)\s*<', re.I)


def parse(html: str) -> dict:
    """Best-effort extraction. If the page changes shape we return {} rather
    than writing rubbish - a stale cache is better than a wrong one."""
    games = _parse_schema(html)
    if games:
        return games
    return _parse_legacy_tables(html)


def _parse_schema(html: str) -> dict:
    """New (2026-10) forebet markup: schema.org SportsEvent blocks."""
    games: dict = {}
    for block in EVENT_BLOCK.findall(html or ""):
        names = TEAM_NAME.findall(block)
        if len(names) < 2:
            continue
        m = FPRC.search(block)
        if not m:
            continue
        pcts = PCT_SPAN.findall(m.group(1))
        if len(pcts) < 3:
            continue
        try:
            home, draw, away = (int(pcts[0]), int(pcts[1]), int(pcts[2]))
        except ValueError:
            continue
        if home + draw + away not in (99, 100, 101):
            continue
        if max(home, draw, away) < 15:          # implausible
            continue
        h, a = names[0].strip(), names[1].strip()
        goals = None
        mg = AVG_GOALS.search(block)
        if mg:
            try:
                goals = float(mg.group(1))
            except ValueError:
                goals = None
        games[f"{h}|{a}"] = {"home": home / 100.0, "draw": draw / 100.0,
                             "away": away / 100.0, "avg_goals": goals}
    return games


def _parse_legacy_tables(html: str) -> dict:
    """Old forebet markup: <tr> rows with three percentages."""
    games: dict = {}
    for tr in re.findall(r"<tr[^>]*>(.*?)</tr>", html, re.I | re.S):
        pcts = re.findall(r"(\d{1,2})\s*%", tr)
        if len(pcts) < 3:
            continue
        home, draw, away = (int(pcts[0]), int(pcts[1]), int(pcts[2]))
        if not (home + draw + away == 100):
            continue
        if max(home, draw, away) < 15:          # implausible
            continue
        names = re.findall(r'title="([^"]{2,40})"', tr)
        if len(names) < 2:
            cells = re.findall(
                r"<td[^>]*>\s*([A-Za-z][A-Za-z0-9 .'\-]{2,30})\s*</td>", tr)
            names = [c for c in cells if not c.isdigit()][:2]
        if len(names) < 2:
            continue
        h, a = names[0].strip(), names[1].strip()
        goals = None
        mg = re.search(r"(\d\.\d)\s*average goals", tr, re.I)
        if mg:
            try:
                goals = float(mg.group(1))
            except ValueError:
                goals = None
        games[f"{h}|{a}"] = {"home": home / 100.0, "draw": draw / 100.0,
                             "away": away / 100.0, "avg_goals": goals}
    return games
    return games


def main() -> int:
    log("fetching")
    merged: dict = {}
    for name, url in FOREBET_COUNTRY_PAGES.items():
        try:
            html = fetch(url)
        except Exception as exc:
            log(f"{name}: fetch failed - {str(exc)[:90]}")
            continue
        found = parse(html)
        log(f"{name}: {len(found)} fixture(s) parsed")
        merged.update(found)

    if not merged:
        log("nothing parsed - leaving any existing cache untouched")
        return 1

    payload = {"fetched_at": time.time(),
               "fetched_at_iso": datetime.now().isoformat(timespec="seconds"),
               "source": "forebet",
               "games": merged}
    OUT.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    log(f"wrote {len(merged)} fixtures -> {OUT.name}")

    # Sanity: show a couple so a broken parse is obvious at a glance.
    for k in list(merged)[:3]:
        v = merged[k]
        log(f"  e.g. {k}: H {v['home']:.0%} D {v['draw']:.0%} A {v['away']:.0%}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())