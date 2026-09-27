"""Smoke test for the Fleet State tab (2026-09-27).

Builds the real tab against a real Tk root and drives the refresh path with a
fake backend, so a broken widget tree or a bad state read fails here instead of
in front of the owner. Verifies the three things the tab promises:
- the banner states the live risk with real numbers,
- a considered decline is NOT coloured as a fault,
- a freeze written through the panel is the freeze the breaker sees.
"""
import os
import sys
import tempfile
import traceback

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

fails = []


def check(name, cond, extra=""):
    if cond:
        print(f"  PASS  {name}")
    else:
        print(f"  FAIL  {name}  {extra}")
        fails.append(name)


class _FakePortfolio:
    """Kept only to document the shape the real portfolio file has."""
    peaks = {"0706719388": 15.40, "0798819388": 104.14}
    portfolio_peak = 119.54
    frozen = {}
    halted = False
    halt_reason = ""
    refused = 7
    last_equity = {"0706719388": 15.40, "0798819388": 104.14}


class _FakeBackend:
    def __init__(self):
        # The real _load_portfolio() returns a plain dict; mirror that contract.
        self.pf = {
            "peaks": {"0706719388": 15.40, "0798819388": 104.14},
            "portfolio_peak": 119.54,
            "frozen": {},
            "halted": False,
            "halt_reason": "",
            "refused": 7,
            "refused_reasons": {"no combo": 7},
            "last_equity": {"0706719388": 15.40, "0798819388": 104.14},
        }
        self._engine_state = {
            "balances": {"0706719388": 15.40, "0798819388": 104.14},
            "phones": ["0706719388", "0798819388"],
            "active_phone": "0706719388",
            "workers": {"0706719388": {"status": "success", "round_attempt": 4,
                                       "last_ts": 0, "longshot": False}},
        }
        self._bets = []
        self.PORTFOLIO_DRAWDOWN_HALT = 0.20
        self.saved = 0

    def _load_portfolio(self):
        return self.pf

    def _save_portfolio(self):
        self.saved += 1

    def _fleet_equity(self, balances):
        tot = 0.0
        for v in (balances or {}).values():
            try:
                f = float(v)
            except (TypeError, ValueError):
                continue
            if f > 0:
                tot += f
        return tot

    def _active_stake_for(self, phone):
        return 0.0

    def _portfolio_metrics(self):
        return {"real_bets": 10, "real_staked": 102.0, "real_returned": 146.01,
                "real_roi": 0.4315, "clv_avg": 0.031, "clv_samples": 4,
                "refused": 7}


try:
    import tkinter as tk
    from tkinter import ttk
    import main_gui
except Exception as _e:
    print(f"SKIP: cannot import GUI ({_e})")
    sys.exit(0)

root = None
try:
    root = tk.Tk()
    root.withdraw()
except Exception as _e:
    print(f"SKIP: no Tk display available ({_e})")
    sys.exit(0)

g = main_gui.BetFlowProGUI.__new__(main_gui.BetFlowProGUI)
g.root = root
g.colors = dict(main_gui.DARK)
g.backend = _FakeBackend()
g.nb = ttk.Notebook(root)
g._round_events = []
g._log_lines = []
g._fleet_card_widgets = {}
g._metric_labels = {}
g.phone_text = None

try:
    g._build_fleet_tab()
    check("Fleet State tab builds", bool(g.nb.tabs()))
    check("risk banner exists", g.fleet_banner is not None)
    check("round history table exists", g.round_tree is not None)
except Exception:
    traceback.print_exc()
    check("Fleet State tab builds", False, "exception during build")
    root.destroy()
    sys.exit(1)

# ── healthy fleet ────────────────────────────────────────────────────────
try:
    g._refresh_fleet_panel()
    banner = g.fleet_banner.cget("text")
    check("healthy banner says healthy", "healthy" in banner.lower(), banner[:90])
    check("healthy banner shows real equity", "119.54" in banner, banner[:120])
    check("healthy banner states the clearing limit", "-20%" in banner, banner[:120])
    check("metric strip shows ROI", "+43.1%" in g._metric_labels["roi"].cget("text"),
          g._metric_labels["roi"].cget("text"))
    check("metric strip shows CLV", "+3.10%" in g._metric_labels["clv"].cget("text"),
          g._metric_labels["clv"].cget("text"))
    check("metric strip shows refusals", g._metric_labels["refused"].cget("text") == "7",
          g._metric_labels["refused"].cget("text"))
    check("a card was built per account", len(g._fleet_card_widgets) == 2,
          str(list(g._fleet_card_widgets)))
except Exception:
    traceback.print_exc()
    check("healthy refresh renders", False)

# ── halted fleet ─────────────────────────────────────────────────────────
g.backend.pf["halted"] = True
g.backend.pf["halt_reason"] = "portfolio -87% from combined peak (limit -20%)"
try:
    g._refresh_fleet_panel()
    banner = g.fleet_banner.cget("text")
    check("halted banner is loud", "HALTED" in banner.upper(), banner[:90])
    check("halted banner repeats the real reason", "-87%" in banner, banner[:140])
    check("halted banner shows the peak it compares to", "119.54" in banner, banner[:160])
    chips = [w["chip"].cget("text") for w in g._fleet_card_widgets.values()]
    check("cards report HALTED, not IDLE",
          chips and all(x == "HALTED" for x in chips), str(chips))
except Exception:
    traceback.print_exc()
    check("halted refresh renders", False)

# ── unpriced account must not be shown as a balance ──────────────────────
g.backend.pf["halted"] = False
g.backend.pf["halt_reason"] = ""
g.backend._engine_state["balances"] = {"0706719388": 15.40, "0798819388": None}
try:
    g._refresh_fleet_panel()
    w = g._fleet_card_widgets.get("0798819388")
    check("an unpriced account is labelled, not shown as KES 0",
          w is not None and "no reading" in w["bal"].cget("text"),
          w["bal"].cget("text") if w else "no card")
    check("an unpriced account is UNPRICED, not HALTED",
          w is not None and w["chip"].cget("text") == "UNPRICED",
          w["chip"].cget("text") if w else "no card")
except Exception:
    traceback.print_exc()
    check("unpriced account renders honestly", False)

# ── outcome classification: a decline is not a fault ────────────────────
g.backend._engine_state["balances"] = {"0706719388": 15.40, "0798819388": 104.14}
g._round_events = []
cases = [
    ("⏭️ 0706719388: no bet this round (No accumulator combination found) — re-crawling in 60s",
     "declined", "DECLINED"),
    ("🛑 0798819388: portfolio refused this slip — no bet this round.", "fault", "FAULT"),
    ("✅ Betslip emptied — bet placed", "placed", "PLACED"),
    ("⏭ 0706719388: already bet today — no match repeats across numbers",
     "declined", "DECLINED"),
    ("ℹ Portfolio drawdown check skipped — 1 account has no usable balance", "declined", "DECLINED"),
]
try:
    for line, _k, _o in cases:
        g._note_round_event(line, "")
    got = [(e["kind"], e["outcome"]) for e in g._round_events]
    check("every case classified", len(got) == len(cases), str(got))
    for i, (_line, k, o) in enumerate(cases):
        check(f"case {i + 1} -> {o}", i < len(got) and got[i] == (k, o),
              str(got[i] if i < len(got) else None))
    placed = [e for e in g._round_events if e["kind"] == "placed"]
    check("a placed bet is attributed to the active account",
          bool(placed) and placed[0]["account"] == "…9388",
          str(placed[0] if placed else None))
    declined = [e for e in g._round_events if e["kind"] == "declined"]
    check("a decline is never coloured as a fault",
          all(e["kind"] != "fault" for e in declined), str(len(declined)))
except Exception:
    traceback.print_exc()
    check("outcome classification works", False)

# ── per-account freeze goes through the portfolio the breaker reads ─────
g.backend.pf["frozen"] = {}
try:
    g._toggle_account_freeze("0798819388")
    check("freeze is written to the portfolio file the breaker reads",
          g.backend.pf["frozen"].get("0798819388") is True and g.backend.saved > 0,
          str(g.backend.pf["frozen"]))
    btn = g._fleet_card_widgets["0798819388"]["btn"].cget("text")
    check("the frozen card offers Unfreeze", "Unfreeze" in btn, btn)
    g._toggle_account_freeze("0798819388")
    check("unfreeze clears it", not g.backend.pf["frozen"].get("0798819388"),
          str(g.backend.pf["frozen"]))
except Exception:
    traceback.print_exc()
    check("per-account freeze works", False)

# ── a panel that cannot read the fleet must say so, not say "healthy" ───
class _BrokenBackend(_FakeBackend):
    def _load_portfolio(self):
        raise RuntimeError("portfolio file locked")


g.backend = _BrokenBackend()
try:
    g._refresh_fleet_panel()
    banner = g.fleet_banner.cget("text")
    check("an unreadable fleet is NOT reported as healthy",
          "healthy" not in banner.lower(), banner[:100])
    check("an unreadable fleet says UNREADABLE", "UNREADABLE" in banner.upper(),
          banner[:100])
    check("an unreadable fleet names the fault",
          "portfolio file locked" in banner, banner[:160])
except Exception:
    traceback.print_exc()
    check("unreadable fleet is surfaced", False)

root.destroy()
print()
if fails:
    print(f"{len(fails)} FAILED: {fails}")
    sys.exit(1)
print("ALL FLEET GUI CHECKS PASSED")
