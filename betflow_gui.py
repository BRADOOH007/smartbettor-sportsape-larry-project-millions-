#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
BetFlow - desktop GUI.

A thin window around the engine in betflow.py. It deliberately contains no
betting logic of its own: Start hands the work to a background thread that calls
the same do_round() the console build uses, and every line the engine prints is
mirrored into the log pane. That way there is exactly one implementation to trust.

What it does:
  * START / STOP the engine
  * live log, colour-coded by severity
  * balance per account, refreshed on demand
  * stake and daily-cap settings, written straight to the settings file
  * "keep this machine awake" toggle
  * shows the version and which build is running
"""
from __future__ import annotations

import os
import queue
import sys
import threading
import time
from datetime import datetime
from pathlib import Path
import tkinter as tk
from tkinter import ttk, messagebox

import betflow as engine

APP_TITLE = "BetFlow"
VERSION = "1.1.0"

# Icon assets live beside the app (or inside the bundle when frozen).
def _assets_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(getattr(sys, "_MEIPASS", "")) / "Assets"
    return Path(__file__).resolve().parent / "Assets"


def load_icon_image():
    """Return a PhotoImage or None, trying PNG first then ICO.

    The original app had a taskbar icon and losing it made this look like a
    different program, so it is restored here - window icon, taskbar icon and
    (via the PyInstaller spec) the exe icon itself.
    """
    for name in ("icon.png", "icon.ico", "balance_icon.png", "balance_icon.ico"):
        p = _assets_dir() / name
        if not p.exists():
            continue
        try:
            if p.suffix.lower() == ".png":
                return tk.PhotoImage(file=str(p))
            return tk.PhotoImage(file=str(p))
        except Exception:
            continue
    return None


# ── colour rules for the log ─────────────────────────────────────────────
def classify(line: str) -> str:
    u = line.upper()
    if any(k in u for k in ("NOT PLACED", "FAILED", "ERROR", "ABORT", "REFUSED")):
        return "bad"
    if any(k in u for k in ("BET PLACED", "LOGGED IN", "CLICKED 2/2", "WINNING")):
        return "good"
    if any(k in u for k in ("WARNING", "WARN", "COOLDOWN", "BELOW", "DISABLED",
                            "SKIPPED", "STANDING DOWN", "COULD NOT")):
        return "warn"
    if any(k in u for k in ("ROUND TOOK", "TOTALS", "PICKED", "BALANCE")):
        return "info"
    return ""


class BetFlowGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"{APP_TITLE} {VERSION}")
        self.geometry("1000x720")
        self.minsize(820, 560)
        self.configure(bg="#12161c")

        self.q: "queue.Queue[tuple[str, str]]" = queue.Queue()
        self.worker: threading.Thread | None = None
        self.stop_flag = threading.Event()
        self.keep_awake_on = True
        self.account_state: dict[str, str] = {}

        self._style()
        self._set_icon()
        self._build()
        self.after(120, self._drain)
        self.after(600, self._tick_status)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ── styling ──────────────────────────────────────────────────────────
    def _style(self):
        s = ttk.Style(self)
        try:
            s.theme_use("clam")
        except Exception:
            pass
        s.configure("TFrame", background="#12161c")
        s.configure("TLabel", background="#12161c", foreground="#d7dee8")
        s.configure("TLabelframe", background="#12161c", foreground="#8fa3bd")
        s.configure("TLabelframe.Label", background="#12161c", foreground="#8fa3bd")
        s.configure("TButton", padding=(10, 6))
        s.configure("Accent.TButton", background="#1f6feb", foreground="white")
        s.map("Accent.TButton",
              background=[("active", "#2b7cf3"), ("disabled", "#2a3440")])
        s.configure("Danger.TButton", background="#b23a48", foreground="white")
        s.map("Danger.TButton",
              background=[("active", "#c8485a"), ("disabled", "#2a3440")])
        s.configure("TEntry", fieldbackground="#0d1117", foreground="#d7dee8")
        s.configure("TCombobox", fieldbackground="#0d1117", foreground="#d7dee8")

    # ── window / taskbar icon ───────────────────────────────────────────
    def _set_icon(self):
        """Restore the app icon (window + taskbar).

        Iconbitmap() is what actually drives the TASKBAR entry on Windows;
        iconphoto alone only changes the client-area image. Try both, and fall
        back silently - a missing icon must never stop the app starting.
        """
        ico = _assets_dir() / "icon.ico"
        try:
            if ico.exists():
                self.iconbitmap(default=str(ico))
        except Exception:
            try:
                alt = _assets_dir() / "balance_icon.ico"
                if alt.exists():
                    self.iconbitmap(default=str(alt))
            except Exception:
                pass
        img = load_icon_image()
        if img is not None:
            try:
                self._icon_ref = img          # keep a reference or it vanishes
                self.iconphoto(True, True, img)
            except Exception:
                pass
        # Windows taskbar grouping hint.
        try:
            self.tk.call("tk", "scaling", 1.0)
        except Exception:
            pass

    # ── layout ───────────────────────────────────────────────────────────
    def _build(self):
        top = ttk.Frame(self, padding=(14, 12))
        top.pack(fill="x")

        ttk.Label(top, text=f"{APP_TITLE}",
                  font=("Segoe UI", 20, "bold"), foreground="#ffffff").pack(side="left")
        ttk.Label(top, text=f"v{VERSION}", foreground="#6b7c93").pack(side="left", padx=(8, 0))

        self.status_lbl = ttk.Label(top, text="idle", foreground="#8fa3bd")
        self.status_lbl.pack(side="right")

        # controls
        ctl = ttk.Frame(self, padding=(14, 0))
        ctl.pack(fill="x", pady=(6, 8))

        self.btn_start = ttk.Button(ctl, text="START", style="Accent.TButton",
                                    command=self._start)
        self.btn_start.pack(side="left")

        self.btn_stop = ttk.Button(ctl, text="STOP", style="Danger.TButton",
                                   command=self._stop, state="disabled")
        self.btn_stop.pack(side="left", padx=(8, 0))

        self.btn_balance = ttk.Button(ctl, text="Check balances", command=self._balances)
        self.btn_balance.pack(side="left", padx=(8, 0))

        self.keep_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(ctl, text="Keep machine awake", variable=self.keep_var,
                        command=self._toggle_awake).pack(side="left", padx=(16, 0))

        # settings row
        cfgf = ttk.LabelFrame(self, text="settings", padding=10)
        cfgf.pack(fill="x", padx=14)

        ttk.Label(cfgf, text="Stake (KES)").grid(row=0, column=0, sticky="w")
        self.stake_var = tk.StringVar(value="10")
        ttk.Entry(cfgf, textvariable=self.stake_var, width=10).grid(row=0, column=1, padx=(6, 18))

        ttk.Label(cfgf, text="Daily cap").grid(row=0, column=2, sticky="w")
        self.cap_var = tk.StringVar(value="20")
        ttk.Entry(cfgf, textvariable=self.cap_var, width=10).grid(row=0, column=3, padx=(6, 18))

        ttk.Button(cfgf, text="Save", command=self._save).grid(row=0, column=4)

        self.acct_lbl = ttk.Label(cfgf, text="", foreground="#8fa3bd")
        self.acct_lbl.grid(row=1, column=0, columnspan=5, sticky="w", pady=(8, 0))

        # log
        logf = ttk.LabelFrame(self, text="activity", padding=6)
        logf.pack(fill="both", expand=True, padx=14, pady=(10, 14))

        self.log = tk.Text(logf, wrap="word", bg="#0d1117", fg="#c9d1d9",
                           insertbackground="#c9d1d9", relief="flat",
                           font=("Consolas", 10), padx=10, pady=8)
        sb = ttk.Scrollbar(logf, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=sb.set)
        self.log.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        self.log.tag_configure("good", foreground="#3fb950")
        self.log.tag_configure("bad", foreground="#f85149")
        self.log.tag_configure("warn", foreground="#d29922")
        self.log.tag_configure("info", foreground="#58a6ff")
        self.log.tag_configure("dim", foreground="#6b7c93")

        self._load_settings()
        self._say("ready. press START to run a betting round.", "info")

    # ── settings ─────────────────────────────────────────────────────────
    def _load_settings(self):
        try:
            cfg = engine.load_settings()
            self.stake_var.set(str(cfg.get("stake", 10)))
            self.cap_var.set(str(cfg.get("daily_bets", 20)))
            phones = cfg.get("phones") or [cfg.get("phone")]
            self.acct_lbl.config(text="accounts: " + ", ".join(str(p) for p in phones))
            self.cfg = cfg
        except Exception as exc:
            self.acct_lbl.config(text=f"could not read settings: {exc}")
            self.cfg = {}

    def _save(self):
        try:
            cfg = engine.load_settings()
            cfg["stake"] = float(self.stake_var.get())
            cfg["daily_bets"] = int(self.cap_var.get())
            engine.SETTINGS.write_text(__import__("json").dumps(cfg, indent=2),
                                      encoding="utf-8")
            self._say(f"saved - stake KES {cfg['stake']:,.2f}, "
                      f"daily cap {cfg['daily_bets']}", "info")
            self._load_settings()
        except Exception as exc:
            messagebox.showerror("Could not save", str(exc))

    # ── logging ──────────────────────────────────────────────────────────
    def _say(self, msg: str, kind: str = ""):
        self.q.put((msg, kind))

    def _drain(self):
        try:
            while True:
                msg, kind = self.q.get_nowait()
                ts = datetime.now().strftime("%H:%M:%S")
                self.log.insert("end", f"[{ts}] {msg}\n", kind or ())
                self.log.see("end")
        except queue.Empty:
            pass
        self.after(120, self._drain)

    # ── engine control ───────────────────────────────────────────────────
    def _toggle_awake(self):
        if self.keep_var.get():
            engine.keep_awake()
        else:
            self._say("keep-awake released - the machine may sleep", "warn")

    def _start(self):
        if self.worker and self.worker.is_alive():
            return
        self.stop_flag.clear()
        self.btn_start.config(state="disabled")
        self.btn_stop.config(state="normal")
        self.status_lbl.config(text="running", foreground="#3fb950")
        self._say("---- START ----", "info")
        self.worker = threading.Thread(target=self._run, daemon=True)
        self.worker.start()

    def _stop(self):
        if self.worker and self.worker.is_alive():
            self.stop_flag.set()
            self._say("stop requested - finishing the current step", "warn")
            self.status_lbl.config(text="stopping", foreground="#d29922")

    def _run(self):
        """Mirror the engine's console output into the GUI, then run rounds."""
        import io
        import contextlib

        buf = io.StringIO()
        orig_log = engine.log

        def tee(msg):
            buf.write(str(msg) + "\n")
            buf.flush()
            self._say(str(msg), classify(str(msg)))

        engine.log = tee
        try:
            cfg = engine.load_settings()
            accounts = cfg.get("phones") or [cfg.get("phone")]
            stake = float(cfg.get("stake", 10))
            cap = int(cfg.get("daily_bets", 20))
            headless = bool(cfg.get("headless", True))

            driver = None
            try:
                driver, _prof = engine.build_driver(headless=headless)
                tee("browser ready")
                for phone in accounts:
                    if self.stop_flag.is_set():
                        break
                    if engine.bets_today(engine.load_ledger()) >= cap:
                        tee(f"daily cap of {cap} reached - stopping")
                        break
                    tee(f"--- {phone} ---")
                    try:
                        engine.do_round(driver, str(phone), cfg.get("password", ""), stake)
                    except Exception as exc:
                        tee(f"round failed: {type(exc).__name__}: {exc}")
            finally:
                if driver is not None:
                    try:
                        driver.quit()
                    except Exception:
                        pass
            tee("done", "info")
        except Exception as exc:
            tee(f"engine error: {type(exc).__name__}: {exc}", "bad")
        finally:
            engine.log = orig_log
            self.q.put(("---- FINISHED ----", "info"))

    def _balances(self):
        def work():
            driver = None
            try:
                cfg = engine.load_settings()
                accounts = cfg.get("phones") or [cfg.get("phone")]
                driver, _p = engine.build_driver(headless=True)
                for phone in accounts:
                    if engine.login(driver, str(phone), cfg.get("password", "")):
                        bal = engine.read_balance(driver)
                        self.q.put((f"{phone}: KES {bal:,.2f}" if bal is not None
                                    else f"{phone}: balance unreadable",
                                    "info" if bal else "warn"))
                    else:
                        self.q.put((f"{phone}: login failed", "bad"))
            except Exception as exc:
                self.q.put((f"balance check failed: {exc}", "bad"))
            finally:
                if driver is not None:
                    try:
                        driver.quit()
                    except Exception:
                        pass
                self.q.put(("", ""))
        threading.Thread(target=work, daemon=True).start()

    def _tick_status(self):
        if self.worker and self.worker.is_alive():
            if self.status_lbl.cget("foreground") not in ("#3fb950",):
                self.status_lbl.config(text="running", foreground="#3fb950")
        else:
            self.btn_start.config(state="normal")
            self.btn_stop.config(state="disabled")
            if self.status_lbl.cget("text") not in ("idle",):
                self.status_lbl.config(text="idle", foreground="#8fa3bd")
        self.after(900, self._tick_status)

    def _on_close(self):
        self.stop_flag.set()
        try:
            self.destroy()
        except Exception:
            pass


def main() -> int:
    # One instance only: two engines means two sessions on one account.
    guard = engine.SingleInstance("Global\\SportsApeBetFlowGuiSingleton")
    if not guard.acquired():
        messagebox.showwarning(
            APP_TITLE,
            "BetFlow is already running.\n\nOnly one instance may run - two engines "
            "would hold two sessions on the same account, which is what makes the "
            "bookmaker report 'logged in from another device'.")
        return 1
    app = BetFlowGUI()
    app.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())