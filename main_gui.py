import queue
import re
import sys
import os
import csv
import json
import time
import threading
from datetime import datetime
import tkinter as tk
from tkinter import ttk, scrolledtext, filedialog, messagebox

import single_instance

if sys.stdout and hasattr(sys.stdout, "reconfigure"):
    try:
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass
if sys.stderr and hasattr(sys.stderr, "reconfigure"):
    try:
        sys.stderr.reconfigure(errors="replace")
    except Exception:
        pass

# ── Single-instance guard ─────────────────────────────────────────────
# EVERY entry point (start_gui.py, main.py, spa_auto_start.py and each
# PyInstaller build) imports this module, so the guard placed here runs in
# every process that boots the tool. Whichever process grabs the named mutex
# first continues; every later process immediately exits. Two instances of the
# tool can never coexist, regardless of which launcher or which EXE build.
if not single_instance.acquire():
    single_instance.notify_and_exit()

from sportsape_backend import SportsapeBackend
from resource_path import writable_path
import notify

if sys.platform == "win32":
    try:
        import ctypes
        _HAS_CTYPES = True
    except ImportError:
        _HAS_CTYPES = False
else:
    _HAS_CTYPES = False


def set_windows_app_id(app_id: str):
    if not _HAS_CTYPES:
        return
    try:
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(app_id)
    except Exception:
        pass


APP_VERSION = "6.2.0"

# ── Crash harness ─────────────────────────────────────────────────────
# The GUI used to silently VANISH with no error message. These hooks make
# sure ANY uncaught exception — main thread, worker thread, or a Tk
# callback — is dumped to gui_crash.log next to this file so the cause is
# never lost again.
CRASH_LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gui_crash.log")
# Every terminal line is also appended verbatim to this file so runs can be
# reviewed/inspected after the fact (same diagnostic intent as CRASH_LOG).
TERMINAL_TEE_LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gui_terminal.log")


def _log_failure(source, exc):
    try:
        import traceback as _tb
        with open(CRASH_LOG, "a", encoding="utf-8") as f:
            f.write("\n" + "=" * 60 + "\n")
            f.write(f"{source} at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write("".join(_tb.format_exception(
                type(exc), exc, getattr(exc, "__traceback__", None))))
    except Exception:
        pass


def _install_crash_harness(root):
    def _main_hook(tp, val, tb):
        try:
            _log_failure("MAIN-THREAD EXCEPTION", val)
        finally:
            orig = getattr(sys, "__excepthook_orig__", None) or sys.__excepthook__
            orig(tp, val, tb)

    sys.__excepthook_orig__ = sys.excepthook
    sys.excepthook = _main_hook

    def _thread_hook(args):
        try:
            import traceback as _tb
            name = getattr(getattr(args, "thread", None), "name", "?")
            _log_failure(f"THREAD CRASH ({name})", args.exc_value)
            with open(CRASH_LOG, "a", encoding="utf-8") as f:
                f.write("".join(_tb.format_exception(
                    args.exc_type, args.exc_value, args.exc_traceback)))
        except Exception:
            pass

    threading.excepthook = _thread_hook

    def _tk_hook(tp, val, tb):
        try:
            _log_failure("TK CALLBACK", val)
        except Exception:
            pass

    try:
        root.report_callback_exception = _tk_hook
    except Exception:
        pass

DARK = {
    "bg": "#111417",
    "panel": "#171c21",
    "fg": "#e6ecf2",
    "button_bg": "#2a3642",
    "button_fg": "#dfe7ee",
    "accent": "#ffb400",
    "accent_dark": "#d99a00",
    "muted": "#8995a3",
    "border": "#2b3640",
    "text_bg": "#13181d",
    "text_fg": "#e6ecf2",
    "terminal_bg": "#070a0d",
    "terminal_fg": "#66ffae",
    "ok": "#2ecc71",
    "warn": "#ffb400",
    "err": "#ff5252",
}
LIGHT = {
    "bg": "#f2f6f9",
    "panel": "#ffffff",
    "fg": "#12222e",
    "button_bg": "#00a8fa",
    "button_fg": "#ffffff",
    "accent": "#ffb200",
    "accent_dark": "#d49900",
    "muted": "#5f7a8c",
    "border": "#cfe0ea",
    "text_bg": "#ffffff",
    "text_fg": "#12222e",
    "terminal_bg": "#0a0f14",
    "terminal_fg": "#00ff9c",
    "ok": "#27ae60",
    "warn": "#e67e22",
    "err": "#c0392b",
}


class AppState:
    def __init__(self):
        self.running = False
        self.engine_state = "IDLE"
        self.balance = None
        self.ledger = {"placed": 0, "active": 0, "won": 0, "lost": 0, "void": 0,
                       "won_return": 0.0, "net_profit": 0.0}
        self.worker_busy = {"bet": False, "balance": False, "withdraw": False, "markets": False, "deposit": False, "jackpot": False, "sync": False, "history": False}


class EventBus:
    def __init__(self):
        self._q = queue.Queue()

    def emit(self, kind, payload=None):
        try:
            self._q.put((kind, payload), timeout=0.5)
        except Exception:
            pass

    def drain(self):
        events = []
        while True:
            try:
                events.append(self._q.get_nowait())
            except queue.Empty:
                break
        return events


class BetFlowProGUI:
    def __init__(self, root, splash_screen=None):
        self.root = root
        self.splash = splash_screen
        self.theme_name = os.environ.get("BETFLOW_THEME", "dark")
        self.colors = dict(DARK if self.theme_name == "dark" else LIGHT)
        set_windows_app_id(f"BetFlowPro.{APP_VERSION}")
        self.backend = None
        self._backend_ready = threading.Event()
        def _load_backend():
            try:
                self.backend = SportsapeBackend()
            except Exception:
                pass
            self._backend_ready.set()
        self._backend_thread = threading.Thread(target=_load_backend, daemon=True)
        self._backend_thread.start()
        self.state = AppState()
        self.bus = EventBus()
        self._stop_event = None
        self._workers = {}
        self._update_lock = threading.Lock()
        root.title(f"⚽ BetFlow Pro v{APP_VERSION} — SportPesa Auto-Bet Machine")
        root.configure(bg=self.colors["bg"])
        root.geometry(self._center_geometry(1080, 760))
        self._build_ui()
        self._load_settings()
        # Icon is deferred so the HWND exists and paint is not blocked
        try:
            root.after(20, self._set_app_icon)
        except Exception:
            self._set_app_icon()
        root.protocol("WM_DELETE_WINDOW", self._on_close)
        self._log_lines = []
        self._last_emit_key = None
        self._last_emit_time = 0
        self._pump()
        # Roll-over visibility: top-bar chip + param checkbox sync
        try:
            def _sync_roll_chip(*_a):
                try:
                    on = bool(self.roll_over_var.get())
                    if on:
                        self.roll_chip.config(text="⚡ ROLL-OVER 50/3", fg=self.colors["accent"])
                    else:
                        self.roll_chip.config(text="● NORMAL", fg=self.colors["muted"])
                    # keep the action-row toggle button in step with the variable
                    btn = getattr(self, "roll_btn", None)
                    if btn is not None:
                        btn.config(bg=self.colors["accent"] if on else self.colors["button_bg"],
                                   fg="#0a1420" if on else self.colors["button_fg"])
                except Exception:
                    pass
            self.roll_over_var.trace_add("write", _sync_roll_chip)
            _sync_roll_chip()
            # re-sync after settings load (after 300ms, settings already loaded in _load_settings)
            root.after(400, _sync_roll_chip)
        except Exception:
            pass
        # Defer heavy ledger I/O so the window paints instantly — fixes
        # "Not Responding" on double-click. Ledger loads ~50ms after paint.
        try:
            root.after(50, self._refresh_ledger)
        except Exception:
            self._refresh_ledger()
        # Auto-sync on startup: settle any bets that finished while the tool was
        # closed. Fires 3 s after launch so the UI has time to fully render first.
        # Only runs if phone + password are already saved in settings.
        root.after(3000, self._startup_sync)

    def _center_geometry(self, w, h):
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        return f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h)//2)}"

    def _startup_sync(self):
        """Auto-sync bet history 3 s after launch (silent, non-blocking).

        Settles any bets that finished while the tool was closed. Only runs if
        phone + password are already saved — otherwise it silently no-ops.
        """
        try:
            if not self._phone_list():
                return
            if not self.password_var.get().strip():
                return
            self.start_sync_winnings(auto=True)
        except Exception:
            pass

    def _set_app_icon(self):
        """Pin the custom .ico as the window AND taskbar icon on Windows.

        Windows creates the taskbar button only after the window handle is
        fully visible.  Calling iconbitmap() before that point has no effect
        on the taskbar — the default Tk feather wins.  The reliable fix is:
        1. Call wm_iconbitmap() right now (title-bar).
        2. Schedule a 200 ms after() to re-apply it once the window is mapped
           and the taskbar button exists.
        3. Use ctypes to explicitly refresh the taskbar via SendMessage so
           Windows drops its cached Tk feather and picks up the new icon.
        iconphoto() is never called on Windows because it unconditionally
        resets the taskbar group icon to the Tk feather.
        """
        base = os.path.dirname(os.path.abspath(__file__))
        ico = os.path.join(base, "Assets", "icon.ico")
        if not os.path.exists(ico):
            try:
                sys.path.insert(0, os.path.join(base, "Assets"))
                from make_icon import build_icon
                build_icon()
            except Exception:
                pass
        if not os.path.exists(ico):
            ico = os.path.join(base, "Assets", "balance_icon.ico")
        if not os.path.exists(ico):
            return

        # Store absolute path — Tkinter resolves relative paths from cwd,
        # which may differ if the app is launched from a shortcut.
        ico_abs = os.path.abspath(ico)

        def _apply_ico():
            try:
                self.root.wm_iconbitmap(ico_abs)
            except Exception:
                try:
                    self.root.iconbitmap(default=ico_abs)
                except Exception:
                    pass
            # Deterministic taskbar-button icon: the button's icon is driven by
            # WM_SETICON/class-icon on THIS window's HWND — broadcasts only nudge
            # the theme cache into redrawing, which is exactly why the feather
            # keeps winning intermittently.  Load the .ico as a real HICON and
            # push it straight to our own HWND (small=taskbar, big=alt-tab).
            if sys.platform == "win32":
                try:
                    import ctypes as _ct
                    from ctypes import wintypes

                    # winfo_id() -> HWND of the child widget; the window that
                    # actually OWNS the taskbar button is the root ancestor of that
                    # child (GA_ROOT = 2). GetParent() on the child returns the
                    # frame window, not the toplevel — that mismatch is exactly why
                    # the taskbar kept showing the stock Tk "feather" instead of the
                    # balance icon. We climb to GA_ROOT and then also pin an explicit
                    # AppUserModelID so Windows groups the button under this app and
                    # re-reads its icon from the EXE resource on relaunch.
                    try:
                        _child = self.root.winfo_id()
                        hwnd = ctypes.windll.user32.GetAncestor(_child, 2)  # GA_ROOT
                    except Exception:
                        try:
                            hwnd = self.root.winfo_id()
                        except Exception:
                            hwnd = None
                    if not hwnd:
                        hwnd = None
                    try:
                        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
                            "SportsApe.BetflowProAuto")
                    except Exception:
                        pass
                    if hwnd:
                        IMAGE_ICON = 1
                        LR_LOADFROMFILE = 0x0010
                        LR_DEFAULTSIZE = 0x0040
                        WM_SETICON = 0x0080
                        ICON_SMALL = 0
                        ICON_BIG = 1
                        try:
                            hsm = ctypes.windll.user32.LoadImageW(
                                None, ico_abs, IMAGE_ICON, 0, 0,
                                LR_LOADFROMFILE | LR_DEFAULTSIZE)
                            if hsm:
                                ctypes.windll.user32.SendMessageW(
                                    hwnd, WM_SETICON, ICON_SMALL, hsm)
                        except Exception:
                            pass
                        try:
                            hbg = ctypes.windll.user32.LoadImageW(
                                None, ico_abs, IMAGE_ICON, 0, 0,
                                LR_LOADFROMFILE | LR_DEFAULTSIZE)
                            if hbg:
                                ctypes.windll.user32.SendMessageW(
                                    hwnd, WM_SETICON, ICON_BIG, hbg)
                        except Exception:
                            pass
                except Exception:
                    pass
            # Tell Windows to refresh its shell icon cache for this window.
            # Without this, the taskbar can show a stale Tk feather even after
            # iconbitmap() has set the correct icon on the HWND.
            if sys.platform == "win32" and _HAS_CTYPES:
                try:
                    # Timeout-based refresh so this can never hang the launch: a
                    # plain synchronous SendMessage to HWND_BROADCAST blocks until
                    # EVERY top-level window responds, so one stuck window (e.g. an
                    # orphaned browser from a killed session) freezes the whole app.
                    WM_SETTINGCHANGE = 0x001A
                    HWND_BROADCAST = 0xFFFF
                    SMTO_ABORTIFHUNG = 0x0002
                    _res = ctypes.c_ulong()
                    ctypes.windll.user32.SendMessageTimeoutW(
                        HWND_BROADCAST, WM_SETTINGCHANGE, 0, "WindowMetrics",
                        SMTO_ABORTIFHUNG, 100, ctypes.byref(_res))
                except Exception:
                    pass

        # Apply immediately (title-bar icon)
        _apply_ico()
        # Apply again after the event loop has shown the window and the
        # taskbar button has been created (200 ms is safely past that point).
        try:
            self.root.after(200, _apply_ico)
        except Exception:
            pass

        if sys.platform != "win32":
            # On non-Windows, iconphoto() is the right approach
            for cand in (os.path.join(base, "Assets", "icon_preview.png"),
                         os.path.join(base, "Assets", "balance_icon.png"),
                         os.path.join(base, "sportpesa_football.png")):
                if os.path.exists(cand):
                    try:
                        img = tk.PhotoImage(master=self.root, file=cand)
                        self.root.iconphoto(True, img)
                        self._icon_img = img
                        break
                    except Exception:
                        continue
            _apply_ico()

    # ── thread-safe emit helpers ──────────────────────────────────────
    def _emit(self, message):
        if message and str(message).strip():
            self.bus.emit("log", str(message))

    def _worker(self, name, fn):
        def runner():
            self.state.worker_busy[name] = True
            self.bus.emit("busy", (name, True))
            try:
                fn()
            except Exception as e:
                self._emit(f"⚠️ {name} error: {e}")
            finally:
                self.state.worker_busy[name] = False
                self.bus.emit("busy", (name, False))
                self.bus.emit("workers_done", None)

        t = threading.Thread(target=runner, daemon=True)
        self._workers[name] = t
        t.start()

    def _pump(self):
        try:
            for kind, payload in self.bus.drain():
                try:
                    self._handle_event(kind, payload)
                except Exception as exc:
                    _log_failure(f"EVENT HANDLER ({kind})", exc)
            try:
                self._tick()
            except Exception as exc:
                _log_failure("TICK", exc)
        finally:
            try:
                self.root.after(120, self._pump)  # ~8fps — sufficient, saves CPU vs 60ms
            except Exception:
                pass

    def _handle_event(self, kind, payload):
        if kind == "log":
            self._append_log(str(payload))
            self._sniff_balance(str(payload))
            self._notify_from_log(str(payload))
            if "🏆" in str(payload) or "WON" in str(payload).upper():
                self._celebrate_win(str(payload))
        elif kind == "busy":
            name, busy = payload
            self._set_worker_button(name, busy)
        elif kind == "workers_done":
            self._refresh_ledger()
        elif kind == "status":
            self.state.engine_state = str(payload)
            self._update_status_chip()
        elif kind == "deposit":
            need, bal = payload
            self.state.balance = bal
            self._update_balance_label()
            self._append_log(f"🛑 Insufficient balance: KES {bal:,.2f} < stake. "
                             f"Deposit at least KES {need:,.2f}.")
            messagebox.showwarning("Insufficient Balance",
                                   f"Balance KES {bal:,.2f} is below the stake. "
                                   f"Deposit at least KES {need:,.2f}.")

    def _tick(self):
        if self.state.balance is not None:
            self._update_balance_label()
        else:
            # Refresh per-phone strip even if overall balance isn't set yet,
            # but only when the engine state actually changed — not every 60 ms.
            now = time.time()
            if now - getattr(self, "_last_per_phone_refresh", 0.0) > 3.0:
                self._last_per_phone_refresh = now
                self._update_per_phone_balances()
        now = time.time()
        if now - getattr(self, "_last_ready_refresh", 0.0) > 5.0:
            self._last_ready_refresh = now
            self._refresh_jackpot_ready()
            self._update_per_phone_balances()
        now = time.time()
        if now - getattr(self, "_last_phone_reconcile", 0.0) > 8.0:
            self._last_phone_reconcile = now
            self._reconcile_phone_list()
        if now - getattr(self, "_last_mem_watch", 0.0) > 60.0:
            self._last_mem_watch = now
            self._watch_memory()
        # The Fleet State tab is the operator's answer to "is my money safe and
        # what is each account doing". Refresh it on its own cadence so a halt or
        # a freeze is visible within a couple of seconds rather than only after
        # the operator reads the log.
        if now - getattr(self, "_last_fleet_refresh", 0.0) > 2.0:
            self._last_fleet_refresh = now
            self._refresh_fleet_panel_safe()

    def _process_mem_mb(self):
        """Current process RAM in MB (Windows). Returns 0 if unavailable."""
        if not _HAS_CTYPES:
            return 0
        try:
            import ctypes as _c

            class _PMC(_c.Structure):
                _fields_ = [("cb", _c.c_ulong),
                            ("PageFaultCount", _c.c_ulong),
                            ("PeakWorkingSetSize", _c.c_size_t),
                            ("WorkingSetSize", _c.c_size_t),
                            ("QuotaPeakPagedPoolUsage", _c.c_size_t),
                            ("QuotaPagedPoolUsage", _c.c_size_t),
                            ("QuotaPeakNonPagedPoolUsage", _c.c_size_t),
                            ("QuotaNonPagedPoolUsage", _c.c_size_t),
                            ("PagefileUsage", _c.c_size_t),
                            ("PeakPagefileUsage", _c.c_size_t),
                            ("PrivateUsage", _c.c_size_t)]

            hproc = _c.windll.kernel32.GetCurrentProcess()
            pmc = _PMC()
            ok = _c.windll.psapi.GetProcessMemoryInfo(
                hproc, _c.byref(pmc), _c.sizeof(pmc))
            if not ok:
                return 0
            return (pmc.WorkingSetSize or 0) / (1024.0 * 1024.0)
        except Exception:
            return 0

    def _watch_memory(self):
        """Memory creep is the classic cause of the window silently vanishing
        (each phone worker owns its own Chrome). Warn early and sweep orphan
        browsers so a freshly added number never tips the process over."""
        try:
            mb = self._process_mem_mb()
            if mb <= 0:
                return
            if mb >= 1600:
                self._append_log(
                    f"🛑 WARNING: app using ~{mb:.0f} MB. This is the danger zone "
                    f"where the window silently closes. Sweeping orphan browsers "
                    f"now and recommending a restart.")
                try:
                    self.backend._sweep_orphan_chromedrivers(gui_callback=self._emit,
                                                             aggressive=False)
                except Exception:
                    pass
            elif mb >= 1100:
                self._append_log(
                    f"⚠️ Memory high (~{mb:.0f} MB). Sweeping orphaned browsers "
                    f"to make room for new phone workers.")
                try:
                    self.backend._sweep_orphan_chromedrivers(gui_callback=self._emit,
                                                             aggressive=False)
                except Exception:
                    pass
        except Exception:
            pass

    def _reconcile_phone_list(self):
        """While the machine is running, diffs the phone box against the
        backend's active phone list. Newly typed numbers get a dedicated
        worker; removed numbers wind their worker down. Engine reads
        _engine_state['phones'] inside its own supervisor loop."""
        try:
            if not getattr(self.backend, "running", False):
                return
            if not self.state.worker_busy.get("bet"):
                return
            new_phones = [str(p) for p in self._phone_list() if str(p).strip()]
            if not new_phones:
                return
            es = getattr(self.backend, "_engine_state", None)
            if es is None:
                return
            old = [str(p) for p in (es.get("phones") or []) if str(p).strip()]
            added = [p for p in new_phones if p not in old]
            removed = [p for p in old if p not in new_phones]
            if not added and not removed:
                return
            es["phones"] = list(new_phones)
            for p in added:
                self._append_log(f"➕ {p} ADDED to the phone list — its worker will "
                                 f"start on the next round.")
                try:
                    notify.toast("Phone list update", f"➕ {p} added")
                except Exception:
                    pass
            for p in removed:
                self._append_log(f"➖ {p} REMOVED from the phone list — winding "
                                 f"down its worker now.")
                try:
                    notify.toast("Phone list update", f"➖ {p} removed")
                except Exception:
                    pass
        except Exception:
            _log_failure("PHONE RECONCILE", sys.exc_info()[1])

    def _refresh_jackpot_ready(self):
        """Live 'Mega / Midweek jackpot — picks ready' alert fed by the idle
        research. Each pool shows its own readiness (🟢 fresh / 🟠 stale)."""
        try:
            st = self.backend._load_jackpot_ready()
        except Exception:
            st = None
        if not st:
            self.ready_lbl.config(text="⚪ jackpot research idle", fg="#8a929e")
            return
        pools = {}
        try:
            pools = st.get("pools") or {}
        except Exception:
            pools = {}
        if not any(dict(p or {}).get("ready") for p in pools.values()):
            self.ready_lbl.config(text="⚪ jackpot research idle", fg="#8a929e")
            return
        parts = []
        worst_age = 0.0
        for pname, pst in pools.items():
            if not isinstance(pst, dict) or not pst.get("ready"):
                continue
            n = int(pst.get("picks") or 0)
            age_h = (time.time() - float(pst.get("ts") or 0)) / 3600.0
            worst_age = max(worst_age, age_h)
            if age_h <= 5:
                parts.append(f"🟢 {str(pname).upper()} {n} picks READY")
            else:
                parts.append(f"🟠 {str(pname).upper()} {n} picks stale")
        if not parts:
            self.ready_lbl.config(text="⚪ jackpot research idle", fg="#8a929e")
            return
        self.ready_lbl.config(text="  ".join(parts),
                              fg="#5fd06b" if worst_age <= 5 else "#d9a441")

    # Lines worth interrupting the operator for. Everything else — a considered
    # decline, a research note, a retry, a top-up — stays in the log and in the
    # round table, because a machine that declines 9 rounds out of 10 is working,
    # and a notification for each one trains the owner to ignore notifications.
    _NOTIFY_WORDS = (
        "BET PLACED", "PLACED ✅", "🏆", "WON", "🛑", "HALT", "FROZEN",
        "FATAL", "Traceback", "CRITICAL",
    )

    def _notify_from_log(self, text):
        if not getattr(self, "notify_var", None) or not self.notify_var.get():
            return
        try:
            t = str(text or "")
            if not any(w in t or w in t.upper() for w in self._NOTIFY_WORDS):
                return
            kind, title, msg = notify.classify(t) or (None, None, None)
            if kind:
                notify.sound(kind)
                notify.toast(title, msg)
        except Exception:
            pass

    def _celebrate_win(self, text):
        """Industrial-grade celebration: every win lights up the status chip and
        the balance label, then settles back after a few seconds."""
        try:
            prev = self.status_chip.cget("text")
            self.status_chip.config(text="🎉 WIN! 💰", fg="#ffd75e")
            self.balance_label.config(fg="#ffd75e")

            def _settle():
                try:
                    self.status_chip.config(text=prev, fg=self.colors["muted"])
                    self._update_balance_label()
                except Exception:
                    pass
            try:
                self.root.after(8000, _settle)
            except Exception:
                pass
        except Exception:
            pass

    # ── UI construction ──────────────────────────────────────────────
    def _build_ui(self):
        c = self.colors
        top = tk.Frame(self.root, bg=c["panel"], padx=10, pady=8)
        top.pack(fill="x")

        self.status_chip = tk.Label(top, text="● IDLE", fg=c["muted"], bg=c["panel"],
                                    font=("Consolas", 11, "bold"))
        self.status_chip.pack(side="left")

        self.roll_chip = tk.Label(top, text="● NORMAL", fg=c["muted"], bg=c["panel"],
                                  font=("Consolas", 10, "bold"))
        self.roll_chip.pack(side="left", padx=(12, 0))

        self.balance_label = tk.Label(top, text="Balance: —", fg=c["accent"], bg=c["panel"],
                                      font=("Consolas", 11, "bold"))
        self.balance_label.pack(side="left", padx=18)

        # Per-phone balance mini-strip — shows each account's live balance when the
        # engine is running with multiple accounts. Hidden when only one phone is used.
        self.per_phone_frame = tk.Frame(top, bg=c["panel"])
        self.per_phone_frame.pack(side="left", padx=(0, 12))
        self._per_phone_labels = {}   # phone -> Label widget

        self.winnings_label = tk.Label(top, text="📊 —", fg=c["terminal_fg"], bg=c["panel"],
                                       font=("Consolas", 10))
        self.winnings_label.pack(side="left")

        self.theme_btn = tk.Button(top, text="🌙", relief=tk.FLAT, cursor="hand2",
                                   bg=c["panel"], fg=c["fg"], command=self.toggle_theme,
                                   font=("Segoe UI", 10))
        self.theme_btn.pack(side="right")

        self.nb = ttk.Notebook(self.root)
        self.nb.pack(fill="both", expand=True, padx=6, pady=4)
        self._build_dashboard_tab()
        self._build_fleet_tab()
        self._build_ledger_tab()
        self._build_markets_tab()
        self._build_learning_tab()
        self._build_tools_tab()

    # ── Fleet State tab ─────────────────────────────────────────────────
    # The dashboard terminal is a wall of text: it records WHAT happened but
    # never answers the three questions an operator actually has, which are
    # "is my money safe right now", "what is each account doing", and "is this
    # strategy profitable". This tab answers all three at a glance, from the
    # same state the breakers themselves read, so what is shown here is what is
    # actually gating the next bet rather than a log line that may be stale.
    def _build_fleet_tab(self):
        c = self.colors
        tab = tk.Frame(self.nb, bg=c["bg"], padx=12, pady=10)
        self.nb.add(tab, text="  🚦 Fleet State  ")

        # ── Risk banner: the single most important line in the app ──────
        self.fleet_banner = tk.Label(
            tab, text="⚪ Fleet state unknown — engine not reporting yet",
            bg=c["panel"], fg=c["muted"], anchor="w", justify="left",
            font=("Segoe UI", 11, "bold"), padx=12, pady=10, wraplength=980)
        self.fleet_banner.pack(fill="x", pady=(0, 8))

        # ── ROI / CLV strip ─────────────────────────────────────────────
        mrow = tk.Frame(tab, bg=c["bg"])
        mrow.pack(fill="x", pady=(0, 8))
        self._metric_labels = {}
        for key, title in (("bets", "Real bets"), ("staked", "Staked"),
                           ("returned", "Returned"), ("roi", "ROI"),
                           ("clv", "Avg CLV"), ("refused", "Refused")):
            cell = tk.Frame(mrow, bg=c["panel"], padx=10, pady=6)
            cell.pack(side="left", padx=(0, 8))
            tk.Label(cell, text=title, bg=c["panel"], fg=c["muted"],
                     font=("Segoe UI", 8)).pack(anchor="w")
            val = tk.Label(cell, text="—", bg=c["panel"], fg=c["fg"],
                           font=("Consolas", 12, "bold"))
            val.pack(anchor="w")
            self._metric_labels[key] = val

        # ── Per-account cards ───────────────────────────────────────────
        ak = tk.Label(tab, text="  Accounts  ", bg=c["bg"], fg=c["muted"],
                      font=("Segoe UI", 9, "bold"), anchor="w")
        ak.pack(fill="x")
        ak2 = tk.Label(
            tab,
            text=("START / STOP on the Dashboard runs or stops the whole fleet — "
                  "there is one machine, not one per account. The button on each "
                  "card below freezes or unfreezes that single account against "
                  "the drawdown breaker, without touching the others."),
            bg=c["bg"], fg=c["muted"], font=("Segoe UI", 8), anchor="w",
            justify="left", wraplength=980)
        ak2.pack(fill="x", pady=(0, 4))
        self.fleet_cards = tk.Frame(tab, bg=c["bg"])
        self.fleet_cards.pack(fill="x", pady=(0, 8))
        self._fleet_card_widgets = {}
        self.fleet_empty = tk.Label(
            self.fleet_cards, text="No accounts loaded yet.",
            bg=c["bg"], fg=c["muted"], font=("Segoe UI", 9))
        self.fleet_empty.pack(anchor="w", pady=4)

        # ── Round history, aligned to the ledger ───────────────────────
        hk = tk.Label(tab, text="  Recent rounds  ", bg=c["bg"], fg=c["muted"],
                      font=("Segoe UI", 9, "bold"), anchor="w")
        hk.pack(fill="x")
        cols = ("when", "account", "outcome", "detail", "stake", "odds")
        wrap = tk.Frame(tab, bg=c["bg"])
        wrap.pack(fill="both", expand=True)
        self.round_tree = ttk.Treeview(wrap, columns=cols, show="headings", height=12)
        _st = ttk.Style()
        try:
            _st.theme_use("clam")
        except Exception:
            pass
        heads = {"when": "Time", "account": "Account", "outcome": "Outcome",
                 "detail": "Detail", "stake": "Stake", "odds": "Odds"}
        widths = {"when": 80, "account": 100, "outcome": 96, "detail": 520,
                  "stake": 76, "odds": 70}
        for col in cols:
            self.round_tree.heading(col, text=heads[col])
            self.round_tree.column(col, width=widths[col],
                                   anchor="w" if col == "detail" else "center")
        vsb = ttk.Scrollbar(wrap, orient="vertical", command=self.round_tree.yview)
        self.round_tree.configure(yscrollcommand=vsb.set)
        self.round_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        # Green = a bet actually went on. Blue-grey = a considered decline,
        # which is the machine working, not a fault. Red = a real fault the
        # operator must act on.
        self.round_tree.tag_configure("placed", foreground=c["ok"])
        self.round_tree.tag_configure("declined", foreground=c["muted"])
        self.round_tree.tag_configure("fault", foreground=c["err"])
        self.round_tree.tag_configure("won", foreground=c["ok"])
        self.round_tree.tag_configure("lost", foreground=c["err"])

        self._round_events = []
        self._note_round_event = getattr(self, "_note_round_event", None)

    _PHONE_RE = re.compile(r"\b(\d{10})\b")
    _STAKE_RE = re.compile(r"KES\s*([\d,]+(?:\.\d+)?)", re.I)
    _ODDS_RE = re.compile(r"(?:@|\bat\s+odds\s+|odds\s+x?)\s*x?(\d+(?:\.\d+)?)", re.I)

    def _note_round_event(self, text, tag):
        """Classify a log line into a round outcome for the history table.

        Driven off the same lines the terminal shows, so the table can never
        disagree with the log. Only three buckets matter to the operator:
        a bet went on, the machine considered and declined, or something
        actually broke.
        """
        t = str(text or "")
        up = t.upper()
        kind = None
        if ("BET PLACED" in up) or ("BETSLIP EMPTIED" in up) \
                or ("✅" in t and "PLACED" in up):
            kind = "placed"
        elif "🏆" in t or ("WON" in up and "LOST" not in up):
            kind = "won"
        elif "LOST" in up:
            kind = "lost"
        elif any(k in t for k in ("🛑", "⛔", "HALT", "FROZEN", "FAULT")) \
                or "FATAL" in up or "TRACEBACK" in up or "CRITICAL" in up:
            kind = "fault"
        elif any(k in t for k in ("no bet this round", "No accumulator combination",
                                  "Not enough qualifying", "skipped", "declined",
                                  "🪜", "⏭", "ℹ", "no combo", "refused",
                                  "no bet placed", "Could not")):
            kind = "declined"
        if not kind:
            return
        outcome = {"placed": "PLACED", "won": "WON", "lost": "LOST",
                   "fault": "FAULT", "declined": "DECLINED"}[kind]
        phone = ""
        m = self._PHONE_RE.search(t)
        if m:
            phone = "…" + m.group(1)[-4:]
        elif kind in ("placed", "won", "lost"):
            # Placement lines carry no phone of their own; they belong to
            # whichever account the engine says is betting right now.
            try:
                ap = str((getattr(self.backend, "_engine_state", {}) or {})
                         .get("active_phone") or "")
                phone = ("…" + ap[-4:]) if ap else ""
            except Exception:
                phone = ""
        stake = odds = ""
        ms = self._STAKE_RE.search(t)
        if ms and kind in ("placed", "lost", "won"):
            stake = f"{float(ms.group(1).replace(',', '')):,.0f}"
        mo = self._ODDS_RE.search(t)
        if mo and kind in ("placed", "lost", "won"):
            odds = f"x{mo.group(1)}"
        detail = t.strip()
        if len(detail) > 150:
            detail = detail[:147] + "..."
        try:
            self._round_events.append({
                "when": datetime.now().strftime("%H:%M:%S"),
                "account": phone,
                "outcome": outcome,
                "detail": detail,
                "stake": stake,
                "odds": odds,
                "kind": kind,
            })
            if len(self._round_events) > 300:
                del self._round_events[: len(self._round_events) - 300]
        except Exception:
            pass

    def _refresh_round_history(self):
        try:
            tree = getattr(self, "round_tree", None)
            if tree is None:
                return
            tree.delete(*tree.get_children())
            for ev in list(self._round_events)[-120:][::-1]:
                tree.insert("", tk.END, values=(
                    ev.get("when", ""), ev.get("account", "—"),
                    ev.get("outcome", ""), ev.get("detail", ""),
                    ev.get("stake", ""), ev.get("odds", "")), tags=(ev.get("kind", ""),))
        except Exception:
            pass

    def _fleet_state_snapshot(self):
        """Read the same state the breakers gate on, so the panel cannot lie."""
        snap = {"phones": [], "balances": {}, "workers": {}, "peaks": {},
                "frozen": {}, "halted": False, "halt_reason": "",
                "portfolio_peak": 0.0, "fleet_equity": 0.0, "drawdown": 0.0,
                "open_stake": 0.0, "open_n": 0, "refused": 0,
                "refused_reasons": {}, "metrics": {}, "error": ""}
        try:
            be = getattr(self, "backend", None)
            if be is None:
                snap["error"] = "backend not attached"
                return snap
            es = dict(getattr(be, "_engine_state", {}) or {})
            snap["balances"] = {str(k): v for k, v in (es.get("balances") or {}).items()}
            snap["workers"] = dict(es.get("workers") or {})
            snap["active_phone"] = str(es.get("active_phone") or "")
            ph = [str(p).strip() for p in (es.get("phones") or []) if str(p).strip()]
            if not ph:
                try:
                    ph = [p for p in self._phone_list() if p]
                except Exception:
                    ph = []
            snap["phones"] = ph
            pf = be._load_portfolio()
            snap["peaks"] = dict(pf.get("peaks") or {})
            snap["frozen"] = dict(pf.get("frozen") or {})
            snap["halted"] = bool(pf.get("halted"))
            snap["halt_reason"] = str(pf.get("halt_reason") or "")
            snap["portfolio_peak"] = float(pf.get("portfolio_peak") or 0.0)
            snap["refused"] = int(pf.get("refused") or 0)
            snap["refused_reasons"] = dict(pf.get("refused_reasons") or {})
            try:
                snap["fleet_equity"] = be._fleet_equity(snap["balances"])
            except Exception:
                snap["fleet_equity"] = sum(
                    float(v or 0) for v in snap["balances"].values())
            pk = snap["portfolio_peak"]
            snap["drawdown"] = max(0.0, (pk - snap["fleet_equity"]) / pk) if pk > 0 else 0.0
            try:
                snap["open_stake"] = sum(
                    float(be._active_stake_for(p) or 0.0) for p in ph)
            except Exception:
                snap["open_stake"] = 0.0
            for b in (getattr(be, "_bets", None) or []):
                if str(b.get("status") or "") in ("active", ""):
                    snap["open_n"] += 1
            try:
                snap["metrics"] = be._portfolio_metrics() or {}
            except Exception:
                snap["metrics"] = {}
        except Exception as _e:
            # Never swallow this silently. A status panel that quietly shows zeros
            # when its read failed is indistinguishable from a status panel
            # reporting a dead fleet, which is how a real -87% halt stayed
            # invisible. Surface the error in the banner instead.
            snap["error"] = f"{type(_e).__name__}: {_e}"
        return snap

    def _refresh_fleet_panel(self):
        c = self.colors
        snap = self._fleet_state_snapshot()
        be = getattr(self, "backend", None)
        try:
            pk = snap["portfolio_peak"]
            eq = snap["fleet_equity"]
            dd = snap["drawdown"]
            lim = 0.20
            try:
                lim = float(getattr(be, "PORTFOLIO_DRAWDOWN_HALT", 0.20))
            except Exception:
                pass
            if snap.get("error"):
                # A panel that cannot read the fleet must say so. Showing
                # "healthy" here would be a lie in the exact direction that hurts
                # most: an invisible halt.
                self.fleet_banner.config(
                    text=(f"⚠️  FLEET STATE UNREADABLE — {snap['error']}\n"
                          f"        The numbers below may be stale or zero. This is "
                          f"a fault in the app, not a verdict on the account."),
                    bg="#3a2f10", fg="#ffd75e")
            elif snap["halted"]:
                self.fleet_banner.config(
                    text=(f"🛑  FLEET HALTED — {snap['halt_reason']}\n"
                          f"        No account will bet until the fleet drawdown is "
                          f"inside -{lim:.0%}.  Current: KES {eq:,.2f} against a peak "
                          f"of KES {pk:,.2f} ({dd:.0%} down)."),
                    bg="#3a1414", fg="#ff8a80")
            elif snap["frozen"]:
                _who = ", ".join(sorted(snap["frozen"])[0:3])
                self.fleet_banner.config(
                    text=(f"❄️  {len(snap['frozen'])} ACCOUNT(S) FROZEN by the "
                          f"drawdown breaker ({_who})\n"
                          f"        The rest of the fleet is live.  Fleet equity "
                          f"KES {eq:,.2f} of KES {pk:,.2f} peak ({dd:.0%} down, "
                          f"limit -{lim:.0%})."),
                    bg="#3a2f10", fg="#ffd75e")
            elif dd > 0:
                self.fleet_banner.config(
                    text=(f"🟡  Fleet live — drawdown {dd:.0%} of the "
                          f"-{lim:.0%} limit\n"
                          f"        Equity KES {eq:,.2f} against peak KES "
                          f"{pk:,.2f}."),
                    bg="#2f2a10", fg=c["warn"])
            else:
                self.fleet_banner.config(
                    text=(f"🟢  Fleet healthy — at peak equity, no account frozen\n"
                          f"        Equity KES {eq:,.2f} of KES {pk:,.2f} peak.  "
                          f"Halts below -{lim:.0%}."),
                    bg="#12301f", fg="#7ee2a8")
        except Exception:
            pass

        # ── metric strip ────────────────────────────────────────────────
        m = snap.get("metrics") or {}
        try:
            def _set(k, txt, col=None):
                w = self._metric_labels.get(k)
                if w is None:
                    return
                w.config(text=txt)
                if col:
                    w.config(fg=col)
            _set("bets", f"{m.get('real_bets', 0)}")
            _set("staked", f"{m.get('real_staked', 0):,.0f}")
            _set("returned", f"{m.get('real_returned', 0):,.0f}")
            roi = float(m.get("real_roi") or 0.0)
            _set("roi", f"{roi:+.1%}", c["ok"] if roi > 0 else (c["err"] if roi < 0 else c["fg"]))
            cav = m.get("clv_avg")
            if cav is None:
                _set("clv", "no closes", c["muted"])
            else:
                _set("clv", f"{float(cav):+.2%}",
                     c["ok"] if float(cav) > 0 else (c["err"] if float(cav) < 0 else c["fg"]))
            _set("refused", f"{snap.get('refused', 0)}", c["muted"])
        except Exception:
            pass

        # ── per-account cards ───────────────────────────────────────────
        try:
            self._render_fleet_cards(snap)
        except Exception:
            pass
        try:
            self._refresh_round_history()
        except Exception:
            pass

    def _render_fleet_cards(self, snap):
        c = self.colors
        host = getattr(self, "fleet_cards", None)
        if host is None:
            return
        phones = snap.get("phones") or []
        if not phones:
            return
        try:
            self.fleet_empty.pack_forget()
        except Exception:
            pass
        existing = getattr(self, "_fleet_card_widgets", {}) or {}
        seen = set()
        for phone in phones:
            seen.add(phone)
            w = existing.get(phone)
            bal = snap["balances"].get(phone)
            peak = float(snap["peaks"].get(phone) or 0.0)
            usable = isinstance(bal, (int, float)) and float(bal) > 0
            dd = max(0.0, (peak - float(bal)) / peak) if (usable and peak > 0) else 0.0
            frozen = bool(snap["frozen"].get(phone))
            wk = (snap.get("workers") or {}).get(phone) or {}
            status = str(wk.get("status") or "")
            if not usable:
                state, col = "UNPRICED", c["muted"]
            elif snap.get("halted"):
                state, col = "HALTED", c["err"]
            elif frozen:
                state, col = "FROZEN", c["warn"]
            elif status == "success":
                state, col = "BET PLACED", c["ok"]
            elif status:
                state, col = str(status).upper()[:12], c["fg"]
            else:
                state, col = "IDLE", c["muted"]
            if w is None:
                w = self._make_fleet_card(phone)
                existing[phone] = w
            self._update_fleet_card(w, phone, snap, state, col, bal, peak, dd,
                                    frozen, status, wk)
        for phone in list(existing.keys()):
            if phone not in seen:
                try:
                    existing[phone]["frame"].destroy()
                except Exception:
                    pass
                del existing[phone]
        self._fleet_card_widgets = existing

    def _make_fleet_card(self, phone):
        c = self.colors
        frame = tk.LabelFrame(self.fleet_cards, text=f"  …{str(phone)[-4:]}  ",
                              bg=c["panel"], fg=c["accent"],
                              font=("Segoe UI", 9, "bold"), bd=1,
                              relief=tk.GROOVE, padx=10, pady=6)
        frame.pack(side="left", fill="x", expand=True, padx=(0, 8))
        head = tk.Frame(frame, bg=c["panel"])
        head.pack(fill="x")
        chip = tk.Label(head, text="IDLE", bg=c["panel"], fg=c["muted"],
                        font=("Consolas", 10, "bold"))
        chip.pack(side="left")
        bal = tk.Label(head, text="—", bg=c["panel"], fg=c["fg"],
                       font=("Consolas", 11, "bold"))
        bal.pack(side="right")
        dd = tk.Label(frame, text="", bg=c["panel"], fg=c["muted"],
                      font=("Consolas", 9))
        dd.pack(anchor="w")
        info = tk.Label(frame, text="", bg=c["panel"], fg=c["muted"],
                        font=("Segoe UI", 8), justify="left", anchor="w")
        info.pack(anchor="w", fill="x")
        btn = tk.Button(frame, text="❄️ Freeze", relief=tk.FLAT, cursor="hand2",
                        bg=c["button_bg"], fg=c["button_fg"],
                        font=("Segoe UI", 8, "bold"),
                        command=lambda p=phone: self._toggle_account_freeze(p))
        btn.pack(anchor="w", pady=(4, 0))
        return {"frame": frame, "chip": chip, "bal": bal, "dd": dd,
                "info": info, "btn": btn, "phone": phone}

    def _update_fleet_card(self, w, phone, snap, state, col, bal, peak, dd,
                           frozen, status, wk):
        c = self.colors
        try:
            w["chip"].config(text=state, fg=col)
            if isinstance(bal, (int, float)) and float(bal) > 0:
                w["bal"].config(text=f"KES {float(bal):,.2f}", fg=c["fg"])
                w["dd"].config(
                    text=(f"peak KES {peak:,.2f} · drawdown {dd:.0%}"
                          if peak > 0 else "peak not established"),
                    fg=c["err"] if dd >= 0.40 else (c["warn"] if dd > 0 else c["muted"]))
            else:
                w["bal"].config(text="no reading", fg=c["muted"])
                w["dd"].config(text="equity unknown this round", fg=c["muted"])
            bits = []
            if wk.get("last_ts"):
                try:
                    bits.append("last round " +
                                datetime.fromtimestamp(float(wk["last_ts"])).strftime("%H:%M:%S"))
                except Exception:
                    pass
            if wk.get("round_attempt"):
                bits.append(f"round #{wk['round_attempt']}")
            if wk.get("longshot"):
                bits.append("long-shot")
            bits.append(f"open bets {snap.get('open_n', 0)}")
            if snap.get("open_stake"):
                bits.append(f"staked KES {snap['open_stake']:,.0f}")
            w["info"].config(text=" · ".join(bits) if bits else "no rounds yet")
            w["btn"].config(
                text="▶ Unfreeze" if frozen else "❄️ Freeze",
                bg=c["ok"] if frozen else c["button_bg"],
                fg="#04110a" if frozen else c["button_fg"])
        except Exception:
            pass

    def _toggle_account_freeze(self, phone):
        """Per-account freeze, read and written through the same portfolio file the
        breaker uses, so the panel can never disagree with the gate."""
        try:
            be = getattr(self, "backend", None)
            if be is None:
                return
            pf = be._load_portfolio()
            fro = pf.setdefault("frozen", {})
            if fro.get(str(phone)):
                fro.pop(str(phone), None)
                self._append_log(f"▶ {phone}: drawdown freeze lifted by owner.")
            else:
                fro[str(phone)] = True
                self._append_log(
                    f"❄️ {phone}: frozen by owner — the drawdown breaker will "
                    f"refuse this account until it is unfrozen.")
            be._save_portfolio()
            self._refresh_fleet_panel()
        except Exception:
            pass

    def _refresh_fleet_panel_safe(self):
        try:
            self._refresh_fleet_panel()
        except Exception:
            pass

    def _styled_button(self, parent, text, command, fg=None, bg=None, width=16,
                       font=("Segoe UI", 10, "bold")):
        c = self.colors
        return tk.Button(parent, text=text, command=command, relief=tk.FLAT,
                         cursor="hand2", font=font, width=width,
                         bg=bg or c["button_bg"], fg=fg or c["button_fg"],
                         activebackground=c["accent_dark"], activeforeground="white")

    # ── Dashboard ────────────────────────────────────────────────────
    def _build_dashboard_tab(self):
        c = self.colors
        tab = tk.Frame(self.nb, bg=c["bg"], padx=12, pady=10)
        self.nb.add(tab, text="  🏠 Dashboard  ")

        account = tk.LabelFrame(tab, text="  Account(s)  ", bg=c["panel"], fg=c["accent"],
                                font=("Segoe UI", 9, "bold"),
                                labelanchor="nw", bd=1, relief=tk.GROOVE)
        account.pack(fill="x", pady=(0, 5))

        arow = tk.Frame(account, bg=c["panel"])
        arow.pack(fill="x", padx=8, pady=3)
        arow.columnconfigure(1, weight=1)
        tk.Label(arow, text="Phone (one per line):", bg=c["panel"], fg=c["muted"],
                 font=("Segoe UI", 9)).grid(row=0, column=0, sticky="nw", padx=(0, 8), pady=4)
        self.phone_text = scrolledtext.ScrolledText(arow, height=1, width=32,
                                                    bg=c["text_bg"], fg=c["text_fg"],
                                                    insertbackground=c["text_fg"],
                                                    relief=tk.FLAT, bd=0,
                                                    highlightthickness=1,
                                                    highlightbackground=c["border"],
                                                    font=("Consolas", 10))
        self.phone_text.grid(row=0, column=1, sticky="nsew", padx=(0, 14))
        pwcell = tk.Frame(arow, bg=c["panel"])
        pwcell.grid(row=0, column=2, sticky="n", padx=(0, 6))
        tk.Label(pwcell, text="Password:", bg=c["panel"], fg=c["muted"],
                 font=("Segoe UI", 9)).pack(anchor="w")
        self.password_var = tk.StringVar()
        self.password_entry = tk.Entry(pwcell, textvariable=self.password_var, width=20,
                                       show="*", bg=c["text_bg"], fg=c["text_fg"],
                                       insertbackground=c["text_fg"], relief=tk.FLAT,
                                       highlightthickness=1,
                                       highlightbackground=c["border"])
        self.password_entry.pack(anchor="w", padx=(0, 8), pady=(2, 0), ipady=4)
        self.show_pw_btn = self._styled_button(arow, "👁", self._toggle_show_pw,
                                               width=3, font=("Segoe UI", 10))
        self.show_pw_btn.grid(row=0, column=3, sticky="n", pady=14)

        # ── Lock In button — saves phone numbers so they auto-load on next launch ──
        self.lock_in_var = tk.BooleanVar(value=False)
        self.lock_in_btn = tk.Checkbutton(
            arow, text="🔒 Lock In",
            variable=self.lock_in_var,
            command=self._toggle_lock_in,
            bg=c["panel"], fg=c["fg"],
            selectcolor="#1a3a1a",
            activebackground=c["panel"],
            activeforeground=c["fg"],
            font=("Segoe UI", 8, "bold"),
            cursor="hand2",
        )
        self.lock_in_btn.grid(row=0, column=4, sticky="n", padx=(8, 0), pady=14)

        self.sync_btn = self._styled_button(arow, "🔄 Sync Winnings",
                                            self.start_sync_winnings,
                                            bg=c["accent"], fg="#0a1420", width=11,
                                            font=("Segoe UI", 8, "bold"))
        self.sync_btn.grid(row=0, column=5, sticky="n", padx=(8, 0), pady=14)
        self.history_btn = self._styled_button(arow, "📋 Live History",
                                               self.show_live_bet_history,
                                               bg=c["button_bg"], width=10,
                                               font=("Segoe UI", 8, "bold"))
        self.history_btn.grid(row=0, column=6, sticky="n", padx=(4, 0), pady=14)

        params = tk.Frame(tab, bg=c["bg"])
        params.pack(fill="x", pady=(0, 4))
        self._field(params, "Stake KES", "stake_var", "10", 0, 0)
        self._field(params, "Every (min)", "cadence_var", "60", 0, 1)
        self._field(params, "Daily cap (0=∞)", "daily_var", "20", 0, 2)
        self._field(params, "Max bets (0=∞)", "max_var", "0", 1, 0)
        self._field(params, "Stake % (0=fixed)", "pct_var", "0", 1, 1)

        self.chain_var = tk.BooleanVar(value=True)
        self.autostart_var = tk.BooleanVar(value=True)
        self.longshot_var = tk.BooleanVar(value=True)
        self.headless_var = tk.BooleanVar(value=True)
        chain_chk = tk.Checkbutton(params, text="🧲 Chain slips (hungry)",
                                   variable=self.chain_var, bg=c["bg"], fg=c["fg"],
                                   selectcolor=c["panel"], activebackground=c["bg"],
                                   activeforeground=c["fg"], font=("Segoe UI", 9, "bold"))
        chain_chk.grid(row=1, column=2, sticky="w", padx=14)
        auto_chk = tk.Checkbutton(params, text="Auto-start on launch",
                                  variable=self.autostart_var, bg=c["bg"], fg=c["fg"],
                                  selectcolor=c["panel"], activebackground=c["bg"],
                                  activeforeground=c["fg"], font=("Segoe UI", 9))
        auto_chk.grid(row=2, column=0, sticky="w", padx=2)
        ls_chk = tk.Checkbutton(params, text="🎯 Daily long-shot",
                                variable=self.longshot_var, bg=c["bg"], fg=c["fg"],
                                selectcolor=c["panel"], activebackground=c["bg"],
                                activeforeground=c["fg"], font=("Segoe UI", 9, "bold"))
        ls_chk.grid(row=2, column=2, sticky="w", padx=14)
        hd_chk = tk.Checkbutton(params, text="🤫 Headless (no window)",
                                variable=self.headless_var, bg=c["bg"], fg=c["fg"],
                                selectcolor=c["panel"], activebackground=c["bg"],
                                activeforeground=c["fg"], font=("Segoe UI", 9))
        hd_chk.grid(row=2, column=1, sticky="w", padx=2)
        # ── ROLL-OVER mode (owner rule): KES 50 @ ~x3.00 odds, exactly 3 legs,
        # twice a day. Lives as a compact toggle button next to MID POT in the
        # action row — an in-parameter full-width chip ate terminal height
        # every launch, so it moved out of the params grid. ─────────────────
        self.roll_over_var = tk.BooleanVar(value=False)
        self._field(params, "LS legs (0=off)", "ls_legs_var", "14", 3, 0)
        self._field(params, "LS x min", "ls_min_var", "15", 3, 1)
        self._field(params, "LS x max", "ls_max_var", "60", 3, 2)
        self._field(params, "Auto-withdraw KES (0=off)", "withdraw_var", "200", 4, 0)
        self._field(params, "Deposit KES (M-Pesa)", "deposit_var", "99", 4, 1)
        self.cashout_var = tk.BooleanVar(value=True)
        self.cashout_pct_var = tk.StringVar(value="75")
        tk.Checkbutton(params, text="💱 Auto cash-out",
                       variable=self.cashout_var, bg=c["bg"], fg=c["fg"],
                       selectcolor=c["panel"], activebackground=c["bg"],
                       activeforeground=c["fg"], font=("Segoe UI", 9, "bold")).grid(
                       row=4, column=2, sticky="w", padx=14)
        self._field(params, "CO min % (0-100)", "cashout_pct_var", "75", 5, 2)
        self.notify_var = tk.BooleanVar(value=True)
        tk.Checkbutton(params, text="🔔 Sounds + toasts",
                       variable=self.notify_var, bg=c["bg"], fg=c["fg"],
                       selectcolor=c["panel"], activebackground=c["bg"],
                       activeforeground=c["fg"], font=("Segoe UI", 9)).grid(
                       row=5, column=0, sticky="w", padx=2, pady=(6, 0))
        self._field(params, "Jackpot KES", "jackpot_stake_var", "99", 5, 1)

        # ── Markets to bet — kept as always-on defaults; the on-screen toggles
        # were removed to give the terminal more vertical area. All markets stay
        # enabled (selector builds legs from every group below). ─────────────
        self.mk_vars = {
            "1x2": tk.BooleanVar(value=True),
            "btts": tk.BooleanVar(value=True),
            "ou25": tk.BooleanVar(value=True),
            "ou15": tk.BooleanVar(value=True),
        }
        self.bet_on_label = tk.Label(params, text="Betting on: 1X2 · BTTS · O/U 2.5 · O/U 1.5 (all)",
                                     bg=c["bg"], fg=c["muted"], font=("Segoe UI", 8))
        self.bet_on_label.grid(row=6, column=0, columnspan=3, sticky="w", padx=2, pady=(1, 0))

        ctl = tk.Frame(tab, bg=c["bg"])
        ctl.pack(fill="x", pady=(0, 4))
        _bfont = ("Segoe UI", 8, "bold")
        _mfont = ("Segoe UI", 8)
        self.start_btn = self._styled_button(ctl, "▶ START",
                                             self.start_bet_machine,
                                             bg=c["ok"], fg="#04110a", width=10,
                                             font=_bfont)
        self.start_btn.grid(row=0, column=0, sticky="w", padx=(0, 4))
        self.stop_btn = self._styled_button(ctl, "■ STOP",
                                            self.emergency_stop,
                                            bg=c["err"], fg="white", width=9,
                                            font=_bfont)
        self.stop_btn.config(state="disabled")
        self.stop_btn.grid(row=0, column=1, sticky="w", padx=(0, 4))
        self.check_balance_btn = self._styled_button(ctl, "⚡ Balance",
                                                     self.start_balance_check,
                                                     bg=c["button_bg"], width=9,
                                                     font=_bfont)
        self.check_balance_btn.grid(row=0, column=2, sticky="w", padx=(0, 4))
        self.withdraw_btn = self._styled_button(ctl, "💸 Withdraw",
                                                self.start_withdraw_flow,
                                                bg=c["accent_dark"], fg="#201800",
                                                width=9, font=_bfont)
        self.withdraw_btn.grid(row=0, column=3, sticky="w", padx=(0, 4))
        self.deposit_btn = self._styled_button(ctl, "💵 Deposit",
                                               self.start_deposit_flow,
                                               bg="#1f7a33", fg="white", width=9,
                                               font=_bfont)
        self.deposit_btn.grid(row=0, column=4, sticky="w", padx=(0, 4))
        self.mega_btn = self._styled_button(ctl, "🎰 MEGA",
                                            self.start_mega_pot,
                                            bg="#8a5a00", fg="#ffe08a", width=8,
                                            font=_bfont)
        self.mega_btn.grid(row=1, column=0, sticky="w", padx=(0, 4), pady=(3, 0))
        self.mid_btn = self._styled_button(ctl, "🀄 MID",
                                           self.start_mid_pot,
                                           bg="#5b3d8f", fg="#e8dcff", width=8,
                                           font=_bfont)
        self.mid_btn.grid(row=1, column=1, sticky="w", padx=(0, 4), pady=(3, 0))
        self.form_btn = self._styled_button(ctl, "📈 Form",
                                            self.show_form_cache, width=8,
                                            font=_mfont,
                                            bg=c["muted"])
        self.form_btn.grid(row=1, column=2, sticky="w", padx=(0, 4), pady=(3, 0))
        self.roll_btn = self._styled_button(ctl, "⚡ ROLL",
                                            self._toggle_roll_over,
                                            bg=c["button_bg"], width=8,
                                            font=_bfont)
        self.roll_btn.grid(row=1, column=3, sticky="w", padx=(0, 4), pady=(3, 0))
        self.ready_lbl = tk.Label(ctl, text="⚪ jackpot research idle", bg=c["panel"],
                                  fg=c["muted"], font=("Segoe UI", 8, "bold"))
        self.ready_lbl.grid(row=1, column=4, columnspan=2, sticky="w", padx=(8, 0), pady=(3, 0))
        self._last_ready_refresh = 0.0

        lbl = tk.Label(tab, text="  Live Machine Log  ", bg=c["bg"], fg=c["muted"],
                       font=("Segoe UI", 9, "bold"), anchor="w")
        lbl.pack(fill="x")
        logrow = tk.Frame(tab, bg=c["bg"])
        logrow.pack(fill="both", expand=True)
        _fsize = getattr(self, "_terminal_font_size", 10)
        self._terminal_font_size = _fsize
        self.terminal = scrolledtext.ScrolledText(logrow, height=26, state="disabled",
                                                  wrap="word", relief=tk.FLAT, bd=0,
                                                  bg=c["terminal_bg"],
                                                  fg=c["terminal_fg"],
                                                  insertbackground=c["terminal_fg"],
                                                  font=("Consolas", _fsize))
        self.terminal.pack(side="left", fill="both", expand=True)

        # ── Colour-coded log tags ─────────────────────────────────────
        # Each message type gets a distinct colour so the log is scannable at a glance.
        self.terminal.tag_configure("win",      foreground="#ffd700", font=("Consolas", _fsize, "bold"))  # gold
        self.terminal.tag_configure("loss",     foreground="#ff5252", font=("Consolas", _fsize, "bold"))  # red
        self.terminal.tag_configure("bet",      foreground="#5fd068", font=("Consolas", _fsize, "bold"))  # bright green
        self.terminal.tag_configure("longshot", foreground="#ffb400", font=("Consolas", _fsize, "bold"))  # amber
        self.terminal.tag_configure("warn",     foreground="#ff9640")                                     # orange
        self.terminal.tag_configure("fibi",     foreground="#ff80c8")                                     # pink
        self.terminal.tag_configure("research", foreground="#40d4ff")                                     # cyan
        self.terminal.tag_configure("money",    foreground="#ffe066")                                     # yellow
        self.terminal.tag_configure("ok",       foreground="#5fd068")                                     # green
        self.terminal.tag_configure("muted",    foreground="#5a6a7a")                                     # dim grey
        self.terminal.tag_configure("div",      foreground="#2a3848")                                     # very dim separator
        # Ctrl+scroll zoom on the terminal
        self.terminal.bind("<Control-MouseWheel>", self._terminal_scroll_zoom)
        self.terminal.bind("<Control-Button-4>", self._terminal_scroll_zoom)  # Linux up
        self.terminal.bind("<Control-Button-5>", self._terminal_scroll_zoom)  # Linux down

        logtools = tk.Frame(logrow, bg=c["bg"])
        logtools.pack(side="left", fill="y", padx=(8, 0))
        self._styled_button(logtools, "📜 Auto-scroll", self.toggle_auto_scroll, width=13,
                            font=("Segoe UI", 8)).pack(pady=(0, 6))
        self._styled_button(logtools, "🔍+  Zoom in", self._terminal_zoom_in, width=13,
                            font=("Segoe UI", 8), bg=c["accent_dark"]).pack(pady=(0, 2))
        self._styled_button(logtools, "🔍−  Zoom out", self._terminal_zoom_out, width=13,
                            font=("Segoe UI", 8), bg=c["accent_dark"]).pack(pady=(0, 6))
        self._styled_button(logtools, "🗑 Clear log", lambda: self._clear_log(),
                            width=13, font=("Segoe UI", 8),
                            bg=c["muted"]).pack(pady=(0, 6))
        self._styled_button(logtools, "📤 Export log", self._export_log,
                            width=13, font=("Segoe UI", 8),
                            bg=c["muted"]).pack(pady=(0, 6))

        self._show_all_var = tk.BooleanVar(value=False)
        tk.Checkbutton(logtools, text="Show all", variable=self._show_all_var,
                       command=self._toggle_show_all, bg=c["bg"], fg=c["muted"],
                       selectcolor=c["text_bg"], activebackground=c["bg"],
                       activeforeground=c["text_fg"], font=("Segoe UI", 8),
                       highlightthickness=0, anchor="w", justify="left"
                       ).pack(fill="x", pady=(0, 6))

        self.auto_scroll_enabled = True

    def _field(self, parent, label, var_name, default, r, col):
        c = self.colors
        f = tk.Frame(parent, bg=c["bg"])
        f.grid(row=r, column=col, sticky="w", padx=(0, 18), pady=1)
        tk.Label(f, text=label, bg=c["bg"], fg=c["muted"], font=("Consolas", 8)).pack(side="left")
        var = tk.StringVar(value=default)
        setattr(self, var_name, var)
        e = tk.Entry(f, textvariable=var, width=9, bg=c["text_bg"], fg=c["text_fg"],
                     insertbackground=c["text_fg"], justify="center", relief=tk.FLAT,
                     highlightthickness=1, highlightbackground=c["border"], font=("Consolas", 10))
        e.pack(side="left", padx=(6, 0), ipady=3)

    # ── Ledger tab ────────────────────────────────────────────────────
    def _build_ledger_tab(self):
        c = self.colors
        tab = tk.Frame(self.nb, bg=c["bg"], padx=12, pady=10)
        self.nb.add(tab, text="  📒 Ledger  ")

        bar = tk.Frame(tab, bg=c["bg"])
        bar.pack(fill="x", pady=(0, 8))
        self._styled_button(bar, "↻ Refresh", self._refresh_ledger, width=12).pack(side="left")
        self._styled_button(bar, "💾 Export CSV", self._export_ledger_csv, width=14,
                            bg=c["muted"]).pack(side="left", padx=(8, 0))
        self.ledger_hint = tk.Label(bar, text="", bg=c["bg"], fg=c["muted"],
                                    font=("Segoe UI", 9))
        self.ledger_hint.pack(side="left", padx=12)

        cols = ("id", "placed", "phone", "status", "stake", "odds", "win", "markets", "recipe")
        wrap = tk.Frame(tab, bg=c["bg"])
        wrap.pack(fill="both", expand=True)
        self.ledger_tree = ttk.Treeview(wrap, columns=cols, show="headings", height=16)
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        heads = {"id": "Bet ID", "placed": "Placed", "phone": "Account",
                 "status": "Status",
                 "stake": "Stake", "odds": "Odds", "win": "Win",
                 "markets": "Markets", "recipe": "Recipe"}
        widths = {"id": 90, "placed": 140, "phone": 100, "status": 90, "stake": 70, "odds": 70,
                  "win": 90, "markets": 190, "recipe": 200}
        for col in cols:
            self.ledger_tree.heading(col, text=heads[col])
            self.ledger_tree.column(col, width=widths[col], anchor="center")
        vsb = ttk.Scrollbar(wrap, orient="vertical", command=self.ledger_tree.yview)
        self.ledger_tree.configure(yscrollcommand=vsb.set)
        self.ledger_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.ledger_tree.tag_configure("won", foreground=c["ok"])
        self.ledger_tree.tag_configure("lost", foreground=c["err"])
        self.ledger_tree.tag_configure("active", foreground=c["warn"])

    # ── Markets tab ───────────────────────────────────────────────────
    def _build_markets_tab(self):
        c = self.colors
        tab = tk.Frame(self.nb, bg=c["bg"], padx=12, pady=10)
        self.nb.add(tab, text="  📋 Markets  ")

        bar = tk.Frame(tab, bg=c["bg"])
        bar.pack(fill="x", pady=(0, 8))
        tk.Label(bar, text="Game ID (blank = first game):", bg=c["bg"], fg=c["muted"],
                 font=("Segoe UI", 9)).pack(side="left")
        self.allmkt_gid_var = tk.StringVar()
        tk.Entry(bar, textvariable=self.allmkt_gid_var, width=12, bg=c["text_bg"],
                 fg=c["text_fg"], insertbackground=c["text_fg"], relief=tk.FLAT,
                 highlightthickness=1, highlightbackground=c["border"],
                 font=("Consolas", 10)).pack(side="left", padx=(8, 10), ipady=3)
        self.markets_btn = self._styled_button(bar, "📋 Show ALL MARKETS",
                                               self.view_all_markets, width=22)
        self.markets_btn.pack(side="left")

        hint = ("Full market dump for one game: DOUBLE CHANCE, 1X2 1UP/2UP/3UP, DNB, "
                "Asian lines and more. Requires login (uses the machine browser if it is "
                "already running, otherwise opens a temporary one).")
        tk.Label(tab, text=hint, bg=c["bg"], fg=c["muted"], font=("Segoe UI", 8),
                 justify="left", wraplength=950, anchor="w").pack(fill="x", pady=(0, 6))
        self.markets_btn2 = self._styled_button(tab, "📣 Load markets into live log",
                                                self.view_all_markets, width=30,
                                                font=("Segoe UI", 9))
        self.markets_btn2.pack(anchor="w")

    # ── Learning tab ──────────────────────────────────────────────────
    def _build_learning_tab(self):
        c = self.colors
        tab = tk.Frame(self.nb, bg=c["bg"], padx=12, pady=10)
        self.nb.add(tab, text="  🧠 Learning  ")

        bar = tk.Frame(tab, bg=c["bg"])
        bar.pack(fill="x", pady=(0, 8))
        self._styled_button(bar, "↻ Refresh stats", self._refresh_learning, width=16).pack(side="left")
        self.learning_summary = tk.Label(bar, text="", bg=c["bg"], fg=c["muted"],
                                         font=("Segoe UI", 9))
        self.learning_summary.pack(side="left", padx=12)

        cols = ("mkt", "trials", "won", "hit", "pred", "deficit", "weight", "status")
        wrap = tk.Frame(tab, bg=c["bg"])
        wrap.pack(fill="both", expand=True)
        self.learning_tree = ttk.Treeview(wrap, columns=cols, show="headings", height=9)
        heads = {"mkt": "Market", "trials": "Trials", "won": "Won", "hit": "Hit-rate",
                 "pred": "Predicted", "deficit": "Deficit", "weight": "Boost",
                 "status": "Status"}
        widths = {"mkt": 130, "trials": 70, "won": 60, "hit": 90, "pred": 100,
                  "deficit": 90, "weight": 70, "status": 110}
        for col in cols:
            self.learning_tree.heading(col, text=heads[col])
            self.learning_tree.column(col, width=widths[col], anchor="center")
        vsb = ttk.Scrollbar(wrap, orient="vertical", command=self.learning_tree.yview)
        self.learning_tree.configure(yscrollcommand=vsb.set)
        self.learning_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.learning_tree.tag_configure("retired", foreground=c["err"])
        self.learning_tree.tag_configure("boosted", foreground=c["ok"])

        tk.Label(tab, text="  Recipe / odds-band performance  ", bg=c["bg"], fg=c["muted"],
                 font=("Segoe UI", 9, "bold"), anchor="w").pack(fill="x", pady=(8, 2))
        rcols = ("recipe", "trials", "won", "roi", "status")
        wrap2 = tk.Frame(tab, bg=c["bg"])
        wrap2.pack(fill="both", expand=True)
        self.recipe_tree = ttk.Treeview(wrap2, columns=rcols, show="headings", height=6)
        rheads = {"recipe": "Recipe (legs@band/lead/mix)", "trials": "Trials", "won": "Won",
                  "roi": "ROI", "status": "Status"}
        rwidths = {"recipe": 330, "trials": 70, "won": 60, "roi": 90, "status": 120}
        for col in rcols:
            self.recipe_tree.heading(col, text=rheads[col])
            self.recipe_tree.column(col, width=rwidths[col], anchor="center")
        vsb2 = ttk.Scrollbar(wrap2, orient="vertical", command=self.recipe_tree.yview)
        self.recipe_tree.configure(yscrollcommand=vsb2.set)
        self.recipe_tree.pack(side="left", fill="both", expand=True)
        vsb2.pack(side="right", fill="y")

        tk.Label(tab, text="  Analyst accuracy by confidence bucket  ", bg=c["bg"], fg=c["muted"],
                 font=("Segoe UI", 9, "bold"), anchor="w").pack(fill="x", pady=(8, 2))
        acols = ("bucket", "picks", "wins", "accuracy", "note")
        wrap3 = tk.Frame(tab, bg=c["bg"])
        wrap3.pack(fill="both", expand=True)
        self.analyst_tree = ttk.Treeview(wrap3, columns=acols, show="headings", height=4)
        aheads = {"bucket": "Confidence", "picks": "Picks used", "wins": "Slips won",
                  "accuracy": "Win rate", "note": "Verdict"}
        awidths = {"bucket": 110, "picks": 90, "wins": 90, "accuracy": 90, "note": 260}
        for col in acols:
            self.analyst_tree.heading(col, text=aheads[col])
            self.analyst_tree.column(col, width=awidths[col], anchor="center")
        vsb3 = ttk.Scrollbar(wrap3, orient="vertical", command=self.analyst_tree.yview)
        self.analyst_tree.configure(yscrollcommand=vsb3.set)
        self.analyst_tree.pack(side="left", fill="both", expand=True)
        vsb3.pack(side="right", fill="y")
        self.analyst_tree.tag_configure("good", foreground=c["ok"])
        self.analyst_tree.tag_configure("poor", foreground=c["err"])

        self._refresh_learning()

    # ── Tools tab ─────────────────────────────────────────────────────
    def _build_tools_tab(self):
        c = self.colors
        tab = tk.Frame(self.nb, bg=c["bg"], padx=12, pady=10)
        self.nb.add(tab, text="  🧰 Tools  ")

        bal = tk.LabelFrame(tab, text="  Balance Checker  ", bg=c["panel"],
                            fg=c["accent"], font=("Segoe UI", 9, "bold"),
                            labelanchor="nw", bd=1, relief=tk.GROOVE)
        bal.pack(fill="x", pady=(0, 10))
        b1 = tk.Frame(bal, bg=c["panel"])
        b1.pack(fill="x", padx=10, pady=8)
        tk.Label(b1, text="Checks every account entered in the Dashboard's phone box. "
                          "Results land in the live log.",
                 bg=c["panel"], fg=c["muted"], font=("Segoe UI", 9), justify="left",
                 wraplength=900, anchor="w").pack(fill="x")
        self._styled_button(b1, "⚡ Start Balance Check", self.start_balance_check,
                            width=24).pack(anchor="w", pady=(6, 0))

        wd = tk.LabelFrame(tab, text="  Withdraw  ", bg=c["panel"], fg=c["accent"],
                           font=("Segoe UI", 9, "bold"), labelanchor="nw",
                           bd=1, relief=tk.GROOVE)
        wd.pack(fill="x")
        w1 = tk.Frame(wd, bg=c["panel"])
        w1.pack(fill="x", padx=10, pady=8)
        tk.Label(w1, text="Withdraws a fixed amount from every account in the phone box. "
                          "You will be asked for the amount (KES). Uses the safe browser "
                          "withdraw flow.",
                 bg=c["panel"], fg=c["muted"], font=("Segoe UI", 9), justify="left",
                 wraplength=900, anchor="w").pack(fill="x")
        self._styled_button(w1, "💸 Withdraw from all accounts",
                            self.start_withdraw_flow, width=24,
                            bg=c["accent_dark"], fg="#201800").pack(anchor="w", pady=(6, 0))

        about = tk.LabelFrame(tab, text="  System  ", bg=c["panel"], fg=c["accent"],
                              font=("Segoe UI", 9, "bold"), labelanchor="nw",
                              bd=1, relief=tk.GROOVE)
        about.pack(fill="x", pady=(10, 0))
        a1 = tk.Frame(about, bg=c["panel"])
        a1.pack(fill="x", padx=10, pady=8)
        tk.Label(a1, text=(f"BetFlow Pro v{APP_VERSION} — self-learning SportPesa "
                           "auto-bet machine.\n"
                           "Hungry chaining, no-repeat memory, daily cap, compounding stake,\n"
                           "market-type retirement/boost and an odds-band bandit after 30+ "
                           "settled bets."),
                 bg=c["panel"], fg=c["muted"], font=("Segoe UI", 9), justify="left",
                 anchor="w").pack(fill="x")

        # ── Diagnostics & Control ──────────────────────────────────────
        diag = tk.LabelFrame(tab, text="  Diagnostics & Control  ", bg=c["panel"],
                             fg=c["accent"], font=("Segoe UI", 9, "bold"),
                             labelanchor="nw", bd=1, relief=tk.GROOVE)
        diag.pack(fill="x", pady=(10, 0))
        d1 = tk.Frame(diag, bg=c["panel"])
        d1.pack(fill="x", padx=10, pady=8)
        row1 = tk.Frame(d1, bg=c["panel"])
        row1.pack(fill="x", pady=(0, 6))
        self._styled_button(row1, "🔄 Full Win-Sync",
                            self.start_sync_winnings,
                            width=16, font=("Segoe UI", 9),
                            bg=c["accent"], fg="#0a1420").pack(side="left", padx=(0, 8))
        self._styled_button(row1, "🗑️ Clear Usage Memory",
                            self._clear_usage_memory,
                            width=18, font=("Segoe UI", 9),
                            bg=c["muted"]).pack(side="left", padx=(0, 8))
        self._styled_button(row1, "🔓 Unpark All Accounts",
                            self._unpark_all_accounts,
                            width=18, font=("Segoe UI", 9),
                            bg="#5b3d8f", fg="#e8dcff").pack(side="left", padx=(0, 8))
        row2 = tk.Frame(d1, bg=c["panel"])
        row2.pack(fill="x", pady=(0, 6))
        self._styled_button(row2, "📊 Show Fibi Status",
                            self._show_fibi_status,
                            width=16, font=("Segoe UI", 9),
                            bg=c["button_bg"]).pack(side="left", padx=(0, 8))
        self._styled_button(row2, "🗂️ Clean Balance Reports",
                            self._run_cleaner_now,
                            width=20, font=("Segoe UI", 9),
                            bg=c["muted"]).pack(side="left", padx=(0, 8))
        self._styled_button(row2, "🧹 Reset Stale Active Bets",
                            self._force_settle_stale,
                            width=22, font=("Segoe UI", 9),
                            bg=c["err"], fg="white").pack(side="left", padx=(0, 8))

    # ── Dashboard actions ─────────────────────────────────────────────
    def _phone_list(self):
        txt = ""
        try:
            txt = self.phone_text.get("1.0", tk.END).strip()
        except Exception:
            pass
        phones = []
        for line in txt.splitlines():
            line = line.strip()
            if not line:
                continue
            for p in line.split(","):
                p = p.strip()
                if p:
                    phones.append(p)
        return phones

    def _toggle_show_pw(self):
        self.password_entry.config(show="" if self.password_entry.cget("show") == "*" else "*")

    def _toggle_lock_in(self):
        """Save or clear the locked-in phone numbers and password."""
        c = self.colors
        locked = self.lock_in_var.get()
        if locked:
            # Save current phones and password into settings immediately
            try:
                import json as _j
                sp = self._settings_path()
                try:
                    with open(sp, "r", encoding="utf-8") as f:
                        d = _j.load(f)
                except Exception:
                    d = {}
                phones = self._phone_list()
                pw = self.password_var.get().strip()
                d["lock_in"] = True
                d["phones_locked"] = phones
                d["phones"] = phones
                d["phone"] = phones[0] if phones else ""
                d["password_locked"] = pw
                with open(sp, "w", encoding="utf-8") as f:
                    _j.dump(d, f, indent=2)
                self.lock_in_btn.config(fg=c["ok"])
                self._emit(f"🔒 Locked in {len(phones)} account(s) — will auto-load on next launch.")
            except Exception as e:
                self._emit(f"⚠️ Lock-in save failed: {e}")
        else:
            # Clear the lock — phones won't auto-load next time
            try:
                import json as _j
                sp = self._settings_path()
                try:
                    with open(sp, "r", encoding="utf-8") as f:
                        d = _j.load(f)
                except Exception:
                    d = {}
                d["lock_in"] = False
                d.pop("phones_locked", None)
                d.pop("password_locked", None)
                with open(sp, "w", encoding="utf-8") as f:
                    _j.dump(d, f, indent=2)
                self.lock_in_btn.config(fg=c["fg"])
                self._emit("🔓 Lock-in cleared — phone numbers will need to be entered on next launch.")
            except Exception as e:
                self._emit(f"⚠️ Lock-in clear failed: {e}")

    # ── Diagnostics button handlers ───────────────────────────────────

    def _clear_usage_memory(self):
        """Clear the no-repeat game memory so all games are eligible again."""
        try:
            import json
            from resource_path import writable_path
            p = writable_path("sportsape_usage.json")
            with open(p, "w", encoding="utf-8") as f:
                json.dump({}, f)
            self.backend._used_games = {}
            self._emit("🗑️ Usage memory cleared — all games eligible for next slip.")
        except Exception as e:
            self._emit(f"⚠️ Could not clear usage memory: {e}")

    def _unpark_all_accounts(self):
        """Force-unpark all accounts that the engine has parked due to login failures."""
        try:
            es = getattr(self.backend, "_engine_state", {})
            if es:
                es.pop("force_relogin", None)
            hub = getattr(self.backend, "_agent_hub", None)
            if hub:
                hub.fibi.state.get("parked_since", {}).clear()
                hub.fibi._save_state()
                hub.fibi.state["consecutive_aborts"] = 0
                hub.fibi.state["consecutive_balance_unreadable"] = {}
                hub.fibi._save_state()
            self._emit("🔓 All accounts unparked — machine will retry logins immediately.")
        except Exception as e:
            self._emit(f"⚠️ Unpark failed: {e}")

    def _show_fibi_status(self):
        """Print Fibi's current watchdog status to the live log."""
        try:
            hub = getattr(self.backend, "_agent_hub", None)
            if hub is None:
                self._emit("🌸 Fibi: agents not running (start the bet machine first).")
                return
            sl = hub.fibi.status_line()
            self._emit(f"🌸 Fibi status: {sl}")
            ws = hub.fibi.state.get("warnings_log") or []
            if ws:
                self._emit(f"🌸 Last {min(5, len(ws))} warnings:")
                for entry in ws[-5:]:
                    self._emit(f"   • {entry.get('msg', '')}")
            else:
                self._emit("🌸 Fibi: no warnings on record.")
        except Exception as e:
            self._emit(f"⚠️ Fibi status failed: {e}")

    def _run_cleaner_now(self):
        """Force-run the balance report cleaner immediately."""
        try:
            hub = getattr(self.backend, "_agent_hub", None)
            if hub is None:
                # Run without agent hub using the cleaner directly
                from sportsape_agents import BalanceReportCleaner
                import os
                base = os.path.dirname(os.path.abspath(__file__))
                c = BalanceReportCleaner(search_dir=base)
                r = c.run(gui_callback=self._emit)
                self._emit(f"🗂️ Cleaner done: scanned {r['scanned']}, "
                           f"deleted {r['deleted']}, freed {r['freed_bytes']:,} bytes")
                return
            hub.cleaner._last_run = 0  # force next should_run() to return True
            result = hub.clean_balance_reports(gui_callback=self._emit)
            if result:
                self._emit(f"🗂️ Cleaner: scanned {result.get('scanned', 0)}, "
                           f"deleted {result.get('deleted', 0)}, "
                           f"freed {result.get('freed_bytes', 0):,} bytes")
        except Exception as e:
            self._emit(f"⚠️ Cleaner failed: {e}")

    def _force_settle_stale(self):
        """Mark any bet active for 48+ hours as lost so the ledger stays clean."""
        if not messagebox.askyesno("Confirm",
                                   "Mark all bets older than 48 hours as lost?\n\n"
                                   "Only do this if the machine didn't sync their results."):
            return
        try:
            from datetime import datetime as _dt
            self.backend._load_ledger()
            now = _dt.now()
            count = 0
            for b in getattr(self.backend, "_bets", []) or []:
                if str(b.get("status") or "").startswith("shadow"):
                    continue
                if b.get("status") not in ("active", None, ""):
                    continue
                try:
                    age_h = (now - _dt.fromisoformat(b.get("placed_at") or "")).total_seconds() / 3600
                except Exception:
                    age_h = 0
                if age_h >= 48:
                    b["status"] = "lost"
                    b["settled_at"] = now.isoformat(timespec="seconds")
                    b["auto_settled"] = True
                    count += 1
            if count:
                self.backend._save_ledger()
                self._emit(f"🧹 Force-settled {count} stale bet(s) as lost.")
                self._refresh_ledger()
            else:
                self._emit("🧹 No stale active bets found (all under 48 hours).")
        except Exception as e:
            self._emit(f"⚠️ Force-settle failed: {e}")

    def toggle_auto_scroll(self):
        self.auto_scroll_enabled = not self.auto_scroll_enabled

    def _toggle_roll_over(self):
        """Compact ROLL-OVER toggle (button next to MID POT). Flips the same
        variable the settings save/load path uses, so the top-bar chip and the
        button both reflect the mode."""
        try:
            self.roll_over_var.set(not self.roll_over_var.get())
        except Exception:
            pass

    def _toggle_show_all(self):
        """Tickbox: when off, only important lines (bets/wins/money/errors)
        show; when on, every line including research + crawl noise appears."""
        self._reseed_terminal()
        self._append_log("👁 Show-all view " +
                         ("ON" if self._show_all_var.get() else "OFF"))

    # ── Terminal zoom ─────────────────────────────────────────────────
    _TERM_FONT_MIN = 7
    _TERM_FONT_MAX = 26

    def _terminal_zoom_in(self):
        self._terminal_font_size = min(
            getattr(self, "_terminal_font_size", 10) + 1, self._TERM_FONT_MAX)
        self._apply_terminal_font()

    def _terminal_zoom_out(self):
        self._terminal_font_size = max(
            getattr(self, "_terminal_font_size", 10) - 1, self._TERM_FONT_MIN)
        self._apply_terminal_font()

    def _terminal_scroll_zoom(self, event):
        """Ctrl+scroll wheel zooms the terminal font size."""
        try:
            # Windows: event.delta is +/-120 per notch
            # Linux: event.num 4=up, 5=down
            if event.delta > 0 or getattr(event, "num", 0) == 4:
                self._terminal_zoom_in()
            else:
                self._terminal_zoom_out()
        except Exception:
            pass
        return "break"  # prevent default scroll

    def _apply_terminal_font(self):
        size = getattr(self, "_terminal_font_size", 10)
        if getattr(self, "terminal", None):
            try:
                self.terminal.config(font=("Consolas", size))
                # Keep bold tags in sync with new size
                for bold_tag in ("win", "loss", "bet", "longshot"):
                    self.terminal.tag_configure(bold_tag, font=("Consolas", size, "bold"))
                for normal_tag in ("warn", "fibi", "research", "money", "ok", "muted", "div"):
                    self.terminal.tag_configure(normal_tag, font=("Consolas", size))
            except Exception:
                pass

    def _clear_log(self):
        self._log_lines = []
        try:
            self.terminal.config(state="normal")
            self.terminal.delete("1.0", tk.END)
            self.terminal.config(state="disabled")
        except Exception:
            pass

    def _export_log(self):
        path = filedialog.asksaveasfilename(defaultextension=".txt",
                                            filetypes=[("Text", "*.txt")],
                                            initialfile="betflow_log.txt")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(self.terminal.get("1.0", tk.END))
            self._emit(f"📤 Log exported to {path}")
        except Exception as e:
            messagebox.showerror("Export", str(e))

    # ── Tag auto-detection rules ─────────────────────────────────────
    # Each rule is (pattern_to_check_in_text, tag_name).
    # First match wins.  Case-sensitive on emoji, insensitive on words.
    _LOG_TAG_RULES = [
        # Wins
        ("🏆", "win"), ("WON!", "win"), ("🎉", "win"),
        # Losses
        ("❌ LOST", "loss"), ("LOST Bet", "loss"),
        # Long-shot
        ("🎯 LONG-SHOT", "longshot"), ("🎯 DAILY LONG-SHOT", "longshot"),
        # Bets placed
        ("✅ SMART", "bet"), ("bet placed", "bet"), ("PLACING BET", "bet"),
        # Warnings / errors
        ("⚠️", "warn"), ("🚨", "warn"), ("ERROR", "warn"),
        # Fibi
        ("🌸 Fibi", "fibi"),
        # Research / analyst
        ("🧠 Analyst", "research"), ("🎯 Scout", "research"),
        ("🔬 Research", "research"), ("APEX:", "research"),
        ("📋 PLANNED", "research"), ("🔍 BetRecovery", "research"),
        # Money / balance
        ("💰", "money"), ("💵", "money"), ("KES ", "money"),
        ("💸", "money"), ("💹", "money"), ("Savings:", "money"),
        # OK / success
        ("✅ Logged", "ok"), ("✅ Session", "ok"), ("✅ Win-Sync", "ok"),
        # Muted / debug noise
        ("Crawl-and-bet attempt", "muted"), ("📅 Games (", "muted"),
        ("  •", "muted"), ("scroll", "muted"),
    ]

    # Messages that trigger a visual separator line before them
    _SEPARATOR_TRIGGERS = (
        "⏱️ Crawl-and-bet attempt",
        "🎯 DAILY LONG-SHOT",
        "🎯 LONG-SHOT",
        "FOOTBALL AUTO-BET:",
    )

    # "Show only important" filter — which lines are worth watching live.
    # Everything not listed here (or unclassified) still appears; only research
    # spam, crawl status lines and per-leg detail lines get hidden by default.
    _IMPORTANT_TAGS = frozenset({
        "win", "loss", "bet", "longshot", "warn", "money", "fibi", "ok",
    })
    _IMPORTANT_MARKERS = (
        "⚽ STARTING", "🛑 EMERGENCY", "Selected",
        "Thread crash", "thread crash", "🚨", "💥",
    )
    _NOISE_MARKERS = (
        "Crawl-and-bet attempt", "📅 Games (", "  •",
        "↗ ", "↖ DC:", "🔀 ", "🔎 Pre-flight skip", "Re-crawling shortly",
        "full-markets opener", "scroll", "│ ",
    )

    def _log_line_visible(self, raw: str, tag: str) -> bool:
        """Decide whether a log line should appear in the live terminal when the
        'Show all' checkbox is off. Classified lines (bets, wins, money, errors,
        cash-outs, balance) always show; research/crawl noise and per-leg detail
        are hidden until the user ticks 'Show all'."""
        if getattr(self, "_show_all_var", None) and self._show_all_var.get():
            return True
        if tag and tag in self._IMPORTANT_TAGS:
            return True
        if any(m in raw for m in self._IMPORTANT_MARKERS):
            return True
        if tag in ("research", "muted", "div"):
            return False
        if any(m in raw for m in self._NOISE_MARKERS):
            return False
        return True

    def _auto_tag(self, text: str) -> str:
        """Return the best colour tag for this log line, or empty string for default."""
        for pattern, tag in self._LOG_TAG_RULES:
            if pattern in text:
                return tag
        return ""

    def _append_log(self, text, tag=None):
        line = f"[{datetime.now().strftime('%H:%M:%S')}] {text}"
        self._log_lines.append(line)
        if len(self._log_lines) > 6000:
            del self._log_lines[: len(self._log_lines) - 6000]
        try:
            with open(TERMINAL_TEE_LOG, "a", encoding="utf-8", errors="replace") as _fh:
                _fh.write(line + "\n")
        except Exception:
            pass
        if not getattr(self, "terminal", None):
            return
        try:
            # Auto-detect tag from content if caller didn't specify one
            effective_tag = tag or self._auto_tag(text)

            # Feed the Fleet State round table from the same line the terminal
            # shows, so the two can never disagree about what happened.
            try:
                self._note_round_event(text, effective_tag)
            except Exception:
                pass

            # "Show only important" filter: skip noise lines until 'Show all' is on
            if not self._log_line_visible(text, effective_tag):
                return

            self.terminal.config(state="normal")

            # Insert a subtle separator line before new betting rounds
            if any(trigger in text for trigger in self._SEPARATOR_TRIGGERS):
                sep = "─" * 72 + "\n"
                self.terminal.insert(tk.END, sep, "div")

            self.terminal.insert(tk.END, line + "\n", effective_tag or "")

            if self.auto_scroll_enabled:
                self.terminal.see(tk.END)
            self.terminal.config(state="disabled")
            self._trim_log()
        except Exception:
            pass

    def _trim_log(self, limit=5000):
        try:
            if int(self.terminal.index("end-1c").split(".")[0]) > limit:
                self.terminal.config(state="normal")
                self.terminal.delete("1.0", f"{limit}.0")
                self.terminal.config(state="disabled")
        except Exception:
            pass

    def _sniff_balance(self, text):
        m = re.search(r"(?:Starting balance|Balance|balance[:\s]+KES)\s*[:=]?\s*KES\s*([\d,\.]+)",
                      text)
        if m:
            try:
                bal = float(m.group(1).replace(",", ""))
                self.state.balance = bal
                # Also push into engine_state.balances for the active phone so the
                # per-phone strip stays in sync even when the machine is idle.
                try:
                    es = getattr(self.backend, "_engine_state", {}) or {}
                    active = str(es.get("active_phone") or "")
                    if active:
                        es.setdefault("balances", {})[active] = bal
                except Exception:
                    pass
            except Exception:
                pass
            self._update_balance_label()

    # ── Start / Stop bet machine ──────────────────────────────────────
    def _read_params(self):
        def num(var, default):
            try:
                return float(var.get().strip() or default)
            except Exception:
                return default

        def integer(var, default):
            try:
                return int(float(var.get().strip() or default))
            except Exception:
                return default

        phones = self._phone_list()
        if not phones:
            messagebox.showerror("Missing Data", "Enter at least one phone number first.")
            return None
        phone = phones[0]
        if not self.password_var.get().strip():
            messagebox.showerror("Missing Data", "Enter the account password.")
            return None
        stake = max(10.0, num(self.stake_var, 10.0))
        cadence_min = max(0.25, num(self.cadence_var, 60.0))
        max_bets = integer(self.max_var, 0)
        daily = integer(self.daily_var, 0)
        pct = max(0.0, num(self.pct_var, 2.0))
        ls_legs = integer(self.ls_legs_var, 14)
        ls_min = max(3.0, num(self.ls_min_var, 15.0))
        ls_max = max(ls_min, num(self.ls_max_var, 60.0))
        withdraw = max(0.0, num(self.withdraw_var, 200.0))
        mk_on = [k for k, v in self.mk_vars.items() if v.get()]
        market_whitelist = "*" if len(mk_on) >= 4 else mk_on
        return {
            "phone": phone,
            "phones": phones,
            "password": self.password_var.get().strip(),
            "stake": stake,
            "cadence_seconds": max(20.0, cadence_min * 60.0),
            "max_bets": max_bets if max_bets > 0 else None,
            "daily_bets": daily if daily > 0 else None,
            "stake_percent": pct,
            "chain_bets": bool(self.chain_var.get()),
            "longshot": bool(self.longshot_var.get()) and ls_legs > 0,
            "longshot_odds_min": ls_min,
            "longshot_odds_max": ls_max,
            "longshot_legs": ls_legs,
            "longshot_odds_cap": 0,
            "auto_withdraw": withdraw > 0,
            "withdraw_amount": withdraw,
            "headless": bool(self.headless_var.get()),
            "market_whitelist": market_whitelist,
            "cashout_enabled": bool(self.cashout_var.get()),
            "cashout_threshold": max(0.1, min(1.0,
                                      float(str(self.cashout_pct_var.get()).strip() or 75) / 100.0)),
            "roll_over": bool(self.roll_over_var.get()),
        }

    def start_bet_machine(self):
        q = self._read_params()
        if q is None:
            return
        if self.state.worker_busy["bet"]:
            messagebox.showinfo("Already Running",
                                "The bet machine is already running. Emergency-stop it first.")
            return
        self._save_settings()
        self._stop_event = threading.Event()
        if self.backend is None or not self._backend_ready.is_set():
            messagebox.showwarning("Backend loading",
                                   "The backend is still loading — wait a moment, then try again.")
            return
        self.backend.running = True
        self.state.engine_state = "RUNNING"
        self.bus.emit("status", "RUNNING")
        ls_txt = (f"long-shot ON x{q['longshot_odds_min']:g}-x{q['longshot_odds_max']:g} "
                  f"{q['longshot_legs']}-leg/day | " if q.get("longshot") else "long-shot OFF | ")
        wd_txt = (f"auto-withdraw ON KES {q['withdraw_amount']:g}/day | "
                  if q.get("auto_withdraw") else "auto-withdraw OFF | ")
        hd_txt = "HEADLESS | " if q.get("headless") else ""
        ro_txt = "⚡ ROLL-OVER | " if q.get("roll_over") else ""
        pct_txt = f"{q['stake_percent']:g}%" if q["stake_percent"] else "OFF"
        daily_txt = "∞"
        if q.get("daily_bets"):
            db = int(q["daily_bets"])
            daily_txt = f"{db} (split 18:00 {(db + 1) // 2}+{db // 2})"
        self._append_log("⚽ STARTING Bet Machine | " +
                         f"stake KES {q['stake']:.0f} | " +
                         f"{'HUNGRY chained slips' if q['chain_bets'] else 'classic paced'} | " +
                         f"daily {daily_txt} | " +
                         f"bets {'∞' if not q['max_bets'] else q['max_bets']} | " +
                         f"stake% {pct_txt} | " +
                         ro_txt + hd_txt + ls_txt + wd_txt)

        def job():
            qq = q
            try:
                res = self.backend.run_football_bet_schedule(
                    qq["phone"], qq["password"], phones=qq.get("phones") or [qq["phone"]],
                    stake=qq["stake"],
                    cadence_seconds=qq["cadence_seconds"], max_bets=qq["max_bets"],
                    daily_bets=qq["daily_bets"], stake_percent=qq["stake_percent"],
                    chain_bets=qq["chain_bets"], gui_callback=self._emit,
                    stop_event=self._stop_event, visible=False,
                    longshot=qq.get("longshot", True),
                    longshot_odds_min=qq.get("longshot_odds_min", 15.0),
                    longshot_odds_max=qq.get("longshot_odds_max", 60.0),
                    longshot_odds_cap=qq.get("longshot_odds_cap", 0),
                    longshot_legs=qq.get("longshot_legs", 10),
                    auto_withdraw=qq.get("auto_withdraw", False),
                    withdraw_amount=qq.get("withdraw_amount", 200.0),
                    headless=True,
                    market_whitelist=qq.get("market_whitelist", "*"),
                    cashout_enabled=qq.get("cashout_enabled", True),
                    cashout_threshold=qq.get("cashout_threshold", 0.75),
                     grok_api_key=self._grok_cfg().get("grok_api_key") or None,
                     grok_model=self._grok_cfg().get("grok_model") or None,
                     grok_interval=self._grok_cfg().get("grok_interval") or 90.0,
                     agent_cfg=self._agent_cfg(),
                     roll_over=q.get("roll_over", False))
                if isinstance(res, dict) and res.get("deposit_needed"):
                    self.bus.emit("deposit", (res.get("deposit_needed", 0.0),
                                              res.get("balance", 0.0)))
            finally:
                try:
                    self._stop_event.clear()
                except Exception:
                    pass
                self.bus.emit("status", "IDLE")
                self.bus.emit("log", "⏹️ Bet machine stopped.")

        self.start_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        self._worker("bet", job)

    def emergency_stop(self):
        try:
            self.backend.running = False
        except Exception:
            pass
        try:
            if self._stop_event is not None:
                self._stop_event.set()
        except Exception:
            pass
        try:
            self.backend.force_stop_bet_driver()
        except Exception:
            pass
        self.state.engine_state = "STOPPED"
        self.bus.emit("status", "STOPPED")
        self._append_log("🛑 EMERGENCY STOP issued — killing bet browser and threads.")
        self.start_btn.config(state="normal")
        self.stop_btn.config(state="disabled")

    def _set_worker_button(self, name, busy):
        buttons = {"bet": self.start_btn, "balance": self.check_balance_btn,
                   "withdraw": self.withdraw_btn, "markets": self.markets_btn,
                   "deposit": self.deposit_btn, "jackpot": self.mega_btn,
                   "sync": self.sync_btn, "history": self.history_btn}
        btn = buttons.get(name)
        if btn is None:
            return
        btn.config(state="disabled" if busy else "normal")
        if name == "bet":
            self.stop_btn.config(state="normal" if busy else "disabled")

    # ── Balance check / withdraw ──────────────────────────────────────
    def start_balance_check(self):
        phones = self._phone_list()
        if not phones:
            messagebox.showerror("Missing Data", "Enter phone number(s) first.")
            return
        if not self.password_var.get().strip():
            messagebox.showerror("Missing Data", "Enter the password.")
            return
        if self.state.worker_busy["balance"]:
            messagebox.showinfo("Busy", "Balance check is already running.")
            return
        pw = self.password_var.get().strip()
        self._append_log(f"⚡ Balance check started for {len(phones)} account(s)...")

        def job():
            self.backend.running = True
            self.backend.check_balances(phones, pw, gui_callback=self._emit)
            # ── After balance check: push results into the engine's in-memory
            # cache so any running worker thread picks up the fresh balance
            # immediately without waiting for its next internal read.
            try:
                bc = self.backend._load_balance_cache() or {}
                if not hasattr(self.backend, '_balance_cache') or self.backend._balance_cache is None:
                    self.backend._balance_cache = {}
                for ph, entry in bc.items():
                    if entry.get("confirmed"):
                        self.backend._balance_cache[str(ph)] = entry
                        # Also update engine_state so the per-phone header updates
                        bal = float(entry.get("balance") or 0)
                        es = getattr(self.backend, "_engine_state", {})
                        es.setdefault("balances", {})[str(ph)] = bal
                        # If balance is enough to bet, signal the win_funded_wait
                        # loop to re-check immediately
                        self.backend._engine_state["_balance_refreshed"] = True
            except Exception:
                pass
            self._emit("✅ Balance check completed — engine will resume betting if funded.")

        self._worker("balance", job)

    def start_sync_winnings(self, auto: bool = False):
        """Sync bet history for all phones.

        *auto* = True means this is the silent startup sync — skips the busy
        guard so it always runs once at launch regardless of other workers.
        """
        phones = self._phone_list()
        if not phones:
            if not auto:
                messagebox.showerror("Missing Data", "Enter phone number(s) first.")
            return
        if not self.password_var.get().strip():
            if not auto:
                messagebox.showerror("Missing Data", "Enter the password.")
            return
        if self.state.worker_busy["sync"] and not auto:
            messagebox.showinfo("Busy", "A win-sync is already running.")
            return
        pw = self.password_var.get().strip()
        if not auto:
            self._append_log(f"🔄 Win-sync started for {len(phones)} account(s)...")

        def job():
            try:
                self.backend._load_ledger()
                # Count active bets before sync so we can report changes
                active_before = sum(
                    1 for b in (getattr(self.backend, "_bets", None) or [])
                    if b.get("status") == "active")
                for phone in phones:
                    self.backend.sync_winnings_now(phone, pw, gui_callback=self._emit)
                active_after = sum(
                    1 for b in (getattr(self.backend, "_bets", None) or [])
                    if b.get("status") == "active")
                settled = active_before - active_after
                if settled > 0:
                    self._emit(f"✅ Sync complete — {settled} bet(s) settled, "
                               f"{active_after} still active.")
                else:
                    self._emit(f"✅ Sync complete — {active_after} active bet(s), nothing changed.")
                self._refresh_ledger()
            except Exception as e:
                self._emit(f"⚠️ Win-sync error: {str(e)[:120]}")

        self._worker("sync", job)

    def _ask_deposit_phones(self, phones):
        """Modal picker — the human chooses WHICH account(s) get the STK push
        (e.g. first, second, or both) before any deposit fires."""
        phones = [p for p in (phones or []) if p]
        if len(phones) <= 1:
            return list(phones)
        result = {"sel": []}
        top = tk.Toplevel(self.root)
        top.title("Deposit to which number?")
        top.configure(bg=self.colors.get("bg", "#111418"))
        top.resizable(False, False)
        top.transient(self.root)
        top.grab_set()
        fg = self.colors.get("fg", "#e8e8e8")
        tk.Label(
            top,
            text="Choose account(s) to fund.\nApprove the STK push on your phone — "
                 "the machine bets as the money lands.",
            bg=self.colors.get("bg", "#111418"), fg=fg,
            justify="left").pack(padx=16, pady=(14, 8))
        vars_ = {}
        for ph in phones:
            vars_[ph] = tk.BooleanVar(value=True)
            tk.Checkbutton(
                top, text=ph, variable=vars_[ph],
                bg=self.colors.get("bg", "#111418"), fg=fg,
                selectcolor="#2a2f3a", anchor="w",
                highlightthickness=0).pack(anchor="w", padx=22)
        def _ok():
            result["sel"] = [ph for ph in phones if vars_[ph].get()]
            top.destroy()
        def _cancel():
            top.destroy()
        row = tk.Frame(top, bg=self.colors.get("bg", "#111418"))
        row.pack(pady=(10, 14))
        tk.Button(row, text="OK — Deposit", command=_ok,
                  bg="#29a34a", fg="white").pack(side="left", padx=6)
        tk.Button(row, text="Cancel", command=_cancel, bg="#465061", fg="white").pack(side="left", padx=6)
        self.root.wait_window(top)
        return result["sel"]

    def show_live_bet_history(self):
        """Fetch today's bets from SportPesa Bet History page for all phones."""
        phones = self._phone_list()
        if not phones:
            messagebox.showerror("Missing Data", "Enter phone number(s) first.")
            return
        if not self.password_var.get().strip():
            messagebox.showerror("Missing Data", "Enter the password.")
            return
        if self.state.worker_busy["history"]:
            messagebox.showinfo("Busy", "History fetch already running.")
            return
        pw = self.password_var.get().strip()
        self._append_log(f"📋 Fetching live bet history for {len(phones)} account(s)...")

        def job():
            for phone in phones:
                try:
                    self.backend.fetch_bet_history_live(
                        phone, pw, gui_callback=self._emit)
                except Exception as e:
                    self._emit(f"⚠️ History fetch error ({phone}): {str(e)[:80]}")
            self._emit("✅ Live history fetch done.")
            self._refresh_ledger()

        self._worker("history", job)

    def start_deposit_flow(self):
        """Fill the SportPesa deposit page so the M-Pesa STK pops on your phone."""
        phones = self._phone_list()
        if not phones:
            messagebox.showerror("Missing Data", "Enter phone number(s) first.")
            return
        if not self.password_var.get().strip():
            messagebox.showerror("Missing Data", "Enter the password.")
            return
        if self.state.worker_busy["deposit"]:
            messagebox.showinfo("Busy", "A deposit is already being sent.")
            return
        try:
            amount = max(1.0, float(self.deposit_var.get().strip() or "99"))
        except ValueError:
            amount = 99.0
        pw = self.password_var.get().strip()
        phones = self._ask_deposit_phones(phones)
        if not phones:
            self._append_log("🚫 Deposit cancelled — no account selected.")
            return
        self._append_log(f"💵 Deposit request: KES {amount:,.2f} each → {', '.join(phones)} "
                         "(M-Pesa — one STK push per account; approve each on your phone; "
                         "the machine bets as funds land).")

        def job():
            self.backend.running = True
            self.backend.deposit_funds_multi(phones, pw, amount, gui_callback=self._emit)
            self._emit("✅ Deposit flow done — machine will auto-bet the planned slips when funds arrive.")

        self._worker("deposit", job)

    def start_withdraw_flow(self):
        phones = self._phone_list()
        if not phones:
            messagebox.showerror("Missing Data", "Enter phone number(s) first.")
            return
        if not self.password_var.get().strip():
            messagebox.showerror("Missing Data", "Enter the password.")
            return
        if self.state.worker_busy["withdraw"]:
            messagebox.showinfo("Busy", "A withdrawal is already running.")
            return
        amount = self._ask_amount(len(phones))
        if not amount:
            return
        pw = self.password_var.get().strip()
        self._append_log(f"💸 Withdraw request: {len(phones)} accounts x KES {amount:,.2f}")

        def job():
            self.backend.running = True
            self.backend.withdraw_funds_browser(phones, pw, amount, gui_callback=self._emit)
            self._emit("✅ Withdrawal process completed.")

        self._worker("withdraw", job)

    def _ask_amount(self, count):
        c = self.colors
        dlg = tk.Toplevel(self.root)
        dlg.title("Withdraw Funds")
        dlg.configure(bg=c["panel"])
        dlg.resizable(False, False)
        dlg.transient(self.root)
        dlg.grab_set()
        f = tk.Frame(dlg, bg=c["panel"], padx=24, pady=20)
        f.pack(fill="both", expand=True)
        tk.Label(f, text=f"Withdraw from {count} account(s)",
                 bg=c["panel"], fg=c["fg"], font=("Segoe UI", 11, "bold")).pack(pady=(0, 12))
        row = tk.Frame(f, bg=c["panel"])
        row.pack(pady=(0, 12))
        tk.Label(row, text="Amount (KES):", bg=c["panel"], fg=c["fg"],
                 font=("Segoe UI", 10)).pack(side="left", padx=(0, 8))
        amount_var = tk.StringVar(value="100")
        ent = tk.Entry(row, textvariable=amount_var, width=12, bg=c["text_bg"],
                       fg=c["text_fg"], justify="center", relief=tk.FLAT,
                       highlightthickness=1, highlightbackground=c["border"],
                       font=("Consolas", 14))
        ent.pack(side="left", ipady=4)
        ent.select_range(0, tk.END)
        ent.focus_set()
        result = {"v": None}

        def on_go():
            raw = amount_var.get().strip()
            if not raw.replace(".", "").isdigit() or not raw:
                messagebox.showerror("Invalid", "Enter a valid amount", parent=dlg)
                return
            result["v"] = float(raw)
            dlg.destroy()

        btns = tk.Frame(f, bg=c["panel"])
        btns.pack()
        tk.Button(btns, text="Cancel", command=dlg.destroy, relief=tk.FLAT, cursor="hand2",
                  bg=c["muted"], fg="white", padx=16, pady=6,
                  font=("Segoe UI", 9)).pack(side="left", padx=4)
        tk.Button(btns, text="WITHDRAW", command=on_go, relief=tk.FLAT, cursor="hand2",
                  bg=c["accent"], fg="#201800", padx=16, pady=6,
                  font=("Segoe UI", 9, "bold")).pack(side="left", padx=4)
        dlg.bind("<Return>", lambda e: on_go())
        self.root.wait_window(dlg)
        return result["v"]

    # ── Jackpot (MEGA POT / MID POT) ─────────────────────────────────
    def start_mega_pot(self):
        self._start_jackpot_flow("mega")

    def start_mid_pot(self):
        self._start_jackpot_flow("mid")

    def show_form_cache(self):
        """Print the cached team-form entries gathered via the H2H stats overlay."""
        try:
            cache = self.backend._load_form_cache()
            if not cache:
                self._emit("📈 Form cache is empty — it fills as the machine analyses "
                           "the jackpot pool (search-box lookups).")
                return
            rows = []
            for key, e in sorted(cache.items()):
                n = int(e.get("n") or 0)
                rows.append(f"{key}: {'-'.join(str(c) for c in (e.get('results') or '')[-n:])} "
                            f"({n} games, {int(time.time() - (e.get('ts') or 0))//3600}h old)")
            self._emit(f"📈 Form cache: {len(rows)} team(s)")
            for r in rows:
                self._emit("   " + r)
        except Exception as e:
            self._emit(f"⚠️ Form cache view failed: {str(e)[:80]}")

    def _start_jackpot_flow(self, pool_key):
        label = "MEGA" if pool_key == "mega" else "MIDWEEK"
        emoji = "🎰" if pool_key == "mega" else "🀄"
        phones = self._phone_list()
        if not phones:
            messagebox.showerror("Missing Data", "Enter phone number(s) first.")
            return
        if not self.password_var.get().strip():
            messagebox.showerror("Missing Data", "Enter the password.")
            return
        if self.state.worker_busy["jackpot"]:
            messagebox.showinfo("Busy", "A jackpot flow is already running.")
            return
        try:
            stake = max(1.0, min(999.0, float(self.jackpot_stake_var.get().strip() or "99")))
        except ValueError:
            stake = 99.0
        pw = self.password_var.get().strip()
        self._append_log(f"{emoji} {label} JACKPOT requested — KES {stake:,.0f} entry. "
                         f"Trying {len(phones)} account(s)...")

        def job():
            self.backend.running = True
            for phone in phones:
                self._emit(f"Trying account {phone}...")
                res = self.backend.run_jackpot_button(phone, pw, pool_key=pool_key,
                                                      stake=stake, gui_callback=self._emit)
                if isinstance(res, dict):
                    if res.get("status") == "ok":
                        self._emit(f"✅ Placed on {phone}!")
                        return
                    elif res.get("status") == "no_funds":
                        self._emit(f"💵 {phone} has insufficient funds — trying next account...")
                        continue
                    elif res.get("status") in ("bail", "error"):
                        continue
            self._emit("❌ No accounts had sufficient funds for the jackpot entry.")

        self._worker("jackpot", job)

    # ── Markets explorer ──────────────────────────────────────────────
    def view_all_markets(self):
        phones = self._phone_list()
        if not phones:
            messagebox.showerror("Missing Data", "Enter a phone number first.")
            return
        if not self.password_var.get().strip():
            messagebox.showerror("Missing Data", "Enter the password.")
            return
        if self.state.worker_busy["markets"]:
            messagebox.showinfo("Busy", "Already opening the markets browser.")
            return
        phone = phones[0]
        pw = self.password_var.get().strip()
        gid = self.allmkt_gid_var.get().strip() or None
        machine_running = self.state.worker_busy["bet"]

        def job():
            owned = False
            driver = getattr(self.backend, "_bet_driver", None)
            try:
                if driver is None:
                    self._emit("🌐 Opening a browser to view all markets (closes when done)...")
                    driver = self.backend._build_driver(gui_callback=self._emit,
                                                        force_visible=True, mobile=False)
                    owned = True
                self.backend._ensure_bet_login(driver, phone, pw, gui_callback=self._emit)
                self.backend._dismiss_visible_promos(driver, rounds=1)
                res = self.backend._open_game_full_markets(driver, gid=gid,
                                                           gui_callback=self._emit)
                self._emit(f"📋 GAME MARKETS ({res.get('url', '')[:90]})")
                lines = self.backend._dump_full_markets_text(res.get("markets") or [],
                                                             max_markets=60)
                for ln in lines:
                    self._emit("   " + ln)
                self._emit(f"📋 Total markets found: {len(res.get('markets') or [])}")
                if not machine_running:
                    self.backend._safe_get(driver, self.backend.TODAY_GAMES_PAGE_URL)
            except Exception as e:
                self._emit(f"⚠️ All Markets failed: {str(e)[:120]}")
            finally:
                if owned and driver is not None:
                    try:
                        driver.quit()
                    except Exception:
                        pass

        self._worker("markets", job)

    # ── Ledger ────────────────────────────────────────────────────────
    def _refresh_ledger(self):
        try:
            self.backend._load_ledger()
            s = self.backend._ledger_summary()
            self.state.ledger = dict(s)
            for item in self.ledger_tree.get_children():
                self.ledger_tree.delete(item)
            bets = getattr(self.backend, "_bets", [])
            for b in bets:
                tag = "active"
                st = str(b.get("status") or "")
                if st == "won":
                    tag = "won"
                elif st == "lost":
                    tag = "lost"
                markets = ",".join(list(b.get("markets") or [])[:5]) or "—"
                rec = b.get("recipe") or {}
                recipe = f"{rec.get('legs','?')}L@{rec.get('band','-')}/{rec.get('lead','-')}"
                ph = (b.get("phone") or "—")
                self.ledger_tree.insert("", "end", values=(
                    b.get("id") or "—", b.get("placed_at", "")[:16], ph,
                    st or "active", b.get("stake") or "", b.get("odds") or "",
                    b.get("won_amount") or "", markets, recipe), tags=(tag,))
            net = s.get("net_profit", 0.0)
            arrow = "▲" if net >= 0 else "▼"
            per = s.get("per_phone") or {}
            per_txt = ""
            if len(per) > 1:
                parts = []
                for p, ps in sorted(per.items()):
                    a2 = "▲" if ps.get("net_profit", 0) >= 0 else "▼"
                    parts.append(f"{p[-4:]}: {ps.get('won',0)}W/{ps.get('lost',0)}L "
                                 f"{a2}{abs(ps.get('net_profit',0)):,.0f}")
                per_txt = " | " + " · ".join(parts)
            self.winnings_label.config(
                text=f"📊 {s.get('placed',0)} bets | won {s.get('won',0)} "
                     f"(+KES {s.get('won_return',0):,.2f}) | lost {s.get('lost',0)} | "
                     f"active {s.get('active',0)} | net {arrow} KES {abs(net):,.2f}{per_txt}")
            self.ledger_hint.config(text=f"{len(bets)} tracked bet(s)")
        except Exception:
            pass

    def _export_ledger_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv",
                                            filetypes=[("CSV", "*.csv")],
                                            initialfile="betflow_ledger.csv")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8", newline="") as f:
                rows = getattr(self.backend, "_bets", [])
                fieldnames = ["id", "placed_at", "phone", "status", "stake", "odds",
                              "possible_win", "won_amount", "settled_at",
                              "markets", "recipe"]
                w = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
                w.writeheader()
                for r in rows:
                    w.writerow(r)
            self._emit(f"💾 Ledger exported to {path}")
        except Exception as e:
            messagebox.showerror("Export", str(e))

    # ── Learning ──────────────────────────────────────────────────────
    def _refresh_learning(self):
        try:
            self.backend._load_stats()
            st = self.backend._stats
            for tree in (self.learning_tree, self.recipe_tree):
                for item in tree.get_children():
                    tree.delete(item)
            # ── Market types ────────────────────────────────────────────
            mt = st.get("market_types") or {}
            for mk, e in sorted(mt.items()):
                trials = int(e.get("trials") or 0)
                won_raw = float(e.get("won") or 0)  # may be fractional from blame-weighting
                won_disp = f"{won_raw:.1f}" if won_raw != int(won_raw) else str(int(won_raw))
                hit = (won_raw / trials) if trials else 0.0
                pred = ((e.get("expected") or 0.0) / trials) if trials else 0.0
                deficit = pred - hit
                tag = "retired" if mk in (st.get("retired_markets") or []) else (
                    "boosted" if float(e.get("weight") or 1.0) > 1.0 else "")
                status = ("RETIRED" if mk in (st.get("retired_markets") or [])
                          else f"boost x{e.get('weight',1.0):g}" if float(e.get("weight") or 1.0) > 1.0
                          else "neutral")
                self.learning_tree.insert("", "end", values=(
                    mk, trials, won_disp, f"{hit:.1%}", f"{pred:.1%}",
                    f"{deficit:+.1%}", e.get("weight", 1.0), status), tags=(tag,))
            # ── Recipes ─────────────────────────────────────────────────
            recipes = st.get("recipes") or {}
            for key, r in sorted(recipes.items()):
                trials = int(r.get("trials") or 0)
                won = int(r.get("won") or 0)
                staked = float(r.get("stake") or 0)
                ret = float(r.get("ret") or 0)
                roi = ((ret - staked) / staked) if staked else 0.0
                self.recipe_tree.insert("", "end", values=(
                    key, trials, won, f"{roi:+.1%}", ""))
            # ── Analyst accuracy ─────────────────────────────────────────
            analyst_tree = getattr(self, "analyst_tree", None)
            if analyst_tree is not None:
                for item in analyst_tree.get_children():
                    analyst_tree.delete(item)
                try:
                    cache = self.backend._agent_hub.cache if self.backend._agent_hub else None
                    acc = cache.analyst_accuracy_summary() if cache else {}
                except Exception:
                    acc = {}
                # Also pull from stats if available
                if not acc:
                    acc = st.get("analyst_calibration") or {}
                for bucket, e in sorted(acc.items()):
                    n = int(e.get("n") or 0)
                    wins = int(e.get("wins") or 0)
                    if n == 0:
                        continue
                    rate = wins / n
                    conf_f = float(bucket)
                    # Verdict: is actual win-rate tracking with stated confidence?
                    if rate >= conf_f - 0.05:
                        verdict = "✅ Calibrated"
                        tag = "good"
                    elif rate >= conf_f * 0.7:
                        verdict = "⚠️ Slightly overconfident"
                        tag = ""
                    else:
                        verdict = f"❌ Overconfident ({conf_f:.0%} stated vs {rate:.0%} actual)"
                        tag = "poor"
                    analyst_tree.insert("", "end", values=(
                        f"{conf_f:.0%}", n, wins, f"{rate:.0%}", verdict), tags=(tag,))

            settled = int(st.get("settled") or 0)
            bandit = "ACTIVE" if settled >= 30 else f"learning ({settled}/30 settled)"
            self.learning_summary.config(
                text=f"settled {settled} | retired "
                     f"{len(st.get('retired_markets') or [])} | bandit {bandit}")
        except Exception:
            pass

    # ── Status / theme ────────────────────────────────────────────────
    def _update_status_chip(self):
        c = self.colors
        s = self.state.engine_state
        color = {"RUNNING": c["ok"], "IDLE": c["muted"],
                 "STOPPED": c["err"]}.get(s, c["muted"])
        self.status_chip.config(text=f"● {s}", fg=color)

    def _update_balance_label(self):
        c = self.colors
        try:
            if self.state.balance is None:
                self.balance_label.config(text="Balance: —")
            else:
                self.balance_label.config(
                    text=f"Balance: KES {self.state.balance:,.2f}")
        except Exception:
            pass
        # Per-phone strip: rate-limited to once per 3 s to avoid hammering
        # Tkinter widget updates at log-parsing speed.
        now = time.time()
        if now - getattr(self, "_last_per_phone_refresh", 0.0) > 3.0:
            self._last_per_phone_refresh = now
            self._update_per_phone_balances()

    def _update_per_phone_balances(self):
        """Refresh the per-account balance labels in the header strip.

        Reads from _engine_state['balances'] which is a {phone: balance} dict
        the engine updates every round.  Shows nothing when there is only one
        account (the main balance label already covers that case) or when the
        engine isn't running yet.
        """
        c = self.colors
        try:
            es = getattr(self.backend, "_engine_state", {}) or {}
            balances = dict(es.get("balances") or {})
            active_phone = str(es.get("active_phone") or "")
            phones = list(es.get("phones") or [])

            ppf = getattr(self, "per_phone_frame", None)
            if ppf is None:
                return

            # Only show the strip when there are at least 2 phones
            if len(phones) < 2 or not balances:
                # Hide all existing labels
                for lbl in getattr(self, "_per_phone_labels", {}).values():
                    try:
                        lbl.pack_forget()
                    except Exception:
                        pass
                self._per_phone_labels = {}
                return

            existing = getattr(self, "_per_phone_labels", {})
            shown = set()
            for phone in phones:
                bal = balances.get(phone)
                if bal is None:
                    continue
                # Last 4 digits as a short identifier
                short = str(phone)[-4:]
                is_active = (phone == active_phone)
                text = f"{'▶' if is_active else ' '}{short}: KES {bal:,.0f}"
                fg = c["ok"] if is_active else c["muted"]
                if phone not in existing:
                    lbl = tk.Label(ppf, text=text, bg=c["panel"], fg=fg,
                                   font=("Consolas", 9))
                    lbl.pack(side="left", padx=(0, 8))
                    existing[phone] = lbl
                else:
                    existing[phone].config(text=text, fg=fg)
                shown.add(phone)

            # Remove labels for phones no longer in the list
            for phone in list(existing.keys()):
                if phone not in shown:
                    try:
                        existing[phone].destroy()
                    except Exception:
                        pass
                    del existing[phone]

            self._per_phone_labels = existing
        except Exception:
            pass

    def toggle_theme(self):
        self.theme_name = "light" if self.theme_name == "dark" else "dark"
        self.colors = dict(DARK if self.theme_name == "dark" else LIGHT)
        snap = self._snapshot_vars()
        try:
            scroll_enabled = bool(getattr(self, "auto_scroll_enabled", True))
        except Exception:
            scroll_enabled = True
        self.root.configure(bg=self.colors["bg"])
        self._rebuild_theme()
        self._restore_vars(snap)
        self.auto_scroll_enabled = scroll_enabled
        self._reseed_terminal()
        self._update_status_chip()
        self._update_balance_label()
        for name, busy in self.state.worker_busy.items():
            try:
                self._set_worker_button(name, busy)
            except Exception:
                pass

    def _snapshot_vars(self):
        snap = {}
        for a in dir(self):
            if a.endswith("_var"):
                try:
                    v = getattr(self, a)
                    if isinstance(v, (tk.Variable, tk.BooleanVar, tk.StringVar,
                                      tk.DoubleVar, tk.IntVar)):
                        snap[a] = v.get()
                except Exception:
                    pass
        return snap

    def _restore_vars(self, snap):
        for a, val in (snap or {}).items():
            try:
                v = getattr(self, a)
                if isinstance(v, tk.Variable):
                    v.set(val)
            except Exception:
                pass

    def _reseed_terminal(self):
        if not getattr(self, "terminal", None):
            return
        try:
            self.terminal.config(state="normal")
            self.terminal.delete("1.0", tk.END)
            if self._log_lines:
                for line in self._log_lines:
                    # Strip the timestamp prefix to get the raw message for tag detection
                    raw = re.sub(r"^\[\d{2}:\d{2}:\d{2}\] ", "", line)
                    tag = self._auto_tag(raw)
                    if not self._log_line_visible(raw, tag):
                        continue
                    if any(trigger in raw for trigger in self._SEPARATOR_TRIGGERS):
                        self.terminal.insert(tk.END, "─" * 72 + "\n", "div")
                    self.terminal.insert(tk.END, line + "\n", tag or "")
            if self.auto_scroll_enabled:
                self.terminal.see(tk.END)
            self.terminal.config(state="disabled")
            self._trim_log()
        except Exception:
            pass

    def _rebuild_theme(self):
        old_nb = getattr(self, "nb", None)
        for child in self.root.winfo_children():
            if child is not old_nb:
                child.destroy()
        if old_nb is not None:
            try:
                old_nb.destroy()
            except Exception:
                pass
        self._build_ui()
        self._load_settings()

    # ── Settings persistence ──────────────────────────────────────────
    def _settings_path(self):
        return writable_path("sportsape_settings.json")

    def _grok_cfg(self):
        try:
            with open(self._settings_path(), "r", encoding="utf-8") as f:
                d = json.load(f)
        except Exception:
            d = {}
        return {
            "grok_api_key": str(d.get("grok_api_key") or "").strip(),
            "grok_model": str(d.get("grok_model") or "").strip(),
            "grok_interval": float(d.get("grok_interval") or 90.0),
        }

    def _agent_cfg(self):
        try:
            with open(self._settings_path(), "r", encoding="utf-8") as f:
                d = json.load(f)
        except Exception:
            d = {}
        return {
            "agents_enabled":      bool(d.get("agents_enabled", True)),
            "alerts_enabled":      bool(d.get("alerts_enabled", False)),
            "alert_provider":      str(d.get("alert_provider") or "").strip(),
            "twilio_sid":          str(d.get("twilio_sid") or "").strip(),
            "twilio_auth":         str(d.get("twilio_auth") or "").strip(),
            "twilio_from":         str(d.get("twilio_from") or "").strip(),
            "alert_phone":         str(d.get("alert_phone") or "").strip(),
            "webhook_url":         str(d.get("webhook_url") or "").strip(),
            "webhook_token":       str(d.get("webhook_token") or "").strip(),
            "api_football_key":    str(d.get("api_football_key") or "").strip(),
            "api_football_keys":   [str(k).strip() for k in (d.get("api_football_keys") or [])
                                    if str(k or "").strip()],
            # All AI keys for rotation (Grok + Gemini)
            "ai_keys":             [str(k).strip() for k in (d.get("ai_keys") or [])
                                    if str(k or "").strip()],
            # Per-hour cap on AI calls (spend guard for paid keys)
            "ai_calls_per_hour":   int(d.get("ai_calls_per_hour") or 0),
            # JEV (tokenra.io) — fast typed-decision leg validator
            "jev_api_key":         str(d.get("jev_api_key") or "").strip(),
            "jev_weight":          float(d.get("jev_weight") or 0.35),
        }

    def _load_settings(self):
        try:
            with open(self._settings_path(), "r", encoding="utf-8") as f:
                data = json.load(f)
            self.stake_var.set(str(data.get("stake", 10)))
            self.cadence_var.set(str(data.get("cadence_minutes",
                                              (data.get("cadence_seconds", 3600) or 3600) / 60.0)))
            self.max_var.set(str(data.get("max_bets", 0)))
            self.daily_var.set(str(data.get("daily_bets", 20)))
            self.pct_var.set(str(data.get("stake_percent", 0)))
            self.chain_var.set(bool(data.get("chain_bets", True)))
            self.longshot_var.set(bool(data.get("longshot", True)))
            self.ls_legs_var.set(str(data.get("longshot_legs", 14)))
            self.ls_min_var.set(str(data.get("longshot_odds_min", 15)))
            self.ls_max_var.set(str(data.get("longshot_odds_max", 60)))
            self.withdraw_var.set(str(data.get("withdraw_amount", 200)))
            self.deposit_var.set(str(data.get("deposit_default", 99)))
            self.headless_var.set(bool(data.get("headless", True)))
            self.autostart_var.set(bool(data.get("autostart", False)))
            self.notify_var.set(bool(data.get("notify", True)))
            try:
                self.cashout_var.set(bool(data.get("cashout_enabled", True)))
                self.cashout_pct_var.set(str(int(round(float(data.get("cashout_threshold", 0.75)) * 100))))
            except Exception:
                pass
            try:
                self.jackpot_stake_var.set(str(data.get("jackpot_stake", 99)))
            except Exception:
                pass
            try:
                _mk = data.get("markets") or {}
                self.mk_vars["1x2"].set(bool(_mk.get("1x2", True)))
                self.mk_vars["btts"].set(bool(_mk.get("btts", True)))
                self.mk_vars["ou25"].set(bool(_mk.get("ou25", True)))
                self.mk_vars["ou15"].set(bool(_mk.get("ou15", True)))
            except Exception:
                pass
            # Load lock-in state and auto-populate phones/password if locked
            _locked = bool(data.get("lock_in", False))
            try:
                self.lock_in_var.set(_locked)
                c = self.colors
                self.lock_in_btn.config(fg=c["ok"] if _locked else c["fg"])
            except Exception:
                pass
            if _locked:
                # Auto-populate phones and password from locked values
                locked_phones = data.get("phones_locked") or data.get("phones") or []
                locked_pw     = data.get("password_locked") or data.get("password") or ""
                if locked_phones:
                    try:
                        self.phone_text.delete("1.0", tk.END)
                        self.phone_text.insert("1.0", "\n".join(str(p) for p in locked_phones))
                    except Exception:
                        pass
                if locked_pw:
                    self.password_var.set(locked_pw)
            else:
                # Not locked — only load password, leave phones blank for security
                if data.get("password"):
                    self.password_var.set(str(data["password"]))
        except Exception:
            pass
        if self.autostart_var.get():
            self.root.after(1200, self._safe_autostart)

    def _save_settings(self):
        try:
            cadence_min = max(0.25, float(self.cadence_var.get().strip() or "60"))
            team = self._phone_list()
            data = {
                "phone": team[0] if team else "",
                "phones": team,
                "password": self.password_var.get().strip(),
                "cadence_minutes": cadence_min,
                "cadence_seconds": cadence_min * 60.0,
                "stake": float(self.stake_var.get().strip() or 10),
                "max_bets": int(float(self.max_var.get().strip() or 0)),
                "daily_bets": int(float(self.daily_var.get().strip() or 20)),
                "stake_percent": float(self.pct_var.get().strip() or 0),
                "chain_bets": bool(self.chain_var.get()),
                "longshot": bool(self.longshot_var.get()),
                "longshot_legs": int(float(self.ls_legs_var.get().strip() or 14)),
                "longshot_odds_min": float(self.ls_min_var.get().strip() or 15),
                "longshot_odds_max": float(self.ls_max_var.get().strip() or 60),
                "withdraw_amount": float(self.withdraw_var.get().strip() or 200),
                "deposit_default": float(self.deposit_var.get().strip() or 99),
                "headless": bool(self.headless_var.get()),
                "autostart": bool(self.autostart_var.get()),
                "notify": bool(self.notify_var.get()),
                "jackpot_stake": float(self.jackpot_stake_var.get().strip() or 99),
                "cashout_enabled": bool(self.cashout_var.get()),
                "cashout_threshold": max(0.1, min(1.0,
                     float(str(self.cashout_pct_var.get()).strip() or 75) / 100.0)),
                "markets": {k: bool(v.get()) for k, v in self.mk_vars.items()},
                # Lock-in state
                "lock_in": bool(getattr(self, "lock_in_var", tk.BooleanVar()).get()),
                "phones_locked": team if bool(getattr(self, "lock_in_var", tk.BooleanVar()).get()) else [],
                "password_locked": self.password_var.get().strip() if bool(getattr(self, "lock_in_var", tk.BooleanVar()).get()) else "",
            }
            gc = self._grok_cfg()
            data["grok_api_key"] = gc["grok_api_key"]
            data["grok_model"] = gc["grok_model"]
            data["grok_interval"] = gc["grok_interval"]
            # Preserve AI-key rotation + JEV fields that live in the file but
            # have no dedicated widgets (never clobber them on save).
            try:
                with open(self._settings_path(), "r", encoding="utf-8") as f:
                    prev = json.load(f)
                if prev.get("ai_keys"):
                    data["ai_keys"] = prev["ai_keys"]
                if "ai_calls_per_hour" in prev:
                    data["ai_calls_per_hour"] = int(prev["ai_calls_per_hour"] or 0)
                if prev.get("jev_api_key"):
                    data["jev_api_key"] = str(prev["jev_api_key"]).strip()
                if prev.get("jev_weight"):
                    data["jev_weight"] = float(prev["jev_weight"])
                for k in ("api_football_key", "api_football_keys",
                          "twilio_sid", "twilio_auth", "twilio_from",
                          "alert_phone", "webhook_url", "webhook_token",
                          "alert_provider", "agents_enabled", "alerts_enabled"):
                    if k in prev:
                        data[k] = prev[k]
            except Exception:
                pass
            with open(self._settings_path(), "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
        except Exception:
            pass

    def _safe_autostart(self):
        try:
            if not self.state.worker_busy["bet"]:
                self.start_bet_machine()
        except Exception:
            pass

    def _on_close(self):
        if not messagebox.askyesno("Confirm exit",
                                   "Are you sure you want to close the tool?\n\n"
                                   "The bet machine and any browser sessions will be shut down."):
            return
        try:
            self.backend.running = False
            if self._stop_event is not None:
                self._stop_event.set()
        except Exception:
            pass
        try:
            self.backend.force_stop_bet_driver()
        except Exception:
            pass
        try:
            closed = self.backend.shutdown_all_browsers()
            if closed:
                print(f"[exit] Quit {closed} tool browser session(s)")
        except Exception:
            pass
        try:
            self._save_settings()
        except Exception:
            pass
        # ── Exit cleanup: remove balance report files, pyc cache, and log files
        # that are no longer needed.  Runs synchronously (fast — just file deletes).
        try:
            from sportsape_agents import BalanceReportCleaner
            import os as _os
            base = _os.path.dirname(_os.path.abspath(__file__))
            c = BalanceReportCleaner(max_age_days=0.0, search_dir=base)
            c._last_run = 0.0  # force run immediately
            result = c.run(gui_callback=None)
            freed_kb = round(result.get("freed_bytes", 0) / 1024, 1)
            if freed_kb > 0:
                print(f"[exit] Cleaned {result.get('deleted',0)} file(s), freed {freed_kb} KB")
        except Exception:
            pass
        self.root.destroy()


def main():
    # Set the AppUserModelID BEFORE creating the Tk window — this is what
    # Windows uses to group taskbar buttons and associate the .ico with the
    # process. It must be set before the first HWND is created.
    set_windows_app_id(f"BetFlowPro.{APP_VERSION}")

    # Also set it via the older ctypes path that some Windows versions need
    if sys.platform == "win32" and _HAS_CTYPES:
        try:
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
                f"BetFlowPro.{APP_VERSION}")
        except Exception:
            pass

    root = tk.Tk()
    # Withdraw before building UI so the window is never shown with the
    # default Tk feather icon — it only becomes visible after the icon is set.
    root.withdraw()
    _install_crash_harness(root)
    app = BetFlowProGUI(root)
    # Show the window after a short delay so _set_app_icon's after(200,...) has
    # already been scheduled and will fire while the window is visible.
    root.after(10, root.deiconify)
    root.mainloop()


if __name__ == "__main__":
    main()
