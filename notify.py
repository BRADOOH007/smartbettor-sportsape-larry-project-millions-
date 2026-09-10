"""Sound + desktop toast alerts for BetFlow Pro.

Pure standard library: winsound (Windows built-in) for beeps and a tiny
tkinter Toplevel for the auto-hiding toast. No new dependencies.
"""
import sys
import threading
import tkinter as tk

_ACTIVE_TOAST = {"win": None}


def sound(kind: str) -> None:
    """Play a short non-blocking beep pattern for an event kind."""
    if sys.platform != "win32":
        return
    patterns = {
        "placed":    ((880, 90), (660, 90)),
        "won":       ((880, 130), (1109, 140), (1319, 260)),
        "lost":      ((330, 220),),
        "warn":      ((520, 160), (520, 160)),
        "funds":     ((784, 110), (1047, 190)),
        "withdraw":  ((1047, 110), (784, 110), (1047, 220)),
        "planned":   ((1047, 90),),
    }
    pat = patterns.get(kind)
    if not pat:
        return

    def _play():
        try:
            import winsound
            for i, (freq, dur) in enumerate(pat):
                winsound.Beep(freq, dur)
                if i < len(pat) - 1:
                    threading.Event().wait(0.05)
        except Exception:
            pass

    threading.Thread(target=_play, daemon=True).start()


def toast(title: str, msg: str, ms: int = 5000) -> None:
    """Pop a bottom-right, always-on-top toast that auto-disappears."""
    try:
        prev = _ACTIVE_TOAST.get("win")
        if prev is not None:
            try:
                prev.destroy()
            except Exception:
                pass
        root = tk._default_root
        if root is None:
            try:
                import main_gui
            except Exception:
                return
            if not tk._default_root:
                return
            root = tk._default_root
        win = tk.Toplevel(root)
        _ACTIVE_TOAST["win"] = win
        win.overrideredirect(True)
        try:
            win.wm_attributes("-topmost", True)
        except Exception:
            pass
        try:
            win.wm_attributes("-alpha", 0.96)
        except Exception:
            pass

        colors = {
            "won":      ("#0f2a18", "#2ecc71"),
            "placed":   ("#101820", "#4db8ff"),
            "lost":     ("#2a1414", "#ff5252"),
            "warn":     ("#2a2210", "#ffb400"),
            "funds":    ("#13202e", "#66ccff"),
            "withdraw": ("#231c2e", "#b18cff"),
            "planned":  ("#1a1f18", "#8fe388"),
            "info":     ("#171c21", "#e6ecf2"),
        }
        bg, accent = colors.get("info")
        for k, (cb, ca) in colors.items():
            if k in (title or "").lower():
                bg, accent = cb, ca
                break

        sw = win.winfo_screenwidth()
        sh = win.winfo_screenheight()
        pad, w = 14, 360
        h = 96
        win.geometry(f"{w}x{h}+{sw - w - pad}+{sh - h - pad - 8}")

        pad_frame = tk.Frame(win, bg=accent)
        pad_frame.pack(fill="both", expand=True)
        body = tk.Frame(pad_frame, bg=bg)
        body.pack(fill="both", expand=True, padx=2, pady=2)
        tk.Label(body, text=title, bg=bg, fg=accent,
                 font=("Consolas", 11, "bold"), anchor="w").pack(
                 fill="x", padx=12, pady=(8, 2))
        tk.Label(body, text=msg, bg=bg, fg="#dfe7ee", justify="left",
                 wraplength=w - 30, anchor="w", font=("Segoe UI", 9)).pack(
                 fill="x", padx=12, pady=(0, 8))

        win.after(ms, lambda: _safe_destroy(win))
    except Exception:
        pass


def _safe_destroy(win):
    try:
        win.destroy()
        if _ACTIVE_TOAST.get("win") is win:
            _ACTIVE_TOAST["win"] = None
    except Exception:
        pass


def classify(text: str):
    """Map an engine log line to (kind, title, message) or None."""
    t = (text or "").strip()
    if not t:
        return None
    low = t.lower()
    if "🏆 won!" in t or "🏆 won" in t:
        return ("won", "🏆 BET WON", _squeeze(t))
    if "❌ lost bet" in t:
        return ("lost", "Bet lost", _squeeze(t))
    if ("smart bet #" in low and "placed" in low) or ("long-shot bet #" in low and "placed" in low):
        return ("placed", "Bet placed", _squeeze(t))
    if "ready to auto-withdraw" in low or "reserve recycles" in low:
        return ("withdraw", "Savings reached", _squeeze(t))
    if "auto-withdraw done" in low:
        return ("withdraw", "Auto-withdraw done", _squeeze(t))
    if "typ wait" in low or "waiting for winnings" in low or "win-funded wait" in low:
        return ("funds", "Waiting for funds", _squeeze(t))
    if "deposit flow done" in low or "confirm the m-pesa" in low:
        return ("funds", "Deposit", _squeeze(t))
    if "insufficient" in low or "deposit required" in low:
        return ("warn", "Deposit needed", _squeeze(t))
    if "📋 planned" in t:
        return ("planned", "Slip planned", _squeeze(t))
    return None


def _squeeze(text: str, limit: int = 240) -> str:
    s = " ".join(text.split())
    return s if len(s) <= limit else s[: limit - 1] + "…"