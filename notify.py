"""Sound + desktop toast alerts for BetFlow Pro.

Pure standard library: winsound (Windows built-in) for soft system beeps
and a tiny tkinter Toplevel for the auto-hiding toast. No new dependencies.

Soft beep philosophy: single short tones only, no multi-note fanfares.
Win = one gentle ascending beep. Loss = one low quiet tone. No noise spam.
"""
import sys
import threading
import tkinter as tk

_ACTIVE_TOAST = {"win": None}


def sound(kind: str) -> None:
    """Play a single short pure-tone beep *only* for the three important events:
         won    → high short note (gentle ascending)
         lost   → low short note
         placed → mid short note
    All other event kinds (funds, withdraw, planned, warn, info, etc.) are
    deliberately SILENT — they only ever show the visual toast, never a
    desktop system sound or a beep. No MessageBeep (Windows stock sound
    schemes) is ever used because those play the user's configured
    information / warning / exclamation wav file, which is loud and
    sounds identical to OS-level alerts the user actually cares about.
    """
    if sys.platform != "win32":
        return

    tones = {
        "won":    (880, 120),
        "lost":   (330, 150),
        "placed": (660,  80),
    }
    if kind not in tones:
        return
    freq, dur = tones[kind]

    def _play():
        try:
            import winsound
            winsound.Beep(freq, dur)
        except Exception:
            pass

    threading.Thread(target=_play, daemon=True).start()


def toast(title: str, msg: str, ms: int = 4000) -> None:
    """Pop a small bottom-right toast that auto-disappears after *ms* ms.

    Smaller than before (280×72), slightly transparent, no border flash —
    visible but not grabbing focus or covering work.
    """
    try:
        prev = _ACTIVE_TOAST.get("win")
        if prev is not None:
            try:
                prev.destroy()
            except Exception:
                pass
        root = tk._default_root
        if root is None:
            return

        win = tk.Toplevel(root)
        _ACTIVE_TOAST["win"] = win
        win.overrideredirect(True)
        try:
            win.wm_attributes("-topmost", True)
            win.wm_attributes("-alpha", 0.88)   # slightly transparent — less intrusive
        except Exception:
            pass

        colors = {
            "won":      ("#0c2014", "#27ae60"),
            "placed":   ("#0d1620", "#3d9be9"),
            "lost":     ("#1e0f0f", "#c0392b"),
            "warn":     ("#1e1a0a", "#d4a017"),
            "funds":    ("#0d1a24", "#4fc3f7"),
            "withdraw": ("#1a1424", "#9b59b6"),
            "planned":  ("#141a10", "#7dce82"),
            "info":     ("#141a1f", "#c8d8e4"),
        }
        bg, accent = colors.get("info")
        for k, (cb, ca) in colors.items():
            if k in (title or "").lower():
                bg, accent = cb, ca
                break

        sw = win.winfo_screenwidth()
        sh = win.winfo_screenheight()
        w, h, pad = 280, 70, 12
        win.geometry(f"{w}x{h}+{sw - w - pad}+{sh - h - pad - 40}")

        # Thin left-border accent strip
        border = tk.Frame(win, bg=accent, width=3)
        border.pack(side="left", fill="y")
        body = tk.Frame(win, bg=bg)
        body.pack(side="left", fill="both", expand=True)

        tk.Label(body, text=title, bg=bg, fg=accent,
                 font=("Consolas", 10, "bold"), anchor="w").pack(
                 fill="x", padx=10, pady=(8, 1))
        tk.Label(body, text=_squeeze(msg, 100), bg=bg, fg="#c8d8e4",
                 justify="left", anchor="w",
                 font=("Segoe UI", 8)).pack(
                 fill="x", padx=10, pady=(0, 8))

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