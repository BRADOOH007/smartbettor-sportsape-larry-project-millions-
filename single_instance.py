#!/usr/bin/env python3
"""Single-instance guard shared by EVERY entry point of the tool.

One named mutex is used by all launchers (start_gui.py, main.py, spa_auto_start.py
and every PyInstaller build that imports main_gui). Whichever process claims it
first is "the" running instance; any later process is told to exit immediately —
so two instances of the tool can never run at once, from any build, any exe name,
any console vs windowed binary, ever.

The mutex handle lives in this module for the lifetime of the process and is
released by the OS automatically when the owning process exits (kill, crash or
clean close), so the guard never leaves a stale lock behind.
"""

from __future__ import annotations

import ctypes
import os
import sys

# Local-namespace named mutex. "Local\\" needs no special privilege and still
# separates per-session. Kept unique to this project so it never collides with
# the user's own tooling or other software.
_MUTEX_NAME = "Local\\BetFlowPro.SportsApe.SingleInstance"

_handle = None          # c_void_p for the current process (once acquired)
_acquired = False


def _last_error() -> int:
    try:
        return int(ctypes.get_last_error())
    except Exception:
        return 0


def acquire(name: str = None) -> bool:
    """Try to claim the single-instance mutex. Returns True if THIS process is
    the one and only running instance; returns False if another instance is
    already alive. Never raises (a guard failure degrades to 'allowed' rather
    than blocking the user out of their own tool)."""
    global _handle, _acquired
    if _acquired:
        return True
    mutex_name = name or _MUTEX_NAME
    try:
        _k32 = ctypes.windll.kernel32
        _CreateMutexW = _k32.CreateMutexW
        _CreateMutexW.argtypes = [ctypes.c_void_p, ctypes.c_long, ctypes.c_wchar_p]
        _CreateMutexW.restype = ctypes.c_void_p
        # Must read the Win32 last-error directly: ctypes.get_last_error() only
        # works for WinDLL(use_last_error=True), not for windll.kernel32.
        _GetLastError = _k32.GetLastError
        _GetLastError.restype = ctypes.c_ulong

        h = _CreateMutexW(None, False, mutex_name)
        if not h:
            # CreateMutexW failed outright (rare) — allow rather than lock out.
            return True
        # Read ERROR code IMMEDIATELY after CreateMutexW — any other ctypes call
        # in between could clobber the thread-local last-error value.
        err = _GetLastError()
        _handle = ctypes.c_void_p(h)
        if err == 183:  # ERROR_ALREADY_EXISTS
            _acquired = False
            return False
        _acquired = True
        return True
    except Exception:
        return True  # guard failure = allow (never block the user's own run)


def is_owner() -> bool:
    return bool(_acquired)


def notify_and_exit(message: str = None) -> None:
    """Show a one-line notice (no Tk required — works in windowed EXEs too) and
    hard-exit this second instance. Even if the popup is never clicked, a
    watchdog exits the process ~2s later — a second instance can never linger."""
    body = message or ("BetFlow Pro is already running in another window.\n"
                       "Close that instance first, or reuse its window.")

    def _watchdog():
        import time as _t
        _t.sleep(2.0)
        os._exit(0)

    try:
        import threading as _th
        _th.Thread(target=_watchdog, daemon=True).start()
    except Exception:
        pass
    try:
        MB_ICONINFO = 0x00000040
        MB_OK = 0x00000000
        ctypes.windll.user32.MessageBoxW(None, body, "BetFlow Pro", MB_OK | MB_ICONINFO)
    except Exception:
        pass
    try:
        sys.exit(0)
    except SystemExit:
        raise
    except Exception:
        pass
    os._exit(0)


def guard_required_entry(*, message: str = None) -> int:
    """Call this at the very top of any entry module. Returns 0 if this process
    should keep running, otherwise exits the extra instance with code 0."""
    if acquire():
        return 0
    notify_and_exit(message)
    return 1  # unreachable in practice — notify_and_exit exits


if __name__ == "__main__":
    # Self-test: two acquires in the same process — second must be False.
    ok1 = acquire()
    ok2 = acquire()
    print(f"first acquire={ok1}, second acquire={ok2}")
    sys.exit(0 if (ok1 is True and ok2 is False) else 1)