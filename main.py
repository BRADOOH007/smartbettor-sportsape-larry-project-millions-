#!/usr/bin/env python3
"""Convenient launcher for the Tkinter GUI."""

# Single-instance guard: only one build of this executable may run at a time.
import ctypes
import os
import sys

if sys.platform == "win32":
    _exe_name = os.path.splitext(os.path.basename(sys.argv[0] or sys.executable or ""))[0]
    _mutex = ctypes.windll.kernel32.CreateMutexW(None, False, _exe_name)
    if ctypes.windll.kernel32.GetLastError() == 183:  # ERROR_ALREADY_EXISTS
        # Second double-click while first instance is still starting (withdrawn) —
        # bring the existing window to the front instead of silently exiting.
        try:
            import ctypes as _ct2
            _user32 = _ct2.windll.user32
            # Try by window title ( BetFlow Pro v* ) — works even while withdrawn.
            _hwnd = _user32.FindWindowW(None, f"⚽ BetFlow Pro v6.0.0 — SportPesa Auto-Bet Machine")
            if not _hwnd:
                _hwnd = _user32.FindWindowW(None, None)
                # fallback: enumerate is too heavy, just flash
                pass
            if _hwnd:
                _user32.ShowWindow(_hwnd, 9)  # SW_RESTORE
                _user32.SetForegroundWindow(_hwnd)
                _user32.BringWindowToTop(_hwnd)
        except Exception:
            pass
        sys.exit(0)

import runpy


if __name__ == "__main__":
    # Execute main_gui as a script so its existing startup flow stays intact.
    runpy.run_module("main_gui", run_name="__main__")
