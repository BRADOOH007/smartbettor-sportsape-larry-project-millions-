#!/usr/bin/env python3
"""Robust launcher script for the SportsApe / BetFlow Pro GUI.

This script:
  * Ensures the working directory is set to the script's own folder so
    Assets/, cache files, and relative paths resolve correctly whether
    launched from the terminal or by double-clicking in Explorer.
  * Sets the Windows AppUserModelID BEFORE creating the first Tk window so
    the custom icon (Assets/balance_icon.ico) is used on the taskbar
    instead of the default Tk / python.exe feather icon.
  * Captures and displays startup errors in a message box (and writes them
    to a crash log) so that crashes don't simply flash away a console.
  * Re-routes stdout/stderr through replace-mode encoding handlers so
    oddball characters in logs don't kill the GUI.
"""

from __future__ import annotations

import os
import sys
import time
import traceback
from datetime import datetime


def _chdir_to_script_folder() -> None:
    """Set CWD to the directory that contains THIS launcher file."""
    script_file = os.path.abspath(__file__)
    script_dir = os.path.dirname(script_file)
    os.chdir(script_dir)
    sys.path.insert(0, script_dir)


def _configure_encodings() -> None:
    """Best-effort: make stdout/stderr tolerant of non-encodable chars."""
    for stream_name in ("stdout", "stderr"):
        stream = getattr(sys, stream_name, None)
        if stream is None:
            continue
        reconf = getattr(stream, "reconfigure", None)
        if callable(reconf):
            try:
                reconf(errors="replace")
            except Exception:
                pass


def _write_crash_log(message: str) -> str:
    """Append a crash report to crash_log.txt next to the launcher."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    log_path = os.path.join(script_dir, "crash_log.txt")
    stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    try:
        with open(log_path, "a", encoding="utf-8") as fh:
            fh.write(f"===== Crash at {stamp} =====\n{message}\n\n")
    except Exception:
        pass
    return log_path


def _show_fatal_error(title: str, body: str) -> None:
    """Show a popup error using Tk (fallback to console print)."""
    log_path = _write_crash_log(body)
    full_body = f"{body}\n\nCrash log written to:\n{log_path}"
    try:
        import tkinter as tk
        from tkinter import messagebox

        root = tk.Tk()
        root.withdraw()
        try:
            root.attributes("-topmost", True)
        except Exception:
            pass
        messagebox.showerror(title, full_body)
        try:
            root.destroy()
        except Exception:
            pass
    except Exception:
        print(f"[{title}] {full_body}", file=sys.stderr)


def main() -> int:
    _chdir_to_script_folder()
    _configure_encodings()

    try:
        import main_gui as gui
    except Exception as exc:
        tb = traceback.format_exc()
        _show_fatal_error(
            "Failed to import main_gui",
            f"{type(exc).__name__}: {exc}\n\n{tb}",
        )
        return 2

    try:
        gui.set_windows_app_id(f"BetFlowPro.{getattr(gui, 'APP_VERSION', '6.0.0')}")
        if sys.platform == "win32":
            try:
                import ctypes

                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
                    f"BetFlowPro.{getattr(gui, 'APP_VERSION', '6.0.0')}"
                )
            except Exception:
                pass
    except Exception:
        pass

    try:
        if hasattr(gui, "main") and callable(gui.main):
            gui.main()
        else:
            import tkinter as tk

            root = tk.Tk()
            root.withdraw()
            app = gui.BetFlowProGUI(root)
            root.mainloop()
        return 0
    except Exception as exc:
        tb = traceback.format_exc()
        _show_fatal_error(
            "GUI crashed",
            f"{type(exc).__name__}: {exc}\n\n{tb}",
        )
        return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)
    except SystemExit:
        raise
    except Exception as exc_final:
        try:
            _show_fatal_error(
                "Unexpected launcher crash",
                f"{type(exc_final).__name__}: {exc_final}\n\n{traceback.format_exc()}",
            )
        except Exception:
            pass
        sys.exit(99)
