import sys
import threading
import ctypes
from datetime import datetime
from tkinter import Tk
import main_gui as gui

LOG = r"C:\Users\Home\Desktop\ALL FILES\sportsape\run24h_terminal.log"
ERR = r"C:\Users\Home\Desktop\ALL FILES\sportsape\stderr.log"


def stamp():
    return datetime.now().strftime("%H:%M:%S")


def engage_keep_awake():
    """Keep the laptop RUNNING (never sleep) while still letting the screen
    turn itself off — the machine must stay up to place/watch bets overnight.

    SetThreadExecutionState(ES_CONTINUOUS | ES_SYSTEM_REQUIRED):
      - ES_SYSTEM_REQUIRED  → the OS will NOT sleep on its own timer.
      - ES_CONTINUOUS       → the flag persists for the whole process.
      - NO ES_DISPLAY_REQUIRED → the monitor may still go dark to save power.
    The call is process-local: nothing is changed system-wide, and normal sleep
    behaviour returns automatically the moment this process stops.
    """
    try:
        ES_CONTINUOUS = 0x80000000
        ES_SYSTEM_REQUIRED = 0x00000001
        ctypes.windll.kernel32.SetThreadExecutionState(
            ES_CONTINUOUS | ES_SYSTEM_REQUIRED)
        write_log("⏰ Keep-awake engaged — laptop stays on, screen may turn off (safe to sleep the display).")
    except Exception as e:
        write_log(f"⏰ Keep-awake NOT engaged (err: {str(e)[:80]}) — laptop may sleep.")


def write_log(line):
    try:
        with open(LOG, "a", encoding="utf-8") as f:
            f.write(f"[{stamp()}] {line}\n")
    except Exception:
        pass


# Surface ANY thread crash into the main log instead of a hidden console.
# Without this, a worker thread dying on an unhandled exception would leave the
# machine "online" but silently doing nothing — exactly the stall we saw.
def _thread_crash_hook(args):
    try:
        tb = "".join(__import__("traceback").format_exception(
            args.exc_type, args.exc_value, args.exc_traceback))
        with open(LOG, "a", encoding="utf-8") as f:
            f.write(f"[{stamp()}] 💥 THREAD CRASH ({args.thread.name or '?'}):\n{tb}\n")
        with open(ERR, "a", encoding="utf-8") as f:
            f.write(tb)
    except Exception:
        pass


threading.excepthook = _thread_crash_hook


def engage_keep_awake():
    """Keep the laptop RUNNING (never sleep) while still letting the screen
    turn itself off — the machine must stay up to place/watch bets overnight.

    SetThreadExecutionState(ES_CONTINUOUS | ES_SYSTEM_REQUIRED):
      - ES_SYSTEM_REQUIRED  → the OS will NOT sleep on its own timer.
      - ES_CONTINUOUS       → the flag persists for the whole process.
      - NO ES_DISPLAY_REQUIRED → the monitor may still go dark to save power.
    The call is process-local: nothing is changed system-wide, and normal sleep
    behaviour returns automatically the moment this process stops.
    """
    try:
        ES_CONTINUOUS = 0x80000000
        ES_SYSTEM_REQUIRED = 0x00000001
        ctypes.windll.kernel32.SetThreadExecutionState(
            ES_CONTINUOUS | ES_SYSTEM_REQUIRED)
        write_log("⏰ Keep-awake engaged — laptop stays on, screen may turn off (safe to sleep the display).")
    except Exception as e:
        write_log(f"⏰ Keep-awake NOT engaged (err: {str(e)[:80]}) — laptop may sleep.")


engage_keep_awake()


# Command-line trigger for an M-Pesa deposit test: `python spa_auto_start.py --deposit 30`
# fires one STK push per configured phone a few seconds after the GUI finishes loading.
_deposit_amount = None
_rest = sys.argv[1:]
if "--deposit" in _rest:
    try:
        i = _rest.index("--deposit")
        _deposit_amount = max(1.0, float(_rest[i + 1]))
    except Exception:
        _deposit_amount = 99.0


# The AppUserModelID must be set BEFORE the first tkinter window is created,
# otherwise Windows groups the taskbar under the generic python.exe icon.
gui.set_windows_app_id("BetFlowPro.Machine")

root = Tk()
app = gui.BetFlowProGUI(root)

orig_append = app._append_log


def wrapped(line):
    try:
        orig_append(line)
    except Exception:
        pass
    if isinstance(line, str):
        write_log(line)


app._append_log = wrapped

# No auto-start on launch: the user may want to add a phone number, change the
# daily budget, or run a balance check before the machine begins betting.


def fire_deposit():
    if _deposit_amount is None:
        return
    try:
        app.deposit_var.set(str(int(_deposit_amount)))
        write_log(f"--deposit trigger scheduled: KES {_deposit_amount:,.0f} per phone after GUI load")
        root.after(10000, app.start_deposit_flow)
    except Exception as e:
        write_log(f"--deposit trigger failed: {str(e)[:150]}")


if _deposit_amount is not None:
    root.after(3000, fire_deposit)

root.mainloop()