import sys
import threading
from datetime import datetime
from tkinter import Tk
import main_gui as gui

LOG = r"C:\Users\Home\Desktop\ALL FILES\sportsape\run24h_terminal.log"


def stamp():
    return datetime.now().strftime("%H:%M:%S")


def write_log(line):
    try:
        with open(LOG, "a", encoding="utf-8") as f:
            f.write(f"[{stamp()}] {line}\n")
    except Exception:
        pass


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