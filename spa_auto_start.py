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

root.after(2000, app.start_bet_machine)
root.mainloop()