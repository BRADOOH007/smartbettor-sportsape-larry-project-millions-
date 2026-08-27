#!/usr/bin/env python3
"""Convenient launcher for the Tkinter GUI."""

import runpy


if __name__ == "__main__":
    # Execute main_gui as a script so its existing startup flow stays intact.
    runpy.run_module("main_gui", run_name="__main__")
