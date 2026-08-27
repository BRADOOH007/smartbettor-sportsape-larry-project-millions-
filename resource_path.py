"""
Resource path helpers for development and PyInstaller bundles.
"""
import os
import sys


def app_base_dir():
    """Return the writable app directory."""
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.abspath(".")


def resource_path(relative_path):
    """
    Get absolute path to a bundled resource.

    PyInstaller one-file builds extract bundled files into ``_MEIPASS``.
    In development, resources are read from the current project folder.
    """
    base_path = getattr(sys, "_MEIPASS", app_base_dir())
    return os.path.join(base_path, relative_path)


def writable_path(relative_path):
    """Return a writable path next to the app/exe."""
    return os.path.join(app_base_dir(), relative_path)

