"""
Resource path helpers for development and PyInstaller bundles.
"""
import os
import sys


# Files that prove a directory IS the live app workspace. Used to stop a frozen
# build from inventing its own empty state next to the .exe.
_STATE_MARKERS = (
    "sportsape_settings.json",
    "sportsape_ledger.json",
)


def _has_state(directory):
    """True when `directory` holds the real, populated app state."""
    try:
        hits = 0
        for marker in _STATE_MARKERS:
            p = os.path.join(directory, marker)
            if os.path.exists(p):
                try:
                    # An empty/freshly-created marker does not count as proof.
                    if os.path.getsize(p) > 2:
                        hits += 1
                except OSError:
                    pass
        return hits > 0
    except Exception:
        return False


def app_base_dir():
    """Return the writable app directory.

    Dev: the folder containing this module (not the CWD, so results land in the
    same place regardless of where the app is launched from).
    Frozen bundles: the LIVE WORKSPACE, not necessarily next to the .exe.

    WHY THE FROZEN CASE NEEDS CARE (2026-10-05). The old implementation
    returned ``dirname(sys.executable)``, which for a one-file build is
    ``dist/``. That silently created a SECOND, EMPTY state set inside dist/:
    the app saw 0 bets instead of 17, no CLV, no calibration, no form cache,
    and - worst of all - believed the daily stake cap had never been used, so
    it could bet straight past the owner's limit. The app "forgot everything"
    for no reason other than the folder it was launched from.

    We now anchor on whichever candidate directory actually holds the populated
    state, preferring the parent of a build-output folder (dist/build). If no
    candidate has state yet (a genuine first run), we fall back to next to the
    .exe so a fresh install still behaves sensibly.

    2026-10-08: the shipped exe lives on the Desktop at
    ``Desktop\\BetFlow.exe`` and its state lives there too. Dev runs used to
    resolve a SECOND state set inside the source folder (``sportsape/``), so
    the same app had two ledgers, two settings files and two daily-cap clocks,
    and which one applied depended on how it was launched. Split state means a
    cap enforced against one copy while bets are staked against another. So a
    Desktop state set, when present, wins for every launch mode - that is the
    one folder the shipped app is guaranteed to reach.
    """
    desktop = os.path.join(os.path.expanduser("~"), "Desktop")
    if _has_state(desktop):
        return desktop

    if not getattr(sys, "frozen", False):
        return os.path.dirname(os.path.abspath(__file__))

    exe_dir = os.path.dirname(os.path.abspath(sys.executable))
    parent = os.path.dirname(exe_dir)

    # Preferred: the project root above a PyInstaller output folder. This is
    # where every ledger, cache and log the user actually inspects lives.
    if os.path.basename(exe_dir).lower() in ("dist", "build") and _has_state(parent):
        return parent

    # Next best: next to the exe, but only if it genuinely holds live state.
    if _has_state(exe_dir):
        return exe_dir

    # Nothing there yet -> if the exe sits in a build-output folder, use the
    # project root anyway so we never strand state inside dist/.
    if os.path.basename(exe_dir).lower() in ("dist", "build"):
        return parent

    return exe_dir


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

