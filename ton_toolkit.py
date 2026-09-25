#!/usr/bin/env python3
"""
ToN Toolkit — modular helper for Terrors of Nowhere.

Each feature is a module you can toggle independently. They share one OSC
connection and one VRChat log reader, so nothing is done twice.

    pip install python-osc
    python ton_toolkit.py

Build an exe:
    pip install pyinstaller
    pyinstaller --onefile --windowed --name ToNToolkit ton_toolkit.py
"""

import glob
import array
import hashlib
import urllib.request
import webbrowser
import zipfile
import json
import os
import queue
import re
import subprocess
import tempfile
import sys
import threading
import time
import wave
import tkinter as tk
from tkinter import filedialog
from tkinter import messagebox
from tkinter import font as tkfont
from tkinter import ttk

from pythonosc import udp_client
from pythonosc.dispatcher import Dispatcher
from pythonosc.osc_server import ThreadingOSCUDPServer

try:
    import winsound
except ImportError:
    winsound = None

APP_NAME = "ToN Toolkit"
# Bumped whenever the file changes, and printed at startup. If the log does
# not show the version you expect, the running file is not the one you edited.
APP_VERSION = "1.1"
# Where releases are published, as "owner/repo" on GitHub. While this is
# blank the update check is off. Release tags must look like v1.1.
UPDATE_REPO = "SkipzXD/Terror-of-Nowhere-Farming-App-"
# Personal build?  False for public releases.
#   * AFK Helper — idling through rounds is what most players object to
# Everything else, including the terror picker, is in both builds.
# build_personal.bat flips this on; the repo always holds the public value.
# Public value. A file named "personal.txt" beside the app also turns it on,
# so running from source for yourself needs no edit and the repo stays public.
# (HERE is defined below, so the path is worked out here directly.)
# Only when running from SOURCE: an exe never looks for personal.txt, so an
# empty text file beside the public exe cannot switch the AFK Helper on.
# build_personal.bat sets the flag itself, so the personal exe needs no file.
PERSONAL_BUILD = False or (not getattr(sys, "frozen", False) and os.path.isfile(
    os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), "personal.txt")))

# Where ToNSaveManager writes the current terror, if its "Round Info To File"
# option is on. Blank means look in the usual places.
TERROR_NAME_FILE = ""
HERE = os.path.dirname(os.path.abspath(sys.argv[0]))
CONFIG_FILE = os.path.join(HERE, "ton_toolkit.json")
LOG_DIR = os.path.join(os.environ.get("USERPROFILE", ""),
                       "AppData", "LocalLow", "VRChat", "VRChat")
VRC_IP, SEND_PORT, LISTEN_PORT = "127.0.0.1", 9000, 9001

DIRS = {"left": "/input/MoveLeft", "right": "/input/MoveRight",
        "forward": "/input/MoveForward", "back": "/input/MoveBackward"}

ROUND_START = re.compile(
    r"This round is taking place at (.+?) \((\d+)\) and the round type is (.+?)\s*$")
ROUND_FETCH = re.compile(r"\[String Download\].*pastebin\.com")
VERIFIED_END = "Verified Round End"
# "Killers have been set - 44 0 0 // Round type is Classic". The terrors are
# numeric ids; ToN ListTool's own table turns them into names. It lands about
# 10s after the round line, which is why the terror picker needs to wait.
# Most rounds say "Killers have been SET"; Fog hides the terror first and
# later says "Killers have been REVEALED". Missing the second form meant a Fog
# round never reported its terror at all.
KILLERS = re.compile(r"Killers have been (?:set|revealed) - ([\d ]+?)\s*//"
                     r"\s*Round type is (.+?)\s*$")
# "Killers is unknown - ??? // Will be revealed after 50 seconds": tells us
# how long to wait instead of guessing.
KILLERS_LATER = re.compile(r"Killers is unknown.*?revealed after (\d+) second")


# 8 Pages pool index -> real terror id. Filled from terror_names.json's
# "eight_pages" key when present; empty means 8 Pages terrors are unknown.
EIGHT_PAGES_MAP = {}


def resolve_terror_ids(round_name, raw):
    """
    Turn the log's terror numbers into real terror ids.

    The log does NOT always give the real id. Checked against ~900 rounds of
    logs:
      * Alternate reports 0-35, the position among the 36 Alternates, so the
        real id is 134 + that (a logged 2 is Sanic, 136 — not Demented
        Spongebob, 2).
      * Unbound reports its position among the 84 Unbound: 200 + that.
      * Midnight's THIRD terror is always an Alternate (it never goes above
        34), so that one slot gets the 134 offset too.
    Everything else is already the real id.

    The number of slots that count is fixed per round type. Dropping every 0
    as "empty" was wrong: in a one-terror round a 0 in the first slot is a
    real terror (Huggy in Classic, Decayed Sponge in Alternate).
    """
    def is_(*names):
        return round_name in names
    # A Moon round always logs "0 0 0": the terror IS the moon, so it comes
    # from the round name. Reading the 0 gave Huggy for every Moon round.
    moon = {"Mystic Moon": 196, "ミスティックムーン": 196,
            "Blood Moon": 197, "ブラッドムーン": 197,
            "Twilight": 198, "トワイライト": 198,
            "Solstice": 199, "ソルスティス": 199}.get(round_name)
    if moon is not None:
        return [moon]
    if is_("Bloodbath", "ブラッドバス", "Midnight", "ミッドナイト"):
        n = 3
    elif is_("Double Trouble", "ダブルトラブル"):
        n = 2
    else:
        n = 1
    ids = list(raw[:n])
    if is_("8 Pages", "8ページ"):
        # 8 Pages logs an index into its OWN pool, which redirects to a
        # Classic or Alternate terror (a logged 30 is Judgement Bird, not MX).
        # The table lives inside ToNSaveManager's exe. Without it, report the
        # index as unknown (negative) rather than a confident wrong terror.
        table = EIGHT_PAGES_MAP
        return [table.get(i, -(i + 1)) for i in ids]
    if is_("Alternate", "オルタネイト"):
        ids = [134 + i for i in ids]
    elif is_("Unbound", "アンバウンド"):
        ids = [200 + i for i in ids]
    elif is_("Midnight", "ミッドナイト") and len(ids) == 3:
        ids[2] = 134 + ids[2]
    return ids
ROUND_OVER = "RoundOver"
DIED = "You died."
# TON logs this the instant a round begins if you are sitting in the respawn
# area, always BEFORE the round-type line (14/14 in the sample log). "opted in"
# marks coming back.
MASTER_SWITCH = "OnMasterClientSwitched"
NOT_OPTED = "Not opted in. Not joining this round."
OPTED_IN = "opted in"

# VRChat logs round names in the client's language, so every set holds both
# the Japanese and English spellings — matching only one silently breaks the
# sequence predictor and the post-round sequence choice.
PLAIN_NAMES = {"クラシック", "Classic"}
# Rounds that can appear in ANY slot, so they say nothing about what comes
# next. RUN is here because a パニッシュ followed one directly, while the
# sequence rule was insisting the next round had to be 通常.
OVERRIDE_NAMES = {"8ページ", "ゴースト", "アンバウンド", "オルタネイト",
                  "8 Pages", "Eight Pages", "Ghost", "Unbound", "Alternate",
                  "RUN", "Run"}
ALERT_NAMES = {"パニッシュ", "8ページ", "Punished", "8 Pages", "Eight Pages"}
# Items are confiscated after these rounds, so your lobby speed differs and the
# walk timings that work at 6.60 no longer land in the same place.

PICKUP = re.compile(r"Pickup object: '([^',]+)'\s*equipped = True")
DROP = re.compile(r"Drop object: '([^',]+),\s*was equipped")

# (passive, activated) top speed for each held item.
#   passive   = just holding it
#   activated = while the use button is held (Emerald Coil needs left click)
# Punish is a cap that overrides these, so holding an Auric Coil and only
# reaching 6.60 is the giveaway -- correct these numbers to what you observe.
ITEM_SPEED = {
    "": (6.60, 6.60),
    "Auric Coil": (10.20, 10.20),     # aura, always on
    "Emerald Coil": (6.60, 15.30),    # boost only while clicking
    "Regen Coil": (8.30, 8.30),
    "Delicate Coil": (10.70, 10.70),
}
# (english, japanese) for every round seen in your own logs. Matching accepts
# either spelling, so it works whichever language the client is set to.
ROUND_TYPES = [
    ("Classic", "クラシック"), ("Fog", "霧"),
    ("Punished", "パニッシュ"), ("Sabotage", "サボタージュ"),
    ("Bloodbath", "ブラッドバス"), ("Double Trouble", "ダブルトラブル"),
    ("Ghost", "ゴースト"), ("Unbound", "アンバウンド"),
    ("Alternate", "オルタネイト"), ("Midnight", "ミッドナイト"),
    # "RUN" is deliberately absent: the self-destruct key does nothing in
    # that round, so arming it would only look broken.
    ("8 Pages", "8ページ"), ("Cracked", "狂気"),
    # The big four, kept together at the bottom.
    ("Mystic Moon", "ミスティックムーン"), ("Blood Moon", "ブラッドムーン"),
    ("Solstice", "ソルスティス"), ("Twilight", "トワイライト"),
]

# The four rare "big" rounds get their own block under the common list. Left in
# the two-column flow they would split across rows and get lost among the rest.
BIG_FOUR = ("Mystic Moon", "Blood Moon", "Solstice", "Twilight")

USE_INPUT = "/input/UseRight"         # desktop left click
# A capped speed still jitters by a hundredth or two. Anything inside this band
# counts as "the same value", otherwise the plateau timer resets constantly and
# never reaches the hold time an alert needs.
STABLE_BAND = 0.04
# Slopes and stairs push you past your flat-ground cap (6.83 seen against a
# 6.60 cap). Readings above cap+margin are assisted, so they are not evidence
# of an uncapped round and must not veto a detection.
SLOPE_MARGIN = 0.05
# A probe whose raw peak is this far above your cap was mostly spent airborne.
# Filtering the high samples then leaves a low grounded one behind, which reads
# as a cap — so the whole probe has to be thrown away, not cleaned up.
FALL_LIMIT = 1.00
DROP_INPUT = "/input/DropRight"       # desktop right click
MIN_PRESS = 0.09                      # a press shorter than this may be missed
# Walking is 4.00 m/s, so nothing slower is a decision to move. Coming to a
# stop leaves 0.5-0.9 m/s of drift for a moment, and treating that as movement
# cancelled self-destructs and speed checks while standing perfectly still.
MOVING_SPEED = 3.50


# =======================================================  keyboard  ========
# VRChat's OSC exposes only a fixed set of /input/ addresses, so a key like "="
# cannot be sent that way. SendInput with SCAN codes is what Unity reads most
# reliably — virtual-key-only events are ignored by some games.
if sys.platform == "win32":
    import ctypes
    from ctypes import wintypes

    _user32 = ctypes.windll.user32

    ULONG_PTR = ctypes.c_ulonglong if ctypes.sizeof(
        ctypes.c_void_p) == 8 else ctypes.c_ulong

    class _KEYBDINPUT(ctypes.Structure):
        _fields_ = [("wVk", wintypes.WORD), ("wScan", wintypes.WORD),
                    ("dwFlags", wintypes.DWORD), ("time", wintypes.DWORD),
                    ("dwExtraInfo", ULONG_PTR)]

    class _MOUSEINPUT(ctypes.Structure):
        _fields_ = [("dx", wintypes.LONG), ("dy", wintypes.LONG),
                    ("mouseData", wintypes.DWORD), ("dwFlags", wintypes.DWORD),
                    ("time", wintypes.DWORD), ("dwExtraInfo", ULONG_PTR)]

    class _HARDWAREINPUT(ctypes.Structure):
        _fields_ = [("uMsg", wintypes.DWORD), ("wParamL", wintypes.WORD),
                    ("wParamH", wintypes.WORD)]

    class _INPUTUNION(ctypes.Union):
        # All three members are required: INPUT is sized by its LARGEST member
        # (40 bytes on x64). A union holding only KEYBDINPUT gives 32, and
        # SendInput then misreads the struct — the key-up never arrives and the
        # key appears stuck down.
        _fields_ = [("mi", _MOUSEINPUT), ("ki", _KEYBDINPUT),
                    ("hi", _HARDWAREINPUT)]

    class _INPUT(ctypes.Structure):
        _fields_ = [("type", wintypes.DWORD), ("u", _INPUTUNION)]

    _KEYEVENTF_SCANCODE, _KEYEVENTF_KEYUP = 0x0008, 0x0002

    def _scan_for(ch):
        vk = _user32.VkKeyScanW(ord(ch))
        if vk == -1:
            return 0
        return _user32.MapVirtualKeyW(vk & 0xFF, 0)

    def _send(scan, flags):
        inp = _INPUT(type=1, u=_INPUTUNION(
            ki=_KEYBDINPUT(0, scan, flags, 0, 0)))
        return _user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(_INPUT))

    _MOUSEEVENTF_XDOWN, _MOUSEEVENTF_XUP = 0x0080, 0x0100

    def _send_mouse(flag, data):
        inp = _INPUT(type=0, u=_INPUTUNION(
            mi=_MOUSEINPUT(0, 0, data, flag, 0, 0)))
        return _user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(_INPUT))

    def key_down(token):
        if token in MOUSE_TOKENS:
            _send_mouse(_MOUSEEVENTF_XDOWN, MOUSE_TOKENS[token])
            return True
        scan = _scan_for(token) if len(token or "") == 1 else 0
        if not scan:
            vk = token_vk(token or "")
            if vk < 0:
                return False
            scan = _user32.MapVirtualKeyW(vk, 0)
        if not scan:
            return False
        _send(scan, _KEYEVENTF_SCANCODE)
        return True

    def key_up(token):
        if token in MOUSE_TOKENS:
            _send_mouse(_MOUSEEVENTF_XUP, MOUSE_TOKENS[token])
            return True
        scan = _scan_for(token) if len(token or "") == 1 else 0
        if not scan:
            vk = token_vk(token or "")
            if vk < 0:
                return False
            scan = _user32.MapVirtualKeyW(vk, 0)
        if not scan:
            return False
        _send(scan, _KEYEVENTF_SCANCODE | _KEYEVENTF_KEYUP)
        return True

    def send_key(ch, hold=0.05):
        """Press and release one character key. Returns False if unmappable."""
        if not key_down(ch):
            return False
        try:
            time.sleep(hold)
        finally:
            # Always release, even if the sleep is interrupted, so a stuck key
            # can never outlive the press.
            key_up(ch)
        return True

    # Tokens for keys that are not a single character. Mouse4/Mouse5 are the
    # side buttons, which Tk cannot see reliably, so they are polled directly.
    VK_TOKENS = {
        "Mouse4": 0x05, "Mouse5": 0x06, "MouseMiddle": 0x04,
        "Space": 0x20, "Tab": 0x09, "Enter": 0x0D, "Backspace": 0x08,
        "Shift": 0x10, "Ctrl": 0x11, "Alt": 0x12, "Caps": 0x14,
        "Esc": 0x1B, "Insert": 0x2D, "Delete": 0x2E, "Home": 0x24,
        "End": 0x23, "PageUp": 0x21, "PageDown": 0x22,
        "Left": 0x25, "Up": 0x26, "Right": 0x27, "Down": 0x28,
        **{f"F{i}": 0x6F + i for i in range(1, 25)},
        **{f"Num{i}": 0x60 + i for i in range(0, 10)},
    }
    MOUSE_TOKENS = {"Mouse4": 0x0001, "Mouse5": 0x0002}   # XBUTTON1 / XBUTTON2

    def token_vk(token):
        if token in VK_TOKENS:
            return VK_TOKENS[token]
        if len(token) == 1:
            vk = _user32.VkKeyScanW(ord(token))
            return -1 if vk == -1 else (vk & 0xFF)
        return -1

    def key_is_down(token):
        """Global key/button state — works whatever window has focus."""
        vk = token_vk(token or "")
        if vk < 0:
            return False
        return bool(_user32.GetAsyncKeyState(vk) & 0x8000)

    _WM_KEYDOWN, _WM_KEYUP = 0x0100, 0x0101

    def vrchat_windows():
        """Every VRChat window, in a stable order."""
        found = []

        @ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)
        def cb(hwnd, _lp):
            buf = ctypes.create_unicode_buffer(256)
            _user32.GetWindowTextW(hwnd, buf, 256)
            cls = ctypes.create_unicode_buffer(256)
            _user32.GetClassNameW(hwnd, cls, 256)
            if "VRChat" in buf.value and "Unity" in cls.value:
                found.append(hwnd)
            return True                 # keep going: there may be several

        _user32.EnumWindows(cb, 0)
        return sorted(found)            # stable across calls


    def vrchat_hwnd():
        """
        The VRChat window belonging to THIS copy of the toolkit.

        Stopping at the first match was fine with one client and wrong with
        two — both copies would drive the same window. Sorting the handles
        gives a stable order; the first is the one we drive.
        """
        wins = vrchat_windows()
        return wins[0] if wins else 0

    class BgHold:
        """
        Hold a key in VRChat while another app has the foreground.

        The recipe:

          AttachThreadInput  - share VRChat's input queue, so focus and
                               keyboard state become common to both threads
          SetFocus           - give the KEYBOARD focus to VRChat's window
                               without changing the FOREGROUND window, which
                               is the part that makes this invisible
          SetKeyboardState   - mark the key as held in the shared state, which
                               is what Unity's legacy Input.GetKey reads
          SendInput          - deliver the event itself, now routed to the
                               focused-within-the-queue window

        The attachment has to stay up for the whole hold, and every call must
        come from the same thread, so this is a small object rather than a
        function.
        """

        def __init__(self, hwnd, token):
            self.hwnd, self.token = hwnd, token
            self.tid = self.mine = 0
            self.prev_focus = 0
            self.ok = False
            self.fail = ""
            # Two clients: the key only reaches the window in front, so take
            # the front for the press and give it straight back.
            self.steal = len(vrchat_windows()) > 1
            self.old_front = 0

        def start(self, tries=4):
            """
            Attach and take keyboard focus, retrying briefly.

            The first attempt after launch often fails: a thread only gets a
            message queue once it has called into user32, and AttachThreadInput
            needs one on BOTH threads. A throwaway call creates ours, and a
            couple of retries cover VRChat still settling. This is why it never
            worked on the first explode of a session and worked from then on.
            """
            vk = token_vk(self.token or "")
            if vk < 0:
                self.fail = "key is not on your layout"
                return False
            self.vk = vk
            self.mine = ctypes.windll.kernel32.GetCurrentThreadId()
            # Force a message queue onto this thread before attaching.
            _user32.GetKeyState(0)
            if self.steal and not self.old_front:
                self.old_front = _user32.GetForegroundWindow()
                if self.old_front != self.hwnd:
                    focus_window(self.hwnd)
                    time.sleep(0.05)
            for attempt in range(max(1, tries)):
                if attempt:
                    time.sleep(0.12)
                    self.hwnd = vrchat_hwnd()      # it may have changed
                if not self.hwnd:
                    self.fail = "VRChat window not found"
                    continue
                self.tid = _user32.GetWindowThreadProcessId(self.hwnd, None)
                if _user32.AttachThreadInput(self.mine, self.tid, True):
                    break
                self.fail = "could not attach to VRChat's input thread"
            else:
                return False
            self.ok = True
            try:
                self.prev_focus = _user32.GetFocus()
                _user32.SetFocus(self.hwnd)
                if _user32.GetFocus() != self.hwnd:
                    # Attached but focus refused. Retry the whole thing: on the
                    # first go VRChat is sometimes still claiming its own.
                    self.fail = "VRChat refused keyboard focus"
                    self.stop()
                    return self.start(tries - 1) if tries > 1 else False
                self._press(True)
                return True
            except Exception:
                self.stop()
                return False

        def _press(self, down):
            """
            NEVER SendInput here.

            SendInput injects at system level and lands in the FOREGROUND
            window whatever the attached queue says — which typed "=====" into
            Chrome instead of VRChat. The attachment gives us the shared
            keyboard STATE; the event itself must be posted to VRChat's window
            directly.
            """
            state = (ctypes.c_ubyte * 256)()
            _user32.GetKeyboardState(ctypes.byref(state))
            state[self.vk] = 0x80 if down else 0x00
            _user32.SetKeyboardState(ctypes.byref(state))
            scan = _user32.MapVirtualKeyW(self.vk, 0)
            lp = (scan << 16) | 1
            if down:
                _user32.PostMessageW(self.hwnd, _WM_KEYDOWN, self.vk, lp)
            else:
                _user32.PostMessageW(self.hwnd, _WM_KEYUP, self.vk,
                                     lp | (3 << 30))

        def keep(self):
            """
            Re-assert the held state without re-sending the key event.

            A repeated WM_KEYDOWN reads as a fresh press and restarts the
            hold-to-confirm bar, so only the STATE is refreshed here.
            """
            if not self.ok:
                return
            try:
                # Only re-issue focus if it actually moved. Calling SetFocus on
                # every tick is what sometimes pulled VRChat to the front.
                if _user32.GetFocus() != self.hwnd:
                    _user32.SetFocus(self.hwnd)
                state = (ctypes.c_ubyte * 256)()
                _user32.GetKeyboardState(ctypes.byref(state))
                state[self.vk] = 0x80
                _user32.SetKeyboardState(ctypes.byref(state))
            except Exception:
                pass

        def stop(self):
            if not self.ok:
                return
            try:
                self._press(False)
                if self.prev_focus:
                    _user32.SetFocus(self.prev_focus)
            except Exception:
                pass
            finally:
                _user32.AttachThreadInput(self.mine, self.tid, False)
                self.ok = False
                if self.steal and self.old_front and \
                        self.old_front != self.hwnd:
                    focus_window(self.old_front)
                    self.old_front = 0

    def post_key(hwnd, token, down):
        """
        Deliver a key straight to a window, focused or not.

        SendInput always goes to the FOREGROUND window, so it cannot work in
        the background. PostMessage addresses a window directly. Unity's legacy
        input path reads window messages, so this sometimes works — but Unity
        does not forward background keyboard to the newer Input System, so it
        is not guaranteed. Test it before relying on it.
        """
        vk = token_vk(token or "")
        if vk < 0 or not hwnd:
            return False
        scan = _user32.MapVirtualKeyW(vk, 0)
        lp = (scan << 16) | 1
        if down:
            _user32.PostMessageW(hwnd, _WM_KEYDOWN, vk, lp)
        else:
            _user32.PostMessageW(hwnd, _WM_KEYUP, vk, lp | (3 << 30))
        return True

    _SPI_GET_TIMEOUT, _SPI_SET_TIMEOUT = 0x2000, 0x2001

    def _unlock_foreground():
        """
        Lift Windows' foreground lock.

        SetForegroundWindow is refused for a background process unless the
        caller "deserves" focus. Zeroing the lock timeout, plus a synthetic ALT
        tap, is the long-standing pair of tricks that satisfies the rule.
        """
        old = wintypes.DWORD()
        try:
            ctypes.windll.user32.SystemParametersInfoW(
                _SPI_GET_TIMEOUT, 0, ctypes.byref(old), 0)
            ctypes.windll.user32.SystemParametersInfoW(
                _SPI_SET_TIMEOUT, 0, ctypes.c_void_p(0), 0)
        except Exception:
            pass
        try:                      # an ALT tap marks this thread as "active"
            _send(_user32.MapVirtualKeyW(0x12, 0), _KEYEVENTF_SCANCODE)
            _send(_user32.MapVirtualKeyW(0x12, 0),
                  _KEYEVENTF_SCANCODE | _KEYEVENTF_KEYUP)
        except Exception:
            pass
        return old

    def is_minimised(hwnd):
        """
        True when the window is minimised rather than merely behind another.

        Unity throttles hard once a window is minimised, and the self-destruct
        hold needs frames to advance — a key held against a minimised client
        can be received and still never complete.
        """
        return bool(hwnd) and bool(_user32.IsIconic(hwnd))

    def _rect(hwnd):
        r = (ctypes.c_long * 4)()
        if _user32.GetWindowRect(hwnd, ctypes.byref(r)):
            return (r[0], r[1], r[2], r[3])
        return None

    def focus_window(hwnd):
        """
        Bring a window to the front WITHOUT moving or resizing it.

        The previous version called ShowWindow(SW_RESTORE) every time and fell
        back to a minimise/restore cycle — both of which reposition a window
        that was already visible, which is why two half-screen clients ended
        up stacked on the same side. Restore is now only used on a window that
        is genuinely minimised, and the rectangle is put back if anything
        moved it anyway.
        """
        if not hwnd:
            return False
        if _user32.GetForegroundWindow() == hwnd:
            return True
        before = _rect(hwnd)
        _unlock_foreground()
        mine = ctypes.windll.kernel32.GetCurrentThreadId()
        other = _user32.GetWindowThreadProcessId(
            _user32.GetForegroundWindow(), None)
        attached = _user32.AttachThreadInput(other, mine, True)
        try:
            if _user32.IsIconic(hwnd):
                _user32.ShowWindow(hwnd, 9)          # SW_RESTORE, only if
            _user32.BringWindowToTop(hwnd)           # actually minimised
            _user32.SetForegroundWindow(hwnd)
            if _user32.GetForegroundWindow() != hwnd:
                try:
                    _user32.SwitchToThisWindow(hwnd, True)
                except Exception:
                    pass
        finally:
            if attached:
                _user32.AttachThreadInput(other, mine, False)

        after = _rect(hwnd)
        if before and after and before != after:
            # Something moved it: put it back exactly where it was.
            #   SWP_NOZORDER | SWP_NOACTIVATE = 0x0004 | 0x0010
            _user32.SetWindowPos(hwnd, 0, before[0], before[1],
                                 before[2] - before[0],
                                 before[3] - before[1], 0x0014)

        if _user32.GetForegroundWindow() == hwnd:
            return True
        buf = ctypes.create_unicode_buffer(256)
        _user32.GetWindowTextW(_user32.GetForegroundWindow(), buf, 256)
        return "VRChat" in buf.value

    class BgFocus:
        """
        Put the cursor on this client's window for a click, then put it back.

        VRChat aims its interaction from the MOUSE CURSOR, not the camera, so
        a click only lands if the pointer is over the button inside the right
        window. The pointer is moved to the centre of THIS client's window for
        the duration and restored afterwards.

        With two clients it also brings the window to the front, because the
        interaction only reaches the foreground one — and puts the previous
        window back straight after. With a single client none of that happens:
        it attaches and gives keyboard focus exactly as it always did.
        """

        def __init__(self, hwnd, move_cursor=True):
            self.hwnd, self.tid, self.mine = hwnd, 0, 0
            self.prev = 0
            self.move_cursor = move_cursor
            self.old_pos = None
            self.ok = False
            self.steal = len(vrchat_windows()) > 1
            self.old_front = 0

        def _centre(self):
            """Middle of THIS window, read fresh: two clients sit far apart."""
            rect = (ctypes.c_long * 4)()
            if not _user32.GetWindowRect(self.hwnd, ctypes.byref(rect)):
                return None
            left, top, right, bottom = rect
            if right - left < 50 or bottom - top < 50:
                return None                 # minimised or not laid out yet
            return (left + right) // 2, (top + bottom) // 2

        def __enter__(self):
            if not self.hwnd:
                return self
            if self.steal:
                self.old_front = _user32.GetForegroundWindow()
                if self.old_front != self.hwnd:
                    focus_window(self.hwnd)
                    time.sleep(0.05)
            if self.move_cursor:
                pt = (ctypes.c_long * 2)()
                if _user32.GetCursorPos(ctypes.byref(pt)):
                    self.old_pos = (pt[0], pt[1])
                mid = self._centre()
                if mid:
                    _user32.SetCursorPos(mid[0], mid[1])
            _user32.GetKeyState(0)          # force a message queue
            self.mine = ctypes.windll.kernel32.GetCurrentThreadId()
            self.tid = _user32.GetWindowThreadProcessId(self.hwnd, None)
            if _user32.AttachThreadInput(self.mine, self.tid, True):
                self.ok = True
                self.prev = _user32.GetFocus()
                _user32.SetFocus(self.hwnd)
            return self

        def __exit__(self, *_):
            if self.ok:
                try:
                    if self.prev:
                        _user32.SetFocus(self.prev)
                finally:
                    _user32.AttachThreadInput(self.mine, self.tid, False)
                self.ok = False
            if self.old_pos:
                _user32.SetCursorPos(*self.old_pos)
                self.old_pos = None
            if self.steal and self.old_front and self.old_front != self.hwnd:
                focus_window(self.old_front)
                self.old_front = 0
            return False


    def foreground_hwnd():
        return _user32.GetForegroundWindow()

    def my_vrchat_focused():
        """
        Is OUR client the window in front?

        With two clients running, every copy sees the same key press, so a
        shared hold key would explode both games at once. Whichever VRChat you
        are actually looking at is the one you mean, so only that copy acts.
        With a single client this is just "is VRChat in front".
        """
        mine = vrchat_hwnd()
        if not mine:
            return False
        front = _user32.GetForegroundWindow()
        if len(vrchat_windows()) < 2:
            buf = ctypes.create_unicode_buffer(256)
            _user32.GetWindowTextW(front, buf, 256)
            return "VRChat" in buf.value
        return front == mine

    def foreground_title():
        hwnd = _user32.GetForegroundWindow()
        buf = ctypes.create_unicode_buffer(256)
        _user32.GetWindowTextW(hwnd, buf, 256)
        return buf.value
else:
    VK_TOKENS, MOUSE_TOKENS = {}, {}

    def vrchat_windows():
        return []

    def vrchat_hwnd():
        return 0

    def post_key(hwnd, token, down):
        return False

    class BgHold:
        def __init__(self, hwnd, token):
            self.ok = False

        def start(self):
            return False

        def keep(self):
            pass

        def stop(self):
            pass

    def focus_window(hwnd):
        return False

    class BgFocus:
        def __init__(self, hwnd, move_cursor=True):
            self.ok = False

        def __enter__(self):
            return self

        def __exit__(self, *_):
            return False

    def is_minimised(hwnd):
        return False

    def my_vrchat_focused():
        return False

    def foreground_hwnd():
        return 0

    def token_vk(token):
        return -1

    def key_is_down(token):
        return False

    def key_down(token):
        return False

    def key_up(token):
        return False

    def send_key(token, hold=0.05):
        return False


    def foreground_title():
        return ""


# =========================================================  sound  =========
# Alerts are WAV files the user picks, played at their chosen volume. There is
# no built-in beep: winsound.Beep has no volume control at all.


_SND_CACHE = {}


def sound_dirs():
    """
    Where to look for alert clips, in priority order.

    A Sounds folder beside the exe wins, so anyone can drop in their own
    voice without rebuilding. The copies baked into the exe come next:
    PyInstaller unpacks onefile builds to _MEIPASS and puts onedir data in
    _internal, so both are checked.
    """
    here = [os.path.join(HERE, "Sounds")]
    bundled = getattr(sys, "_MEIPASS", None)
    if bundled:
        here.append(os.path.join(bundled, "Sounds"))
    here.append(os.path.join(HERE, "_internal", "Sounds"))
    return here


def find_asset(name):
    """A bundled file, or one the user dropped in beside the app."""
    for d in [HERE] + [os.path.dirname(x) for x in sound_dirs()]:
        p = os.path.join(d, name)
        if os.path.isfile(p):
            return p
    return ""


def find_sound(*names):
    for d in sound_dirs():
        for n in names:
            p = os.path.join(d, n)
            if os.path.isfile(p):
                return p
    return ""


def scaled_copy(path, volume):
    """
    Return a path to a copy of `path` at `volume`.

    Playing from memory with SND_ASYNC is unreliable — Windows reads the buffer
    after the call returns — so the rescaled audio is written to a temp file and
    played by name instead. Raises with a readable reason on failure.
    """
    vol = max(0.0, min(1.0, volume))
    key = (path, os.path.getmtime(path), round(vol, 2))
    if key in _SND_CACHE and os.path.isfile(_SND_CACHE[key]):
        return _SND_CACHE[key]
    with wave.open(path, "rb") as w:
        if w.getsampwidth() != 2:
            return path             # not 16-bit: play the original as-is
        ch, rate, n = w.getnchannels(), w.getframerate(), w.getnframes()
        samples = array.array("h")
        samples.frombytes(w.readframes(n))
    if vol < 0.999:
        for i, s in enumerate(samples):
            samples[i] = max(-32768, min(32767, int(s * vol)))
    out = os.path.join(tempfile.gettempdir(),
                       f"ton_{abs(hash(key)):x}.wav")
    with wave.open(out, "wb") as o:
        o.setnchannels(ch)
        o.setsampwidth(2)
        o.setframerate(rate)
        o.writeframes(samples.tobytes())
    _SND_CACHE[key] = out
    return out


def play_mci(path, volume, log=None):
    """
    Play a non-WAV file through Windows' own media player (MCI).

    winsound handles PCM WAV only, so an mp3 fails with "file does not start
    with RIFF id". MCI is built into Windows and plays mp3 without any extra
    library, with its own volume control.

    Ogg has no MCI device on a stock Windows, so it will be reported as
    unplayable rather than silently doing nothing.
    """
    if sys.platform != "win32":
        return False
    try:
        mci = ctypes.windll.winmm.mciSendStringW
        mci("close tonsnd", None, 0, None)      # allow replaying
        if mci(f'open "{path}" alias tonsnd', None, 0, None) != 0:
            if log:
                log(f"Windows cannot play {os.path.splitext(path)[1]} files — "
                    f"use .wav or .mp3")
            return False
        vol = int(max(0.0, min(1.0, volume)) * 1000)
        mci(f"setaudio tonsnd volume to {vol}", None, 0, None)
        mci("play tonsnd", None, 0, None)
        return True
    except Exception as e:
        if log:
            log(f"could not play {os.path.basename(path)}: {e}")
        return False


def play_sound(path, volume, log=None):
    """Play a clip. Says why in the log instead of silently falling back."""
    if not winsound:
        return
    if not path:
        if log:
            log("no sound file set for this alert")
        return
    if not os.path.isfile(path):
        if log:
            log(f"sound file not found: {path}")
        return
    if volume <= 0:
        return
    if os.path.splitext(path)[1].lower() != ".wav":
        play_mci(path, volume, log)     # mp3 and anything else Windows knows
        return
    try:
        winsound.PlaySound(scaled_copy(path, volume),
                           winsound.SND_FILENAME | winsound.SND_ASYNC)
    except Exception as e:
        if log:
            log(f"could not play {os.path.basename(path)}: {e}")






def _pid_alive(pid):
    """Is that process still running? OpenProcess, not a shell command."""
    try:
        h = ctypes.windll.kernel32.OpenProcess(0x1000, False, int(pid))
        if not h:
            return False
        ctypes.windll.kernel32.CloseHandle(h)
        return True
    except Exception:
        return True                 # cannot tell: assume it is




# =========================================================  theme  =========
# Plain ttk on Windows uses Segoe UI, which has thin CJK coverage and falls
# back to a bitmap font — that is what makes the Japanese look muddy. Yu Gothic
# UI is the readable default, one point larger because kanji need the height.
FONT_EN = ["Segoe UI", "Inter", "Helvetica"]
FONT_JA = ["Yu Gothic UI", "Meiryo UI", "Meiryo", "MS UI Gothic", "Segoe UI"]

# Nord palette, matching ToN Overlay and ToN ListTool (#2E3440 / #ECEFF4).
THEME = {
    "bg":      "#2E3440",   # window
    "panel":   "#3B4252",   # cards, tabs, header
    "raised":  "#434C5E",   # entries, buttons, hovered tabs
    "line":    "#4C566A",   # borders and separators
    "fg":      "#ECEFF4",
    "muted":   "#A0AABF",
    "accent":  "#BF616A",   # alerts, selected tab
    "accent2": "#88C0D0",   # informational
    "ok":      "#A3BE8C",
}


class TerrorNames:
    """
    Turns terror ids into names, purely so the log reads sensibly.

    The log only ever gives numbers ("Killers have been set - 44 0 0"), and
    "ids [131]" tells you nothing. Names come from terror_names.json beside
    the app; without it the ids are shown as they are and nothing else
    changes.
    """

    # ToNSaveManager can write the current round to plain text files
    # (Settings -> ラウンド情報をファイルに書き出す). That is the user's own
    # output and always current, so it beats any bundled table.
    LIVE_FILE = "ton_terror_name.txt"
    LIVE_DIRS = (
        os.path.join(os.environ.get("APPDATA", ""), "ToNSaveManager"),
        os.path.join(os.environ.get("LOCALAPPDATA", ""), "ToNSaveManager"),
        os.path.join(os.path.expanduser("~"), "Documents", "ToNSaveManager"),
    ) + tuple(f"{d}:\\ToNSaveManager" for d in "CDEFG")

    def __init__(self):
        self._names = {}
        self._rounds = {}
        self._sprites = {}
        self._sheet_names = []
        self._dir = ""
        self._sheets = {}
        self._icons = {}
        self.loaded_from = ""
        self.format = 0
        self._tried = False

    def _load(self):
        if self._tried:
            return
        self._tried = True
        # Read EVERY copy and keep the most complete. Stopping at the first
        # meant a stale names-only file beside the exe beat a full copy
        # bundled inside _internal.
        best, best_score = None, -1
        # The packed copy inside _internal is checked FIRST, so it wins a tie.
        # Earlier builds also put a loose copy beside the exe; the
        # updater does not delete files, so that old copy would otherwise
        # override every future data update.
        # No fallback to HERE for _MEIPASS: that would put the loose folder
        # first again whenever _MEIPASS is absent.
        cands = [getattr(sys, "_MEIPASS", None),
                 os.path.join(HERE, "_internal"), HERE]
        for d in dict.fromkeys(c for c in cands if c):
            p = os.path.join(d, "terror_names.json")
            try:
                with open(p, encoding="utf-8") as f:
                    blob = json.load(f)
            except (OSError, ValueError):
                continue
            if not isinstance(blob, dict):
                continue
            # Newer layouts win outright over any older copy lying about.
            score = (int(blob.get("format", 1)) * 100
                     + bool(blob.get("names")) + 2 * bool(blob.get("rounds"))
                     + 4 * bool(blob.get("sprites")))
            if score > best_score:
                best, best_score = (d, p, blob), score
        if best:
            d, p, blob = best
            self._names = blob.get("names", blob)
            self._rounds = blob.get("rounds", {})
            EIGHT_PAGES_MAP.clear()
            EIGHT_PAGES_MAP.update({int(k): int(v) for k, v in
                                    (blob.get("eight_pages") or {}).items()})
            self._sprites = blob.get("sprites", {})
            # Two atlases: ToN ListTool keeps the Unbound terrors (40px) on a
            # separate sheet from the rest (32px). Older files name one.
            self._sheet_names = blob.get("sprite_sheets") or \
                ([blob["sprite_sheet"]] if blob.get("sprite_sheet") else [])
            self._dir = d
            self.loaded_from = p
            self.format = int(blob.get("format", 1))

    def live(self):
        """
        The current terror name straight from ToNSaveManager, or "".

        Written by its "round info to file" option and refreshed every round,
        so it needs no id table and cannot go out of date.
        """
        if TERROR_NAME_FILE:
            try:
                with open(TERROR_NAME_FILE, encoding="utf-8") as f:
                    s = f.read().strip()
                if s:
                    return s
            except OSError:
                pass
        for d in (HERE,) + self.LIVE_DIRS:
            if not d:
                continue
            p = os.path.join(d, self.LIVE_FILE)
            try:
                with open(p, encoding="utf-8") as f:
                    s = f.read().strip()
                # ToNSaveManager writes "???" (and similar) before the terror
                # is known. Showing that is worse than showing the id.
                if s and s not in ("???", "?", "-", "N/A", "Unknown", "なし"):
                    return s
            except OSError:
                continue
        return ""

    def icon(self, tid):
        """
        The terror's icon as a Tk image, cut from the sprite sheet, or None.

        Cut with Tk's own "copy -from", so no image library is needed at
        runtime. Cached: the picker asks for the same icons repeatedly.
        """
        self._load()
        key = str(tid)
        if key in self._icons:
            return self._icons[key]
        pos = self._sprites.get(key)
        if not pos or not self._sheet_names:
            return None
        # [sheet, x, y, w, h]; older files stored just [x, y] at 32px
        if len(pos) == 2:
            sheet_i, (x, y), w, h = 0, pos, 32, 32
        else:
            sheet_i, x, y, w, h = pos
        try:
            name = self._sheet_names[sheet_i]
            if name not in self._sheets:
                self._sheets[name] = tk.PhotoImage(
                    file=os.path.join(self._dir, name))
            img = tk.PhotoImage(width=w, height=h)
            img.tk.call(img, "copy", self._sheets[name], "-from",
                        x, y, x + w, y + h)
            self._icons[key] = img
            return img
        except (tk.TclError, OSError, IndexError):
            self._icons[key] = None
            return None

    def rounds(self):
        """{"Bloodbath/ブラッドバス": [ids…]} — which terrors each round spawns."""
        self._load()
        return self._rounds

    def name(self, tid):
        self._load()
        return self._names.get(str(tid), f"#{tid}")

    def label(self, ids):
        """'Maze Thing' for one, 'A, B, C' for several, ids if unknown."""
        live = self.live()
        if live:
            return live
        self._load()
        out = []
        for i in ids:
            if i < 0:
                out.append(f"8 Pages #{-i - 1} (unknown)")
                continue
            n = self._names.get(str(i))
            out.append(f"{n}" if n else f"#{i}")
        return ", ".join(out) if out else "none"





class Toggle(tk.Frame):
    """
    A minimal check box, drawn on a Canvas.

    Deliberately NOT a restyled ttk.Checkbutton: replacing the indicator
    element through ttk styling is fragile and has silently produced blank
    boxes before. A Canvas draws exactly what it is told on every platform,
    and the only state it holds is the BooleanVar it is given.

    Filled with a tick when on, a plain outline when off.
    """
    BOX, RAD = 16, 4

    def __init__(self, parent, variable, text="", command=None, muted=False):
        super().__init__(parent, bg=THEME["bg"])
        self.var, self.command = variable, command
        b = self.BOX
        self.cv = tk.Canvas(self, width=b + 2, height=b + 2,
                            highlightthickness=0, bd=0, bg=THEME["bg"],
                            cursor="hand2")
        self.cv.pack(side="left")
        self.label = tk.Label(self, text=text, bg=THEME["bg"],
                              fg=THEME["muted"] if muted else THEME["fg"],
                              font=UI_FONT[0], cursor="hand2", anchor="w")
        self.label.pack(side="left", padx=(8, 0))
        for w in (self.cv, self.label):
            w.bind("<Button-1>", self._flip)
        self._trace = self.var.trace_add("write", lambda *_: self._draw())
        self._draw()

    def _flip(self, _e=None):
        self.var.set(not self.var.get())
        self._draw()
        if self.command:
            self.command()

    def set_bg(self, colour):
        """Match a highlighted row: the box must not keep the old backdrop."""
        self._bg = colour
        for w in (self, self.cv, self.label):
            w.configure(bg=colour)
        self._draw()

    def _round_rect(self, x0, y0, x1, y1, r, **kw):
        """Tk has no rounded rectangle, so trace one as a polygon."""
        pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r,
               x1, y1 - r, x1, y1, x1 - r, y1, x0 + r, y1,
               x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
        return self.cv.create_polygon(pts, smooth=True, **kw)

    def _draw(self):
        try:
            on = bool(self.var.get())
        except Exception:
            on = False
        self.cv.delete("all")
        b, r = self.BOX, self.RAD
        # On a highlighted row the backdrop IS the accent colour, so an
        # accent-filled box would vanish into it. Invert there.
        lit = getattr(self, "_bg", THEME["bg"]) == THEME["accent2"]
        fill = THEME["bg"] if lit else THEME["accent2"]
        tick = THEME["accent2"] if lit else THEME["bg"]
        edge = THEME["bg"] if lit else THEME["line"]
        if on:
            self._round_rect(1, 1, b, b, r, fill=fill, outline="")
            self.cv.create_line(4.2, 8.4, 6.8, 11.2, 11.9, 5.0,
                                fill=tick, width=2, capstyle="round",
                                joinstyle="round", smooth=False)
        else:
            self._round_rect(1, 1, b, b, r, fill="", outline=edge,
                             width=1.5)

    def destroy(self):
        try:
            self.var.trace_remove("write", self._trace)
        except Exception:
            pass
        super().destroy()



class IconTile(tk.Canvas):
    """
    One terror in the explode picker: its icon, framed red when ticked.

    Modelled on ToN ListTool's 自動自爆設定 grid — red frame and tick means
    explode, a dimmed tile means sit it out. Terrors with no icon get a short
    name instead, so every terror is still selectable.
    """
    S = 44                     # tile size; icons are 32px, centred

    def __init__(self, parent, variable, image=None, name="", command=None):
        super().__init__(parent, width=self.S, height=self.S, bd=0,
                         highlightthickness=0, bg=THEME["bg"],
                         cursor="hand2")
        self.var, self.image, self.name = variable, image, name
        self.command = command
        self.bind("<Button-1>", self._flip)
        self._trace = self.var.trace_add("write", lambda *_: self._draw())
        self._draw()
        Tip(self, name)

    def _flip(self, _e=None):
        self.var.set(not self.var.get())
        if self.command:
            self.command()

    def _draw(self):
        try:
            on = bool(self.var.get())
        except Exception:
            on = False
        self.delete("all")
        s = self.S
        if self.image is not None:
            self.create_image(s // 2, s // 2, image=self.image)
        else:
            short = self.name if len(self.name) <= 9 else self.name[:8] + "…"
            self.create_text(s // 2, s // 2, text=short, width=s - 4,
                             fill=THEME["fg"], font=(UI_FONT[0][0], 7))
        if on:
            self.create_rectangle(2, 2, s - 3, s - 3, outline=THEME["accent"],
                                  width=2)
            # tick in the corner, like ListTool
            self.create_line(s - 15, s - 9, s - 11, s - 5, s - 4, s - 13,
                             fill=THEME["accent"], width=2)
        else:
            # Tk has no alpha: a stippled dark wash dims the icon instead
            self.create_rectangle(0, 0, s, s, fill=THEME["bg"], outline="",
                                  stipple="gray50")
            self.create_rectangle(2, 2, s - 3, s - 3, outline=THEME["line"],
                                  width=1)

    def destroy(self):
        try:
            self.var.trace_remove("write", self._trace)
        except Exception:
            pass
        super().destroy()


class KeyGrab(tk.Toplevel):
    """
    Modal "press a key" capture.

    Keyboard comes through Tk's own events, but the mouse side buttons do not
    reach Tk on Windows, so those are polled from the OS while the dialog is
    open. Escape cancels without changing anything.
    """

    def __init__(self, parent, on_pick):
        super().__init__(parent)
        self.on_pick, self.done = on_pick, False
        self.overrideredirect(True)
        self.configure(bg=THEME["line"])
        tk.Label(self, text=t("key.prompt"), bg=THEME["panel"],
                 fg=THEME["fg"], font=UI_FONT[0], padx=18, pady=14,
                 wraplength=260, justify="center").pack(padx=1, pady=1)
        self.update_idletasks()
        x = parent.winfo_rootx() + (parent.winfo_width() - self.winfo_width()) // 2
        y = parent.winfo_rooty() + (parent.winfo_height() - self.winfo_height()) // 2
        self.geometry(f"+{max(0, x)}+{max(0, y)}")
        self.grab_set()
        self.focus_force()
        self.bind("<KeyPress>", self._on_key)
        self.after(40, self._poll_mouse)

    _NAMED = {"space": "Space", "Return": "Enter", "Tab": "Tab",
              "BackSpace": "Backspace", "Escape": None, "Delete": "Delete",
              "Insert": "Insert", "Home": "Home", "End": "End",
              "Prior": "PageUp", "Next": "PageDown", "Left": "Left",
              "Right": "Right", "Up": "Up", "Down": "Down"}

    def _on_key(self, e):
        ks = e.keysym
        if ks in self._NAMED:
            tok = self._NAMED[ks]
            return self._finish(tok)            # None here means cancelled
        if re.fullmatch(r"F\d{1,2}", ks):
            return self._finish(ks)
        if len(e.char) == 1 and e.char.isprintable():
            return self._finish(e.char.upper() if e.char.isalpha() else e.char)
        return None

    def _poll_mouse(self):
        if self.done:
            return
        for tok in ("Mouse4", "Mouse5", "MouseMiddle"):
            if key_is_down(tok):
                return self._finish(tok)
        self.after(40, self._poll_mouse)

    def _finish(self, token):
        if self.done:
            return
        self.done = True
        try:
            self.grab_release()
        except Exception:
            pass
        self.destroy()
        if token:
            self.on_pick(token)


class Tip:
    """Hover help. Tk has no tooltip, so this is a borderless Toplevel."""

    def __init__(self, widget, text):
        self.widget, self.text, self.win = widget, text, None
        widget.bind("<Enter>", self.show, add="+")
        widget.bind("<Leave>", self.hide, add="+")

    def show(self, _e=None):
        if self.win or not self.text:
            return
        x = self.widget.winfo_rootx() + 20
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
        self.win = tk.Toplevel(self.widget)
        self.win.wm_overrideredirect(True)
        self.win.wm_geometry(f"+{x}+{y}")
        tk.Label(self.win, text=self.text, justify="left", wraplength=320,
                 bg=THEME["raised"], fg=THEME["fg"], bd=1, relief="solid",
                 padx=8, pady=6, font=UI_FONT[0]).pack()

    def hide(self, _e=None):
        if self.win:
            self.win.destroy()
            self.win = None


UI_FONT = [("Segoe UI", 9)]     # replaced once the theme is applied


def pick_font(candidates, root):
    have = set(tkfont.families(root))
    for name in candidates:
        if name in have:
            return name
    return candidates[-1]


# ==========================================================  i18n  =========
LANG = "en"          # "en" or "ja"; switched from the toggle at the bottom

# (english, japanese). Round-name matching is separate and always accepts both.
STRINGS = {
    "app.title":        ("ToN Toolkit", "ToN ツールキット"),
    "ui.enabled":       ("Enabled", "有効"),
    "err.port":         ("Port 9001 is taken by another OSC app.",
                         "ポート9001は他のOSCアプリが使用中です。"),
    "err.port2":        ("Trying OSCQuery instead, so both can run together.",
                         "OSCQueryで共存を試みます。"),
    "err.port3":        ("OSCQuery needs the zeroconf package:  "
                         "pip install zeroconf",
                         "OSCQueryには zeroconf が必要です:  "
                         "pip install zeroconf"),
    "ui.activity":      ("Activity", "ログ"),
    "ui.clear":         ("Clear", "クリア"),
    "ui.language":      ("Language / 言語", "Language / 言語"),
    "upd.title":        ("Update available", "アップデートがあります"),
    "upd.ask":          ("ToN Toolkit {new} is out (you have {cur}).",
                         "ToN Toolkit {new} が公開されました（現在 {cur}）。"),
    "upd.yes_install":  ("Update now? The app will close, update and "
                         "reopen. Your settings are kept.",
                         "今すぐ更新しますか？アプリが閉じて更新され、"
                         "再起動します。設定はそのまま残ります。"),
    "upd.yes_page":     ("Open the download page?",
                         "ダウンロードページを開きますか？"),

    "tab.helper":       ("TON Helper", "TON ヘルパー"),
    "afk.name":         ("AFK Helper", "AFK対策"),
    "afk.blurb":        ("Watches your movement during a round. Jumps only "
                         "after you have been still for the idle time — "
                         "moving resets the timer.",
                         "ラウンド中の移動を監視し、一定時間動かなかったときだけ"
                         "ジャンプします。動くとタイマーはリセットされます。"),
    "afk.idle":         ("Jump after idle (s)", "自動AFKジャンプ (秒)"),

    "spd.name":         ("8 Page/Punished Detector", "8ページ/パニッシュ検知"),
    "spd.blurb":        ("Press your check key in the lobby to measure your "
                         "speed — that is how 8 Page and Punished are spotted "
                         "before the round starts. Tick Enabled AND set a key "
                         "below: they work as a pair.",
                         "ロビーでチェックキーを押すと速度を測定します。"
                         "これでラウンド開始前に8ページとパニッシュを判定します。"
                         "「有効」のチェックとキー設定はセットで必要です。"),
    "spd.auto_probe":   ("Auto Speed Detection", "自動速度チェック"),
    "spd.probe_hold":   ("Sweep length (s)", "スイープ時間 (秒)"),
    "spd.probe_step":   ("Time per leg (s)", "1方向あたり (秒)"),
    "spd.settle":       ("8 Page hold needed (s)", "8ページ必要時間 (秒)"),
    "tip.settle":       ("Total time the speed must sit on 6.50 during a "
                         "sweep before it is called 8 Page.\n\n"
                         "Low values alert readily but can fire when a normal "
                         "round passes through 6.50 while accelerating to "
                         "6.60. Raise it if you get false alarms; lower it if "
                         "you have to check twice.",
                         "スイープ中に6.50でいた合計時間です。\n\n"
                         "小さいほど鳴りやすい反面、通常ラウンドが6.60へ"
                         "加速する途中で6.50を通過したときにも鳴ります。"
                         "誤検知が多ければ上げ、2回チェックが必要なら"
                         "下げてください。"),
    "tip.sweep":        ("How long the strafe lasts in total.\n\n"
                         "8 Page needs the speed to SETTLE on 6.50, not just "
                         "touch it: roughly 0.5s to accelerate plus 0.45s "
                         "sitting there. Below about 1.2s a plateau never "
                         "forms and detection fails quietly.",
                         "横移動の合計時間です。\n\n"
                         "8ページ判定には6.50で「一定になる」ことが必要で、"
                         "加速に約0.5秒＋維持0.45秒かかります。"
                         "1.2秒未満だと一定値にならず、検知できません。"),
    "tip.leg":          ("How long each left/right leg runs before reversing."
                         "\n\n"
                         "Short legs keep you in place but spend more time "
                         "accelerating; long legs reach the cap cleanly but "
                         "drift you across the lobby into walls, which reads "
                         "low. 0.45s is the balance; raise it in open rooms.",
                         "左右を切り替えるまでの時間です。\n\n"
                         "短いとその場に留まれますが加速に時間を取られ、"
                         "長いと確実に最高速に届く一方で壁にぶつかり"
                         "低く出ます。0.45秒が中間で、広い場所なら長めに。"),
    "spd.debug":        ("Log speed details", "速度の詳細をログ"),
    "spd.p8only":       ("Disable Punish Alerts", "パニッシュ検知オフ"),
    "tip.p8only":       ("Removes the PUNISH alert ONLY. Everything else is "
                         "untouched and 8ページ detection carries on "
                         "exactly as before.\n\n"
                         "Punish is a variable cap whose speeds overlap with "
                         "ordinary deceleration, so it is the source of "
                         "almost every false alarm. Turn this on to use the "
                         "toolkit purely as an 8ページ detector.\n\n"
                         "Punish is still worked out and written to the log — "
                         "it simply does not announce itself.",
                         "「パニッシュの通知だけ」を無効にします。"
                         "他の機能はそのままで、8ページ検知も"
                         "これまでどおり動作します。\n\n"
                         "パニッシュは可変の速度制限で、通常の減速と数値が"
                         "重なるため、誤検知のほとんどはこれが原因です。"
                         "8ページ専用として使いたい場合にオンにしてください。"
                         "\n\n"
                         "パニッシュの判定自体は続き、ログには残りますが、"
                         "通知は行いません。"),
    "spd.cancel":       ("Skip if I move first",
                         "動いたら自動速度チェックをやめる"),
    "spd.hotkey":       ("Manual check key", "手動チェックキー"),
    "key.prompt":       ("Press any key or a side mouse button…\n"
                         "(Esc to cancel)",
                         "任意のキーかサイドボタンを押してください…\n"
                         "(Esc でキャンセル)"),
    "key.set":          ("Click to set", "クリックで設定"),
    "key.reset":        ("Reset", "既定に戻す"),
    "spd.vol":          ("Alert volume", "アラート音量"),
    "spd.vtest":        ("Test", "テスト"),
    "spd.snd8":         ("8 Page sound", "8ページの音声"),
    "spd.sndp":         ("パニッシュ sound", "パニッシュの音声"),
    "spd.browse":       ("…", "…"),
    "spd.sndhint":      ("WAV or MP3. WAV follows the volume slider exactly; "
                         "other formats are played by Windows. Leave empty "
                         "for no sound.",
                         "WAV または MP3。WAVは音量スライダーがそのまま効き、"
                         "他の形式はWindows側で再生します。空欄なら"
                         "音は鳴りません。"),
    "spd.collide":      ("auto check off — Auto Round Starter is enabled "
                         "(they both move you; use the manual key or the "
                         "starter's own check)",
                         "自動チェックは無効 — 自動ラウンド開始が有効です"
                         "(どちらも移動するため。手動キーか"
                         "「開始後に速度チェック」を使ってください)"),
    "tip.auto":         ("Checks automatically as soon as the round data "
                         "arrives. That is only a GUESS at when the master "
                         "presses start — if they are slow, the reading is "
                         "taken before the round type applies and will say "
                         "NORMAL.\n\n"
                         "Assumes you are NOT the instance master. If you are "
                         "the one pressing start, use the manual key instead."
                         "\n\n"
                         "Turn this OFF if you use Auto Round Starter: both "
                         "walk your character around the lobby and they will "
                         "fight each other.",
                         "ラウンド情報を受信した直後に自動でチェックします。"
                         "ただしホストがボタンを押すタイミングの推測にすぎず、"
                         "押すのが遅いとラウンド適用前の速度を測ってしまい、"
                         "NORMAL と出ます。\n\n"
                         "自分がインスタンスマスターでない前提です。"
                         "自分がボタンを押す場合は手動キーを使ってください。"
                         "\n\n"
                         "自動ラウンド開始を使うときはオフにしてください。"
                         "どちらもロビーで移動するため干渉します。"),
    "tip.hotkey":       ("Press this key yourself right after you hear the "
                         "start button — that is the exact moment the speed "
                         "changes, so it is the most reliable check. Works "
                         "on its own; Auto Speed Detection can stay off.",
                         "スタートボタンの音が聞こえたら、このキーを押して"
                         "ください。速度が変わる瞬間なので最も確実です。"
                         "単独で動作し、自動速度チェックはオフでも構いません。"),
    "skp.name":         ("Auto Explode", "自爆設定"),
    "skp.blurb":        ("Presses your self-destruct key when a chosen round "
                         "starts, repeating until you die.",
                         "選択したラウンドが始まると自爆キーを押し、"
                         "死亡するまで繰り返します。"),
    "skp.hotkey":       ("Self-destruct key", "自爆キー"),
    "skp.rounds":       ("Explode on these rounds", "自爆するラウンド"),
    "skp.cancel":       ("Cancel key", "中止キー"),
    "skp.manual":       ("Hold-to-explode key", "押している間だけ自爆"),
    "tip.only":         ("With two clients running, the automatic explode "
                         "fires on this copy's own rounds only — each copy "
                         "reads its own log, so one game exploding does not "
                         "affect the other.\n\n"
                         "The hold key is shared across copies, so it acts on "
                         "whichever VRChat window is IN FRONT. Look at the "
                         "game you want to blow up, then hold the key.",
                         "2つのクライアントを動かしている場合、自動自爆は"
                         "そのコピー自身のラウンドにのみ反応します"
                         "(それぞれ別のログを読むため、片方の自爆は"
                         "もう片方に影響しません)。\n\n"
                         "手動キーは全コピー共通なので、「前面にある」"
                         "VRChatにのみ効きます。自爆させたいゲームを"
                         "前面にしてからキーを押してください。"),
    "skp.all":          ("Select all", "すべて選択"),
    "skp.none":         ("Clear all", "すべて解除"),
    "skp.extradelay":   ("Add extra delay", "追加の待機を使う"),
    "skp.delay":        ("Extra seconds", "追加の秒数"),
    "tip.delay":        ("The round line is logged before the round actually "
                         "begins, and self-destruct does nothing until it "
                         "has, so there is always a 10 second wait — the "
                         "fastest that reliably works.\n\n"
                         "Tick this to wait LONGER than that. The number is "
                         "ADDED to the 10s, so 3 means 13 seconds.\n\n"
                         "The cancel key still works while waiting, and it is "
                         "skipped if you start moving.",
                         "ログにラウンド名が出るのは実際の開始より前で、"
                         "開始前では自爆できないため、常に10秒待ちます"
                         "(確実に動く最速の値です)。\n\n"
                         "それより長く待ちたい場合にチェックします。"
                         "数値は10秒に「加算」され、3なら13秒です。\n\n"
                         "待機中も中止キーは有効で、動き出した場合は"
                         "実行しません。"),
    "skp.terrorbtn":    ("Choose terrors per round…", "ラウンドごとのテラー選択…"),
    "tip.terrorbtn":    ("For each round, choose WHICH terrors to explode on. "
                         "Ticked = explode, unticked = sit it out.\n\n"
                         "A round you never open keeps exploding on every "
                         "terror, so this only narrows rounds you choose to "
                         "configure.\n\n"
                         "It has to wait for the "
                         "terrors to be announced about 10 seconds into the "
                         "round before it can decide.",
                         "ラウンドごとに、どのテラーで自爆するかを選びます。"
                         "チェック = 自爆、チェックなし = 続行。\n\n"
                         "開かなかったラウンドはこれまでどおり全テラーで"
                         "自爆するので、設定したラウンドだけが絞り込まれます。"
                         "\n\n"
                         "テラーが判明するまで(開始から約10秒)待ってから"
                         "判定します。"),
    "skp.terrortitle":  ("Explode on which terrors", "自爆するテラーの選択"),
    "skp.terrorrounds": ("Rounds", "ラウンド"),
    "skp.terrorhint":   ("Ticked = Explode.  Unticked = Do not explode.",
                         "チェック = 自爆  /  チェックなし = 自爆しない"),
    "skp.terrorsave":   ("Save", "保存"),
    "skp.fognow":       ("Don't wait for the terror — explode at round start",
                         "テラーを待たずにラウンド開始で自爆"),
    "tip.fognow":       ("Fog hides its terror for about 50 seconds after "
                         "the round begins.\n\n"
                         "OFF: wait for the terror to be revealed, then "
                         "explode only if every terror is ticked below.\n\n"
                         "ON: ignore the terror and explode as soon as the "
                         "round starts. The ticks below are not used while "
                         "this is on.",
                         "霧ではラウンド開始から約50秒間テラーが"
                         "隠されます。\n\n"
                         "オフ: テラーが判明するまで待ち、下のテラーが"
                         "すべてチェックされている場合のみ自爆します。\n\n"
                         "オン: テラーを待たず、ラウンド開始と同時に"
                         "自爆します。オンの間、下のチェックは使われません。"),
    "skp.terrorsearch": ("Search:", "検索:"),
    "sec.terrors":      ("Terrors", "テラー"),
    "sec.alternates":   ("Alternates", "オルタネイト"),
    "sec.moons":        ("Moons", "ムーン"),
    "sec.8pages":       ("8 Pages", "8ページ"),
    "sec.special":      ("Special", "スペシャル"),
    "sec.unbound":      ("Unbound", "アンバウンド"),
    "skp.bg":           ("Explode without focusing VRChat", "裏画面自爆"),
    "tip.bg":           ("ON: the key works while you are in another window, "
                         "so you can explode without switching to VRChat.\n\n"
                         "DO NOT use this with more than one VRChat open. The "
                         "key that gets sent is the same for every client, so "
                         "it fires in whichever VRChat has focus — not "
                         "necessarily the one you meant. This toolkit "
                         "controls one VRChat at a time.",
                         "オン: VRChatを前面にしなくても自爆キーが効くため、"
                         "他のウィンドウを操作したまま自爆できます。\n\n"
                         "⚠ 複窓 (VRChatを2つ以上起動) では使用しないで"
                         "ください。送信されるキーはどのクライアントでも"
                         "同じため、フォーカスのあるVRChatで発動します。"
                         "意図していない方が自爆する可能性があります。\n\n"
                         "複窓で使う場合はこの設定をオフにしてください。"
                         "オフなら前面のVRChatだけが対象になるので、"
                         "自爆させたいウィンドウをクリックしてから"
                         "キーを押してください。"),
    "tip.skcancel":     ("Press this at any time to abort a self-destruct in "
                         "progress and release the key immediately. It also "
                         "blocks any further attempt for the rest of that "
                         "round, so a last-second change of mind sticks.",
                         "自爆中にこのキーを押すと即座に中止し、キーを離します。"
                         "そのラウンド中は再実行されないので、"
                         "直前で気が変わっても確実に止まります。"),
    "str.name":         ("Auto Round Starter", "自動ラウンド開始"),
    "str.blurb":        ("Runs a movement macro after a round ends to reach "
                         "and press the start button. Friends+ or private "
                         "instances only.",
                         "ラウンド終了後にマクロで移動し、スタートボタンを"
                         "押します。Friends+ 以下でのみ使用してください。"),
    "str.seq":          ("Movement sequence", "移動シーケンス"),
    "str.help":         ("drop = right click · use = left click · wait N · "
                         "jump · forward/back/left/right N = hold N seconds · "
                         "spam N = click repeatedly · left+use N = strafe AND "
                         "click together",
                         "drop = 右クリック · use = 左クリック · wait N = 待機 · "
                         "jump · forward/back/left/right N = N秒間移動 · "
                         "spam N = 連打 · left+use N = 横移動しながら連打"),
    "str.delay":        ("Wait before starting (s)", "開始までの待機 (秒)"),
    "tip.strdelay":     ("How long to wait after the round ends before the "
                         "macro runs.\n\n"
                         "RoundOver fires while you are still being returned "
                         "to the lobby, so starting immediately moves you "
                         "before you are back.",
                         "ラウンド終了後、マクロを実行するまでの待機時間です。"
                         "\n\n"
                         "RoundOver はロビーへ戻る前に発生するため、"
                         "すぐ動き出すと戻る前に動いてしまいます。"),
    "str.cancelmove":   ("Cancel if I move", "自分が動いたら中止"),
}


def t(key):
    pair = STRINGS.get(key)
    if not pair:
        return key
    return pair[0] if LANG == "en" else pair[1]


# ======================================================  oscquery  =========
# VRChat sends avatar data to 9001 only, UNLESS an app advertises itself via
# OSCQuery — then VRChat asks where to send and uses that app's own port. This
# is how ToN Overlay stopped fighting other tools for 9001, and it is the only
# way two OSC apps can receive avatar parameters at the same time.
WANTED_PARAMS = [("VelocityMagnitude", "f"), ("VelocityX", "f"),
                 ("VelocityY", "f"), ("VelocityZ", "f"), ("Grounded", "T")]


# Filled in the first time a running VRChat is seen, so a new one can be
# launched from the same place without asking where it is installed.
# What we launched, and with which ports. Reading them back from VRChat's
# command line does not work — the launcher starts the game as a separate
# process and the arguments are not visible there — so the ports we chose are
# written down instead. Shared by every copy of the toolkit.










def _node(path, contents=None, type_tag=None):
    n = {"FULL_PATH": path, "ACCESS": 0}
    if contents is not None:
        n["CONTENTS"] = contents
    if type_tag:
        n["ACCESS"], n["TYPE"] = 2, type_tag
    return n


class OSCQueryService:
    """Advertises this app so VRChat sends avatar parameters to our own port."""

    def __init__(self, name, osc_port, log):
        self.name, self.osc_port, self.log = name, osc_port, log
        self.http = self.zc = self.info = None


    def start(self):
        try:
            from zeroconf import ServiceInfo, Zeroconf
        except ImportError:
            self.log(t("err.port3"))
            return False
        import http.server
        import json as _json
        import socket as _socket

        params = {n: _node(f"/avatar/parameters/{n}", type_tag=tt)
                  for n, tt in WANTED_PARAMS}
        tree = _node("/", {"avatar": _node("/avatar", {
            "parameters": _node("/avatar/parameters", params)})})
        host_info = {"NAME": self.name, "OSC_IP": VRC_IP,
                     "OSC_PORT": self.osc_port, "OSC_TRANSPORT": "UDP",
                     "EXTENSIONS": {"ACCESS": True, "VALUE": True,
                                    "TYPE": True}}

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(inner):
                body = (host_info if "HOST_INFO" in (inner.path or "")
                        else tree)
                raw = _json.dumps(body).encode()
                inner.send_response(200)
                inner.send_header("Content-Type", "application/json")
                inner.send_header("Content-Length", str(len(raw)))
                inner.end_headers()
                inner.wfile.write(raw)

            def log_message(inner, *a):
                pass

        try:
            self.http = http.server.ThreadingHTTPServer((VRC_IP, 0), Handler)
            http_port = self.http.server_address[1]
            threading.Thread(target=self.http.serve_forever,
                             daemon=True).start()

            self.zc = Zeroconf()
            addr = _socket.inet_aton("127.0.0.1")
            self.info = ServiceInfo(
                "_oscjson._tcp.local.", f"{self.name}._oscjson._tcp.local.",
                addresses=[addr], port=http_port, properties={},
                server=f"{self.name}.local.")
            self.zc.register_service(self.info)
            self.osc_info = ServiceInfo(
                "_osc._udp.local.", f"{self.name}._osc._udp.local.",
                addresses=[addr], port=self.osc_port, properties={},
                server=f"{self.name}.local.")
            self.zc.register_service(self.osc_info)
            self.log(f"OSCQuery advertised on http {http_port}, "
                     f"osc {self.osc_port}")
            return True
        except Exception as e:
            self.log(f"OSCQuery failed: {e}")
            return False

    def stop(self):
        for svc in ("info", "osc_info"):
            try:
                if self.zc and getattr(self, svc, None):
                    self.zc.unregister_service(getattr(self, svc))
            except Exception:
                pass
        try:
            if self.zc:
                self.zc.close()
            if self.http:
                self.http.shutdown()
        except Exception:
            pass


# ===========================================================  core  =========
class Velocity:
    """Grounded speed from VRChat, with per-probe and per-lobby maxima."""

    def __init__(self, y_gate=0.25):
        self.y_gate = y_gate
        self._lock = threading.Lock()
        self._max = self._lobby_max = 0.0
        self._recent = []          # (time, speed) for the rolling-window max
        self.vy = self.current = 0.0
        self.grounded = True        # VRChat's own flag
        self.has_grounded = False   # does this avatar report it?
        self.vx = self.vz = 0.0
        self.sideways = False
        self.driven = False        # set by Core while a module moves you
        # VelocityX/Z are WORLD axes, so the |vx|>|vz| test only means
        # "sideways" when you happen to face along Z. During our own strafe we
        # know the truth, so Core states it instead of inferring it.
        self.force_sideways = False
        self.stable_since = self.last_update = 0.0
        self.stable_value = 0.0
        self.rejected = 0
        self.last_accepted = 0.0   # when a sample last got through the gates
        self.ever = False

    def handle(self, address, *args):
        if not args:
            return
        try:
            v = float(args[0])
        except (TypeError, ValueError):
            return
        with self._lock:
            if address.endswith("/Grounded"):
                self.grounded = bool(v)
                self.has_grounded = True
                return
            if address.endswith("/VelocityY"):
                self.vy = v
                return
            if address.endswith("/VelocityX"):
                self.vx = v
                return
            if address.endswith("/VelocityZ"):
                self.vz = v
                return
            if not address.endswith("/VelocityMagnitude"):
                return
            now = time.time()
            self.last_update = now
            self.ever = True
            # Grounded is VRChat's own state and beats inferring from
            # VelocityY, which can lag Magnitude — that lag is how falling
            # samples were slipping through and reading as a speed cap.
            airborne = ((self.has_grounded and not self.grounded)
                        or abs(self.vy) > self.y_gate)
            # Two exceptions, both about not getting STUCK on a stale value:
            #   * "stopped" is true whether or not you are on the ground, and
            #     discarding it leaves the last moving speed frozen forever;
            #   * if nothing has passed the gates for a while the gate itself
            #     is wrong (a Grounded flag stuck false rejects everything),
            #     so let a sample through rather than trust old data.
            stuck = self.last_accepted and now - self.last_accepted > 2.0
            if airborne and v > 0.25 and not stuck:
                self.rejected += 1
                return
            self.last_accepted = now
            # 8ページ caps SIDEWAYS movement at 6.50 while forward stays at
            # 6.60, so every sample has to be tagged with its direction --
            # a bare speed number cannot tell the two rounds apart.
            self.sideways = (True if self.force_sideways
                             else abs(self.vx) > 2.0 * abs(self.vz))
            if abs(v - self.stable_value) > STABLE_BAND:
                self.stable_value = v
                self.stable_since = time.time()
            self.current = v
            self._max = max(self._max, v)
            self._lobby_max = max(self._lobby_max, v)
            self._recent.append((now, v, self.sideways, self.driven))
            if len(self._recent) > 4000:
                self._recent = self._recent[-2000:]

    def reset_probe(self):
        with self._lock:
            self._max = 0.0
            self.rejected = 0

    def reset_lobby(self):
        with self._lock:
            self._lobby_max = 0.0

    def reset_recent(self):
        """
        Forget every past reading.

        Called when the start button is pressed: your speed only changes at
        that moment, so anything measured before it describes the old state and
        would wrongly veto the new one.
        """
        with self._lock:
            self._recent.clear()
            self._lobby_max = 0.0

    def probe_max(self):
        with self._lock:
            return self._max

    def lobby_max(self):
        with self._lock:
            return self._lobby_max

    def recent_max(self, window, sideways_only=False, ignore_above=None,
                   pct=0.90, exclude_driven=False, since=None):
        """
        Fastest speed in the last `window` seconds, optionally sideways only.

        `since` limits the ceiling to speeds observed since the current
        plateau began. A reading from BEFORE a step down describes the speed
        you used to have, not the one you have now — and when the master
        presses start mid-lobby that stale 6.60 would veto the 4.00 that
        follows it.

        `ignore_above` drops readings faster than flat ground allows: running
        downstairs reaches ~6.83 when your cap is 6.60, and such a reading is
        slope assistance, not proof you were uncapped. Counting it as a ceiling
        vetoes a correct 6.50 detection.

        Two reasons this is not a whole-lobby figure. Your speed only changes
        when the master presses start, so earlier movement would mask it. And
        in an 8ページ round you can still reach 6.60 going FORWARD, so a ceiling
        built from all directions would hide the 6.50 sideways cap entirely.
        """
        cutoff = time.time() - window
        if since:
            cutoff = max(cutoff, since)
        with self._lock:
            self._recent = [r for r in self._recent
                            if r[0] >= time.time() - window]
            vals = [v for t, v, side, drv in self._recent
                    if t >= cutoff and (side or not sideways_only)
                    and (ignore_above is None or v <= ignore_above)
                    and not (exclude_driven and drv)]
            if not vals:
                return 0.0
            if pct >= 1.0 or len(vals) < 8:
                return max(vals)
            # A percentile, not the maximum. Reversing direction produces a
            # single-frame spike (6.11 among a steady 5.82), and one such
            # sample as the ceiling vetoes a correct verdict for the whole
            # window. Anything that brief is not a speed you can sustain.
            vals.sort()
            return vals[min(len(vals) - 1, int(len(vals) * pct))]

    def plateau_held(self, window, target, tol, min_hold, sideways_only=False):
        """
        Was `target` HELD for min_hold seconds inside the last `window`?

        A peak is not evidence of a cap. A normal round that briefly undershoots
        touches 6.46 or 6.53 in passing, while an 8ページ round sits on 6.50 and
        stays there. Every false 8 PAGES alert so far came from reading a peak;
        none came from the live watch, which already demanded a plateau.
        """
        cutoff = time.time() - window
        with self._lock:
            rows = [r for r in self._recent
                    if r[0] >= cutoff and (r[2] or not sideways_only)]
        run_start = None
        for t, v, _side, _drv in rows:
            if abs(v - target) <= tol:
                if run_start is None:
                    run_start = t
                elif t - run_start >= min_hold:
                    return True
            else:
                run_start = None
        return False

    def time_at(self, window, target, tol, sideways_only=False):
        """
        TOTAL time the speed SAT on `target`, contiguous or not.

        VRChat sends a value only when it CHANGES, so a speed held at 6.50
        produces one sample and then silence — the dwell time is the gap AFTER
        that sample, until the next different reading. Summing gaps between
        pairs of matching samples (the obvious reading) measures almost
        nothing, because matching samples never come in pairs.

        Cumulative rather than contiguous because a strafing sweep reverses
        every leg, and each reversal would reset a run.
        """
        now = time.time()
        cutoff = now - window
        with self._lock:
            rows = [r for r in self._recent
                    if r[0] >= cutoff and (r[2] or not sideways_only)]
        total = 0.0
        for i, (t, v, _side, _drv) in enumerate(rows):
            if abs(v - target) > tol:
                continue
            nxt = rows[i + 1][0] if i + 1 < len(rows) else now
            total += min(nxt - t, window)      # dwell until the value changed
        return total

    def moving_sideways(self):
        with self._lock:
            return self.sideways

    STALE_AFTER = 8.0      # no sample for this long: the value means nothing

    def held(self):
        """
        (current speed, seconds it has stayed within STABLE_BAND).

        VRChat only sends on change, so silence usually means "still at that
        speed" — which is what plateau detection relies on. But silence lasting
        longer than a round of movement means the data stopped rather than
        settled, and acting on it produced a 5.43 m/s "cap" while standing
        still. Past that point the reading is reported as no data.
        """
        with self._lock:
            if self.stable_since == 0.0:
                return 0.0, 0.0
            if self.last_update and \
                    time.time() - self.last_update > self.STALE_AFTER:
                return 0.0, 0.0
            return self.current, time.time() - self.stable_since


class Core:
    """Shared OSC connection, log reader and event bus."""

    def __init__(self, log_fn):
        self.log = log_fn
        self.vel = Velocity()
        self.client = udp_client.SimpleUDPClient(VRC_IP, SEND_PORT)
        self.server = None
        self.stop_evt = threading.Event()
        self.busy = threading.Lock()      # only one module may move you
        self._driving = False             # a module is moving you right now
        self._drive_run = False           # ...and is it holding Run?
        self._drive_until = 0.0           # ignore readings until this time
        self.subscribers = []
        self.lobby = threading.Event()
        self.in_round = threading.Event()   # set between round start and end
        self.seq = {"state": "boot"}
        self.last_round = None
        self.item = ""                      # currently equipped pickup
        self.opted_in = True                # am I actually in the round?
        self.terror_ids = []                # this round's terrors, by id
        self.terrors_known = threading.Event()
        self.terrors_eta = 0.0              # when a hidden terror is revealed
        self.terrors_at = 0.0               # when it actually was revealed
        self.round_started_at = 0.0
        self._saw_not_opted = False         # seen since the last round start
        self.ui_refresh = None              # set by the App
        # Tk variables cannot be read before mainloop() starts or after it
        # ends. Module threads launch from __init__, which is earlier, so they
        # wait on this instead of racing the GUI.
        self.ui_ready = threading.Event()
        self.modules = []           # filled in by the App

    # -- events -------------------------------------------------------------
    def subscribe(self, fn):
        self.subscribers.append(fn)

    def emit(self, kind, **data):
        for fn in list(self.subscribers):
            try:
                fn(kind, data)
            except Exception as e:
                self.log(f"[module error] {e}")

    # -- lifecycle ----------------------------------------------------------


    def start(self):
        disp = Dispatcher()
        for p in ("VelocityMagnitude", "VelocityX", "VelocityY", "VelocityZ",
                  "Grounded"):
            disp.map(f"/avatar/parameters/{p}", self.vel.handle)
        self.oscq = None
        try:
            self.server = ThreadingOSCUDPServer((VRC_IP, LISTEN_PORT), disp)
        except OSError as e:
            # 9001 is taken. Instead of giving up, bind any free port and tell
            # VRChat about it through OSCQuery — both apps then receive data.
            self.log(f"[{LISTEN_PORT}] {e}")
            self.log(t("err.port"))
            who = self._who_has_port()
            if who:
                self.log(who)
            self.log(t("err.port2"))
            try:
                self.server = ThreadingOSCUDPServer((VRC_IP, 0), disp)
            except OSError as e2:
                self.log(f"No free port either: {e2}")
                return False
            port = self.server.server_address[1]
            self.oscq = OSCQueryService("ToNToolkit", port, self.log)
            if not self.oscq.start():
                self.server.server_close()
                return False
        return self._after_bind(disp)

    def _who_has_port(self):
        """Name the program holding 9001, so the fix is obvious."""
        try:
            out = subprocess.run(
                ["powershell", "-NoProfile", "-Command",
                 f"Get-NetUDPEndpoint -LocalPort {LISTEN_PORT} "
                 "-ErrorAction SilentlyContinue | ForEach-Object "
                 "{ (Get-Process -Id $_.OwningProcess).ProcessName }"],
                capture_output=True, text=True, timeout=6,
                creationflags=0x08000000)
            names = {n.strip() for n in out.stdout.splitlines() if n.strip()}
            if names:
                return f"Holding the port: {', '.join(sorted(names))}"
        except Exception:
            pass
        return ""

    def _after_bind(self, disp):
        self.release_all()          # clear anything a previous run left held
        threading.Thread(target=self.server.serve_forever, daemon=True).start()
        threading.Thread(target=self._tail_log, daemon=True).start()
        bound = self.server.server_address[1]
        how = "" if bound == LISTEN_PORT else " via OSCQuery"
        # Say which build this is: the personal-only features are invisible
        # otherwise, and "the option is missing" looks like a bug.
        # Public users should not be told about hidden features: just the
        # version. The personal build says so, which is useful to you.
        self.log(f"{APP_NAME} {APP_VERSION}"
                 + ("  (personal build)" if PERSONAL_BUILD else ""))
        self.log(f"OSC listening on {bound}{how}, sending to {SEND_PORT}")
        return True


    def shutdown(self):
        self.stop_evt.set()
        for a in list(DIRS.values()) + ["/input/Run", "/input/Jump"]:
            try:
                self.client.send_message(a, 0)
            except Exception:
                pass
        self.release_all()
        if getattr(self, "oscq", None):
            self.oscq.stop()
        if self.server:
            self.server.shutdown()

    # -- log ----------------------------------------------------------------

    def _newest_log(self):
        files = glob.glob(os.path.join(LOG_DIR, "output_log_*.txt"))
        return max(files, key=os.path.getmtime) if files else None

    def _tail_log(self):
        """
        Follow VRChat's newest log.

        Always seek to the end when opening: re-reading a file from the start
        replays every past round as if it were happening now.
        """
        path = self._newest_log()
        if not path:
            self.log(f"No VRChat log in {LOG_DIR}")
            return
        self.log(f"Reading {os.path.basename(path)}")
        f = open(path, encoding="utf-8", errors="replace")
        f.seek(0, os.SEEK_END)
        try:
            while not self.stop_evt.is_set():
                line = f.readline()
                if line:
                    self._handle(line.rstrip())
                    continue

                # A new log means VRChat restarted. Always seek to the end
                # so history is never replayed as live events.
                nxt = self._newest_log()
                if nxt and nxt != path:
                    f.close()
                    path = nxt
                    f = open(path, encoding="utf-8", errors="replace")
                    f.seek(0, os.SEEK_END)
                    self.log("--- log rotated ---")
                time.sleep(0.25)
        finally:
            f.close()
    def _handle(self, line):
        m = PICKUP.search(line)
        if m:
            self.item = m.group(1).strip()
            self.emit("item", name=self.item)
            return
        m = DROP.search(line)
        if m:
            if self.item == m.group(1).strip():
                self.item = ""
                self.emit("item", name="")
            return
        if ROUND_OVER in line:
            if self.in_round.is_set():
                self.in_round.clear()
                self.emit("round_over")
            return
        if DIED in line:
            self.emit("death")
            return
        if MASTER_SWITCH in line:
            # 6 of 6 master switches in the sample log were followed by a 特殊
            # round, so the "next must be 通常" guarantee no longer holds.
            if self.seq["state"] != "normal2":
                self.seq["state"] = "normal2"
                self.emit("master")
            return
        if NOT_OPTED in line:
            self._saw_not_opted = True
            if self.opted_in:
                self.opted_in = False
                self.emit("opt", opted_in=False)
            return
        if line.rstrip().endswith(OPTED_IN) and NOT_OPTED not in line:
            self.opted_in = True
            self.emit("opt", opted_in=True)
            return
        if VERIFIED_END in line:
            self.lobby.set()
            self.vel.reset_lobby()
            self.emit("lobby_start")
            return
        if ROUND_FETCH.search(line):
            self.emit("round_fetch")
            return
        m = KILLERS_LATER.search(line)
        if m:
            self.terrors_eta = time.time() + int(m.group(1))
            return
        m = KILLERS.search(line)
        if m:
            # Arrives ~10s after the round line; this is the only place the
            # terrors are named, and then only as ids.
            raw = [int(x) for x in m.group(1).split()]
            self.terror_ids = resolve_terror_ids(m.group(2).strip(), raw)
            self.terrors_at = time.time()
            self.terrors_known.set()
            self.emit("terrors", ids=self.terror_ids, round=m.group(2).strip())
            return
        m = ROUND_START.search(line)
        if m:
            self.lobby.clear()
            self.terror_ids = []
            self.terrors_known.clear()
            self.terrors_eta = 0.0
            self.terrors_at = 0.0
            self.round_started_at = time.time()
            # The opt-out line always precedes this one, so its ABSENCE means
            # you are in the round. Deciding it fresh each round means the
            # state is correct from the very first round after launch, with no
            # "unknown" period to guess through.
            now_in = not self._saw_not_opted
            self._saw_not_opted = False
            if now_in != self.opted_in:
                self.opted_in = now_in
                self.emit("opt", opted_in=now_in)
            name, map_name = m.group(3), m.group(1)
            self.last_round = name
            self.in_round.set()
            self._advance(name)
            # Logged here, not in a module: every copy should report its own
            # rounds whether or not the detector happens to be enabled.
            mark = "!!" if name in ALERT_NAMES else ""
            label = {"normal": "通常", "special": "特殊",
                     "unknown": "通常or特殊"}[self.predict()]
            note = ""
            self.log(f"{mark} {name} @ {map_name}  -> next: {label}{note}"
                     .strip())
            self.emit("round_start", name=name, map=map_name,
                      predict=self.predict())

    def _advance(self, name):
        special = name not in PLAIN_NAMES and name not in OVERRIDE_NAMES
        if self.seq["state"] == "boot" and not special:
            # Stay unanchored until a 特殊 appears: only then do we know where
            # in the cycle this instance actually is.
            return
        if name in OVERRIDE_NAMES:
            self.seq["state"] = "unknown"
        elif name in PLAIN_NAMES:
            self.seq["state"] = ("normal2" if self.seq["state"] == "normal1"
                                 else "normal1")
        else:
            self.seq["state"] = "special"

    def expected_speed(self, activated=False):
        """Top speed your current loadout should reach."""
        pair = ITEM_SPEED.get(self.item, ITEM_SPEED[""])
        return pair[1] if activated else pair[0]

    def item_boosts_on_use(self):
        """True when the held item only gives speed while the use key is down."""
        pair = ITEM_SPEED.get(self.item, ITEM_SPEED[""])
        return pair[1] > pair[0] + 0.05

    def module_on(self, key):
        """Is another module currently enabled? Used to avoid collisions."""
        for m in self.modules:
            if m.key == key:
                return m.is_on()
        return False

    def request_refresh(self):
        """Ask the GUI to rebuild its tabs, from any thread."""
        if self.ui_refresh:
            try:
                self.ui_refresh()
            except Exception:
                pass

    def predict(self):
        # "boot" reports UNKNOWN, not 通常. Assuming 通常 is only right for a
        # brand-new instance where 特殊 has not unlocked yet; joining an
        # existing public instance drops you at an unknown point in the cycle,
        # and claiming 通常 there is a guess dressed up as a fact.
        return {"special": "normal", "normal2": "special",
                "normal1": "unknown", "boot": "unknown"
                }.get(self.seq["state"], "unknown")

    # -- movement (serialised so modules never fight) -----------------------
    def probe(self, direction, hold, use_run=True, activate=False):
        """Hold one direction, return (max speed, airborne samples)."""
        with self.busy:
            self._drive_start(use_run)
            addr = DIRS[direction]
            if activate:
                self.client.send_message(USE_INPUT, 1)
            if use_run:
                self.client.send_message("/input/Run", 1)
                time.sleep(0.12)
            self.vel.reset_probe()
            self.client.send_message(addr, 1)
            t0 = last = time.time()
            try:
                while time.time() - t0 < hold:
                    if use_run and time.time() - last > 0.2:
                        self.client.send_message("/input/Run", 1)
                        last = time.time()
                    time.sleep(0.02)
            finally:
                self.client.send_message(addr, 0)
                if use_run:
                    self.client.send_message("/input/Run", 0)
                if activate:
                    self.client.send_message(USE_INPUT, 0)
                self.vel.force_sideways = False
                self._drive_end()
            time.sleep(0.08)
            return self.vel.probe_max(), self.vel.rejected

    def probe_oscillate(self, total, step=0.45, use_run=True, activate=False,
                        first="left"):
        """
        Strafe left-right-left-right, the way you check by hand.

        A single long hold drifts you across the lobby and into walls, which
        reads low. Alternating keeps you roughly in place while still reaching
        the cap, and the running max is taken across the WHOLE sweep rather
        than per leg, so the acceleration ramp at each reversal costs nothing.
        """
        with self.busy:
            self._drive_start(use_run)
            self.vel.force_sideways = True      # we are strafing, by design
            self.vel.reset_probe()
            if activate:
                self.client.send_message(USE_INPUT, 1)
            if use_run:
                self.client.send_message("/input/Run", 1)
                time.sleep(0.10)
            t0 = last_run = time.time()
            i = 0
            addr = None
            try:
                while time.time() - t0 < total:
                    # Which side it starts on decides where you end up when
                    # the sweep has an odd number of legs.
                    other = "right" if first == "left" else "left"
                    addr = DIRS[first if i % 2 == 0 else other]
                    self.client.send_message(addr, 1)
                    leg = time.time()
                    while (time.time() - leg < step
                           and time.time() - t0 < total):
                        if use_run and time.time() - last_run > 0.2:
                            self.client.send_message("/input/Run", 1)
                            last_run = time.time()
                        time.sleep(0.02)
                    self.client.send_message(addr, 0)
                    i += 1
            finally:
                for d in DIRS.values():
                    self.client.send_message(d, 0)
                if use_run:
                    self.client.send_message("/input/Run", 0)
                if activate:
                    self.client.send_message(USE_INPUT, 0)
                self.vel.force_sideways = False
                self._drive_end()
            time.sleep(0.08)
            return self.vel.probe_max(), self.vel.rejected

    def release_all(self):
        """
        Send 0 for every input we ever hold.

        A macro that is interrupted — or two copies of the toolkit aimed at the
        same OSC port — can leave a direction stuck down, and VRChat keeps
        walking until something clears it. Cheap to send, so it runs at
        startup, after every macro, and on shutdown.
        """
        try:
            for addr in list(DIRS.values()) + ["/input/Run", "/input/Jump",
                                               USE_INPUT, DROP_INPUT]:
                self.client.send_message(addr, 0)
        except Exception:
            pass

    def macro_move(self, direction, seconds, use_run=False,
                   spam_use=False, rate=0.12):
        """
        Hold a direction, optionally clicking repeatedly the whole time.

        Spamming while still moving is what makes the button press reliable:
        one click at a fixed moment either lands or it doesn't, whereas a
        stream of clicks across the approach covers the whole window in which
        you are actually in range.
        """
        with self.busy:
            self._drive_start(use_run)
            addr = DIRS[direction]
            if use_run:
                self.client.send_message("/input/Run", 1)
            self.client.send_message(addr, 1)
            t0 = last_run = time.time()
            try:
                while time.time() - t0 < seconds:
                    if use_run and time.time() - last_run > 0.2:
                        self.client.send_message("/input/Run", 1)
                        last_run = time.time()
                    if spam_use:
                        # Hold each press long enough to register. rate/2 was
                        # 60ms by default, short enough for VRChat to miss it.
                        self.client.send_message(USE_INPUT, 1)
                        time.sleep(max(MIN_PRESS, rate / 2))
                        self.client.send_message(USE_INPUT, 0)
                        time.sleep(max(0.04, rate / 2))
                    else:
                        time.sleep(0.02)
            finally:
                self.client.send_message(addr, 0)
                self.client.send_message(USE_INPUT, 0)
                if use_run:
                    self.client.send_message("/input/Run", 0)
                self._drive_end()

    def spam_click(self, seconds, rate=0.12):
        with self.busy:
            t0 = time.time()
            clicks = 0
            try:
                # Always land at least one full click, however short the step.
                while time.time() - t0 < seconds or clicks == 0:
                    self.client.send_message(USE_INPUT, 1)
                    time.sleep(max(MIN_PRESS, rate / 2))
                    self.client.send_message(USE_INPUT, 0)
                    time.sleep(max(0.04, rate / 2))
                    clicks += 1
            finally:
                self.client.send_message(USE_INPUT, 0)

    def is_driving(self):
        """
        True only while scripted movement is UNUSABLE for detection.

        Walking (Run off) tops out around 4.00 and would read as a cap, so it
        must be ignored. Movement with Run held reaches your real ceiling and
        is perfectly good data — ignoring it just delays detection until you
        happen to move yourself.
        """
        if self._driving:
            return not self._drive_run
        return time.time() < self._drive_until

    def _drive_start(self, use_run=False):
        self._driving = True
        self._drive_run = bool(use_run)
        self.vel.driven = True

    def _drive_end(self, settle=0.8):
        self._driving = False
        self.vel.driven = False
        # Only quarantine the aftermath of unusable (walking) movement.
        self._drive_until = 0.0 if self._drive_run else time.time() + settle
        self._drive_run = False

    def tap(self, address, hold=0.1):
        with self.busy:
            self.client.send_message(address, 1)
            time.sleep(hold)
            self.client.send_message(address, 0)

    def wait_still(self, limit=0.30, timeout=2.5):
        t0 = time.time()
        while time.time() - t0 < timeout:
            self.vel.reset_probe()
            time.sleep(0.25)
            if self.vel.probe_max() < limit:
                return True
        return False


# ========================================================  modules  =========
class Module:
    """Base class. Subclasses declare settings and react to core events."""
    key = "module"          # stable id for the settings file — never translated
    name_key = ""
    blurb_key = ""
    tab_key = ""            # modules sharing a tab_key share one tab
    tip_key = ""            # hover help shown on the Enabled checkbox
    # Keys NOT shown in the UI. They are never loaded from or written to the
    # settings file, so editing a default in code actually takes effect —
    # otherwise a value saved months ago silently overrides it forever.
    code_only = ()
    # Key prefixes that are deliberately NOT written to the settings file, so
    # they start fresh every launch.
    volatile = ()
    defaults = {}

    @property
    def name(self):
        return t(self.name_key)

    @property
    def blurb(self):
        return t(self.blurb_key)

    def __init__(self, core, log):
        self.core, self.log = core, log
        self.enabled = tk.BooleanVar(value=False)
        self.vars = {}
        for k, v in self.defaults.items():
            self.vars[k] = (tk.BooleanVar(value=v) if isinstance(v, bool)
                            else tk.StringVar(value=str(v)))
        core.subscribe(self._route)

    def get(self, key, cast=float):
        try:
            v = self.vars[key].get()
        except (RuntimeError, tk.TclError):
            # GUI not up yet, or already torn down: fall back to the default.
            v = self.defaults.get(key)
        if isinstance(v, bool):
            return v
        try:
            return cast(v)
        except (TypeError, ValueError):
            return cast(self.defaults[key])

    def is_on(self):
        """Enabled state, safe to call from any thread at any time."""
        try:
            return bool(self.enabled.get())
        except (RuntimeError, tk.TclError):
            return False

    def _route(self, kind, data):
        if self.is_on():
            self.on_event(kind, data)

    def on_event(self, kind, data):
        pass

    def build(self, parent):
        """Override to add setting widgets."""

    def after_load(self):
        """Called once the settings file has been applied."""

    def key_row(self, parent, label_key, key, tip=None):
        """A binding row: shows the key, click to rebind, Reset restores it."""
        f = ttk.Frame(parent)
        f.pack(fill="x", pady=1)
        mark = "  ⍰" if tip else ""
        lbl = ttk.Label(f, text=t(label_key) + mark, width=32, anchor="w")
        lbl.pack(side="left")
        if tip:
            Tip(lbl, t(tip))
        btn = ttk.Button(f, width=12)

        def show():
            btn.configure(text=self.vars[key].get() or t("key.set"))

        def grab():
            KeyGrab(parent.winfo_toplevel(),
                    lambda tok: (self.vars[key].set(tok), show()))

        btn.configure(command=grab)
        show()
        btn.pack(side="left")
        ttk.Button(f, text=t("key.reset"), width=8,
                   command=lambda: (self.vars[key].set(self.defaults[key]),
                                    show())).pack(side="left", padx=4)
        return f

    def row(self, parent, label_key, key, width=6, tip=None):
        f = ttk.Frame(parent)
        f.pack(fill="x", pady=1)
        mark = "  ⍰" if tip else ""
        lbl = ttk.Label(f, text=t(label_key) + mark, width=32, anchor="w")
        lbl.pack(side="left")
        if tip:
            Tip(lbl, t(tip))
        if isinstance(self.vars[key], tk.BooleanVar):
            # Same Canvas check as the Enabled rows, so every tick box in the
            # app looks identical rather than mixing two styles.
            Toggle(f, self.vars[key]).pack(side="left")
        else:
            ttk.Entry(f, textvariable=self.vars[key], width=width).pack(side="left")
        return f







class AfkJumper(Module):
    key = "afk"
    name_key, blurb_key = "afk.name", "afk.blurb"
    tab_key = "tab.helper"
    defaults = {"idle": 60.0}
    MOVE_SPEED = MOVING_SPEED     # above this counts as you moving

    def __init__(self, core, log):
        super().__init__(core, log)
        self.round_stop = threading.Event()

    def build(self, parent):
        self.row(parent, "afk.idle", "idle")

    def on_event(self, kind, data):
        if kind == "round_start":
            if not self.core.opted_in:
                # Sitting in the respawn area: you are not in the match, so
                # there is no AFK timer to beat and jumping there is pointless.
                self.log("AFK helper: not in this round — no jumping")
                return
            self.round_stop.clear()
            threading.Thread(target=self._round_loop, daemon=True).start()
        elif kind in ("round_over", "death"):
            self.round_stop.set()      # dead or round finished: nothing to do
        elif kind == "opt":
            if not data.get("opted_in"):
                self.round_stop.set()
            else:
                self.log("AFK helper: opted back in")

    def _round_loop(self):
        """
        Idle-driven: the timer only runs while you are standing still.

        Silent by design — it runs every round and logging it would bury the
        round and speed messages that actually need reading.

        A jump cannot reset its own timer: Velocity discards samples taken
        while you are off the ground, so the jump's vertical motion never
        registers as movement.
        """
        idle = max(10.0, self.get("idle"))
        last_move = time.time()
        while not self._stop():
            speed, _ = self.core.vel.held()
            if speed > self.MOVE_SPEED:
                last_move = time.time()
            elif time.time() - last_move >= idle:
                self.core.tap("/input/Jump")
                last_move = time.time()
            time.sleep(0.5)

    def _stop(self):
        return (self.round_stop.is_set() or self.core.stop_evt.is_set()
                or not self.is_on() or not self.core.in_round.is_set()
                or not self.core.opted_in)


class SpeedDetector(Module):
    key = "speed"
    name_key, blurb_key = "spd.name", "spd.blurb"
    tab_key = "tab.helper"
    code_only = ("fast_hold", "fast_step", "eight",
                 "eight_tol", "split", "short_by",
                 "activate_item", "live_watch", "live_hold", "cap_tol",
                 "cap_window", "beep", "trust_seq",
                 "recheck_after", "punish_hold")
    defaults = {
        "auto_probe": False, "probe_hold": 1.5, "probe_step": 0.60,
        # 8 Pages caps sideways speed at exactly 6.50. The old ±0.03 also took
        # 6.47-6.53, so a 6.51 plateau set off the alarm. ±0.005 accepts only
        # readings that display as 6.50.
        "eight": 6.50, "eight_tol": 0.005, "split": 6.55,
        "short_by": 0.60, "activate_item": False,
        "live_watch": True, "live_hold": 0.45, "cap_tol": 0.06,
        "cap_window": 15.0,
        "beep": True, "beep_volume": 60.0, "eight_only": False,
        "snd_eight": find_sound("8ページ.wav", "8pages.wav"),
        "snd_punish": find_sound("パニッシュ.wav", "punish.wav"),
        "debug": False,
        "hotkey": "Q",
        # After our own macro the cap is already live, so the sweep only has to
        # confirm it — fewer, longer legs instead of a long careful survey.
        "fast_hold": 1.30, "fast_step": 0.65,
        # 0 disables the automatic second probe: the hotkey is a better answer,
        # because you can see when the master actually presses start.
        "recheck_after": 0.0,
        # A punish cap persists for as long as you keep moving. A deceleration
        # step or a slope touches the same value for a few tenths and moves on,
        # which is what most false punishes were.
        "punish_hold": 1.20,
        # Cumulative time the speed must sit on 6.50 across the whole sweep.
        # Low on purpose: missing an 8ページ round costs more than a false
        # alarm you can dismiss, so a brief touch is enough to call it.
        "settle_total": 0.38,
        "cancel_on_move": True,
        "trust_seq": True,
    }
    MOVE_THRESH = MOVING_SPEED   # your movement above this cancels a check

    def __init__(self, core, log):
        super().__init__(core, log)
        self.fired = threading.Event()
        self.announced = None
        self.alerted = set()        # labels already announced THIS lobby
        self._logged = 0.0
        self.moved = threading.Event()
        self.watch_stop = threading.Event()
        self.watching = False
        self._slow_since = None     # when the speed last went below the cap
        self.probing = False        # one probe at a time, whatever fires it
        threading.Thread(target=self._live, daemon=True).start()
        threading.Thread(target=self._hotkey_loop, daemon=True).start()

    def _diagnose(self, val, held, side_now, win, exp):
        """
        One line per plateau with every input to the decision.

        Printed once per plateau, not per poll: a plateau is the only moment a
        verdict can be reached, so this shows exactly why one was or was not.
        """
        eight, tol = self.get("eight"), self.get("eight_tol")
        short = self.get("short_by")
        cap = exp + SLOPE_MARGIN
        since = self.core.vel.stable_since
        side_max = self.core.vel.recent_max(win, sideways_only=True,
                                            ignore_above=cap,
                                            exclude_driven=True, since=since)
        all_max = self.core.vel.recent_max(win, ignore_above=cap,
                                           exclude_driven=True, since=since)
        bits = [f"speed {val:.2f} held {held:.1f}s",
                f"dir {'side' if side_now else 'fwd'}",
                f"max {win:.0f}s: side {side_max:.2f} all {all_max:.2f}",
                f"expected {exp:.2f} ({self.core.item or 'no item'})"]

        if abs(val - eight) > tol:
            eight_why = (f"no (need exactly {eight:.2f})" if tol < 0.01 else
                         f"no (need {eight - tol:.2f}-{eight + tol:.2f})")
        elif all_max > eight + self.get("cap_tol"):
            eight_why = f"no ({all_max:.2f} seen, above the cap)"
        else:
            eight_why = "YES"

        if self.get("trust_seq") and self.core.seq["state"] == "special":
            pun_why = "no (next round must be 通常, パニッシュ impossible)"
        elif val >= exp - short:
            pun_why = f"no (need below {exp - short:.2f})"
        elif all_max > exp - short:
            pun_why = f"no ({all_max:.2f} seen, above the cap)"
        else:
            pun_why = "YES"

        self.log(" | ".join(bits) + f"  ->  8P: {eight_why}  ·  PUNISH: {pun_why}")

    def build(self, parent):
        self.key_row(parent, "spd.hotkey", "hotkey", tip="tip.hotkey")
        self.row(parent, "spd.auto_probe", "auto_probe", tip="tip.auto")
        self.row(parent, "spd.p8only", "eight_only", tip="tip.p8only")
        self.row(parent, "spd.probe_hold", "probe_hold", tip="tip.sweep")
        self.row(parent, "spd.probe_step", "probe_step", tip="tip.leg")
        self.row(parent, "spd.settle", "settle_total", tip="tip.settle")
        vf = ttk.Frame(parent)
        vf.pack(fill="x", pady=(4, 1))
        ttk.Label(vf, text=t("spd.vol"), width=24, anchor="w").pack(side="left")
        self.vol_lbl = ttk.Label(vf, text="", width=4, anchor="e")
        scale = ttk.Scale(vf, from_=0, to=100, orient="horizontal",
                          command=self._vol_moved)
        scale.set(self.get("beep_volume"))
        scale.pack(side="left", fill="x", expand=True, padx=(0, 6))
        self.vol_lbl.pack(side="left")
        self._vol_moved(scale.get())
        for lbl, key in (("spd.snd8", "snd_eight"),
                         ("spd.sndp", "snd_punish")):
            g = ttk.Frame(parent)
            g.pack(fill="x", pady=1)
            ttk.Label(g, text=t(lbl), width=24, anchor="w").pack(side="left")
            ttk.Entry(g, textvariable=self.vars[key]).pack(
                side="left", fill="x", expand=True)
            ttk.Button(g, text=t("spd.browse"), width=3,
                       command=lambda k=key: self._pick_sound(k)
                       ).pack(side="left", padx=2)
            ttk.Button(g, text=t("spd.vtest"), width=6,
                       command=lambda k=key: play_sound(
                           self.vars[k].get(), self.get("beep_volume") / 100.0,
                           self.log)).pack(side="left")
        ttk.Label(parent, style="Muted.TLabel",
                  text=t("spd.sndhint")).pack(fill="x", pady=(0, 4))
        self.row(parent, "spd.cancel", "cancel_on_move")
        self.row(parent, "spd.debug", "debug")

    # -- classification -----------------------------------------------------
    def classify(self, v, sideways=True, activated=False):
        """
        Punish is a CAP, not a speed. It shows as 4.00, 5.90, or even 6.60
        while holding a coil that should reach 10.20 — the constant is that you
        fall short of your loadout, so the test is relative, not absolute.

        8ページ is absolute and directional: sideways pins to 6.50 exactly while
        forward still reaches 6.60.
        """
        if v <= 0.10:
            return "NO DATA"
        expected = self.core.expected_speed(activated)
        if sideways and abs(v - self.get("eight")) <= self.get("eight_tol"):
            return "8 PAGES"
        if v < expected - self.get("short_by"):
            return "SLOWED"
        return "NORMAL"

    def after_load(self):
        """Re-detect an alert clip whose saved path no longer exists."""
        for key, names in (("snd_eight", ("8ページ.wav", "8pages.wav")),
                           ("snd_punish", ("パニッシュ.wav", "punish.wav"))):
            p = self.vars[key].get()
            if not p or not os.path.isfile(p):
                found = find_sound(*names)
                if found:
                    self.vars[key].set(found)

    def _vol_moved(self, value):
        """Slider position -> the stored 0-100 value, shown as a number."""
        v = round(float(value))
        self.vars["beep_volume"].set(str(float(v)))
        try:
            self.vol_lbl.configure(text=f"{v}")
        except Exception:
            pass

    def _pick_sound(self, key):
        p = filedialog.askopenfilename(
            title=t("spd.snd8"),
            filetypes=[("Sound", "*.wav *.mp3"), ("WAV", "*.wav"),
                       ("MP3", "*.mp3"), ("All", "*.*")])
        if p:
            self.vars[key].set(p)

    def alert(self, text, kind=None):
        self.log(text)
        if kind == "PUNISH" and self.get("eight_only"):
            return          # identified and logged, just not announced
        if not self.get("beep"):
            return
        vol = self.get("beep_volume") / 100.0
        key = "snd_punish" if kind == "PUNISH" else "snd_eight"
        play_sound(self.vars[key].get(), vol, self.log)

    # -- events -------------------------------------------------------------
    def on_event(self, kind, data):
        if kind == "lobby_start":
            self.fired.clear()
            self.announced = None
            self.alerted.clear()
            self._slow_since = None
            self._start_watch()
        elif kind == "pressed":
            # Fired by the round starter right after IT pressed the button.
            self.fired.clear()
            self.moved.clear()
            self.watch_stop.set()
            self.run_probe("after start")
        elif kind == "master":
            self.log("master changed — 特殊 now possible, checks re-enabled")
        elif kind == "round_fetch":
            # Button pressed: the speed cap applies from here, so throw away
            # everything measured before it. `alerted` is deliberately NOT
            # cleared — the fetch can land between two plateaus and you would
            # get the same verdict beeped twice.
            self.core.vel.reset_recent()
            self.announced = None
            if self.get("auto_probe"):
                self.run_probe("auto")        # the round line is logged by the core, for every copy

    def _hotkey_loop(self):
        """
        Run a check the moment YOU press the key.

        The fetch event fires anywhere from 6 to 22 seconds before the round,
        so an automatic probe often measures the speed before the master has
        pressed start. You can see when they press; the app cannot.
        """
        was_down = False
        while not self.core.stop_evt.is_set():
            if not self.core.ui_ready.wait(timeout=0.5):
                continue
            # NOT [:1] — a binding can be a token like "Mouse4" or "F13",
            # and truncating it to one character turned Mouse4 into "M".
            ch = self.vars["hotkey"].get().strip() or "Q"
            # Same rule the AFK helper uses: sitting in the respawn area
            # means the next round is not yours, so a check would move you
            # for nothing.
            if ch and self.is_on() and self.core.lobby.is_set() \
                    and self.core.opted_in:
                down = key_is_down(ch)
                if down and not was_down:
                    self.fired.clear()       # a manual press always runs
                    self.moved.clear()
                    self.run_probe("hotkey")
                was_down = down
            else:
                was_down = False
            time.sleep(0.05)

    def _start_watch(self):
        """Watch for YOUR movement, same as the round starter does."""
        if self.watching or not self.get("cancel_on_move"):
            return
        self.watching = True
        self.watch_stop.clear()
        self.moved.clear()

        def watch():
            try:
                while not (self.watch_stop.is_set()
                           or self.core.stop_evt.is_set()):
                    if not self.core.lobby.is_set():
                        return
                    speed, _ = self.core.vel.held()
                    if speed > self.MOVE_THRESH and not self.core.is_driving():
                        self.moved.set()
                        return
                    time.sleep(0.1)
            finally:
                self.watching = False

        threading.Thread(target=watch, daemon=True).start()

    def run_probe(self, source):
        if self.probing or self.fired.is_set() or not self.core.lobby.is_set():
            return
        if source == "auto" and self.core.module_on("starter"):
            # Both walk you around the lobby; together they push you off the
            # start button. The starter has its own post-press check and the
            # manual key still works, so nothing is lost by standing down.
            if self.announced != "collide":
                self.announced = "collide"
                self.log(t("spd.collide"))
            self.fired.set()
            return
        if not self.core.opted_in:
            # Same rule the AFK helper uses: you are sitting in the respawn
            # area, so the next round's type is no concern of yours.
            self.log("auto detection: not in this round — no check")
            self.fired.set()
            return
        # NO skip on a guaranteed-通常 slot. 8ページ is an OVERRIDE round: it
        # can appear in any slot including that one, and skipping there missed
        # a real 8ページ straight after a ブラッドバス. Only パニッシュ is bound by
        # the sequence, and trust_seq already suppresses that verdict alone.
        if (source == "auto" and self.get("cancel_on_move")
                and self.moved.is_set()):
            # You are already moving, so the live watch is seeing real speed
            # data. Walking you around on top of that would be pointless.
            self.log("auto detection: you are moving — check skipped")
            self.fired.set()
            return
        self.fired.set()
        self.watch_stop.set()       # from here the probe drives, not you
        self.log("auto detection: checking speed")
        threading.Thread(target=self._probe_now, args=(source,),
                         daemon=True).start()

    def _probe_now(self, source):
        self.probing = True
        try:
            return self._probe_body(source)
        finally:
            self.probing = False

    def _probe_body(self, source):
        # The settle wait exists because YOUR movement is unpredictable. On
        # the "after start" path the macro just released the keys itself and
        # release_all() cleared them, so there is nothing to wait for — and
        # every tenth of a second here delays the verdict the master needs.
        fast = source == "after start"
        if not fast:
            self.core.wait_still(timeout=2.5)
        # Activating a click-to-boost item WIDENS the gap: normal gives ~15.30,
        # while a punish cap holds you at 6.60 however hard you click.
        act = self.get("activate_item") and self.core.item_boosts_on_use()
        hold = (max(0.6, self.get("fast_hold")) if fast
                else max(0.6, self.get("probe_hold")))
        step = (self.get("fast_step") if fast
                else max(0.15, self.get("probe_step")))
        # The round starter's own check sweeps RIGHT first; every other check
        # starts left. After the macro you are stood at the button, and going
        # left first would walk you back the way you came.
        first = "right" if fast else "left"
        raw, air = self.core.probe_oscillate(hold, step=step, activate=act,
                                             first=first)
        exp = self.core.expected_speed(act)
        # Re-derive the peak ignoring anything faster than flat ground allows.
        # VelocityY can lag VelocityMagnitude, so a falling sample sometimes
        # slips past the Y gate and shows up as 7.76 or 9.58 against a 6.60 cap.
        if raw > exp + FALL_LIMIT:
            self.log(f"{source} probe discarded — {raw:.2f} m/s means you were "
                     f"falling, not moving")
            return
        top = self.core.vel.recent_max(hold + 0.4,
                                       ignore_above=exp + SLOPE_MARGIN) or raw
        if raw > top + 0.05:
            self.log(f"  ignored {raw:.2f} m/s — downhill")
        # Ask the plateau FIRST. A slope bump to 6.55 pushes the peak outside
        # the 8ページ window even when the speed sat on 6.50 throughout, and the
        # sustained value is the one that means anything here.
        #
        # CUMULATIVE time, not a contiguous run: the sweep reverses every leg
        # and each reversal resets a run, so with 0.5s legs a contiguous
        # plateau is arithmetically impossible even in a real 8ページ round.
        at_cap = self.core.vel.time_at(hold + 0.4, self.get("eight"),
                                       self.get("eight_tol"),
                                       sideways_only=True)
        if at_cap >= self.get("settle_total"):
            top = self.get("eight")
            verdict = "8 PAGES"
            self.log(f"  held {self.get('eight'):.2f} for {at_cap:.2f}s "
                     f"across the sweep — 8 Page")
        else:
            verdict = self.classify(top, sideways=True, activated=act)
        if verdict == "8 PAGES" and at_cap < self.get("settle_total"):
            self.log(f"  {top:.2f} only touched for {at_cap:.2f}s — "
                     f"not calling it 8 Page")
            verdict = "NORMAL"
        if (verdict == "SLOWED" and self.get("trust_seq")
                and self.core.seq["state"] == "special"):
            verdict = "NORMAL (次は通常)"
        item = self.core.item or "no item"
        tag = f", {air} airborne" if air else ""
        how = " +use" if act else ""
        self.log(f"{source} probe{how}: {top:.2f} m/s (expected {exp:.2f}"
                 f" with {item}) -> {verdict}{tag}")
        if verdict in ("8 PAGES", "SLOWED"):
            self.alert(f"!! {verdict} — {top:.2f} m/s !!",
                       "8 PAGES" if verdict == "8 PAGES" else "PUNISH")
            return

        # NORMAL is the answer that can be stale: the fetch can fire well
        # before the master actually presses, so this probe may have measured
        # the speed BEFORE the cap applied. Check again shortly after. A capped
        # round cannot read normal twice.
        delay = self.get("recheck_after")
        if source == "auto" and delay > 0 and verdict == "NORMAL":
            # Re-arm the movement watcher: it was stopped for the first probe,
            # so without this the re-check could never see you take over.
            self._start_watch()
            if self.core.stop_evt.wait(delay):
                return
            if not self.core.lobby.is_set() or not self.is_on():
                return          # round already started, or module turned off
            if self.get("cancel_on_move") and self.moved.is_set():
                self.log("auto detection: you are moving — re-check skipped")
                return          # you took over; the live watch has it
            self.watch_stop.set()       # the re-check drives from here
            self.log("auto detection: re-checking, round has not started yet")
            self.core.wait_still()
            act2 = self.get("activate_item") and self.core.item_boosts_on_use()
            hold2 = max(0.6, self.get("probe_hold"))
            raw2, air2 = self.core.probe_oscillate(
                hold2, step=max(0.15, self.get("probe_step")), activate=act2,
                first=first)
            exp2 = self.core.expected_speed(act2)
            if raw2 > exp2 + FALL_LIMIT:
                self.log(f"re-check discarded — {raw2:.2f} m/s means falling")
                return
            again = self.core.vel.recent_max(
                hold2 + 0.4, ignore_above=exp2 + SLOPE_MARGIN) or raw2
            v2 = self.classify(again, sideways=True, activated=act2)
            if v2 == "8 PAGES" and self.core.vel.time_at(
                    hold2 + 0.4, self.get("eight"), self.get("eight_tol"),
                    sideways_only=True) < self.get("settle_total"):
                self.log(f"  {again:.2f} never settled — not 8 Page")
                v2 = "NORMAL"
            self.log(f"re-check: {again:.2f} m/s -> {v2}"
                     + (f", {air2} airborne" if air2 else ""))
            if v2 in ("8 PAGES", "SLOWED") and v2 not in self.alerted:
                self.alerted.add(v2)
                self.alert(f"!! {v2} — {again:.2f} m/s (re-check) !!",
                           "8 PAGES" if v2 == "8 PAGES" else "PUNISH")

    def _live(self):
        """Passive: alert when speed HOLDS at a cap and nothing was faster."""
        while not self.core.stop_evt.is_set():
            if not self.core.ui_ready.wait(timeout=0.5):
                continue
            if not (self.is_on() and self.get("live_watch")
                    and self.core.lobby.is_set()) or self.core.is_driving():
                time.sleep(0.3)
                continue
            val, held = self.core.vel.held()
            win = max(3.0, self.get("cap_window"))
            side_now = self.core.vel.moving_sideways()
            exp = self.core.expected_speed()   # passive: we are not clicking
            short = self.get("short_by")

            if (self.get("debug") and val > 0.5
                    and held >= self.get("live_hold")
                    and self.core.vel.stable_since != self._logged):
                self._logged = self.core.vel.stable_since
                self._diagnose(val, held, side_now, win, exp)
            for target, tol, label, need_side in (
                    (self.get("eight"), self.get("eight_tol"), "8 PAGES", True),
                    (None, 0.0, "PUNISH", False)):
                if target is None:
                    # パニッシュ is a 特殊 round, so it cannot follow one — the
                    # next round is guaranteed 通常. That matters because walk
                    # speed is 4.00, exactly what a punish cap reads, and after
                    # a 特殊 round your items are gone so you often walk.
                    #
                    # Test the sequence state directly, NOT predict(): that
                    # also answers "normal" from the boot state, before any 特殊
                    # has been seen, which silently disabled punish detection
                    # for the first part of every session.
                    if (self.get("trust_seq")
                            and self.core.seq["state"] == "special"):
                        if self.announced != "seq":
                            self.announced = "seq"
                            self.log("punish ignored — a 特殊 round just ended, "
                                     "so the next one must be 通常")
                        break
                    # Any sustained plateau meaningfully below what this
                    # loadout should reach: covers 4.00, 5.90 and the 6.60
                    # that means a coil is being suppressed.
                    # "stayed slow", not "held one exact number". A real cap
                    # wobbles a little (4.50 / 4.73 / 4.50) and a plateau timer
                    # restarts on every wobble, so it never accumulates.
                    slow = 0.5 < val < exp - short
                    if not slow:
                        self._slow_since = None
                    elif self._slow_since is None:
                        self._slow_since = time.time()
                    low_for = (time.time() - self._slow_since
                               if self._slow_since else 0.0)
                    if slow and low_for >= self.get("punish_hold"):
                        # Exclude our own probe: it may have run BEFORE the
                        # button press, measuring the old uncapped speed, and
                        # that stale reading would veto a correct detection.
                        top = self.core.vel.recent_max(
                            win, ignore_above=exp + SLOPE_MARGIN,
                            exclude_driven=True,
                            since=self.core.vel.stable_since)
                        if top > exp - short:
                            # Never fail silently: this branch used to reject
                            # a correct reading with no message at all.
                            if (self.announced != f"skip{label}"
                                    and label not in self.alerted):
                                self.announced = f"skip{label}"
                                self.log(f"{label} at {val:.2f} ignored — "
                                         f"{top:.2f} seen in the last "
                                         f"{win:.0f}s (expected {exp:.2f})")
                        elif label not in self.alerted:
                            # Your own movement beats any probe result: the
                            # probe may have run before the cap applied.
                            self.alerted.add(label)
                            self.announced = label
                            self.alert(f"!! {label} — capped at {val:.2f} m/s, "
                                       f"expected {exp:.2f} !!", label)
                    break
                if abs(val - target) <= tol and held >= self.get("live_hold"):
                    # The direction test is NOT required any more. VelocityX/Z
                    # are world axes, so "sideways" depends on which way you
                    # happen to face, and it tagged real 8ページ strafes as
                    # forward — two confirmed misses, both 6.50 held.
                    #
                    # Holding 6.50 is diagnostic on its own: forward is 6.60 in
                    # a normal round AND in 8ページ, so a sustained 6.50 cannot
                    # be forward movement whatever the axes claim.
                    top = self.core.vel.recent_max(
                        win, sideways_only=False,
                        ignore_above=exp + SLOPE_MARGIN, exclude_driven=True,
                        since=self.core.vel.stable_since)
                    if top > target + self.get("cap_tol"):
                        # Say so rather than staying silent: a suppressed alert
                        # is otherwise indistinguishable from no detection.
                        if (self.announced != f"skip{label}"
                                and label not in self.alerted):
                            self.announced = f"skip{label}"
                            what = "sideways" if need_side else "any direction"
                            self.log(f"{label} plateau at {val:.2f} ignored — "
                                     f"{top:.2f} {what} in the last "
                                     f"{win:.0f}s")
                        break
                    if label not in self.alerted:
                        self.alerted.add(label)
                        self.announced = label
                        how = " sideways" if need_side else ""
                        self.alert(f"!! {label} — held {val:.2f} m/s{how} !!",
                                   label)
                    break
            time.sleep(0.1)




class AutoSkip(Module):
    key = "skip"
    name_key, blurb_key = "skp.name", "skp.blurb"
    tab_key = "skp.name"
    # Armed rounds reset on exit: self-destruct should never be live because
    # of something you ticked days ago and forgot.
    volatile = ("r_",)
    code_only = ("focus_only", "extra", "max_secs")
    defaults = dict(
        {f"r_{en}": False for en, _ in ROUND_TYPES},
        hotkey="=", cancel_key="-",
        # A different key per copy: the key is read globally, so two copies
        # sharing one would both fire. F8 for the first, F9 for the second.
        manual_key="F8",
        extra="", max_secs=30.0,
        focus_only=True, background=True, learned="",
        terror_filter="", fog_now=False,
        extra_delay_on=False, extra_delay=0.0,
    )

    def __init__(self, core, log):
        super().__init__(core, log)
        self.stop_flag = threading.Event()
        self.aborted = False        # cancelled by hand for this round
        self.done_round = None      # round we have already acted on
        self.names = TerrorNames()  # ids -> names, for the log only
        self._wait_end = ""         # why the last terror wait ended
        self.unknown = set()
        threading.Thread(target=self._cancel_loop, daemon=True).start()
        threading.Thread(target=self._manual_loop, daemon=True).start()
        threading.Thread(target=self._arm_loop, daemon=True).start()

    # Rounds the self-destruct key does nothing in. They are never offered as
    # a tick box, including rounds learned before this rule existed.
    NO_EXPLODE = {"RUN", "Run", "ラン"}

    def _learned_names(self):
        return [x for x in self.vars["learned"].get().split(",")
                if x and x not in self.NO_EXPLODE]

    def build(self, parent):
        self.key_row(parent, "skp.hotkey", "hotkey")
        self.key_row(parent, "skp.manual", "manual_key", tip="tip.only")
        self._panel = parent        # a real widget, for dialogs
        self.row(parent, "skp.bg", "background", tip="tip.bg")
        self.row(parent, "skp.extradelay", "extra_delay_on", tip="tip.delay")
        self.row(parent, "skp.delay", "extra_delay")
        ttk.Label(parent, text=t("skp.rounds"), anchor="w").pack(fill="x",
                                                                pady=(6, 2))
        rows = list(ROUND_TYPES) + [(n, n) for n in self._learned_names()]
        common = [r for r in rows if r[0] not in BIG_FOUR]
        big = [r for r in rows if r[0] in BIG_FOUR]

        def grid_of(items):
            # Names discovered at runtime get a box of their own, so a round
            # type I never listed still becomes selectable.
            g = ttk.Frame(parent)
            g.pack(fill="x")
            for c in range(2):
                g.columnconfigure(c, weight=1, uniform="rt")
            for i, (en, ja) in enumerate(items):
                self._ensure_var(en)
                # Only the current language is shown so the column stays
                # narrow; matching still accepts both spellings.
                Toggle(g, self.vars[f"r_{en}"],
                       text=en if LANG == "en" else ja
                       ).grid(row=i // 2, column=i % 2,
                              sticky="w", padx=2, pady=1)

        grid_of(common)
        # A divider groups the big four without needing a header above them.
        ttk.Separator(parent).pack(fill="x", pady=(8, 6))
        grid_of(big)

        tb = ttk.Button(parent, text=t("skp.terrorbtn"),
                        command=self._terror_window)
        tb.pack(anchor="w", pady=(6, 0))
        Tip(tb, t("tip.terrorbtn"))

        # One button that flips every round at once, label following the state.
        btn = ttk.Button(parent)
        btn.configure(command=lambda: self._toggle_all(btn))
        self._sync_all_label(btn)
        btn.pack(anchor="w", pady=(6, 2))
        self.key_row(parent, "skp.cancel", "cancel_key", tip="tip.skcancel")

    def _ensure_var(self, name):
        self.vars.setdefault(f"r_{name}", tk.BooleanVar(value=False))

    def _arm_loop(self):
        """
        Watch the tick boxes continuously instead of only at round start.

        Arming mid-round used to do nothing until the NEXT round, because the
        explode was fired by the round_start event alone. Polling means a
        last-second tick still takes effect on the round you are in.
        """
        while not self.core.stop_evt.is_set():
            if not self.core.ui_ready.wait(timeout=0.5):
                continue
            name = self.core.last_round
            if (self.is_on() and self.core.in_round.is_set() and name
                    and not self.aborted and self.done_round != name
                    and name in self._wanted()):
                # done_round stops it restarting after you die, since in_round
                # stays set until the round formally ends.
                self.done_round = name
                self.stop_flag.clear()
                threading.Thread(target=self._explode, args=(name,),
                                 daemon=True).start()
            time.sleep(0.2)

    def _manual_loop(self):
        """
        Mirror a key you hold onto the self-destruct key.

        Binding the self-destruct FIELD to Mouse5 makes the app SEND Mouse5,
        which the world does not read. What you want is the opposite: hold
        Mouse5 yourself and have the app hold "=" for as long as you do.
        """
        held, grip = False, None
        try:
            while not self.core.stop_evt.is_set():
                if not self.core.ui_ready.wait(timeout=0.5):
                    continue
                trig = self.vars["manual_key"].get().strip()
                send = self.vars["hotkey"].get().strip() or "="
                # Each copy has its own key, so there is nothing to
                # disambiguate: background mode means the key works whatever
                # window you are in, with one client or several.
                allowed = (self.get("background")
                           or not self.get("focus_only")
                           or my_vrchat_focused())
                want = bool(trig) and trig != send and self.is_on() \
                    and key_is_down(trig) and allowed
                # Silent: this fires on every press and would bury the
                # round and speed messages that actually need reading.
                bg = bool(self.get("background"))
                hwnd = vrchat_hwnd() if bg else 0
                if want and not held:
                    if bg and hwnd:
                        grip = BgHold(hwnd, send)
                        held = grip.start()
                        if not held:
                            grip = None
                    else:
                        held = key_down(send)
                elif held and want and grip:
                    grip.keep()
                elif held and not want:
                    if grip:
                        grip.stop()
                        grip = None
                    else:
                        key_up(send)
                    held = False
                time.sleep(0.02)
        finally:
            if grip:
                grip.stop()
            elif held:
                key_up(self.vars["hotkey"].get().strip() or "=")

    def _cancel_loop(self):
        """Abort a self-destruct the instant you press the cancel key."""
        was = False
        while not self.core.stop_evt.is_set():
            if not self.core.ui_ready.wait(timeout=0.5):
                continue
            ch = self.vars["cancel_key"].get().strip()
            down = bool(ch) and key_is_down(ch)
            if down and not was:
                if not self.stop_flag.is_set():
                    self.aborted = True
                    self.stop_flag.set()
                    key_up(self.vars["hotkey"].get().strip() or "=")
                    self.log(f"auto explode CANCELLED by '{ch}'")
            was = down
            time.sleep(0.04)

    def _all_round_names(self):
        return [en for en, _ in ROUND_TYPES] + self._learned_names()

    def _sync_all_label(self, btn):
        names = self._all_round_names()
        for n in names:
            self._ensure_var(n)
        every = names and all(self.vars[f"r_{n}"].get() for n in names)
        btn.configure(text=t("skp.none") if every else t("skp.all"))

    def _toggle_all(self, btn):
        """Select every round, or clear every round, whichever applies."""
        names = self._all_round_names()
        for n in names:
            self._ensure_var(n)
        every = all(self.vars[f"r_{n}"].get() for n in names)
        for n in names:
            self.vars[f"r_{n}"].set(not every)
        self._sync_all_label(btn)

    def _wanted(self):
        """Every name, in both languages, that should trigger self-destruct."""
        names = set()
        for en, ja in list(ROUND_TYPES) + [(n, n) for n in
                                           self._learned_names()]:
            self._ensure_var(en)
            if self.vars[f"r_{en}"].get():
                names.update((en, ja))
        names.update(x.strip() for x in self.vars["extra"].get().split(",")
                     if x.strip())
        return names

    def _known(self):
        names = set(self._learned_names())
        for en, ja in ROUND_TYPES:
            names.update((en, ja))
        return names

    def _test(self):
        ch = self.vars["hotkey"].get().strip() or "="
        ok = send_key(ch)
        self.log(f"self-destruct key '{ch}': "
                 + ("sent" if ok else "could not be mapped on this layout"))

    def on_event(self, kind, data):
        if kind == "lobby_start":
            self.aborted = False        # a new lobby clears the abort
        if kind == "round_start":
            name = data["name"]
            if name not in self._known() and name not in self.NO_EXPLODE:
                # Learn it instead of asking you to type it in: a tick box
                # appears immediately and persists in the settings file.
                got = self._learned_names()
                got.append(name)
                self.vars["learned"].set(",".join(got))
                self._ensure_var(name)
                self.log(f"auto skip: new round '{name}' — tick box added")
                self.core.request_refresh()
            # The arm loop starts it, so ticking the box mid-round works too.
            self.done_round = None
        elif kind == "terrors":
            # Logged on its own, not only as part of an explode decision: a Fog
            # terror is revealed at +60s, often after you have already died,
            # and you still want to know what it was.
            ids = data.get("ids") or []
            if ids:
                self.log(f"terror: {self.names.label(ids)}")
        elif kind in ("death", "round_over"):
            self.stop_flag.set()

    MOVE_THRESH = MOVING_SPEED   # above this you are playing, not waiting
    # The round line is logged before the round is actually live. This is the
    # shortest wait that works; extra_delay is added on top of it.
    BASE_DELAY = 10.0
    # When the "are you moving?" decision is taken, measured from the round
    # line. Late enough that lobby wandering has finished, early enough to
    # still back out before the key goes down.
    CHECK_AT = 7.0

    def _moving(self, window=1.0):
        """Your own movement, ignoring anything the app made you do."""
        speed, _ = self.core.vel.held()
        return max(speed, self.core.vel.recent_max(
            window, exclude_driven=True))

    def _explode(self, round_name):
        """
        Wait for the round to actually begin, then explode unless you moved.

        The timeline, measured from the round line in the log:
          0s          round announced (the round is NOT live yet)
          CHECK_AT    "are you moving?" is decided here — late enough that
                      wandering around the lobby has finished
          BASE_DELAY  the round is live, so the key goes down
        Movement is then re-checked continuously during the hold, so starting
        to run at any point still releases the key.
        """
        # The movement check is NOT done here. At the round line you are
        # usually still walking around the lobby, which cancelled the explode
        # every time. What matters is whether you are moving once the round is
        # about to start, so the check happens near the end of the wait.
        delay = self.BASE_DELAY
        if self.get("extra_delay_on"):
            delay += max(0.0, self.get("extra_delay"))
        check_at = min(self.CHECK_AT, max(0.0, delay - 1.0))

        if delay:
            extra = delay - self.BASE_DELAY
            self.log(f"auto skip: {round_name} — waiting {delay:.0f}s for the "
                     f"round to begin"
                     + (f" ({self.BASE_DELAY:.0f} + {extra:.0f} extra)"
                        if extra else ""))
        late_check = self._checks_after_reveal(round_name)
        if check_at and self.stop_flag.wait(check_at):
            return                  # died, round ended, or cancelled
        # Where you wait to see the terror, checking your movement here — before
        # it is even known — would cancel on lobby wandering and give you no
        # chance to react. That check moves to just after the reveal instead.
        if not late_check:
            m = self._moving()
            if m > self.MOVE_THRESH:
                self.log(f"auto skip: {round_name} — you are moving "
                         f"({m:.2f} m/s), so not exploding")
                return
        remaining = delay - check_at
        if remaining > 0 and self.stop_flag.wait(remaining):
            return
        if not self._terror_allows(round_name):
            return
        if late_check and not self._still_after_reveal(round_name):
            return
        return self._explode_now(round_name)

    # How long to wait for the terrors after the normal delay has run out.
    # They land ~10s into the round, which is exactly when the explode would
    # otherwise start, so this is the cost of choosing terrors per round.
    TERROR_WAIT = 8.0




    # ---- per-terror explode choice -----------------------------------------
    def _filters(self):
        """{"Bloodbath": [ids to explode on]} — rounds with a terror choice."""
        try:
            return json.loads(self.vars["terror_filter"].get() or "{}")
        except ValueError:
            return {}

    def _filter_key(self, round_name):
        """English round name for a log name in either language."""
        for en, ja in list(ROUND_TYPES) + [(n, n) for n in
                                           self._learned_names()]:
            if round_name in (en, ja):
                return en
        return round_name

    # Latest a terror can arrive, counted from the round line. Your logs show
    # 8 Pages up to 41s and Fog at 60s (a 50s reveal after a 10s notice).
    TERROR_DEADLINE = 75.0

    def _wait_for_terrors(self, round_name):
        """
        Wait until this round's terror is known, however long that takes.

        A fixed 8 seconds was right for most rounds but not Fog, which hides
        its terror for 50 seconds, or 8 Pages, which can take 40. When the
        log announces a delayed reveal we wait for exactly that; otherwise up
        to TERROR_DEADLINE after the round began. Dying or the round ending
        stops the wait at once.
        """
        started = self.core.round_started_at or time.time()
        told = False
        self._wait_end = ""
        while not self.core.terrors_known.is_set():
            if self.stop_flag.is_set() or self.core.stop_evt.is_set():
                self._wait_end = "stopped"      # you died or the round ended
                return False
            eta = self.core.terrors_eta
            deadline = max(started + self.TERROR_DEADLINE,
                           eta + 5 if eta else 0)
            if time.time() > deadline:
                self._wait_end = "timeout"
                return False
            if not told:
                told = True
                if eta:
                    self.log(f"auto skip: {round_name} — terror hidden, "
                             f"revealed in {max(0, eta - time.time()):.0f}s; "
                             f"waiting")
                else:
                    self.log(f"auto skip: {round_name} — waiting for the "
                             f"terror to be announced")
            self.core.terrors_known.wait(0.25)
        return True

    # Rounds that explode as soon as the terror is allowed, with the movement
    # check left at CHECK_AT as before.
    FAST_ROUNDS = ("Classic", "Bloodbath")
    # Time to see the revealed terror and move, if you want to stay.
    REACT_GRACE = 1.0

    def _checks_after_reveal(self, round_name):
        """
        Should the movement check wait until the terror is revealed?

        Only where it means something: you chose terrors for this round, and it
        is not Classic or Bloodbath (those stay fast). Fog with "explode at
        round start" never waits for its terror, so it keeps the early check.
        """
        key = self._filter_key(round_name)
        if key in self.FAST_ROUNDS:
            return False
        if key == "Fog" and self.get("fog_now"):
            return False
        return self._filters().get(key) is not None

    def _still_after_reveal(self, round_name):
        """
        Give you REACT_GRACE after the reveal; explode only if you stay put.

        Measured from the moment the terror was revealed, not from now, so a
        terror announced a moment ago does not get a second full second.
        """
        end = (self.core.terrors_at or time.time()) + self.REACT_GRACE
        wait = max(0.0, end - time.time())
        if wait and self.stop_flag.wait(wait):
            return False            # died, round ended, or cancelled
        m = self._moving(window=self.REACT_GRACE)
        if m > self.MOVE_THRESH:
            self.log(f"auto skip: {round_name} — you moved after the terror "
                     f"was revealed ({m:.2f} m/s), so not exploding")
            return False
        return True

    def _terror_allows(self, round_name):
        """
        With a terror choice set for this round, explode only on those.

        Mirrors ToN ListTool's 自動自爆設定: ticked = explode, unticked = sit
        it out. A round with NO choice set explodes on anything, exactly as
        before, so this is opt-in per round.
        """
        if self._filter_key(round_name) == "Fog" and self.get("fog_now"):
            # Fog hides its terror for about 50 seconds. With this on, the
            # terror choices for Fog are ignored and it explodes at the usual
            # moment, as it did before terrors could be chosen.
            self.log(f"auto skip: {round_name} — exploding at round start "
                     f"(not waiting for the terror)")
            return True
        chosen = self._filters().get(self._filter_key(round_name))
        if chosen is None:
            return True                     # no choice for this round
        if not self.core.terrors_known.is_set():
            if not self._wait_for_terrors(round_name):
                # You chose which terrors to explode on for this round, so
                # exploding without knowing which one it is would override that
                # choice. Stay put instead — and say why the wait ended, since
                # dying mid-wait is not the same as the terror never coming.
                if self._wait_end == "stopped":
                    self.log(f"auto skip: {round_name} — you died or the round "
                             f"ended before the terror was revealed")
                else:
                    self.log(f"auto skip: {round_name} — terror never "
                             f"revealed, so NOT exploding (you chose terrors "
                             f"for this round)")
                return False
        ids = list(self.core.terror_ids)
        if any(i < 0 for i in ids):
            # An 8 Pages terror we cannot identify. You chose terrors for this
            # round, so exploding on a guess would override that choice.
            self.log(f"auto skip: {round_name} — {self.names.label(ids)}: "
                     f"can't identify the terror, so NOT exploding")
            return False
        wanted = set(chosen)
        # ONE terror you left unticked is enough to stay. In Bloodbath,
        # Midnight and Double Trouble several terrors spawn together, and the
        # old rule — explode if ANY of them was ticked — blew you up in a
        # round where the terror you wanted to stay for (Sakuya) was right
        # there beside two ticked ones. Now every spawned terror has to be
        # ticked before it explodes.
        stay = [i for i in ids if i not in wanted]
        who = self.names.label(ids)
        if not stay:
            self.log(f"auto skip: {round_name} — {who}: all ticked, exploding")
            return True
        self.log(f"auto skip: {round_name} — {self.names.label(stay)} is "
                 f"unticked, so NOT exploding")
        return False

    def _terror_window(self):
        try:
            self._terror_window_body()
        except Exception as e:
            self.log(f"could not open the terror picker: {e}")

    def _terror_window_body(self):
        """
        Pick, per round, which terrors to explode on.

        Laid out like ToN ListTool's 自動自爆設定: rounds down the left, that
        round's terrors on the right. Ticked = explode. A round you never
        touch keeps exploding on everything.
        """
        rounds = self._picker_rounds(self.names.rounds())
        if not rounds:
            where = self.names.loaded_from
            if where:
                # Found, but an older copy: names only, no round lists. The
                # old "not found" message sent people hunting for a file that
                # was sitting right there.
                self.log(f"terror picker: {where} is an OLD copy (names "
                         f"only, no round lists). Replace it with the newer "
                         f"terror_names.json — about 29 KB, not 8 KB")
            else:
                self.log("terror picker: terror_names.json not found beside "
                         "the app — it lists which terrors each round can "
                         "spawn")
            return
        # Say what the picker has to work with. Icons silently missing makes
        # the grid look like a plain list, and that looks like a bug.
        n_sprites = len(self.names._sprites)
        missing = [s for s in self.names._sheet_names
                   if not os.path.isfile(os.path.join(self.names._dir or HERE,
                                                      s))]
        if self.names.format < self.NAMES_FORMAT:
            # The one mistake that keeps happening: an older data file left in
            # the build folder gets bundled again on every rebuild.
            self.log(f"terror picker: {self.names.loaded_from} is OUTDATED "
                     f"(format {self.names.format}, need "
                     f"{self.NAMES_FORMAT}). Replace terror_names.json in the "
                     f"folder you BUILD from, then rebuild — otherwise the "
                     f"old copy is bundled again")
        if not n_sprites:
            self.log("terror picker: terror_names.json has no icon "
                     "positions — use the newest copy")
        elif missing:
            self.log(f"terror picker: icons missing — {', '.join(missing)} "
                     f"not found beside the app")
        # Nothing is logged when all is well: a line on every click is noise.
        # Only the problems above are worth saying.
        root = self._panel.winfo_toplevel()
        win = tk.Toplevel(root)
        win.title(t("skp.terrortitle"))
        win.configure(bg=THEME["bg"])
        win.transient(root)
        # Beside the main window, not wherever Windows drops a new one (the
        # top-left corner). If there is no room on the right, slide it back
        # onto the screen rather than let it hang off the edge.
        W_, H_ = 860, 660
        root.update_idletasks()
        x = root.winfo_rootx() + root.winfo_width() + 8
        y = root.winfo_rooty()
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        x = max(0, min(x, sw - W_))
        y = max(0, min(y, sh - H_ - 40))
        win.geometry(f"{W_}x{H_}+{x}+{y}")

        filters = self._filters()
        state = {}                      # round_en -> {id: BooleanVar}

        # Fixed width, wider than the names need: the grid is 12 icons across
        # and left a band of empty space on the right, so give it to the list.
        left = ttk.Frame(win, width=190)
        left.pack(side="left", fill="y", padx=(10, 8), pady=10)
        left.pack_propagate(False)
        ttk.Label(left, text=t("skp.terrorrounds"),
                  style="Head.TLabel").pack(anchor="w")
        # A padded column of rows rather than a Listbox: a Listbox has no row
        # spacing, so the 16 rounds bunched at the top with the rest empty.
        col = tk.Frame(left, bg=THEME["panel"])
        col.pack(fill="both", expand=True, pady=(4, 0))
        keys = list(rounds)
        rows_ = []                      # (frame, name label, toggle or None)

        def paint(row, colour, fg):
            frame, lbl_, box = row
            frame.configure(bg=colour)
            lbl_.configure(bg=colour, fg=fg)
            if box is not None:
                box.set_bg(colour)

        def pick(i):
            for j, row in enumerate(rows_):
                on_ = j == i
                paint(row, THEME["accent2"] if on_ else THEME["panel"],
                      THEME["bg"] if on_ else THEME["fg"])
            show(i)

        for i, k in enumerate(keys):
            en = k.partition("/")[0]
            mark = "  ●" if en in filters else ""
            row = tk.Frame(col, bg=THEME["panel"], cursor="hand2")
            row.pack(fill="x", pady=1)
            # The tick box is the SAME switch as the main tab's "explode on
            # these rounds" list, so the two can never disagree. Clicking the
            # box toggles exploding; clicking the name opens its terrors.
            var = self._round_switch(en)
            if var is not None:
                box = Toggle(row, var)
                box.set_bg(THEME["panel"])
                box.pack(side="left", padx=(10, 0))
            else:
                # Nothing to switch (no round of this name is ever reported),
                # so leave a gap the width of a box to keep the names aligned.
                box = None
                tk.Frame(row, width=28, height=18,
                         bg=THEME["panel"]).pack(side="left", padx=(10, 0))
            lbl_ = tk.Label(row, text=(k.partition("/")[2] if LANG == "ja"
                                       else en) + mark,
                            bg=THEME["panel"], fg=THEME["fg"], anchor="w",
                            font=UI_FONT[0], padx=8, pady=6, cursor="hand2")
            lbl_.pack(side="left", fill="x", expand=True)
            for w in (row, lbl_):
                w.bind("<Button-1>", lambda _e, i=i: pick(i))
            rows_.append((row, lbl_, box))

        right = ttk.Frame(win)
        right.pack(side="left", fill="both", expand=True, padx=(0, 10),
                   pady=10)
        head = ttk.Label(right, style="Head.TLabel")
        head.pack(anchor="w")
        hint = ttk.Label(right, style="Muted.TLabel", wraplength=480,
                         justify="left", text=t("skp.terrorhint"))
        hint.pack(anchor="w", pady=(2, 6))

        # Fog only: explode at round start instead of waiting ~60s for the
        # hidden terror. Packed or hidden by show() as you change round.
        fog_bar = ttk.Frame(right)
        fog_box = Toggle(fog_bar, self.vars["fog_now"],
                         text=t("skp.fognow") + "  ⍰")
        fog_box.pack(side="left")
        Tip(fog_box, t("tip.fognow"))

        tools = ttk.Frame(right)
        tools.pack(fill="x")
        ttk.Label(tools, text=t("skp.terrorsearch")).pack(side="left")
        search = tk.StringVar()
        ttk.Entry(tools, textvariable=search, width=20).pack(side="left",
                                                             padx=(4, 10))
        search.trace_add("write", lambda *_: show(current["i"]))
        body, inner = self._scroll_area(right)

        # Laid out like tontrack.me: id order, 12 across, split into the same
        # sections — so a terror sits where you already expect to find it.
        COLS = 12
        SECTIONS = ((0, 133, "sec.terrors"), (134, 169, "sec.alternates"),
                    (170, 199, "sec.moons"), (200, 283, "sec.unbound"),
                    (284, 9999, "sec.special"))
        current = {"i": 0}

        def show(i):
            current["i"] = i
            for w in inner.winfo_children():
                w.destroy()
            key = keys[i]
            en = key.partition("/")[0]
            head.configure(text=key)
            if en == "Fog":
                fog_bar.pack(anchor="w", pady=(0, 6), before=tools)
            else:
                fog_bar.pack_forget()
            ids = rounds[key]
            chosen = filters.get(en)
            vs = state.setdefault(en, {})
            needle = search.get().strip().lower()
            for tid in ids:
                if tid not in vs:
                    # untouched round: everything ticked = explode on all
                    vs[tid] = tk.BooleanVar(
                        value=True if chosen is None else tid in chosen)
            row = 0
            heads = []

            def recount():
                for lbl, key_, part_ in heads:
                    on_ = sum(1 for i in part_ if vs[i].get())
                    lbl.configure(text=f"{t(key_)}   {on_}/{len(part_)}")

            for lo, hi, label in SECTIONS:
                part = [i for i in ids if lo <= i <= hi
                        and (not needle
                             or needle in self.names.name(i).lower())]
                # Full set of Alternates: use tontrack's placement, so each
                # terror sits exactly where it does on their page.
                if lo == 134 and not needle \
                        and sorted(part) == sorted(self.ALT_ORDER):
                    part = list(self.ALT_ORDER)
                if not part:
                    continue
                # ids 170-199 are the moons in the Moon round, but in 8 Pages
                # the same range holds 8 Pages' own terrors (Baldi, Shadow
                # Freddy, Navigator...), so name the section after the round.
                if lo == 170 and en == "8 Pages":
                    label = "sec.8pages"
                # The full 134: place each terror at its ListTool position.
                classic = (lo == 0 and not needle
                           and sorted(part) == list(range(134)))
                head_lbl = ttk.Label(inner, style="Head.TLabel")
                head_lbl.grid(row=row, column=0, columnspan=COLS, sticky="w",
                              pady=(10 if row else 0, 3))
                heads.append((head_lbl, label, part))
                row += 1
                if classic:
                    placed = [(r, c, tid)
                              for r, cells in enumerate(self.CLASSIC_LAYOUT)
                              for c, tid in enumerate(cells) if tid is not None]
                    rows_used = len(self.CLASSIC_LAYOUT)
                else:
                    placed = [(r, c, tid) for (r, c), tid in zip(
                        self._layout(lo, len(part), COLS, bool(needle)), part)]
                    rows_used = self._layout_rows(lo, len(part), COLS,
                                                  bool(needle))
                for r, c, tid in placed:
                    IconTile(inner, vs[tid], image=self.names.icon(tid),
                             name=self.names.name(tid),
                             command=recount).grid(
                        row=row + r, column=c, padx=2, pady=2)
                row += rows_used
            recount()

        def set_all(on):
            en = keys[current["i"]].partition("/")[0]
            for v in state.get(en, {}).values():
                v.set(on)
            show(current["i"])

        ttk.Button(tools, text=t("skp.all"),
                   command=lambda: set_all(True)).pack(side="left")
        ttk.Button(tools, text=t("skp.none"),
                   command=lambda: set_all(False)).pack(side="left", padx=6)


        def save():
            out = dict(filters)
            for en, vs in state.items():
                ids = sorted(t_ for t_, v in vs.items() if v.get())
                total = len(vs)
                # every terror ticked means "no restriction": drop the entry
                # so the round behaves exactly as it did before
                if len(ids) == total:
                    out.pop(en, None)
                else:
                    out[en] = ids
            self.vars["terror_filter"].set(json.dumps(out))
            win.destroy()

        bar = ttk.Frame(win)
        bar.place(relx=1.0, rely=1.0, x=-10, y=-10, anchor="se")
        ttk.Button(bar, text=t("skp.terrorsave"), command=save).pack()

        pick(0)
        try:
            win.update_idletasks()
            win.grab_set()
        except tk.TclError:
            pass

    NAMES_FORMAT = 4            # terror_names.json layout this code expects

    # tontrack.me stacks the 36 Alternates as a centred pyramid, row widths
    # 11, 9, 7, 5, 3, 1 — which is exactly 36.
    PYRAMID = (11, 9, 7, 5, 3, 1)
    # The 134 main terrors, placed exactly as ToN ListTool and tontrack.me
    # show them: 11 across, the last two rows reaching one slot further left
    # (10 x 11 + 2 x 12 = 134). Mostly id order, but not entirely — lain (83)
    # and "This Killer does not exist" (122) sit in the extra left slots, and
    # the last two rows have their own order. Read cell by cell from
    # ListTool's grid and checked icon against icon. None = empty slot.
    CLASSIC_LAYOUT = (
        (None,   0,   1,   2,   3,   4,   5,   6,   7,   8,   9,  10),
        (None,  11,  12,  13,  14,  15,  16,  17,  18,  19,  20,  21),
        (None,  22,  23,  24,  25,  26,  27,  28,  29,  30,  31,  32),
        (None,  33,  34,  35,  36,  37,  38,  39,  40,  41,  42,  43),
        (None,  44,  45,  46,  47,  48,  49,  50,  51,  52,  53,  54),
        (None,  55,  56,  57,  58,  59,  60,  61,  62,  63,  64,  65),
        (None,  66,  67,  68,  69,  70,  71,  72,  73,  74,  75,  76),
        (None,  77,  78,  79,  80,  81,  82,  84,  85,  86,  87,  88),
        (None,  89,  90,  91,  92,  93,  94,  95,  96,  97,  98,  99),
        (None, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110),
        (122, 120, 119, 118, 116, 111, 112, 113, 115, 117, 114, 121),
        ( 83, 133, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132),
    )

    # ...and not in id order: this is tontrack's own placement, read cell by
    # cell off its page (Feddys top-left, then TBH SPY). Terror ids, one row
    # of the pyramid per line.
    ALT_ORDER = (
        149, 150, 141, 139, 146, 169, 148, 164, 134, 158, 143,
        140, 137, 167, 160, 161, 154, 135, 144, 165,
        138, 159, 145, 163, 168, 152, 142,
        147, 156, 162, 136, 166,
        157, 153, 155,
        151,
    )

    def _layout(self, section_start, count, cols, searching):
        """
        (row, column) for each tile in a section.

        Alternates use the pyramid when the whole set is on screen. While
        searching, or if the count is not the full 36, a plain grid is used —
        a pyramid with gaps punched in it reads worse than a simple list.
        """
        if section_start == 134 and not searching \
                and count == sum(self.PYRAMID):
            out = []
            for r, width in enumerate(self.PYRAMID):
                start = (self.PYRAMID[0] - width) // 2
                out.extend((r, start + c) for c in range(width))
            return out
        return [(n // cols, n % cols) for n in range(count)]

    def _layout_rows(self, section_start, count, cols, searching):
        if section_start == 134 and not searching \
                and count == sum(self.PYRAMID):
            return len(self.PYRAMID)
        return (count + cols - 1) // cols

    # Rounds the picker leaves out entirely.
    # Special is hidden too: the log never reports a round by that name, so
    # neither its tick box nor its terror choices could ever take effect.
    # Moon is hidden as well: a Moon round's only terror is the moon itself,
    # so there is nothing to choose between.
    PICKER_HIDDEN = ("Classic.exe", "Randomizer", "Special", "Moon")
    # Display order. Rounds not listed here follow at the end, so nothing
    # can silently vanish from the picker.
    PICKER_ORDER = ("Classic", "Bloodbath", "Fog", "Cracked", "Punished",
                    "Sabotage", "Alternate", "Midnight", "Ghost",
                    "Double Trouble", "8 Pages", "Unbound")
    # "Moon" in the picker covers four separate explode switches.
    MOON_ROUNDS = ("Mystic Moon", "Blood Moon", "Solstice", "Twilight")

    @staticmethod
    def _picker_rounds(raw):
        """
        The rounds as the picker shows them.

        Sabotage arrives from the log as ONE round, but the data splits it
        into "star" and "murder". Murder cannot self-destruct, so only the
        star list matters — shown as plain "Sabotage", and saved under that
        name so it actually matches the round the log reports. (Saved as
        "Sabotage star" it never matched, so the choice was silently ignored.)
        """
        out = {}
        for key, ids in raw.items():
            en, _, jp = key.partition("/")
            if en in AutoSkip.PICKER_HIDDEN:
                continue
            if en == "Sabotage murder":
                continue
            if en == "Sabotage star":
                out["Sabotage/サボタージュ"] = ids
                continue
            out[key] = ids
        # The terror data has no Double Trouble entry, yet it is a round you
        # can explode on. It draws its terrors from the same pool as Classic,
        # so borrow that list rather than leave the round out.
        if not any(k.startswith("Double Trouble") for k in out):
            classic = next((v for k, v in out.items()
                            if k.startswith("Classic/")), None)
            if classic:
                out["Double Trouble/ダブルトラブル"] = classic
        order = {n: i for i, n in enumerate(AutoSkip.PICKER_ORDER)}
        return dict(sorted(out.items(),
                           key=lambda kv: order.get(kv[0].partition("/")[0],
                                                    len(order))))

    def _round_switch(self, en):
        """
        The explode switch behind a picker round, or None if there is none.

        "Moon" drives the four moons together, so it gets a proxy that turns
        all four on or off and starts ticked only when every moon is.
        """
        if en == "Moon":
            moons = [self.vars[f"r_{m}"] for m in self.MOON_ROUNDS
                     if f"r_{m}" in self.vars]
            if not moons:
                return None
            proxy = tk.BooleanVar(value=all(v.get() for v in moons))

            def push(*_):
                for v in moons:
                    v.set(proxy.get())
            proxy.trace_add("write", push)
            return proxy
        known = {e for e, _j in ROUND_TYPES} | set(self._learned_names())
        if en not in known:
            return None
        self._ensure_var(en)
        return self.vars[f"r_{en}"]

    def _scroll_area(self, parent):
        """A vertically scrolling frame for long terror lists."""
        outer = ttk.Frame(parent)
        outer.pack(fill="both", expand=True, pady=(6, 34))
        cv = tk.Canvas(outer, bg=THEME["bg"], highlightthickness=0)
        sb = ttk.Scrollbar(outer, orient="vertical", command=cv.yview)
        inner = ttk.Frame(cv)
        cv.create_window((0, 0), window=inner, anchor="nw")
        cv.configure(yscrollcommand=sb.set)
        cv.pack(side="left", fill="both", expand=True)
        state = {"scroll": False}

        def refit(_e=None):
            """
            Scroll only when the content is taller than the view.

            A round like Moon has four tiles: showing a scrollbar and letting
            the wheel drag four icons around an empty panel is just noise.
            """
            cv.configure(scrollregion=cv.bbox("all"))
            need = inner.winfo_reqheight() > cv.winfo_height()
            state["scroll"] = need
            if need:
                sb.pack(side="right", fill="y")
            else:
                sb.pack_forget()
                cv.yview_moveto(0)

        def wheel(e):
            if state["scroll"]:
                cv.yview_scroll(-int(e.delta / 120), "units")

        inner.bind("<Configure>", refit)
        cv.bind("<Configure>", refit)
        cv.bind("<Enter>", lambda _e: cv.bind_all("<MouseWheel>", wheel))
        cv.bind("<Leave>", lambda _e: cv.unbind_all("<MouseWheel>"))
        return outer, inner





    def _explode_now(self, round_name):
        """
        Send ONE key-down and leave it down until you die.

        Re-sending the down event looks like a fresh key press, which restarts
        the hold-to-confirm bar — and because injected and physical input share
        the same key state, it also broke a manual hold while this was enabled.
        A real hold is one down, then silence, then one up.
        """
        ch = self.vars["hotkey"].get().strip() or "="
        deadline = time.time() + max(2.0, self.get("max_secs"))
        holding = False
        bghold = None
        began = time.time()
        front_at_start = foreground_title()
        front_changed = False
        died = False
        try:
            while not (self.stop_flag.is_set() or self.core.stop_evt.is_set()):
                if time.time() > deadline:
                    self.log("auto skip: gave up, you are still alive")
                    return
                bg = bool(self.get("background"))
                hwnd = vrchat_hwnd() if bg else 0
                # my_vrchat_focused(), not "any VRChat is in front": with
                # two clients, SendInput goes to whichever has focus — so a
                # copy whose own client was in the background happily
                # exploded the OTHER game. With one client this is exactly
                # the old test.
                focused = (bg and hwnd) or not self.get("focus_only") \
                    or my_vrchat_focused()
                if focused and not holding:
                    if bg and hwnd:
                        bghold = BgHold(hwnd, ch)
                        ok = bghold.start()
                        if not ok:
                            self.log("auto skip: "
                                     + (bghold.fail or "background hold "
                                        "failed"))
                            bghold = None
                    else:
                        ok = key_down(ch)
                    if not ok:
                        self.log(f"auto skip: could not send '{ch}'"
                                 + (" — could not attach to VRChat" if bg
                                    else " — not on your layout"))
                        return
                    holding = True
                    warn = ""
                    if bghold and is_minimised(hwnd):
                        warn = "  [VRChat is MINIMISED — it may be too " \
                               "throttled to complete the hold]"
                    self.log(f"auto skip: {round_name} — holding '{ch}' down"
                             + (" (background)" if bghold else "") + warn)
                elif holding and bghold:
                    bghold.keep()
                    # Record whether VRChat was ever frontmost during the hold.
                    if not front_changed and \
                            "VRChat" in foreground_title() and \
                            "VRChat" not in front_at_start:
                        front_changed = True
                elif holding and not focused:
                    key_up(ch)          # never hold a key into another window
                    holding = False
                    self.log("auto skip: VRChat lost focus, key released")
                if holding:
                    # Moving mid-hold means you changed your mind about this
                    # round. Checking only at the start cannot catch that: the
                    # explode begins within 0.2s of the round line, before you
                    # have had a chance to move at all.
                    m = self._moving(0.6)
                    if m > self.MOVE_THRESH:
                        self.log(f"auto skip: stopped — you started moving "
                                 f"({m:.2f} m/s)")
                        return
                time.sleep(0.1)
        finally:
            died = self.stop_flag.is_set()
            if bghold:
                bghold.stop()
            if holding:
                key_up(ch)              # release both ways, always
                secs = time.time() - began
                if bghold and not died and secs > 3:
                    # A long hold that produced no death means the key never
                    # reached the world. Record the one fact that distinguishes
                    # the cases, so this stops being guesswork.
                    self.log(f"auto skip: held {secs:.0f}s with NO death — "
                             f"front at start: {front_at_start or '?'}"
                             + ("; VRChat was minimised"
                                if is_minimised(vrchat_hwnd()) else "")
                             + ("; VRChat came to the front during the hold"
                                if front_changed else
                                "; VRChat never came to the front"))
                else:
                    self.log(f"auto skip: key released after {secs:.1f}s")


class RoundStarter(Module):
    key = "starter"
    name_key, blurb_key = "str.name", "str.blurb"
    tab_key = "tab.helper"
    tip_key = "tip.starter"
    # Hidden from the UI, so the code default must win — otherwise a value
    # saved while the row was still visible sticks with no way to change it.
    code_only = ("check_delay", "debug", "early_start", "bg_click",
                 "run", "click_rate", "check_after")

    defaults = {
        # One sequence for every round type, editable and testable here.
        "sequence": "drop; wait 0; forward 3.3; left 0.13; spam 0.8",
        "run": False, "click_rate": 0.12,
        "check_after": True, "check_delay": 0.05, "debug": False,
        "early_start": True, "start_delay": 9.0, "cancel_on_move": True,
        "bg_click": True,
    }
    MOVE_THRESH = MOVING_SPEED   # your movement above this cancels the macro

    MOVES = ("forward", "back", "left", "right")
    STEPS = MOVES + ("drop", "use", "wait", "jump", "spam")

    def __init__(self, core, log):
        super().__init__(core, log)
        self.ran_this_lobby = False
        self._running = False       # true once the macro has begun

    def build(self, parent):
        ttk.Label(parent, text=t("str.seq"), anchor="w").pack(fill="x",
                                                              pady=(4, 0))
        ttk.Entry(parent, textvariable=self.vars["sequence"]).pack(fill="x")
        ttk.Label(parent, style="Muted.TLabel", wraplength=700,
                  justify="left",
                  text=t("str.help")).pack(fill="x", pady=(2, 4))
        self.row(parent, "str.delay", "start_delay", tip="tip.strdelay")
        self.row(parent, "str.cancelmove", "cancel_on_move")

    def test(self):
        """Run the sequence on demand, for tuning."""
        threading.Thread(target=self._execute, args=("test",),
                         daemon=True).start()

    # -- events -------------------------------------------------------------
    def on_event(self, kind, data):
        if kind == "round_start":
            self.ran_this_lobby = False
        elif kind == "round_over" and self.get("early_start"):
            # RoundOver is the please-wait phase, well before the lobby is
            # verified. Moving now means standing at the button by the time it
            # becomes pressable, rather than setting off once it already is.
            self._begin("round over")
        elif kind == "lobby_start":
            self._begin("round end")

    def _begin(self, why):
        if self.ran_this_lobby:
            return                  # early start already handled this lobby
        self.ran_this_lobby = True
        threading.Thread(target=self._execute, args=("auto",),
                         daemon=True).start()



    def _user_moving(self):
        """
        Your movement, checked only BEFORE the macro starts.

        Once it is running the macro is moving you too, and telling the two
        apart needs guesswork that produced more false cancels than real ones.
        So the decision is taken during the wait and then left alone.
        """
        if not self.get("cancel_on_move") or self._running:
            return 0.0
        speed, _ = self.core.vel.held()
        return speed if speed > MOVING_SPEED else 0.0

    def _abort(self, source):
        if self.core.stop_evt.is_set():
            return True
        m = self._user_moving()
        if m:
            self.log(f"auto-start cancelled — you moved ({m:.2f} m/s)")
            return True
        if source == "test":
            return False

        # Bounded by the ROUND, not the lobby flag. Starting early means
        # running during the please-wait phase, when the lobby has not been
        # verified yet — requiring it aborted every single run.
        return not self.is_on() or self.core.in_round.is_set()

    def _execute(self, source):
        raw = self.vars["sequence"].get()
        steps = [s.strip() for s in raw.split(";") if s.strip()]
        if source != "test":
            wait = max(0.0, self.get("start_delay"))
            if wait:
                # Being teleported back to the lobby registers as movement —
                # 6.60 m/s while standing perfectly still — so the first part
                # of the wait is spent letting the arrival settle. Only what
                # happens after that counts as you moving.
                settle = min(wait, max(3.0, wait * 0.5))
                self.log(f"auto-start: waiting {wait:g}s to be back in the "
                         f"lobby (watching you from {settle:g}s)")
                t0 = time.time()
                while time.time() - t0 < wait:
                    if self.core.stop_evt.is_set() or not self.is_on():
                        return
                    if time.time() - t0 >= settle and self._abort(source):
                        self.log("auto-start aborted during the wait")
                        return
                    time.sleep(0.1)
        self.log(f"auto-start ({source}): {len(steps)} steps")
        self._running = True        # from here your movement is ignored
        try:
            self._run_steps(steps, source)
        finally:
            self._running = False
            self.core.release_all()     # never leave a direction held
        self.log("auto-start: sequence finished")
        if source != "test" and self.get("check_after"):
            # The button is pressed, so the round type is live NOW. This is the
            # one moment where no guessing is involved.
            time.sleep(max(0.0, self.get("check_delay")))
            self.core.emit("pressed")

    def _run_steps(self, steps, source):
        for raw in steps:
            if self._abort(source):
                self.log("auto-start aborted")
                return
            parts = raw.split()
            verb = parts[0].lower()
            spam = verb.endswith("+use")
            if spam:
                verb = verb[:-4]
            try:
                amount = float(parts[1]) if len(parts) > 1 else 0.0
            except ValueError:
                self.log(f"bad step '{raw}' — expected e.g. 'forward 4'")
                return
            if verb not in self.STEPS or (spam and verb not in self.MOVES):
                self.log(f"unknown step '{raw}' — use: "
                         + ", ".join(self.STEPS) + ", or <direction>+use")
                return
            self._do(verb, amount, spam)

    # Steps that must be AIMED: VRChat raycasts from the cursor, so these
    # need the pointer over the button. "drop" is a right click that needs no
    # target, so it is left out — grabbing the cursor for it moved the mouse
    # away from you for no reason.
    CLICK_VERBS = ("use", "spam")

    def _do(self, verb, amount, spam=False):
        rate = max(0.04, self.get("click_rate"))
        # Only a dedicated clicking step takes the cursor. A movement step
        # that also clicks ("left+use") does NOT: it would grab the mouse,
        # give it back, and grab it again a moment later for the spam that
        # follows. One takeover per sequence is enough, and the spam is the
        # step that actually has to hit the button.
        clicks = verb in self.CLICK_VERBS
        need = (clicks and self.get("bg_click")
                and "VRChat" not in foreground_title())
        hwnd = vrchat_hwnd() if need else 0
        if self.get("debug"):
            where = ("VRChat" if "VRChat" in foreground_title()
                     else f"'{foreground_title()[:24]}'")
            self.log(f"  step: {verb} {amount:g}"
                     + ("  +click" if spam else "")
                     + f"   [front: {where}]")
        if need:
            with BgFocus(hwnd):
                self._do_step(verb, amount, spam, rate)
        else:
            self._do_step(verb, amount, spam, rate)

    def _do_step(self, verb, amount, spam, rate):
        if verb == "wait":
            time.sleep(max(0.0, amount))
        elif verb == "drop":
            self.core.tap(DROP_INPUT, hold=0.12)
        elif verb == "use":
            self.core.tap(USE_INPUT, hold=0.15)
        elif verb == "jump":
            self.core.tap("/input/Jump")
        elif verb == "spam":
            self.core.spam_click(max(0.1, amount), rate)

        else:
            self.core.macro_move(verb, max(0.05, amount),
                                 use_run=bool(self.get("run")),
                                 spam_use=spam, rate=rate)


# ============================================================  gui  =========

# ======================================================  updates  =========
# The release zip build_release.bat makes: ToNToolkit-v1.1.zip
RELEASE_ASSET = re.compile(r"^ToNToolkit-v?[\d.]+\.zip$", re.I)

# Runs after the app has closed. A running program cannot overwrite its own
# files on Windows, so the copy happens here. ASCII only; every path arrives
# as an argument, so Japanese folder names are safe.
_UPDATE_PS1 = r"""
param([int]$AppPid, [string]$Src, [string]$Dst, [string]$Exe)
try { Wait-Process -Id $AppPid -Timeout 60 -ErrorAction SilentlyContinue } catch {}
Start-Sleep -Milliseconds 600
# /XF: never touch the user's own settings.
& robocopy $Src $Dst /E /R:5 /W:1 /XF ton_toolkit.json personal.txt /NFL /NDL /NJH /NJS /NP | Out-Null
# Earlier builds also put these beside the exe; they now live in _internal.
foreach ($f in @("terror_names.json", "terror_icons.png", "terror_icons_unbound.png", "icon.ico")) {
    $p = Join-Path $Dst $f
    if (Test-Path -LiteralPath $p) { Remove-Item -LiteralPath $p -Force -ErrorAction SilentlyContinue }
}
Start-Process -FilePath (Join-Path $Dst $Exe) -WorkingDirectory $Dst
Remove-Item -LiteralPath $Src -Recurse -Force -ErrorAction SilentlyContinue
"""


def version_tuple(v):
    """'v1.1' -> (1, 1), so 1.10 sorts above 1.9."""
    nums = re.findall(r"\d+", v or "")
    return tuple(int(n) for n in nums[:4]) or (0,)


class Updater:
    """
    Tell the user about a newer GitHub release and, if they agree, install it.

    Only an exe built by build_release.bat installs itself. The personal build
    would be replaced by the public one (losing the AFK Helper), and running
    from source has nothing to replace, so both just get the release page.
    """
    API = "https://api.github.com/repos/{repo}/releases/latest"

    def __init__(self, app):
        self.app, self.log = app, app.log

    def can_install(self):
        return bool(getattr(sys, "frozen", False)) and not PERSONAL_BUILD

    def check(self):
        """Background thread. Any failure is quiet: offline is not an error."""
        if not UPDATE_REPO:
            return
        try:
            req = urllib.request.Request(
                self.API.format(repo=UPDATE_REPO),
                headers={"Accept": "application/vnd.github+json",
                         "User-Agent": "ToNToolkit"})
            with urllib.request.urlopen(req, timeout=10) as r:
                rel = json.load(r)
        except Exception:
            return
        tag = rel.get("tag_name", "")
        if rel.get("draft") or rel.get("prerelease"):
            return
        if version_tuple(tag) <= version_tuple(APP_VERSION):
            return
        asset = next((a for a in rel.get("assets", [])
                      if RELEASE_ASSET.match(a.get("name", ""))), None)
        self.app.after(0, lambda: self._ask(rel, tag, asset))

    def _ask(self, rel, tag, asset):
        notes = (rel.get("body") or "").strip()
        if len(notes) > 700:
            notes = notes[:700].rstrip() + "…"
        install = self.can_install() and asset is not None
        text = t("upd.ask").format(new=tag, cur=APP_VERSION)
        if notes:
            text += "\n\n" + notes
        text += "\n\n" + (t("upd.yes_install") if install
                          else t("upd.yes_page"))
        if not messagebox.askyesno(t("upd.title"), text, parent=self.app):
            self.log(f"update {tag} available — not installed this time")
            return
        if not install:
            webbrowser.open(rel.get("html_url")
                            or f"https://github.com/{UPDATE_REPO}/releases")
            return
        threading.Thread(target=self._install, args=(tag, asset),
                         daemon=True).start()

    def _install(self, tag, asset):
        work = os.path.join(tempfile.gettempdir(), "ToNToolkit-update")
        try:
            if os.path.isdir(work):
                import shutil
                shutil.rmtree(work, ignore_errors=True)
            os.makedirs(work, exist_ok=True)
            zpath = os.path.join(work, asset["name"])
            self.log(f"downloading {tag}…")
            last = [-1]

            def hook(blocks, size, total):
                if total > 0:
                    pct = min(100, blocks * size * 100 // total)
                    if pct // 25 != last[0]:
                        last[0] = pct // 25
                        self.log(f"  {pct}%")
            urllib.request.urlretrieve(asset["browser_download_url"], zpath,
                                       hook)
            # GitHub publishes a SHA-256 for every release file; check it, so
            # a broken or tampered download is never installed.
            want = (asset.get("digest") or "").lower()
            if want.startswith("sha256:"):
                h = hashlib.sha256()
                with open(zpath, "rb") as f:
                    for chunk in iter(lambda: f.read(1 << 20), b""):
                        h.update(chunk)
                if h.hexdigest() != want.split(":", 1)[1]:
                    self.log("update stopped — the download is damaged "
                             "(checksum mismatch). Nothing was changed.")
                    return
            stage = os.path.join(work, "files")
            with zipfile.ZipFile(zpath) as z:
                z.extractall(stage)
            exe = os.path.basename(sys.executable)
            # The zip may hold the files directly or inside one folder.
            root = next((d for d, _s, files in os.walk(stage)
                         if exe in files), None)
            if not root:
                self.log(f"update stopped — {exe} is not in {asset['name']}. "
                         f"Nothing was changed.")
                return
            ps1 = os.path.join(work, "apply_update.ps1")
            with open(ps1, "w", encoding="ascii") as f:
                f.write(_UPDATE_PS1)
            subprocess.Popen(
                ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass",
                 "-WindowStyle", "Hidden", "-File", ps1,
                 "-AppPid", str(os.getpid()), "-Src", root, "-Dst", HERE,
                 "-Exe", exe],
                creationflags=0x00000008 | 0x00000200)  # detached, own group
            self.log(f"installing {tag} — the app will restart")
            self.app.after(800, self.app._close)
        except Exception as e:
            self.log(f"update failed: {e}. Nothing was changed.")

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(t("app.title"))
        self._set_icon()
        # Wider by default, with the settings taking most of it: the log is
        # glanced at, the settings are read and clicked.
        self.geometry("960x680")
        self.minsize(820, 560)
        self.queue = queue.Queue()

        self.core = Core(self.log)
        mods = [AfkJumper(self.core, self.log)] if PERSONAL_BUILD else []
        mods += [SpeedDetector(self.core, self.log),
                 AutoSkip(self.core, self.log),
                 RoundStarter(self.core, self.log)]
        self.core.modules = self.modules = mods

        self._load()
        self._build()
        # Tk is not thread safe, so route rebuild requests through after().
        self.core.ui_refresh = lambda: self.after(0, self._build_modules)
        self.after(250, self.core.ui_ready.set)
        self.after(100, self._drain)
        self.protocol("WM_DELETE_WINDOW", self._close)

        if not self.core.start():
            self.log("Start failed — is another OSC app using port 9001?")
        # A few seconds in, so the window is up before any dialog appears.
        self.updater = Updater(self)
        self.after(4000, lambda: threading.Thread(
            target=self.updater.check, daemon=True).start())

    # -- ui -----------------------------------------------------------------
    def _build(self):
        self.style = ttk.Style(self)
        self._apply_theme()

        # The footer must be packed BEFORE the expanding pane, otherwise pane
        # takes every remaining pixel and the language switch is clipped out
        # of the window with no way to reach it.
        foot = tk.Frame(self, bg=THEME["panel"])
        foot.pack(fill="x", side="bottom")
        tk.Frame(foot, bg=THEME["panel"]).pack(side="left", fill="x",
                                               expand=True)
        self.lbl_lang = tk.Label(foot, text=t("ui.language"),
                                 bg=THEME["panel"], fg=THEME["muted"],
                                 font=self.font_ui, padx=8)
        self.lbl_lang.pack(side="left")
        self.lang_var = tk.StringVar(value=LANG)
        for code, label in (("en", "EN"), ("ja", "日本語")):
            ttk.Radiobutton(foot, text=label, value=code,
                            variable=self.lang_var,
                            command=self._set_language).pack(side="left",
                                                             padx=(0, 6))

        pane = ttk.PanedWindow(self, orient="horizontal")
        pane.pack(fill="both", expand=True, padx=8, pady=8)

        self.left = ttk.Frame(pane, width=780)
        self.left.pack_propagate(False)
        pane.add(self.left, weight=4)
        right = ttk.Frame(pane, width=320)
        pane.add(right, weight=1)
        # Put the divider where we want it once the window has a real size;
        # without this the pane splits evenly and the log takes half.
        self.after(120, lambda: self._place_sash(pane))
        self._build_modules()

        bar = ttk.Frame(right)
        bar.pack(fill="x")
        self.lbl_activity = ttk.Label(bar, text=t("ui.activity"),
                                      style="Head.TLabel")
        self.lbl_activity.pack(side="left")
        self.btn_clear = ttk.Button(bar, text=t("ui.clear"), command=self._clear)
        self.btn_clear.pack(side="right")

        wrap = tk.Frame(right, bg=THEME["line"], padx=1, pady=1)
        wrap.pack(fill="both", expand=True, pady=(6, 0))
        self.text = tk.Text(wrap, wrap="word", height=10, state="disabled",
                            bg=THEME["panel"], fg=THEME["fg"], bd=0,
                            padx=10, pady=8, font=self.font_mono,
                            insertbackground=THEME["fg"],
                            selectbackground=THEME["raised"])
        ts = ttk.Scrollbar(wrap, orient="vertical", command=self.text.yview)
        self.text.configure(yscrollcommand=ts.set)
        self.text.pack(side="left", fill="both", expand=True)
        ts.pack(side="right", fill="y")
        # Colour by meaning so an alert is findable at a glance.
        self.text.tag_configure("alert", foreground=THEME["accent"])
        self.text.tag_configure("round", foreground=THEME["accent2"])
        self.text.tag_configure("dim", foreground=THEME["muted"])
        # The module tabs grab <MouseWheel> globally while the pointer is over
        # them, so the log needs its own binding to stay scrollable.
        self.text.bind("<Enter>", lambda e: self.text.bind_all(
            "<MouseWheel>",
            lambda ev: self.text.yview_scroll(-1 if ev.delta > 0 else 1,
                                              "units")))
        self.text.bind("<Leave>", lambda e: self.text.unbind_all("<MouseWheel>"))


    def _set_icon(self):
        """Window and taskbar icon. Says so in the log if it cannot be set."""
        ico = find_asset("icon.ico")
        if not ico:
            self.log("icon.ico not found — put it next to the exe "
                     "(looked in: " + ", ".join(
                         [HERE] + [os.path.dirname(x)
                                   for x in sound_dirs()]) + ")")
            return
        try:
            self.iconbitmap(default=ico)
        except Exception as e:
            self.log(f"could not apply icon: {e}")
        # Windows groups taskbar buttons by AppUserModelID. Without our own,
        # the button inherits python.exe's identity and its icon with it.
        if sys.platform == "win32":
            try:
                ctypes.windll.shell32.\
                    SetCurrentProcessExplicitAppUserModelID("ToN.Toolkit.1")
            except Exception:
                pass

    def _place_sash(self, pane, tries=12):
        """
        Put the divider at ~72% so the settings get the room.

        sashpos does nothing until the pane has actually been laid out, and
        the first attempt usually lands before that — so check the result and
        retry rather than assuming it took.
        """
        try:
            pane.update_idletasks()
            total = pane.winfo_width()
            want = int(total * 0.72)
            if total > 300:
                pane.sashpos(0, want)
                if abs(pane.sashpos(0) - want) <= 8:
                    return              # it stuck
            if tries > 0:
                self.after(120, lambda: self._place_sash(pane, tries - 1))
        except Exception:
            pass

    def _apply_theme(self):
        """Dark ttk styling plus a font that actually renders kanji well."""
        s = self.style
        try:
            s.theme_use("clam")        # the only stock theme that restyles fully
        except tk.TclError:
            pass
        c = THEME
        fam = pick_font(FONT_JA if LANG == "ja" else FONT_EN, self)
        size = 10 if LANG == "ja" else 9
        self.font_ui = (fam, size)
        UI_FONT[0] = self.font_ui
        self.font_bold = (fam, size, "bold")
        self.font_head = (fam, size + 1, "bold")
        self.font_mono = ("Cascadia Mono", size) if "Cascadia Mono" in \
            tkfont.families(self) else ("Consolas", size)

        self.configure(bg=c["bg"])
        s.configure(".", background=c["bg"], foreground=c["fg"],
                    fieldbackground=c["raised"], font=self.font_ui,
                    borderwidth=0, focuscolor=c["accent"])
        s.configure("TFrame", background=c["bg"])
        s.configure("TLabel", background=c["bg"], foreground=c["fg"])
        s.configure("Muted.TLabel", foreground=c["muted"])
        s.configure("Head.TLabel", foreground=c["fg"], font=self.font_head)
        s.configure("Status.TLabel", background=c["panel"],
                    foreground=c["muted"], padding=6)

        s.configure("TNotebook", background=c["bg"], borderwidth=0,
                    tabmargins=(0, 2, 0, 0))
        s.configure("TNotebook.Tab", background=c["panel"],
                    foreground=c["muted"], padding=(18, 9),
                    font=self.font_bold, borderwidth=0)
        s.map("TNotebook.Tab",
              background=[("selected", c["raised"]), ("active", c["line"])],
              foreground=[("selected", c["accent"]), ("active", c["fg"])],
              # Without this clam grows the selected tab, which reads as the
              # tab sinking into the panel. Keep the geometry fixed and let
              # colour alone carry the selection.
              expand=[("selected", [0, 0, 0, 0])])

        s.configure("TLabelframe", background=c["panel"], borderwidth=1,
                    relief="solid", bordercolor=c["line"], padding=10)
        s.configure("TLabelframe.Label", background=c["panel"],
                    foreground=c["accent"], font=self.font_head)

        s.configure("TCheckbutton", background=c["bg"], foreground=c["fg"],
                    indicatorcolor=c["raised"], padding=3)
        s.map("TCheckbutton",
              indicatorcolor=[("selected", c["accent"])],
              foreground=[("active", c["accent2"])],
              background=[("active", c["bg"])])

        s.configure("TEntry", fieldbackground=c["raised"], foreground=c["fg"],
                    insertcolor=c["fg"], bordercolor=c["line"],
                    lightcolor=c["line"], darkcolor=c["line"], padding=4)
        s.configure("TButton", background=c["raised"], foreground=c["fg"],
                    padding=(14, 8), font=self.font_bold, borderwidth=0,
                    relief="flat", anchor="center")
        s.map("TButton",
              background=[("pressed", c["accent"]), ("active", c["line"])],
              foreground=[("pressed", "#ffffff"), ("active", c["accent2"])],
              relief=[("pressed", "flat"), ("active", "flat")])
        s.configure("TRadiobutton", background=c["panel"],
                    foreground=c["muted"])
        s.map("TRadiobutton", foreground=[("selected", c["accent"])],
              background=[("active", c["panel"])])
        s.configure("TSeparator", background=c["line"])
        s.configure("Horizontal.TScale", background=c["bg"],
                    troughcolor=c["raised"], bordercolor=c["line"],
                    lightcolor=c["accent"], darkcolor=c["accent"])
        s.configure("TPanedwindow", background=c["bg"])
        s.configure("Vertical.TScrollbar", background=c["raised"],
                    troughcolor=c["bg"], bordercolor=c["bg"],
                    arrowcolor=c["muted"])

    def _scrollable(self, parent):
        """
        A scrolling page. Returns the frame to put content in.

        The wheel is bound on Enter and released on Leave rather than
        globally, so scrolling only affects the panel the pointer is over —
        the log pane keeps its own scrollbar.
        """
        canvas = tk.Canvas(parent, bg=THEME["bg"], highlightthickness=0, bd=0)
        bar = ttk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        inner = ttk.Frame(canvas, padding=(8, 8, 14, 8))
        win = canvas.create_window((0, 0), window=inner, anchor="nw")

        canvas.configure(yscrollcommand=bar.set)
        canvas.pack(side="left", fill="both", expand=True)
        bar.pack(side="right", fill="y")

        inner.bind("<Configure>",
                   lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>",
                    lambda e: canvas.itemconfigure(win, width=e.width))

        def wheel(e):
            canvas.yview_scroll(-1 if e.delta > 0 else 1, "units")

        canvas.bind("<Enter>",
                    lambda e: canvas.bind_all("<MouseWheel>", wheel))
        canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))
        return inner

    def _build_modules(self):
        """
        (Re)build the module tabs. Called again when the language changes.

        Modules sharing a tab_key are stacked on one page, each in its own
        labelled box with its own Enabled checkbox — merging the UI without
        merging the modules, so their logic stays independent.
        """
        for child in self.left.winfo_children():
            child.destroy()
        nb = ttk.Notebook(self.left)
        nb.pack(fill="both", expand=True)

        pages, order = {}, []
        for m in self.modules:
            tk_key = m.tab_key or m.name_key
            if tk_key not in pages:
                pages[tk_key] = []
                order.append(tk_key)
            pages[tk_key].append(m)

        for tk_key in order:
            group = pages[tk_key]
            shell = ttk.Frame(nb)
            nb.add(shell, text=t(tk_key))
            page = self._scrollable(shell)
            for m in group:
                if len(group) > 1:
                    box = ttk.LabelFrame(page, text=m.name, padding=8)
                    box.pack(fill="x", pady=(0, 8))
                else:
                    box = page
                cb = Toggle(box, m.enabled, text=t("ui.enabled") +
                            ("  ⍰" if m.tip_key else ""))
                cb.pack(anchor="w", pady=(0, 2))
                if m.tip_key:
                    Tip(cb, t(m.tip_key))
                ttk.Label(box, text=m.blurb, wraplength=700, justify="left",
                          style="Muted.TLabel").pack(anchor="w", pady=(2, 6))
                if len(group) == 1:
                    ttk.Separator(box).pack(fill="x", pady=(0, 6))
                m.build(box)

    def _set_language(self):
        """
        Settings live in the Module objects, not the widgets, so the tabs can
        simply be thrown away and rebuilt — nothing the user typed is lost.
        """
        global LANG
        LANG = self.lang_var.get()
        self._apply_theme()          # font family/size differs per language
        self.title(t("app.title"))
        self.lbl_activity.configure(text=t("ui.activity"))
        self.btn_clear.configure(text=t("ui.clear"))
        self.lbl_lang.configure(text=t("ui.language"), font=self.font_ui)
        self.text.configure(font=self.font_mono)
        self._build_modules()

    def log(self, msg):
        self.queue.put(f"[{time.strftime('%H:%M:%S')}] {msg}")

    def _drain(self):
        wrote = False
        while True:
            try:
                line = self.queue.get_nowait()
            except queue.Empty:
                break
            tag = ("alert" if "!!" in line else
                   "round" if "->" in line or "@" in line else
                   "dim" if line.count(":") > 2 and "  " in line else "")
            self.text.configure(state="normal")
            self.text.insert("end", line + "\n", tag)
            self.text.configure(state="disabled")
            wrote = True
        if wrote:
            self.text.see("end")
        self.after(150, self._drain)

    def _clear(self):
        self.text.configure(state="normal")
        self.text.delete("1.0", "end")
        self.text.configure(state="disabled")

    # -- settings -----------------------------------------------------------
    def _load(self):
        try:
            with open(CONFIG_FILE, encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, json.JSONDecodeError):
            for m in self.modules:      # no settings file yet
                m.after_load()
            return
        global LANG
        LANG = data.get("_lang", LANG)
        for m in self.modules:
            blob = data.get(m.key, {})
            m.enabled.set(bool(blob.get("enabled", False)))
            if "learned" in blob:
                m.vars["learned"].set(blob["learned"])
            for k in m.code_only:          # always take the code default
                blob.pop(k, None)
            for k, v in blob.items():
                if k not in m.vars and k.startswith("r_"):
                    m.vars[k] = tk.BooleanVar(value=bool(v))
            for k, var in m.vars.items():
                if k not in blob:
                    continue
                val = blob[k]
                # An empty saved string must not wipe out a default that was
                # auto-detected at startup — that is why the sound paths came
                # up blank after the first run.
                if val == "" and m.defaults.get(k):
                    continue
                var.set(val)
            m.after_load()

    def _save(self):
        data = {m.key: dict({k: v.get() for k, v in m.vars.items()
                             if k not in m.code_only
                             and not k.startswith(m.volatile or ("\0",))},
                            enabled=m.enabled.get())
                for m in self.modules}
        data["_lang"] = LANG
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except OSError:
            pass

    def _close(self):
        self.core.ui_ready.clear()      # stop threads touching Tk as it dies
        self._save()
        self.core.shutdown()
        self.destroy()


if __name__ == "__main__":
    App().mainloop()