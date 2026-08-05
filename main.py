from __future__ import annotations

import argparse
import base64
import contextlib
import ctypes
import hashlib
import io
import json
import math
import os
import queue
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
import webbrowser
from collections import Counter
from ctypes import wintypes
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from threading import Event, Lock, Thread
from typing import Callable, Iterable
from urllib.parse import urlencode

import pyautogui
import pygetwindow as gw
import requests
from mss import MSS
from PIL import Image, ImageChops, ImageDraw, ImageEnhance, ImageFilter, ImageFont, ImageOps, ImageStat

try:
    import pytesseract
except Exception:  # pragma: no cover - optional dependency at runtime
    pytesseract = None
else:
    for candidate in (
        Path(r"C:\Program Files\Tesseract-OCR\tesseract.exe"),
        Path(r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe"),
        Path.home() / r"AppData\Local\Programs\Tesseract-OCR\tesseract.exe",
    ):
        if candidate.exists():
            pytesseract.pytesseract.tesseract_cmd = str(candidate)
            break

try:
    import cv2
    import numpy as np
except Exception:  # pragma: no cover - optional dependency at runtime
    cv2 = None
    np = None

try:
    import onnxruntime as ort
except Exception:  # pragma: no cover - optional dependency at runtime
    ort = None


def _as_int(value, default: int) -> int:
    try:
        return int(value)
    except Exception:
        return default


@dataclass(slots=True)
class SpeedAnalysis:
    input_speed: float
    base_speed: float
    hasty_guard: bool = False
    gifted_hasty: bool = False
    both_hasty_bonuses: bool = False
    divisor: float = 1.0

    @property
    def permanent_multiplier(self) -> float:
        multiplier = 1.0
        if self.hasty_guard:
            multiplier *= 1.10
        if self.gifted_hasty:
            multiplier *= 1.15
        return multiplier

    @property
    def manual_speed(self) -> float:
        return max(1.0, self.base_speed * self.permanent_multiplier)


def _nearly_multiple(value: float, divisor: float, tolerance: float = 0.00001) -> bool:
    if divisor <= 0:
        return False
    remainder = math.fmod(value, divisor)
    return remainder < tolerance or abs(remainder - divisor) < tolerance


def analyse_movespeed(move_speed_num: float) -> SpeedAnalysis:
    """Mirror Natro's MoveSpeedNum handling for Hasty Guard / gifted Hasty Bee."""
    try:
        movespeed = float(move_speed_num)
    except Exception:
        movespeed = 30.0
    if not math.isfinite(movespeed) or movespeed <= 0:
        movespeed = 30.0

    scaled = movespeed * 1000.0
    rounded_scaled = round((movespeed + 0.005) * 1000.0)
    both = _nearly_multiple(scaled, 1265.0) or _nearly_multiple(rounded_scaled, 1265.0)
    hasty_guard = both or _nearly_multiple(scaled, 1100.0)
    gifted_hasty = both or _nearly_multiple(scaled, 1150.0)
    divisor = 1.265 if both else (1.10 if hasty_guard else (1.15 if gifted_hasty else 1.0))
    base_speed = float(max(1, round(movespeed / divisor)))
    return SpeedAnalysis(
        input_speed=movespeed,
        base_speed=base_speed,
        hasty_guard=bool(hasty_guard),
        gifted_hasty=bool(gifted_hasty),
        both_hasty_bonuses=bool(both),
        divisor=float(divisor),
    )


def effective_walk_speed(move_speed_num: float, multiplier: float = 1.0, flat_bonus: float = 0.0) -> tuple[float, SpeedAnalysis]:
    analysis = analyse_movespeed(move_speed_num)
    temp_multiplier = max(0.1, float(multiplier))
    temp_flat_bonus = max(0.0, float(flat_bonus))
    speed = (analysis.base_speed + temp_flat_bonus) * analysis.permanent_multiplier * temp_multiplier
    return max(1.0, speed), analysis


def path_movement_time_multiplier(cfg) -> float:
    try:
        value = float(cfg.get("paths.movement_time_multiplier", 1.0))
    except Exception:
        value = 1.0
    if not math.isfinite(value):
        value = 1.0
    return max(0.1, min(5.0, value))

try:
    from bson import BSON
except Exception:  # pragma: no cover - optional dependency at runtime
    BSON = None


ROOT = Path(__file__).resolve().parent
DEFAULT_CONFIG = ROOT / "config.json"
PATH_REFERENCE_SPEED = 29.0
TESSERACT_WINDOWS_INSTALLER_URL = (
    "https://github.com/tesseract-ocr/tesseract/releases/download/5.5.0/"
    "tesseract-ocr-w64-setup-5.5.0.20241111.exe"
)
TESSERACT_WINDOWS_INSTALLER_SHA256 = "F3FC4236425B690C8BE756F35793F77394EE004BE0A6460A440C754D892F68BC"


KEYS = {
    "forward": "w",
    "backward": "s",
    "left": "a",
    "right": "d",
    "space": "space",
    "shift": "shift",
    "lshift": "shiftleft",
    "rshift": "shiftright",
    "e": "e",
    "r": "r",
    "enter": "enter",
    "escape": "escape",
    "rot_left": ",",
    "rot_right": ".",
    "rot_down": "pagedown",
    "rot_up": "pageup",
    "zoom_in": "i",
    "zoom_out": "o",
}

VK_KEYS = {
    "forward": (0x57, False),
    "backward": (0x53, False),
    "left": (0x41, False),
    "right": (0x44, False),
    "space": (0x20, False),
    "shift": (0xA0, False),
    "lshift": (0xA0, False),
    "rshift": (0xA1, False),
    "e": (0x45, False),
    "r": (0x52, False),
    "enter": (0x0D, False),
    "escape": (0x1B, False),
    "rot_up": (0x21, True),
    "rot_down": (0x22, True),
    "rot_left": (0xBC, False),
    "rot_right": (0xBE, False),
    "zoom_in": (0x49, False),
    "zoom_out": (0x4F, False),
}

if sys.platform.startswith("win"):
    _user32 = ctypes.WinDLL("user32", use_last_error=True)
    _map_virtual_key = _user32.MapVirtualKeyW
    _keybd_event = _user32.keybd_event
else:
    _user32 = None
    _map_virtual_key = None
    _keybd_event = None


if sys.platform.startswith("win"):
    ULONG_PTR = ctypes.c_ulonglong if ctypes.sizeof(ctypes.c_void_p) == 8 else ctypes.c_ulong

    class MOUSEINPUT(ctypes.Structure):
        _fields_ = (
            ("dx", ctypes.c_long),
            ("dy", ctypes.c_long),
            ("mouseData", ctypes.c_ulong),
            ("dwFlags", ctypes.c_ulong),
            ("time", ctypes.c_ulong),
            ("dwExtraInfo", ULONG_PTR),
        )

    class KEYBDINPUT(ctypes.Structure):
        _fields_ = (
            ("wVk", ctypes.c_ushort),
            ("wScan", ctypes.c_ushort),
            ("dwFlags", ctypes.c_ulong),
            ("time", ctypes.c_ulong),
            ("dwExtraInfo", ULONG_PTR),
        )

    class HARDWAREINPUT(ctypes.Structure):
        _fields_ = (
            ("uMsg", ctypes.c_ulong),
            ("wParamL", ctypes.c_ushort),
            ("wParamH", ctypes.c_ushort),
        )

    class INPUTUNION(ctypes.Union):
        _fields_ = (
            ("mi", MOUSEINPUT),
            ("ki", KEYBDINPUT),
            ("hi", HARDWAREINPUT),
        )

    class INPUT(ctypes.Structure):
        _fields_ = (("type", ctypes.c_ulong), ("union", INPUTUNION))

    _send_input = _user32.SendInput
else:
    INPUT = None
    MOUSEINPUT = None
    KEYBDINPUT = None
    HARDWAREINPUT = None
    INPUTUNION = None
    _send_input = None


@dataclass
class Server:
    id: str


class Config:
    def __init__(self, path: Path):
        path = path.resolve()
        if not path.exists():
            raise FileNotFoundError(f"Config missing: {path}. Copy config.example.json to config.json first.")
        self.path = path
        self.base_dir = path.parent
        self.data = json.loads(path.read_text(encoding="utf-8-sig"))

    def get(self, key: str, default=None):
        value = self.data
        for part in key.split("."):
            if not isinstance(value, dict) or part not in value:
                return default
            value = value[part]
        return value


class RejoinRequested(RuntimeError):
    pass


class ApiRateLimited(RuntimeError):
    pass


class PathComplete(RuntimeError):
    pass


class PathMonitorTriggered(RuntimeError):
    pass


class Screen:
    def __init__(self):
        self.sct = MSS()

    def shot(self) -> Image.Image:
        monitor = self.sct.monitors[1]
        raw = self.sct.grab(monitor)
        return Image.frombytes("RGB", raw.size, raw.bgra, "raw", "BGRX")

    def size(self) -> tuple[int, int]:
        monitor = self.sct.monitors[1]
        return int(monitor["width"]), int(monitor["height"])

    def shot_box(self, left: int, top: int, width: int, height: int) -> Image.Image:
        monitor = self.sct.monitors[1]
        box = {
            "left": int(monitor["left"]) + max(0, int(left)),
            "top": int(monitor["top"]) + max(0, int(top)),
            "width": max(1, int(width)),
            "height": max(1, int(height)),
        }
        raw = self.sct.grab(box)
        return Image.frombytes("RGB", raw.size, raw.bgra, "raw", "BGRX")

    def shot_box_bgr(self, left: int, top: int, width: int, height: int):
        monitor = self.sct.monitors[1]
        box = {
            "left": int(monitor["left"]) + max(0, int(left)),
            "top": int(monitor["top"]) + max(0, int(top)),
            "width": max(1, int(width)),
            "height": max(1, int(height)),
        }
        raw = self.sct.grab(box)
        arr = np.frombuffer(raw.bgra, dtype=np.uint8).reshape((box["height"], box["width"], 4))
        return arr[:, :, :3]


class Input:
    def __init__(self, cfg: Config, dry_run: bool, stop_event: Event | None = None):
        self.cfg = cfg
        self.dry_run = dry_run
        self.stop_event = stop_event
        self.speed_multiplier_provider: Callable[[], float | tuple[float, float]] | None = None
        self._movement_key_down_at: dict[str, float] = {}
        self.verbose = True
        pyautogui.FAILSAFE = True
        pyautogui.PAUSE = 0.02

    def stopped(self) -> bool:
        return bool(self.stop_event and self.stop_event.is_set())

    def check_stop(self):
        if self.stopped():
            raise RuntimeError("Stopped by user.")

    def log(self, msg: str):
        if not self.verbose:
            return
        print(msg, flush=True)

    def focus_roblox(self):
        wins = self.roblox_windows()
        if not wins:
            self.log("Nu am gasit fereastra Roblox. Continui, dar inputul merge catre fereastra activa.")
            return
        win = wins[0]
        if self.dry_run:
            self.log(f"[dry-run] focus Roblox: {win.title}")
            return
        try:
            win.activate()
            time.sleep(0.5)
            rect = self.roblox_window_rect()
            if rect is not None:
                left, top, width, height = rect
                pyautogui.click(left + int(width * 0.82), top + int(height * 0.07))
                time.sleep(0.15)
        except Exception as exc:
            self.log(f"Nu pot activa fereastra Roblox: {exc}")

    def roblox_windows(self):
        browser_words = ("chrome", "edge", "firefox", "opera", "brave")
        wins = [w for w in gw.getAllWindows() if "roblox" in w.title.lower()]
        app_wins = [w for w in wins if not any(word in w.title.lower() for word in browser_words)]
        exact = [w for w in app_wins if w.title.strip().lower() == "roblox"]
        return exact or app_wins or wins

    def roblox_window_rect(self):
        wins = self.roblox_windows()
        if not wins:
            return None
        win = wins[0]
        return win.left, win.top, win.width, win.height

    def setup_camera_for_night_check(self):
        self.check_stop()
        cfg = self.cfg.get("camera_setup", {}) or {}
        rect = self.roblox_window_rect()
        self.log("camera setup with keyboard\n")
        if self.dry_run:
            return
        if rect is not None and cfg.get("click_center", True):
            left, top, width, height = rect
            cx = left + width // 2
            cy = top + height // 2
            pyautogui.click(left + int(width * 0.82), top + int(height * 0.07))
            time.sleep(float(cfg.get("click_center_delay_seconds", 0.04)))
        hold = float(cfg.get("night_key_hold_seconds", cfg.get("key_hold_seconds", 0.06)))
        gap = float(cfg.get("night_between_keys_seconds", cfg.get("between_keys_seconds", 0.025)))
        self.press_camera_key("zoom_in", int(cfg.get("zoom_in_presses", 4)), hold, gap)
        self.press_camera_key("zoom_out", int(cfg.get("zoom_out_presses", 2)), hold, gap)
        self.press_camera_key("rot_down", int(cfg.get("rot_down_presses", 3)), hold, gap)
        time.sleep(float(cfg.get("night_after_camera_delay_seconds", 0.04)))

    def zoom_out_max(self):
        self.check_stop()
        cfg = self.cfg.get("camera_setup", {}) or {}
        rect = self.roblox_window_rect()
        self.log("zoom out max for hive scan\n")
        if self.dry_run:
            return
        if rect is not None and cfg.get("hive_click_center_before_zoom", False):
            left, top, width, height = rect
            pyautogui.click(left + int(width * 0.82), top + int(height * 0.07))
            time.sleep(float(cfg.get("hive_click_center_delay_seconds", 0.03)))
        hold = float(cfg.get("hive_zoom_key_hold_seconds", cfg.get("key_hold_seconds", 0.12)))
        gap = float(cfg.get("hive_zoom_gap_seconds", cfg.get("between_keys_seconds", 0.08)))
        self.press_camera_key("zoom_out", int(cfg.get("hive_zoom_out_presses", 18)), hold, gap)
        time.sleep(float(cfg.get("hive_zoom_after_delay_seconds", 0.02)))

    def zoom_in_after_hive_scan(self):
        self.check_stop()
        cfg = self.cfg.get("camera_setup", {}) or {}
        self.log("zoom in after hive scan\n")
        if self.dry_run:
            return
        hold = float(cfg.get("hive_zoom_key_hold_seconds", cfg.get("key_hold_seconds", 0.12)))
        gap = float(cfg.get("hive_zoom_gap_seconds", cfg.get("between_keys_seconds", 0.08)))
        self.press_camera_key("zoom_in", int(cfg.get("hive_zoom_in_after_scan_presses", 12)), hold, gap)
        time.sleep(float(cfg.get("hive_zoom_after_delay_seconds", 0.02)))

    def reset_camera_after_hive_claim(self):
        self.check_stop()
        cfg = self.cfg.get("camera_setup", {}) or {}
        if not cfg.get("reset_after_hive_claim", True):
            return
        self.log("reset camera after hive claim\n")
        if self.dry_run:
            return
        rect = self.roblox_window_rect()
        if rect is not None and cfg.get("click_center", True):
            left, top, width, height = rect
            pyautogui.click(left + int(width * 0.82), top + int(height * 0.07))
            time.sleep(float(cfg.get("click_center_delay_seconds", 0.04)))
        hold = float(cfg.get("hive_zoom_key_hold_seconds", cfg.get("key_hold_seconds", 0.12)))
        gap = float(cfg.get("hive_zoom_gap_seconds", cfg.get("between_keys_seconds", 0.08)))
        rot_down = int(cfg.get("after_hive_claim_rot_down_presses", cfg.get("hive_red_arrow_rot_up_presses", 2)))
        zoom_in = int(cfg.get("after_hive_claim_zoom_in_presses", 18))
        zoom_out = int(cfg.get("after_hive_claim_zoom_out_presses", cfg.get("zoom_out_presses", 2)))
        self.press_camera_key("rot_down", rot_down, hold, gap)
        self.press_camera_key("zoom_in", zoom_in, hold, gap)
        self.press_camera_key("zoom_out", zoom_out, hold, gap)
        time.sleep(float(cfg.get("after_hive_claim_delay_seconds", 0.08)))

    def press_camera_key(self, name: str, repeats: int, hold: float, gap: float):
        for _ in range(max(0, repeats)):
            self.check_stop()
            self.log(f"camera press {name}\n")
            self.send_camera_key(name, down=True)
            time.sleep(hold)
            self.send_camera_key(name, down=False)
            self.sleep(gap)

    def send_camera_key(self, name: str, down: bool):
        if sys.platform.startswith("win") and name in VK_KEYS:
            vk, extended = VK_KEYS[name]
            scan = int(_map_virtual_key(vk, 0)) if _map_virtual_key else 0
            flags = 0x0001 if extended else 0
            if not down:
                flags |= 0x0002
            _keybd_event(vk, scan, flags, 0)
            return
        self.send_key(name, down=down)

    def wait_for_roblox(self, timeout_seconds: float) -> bool:
        end = time.time() + timeout_seconds
        while time.time() < end:
            self.check_stop()
            wins = self.roblox_windows()
            if wins:
                self.focus_roblox()
                return True
            self.sleep(1.0)
        return False

    def key_down(self, name: str):
        self.check_stop()
        self.log(f"down {name}")
        if not self.dry_run:
            self.send_key(name, down=True)
            if name in {"forward", "backward", "left", "right"}:
                self._movement_key_down_at.setdefault(name, time.perf_counter())

    def key_up(self, name: str):
        self.log(f"up {name}")
        if not self.dry_run:
            self.send_key(name, down=False)
        started_at = self._movement_key_down_at.pop(name, None)
        if started_at is not None and bool(self.cfg.get("paths.log_movement_timing", True)):
            print(f"PATH_KEY_HOLD key={name} actual={time.perf_counter() - started_at:.6f}s", flush=True)

    def release_shift(self):
        self.log("release shift/lshift/rshift")
        if self.dry_run:
            return
        for key in ("shift", "lshift", "rshift"):
            self.send_key(key, down=False)
            time.sleep(0.01)
        if sys.platform.startswith("win"):
            for vk in (0x10, 0xA0, 0xA1):
                try:
                    _user32.keybd_event(vk, 0, 0x0002, 0)
                except Exception:
                    pass
        try:
            pyautogui.keyUp("shift")
        except Exception:
            pass

    def release_path_keys(self):
        self.log("release path keys")
        self._movement_key_down_at.clear()
        if self.dry_run:
            return
        for key in ("forward", "backward", "left", "right", "space", "shift", "rot_left", "rot_right", "rot_up", "rot_down"):
            with contextlib.suppress(Exception):
                self.send_key(key, down=False)
        for key in ("w", "s", "a", "d", "space", "shift", "shiftleft", "left", "right", "up", "down", "pageup", "pagedown"):
            with contextlib.suppress(Exception):
                pyautogui.keyUp(key)

    def press(self, name: str, repeats: int = 1, interval: float = 0.08):
        for _ in range(repeats):
            self.check_stop()
            self.log(f"press {name}")
            if not self.dry_run:
                self.send_key(name, down=True)
                time.sleep(float(self.cfg.get("key_press_seconds", 0.08)))
                self.send_key(name, down=False)
            self.sleep(interval)

    def fast_tap(self, name: str, repeats: int = 1, hold: float = 0.025, interval: float = 0.008):
        self.check_stop()
        self.log(f"fast tap {name} x{repeats}")
        if self.dry_run:
            return
        for _ in range(max(1, repeats)):
            self.send_key(name, down=True)
            time.sleep(max(0.005, hold))
            self.send_key(name, down=False)
            if interval > 0:
                time.sleep(interval)

    def fast_tap_silent(self, name: str, hold: float = 0.012):
        if self.dry_run:
            return
        self.send_key(name, down=True)
        time.sleep(max(0.003, hold))
        self.send_key(name, down=False)

    def send_key(self, name: str, down: bool):
        if sys.platform.startswith("win") and name in VK_KEYS:
            vk, extended = VK_KEYS[name]
            scan = int(_map_virtual_key(vk, 0)) if _map_virtual_key else 0
            flags = 0x0008  # KEYEVENTF_SCANCODE
            if extended:
                flags |= 0x0001
            if not down:
                flags |= 0x0002
            inp = INPUT()
            inp.type = 1  # INPUT_KEYBOARD
            inp.union.ki = KEYBDINPUT(0, scan, flags, 0, 0)
            sent = _send_input(1, ctypes.byref(inp), ctypes.sizeof(INPUT))
            if sent == 0:
                err = ctypes.get_last_error()
                print(f"SendInput failed for {name}: {err}", flush=True)
            return
        key = KEYS[name]
        if down:
            pyautogui.keyDown(key)
        else:
            pyautogui.keyUp(key)

    def walk(self, direction: str, studs: float, tick_callback: Callable[[], bool] | None = None, tick_interval: float = 0.05):
        self.check_stop()
        manual_speed = float(self.cfg.get("move_speed_studs_per_second", 29.0))
        multiplier = 1.0
        flat_bonus = 0.0
        if self.speed_multiplier_provider is not None:
            try:
                speed_adjustment = self.speed_multiplier_provider()
                if isinstance(speed_adjustment, tuple):
                    multiplier = max(0.1, float(speed_adjustment[0]))
                    flat_bonus = max(0.0, float(speed_adjustment[1]))
                else:
                    multiplier = max(0.1, float(speed_adjustment))
            except Exception as exc:
                self.log(f"speed multiplier unavailable: {exc}")
                multiplier = 1.0
                flat_bonus = 0.0
        speed, speed_info = effective_walk_speed(manual_speed, multiplier, flat_bonus)
        time_multiplier = path_movement_time_multiplier(self.cfg)
        seconds = max(0.02, studs / speed * time_multiplier)
        path_scale = PATH_REFERENCE_SPEED / speed * time_multiplier
        self.log(
            f"walk {direction} {studs:.1f} studs "
            f"(speed {speed:.1f}, manual {speed_info.input_speed:.1f}, "
            f"base {speed_info.base_speed:.1f}, perm x{speed_info.permanent_multiplier:.3f}, "
            f"temp x{multiplier:.2f}, +{flat_bonus:.1f}, "
            f"cal x{time_multiplier:.3f}, scale {path_scale:.3f}, {seconds:.2f}s)"
        )
        self.key_down(direction)
        try:
            if tick_callback is None:
                self.sleep(seconds)
            else:
                end = time.time() + seconds
                interval = max(0.02, float(tick_interval))
                while time.time() < end:
                    self.check_stop()
                    if tick_callback():
                        self.key_down(direction)
                    wait = min(interval, max(0.0, end - time.time()))
                    if wait <= 0:
                        break
                    time.sleep(wait)
        finally:
            self.key_up(direction)

    def sleep(self, seconds: float):
        try:
            requested = float(seconds)
        except (TypeError, ValueError):
            self.log(f"invalid sleep value ignored: {seconds!r}")
            return
        if not math.isfinite(requested) or requested <= 0:
            # A timer can expire between the loop condition and time.sleep().
            # Treat an already-finished wait as complete instead of killing the macro.
            return
        self.log(f"sleep {requested:.2f}s")
        remaining = min(requested, 0.05) if self.dry_run else requested
        end = time.time() + remaining
        while time.time() < end:
            self.check_stop()
            wait = min(0.05, end - time.time())
            if wait <= 0:
                break
            time.sleep(wait)


class RobloxServers:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.cursor = ""
        self.seen: set[str] = set()

    def fetch_page(self) -> list[Server]:
        place_id = self.cfg.get("roblox_place_id", 1537690962)
        params = {
            "cursor": self.cursor,
            "sortOrder": self.cfg.get("public_server_sort", "Desc"),
            "excludeFullGames": str(bool(self.cfg.get("exclude_full_games", True))).lower(),
            "limit": 100,
        }
        url = f"https://games.roblox.com/v1/games/{place_id}/servers/Public"
        max_retries = int(self.cfg.get("api_max_retries", 8))
        base_wait = float(self.cfg.get("api_rate_limit_wait_seconds", 20))
        fallback_random = bool(self.cfg.get("api_rate_limit_random_deeplink", True))
        for attempt in range(1, max_retries + 1):
            try:
                resp = requests.get(url, params=params, timeout=20)
            except requests.RequestException as exc:
                if fallback_random:
                    print(f"Roblox API request failed ({exc}). Using random place deeplink instead.", flush=True)
                    raise ApiRateLimited("Roblox API request failed") from exc
                wait = base_wait * attempt
                print(f"Roblox API request failed ({exc}). Waiting {wait:.0f}s ({attempt}/{max_retries})", flush=True)
                time.sleep(wait)
                continue
            if resp.status_code != 429:
                if 500 <= resp.status_code < 600:
                    if self.cursor:
                        print(
                            f"Roblox API {resp.status_code} for saved cursor. Resetting cursor and retrying.",
                            flush=True,
                        )
                        self.cursor = ""
                        params["cursor"] = ""
                        continue
                    if fallback_random:
                        print(
                            f"Roblox API temporarily unavailable ({resp.status_code}). "
                            "Using random place deeplink instead.",
                            flush=True,
                        )
                        raise ApiRateLimited("Roblox API temporarily unavailable")
                    wait = base_wait * attempt
                    print(f"Roblox API {resp.status_code}. Waiting {wait:.0f}s ({attempt}/{max_retries})", flush=True)
                    time.sleep(wait)
                    continue
                resp.raise_for_status()
                break
            if fallback_random:
                print("Roblox API rate limited. Using random place deeplink instead.", flush=True)
                raise ApiRateLimited("Roblox API rate limited")
            retry_after = resp.headers.get("Retry-After")
            wait = float(retry_after) if retry_after and retry_after.isdigit() else base_wait * attempt
            print(f"Roblox API rate limited. Waiting {wait:.0f}s ({attempt}/{max_retries})", flush=True)
            time.sleep(wait)
        else:
            raise RuntimeError("Roblox API inca este rate limited dupa mai multe incercari.")
        payload = resp.json()
        self.cursor = payload.get("nextPageCursor") or ""
        servers = [Server(item["id"]) for item in payload.get("data", []) if item.get("id")]
        random.shuffle(servers)
        return servers

    def next_server(self) -> Server:
        while True:
            for server in self.fetch_page():
                if server.id not in self.seen:
                    self.seen.add(server.id)
                    return server
            if not self.cursor:
                self.cursor = ""

    def join(self, server: Server, dry_run: bool):
        place_id = self.cfg.get("roblox_place_id", 1537690962)
        query = urlencode({"placeId": place_id, "gameInstanceId": server.id})
        method = str(self.cfg.get("launch_method", "protocol")).lower()
        uri = f"roblox://experiences/start?{query}"
        if method == "web":
            uri = f"https://www.roblox.com/games/start?{query}"
        print(f"Joining server {server.id}", flush=True)
        if dry_run:
            print(f"[dry-run] {uri}", flush=True)
            return
        if sys.platform.startswith("win"):
            os.startfile(uri)  # type: ignore[attr-defined]
        else:
            webbrowser.open(uri)

    def join_random_public(self, dry_run: bool):
        place_id = self.cfg.get("roblox_place_id", 1537690962)
        query = urlencode({"placeId": place_id})
        method = str(self.cfg.get("launch_method", "protocol")).lower()
        uri = f"roblox://experiences/start?{query}"
        if method == "web":
            uri = f"https://www.roblox.com/games/start?{query}"
        print("Joining random public server via place deeplink", flush=True)
        if dry_run:
            print(f"[dry-run] {uri}", flush=True)
            return
        if sys.platform.startswith("win"):
            os.startfile(uri)  # type: ignore[attr-defined]
        else:
            webbrowser.open(uri)

    def close_roblox(self, dry_run: bool):
        if not self.cfg.get("close_before_rejoin", False):
            print("Rejoin via deeplink without closing Roblox", flush=True)
            return
        print("Closing Roblox before rejoin", flush=True)
        if dry_run or not sys.platform.startswith("win"):
            return
        subprocess.run(
            ["taskkill", "/IM", "RobloxPlayerBeta.exe", "/F"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )


class Detector:
    def __init__(self, cfg: Config, screen: Screen):
        self.cfg = cfg
        self.screen = screen
        template_dir = Path(str(cfg.get("template_dir", "templates") or "templates"))
        if not template_dir.is_absolute():
            template_dir = cfg.base_dir / template_dir
        self.template_dir = template_dir.resolve()
        self._rgba_template_cache: dict[str, tuple[np.ndarray, np.ndarray, np.ndarray] | None] = {}
        self._white_mask_template_cache: dict[str, np.ndarray | None] = {}
        self._speed_stack_template_cache: list[tuple[int, str, np.ndarray]] | None = None
        self._speed_corner_template_cache: list[tuple[int, str, np.ndarray]] | None = None
        self._speed_green_stack_template_cache: list[tuple[int, str, np.ndarray]] | None = None
        self._speed_runner_stack_mask_cache: list[tuple[int, str, np.ndarray]] | None = None
        self._speed_runner_digit_mask_cache: list[tuple[int, str, np.ndarray]] | None = None
        self._speed_runner_icon_mask_cache: list[tuple[str, np.ndarray]] | None = None
        self._natro_digit_template_cache: dict[int, np.ndarray] | None = None
        self._last_haste_line_candidates: list[str] = []
        self._last_natro_haste_stack = 0
        self._last_natro_haste_seen_at = 0.0
        self._natro_haste_animation_fallback_reads = 0
        self._honey_offset_cache: tuple[tuple[int, int] | None, float] = (None, 0.0)
        self._speed_multiplier_cache: tuple[tuple[float, float], float] = ((1.0, 0.0), 0.0)
        self._speed_buff_seen_at: dict[str, float] = {}
        self._last_speed_detection_lines: list[str] = []
        self._revolution_vic_dataset: dict[str, dict] | None = None
        self._revolution_vic_dataset_loaded = False
        self._vicious_yolo_net = None
        self._vicious_yolo_loaded = False
        self._last_vicious_yolo_detection: dict[str, object] = {
            "field": "",
            "confidence": 0.0,
            "found": False,
            "box": None,
        }
        self._tesseract_checked = False
        self._tesseract_available = False
        self._tesseract_install_attempted = False
        self._attack_message_ocr_cache: tuple[bool, float] = (False, 0.0)
        self._defeated_message_ocr_cache: tuple[bool, float] = (False, 0.0)
        self._vicious_left_message_ocr_cache: tuple[bool, float] = (False, 0.0)
        self._vicious_left_precheck_log_last = 0.0
        self._last_defeated_banner_crop: Image.Image | None = None
        self._defeated_live_debug_last = 0.0
        self._defeated_live_debug_count = 0

    def roblox_window_rect(self):
        browser_words = ("chrome", "edge", "firefox", "opera", "brave")
        wins = [w for w in gw.getAllWindows() if "roblox" in w.title.lower()]
        app_wins = [w for w in wins if not any(word in w.title.lower() for word in browser_words)]
        exact = [w for w in app_wins if w.title.strip().lower() == "roblox"]
        wins = exact or app_wins or wins
        if not wins:
            return None
        win = wins[0]
        return win.left, win.top, win.width, win.height

    def roblox_client_rect(self) -> tuple[int, int, int, int] | None:
        browser_words = ("chrome", "edge", "firefox", "opera", "brave")
        wins = [w for w in gw.getAllWindows() if "roblox" in w.title.lower()]
        app_wins = [w for w in wins if not any(word in w.title.lower() for word in browser_words)]
        exact = [w for w in app_wins if w.title.strip().lower() == "roblox"]
        wins = exact or app_wins or wins
        if not wins:
            return None
        win = wins[0]
        hwnd = getattr(win, "_hWnd", None) or getattr(win, "hWnd", None)
        if not hwnd:
            return self.roblox_window_rect()
        try:
            rect = wintypes.RECT()
            if not ctypes.windll.user32.GetClientRect(hwnd, ctypes.byref(rect)):
                return self.roblox_window_rect()
            point = wintypes.POINT(0, 0)
            if not ctypes.windll.user32.ClientToScreen(hwnd, ctypes.byref(point)):
                return self.roblox_window_rect()
            width = int(rect.right - rect.left)
            height = int(rect.bottom - rect.top)
            if width <= 0 or height <= 0:
                return self.roblox_window_rect()
            return int(point.x), int(point.y), width, height
        except Exception:
            return self.roblox_window_rect()

    def roblox_shot(self) -> Image.Image:
        # Use the actual Roblox client area. PyGetWindow's outer rectangle can
        # include the title bar and, under DPI scaling, can extend into the
        # Windows taskbar. Keeping captures client-only makes YOLO frames and
        # their labels stable across window placement.
        rect = self.roblox_client_rect()
        if rect is None:
            return self.screen.shot().convert("RGB")
        left, top, width, height = rect
        return self.screen.shot_box(left, top, width, height).convert("RGB")

    def roblox_client_shot(self) -> Image.Image:
        rect = self.roblox_client_rect()
        if rect is None:
            return self.roblox_shot()
        left, top, width, height = rect
        return self.screen.shot_box(left, top, width, height).convert("RGB")

    def roblox_shot_strict(self) -> Image.Image | None:
        rect = self.roblox_window_rect()
        if rect is None:
            return None
        left, top, width, height = rect
        return self.screen.shot_box(left, top, width, height).convert("RGB")

    def scaled_probe_rect(self, img: Image.Image, probe: dict) -> tuple[int, int, int, int]:
        width, height = img.size
        if all(key in probe for key in ("left", "top", "right", "bottom")):
            left = int(width * float(probe.get("left", 0.0)))
            top = int(height * float(probe.get("top", 0.0)))
            right = int(width * float(probe.get("right", 1.0)))
            bottom = int(height * float(probe.get("bottom", 1.0)))
        else:
            base_w = float(probe.get("base_width", self.cfg.get("screen_calibration.base_width", 2560)))
            base_h = float(probe.get("base_height", self.cfg.get("screen_calibration.base_height", 1440)))
            if base_w <= 0 or base_h <= 0:
                base_w, base_h = 2560.0, 1440.0
            scale_x = width / base_w
            scale_y = height / base_h
            left = int(round(float(probe.get("x", 20)) * scale_x))
            top = int(round(float(probe.get("y", 70)) * scale_y))
            right = left + int(round(float(probe.get("width", 90)) * scale_x))
            bottom = top + int(round(float(probe.get("height", 28)) * scale_y))
        left = max(0, min(width - 1, left))
        top = max(0, min(height - 1, top))
        right = max(left + 1, min(width, right))
        bottom = max(top + 1, min(height, bottom))
        return left, top, right, bottom

    def is_night(self) -> bool:
        img = self.roblox_client_shot()
        probe = self.cfg.get("night_probe", {})
        x1, y1, x2, y2 = self.scaled_probe_rect(img, probe)
        threshold = float(probe.get("max_average_rgb", 58))
        crop = img.crop((x1, y1, x2, y2))
        avg = sum(ImageStat.Stat(crop).mean[:3]) / 3
        print(
            f"night avg rgb={avg:.1f} threshold={threshold} "
            f"capture={img.size[0]}x{img.size[1]} roi=({x1},{y1},{x2},{y2})",
            flush=True,
        )
        return avg <= threshold

    def battle_active(self) -> bool:
        img = self.screen.shot()
        width, height = img.size
        pix = img.load()
        scan = self.cfg.get("battle_scan", {})
        right_offset = int(scan.get("right_offset", 186))
        scan_width = int(scan.get("scan_width", 150))
        scan_height = int(scan.get("scan_height", 100))
        min_red = int(scan.get("min_red_pixels", 180))

        def scan_line(x: int, required=None):
            run = 0
            box_color = None
            box_y = -1
            for y in range(height - 1, max(height - scan_height, 0), -1):
                r, g, b = pix[x, y]
                if box_color and (r == box_color[0] or g == box_color[1] or b == box_color[2]):
                    run += 1
                elif required is None and r <= 14 and g <= 14 and b <= 14:
                    run = 1
                    box_y = y
                    box_color = (r, g, b)
                elif required is not None and (r, g, b) == required:
                    run = 1
                    box_y = y
                    box_color = required
                else:
                    run = 0
                    box_color = None
                if run >= 20:
                    return box_y, box_color
            return -1, None

        center = width - right_offset
        for i in range(1, scan_width):
            direction = -1 if i % 2 else 1
            x = max(1, min(width - 2, center - math.floor(i / 2) * direction))
            y, color = scan_line(x)
            if y == -1 or color is None:
                continue
            left, _ = scan_line(x - 1, color)
            right, _ = scan_line(x + 1, color)
            if left == -1 or right == -1:
                continue
            red_pixels = 0
            for bx in range(max(0, center - 125), min(width, center + 125)):
                for by in range(max(0, y - 20), y + 1):
                    r, g, b = pix[bx, by]
                    if r > 200 and g < 40 and b < 40:
                        red_pixels += 1
            print(f"battle red pixels={red_pixels}", flush=True)
            return red_pixels >= min_red
        return False

    def best_template_score(
        self,
        names: Iterable[str],
        scales: Iterable[float] | None = None,
        masked: bool = True,
    ) -> tuple[str | None, float]:
        name, score, _x, _y = self.best_template_match(names, scales=scales, masked=masked)
        return name, score

    def best_template_match(
        self,
        names: Iterable[str],
        scales: Iterable[float] | None = None,
        masked: bool = True,
        bounds: tuple[int, int, int, int] | None = None,
        source: str = "screen",
        color: bool = False,
    ) -> tuple[str | None, float, int, int]:
        if cv2 is None or np is None:
            return None, 0.0, 0, 0
        if source == "roblox":
            shot = self.roblox_shot_strict()
            if shot is None:
                return None, 0.0, 0, 0
            img = np.array(shot)
        else:
            img = np.array(self.screen.shot())
        offset_x = 0
        offset_y = 0
        if bounds is not None:
            x1, y1, x2, y2 = bounds
            if x2 == 0:
                x2 = img.shape[1]
            if y2 == 0:
                y2 = img.shape[0]
            x1, y1 = max(0, x1), max(0, y1)
            x2, y2 = min(img.shape[1], x2), min(img.shape[0], y2)
            img = img[y1:y2, x1:x2]
            offset_x, offset_y = x1, y1
        haystack = img if color else cv2.cvtColor(img, cv2.COLOR_RGB2GRAY)
        best_name = None
        best_score = 0.0
        best_x = 0
        best_y = 0
        scale_values = [float(s) for s in (scales or [1.0])]
        for name in names:
            path = self.template_dir / name
            if not path.exists():
                continue
            try:
                template_rgba = Image.open(path).convert("RGBA")
            except Exception:
                continue
            for scale in scale_values:
                width = max(1, round(template_rgba.width * scale))
                height = max(1, round(template_rgba.height * scale))
                if width > haystack.shape[1] or height > haystack.shape[0]:
                    continue
                resample = Image.Resampling.LANCZOS if scale != 1.0 else Image.Resampling.NEAREST
                scaled = template_rgba.resize((width, height), resample)
                arr = np.array(scaled)
                template = arr[:, :, :3] if color else cv2.cvtColor(arr[:, :, :3], cv2.COLOR_RGB2GRAY)
                alpha = arr[:, :, 3]
                use_mask = masked and int(np.count_nonzero(alpha)) < alpha.size
                if use_mask:
                    mask = (alpha > 0).astype(np.uint8) * 255
                    result = cv2.matchTemplate(haystack, template, cv2.TM_CCORR_NORMED, mask=mask)
                else:
                    result = cv2.matchTemplate(haystack, template, cv2.TM_CCOEFF_NORMED)
                result = np.nan_to_num(result, nan=0.0, posinf=0.0, neginf=0.0)
                _, max_val, _, max_loc = cv2.minMaxLoc(result)
                if max_val > best_score:
                    best_name = f"{name}@{scale:.2f}"
                    best_score = float(max_val)
                    best_x = offset_x + int(max_loc[0])
                    best_y = offset_y + int(max_loc[1])
        return best_name, best_score, best_x, best_y

    def best_template_match_in_image(
        self,
        image: Image.Image,
        names: Iterable[str],
        scales: Iterable[float] | None = None,
        masked: bool = True,
        color: bool = False,
    ) -> tuple[str | None, float, tuple[int, int, int, int] | None]:
        if cv2 is None or np is None:
            return None, 0.0, None
        img = np.array(image.convert("RGB"))
        haystack = img if color else cv2.cvtColor(img, cv2.COLOR_RGB2GRAY)
        best_name = None
        best_score = 0.0
        best_rect: tuple[int, int, int, int] | None = None
        scale_values = [float(s) for s in (scales or [1.0])]
        for name in names:
            path = self.template_dir / name
            if not path.exists():
                continue
            try:
                template_rgba = Image.open(path).convert("RGBA")
            except Exception:
                continue
            for scale in scale_values:
                width = max(1, round(template_rgba.width * scale))
                height = max(1, round(template_rgba.height * scale))
                if width > haystack.shape[1] or height > haystack.shape[0]:
                    continue
                resample = Image.Resampling.LANCZOS if scale != 1.0 else Image.Resampling.NEAREST
                scaled = template_rgba.resize((width, height), resample)
                arr = np.array(scaled)
                template = arr[:, :, :3] if color else cv2.cvtColor(arr[:, :, :3], cv2.COLOR_RGB2GRAY)
                alpha = arr[:, :, 3]
                use_mask = masked and int(np.count_nonzero(alpha)) < alpha.size
                if use_mask:
                    mask = (alpha > 0).astype(np.uint8) * 255
                    result = cv2.matchTemplate(haystack, template, cv2.TM_CCORR_NORMED, mask=mask)
                else:
                    result = cv2.matchTemplate(haystack, template, cv2.TM_CCOEFF_NORMED)
                result = np.nan_to_num(result, nan=0.0, posinf=0.0, neginf=0.0)
                _, max_val, _, max_loc = cv2.minMaxLoc(result)
                if max_val > best_score:
                    best_name = f"{name}@{scale:.2f}"
                    best_score = float(max_val)
                    best_rect = (
                        int(max_loc[0]),
                        int(max_loc[1]),
                        int(max_loc[0]) + width,
                        int(max_loc[1]) + height,
                    )
        return best_name, best_score, best_rect

    def speed_buff_roi_image(self, cfg: dict | None = None) -> Image.Image | None:
        cfg = cfg or (self.cfg.get("speed_buffs", {}) or {})
        try:
            source_name = str(cfg.get("source", "roblox"))
            if source_name == "roblox":
                image = self.roblox_shot_strict()
                if image is None:
                    return None
            else:
                image = self.screen.shot()
            bounds = cfg.get("bounds")
            if isinstance(bounds, list) and len(bounds) == 4:
                x1, y1, x2, y2 = [int(value) for value in bounds]
                width, height = image.size
                if x2 == 0:
                    x2 = width
                if y2 == 0:
                    y2 = height
                x1, y1 = max(0, x1), max(0, y1)
                x2, y2 = min(width, x2), min(height, y2)
                if x2 > x1 and y2 > y1:
                    image = image.crop((x1, y1, x2, y2))
            return image
        except Exception:
            return None

    def save_speed_buff_debug_crop(self, label: str = "speed", image: Image.Image | None = None) -> Path | None:
        cfg = self.cfg.get("speed_buffs", {}) or {}
        if image is None:
            image = self.speed_buff_roi_image(cfg)
        if image is None:
            return None
        folder = Path(str(cfg.get("debug_crop_folder", "debug_speed_buffs") or "debug_speed_buffs"))
        if not folder.is_absolute():
            folder = self.cfg.base_dir / folder
        try:
            folder.mkdir(parents=True, exist_ok=True)
            stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")[:-3]
            path = folder / f"{stamp}_{label}_roi.png"
            image.save(path)
            if bool(cfg.get("debug_artifacts", True)):
                self.save_speed_buff_debug_artifacts(image, folder, f"{stamp}_{label}")
            return path
        except Exception as exc:
            print(f"Could not save speed buff debug crop: {exc}", flush=True)
            return None

    def top_speed_corner_matches(self, crop: np.ndarray | None, limit: int = 5) -> list[tuple[int, str, float]]:
        if cv2 is None or np is None or crop is None:
            return []
        matches: list[tuple[int, str, float]] = []
        for value, name, template in self.load_speed_corner_templates():
            if template.size == 0:
                continue
            try:
                score = float(cv2.matchTemplate(crop, template, cv2.TM_CCOEFF_NORMED)[0, 0])
            except Exception:
                score = 0.0
            if not math.isfinite(score):
                score = 0.0
            matches.append((value, name, score))
        matches.sort(key=lambda item: item[2], reverse=True)
        return matches[: max(1, int(limit))]

    def load_speed_green_stack_templates(self) -> list[tuple[int, str, np.ndarray]]:
        if self._speed_green_stack_template_cache is not None:
            return self._speed_green_stack_template_cache
        templates: list[tuple[int, str, np.ndarray]] = []
        cfg = self.cfg.get("speed_buffs", {}) or {}
        folder = Path(str(cfg.get("green_stack_template_folder", "speed_green_stack_masks") or "speed_green_stack_masks"))
        if not folder.is_absolute():
            folder = self.template_dir / folder
        if folder.exists():
            for path in sorted(folder.glob("haste_x*.png")):
                match = re.search(r"haste_x(\d+)", path.stem)
                if not match:
                    continue
                try:
                    value = int(match.group(1))
                    image = Image.open(path).convert("L").resize((86, 34), Image.Resampling.NEAREST)
                    templates.append((value, path.name, np.array(image)))
                except Exception:
                    continue
        self._speed_green_stack_template_cache = templates
        return templates

    def top_speed_green_stack_matches(self, mask: np.ndarray | None, limit: int = 5) -> list[tuple[int, str, float]]:
        if cv2 is None or np is None or mask is None:
            return []
        matches: list[tuple[int, str, float]] = []
        for value, name, template in self.load_speed_green_stack_templates():
            if template.size == 0:
                continue
            try:
                resized = cv2.resize(mask, (template.shape[1], template.shape[0]), interpolation=cv2.INTER_NEAREST)
                score = float(cv2.matchTemplate(resized, template, cv2.TM_CCOEFF_NORMED)[0, 0])
            except Exception:
                score = 0.0
            if not math.isfinite(score):
                score = 0.0
            matches.append((value, name, score))
        matches.sort(key=lambda item: item[2], reverse=True)
        return matches[: max(1, int(limit))]

    def find_green_speed_icon_boxes(self, image: Image.Image) -> list[tuple[int, int, int, int, float]]:
        if cv2 is None or np is None:
            return []
        cfg = self.cfg.get("speed_buffs", {}) or {}
        rgb = np.array(image.convert("RGB"))
        height, width = rgb.shape[:2]
        search_w = min(width, int(cfg.get("haste_search_width", 520)))
        search_h = min(height, int(cfg.get("haste_search_height", 155)))
        if search_w <= 0 or search_h <= 0:
            return []
        roi = rgb[:search_h, :search_w]
        hsv = cv2.cvtColor(roi, cv2.COLOR_RGB2HSV)
        lower = np.array(cfg.get("green_speed_hsv_lower", [42, 55, 55]), dtype=np.uint8)
        upper = np.array(cfg.get("green_speed_hsv_upper", [92, 255, 255]), dtype=np.uint8)
        mask = cv2.inRange(hsv, lower, upper)
        mask = cv2.morphologyEx(mask, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))
        count, _labels, stats, _centroids = cv2.connectedComponentsWithStats(mask)
        boxes: list[tuple[float, int, int, int, int, int]] = []
        min_area = int(cfg.get("green_speed_min_area", 140))
        min_size = int(cfg.get("green_speed_min_size", 14))
        max_size = int(cfg.get("green_speed_max_size", 64))
        min_y = int(cfg.get("green_speed_min_y", 45))
        max_y = int(cfg.get("green_speed_max_y", 115))
        for index in range(1, count):
            x, y, w, h, area = [int(value) for value in stats[index]]
            if area < min_area or w < min_size or h < min_size or w > max_size or h > max_size:
                continue
            if y < min_y or y > max_y:
                continue
            score = float(area - abs(w - h) * 6)
            boxes.append((score, x, y, w, h, area))
        boxes.sort(reverse=True)
        limit = max(1, int(cfg.get("green_speed_candidate_limit", 14)))
        return [(x, y, w, h, score) for score, x, y, w, h, _area in boxes[:limit]]

    def speed_candidate_corner_image(
        self,
        image: Image.Image,
        box: tuple[int, int, int, int, float],
        kind: str,
    ) -> tuple[np.ndarray | None, tuple[int, int, int, int]]:
        x, y, w, h, _score = box
        if kind == "green":
            left = max(0, x - 7)
            top = max(0, y + max(4, h - 23))
            right = min(image.width, x + w + 28)
            bottom = min(image.height, y + h + 15)
        else:
            left = max(0, x + 39)
            top = max(0, y + 24)
            right = min(image.width, x + 82)
            bottom = min(image.height, y + 55)
        rect = (left, top, right, bottom)
        if right <= left or bottom <= top:
            return None, rect
        crop = image.crop(rect).convert("L").resize((43, 31))
        return np.array(crop), rect

    def speed_text_mask_image(self, image: Image.Image, rect: tuple[int, int, int, int]) -> Image.Image | None:
        if np is None:
            return None
        left, top, right, bottom = rect
        if right <= left or bottom <= top:
            return None
        crop = image.crop(rect).convert("RGB").resize((86, 62), Image.Resampling.NEAREST)
        arr = np.array(crop)
        spread = arr.max(axis=2) - arr.min(axis=2)
        mask = (
            (arr[:, :, 0] > 145)
            & (arr[:, :, 1] > 145)
            & (arr[:, :, 2] > 145)
            & (spread < 85)
        ).astype(np.uint8) * 255
        return Image.fromarray(mask, mode="L")

    def speed_text_mask_array(self, image: Image.Image, rect: tuple[int, int, int, int]) -> np.ndarray | None:
        mask = self.speed_text_mask_image(image, rect)
        if mask is None or np is None:
            return None
        top_height = max(1, min(mask.height, int((self.cfg.get("speed_buffs", {}) or {}).get("green_stack_mask_height", 34))))
        mask = mask.crop((0, 0, mask.width, top_height)).resize((86, 34), Image.Resampling.NEAREST)
        return np.array(mask)

    def first_green_speed_stack_box(
        self,
        image: Image.Image,
    ) -> tuple[tuple[int, int, int, int, float] | None, str]:
        cfg = self.cfg.get("speed_buffs", {}) or {}
        pink_boxes = self.find_haste_icon_boxes(image)
        if not pink_boxes:
            return None, "speed anchor not found"
        green_boxes = self.find_green_speed_icon_boxes(image)
        if not green_boxes:
            return None, f"speed anchor found at {pink_boxes[0][0]},{pink_boxes[0][1]}, no stack boxes"

        max_dx = int(cfg.get("green_stack_max_dx", 145))
        max_center_dy = int(cfg.get("green_stack_max_center_dy", 38))
        best: tuple[float, tuple[int, int, int, int, float], tuple[int, int, int, int, float]] | None = None
        for pink in sorted(pink_boxes, key=lambda item: (item[0], item[1])):
            px, py, pw, ph, _pscore = pink
            p_cy = py + ph / 2.0
            anchor_x = px + max(8, pw // 2)
            for green in green_boxes:
                gx, gy, gw, gh, gscore = green
                g_cy = gy + gh / 2.0
                dx = gx - anchor_x
                dy = abs(g_cy - p_cy)
                if dx < -6 or dx > max_dx or dy > max_center_dy:
                    continue
                rank = dx + dy * 1.4 - min(gscore, 1200.0) / 250.0
                if best is None or rank < best[0]:
                    best = (rank, green, pink)
        if best is None:
            return None, f"anchors={len(pink_boxes)} stack_candidates={len(green_boxes)} but no stack near anchor"
        _rank, green, pink = best
        return green, f"anchor@{pink[0]},{pink[1]} stack@{green[0]},{green[1]}"

    def save_speed_buff_debug_artifacts(self, image: Image.Image, folder: Path, stem: str) -> None:
        if cv2 is None or np is None:
            return
        cfg = self.cfg.get("speed_buffs", {}) or {}
        lines: list[str] = []
        annotated = image.convert("RGB").copy()
        draw = ImageDraw.Draw(annotated)
        font = ImageFont.load_default()

        def draw_box(rect: tuple[int, int, int, int], color: str, label: str) -> None:
            draw.rectangle(rect, outline=color, width=2)
            text_y = max(0, rect[1] - 12)
            draw.text((rect[0], text_y), label, fill=color, font=font)

        def annotate_extra_buff_templates() -> None:
            if bool(cfg.get("only_natro_haste", False)):
                return
            for buff in cfg.get("buffs", []) or []:
                if not isinstance(buff, dict):
                    continue
                if not bool(buff.get("enabled", True)):
                    continue
                label = str(buff.get("name", "speed_buff"))
                if label == "bear_morph":
                    templates = buff.get("templates", []) or []
                    if isinstance(templates, str):
                        templates = [templates]
                    threshold = float(buff.get("threshold", cfg.get("threshold", 0.84)))
                    name, score, rect = self.best_template_match_in_image(
                        image,
                        templates,
                        scales=buff.get("scales", cfg.get("scales", [1.0])),
                        masked=bool(buff.get("masked", True)),
                        color=bool(buff.get("color", cfg.get("color", False))),
                    )
                    lines.append(
                        f"{label} selected: score={score:.3f} threshold={threshold:.3f} "
                        f"best={name} box={rect}"
                    )
                    if rect is not None and score >= threshold:
                        draw_box(rect, "magenta", f"bear {score:.2f}")

        icon_candidates = self.natro_haste_line_candidates(image)
        if icon_candidates:
            x, y, w, h, score, detail = icon_candidates[0]
            icon_rect = (x, y, min(image.width, x + min(w, 38)), min(image.height, y + min(h, 34)))
            draw_box(icon_rect, "cyan", f"speed icon {score:.2f}")
            lines.append(f"speed-icon selected: box={icon_rect} score={score:.3f} detail={detail}")
            try:
                image.crop(icon_rect).save(folder / f"{stem}_speed_icon_crop.png")
            except Exception:
                pass
        else:
            lines.append("speed-icon selected: none")

        if bool(cfg.get("debug_speed_icon_only", True)):
            stack, stack_score, stack_detail = self.natro_haste_stack_from_image(image)
            lines.append(f"speed-stack selected: stack={stack} score={stack_score:.3f} detail={stack_detail}")
            match = re.search(r"digit_crop=(\d+),(\d+),(\d+),(\d+)", stack_detail)
            if match:
                x1, y1, x2, y2 = [int(value) for value in match.groups()]
                stack_rect = (x1, y1, x2, y2)
                draw_box(stack_rect, "yellow", f"x{stack} {stack_score:.2f}")
                try:
                    image.crop(stack_rect).save(folder / f"{stem}_speed_stack_crop.png")
                except Exception:
                    pass
            annotate_extra_buff_templates()
            try:
                strip_h = min(image.height, int(cfg.get("haste_search_height", 155)))
                strip_w = min(image.width, int(cfg.get("haste_search_width", 520)))
                if strip_w > 0 and strip_h > 0:
                    image.crop((0, 0, strip_w, strip_h)).save(folder / f"{stem}_buff_strip.png")
                annotated.save(folder / f"{stem}_annotated.png")
                (folder / f"{stem}_candidates.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
            except Exception as exc:
                print(f"Could not save speed buff debug artifacts: {exc}", flush=True)
            return

        stack, stack_score, stack_detail = self.natro_haste_stack_from_image(image)
        lines.append(f"selected-speed: stack={stack} score={stack_score:.3f} detail={stack_detail}")
        match = re.search(r"@(\d+),(\d+) size=(\d+)x(\d+)", stack_detail)
        if match:
            x, y, w, h = [int(value) for value in match.groups()]
            draw_box((x, y, x + w, y + h), "cyan", f"speed x{stack} {stack_score:.2f}")

        if bool(cfg.get("debug_all_speed_candidates", False)):
            selected = self.find_speed_haste_box(image)
            if selected is None:
                lines.append("selected-old-speed-box: none")
            else:
                x, y, w, h, score = selected
                draw_box((x, y, x + w, y + h), "cyan", f"old selected {score:.0f}")
                crop, rect = self.speed_candidate_corner_image(image, selected, "old")
                draw_box(rect, "cyan", "old number crop")
                matches = self.top_speed_corner_matches(crop)
                lines.append(
                    "selected-old-speed-box: "
                    f"box=({x},{y},{w},{h}) score={score:.1f} "
                    f"top={[(value, name, round(match_score, 3)) for value, name, match_score in matches]}"
                )
                if bool(cfg.get("debug_candidate_crops", True)) and crop is not None:
                    Image.fromarray(crop).save(folder / f"{stem}_old_selected_corner.png")
                mask = self.speed_text_mask_image(image, rect)
                if bool(cfg.get("debug_candidate_crops", True)) and mask is not None:
                    mask.save(folder / f"{stem}_old_selected_text_mask.png")

            for index, box in enumerate(self.find_haste_icon_boxes(image), start=1):
                x, y, w, h, score = box
                draw_box((x, y, x + w, y + h), "magenta", f"legacy#{index}")
                crop, rect = self.speed_candidate_corner_image(image, box, "old")
                draw_box(rect, "magenta", f"legacy#{index} crop")
                matches = self.top_speed_corner_matches(crop)
                lines.append(
                    f"legacy#{index}: box=({x},{y},{w},{h}) score={score:.1f} "
                    f"crop={rect} top={[(value, name, round(match_score, 3)) for value, name, match_score in matches]}"
                )
                if bool(cfg.get("debug_candidate_crops", True)) and crop is not None:
                    Image.fromarray(crop).save(folder / f"{stem}_legacy_{index:02d}_corner.png")
                mask = self.speed_text_mask_image(image, rect)
                if bool(cfg.get("debug_candidate_crops", True)) and mask is not None:
                    mask.save(folder / f"{stem}_legacy_{index:02d}_text_mask.png")

            for index, box in enumerate(self.find_green_speed_icon_boxes(image), start=1):
                x, y, w, h, score = box
                draw_box((x, y, x + w, y + h), "lime", f"green#{index}")
                crop, rect = self.speed_candidate_corner_image(image, box, "green")
                draw_box(rect, "yellow", f"green#{index} crop")
                matches = self.top_speed_corner_matches(crop)
                mask = self.speed_text_mask_array(image, rect)
                mask_matches = self.top_speed_green_stack_matches(mask)
                lines.append(
                    f"green#{index}: box=({x},{y},{w},{h}) score={score:.1f} "
                    f"crop={rect} top={[(value, name, round(match_score, 3)) for value, name, match_score in matches]} "
                    f"mask_top={[(value, name, round(match_score, 3)) for value, name, match_score in mask_matches]}"
                )
                if bool(cfg.get("debug_candidate_crops", True)) and crop is not None:
                    Image.fromarray(crop).save(folder / f"{stem}_green_{index:02d}_corner.png")
                mask_image = self.speed_text_mask_image(image, rect)
                if bool(cfg.get("debug_candidate_crops", True)) and mask_image is not None:
                    mask_image.save(folder / f"{stem}_green_{index:02d}_text_mask.png")

        annotate_extra_buff_templates()

        try:
            strip_h = min(image.height, int(cfg.get("haste_search_height", 155)))
            strip_w = min(image.width, int(cfg.get("haste_search_width", 520)))
            if strip_w > 0 and strip_h > 0:
                image.crop((0, 0, strip_w, strip_h)).save(folder / f"{stem}_buff_strip.png")
            annotated.save(folder / f"{stem}_annotated.png")
            (folder / f"{stem}_candidates.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
        except Exception as exc:
            print(f"Could not save speed buff debug artifacts: {exc}", flush=True)

    def load_speed_stack_templates(self) -> list[tuple[int, str, np.ndarray]]:
        if self._speed_stack_template_cache is not None:
            return self._speed_stack_template_cache
        templates: list[tuple[int, str, np.ndarray]] = []
        cfg = self.cfg.get("speed_buffs", {}) or {}
        folder = Path(str(cfg.get("stack_template_folder", "speed_stacks") or "speed_stacks"))
        if not folder.is_absolute():
            folder = self.template_dir / folder
        if folder.exists():
            for path in sorted(folder.glob("haste_x*.png")):
                match = re.search(r"haste_x(\d+)", path.stem)
                if not match:
                    continue
                try:
                    value = int(match.group(1))
                    image = Image.open(path).convert("L")
                    templates.append((value, path.name, np.array(image)))
                except Exception:
                    continue
        self._speed_stack_template_cache = templates
        return templates

    def load_speed_corner_templates(self) -> list[tuple[int, str, np.ndarray]]:
        if self._speed_corner_template_cache is not None:
            return self._speed_corner_template_cache
        templates: list[tuple[int, str, np.ndarray]] = []
        cfg = self.cfg.get("speed_buffs", {}) or {}
        folder = Path(str(cfg.get("corner_template_folder", "speed_stack_corner") or "speed_stack_corner"))
        if not folder.is_absolute():
            folder = self.template_dir / folder
        if folder.exists():
            for path in sorted(folder.glob("haste_x*.png")):
                match = re.search(r"haste_x(\d+)", path.stem)
                if not match:
                    continue
                try:
                    value = int(match.group(1))
                    image = Image.open(path).convert("L").resize((43, 31))
                    templates.append((value, path.name, np.array(image)))
                except Exception:
                    continue
        self._speed_corner_template_cache = templates
        return templates

    def load_natro_digit_templates(self) -> dict[int, np.ndarray]:
        if self._natro_digit_template_cache is not None:
            return self._natro_digit_template_cache
        raw = {
            0: "iVBORw0KGgoAAAANSUhEUgAAAAgAAAAKCAAAAACsrEBcAAAAAnRSTlMAAHaTzTgAAAArSURBVHgBY2Rg+MzAwMALxCAaQoDBZyYYmwlMYmXAAFApWPVnBkYIi5cBAJNvCLCTFAy9AAAAAElFTkSuQmCC",
            1: "iVBORw0KGgoAAAANSUhEUgAAAAIAAAAMCAAAAABt1zOIAAAAAnRSTlMAAHaTzTgAAAACYktHRAD/h4/MvwAAABZJREFUeAFjYPjM+JmBgeEzEwMDLgQAWo0C7U3u8hAAAAAASUVORK5CYII=",
            2: "iVBORw0KGgoAAAANSUhEUgAAAAQAAAALCAAAAAB9zHN3AAAAAnRSTlMAAHaTzTgAAABCSURBVHgBATcAyP8BAPMAAADzAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPMAAADzAAAA8wAAAPMAAAAB8wAAAAIAAAAAtc8GqohTl5oAAAAASUVORK5CYII=",
            3: "iVBORw0KGgoAAAANSUhEUgAAAAQAAAAKCAAAAAC2kKDSAAAAAnRSTlMAAHaTzTgAAAA9SURBVHgBATIAzf8BAPMAAAAAAAAAAAAAAAAAAAAAAAAAAADzAAAAAAAAAAAAAAAAAAAAAPMAAAABAPMAAFILA8/B68+8AAAAAElFTkSuQmCC",
            4: "iVBORw0KGgoAAAANSUhEUgAAAAQAAAAGCAAAAADBUmCpAAAAAnRSTlMAAHaTzTgAAAApSURBVHgBAR4A4f8AAAAA8wAAAAAAAAAA8wAAAPMAAALzAAAAAfMAAABBtgTDARckPAAAAABJRU5ErkJggg==",
            5: "iVBORw0KGgoAAAANSUhEUgAAAAQAAAALCAAAAAB9zHN3AAAAAnRSTlMAAHaTzTgAAABCSURBVHgBATcAyP8B8wAAAAIAAAAAAPMAAAACAAAAAAHzAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHzAAAAgmID1KbRt+YAAAAASUVORK5CYII=",
            6: "iVBORw0KGgoAAAANSUhEUgAAAAQAAAAJCAAAAAAwBNJ8AAAAAnRSTlMAAHaTzTgAAAA4SURBVHgBAS0A0v8AAAAA8wAAAPMAAADzAAACAAAAAAEA8wAAAPPzAAAA8wAAAAAA8wAAAQAA8wC5oAiQ09KYngAAAABJRU5ErkJggg==",
            7: "iVBORw0KGgoAAAANSUhEUgAAAAQAAAAMCAAAAABgyUPPAAAAAnRSTlMAAHaTzTgAAABHSURBVHgBATwAw/8B8wAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA8wIAAAAAAgAAAABDdgHu70cIeQAAAABJRU5ErkJggg==",
            8: "iVBORw0KGgoAAAANSUhEUgAAAAQAAAAKCAAAAAC2kKDSAAAAAnRSTlMAAHaTzTgAAAA9SURBVHgBATIAzf8BAADzAAAA8wAAAgAAAAABAPMAAAEAAPMAAADzAAAAAAAAAADzAAAAAADzAAABAADzALv5B59oKTe0AAAAAElFTkSuQmCC",
            9: "iVBORw0KGgoAAAANSUhEUgAAAAQAAAAKCAAAAAC2kKDSAAAAAnRSTlMAAHaTzTgAAAA9SURBVHgBATIAzf8BAADzAAAA8wAAAPMAAAAAAPMAAAEAAPMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA87TcBbXcfy3eAAAAAElFTkSuQmCC",
        }
        templates: dict[int, np.ndarray] = {}
        for value, encoded in raw.items():
            try:
                image = Image.open(io.BytesIO(base64.b64decode(encoded))).convert("RGBA")
                templates[value] = np.array(image)[..., 3] > 0
            except Exception:
                continue
        self._natro_digit_template_cache = templates
        return templates

    def match_natro_haste_digit(self, region: Image.Image) -> tuple[int, float, str]:
        """Read a Haste stack using Natro's sparse 0-9 character masks."""
        if cv2 is None or np is None:
            return 1, 0.0, "Natro digit matching unavailable"
        templates = self.load_natro_digit_templates()
        if not templates:
            return 1, 0.0, "Natro digit templates unavailable"

        cfg = self.cfg.get("speed_buffs", {}) or {}
        color = int(cfg.get("natro_digit_color", 243))
        tolerance = max(0, int(cfg.get("natro_digit_color_tolerance", 0)))
        threshold = float(cfg.get("natro_digit_match_threshold", 0.999))
        min_x = max(0, int(cfg.get("natro_digit_min_x", 20)))
        max_x = max(min_x, int(cfg.get("natro_digit_max_x", 42)))
        rgb = np.array(region.convert("RGB"), dtype=np.int16)
        target = np.all(np.abs(rgb - color) <= tolerance, axis=2).astype("float32")

        best_digit, best_score, best_location = 0, 0.0, (0, 0)
        # Natro checks 9 down to 1. A visible "1" is x10; x1 has no number.
        for digit in range(9, 0, -1):
            template = templates.get(digit)
            if template is None:
                continue
            template_f = template.astype("float32")
            th, tw = template_f.shape
            if target.shape[0] < th or target.shape[1] < tw:
                continue
            result = cv2.matchTemplate(target, template_f, cv2.TM_CCORR)
            search_left = min(min_x, max(0, result.shape[1] - 1))
            search_right = min(max_x + 1, result.shape[1])
            if search_right <= search_left:
                continue
            result_window = result[:, search_left:search_right]
            _min_value, max_value, _min_location, window_location = cv2.minMaxLoc(result_window)
            max_location = (window_location[0] + search_left, window_location[1])
            required_pixels = max(1, int(template.sum()))
            score = min(1.0, float(max_value) / required_pixels)
            if score > best_score:
                best_digit, best_score, best_location = digit, score, max_location
            if score >= threshold:
                stack = 10 if digit == 1 else digit
                return stack, score, f"Natro digit={digit} at {max_location[0]},{max_location[1]}"

        return 1, best_score, (
            f"Natro digit absent best={best_digit} score={best_score:.3f} "
            f"at {best_location[0]},{best_location[1]}"
        )

    def load_speed_runner_stack_masks(self) -> list[tuple[int, str, np.ndarray]]:
        if self._speed_runner_stack_mask_cache is not None:
            return self._speed_runner_stack_mask_cache
        cfg = self.cfg.get("speed_buffs", {}) or {}
        folder_name = str(cfg.get("runner_stack_mask_folder", "speed_runner_stack_masks") or "speed_runner_stack_masks")
        folder = Path(folder_name)
        if not folder.is_absolute():
            folder = self.template_dir / folder
        templates: list[tuple[int, str, np.ndarray]] = []
        if folder.exists():
            for path in sorted(folder.glob("haste_x*.png")):
                match = re.search(r"haste_x(\d+)", path.stem)
                if not match:
                    continue
                try:
                    value = int(match.group(1))
                    image = Image.open(path).convert("L")
                    templates.append((value, path.name, np.array(image) > 0))
                except Exception:
                    continue
        self._speed_runner_stack_mask_cache = templates
        return templates

    def load_speed_runner_digit_masks(self) -> list[tuple[int, str, np.ndarray]]:
        if self._speed_runner_digit_mask_cache is not None:
            return self._speed_runner_digit_mask_cache
        cfg = self.cfg.get("speed_buffs", {}) or {}
        folder_name = str(cfg.get("runner_digit_mask_folder", "speed_runner_digit_masks") or "speed_runner_digit_masks")
        folder = Path(folder_name)
        if not folder.is_absolute():
            folder = self.template_dir / folder
        templates: list[tuple[int, str, np.ndarray]] = []
        if folder.exists():
            for path in sorted(folder.glob("digit_*.png")):
                match = re.search(r"digit_(\d)", path.stem)
                if not match:
                    continue
                try:
                    value = int(match.group(1))
                    image = Image.open(path).convert("L").resize((16, 22), Image.Resampling.NEAREST)
                    mask = np.array(image) > 0
                    if int(mask.sum()) >= 5:
                        templates.append((value, path.name, mask))
                except Exception:
                    continue
        self._speed_runner_digit_mask_cache = templates
        return templates

    def load_speed_runner_icon_masks(self) -> list[tuple[str, np.ndarray]]:
        if self._speed_runner_icon_mask_cache is not None:
            return self._speed_runner_icon_mask_cache
        cfg = self.cfg.get("speed_buffs", {}) or {}
        folder_name = str(cfg.get("runner_icon_mask_folder", "speed_runner_icon_masks") or "speed_runner_icon_masks")
        folder = Path(folder_name)
        if not folder.is_absolute():
            folder = self.template_dir / folder
        templates: list[tuple[str, np.ndarray]] = []
        if folder.exists():
            for path in sorted(folder.glob("runner_*.png")):
                try:
                    image = Image.open(path).convert("L")
                    templates.append((path.name, np.array(image) > 0))
                except Exception:
                    continue
        self._speed_runner_icon_mask_cache = templates
        return templates

    def speed_runner_icon_mask(self, region: Image.Image) -> np.ndarray:
        rgb = np.array(region.convert("RGB"))
        if rgb.size == 0:
            return np.zeros((1, 1), dtype=bool)
        sub = rgb[:min(34, rgb.shape[0]), :min(38, rgb.shape[1])]
        hsv = cv2.cvtColor(sub, cv2.COLOR_RGB2HSV)
        cfg = self.cfg.get("speed_buffs", {}) or {}
        max_s = int(cfg.get("runner_icon_mask_s_max", 80))
        min_v = int(cfg.get("runner_icon_mask_v_min", 105))
        max_v = int(cfg.get("runner_icon_mask_v_max", 245))
        return (hsv[:, :, 1] < max_s) & (hsv[:, :, 2] > min_v) & (hsv[:, :, 2] < max_v)

    def speed_runner_icon_score(self, region: Image.Image) -> tuple[float, str]:
        candidate = self.speed_runner_icon_mask(region)
        templates = self.load_speed_runner_icon_masks()
        if not templates:
            return 1.0, "no runner icon masks"
        best_score = 0.0
        best_name = "none"
        for name, template in templates:
            current = candidate
            if current.shape != template.shape:
                current = cv2.resize(
                    current.astype("uint8"),
                    (template.shape[1], template.shape[0]),
                    interpolation=cv2.INTER_NEAREST,
                ).astype(bool)
            inter = int((current & template).sum())
            union = int((current | template).sum())
            score = (inter / union) if union else 0.0
            if score > best_score:
                best_score = score
                best_name = name
        return best_score, best_name

    def speed_runner_stack_text_mask(self, region: Image.Image) -> np.ndarray:
        rgb = np.array(region.convert("RGB"))
        if rgb.size == 0:
            return np.zeros((1, 1), dtype=bool)
        cfg = self.cfg.get("speed_buffs", {}) or {}
        x1 = int(cfg.get("runner_stack_text_x1", 10))
        y1 = int(cfg.get("runner_stack_text_y1", 12))
        x2 = int(cfg.get("runner_stack_text_x2", 43))
        y2 = int(cfg.get("runner_stack_text_y2", 31))
        x1 = max(0, min(rgb.shape[1], x1))
        x2 = max(x1 + 1, min(rgb.shape[1], x2))
        y1 = max(0, min(rgb.shape[0], y1))
        y2 = max(y1 + 1, min(rgb.shape[0], y2))
        sub = rgb[y1:y2, x1:x2]
        hsv = cv2.cvtColor(sub, cv2.COLOR_RGB2HSV)
        max_s = int(cfg.get("runner_stack_mask_s_max", 180))
        max_v = int(cfg.get("runner_stack_mask_v_max", 120))
        white_s = int(cfg.get("runner_stack_white_s_max", 80))
        white_v = int(cfg.get("runner_stack_white_v_min", 150))
        dark_outline = (hsv[:, :, 1] < max_s) & (hsv[:, :, 2] < max_v)
        white_fill = (hsv[:, :, 1] < white_s) & (hsv[:, :, 2] > white_v)
        return dark_outline | white_fill

    def natro_haste_line_candidates(self, image: Image.Image) -> list[tuple[int, int, int, int, float, str]]:
        if cv2 is None or np is None:
            return []
        cfg = self.cfg.get("speed_buffs", {}) or {}
        rgb = np.array(image.convert("RGB"))
        height, width = rgb.shape[:2]
        search_w = min(width, int(cfg.get("haste_search_width", 760)))
        max_x = min(search_w, int(cfg.get("grey_runner_max_x", 360)))
        if search_w <= 0 or max_x <= 0:
            return []

        line_len = max(6, int(cfg.get("grey_runner_line_length", 10)))
        tolerance = int(cfg.get("grey_runner_line_tolerance", 10))
        min_cluster = max(2, int(cfg.get("grey_runner_min_line_cluster", 3)))
        y_starts = cfg.get("grey_runner_band_y_starts", [55, 60, 65, 70, 75, 80])
        band_h = max(30, int(cfg.get("grey_runner_band_height", 45)))
        min_rel_y = int(cfg.get("grey_runner_min_relative_y", 8))
        max_rel_y = int(cfg.get("grey_runner_max_relative_y", 43))
        candidates: list[tuple[int, int, int, int, float, str]] = []
        debug_lines: list[str] = []

        def has_melody_marker(area: np.ndarray, x: int, y: int) -> bool:
            # Natro skips Melody by checking for the tiny dark melody mark above
            # the white line. This keeps white/grey non-speed buffs out.
            x1 = max(0, x + 2)
            x2 = min(area.shape[1], x + max(16, 2 * y - 24))
            y2 = min(area.shape[0], y + 1)
            if x2 <= x1 or y2 <= 0:
                return False
            sub = area[:y2, x1:x2]
            dark = np.all(np.abs(sub.astype(np.int16) - 36) <= 22, axis=2)
            if dark.shape[0] < 2 or dark.shape[1] < 3:
                return False
            kernel = np.ones((2, 3), dtype=np.uint8)
            hits = cv2.filter2D(dark.astype(np.uint8), -1, kernel, borderType=cv2.BORDER_CONSTANT)
            return bool((hits >= 6).any())

        for y_start_raw in y_starts:
            try:
                y_start = int(y_start_raw)
            except Exception:
                continue
            if y_start < 0 or y_start >= height:
                continue
            area = rgb[y_start:min(height, y_start + band_h), :search_w]
            if area.shape[0] <= min_rel_y:
                continue
            white = np.all(np.abs(area.astype(np.int16) - 240) <= tolerance, axis=2)
            runs: list[tuple[int, int]] = []
            y_stop = min(area.shape[0], max_rel_y + 1)
            for y in range(max(0, min_rel_y), y_stop):
                run = 0
                row = white[y]
                for x in range(0, max_x):
                    if row[x]:
                        run += 1
                        if run == line_len:
                            runs.append((x - line_len + 1, y))
                    else:
                        run = 0
            if not runs:
                continue

            clusters: list[list[tuple[int, int]]] = []
            for x, y in sorted(runs, key=lambda item: (item[0], item[1])):
                if clusters and abs(clusters[-1][-1][0] - x) <= 3:
                    clusters[-1].append((x, y))
                else:
                    clusters.append([(x, y)])
            for cluster in clusters:
                if len(cluster) < min_cluster:
                    continue
                xs = [item[0] for item in cluster]
                ys = [item[1] for item in cluster]
                x = int(round(sum(xs) / len(xs)))
                y = int(round(sum(ys) / len(ys)))
                if has_melody_marker(area, x, y):
                    debug_lines.append(f"skip melody-like line@{x},{y_start + y} n={len(cluster)} band={y_start}")
                    continue
                global_y = y_start + y
                # Runner tile is roughly around this white line. The returned
                # box is only for debug drawing; stack reading uses the line.
                box_x = max(0, x - 6)
                box_y = max(0, global_y - 26)
                box_w = min(width - box_x, 52)
                box_h = min(height - box_y, 56)
                base_detail = f"band={y_start} rel={x},{y} lines={len(cluster)}"
                icon_region = Image.fromarray(rgb[box_y:box_y + box_h, box_x:box_x + box_w])
                icon_score, icon_template = self.speed_runner_icon_score(icon_region)
                icon_threshold = float(cfg.get("runner_icon_mask_threshold", 0.55))
                if icon_score < icon_threshold:
                    debug_lines.append(
                        f"skip non-runner line@{x},{global_y} icon_score={icon_score:.3f} "
                        f"template={icon_template} {base_detail}"
                    )
                    continue
                score = min(0.99, 0.55 + len(cluster) * 0.04)
                detail = f"{base_detail} icon={icon_score:.3f}:{icon_template}"
                candidates.append((box_x, box_y, box_w, box_h, score, detail))
                debug_lines.append(f"candidate line@{x},{global_y} {detail} score={score:.3f}")

        # Reject weak lookalikes before applying Natro's leftmost-Haste rule.
        # Equal-confidence candidates remain ordered from left to right.
        candidates.sort(key=lambda item: (-item[4], item[0], item[1]))
        self._last_haste_line_candidates = debug_lines[:80]
        return candidates

    def first_grey_haste_anchor(self, image: Image.Image) -> tuple[int, int, float] | None:
        candidates = self.natro_haste_line_candidates(image)
        if not candidates:
            return None
        x, y, _w, _h, score, _detail = candidates[0]
        # Convert debug box back to the line anchor used by stack reading.
        return x + 6, y + 26, score

    def read_haste_stack_near_anchor(
        self,
        image: Image.Image,
        anchor: tuple[int, int, float],
    ) -> tuple[int, float, tuple[int, int, int, int] | None, str]:
        if cv2 is None or np is None:
            return 1, 0.0, None, "Natro digit matching unavailable"
        if not bool((self.cfg.get("speed_buffs", {}) or {}).get("runner_stack_detection_enabled", False)):
            return 1, 0.0, None, "runner stack reading disabled"

        cfg = self.cfg.get("speed_buffs", {}) or {}
        x, y, _anchor_score = anchor
        rect = (
            max(0, x + int(cfg.get("grey_runner_stack_left_offset", -2))),
            max(0, y + int(cfg.get("grey_runner_stack_top_offset", -15))),
            min(image.width, x + int(cfg.get("grey_runner_stack_right_offset", 50))),
            min(image.height, y + int(cfg.get("grey_runner_stack_bottom_offset", 20))),
        )
        if rect[2] <= rect[0] or rect[3] <= rect[1]:
            return 1, 0.0, None, "Natro digit area unavailable"

        stack, score, detail = self.match_natro_haste_digit(image.crop(rect))
        return stack, score, rect, detail

    def natro_haste_stack_from_grey_runner(self, image: Image.Image) -> tuple[int, float, str]:
        candidates = self.natro_haste_line_candidates(image)
        if not candidates:
            return 0, 0.0, "grey runner haste icon not found"
        box_x, box_y, box_w, box_h, anchor_score, candidate_detail = candidates[0]
        anchor = box_x + 6, box_y + 26, anchor_score
        stack, digit_score, digit_rect, digit_detail = self.read_haste_stack_near_anchor(image, anchor)
        x, y, anchor_score = anchor
        detail = (
            f"grey-runner@{box_x},{box_y} size={box_w}x{box_h} "
            f"anchor={x},{y} anchor_score={anchor_score:.3f} digit_score={digit_score:.3f} "
            f"{candidate_detail}; {digit_detail}"
        )
        if digit_rect is not None:
            detail += f" digit_crop={digit_rect[0]},{digit_rect[1]},{digit_rect[2]},{digit_rect[3]}"
        return max(1, min(10, stack)), max(anchor_score, digit_score), detail

    def natro_haste_stack_from_animation_fallback(self, image: Image.Image) -> tuple[int, float, str]:
        """Recover an isolated runner animation frame using the last confirmed stack."""
        if cv2 is None or np is None:
            return 0, 0.0, "runner animation fallback unavailable"
        cfg = self.cfg.get("speed_buffs", {}) or {}
        if not bool(cfg.get("grey_runner_animation_fallback_enabled", True)):
            return 0, 0.0, "runner animation fallback disabled"

        previous_stack = int(self._last_natro_haste_stack)
        max_reads = max(1, int(cfg.get("grey_runner_animation_max_fallback_reads", 2)))
        hold_seconds = max(0.0, float(cfg.get("grey_runner_animation_hold_seconds", 10.0)))
        age = time.monotonic() - float(self._last_natro_haste_seen_at)
        if previous_stack <= 1 or age > hold_seconds:
            if age > hold_seconds:
                self._last_natro_haste_stack = 0
                self._natro_haste_animation_fallback_reads = 0
            return 0, 0.0, "no recent numbered Haste stack for animation fallback"
        if self._natro_haste_animation_fallback_reads >= max_reads:
            return 0, 0.0, "runner animation fallback read limit reached"

        slot_x = max(0, int(cfg.get("grey_runner_slot_start_x", 108)))
        slot_step = max(1, int(cfg.get("grey_runner_slot_step_x", 38)))
        slot_y = max(0, int(cfg.get("grey_runner_slot_y", 79)))
        crop_w = max(1, int(cfg.get("grey_runner_slot_width", 52)))
        crop_h = max(1, int(cfg.get("grey_runner_slot_height", 56)))
        max_slot_x = min(
            image.width - crop_w,
            int(cfg.get("grey_runner_max_x", 360)),
        )
        if max_slot_x < slot_x or slot_y + crop_h > image.height:
            return 0, 0.0, "runner animation slots unavailable"

        rgb = np.array(image.convert("RGB"))
        icon_threshold = float(cfg.get("grey_runner_animation_icon_threshold", 0.30))
        min_grey_pixels = max(1, int(cfg.get("grey_runner_animation_min_grey_pixels", 250)))
        best: tuple[float, int, int, str, str] | None = None
        for x in range(slot_x, max_slot_x + 1, slot_step):
            crop_rect = (x, slot_y, x + crop_w, slot_y + crop_h)
            crop = image.crop(crop_rect)
            stack, digit_score, digit_detail = self.match_natro_haste_digit(crop)
            if stack != previous_stack or digit_score < 0.999:
                continue

            icon_h = min(34, crop_h)
            icon_w = min(30, crop_w)
            icon_rgb = rgb[slot_y:slot_y + icon_h, x:x + icon_w]
            if icon_rgb.size == 0:
                continue
            icon_hsv = cv2.cvtColor(icon_rgb, cv2.COLOR_RGB2HSV)
            grey_pixels = int(
                (
                    (icon_hsv[:, :, 1] < int(cfg.get("runner_icon_mask_s_max", 80)))
                    & (icon_hsv[:, :, 2] > int(cfg.get("runner_icon_mask_v_min", 105)))
                    & (icon_hsv[:, :, 2] < int(cfg.get("runner_icon_mask_v_max", 245)))
                ).sum()
            )
            icon_score, icon_template = self.speed_runner_icon_score(crop)
            if icon_score < icon_threshold or grey_pixels < min_grey_pixels:
                continue
            rank = icon_score + min(1.0, grey_pixels / max(1.0, float(min_grey_pixels))) * 0.05
            candidate = (rank, x, grey_pixels, icon_template, digit_detail)
            if best is None or candidate[0] > best[0]:
                best = candidate

        if best is None:
            return 0, 0.0, "runner animation fallback found no matching slot"

        rank, x, grey_pixels, icon_template, digit_detail = best
        self._natro_haste_animation_fallback_reads += 1
        crop_rect = (x, slot_y, x + crop_w, slot_y + crop_h)
        detail = (
            f"grey-runner-animation@{x},{slot_y} previous=x{previous_stack} age={age:.2f}s "
            f"icon={rank - 0.05:.3f}:{icon_template} grey={grey_pixels}; {digit_detail} "
            f"digit_crop={crop_rect[0]},{crop_rect[1]},{crop_rect[2]},{crop_rect[3]}"
        )
        return previous_stack, 1.0, detail

    def natro_haste_stack_from_speed_template(self, image: Image.Image) -> tuple[int, float, str]:
        if cv2 is None or np is None:
            return 0, 0.0, "cv2 unavailable"
        cfg = self.cfg.get("speed_buffs", {}) or {}
        search_w = min(image.width, int(cfg.get("haste_search_width", 420)))
        search_h = min(image.height, int(cfg.get("haste_search_height", 155)))
        if search_w <= 0 or search_h <= 0:
            return 0, 0.0, "empty speed search area"
        haystack = cv2.cvtColor(np.array(image.convert("RGB").crop((0, 0, search_w, search_h))), cv2.COLOR_RGB2GRAY)
        scales = cfg.get("speed_template_scales", cfg.get("scales", [0.8, 0.9, 1.0, 1.1, 1.2, 1.35]))
        best_value = 0
        best_name = "none"
        best_score = 0.0
        best_loc = (0, 0)
        best_size = (0, 0)
        for path in sorted(self.template_dir.glob("speed_haste_x*.png")):
            match = re.search(r"speed_haste_x(\d+)", path.stem)
            if not match:
                continue
            try:
                value = int(match.group(1))
                template_base = Image.open(path).convert("L")
                template_arr = np.array(template_base)
            except Exception:
                continue
            for scale in scales:
                try:
                    scale_f = float(scale)
                except Exception:
                    continue
                tw = max(5, round(template_arr.shape[1] * scale_f))
                th = max(5, round(template_arr.shape[0] * scale_f))
                if tw > haystack.shape[1] or th > haystack.shape[0]:
                    continue
                resized = cv2.resize(template_arr, (tw, th), interpolation=cv2.INTER_AREA)
                result = cv2.matchTemplate(haystack, resized, cv2.TM_CCOEFF_NORMED)
                result = np.nan_to_num(result, nan=0.0, posinf=0.0, neginf=0.0)
                _min_val, max_val, _min_loc, max_loc = cv2.minMaxLoc(result)
                score = float(max_val) if math.isfinite(float(max_val)) else 0.0
                if score > best_score:
                    best_value = value
                    best_name = path.name
                    best_score = score
                    best_loc = (int(max_loc[0]), int(max_loc[1]))
                    best_size = (tw, th)
        threshold = float(cfg.get("speed_template_match_threshold", 0.56))
        if best_score < threshold:
            return 0, best_score, f"speed icon template unclear best={best_name}@{best_loc[0]},{best_loc[1]} size={best_size[0]}x{best_size[1]}"
        return max(1, min(10, best_value)), best_score, f"{best_name} via speed-icon-template@{best_loc[0]},{best_loc[1]} size={best_size[0]}x{best_size[1]}"

    def find_haste_icon_boxes(self, image: Image.Image) -> list[tuple[int, int, int, int, float]]:
        if cv2 is None or np is None:
            return []
        cfg = self.cfg.get("speed_buffs", {}) or {}
        rgb = np.array(image.convert("RGB"))
        height, width = rgb.shape[:2]
        search_w = min(width, int(cfg.get("haste_search_width", 360)))
        search_h = min(height, int(cfg.get("haste_search_height", 155)))
        if search_w <= 0 or search_h <= 0:
            return []
        roi = rgb[:search_h, :search_w]
        hsv = cv2.cvtColor(roi, cv2.COLOR_RGB2HSV)
        lower = np.array(cfg.get("haste_hsv_lower", [125, 25, 80]), dtype=np.uint8)
        upper = np.array(cfg.get("haste_hsv_upper", [178, 255, 255]), dtype=np.uint8)
        mask = cv2.inRange(hsv, lower, upper)
        mask = cv2.morphologyEx(mask, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))
        count, _labels, stats, _centroids = cv2.connectedComponentsWithStats(mask)
        boxes: list[tuple[float, int, int, int, int, int]] = []
        min_area = int(cfg.get("haste_min_area", 220))
        min_size = int(cfg.get("haste_min_size", 18))
        max_size = int(cfg.get("haste_max_size", 72))
        for index in range(1, count):
            x, y, w, h, area = [int(value) for value in stats[index]]
            if area < min_area or w < min_size or h < min_size or w > max_size or h > max_size:
                continue
            score = float(area - abs(w - h) * 8)
            boxes.append((score, x, y, w, h, area))
        boxes.sort(reverse=True)
        limit = max(1, int(cfg.get("haste_candidate_limit", 8)))
        return [(x, y, w, h, score) for score, x, y, w, h, _area in boxes[:limit]]

    def find_haste_icon_box(self, image: Image.Image) -> tuple[int, int, int, int, float] | None:
        boxes = self.find_haste_icon_boxes(image)
        return boxes[0] if boxes else None

    def find_speed_haste_box(self, image: Image.Image) -> tuple[int, int, int, int, float] | None:
        if cv2 is None or np is None:
            return None
        cfg = self.cfg.get("speed_buffs", {}) or {}
        rgb = np.array(image.convert("RGB"))
        height, width = rgb.shape[:2]
        search_w = min(width, int(cfg.get("haste_search_width", 360)))
        search_h = min(height, int(cfg.get("haste_search_height", 155)))
        if search_w <= 0 or search_h <= 0:
            return None
        roi = rgb[:search_h, :search_w]
        hsv = cv2.cvtColor(roi, cv2.COLOR_RGB2HSV)
        lower = np.array(cfg.get("haste_hsv_lower", [125, 25, 80]), dtype=np.uint8)
        upper = np.array(cfg.get("haste_hsv_upper", [178, 255, 255]), dtype=np.uint8)
        mask = cv2.inRange(hsv, lower, upper)
        mask = cv2.morphologyEx(mask, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))
        count, _labels, stats, _centroids = cv2.connectedComponentsWithStats(mask)
        min_area = int(cfg.get("haste_min_area", 220))
        min_size = int(cfg.get("haste_min_size", 18))
        max_size = int(cfg.get("haste_max_size", 72))
        min_x = int(cfg.get("haste_anchor_min_x", 70))
        max_x = int(cfg.get("haste_anchor_max_x", 230))
        min_y = int(cfg.get("haste_anchor_min_y", 60))
        max_y = int(cfg.get("haste_anchor_max_y", 115))
        best: tuple[float, int, int, int, int] | None = None
        for index in range(1, count):
            x, y, w, h, area = [int(value) for value in stats[index]]
            if area < min_area or w < min_size or h < min_size or w > max_size or h > max_size:
                continue
            if x < min_x or x > max_x or y < min_y or y > max_y:
                continue
            right = rgb[max(0, y - 4) : min(height, y + 50), min(width, x + 34) : min(width, x + 82)]
            if right.size == 0:
                continue
            right_hsv = cv2.cvtColor(right, cv2.COLOR_RGB2HSV)
            gray_pixels = int(
                ((right_hsv[:, :, 1] < 70) & (right_hsv[:, :, 2] > 80) & (right_hsv[:, :, 2] < 245)).sum()
            )
            if gray_pixels < int(cfg.get("speed_anchor_gray_min_pixels", 700)):
                continue
            score = float(gray_pixels + area * 0.05 - abs(w - h) * 4)
            if best is None or score > best[0]:
                best = (score, x, y, w, h)
        if best is None:
            return None
        score, x, y, w, h = best
        return x, y, w, h, score

    def speed_stack_corner_image(self, image: Image.Image, box: tuple[int, int, int, int, float]) -> np.ndarray | None:
        x, y, _w, _h, _score = box
        left = max(0, x + 39)
        top = max(0, y + 24)
        right = min(image.width, x + 82)
        bottom = min(image.height, y + 55)
        if right <= left or bottom <= top:
            return None
        crop = image.crop((left, top, right, bottom)).convert("L").resize((43, 31))
        return np.array(crop)

    def natro_haste_stack_from_corner(self, image: Image.Image) -> tuple[int, float, str]:
        if cv2 is None or np is None:
            return 0, 0.0, "cv2 unavailable"
        box = self.find_speed_haste_box(image)
        source = "speed-corner"
        if box is None:
            boxes = self.find_haste_icon_boxes(image)
            if not boxes:
                return 0, 0.0, "speed haste icon not found"
            box = boxes[0]
            source = "legacy-anchor-fallback"
        templates = self.load_speed_corner_templates()
        if not templates:
            return 1, box[4], "speed haste icon found, no corner templates"
        crop, _rect = self.speed_candidate_corner_image(image, box, "old")
        if crop is None:
            return 1, box[4], "speed haste icon found, corner crop failed"
        best_value = 1
        best_name = "default_x1"
        best_score = 0.0
        for value, name, template in templates:
            if template.size == 0:
                continue
            score = float(cv2.matchTemplate(crop, template, cv2.TM_CCOEFF_NORMED)[0, 0])
            if not math.isfinite(score):
                score = 0.0
            if score > best_score:
                best_value = value
                best_name = name
                best_score = score
        threshold = float((self.cfg.get("speed_buffs", {}) or {}).get("corner_match_threshold", 0.90))
        if best_score < threshold:
            return 1, best_score, f"speed haste icon found, no reliable stack best={best_name} via {source}"
        return max(1, min(10, best_value)), best_score, f"{best_name} via {source}@{box[0]},{box[1]}"

    def natro_haste_stack_from_green_badge(self, image: Image.Image) -> tuple[int, float, str]:
        if cv2 is None or np is None:
            return 0, 0.0, "cv2 unavailable"
        cfg = self.cfg.get("speed_buffs", {}) or {}
        templates = self.load_speed_green_stack_templates()
        if not templates:
            return 0, 0.0, "no green stack templates"
        pink_boxes = self.find_haste_icon_boxes(image)
        if not pink_boxes:
            return 0, 0.0, "speed anchor not found"
        green_boxes = self.find_green_speed_icon_boxes(image)
        if not green_boxes:
            return 0, 0.0, f"speed anchor found at {pink_boxes[0][0]},{pink_boxes[0][1]}, no stack boxes"

        max_dx = int(cfg.get("green_stack_max_dx", 145))
        max_center_dy = int(cfg.get("green_stack_max_center_dy", 38))
        candidate_results: list[tuple[int, str, float, float, tuple[int, int, int, int, float], tuple[int, int, int, int, float], list[tuple[int, str, float]]]] = []
        for pink in pink_boxes:
            px, py, pw, ph, _pscore = pink
            p_cy = py + ph / 2.0
            anchor_x = px + max(8, pw // 2)
            for green in green_boxes:
                gx, gy, gw, gh, _gscore = green
                g_cy = gy + gh / 2.0
                dx = gx - anchor_x
                dy = abs(g_cy - p_cy)
                if dx < -8 or dx > max_dx or dy > max_center_dy:
                    continue
                _crop, rect = self.speed_candidate_corner_image(image, green, "green")
                mask = self.speed_text_mask_array(image, rect)
                matches = self.top_speed_green_stack_matches(mask, limit=4)
                if not matches:
                    continue
                best_value, best_name, best_score = matches[0]
                # Prefer a clear text match. Distance only breaks near ties, so
                # noisy green fragments do not beat the actual xN badge.
                rank = best_score - (abs(dx) * 0.0005) - (dy * 0.001)
                candidate_results.append((best_value, best_name, best_score, rank, green, pink, matches))

        if not candidate_results:
            return 0, 0.0, f"anchors={len(pink_boxes)} stack_candidates={len(green_boxes)} but no readable stack candidates"
        candidate_results.sort(key=lambda item: item[3], reverse=True)
        best_value, best_name, best_score, _rank, best_green, best_pink, matches = candidate_results[0]
        second_score = matches[1][2] if len(matches) > 1 else -1.0
        threshold = float(cfg.get("green_stack_match_threshold", 0.55))
        margin = float(cfg.get("green_stack_match_margin", 0.08))
        source = f"anchor@{best_pink[0]},{best_pink[1]} stack@{best_green[0]},{best_green[1]}"
        if best_score < threshold:
            return 0, best_score, f"{source}, green stack unclear best={best_name}"
        if second_score >= 0.0 and (best_score - second_score) < margin:
            return 0, best_score, f"{source}, green stack ambiguous best={best_name} second={matches[1][1]}"
        return max(1, min(10, int(best_value))), best_score, f"{best_name} via green-stack {source}"

    def speed_stack_mask(self, image: Image.Image, box: tuple[int, int, int, int, float]) -> np.ndarray | None:
        if cv2 is None or np is None:
            return None
        cfg = self.cfg.get("speed_buffs", {}) or {}
        x, y, w, h, _score = box
        left = x + int(cfg.get("stack_crop_left_offset", 20))
        top = y + int(cfg.get("stack_crop_top_offset", 22))
        right = x + w + int(cfg.get("stack_crop_right_pad", 82))
        bottom = y + h + int(cfg.get("stack_crop_bottom_pad", 15))
        left, top = max(0, left), max(0, top)
        right, bottom = min(image.width, right), min(image.height, bottom)
        if right <= left or bottom <= top:
            return None
        crop = image.crop((left, top, right, bottom)).convert("RGB")
        hsv = cv2.cvtColor(np.array(crop), cv2.COLOR_RGB2HSV)
        lower = np.array(cfg.get("stack_text_hsv_lower", [0, 0, 125]), dtype=np.uint8)
        upper = np.array(cfg.get("stack_text_hsv_upper", [179, 145, 255]), dtype=np.uint8)
        return cv2.inRange(hsv, lower, upper)

    def natro_haste_stack_from_image(self, image: Image.Image) -> tuple[int, float, str]:
        if cv2 is None or np is None:
            return 0, 0.0, "cv2 unavailable"
        cfg = self.cfg.get("speed_buffs", {}) or {}
        if bool(cfg.get("grey_runner_detection_enabled", True)):
            stack, score, detail = self.natro_haste_stack_from_grey_runner(image)
            if stack > 0:
                self._last_natro_haste_stack = stack
                self._last_natro_haste_seen_at = time.monotonic()
                self._natro_haste_animation_fallback_reads = 0
                return stack, score, detail
            fallback_stack, fallback_score, fallback_detail = self.natro_haste_stack_from_animation_fallback(image)
            if fallback_stack > 0:
                return fallback_stack, fallback_score, fallback_detail
            if bool(cfg.get("speed_template_only", True)):
                return stack, score, detail
        if bool(cfg.get("speed_template_detection_enabled", True)):
            stack, score, detail = self.natro_haste_stack_from_speed_template(image)
            if stack > 0:
                return stack, score, detail
        green_detail = ""
        if bool(cfg.get("green_stack_detection_enabled", True)):
            stack, score, detail = self.natro_haste_stack_from_green_badge(image)
            if stack > 0:
                return stack, score, detail
            green_detail = detail
        if bool(cfg.get("corner_detection_enabled", True)):
            stack, score, detail = self.natro_haste_stack_from_corner(image)
            if stack > 0 or "not found" in detail:
                if green_detail and stack > 0:
                    detail = f"{detail}; green={green_detail}"
                return stack, score, detail
        templates = self.load_speed_stack_templates()
        if not templates:
            return 0, 0.0, "no stack templates"

        best_value = 0
        best_name = "none"
        best_score = 0.0
        best_source = "anchor"
        boxes = self.find_haste_icon_boxes(image)
        for box_index, box in enumerate(boxes, start=1):
            mask = self.speed_stack_mask(image, box)
            if mask is None:
                continue
            for value, name, template in templates:
                if template.size == 0:
                    continue
                resized = cv2.resize(mask, (template.shape[1], template.shape[0]), interpolation=cv2.INTER_NEAREST)
                score = float(cv2.matchTemplate(resized, template, cv2.TM_CCOEFF_NORMED)[0, 0])
                if not math.isfinite(score):
                    score = 0.0
                if score > best_score:
                    best_value = value
                    best_name = name
                    best_score = score
                    best_source = f"anchor{box_index}@{box[0]},{box[1]}"

        cfg = self.cfg.get("speed_buffs", {}) or {}
        if bool(cfg.get("stack_global_search", True)):
            search_w = min(image.width, int(cfg.get("haste_search_width", 360)))
            search_h = min(image.height, int(cfg.get("haste_search_height", 155)))
            if search_w > 0 and search_h > 0:
                crop = image.crop((0, 0, search_w, search_h)).convert("RGB")
                hsv = cv2.cvtColor(np.array(crop), cv2.COLOR_RGB2HSV)
                lower = np.array(cfg.get("stack_text_hsv_lower", [0, 0, 125]), dtype=np.uint8)
                upper = np.array(cfg.get("stack_text_hsv_upper", [179, 145, 255]), dtype=np.uint8)
                search_mask = cv2.inRange(hsv, lower, upper)
                for value, name, template in templates:
                    if template.size == 0:
                        continue
                    th, tw = template.shape[:2]
                    if search_mask.shape[0] < th or search_mask.shape[1] < tw:
                        continue
                    _min_val, max_val, _min_loc, max_loc = cv2.minMaxLoc(
                        cv2.matchTemplate(search_mask, template, cv2.TM_CCOEFF_NORMED)
                    )
                    score = float(max_val) if math.isfinite(float(max_val)) else 0.0
                    if score > best_score:
                        best_value = value
                        best_name = name
                        best_score = score
                        best_source = f"global@{max_loc[0]},{max_loc[1]}"

        threshold = float((self.cfg.get("speed_buffs", {}) or {}).get("stack_match_threshold", 0.72))
        if best_score < threshold:
            if boxes:
                return 0, best_score, f"haste candidates found, stack unclear best={best_name} via {best_source}"
            return 0, best_score, f"haste icon not found, stack unclear best={best_name} via {best_source}"
        return max(1, min(10, best_value)), best_score, f"{best_name} via {best_source}"

    def natro_haste_speed_multiplier(self, image: Image.Image | None = None) -> tuple[float, list[str]]:
        cfg = self.cfg.get("speed_buffs", {}) or {}
        if not bool(cfg.get("natro_haste_enabled", True)):
            return 1.0, []
        if image is None:
            image = self.speed_buff_roi_image(cfg)
        if image is None:
            return 1.0, ["natro haste: no speed ROI"]
        stack, score, detail = self.natro_haste_stack_from_image(image)
        if stack <= 0:
            return 1.0, [f"natro haste: none ({detail}, score={score:.3f})"]
        multiplier = 1.0 + max(0, stack) * 0.1
        return multiplier, [f"natro haste: x{stack} -> multiplier={multiplier:.2f} ({detail}, score={score:.3f})"]

    def vic_find_dir(self) -> Path:
        folder = Path(str(self.cfg.get("vicious_detection.folder", "vic find") or "vic find"))
        candidates = [folder] if folder.is_absolute() else [self.cfg.base_dir / folder, self.cfg.base_dir.parent / folder]
        for candidate in candidates:
            if candidate.exists():
                return candidate.resolve()
        return candidates[0].resolve()

    def field_image_candidates(self, field: str) -> list[Path]:
        field_key = str(field or "").lower().replace(" ", "").replace("_", "")
        aliases = {
            "mountain": "mountaintop",
            "mountaintopfield": "mountaintop",
            "pepperpatch": "pepper",
            "spiderfield": "spider",
            "cactusfield": "cactus",
            "rosefield": "rose",
        }
        stem = aliases.get(field_key, field_key)
        folder = self.vic_find_dir()
        stems = [stem]
        if stem == "mountaintop":
            stems.append("mountain")
        paths: list[Path] = []
        for name in stems:
            for suffix in (".png", ".jpg", ".jpeg", ".bmp", ".webp"):
                candidate = folder / f"{name}{suffix}"
                if candidate.exists():
                    paths.append(candidate)
        return paths

    def best_external_template_match(
        self,
        paths: Iterable[Path],
        scales: Iterable[float] | None = None,
        bounds: tuple[int, int, int, int] | None = None,
        source: str = "roblox",
        color: bool = True,
    ) -> tuple[Path | None, float, int, int]:
        if cv2 is None or np is None:
            return None, 0.0, 0, 0
        if source == "roblox":
            shot = self.roblox_shot_strict() or self.roblox_shot()
        else:
            shot = self.screen.shot().convert("RGB")
        img = np.array(shot)
        offset_x = 0
        offset_y = 0
        if bounds is not None:
            x1, y1, x2, y2 = bounds
            if x2 == 0:
                x2 = img.shape[1]
            if y2 == 0:
                y2 = img.shape[0]
            x1, y1 = max(0, x1), max(0, y1)
            x2, y2 = min(img.shape[1], x2), min(img.shape[0], y2)
            img = img[y1:y2, x1:x2]
            offset_x, offset_y = x1, y1
        haystack = img if color else cv2.cvtColor(img, cv2.COLOR_RGB2GRAY)
        best_path = None
        best_score = 0.0
        best_x = 0
        best_y = 0
        for path in paths:
            try:
                template_rgba = Image.open(path).convert("RGBA")
            except Exception:
                continue
            for scale in [float(s) for s in (scales or [1.0])]:
                width = max(1, round(template_rgba.width * scale))
                height = max(1, round(template_rgba.height * scale))
                if width > haystack.shape[1] or height > haystack.shape[0]:
                    continue
                resample = Image.Resampling.LANCZOS if scale != 1.0 else Image.Resampling.NEAREST
                arr = np.array(template_rgba.resize((width, height), resample))
                template = arr[:, :, :3] if color else cv2.cvtColor(arr[:, :, :3], cv2.COLOR_RGB2GRAY)
                alpha = arr[:, :, 3]
                use_mask = int(np.count_nonzero(alpha)) < alpha.size
                if use_mask:
                    mask = (alpha > 0).astype(np.uint8) * 255
                    result = cv2.matchTemplate(haystack, template, cv2.TM_CCORR_NORMED, mask=mask)
                else:
                    result = cv2.matchTemplate(haystack, template, cv2.TM_CCOEFF_NORMED)
                result = np.nan_to_num(result, nan=0.0, posinf=0.0, neginf=0.0)
                _, max_val, _, max_loc = cv2.minMaxLoc(result)
                if max_val > best_score:
                    best_path = path
                    best_score = float(max_val)
                    best_x = offset_x + int(max_loc[0])
                    best_y = offset_y + int(max_loc[1])
        return best_path, best_score, best_x, best_y

    def vicious_field_roi(self, field: str, width: int, height: int) -> tuple[int, int, int, int]:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        rois = cfg.get("field_rois", {}) or {}
        field_key = str(field or "").lower().replace(" ", "").replace("_", "")
        aliases = {
            "mountain": "mountaintop",
            "mountaintopfield": "mountaintop",
            "pepperpatch": "pepper",
            "spiderfield": "spider",
            "cactusfield": "cactus",
            "rosefield": "rose",
        }
        field_key = aliases.get(field_key, field_key)
        roi = rois.get(field_key, rois.get("default", {"left": 0.42, "right": 1.0, "top": 0.08, "bottom": 0.62}))
        x1 = int(width * float(roi.get("left", 0.42)))
        x2 = int(width * float(roi.get("right", 1.0)))
        y1 = int(height * float(roi.get("top", 0.08)))
        y2 = int(height * float(roi.get("bottom", 0.62)))
        x1, y1 = max(0, x1), max(0, y1)
        x2, y2 = min(width, x2), min(height, y2)
        return x1, y1, max(x1 + 1, x2), max(y1 + 1, y2)

    def revolution_vic_field_key(self, field: str) -> str:
        field_key = str(field or "").strip().lower().replace(" ", "").replace("_", "").replace("-", "")
        aliases = {
            "mountain": "mountain",
            "mountaintop": "mountain",
            "mountaintopfield": "mountain",
            "pepperpatch": "pepper",
            "spiderfield": "spider",
            "cactusfield": "cactus",
            "rosefield": "rose",
        }
        return aliases.get(field_key, field_key)

    def revolution_vic_dataset_path(self) -> Path:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        configured = Path(str(cfg.get("revolution_dataset", "models/revolution_vichop.bin") or "models/revolution_vichop.bin"))
        if configured.is_absolute():
            return configured
        return (self.cfg.base_dir / configured).resolve()

    def vicious_yolo_model_path(self) -> Path:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        configured = Path(str(cfg.get("yolo_model", "models/vicious_yolo.onnx") or "models/vicious_yolo.onnx"))
        if configured.is_absolute():
            return configured
        return (self.cfg.base_dir / configured).resolve()

    def load_vicious_yolo(self):
        if self._vicious_yolo_loaded:
            return self._vicious_yolo_net
        self._vicious_yolo_loaded = True
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if not bool(cfg.get("yolo_enabled", True)):
            return None
        if cv2 is None or np is None:
            print("YOLO vic detector unavailable: cv2/numpy missing", flush=True)
            return None
        path = self.vicious_yolo_model_path()
        if not path.exists():
            return None
        try:
            if ort is not None:
                # One field scan is sequential. Cap ONNX Runtime's worker
                # pool so it does not monopolize every CPU core while YOLO is
                # checking the screen. This changes speed only, never model
                # weights or detection quality.
                cpu_threads = max(1, int(cfg.get("yolo_cpu_threads", 1)))
                session_options = ort.SessionOptions()
                session_options.intra_op_num_threads = cpu_threads
                session_options.inter_op_num_threads = 1
                session_options.execution_mode = ort.ExecutionMode.ORT_SEQUENTIAL
                session_options.graph_optimization_level = ort.GraphOptimizationLevel.ORT_ENABLE_ALL
                session_options.add_session_config_entry("session.intra_op.allow_spinning", "0")
                session_options.add_session_config_entry("session.inter_op.allow_spinning", "0")
                preferred_provider = str(cfg.get("yolo_execution_provider", "cpu") or "cpu").lower()
                available_providers = set(ort.get_available_providers())
                providers: list[str] = []
                if preferred_provider in {"directml", "dml", "auto"} and "DmlExecutionProvider" in available_providers:
                    providers.append("DmlExecutionProvider")
                elif preferred_provider in {"cuda", "auto"} and "CUDAExecutionProvider" in available_providers:
                    providers.append("CUDAExecutionProvider")
                providers.append("CPUExecutionProvider")
                session = ort.InferenceSession(
                    str(path),
                    sess_options=session_options,
                    providers=providers,
                )
                input_info = session.get_inputs()[0]
                input_name = input_info.name
                input_shape = input_info.shape
                input_size = _as_int(input_shape[2], _as_int(input_shape[3], int(cfg.get("yolo_input_size", 1280))))
                self._vicious_yolo_net = ("onnxruntime", session, input_name, input_size)
            else:
                self._vicious_yolo_net = ("opencv", cv2.dnn.readNetFromONNX(str(path)), None, int(cfg.get("yolo_input_size", 1280)))
            if ort is not None:
                print(
                    f"YOLO vic detector loaded: {path} "
                    f"(providers={session.get_providers()}, CPU threads={cpu_threads})",
                    flush=True,
                )
            else:
                print(f"YOLO vic detector loaded: {path} (OpenCV)", flush=True)
        except Exception as exc:
            print(f"Could not load YOLO vic detector {path}: {exc}", flush=True)
            self._vicious_yolo_net = None
        return self._vicious_yolo_net

    def yolo_letterbox(self, image: np.ndarray, input_size: int) -> tuple[np.ndarray, float, int, int]:
        height, width = image.shape[:2]
        scale = min(input_size / max(1, width), input_size / max(1, height))
        resized_w = max(1, int(round(width * scale)))
        resized_h = max(1, int(round(height * scale)))
        resized = cv2.resize(image, (resized_w, resized_h), interpolation=cv2.INTER_LINEAR)
        canvas = np.full((input_size, input_size, 3), 114, dtype=np.uint8)
        pad_x = (input_size - resized_w) // 2
        pad_y = (input_size - resized_h) // 2
        canvas[pad_y:pad_y + resized_h, pad_x:pad_x + resized_w] = resized
        return canvas, scale, pad_x, pad_y

    def yolo_best_detection(
        self,
        output,
        input_size: int,
        scale: float,
        pad_x: int,
        pad_y: int,
        offset_x: int = 0,
        offset_y: int = 0,
        accept_roi: tuple[int, int, int, int] | None = None,
    ) -> tuple[float, tuple[int, int, int, int] | None, float, tuple[int, int, int, int] | None, int, str]:
        arr = np.asarray(output)
        arr = np.squeeze(arr)
        if arr.ndim == 1:
            arr = arr.reshape(1, -1)
        if arr.ndim != 2:
            return 0.0, None, 0.0, None, 0, f"unsupported output shape {getattr(output, 'shape', None)}"
        if arr.shape[0] < arr.shape[1] and arr.shape[0] in {5, 6, 84, 85}:
            arr = arr.T
        if arr.shape[1] < 5 or arr.shape[0] == 0:
            return 0.0, None, 0.0, None, 0, ""

        arr = arr.astype(np.float32, copy=False)
        cols = arr.shape[1]
        if cols == 5:
            scores = arr[:, 4]
        elif cols == 6:
            first = arr[:, 4]
            second = arr[:, 5]
            scores = np.where((first <= 1.0) & (second <= 1.0), first * second, np.maximum(first, second))
        else:
            objectness = arr[:, 4]
            max_class = np.max(arr[:, 5:], axis=1)
            max_any = np.max(arr[:, 4:], axis=1)
            scores = np.where(objectness <= 1.0, objectness * max_class, max_any)
        scores = np.nan_to_num(scores, nan=0.0, posinf=0.0, neginf=0.0)

        coords = arr[:, :4].copy()
        normalized = np.max(coords, axis=1) <= 1.5
        coords[normalized] *= float(input_size)

        inv_scale = 1.0 / max(scale, 0.0001)
        left = (coords[:, 0] - coords[:, 2] * 0.5 - pad_x) * inv_scale + offset_x
        top = (coords[:, 1] - coords[:, 3] * 0.5 - pad_y) * inv_scale + offset_y
        width = coords[:, 2] * inv_scale
        height = coords[:, 3] * inv_scale

        best_any_box = None
        best_any_score = 0.0
        if scores.size:
            any_index = int(np.argmax(scores))
            best_any_score = float(scores[any_index])
            if best_any_score > 0.0:
                best_any_box = (
                    int(left[any_index]),
                    int(top[any_index]),
                    int(width[any_index]),
                    int(height[any_index]),
                )

        accepted = np.ones(scores.shape, dtype=bool)
        roi_rejects = 0
        if accept_roi is not None:
            ax1, ay1, ax2, ay2 = accept_roi
            center_x = left + width * 0.5
            center_y = top + height * 0.5
            accepted = (center_x >= ax1) & (center_x <= ax2) & (center_y >= ay1) & (center_y <= ay2)
            roi_rejects = int(np.count_nonzero(~accepted))

        accepted_scores = np.where(accepted, scores, 0.0)
        best_box = None
        best_score = 0.0
        if accepted_scores.size:
            best_index = int(np.argmax(accepted_scores))
            best_score = float(accepted_scores[best_index])
            if best_score > 0.0:
                best_box = (
                    int(left[best_index]),
                    int(top[best_index]),
                    int(width[best_index]),
                    int(height[best_index]),
                )
        return best_score, best_box, best_any_score, best_any_box, roi_rejects, ""

    def vicious_yolo_visible(
        self,
        field: str,
        image: np.ndarray,
        offset_x: int,
        offset_y: int,
        accept_roi: tuple[int, int, int, int] | None = None,
    ) -> bool | None:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        self._last_vicious_yolo_detection = {
            "field": field,
            "confidence": 0.0,
            "found": False,
            "box": None,
        }
        net = self.load_vicious_yolo()
        if net is None:
            return None
        try:
            field_thresholds = cfg.get("yolo_field_confidence", {}) or {}
            conf_threshold = float(field_thresholds.get(field, cfg.get("yolo_confidence", 0.55)))
            engine, model, input_name, model_input_size = net
            input_size = int(model_input_size or cfg.get("yolo_input_size", 1280))
            yolo_input, scale, pad_x, pad_y = self.yolo_letterbox(image, input_size)
            blob = cv2.dnn.blobFromImage(yolo_input, 1.0 / 255.0, (input_size, input_size), swapRB=False, crop=False)
            if engine == "onnxruntime":
                output = model.run(None, {input_name: blob.astype(np.float32)})[0]
            else:
                model.setInput(blob)
                output = model.forward()
            best_score, best_box, best_any_score, best_any_box, roi_rejects, error = self.yolo_best_detection(
                output,
                input_size,
                scale,
                pad_x,
                pad_y,
                offset_x,
                offset_y,
                accept_roi,
            )
            if error:
                print(f"YOLO vic {field}: {error}", flush=True)
                return None
            found = best_score >= conf_threshold
            self._last_vicious_yolo_detection = {
                "field": field,
                "confidence": float(best_score),
                "found": bool(found),
                "box": best_box,
            }
            if best_box is None:
                if best_any_box is None:
                    print(f"YOLO vic {field}: no boxes confidence={best_score:.3f}/{conf_threshold:.3f}", flush=True)
                else:
                    bx, by, bw, bh = best_any_box
                    print(
                        f"YOLO vic {field}: no accepted boxes confidence={best_score:.3f}/{conf_threshold:.3f} "
                        f"best_any={best_any_score:.3f} box=({bx},{by},{bw},{bh}) roi_rejects={roi_rejects}",
                        flush=True,
                    )
            else:
                bx, by, bw, bh = best_box
                print(
                    f"YOLO vic {field}: found={found} confidence={best_score:.3f}/{conf_threshold:.3f} "
                    f"box=({bx},{by},{bw},{bh}) roi_rejects={roi_rejects}",
                    flush=True,
                )
            return found
        except Exception as exc:
            print(f"YOLO vic {field}: detection failed: {exc}", flush=True)
            return None

    def last_vicious_yolo_detection(self) -> dict[str, object]:
        return dict(self._last_vicious_yolo_detection)

    def find_tesseract_executable(self) -> Path | None:
        cmd = shutil.which("tesseract")
        candidates = [
            Path(cmd) if cmd else None,
            self.cfg.base_dir / "tesseract" / "tesseract.exe",
            self.cfg.base_dir / "_internal" / "tesseract" / "tesseract.exe",
            ROOT / "tesseract" / "tesseract.exe",
            Path(r"C:\Program Files\Tesseract-OCR\tesseract.exe"),
            Path(r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe"),
            Path.home() / r"AppData\Local\Programs\Tesseract-OCR\tesseract.exe",
        ]
        for candidate in candidates:
            if candidate and candidate.exists():
                return candidate.resolve()
        return None

    @staticmethod
    def file_sha256(path: Path) -> str:
        digest = hashlib.sha256()
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        return digest.hexdigest().upper()

    def install_tesseract_from_official_release(self) -> Path | None:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if not bool(cfg.get("message_ocr_direct_install_enabled", True)):
            return None
        url = str(cfg.get("message_ocr_tesseract_installer_url", TESSERACT_WINDOWS_INSTALLER_URL) or "").strip()
        expected_hash = str(
            cfg.get("message_ocr_tesseract_installer_sha256", TESSERACT_WINDOWS_INSTALLER_SHA256) or ""
        ).strip().upper()
        if not url or not expected_hash:
            print("Tesseract OCR direct install is missing URL or SHA-256 configuration.", flush=True)
            return None

        cache_dir = Path(tempfile.gettempdir()) / "ViciousBeeFarm"
        cache_dir.mkdir(parents=True, exist_ok=True)
        installer = cache_dir / "tesseract-ocr-w64-setup.exe"
        download = installer.with_suffix(".download")

        try:
            valid_cached = installer.exists() and self.file_sha256(installer) == expected_hash
            if not valid_cached:
                with contextlib.suppress(OSError):
                    download.unlink()
                print("Tesseract OCR missing; downloading verified Windows installer...", flush=True)
                timeout = max(30.0, float(cfg.get("message_ocr_download_timeout_seconds", 180.0)))
                with requests.get(url, stream=True, timeout=(15.0, timeout)) as response:
                    response.raise_for_status()
                    with download.open("wb") as handle:
                        for chunk in response.iter_content(chunk_size=1024 * 1024):
                            if chunk:
                                handle.write(chunk)
                actual_hash = self.file_sha256(download)
                if actual_hash != expected_hash:
                    with contextlib.suppress(OSError):
                        download.unlink()
                    print(
                        f"Tesseract OCR installer hash mismatch: {actual_hash} != {expected_hash}",
                        flush=True,
                    )
                    return None
                os.replace(download, installer)

            print("Installing Tesseract OCR silently...", flush=True)
            timeout = max(30.0, float(cfg.get("message_ocr_install_timeout_seconds", 240.0)))
            completed = subprocess.run(
                [str(installer), "/S"],
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=timeout,
                check=False,
            )
            if completed.returncode != 0:
                output = (completed.stdout or "").strip().replace("\r", "")
                print(
                    f"Tesseract OCR direct install failed (exit {completed.returncode}): {output[-600:]}",
                    flush=True,
                )
                return None
        except Exception as exc:
            print(f"Tesseract OCR direct install failed: {exc}", flush=True)
            return None

        found = self.find_tesseract_executable()
        if found is None:
            print("Tesseract OCR installer finished, but tesseract.exe was not found.", flush=True)
            return None
        print(f"Tesseract OCR installed: {found}", flush=True)
        return found

    def ensure_tesseract_available(self) -> bool:
        if pytesseract is None:
            return False
        if self._tesseract_checked and self._tesseract_available:
            return True

        found = self.find_tesseract_executable()
        if found is not None:
            pytesseract.pytesseract.tesseract_cmd = str(found)
            self._tesseract_checked = True
            self._tesseract_available = True
            return True

        self._tesseract_checked = True
        auto_install = bool(self.cfg.get("vicious_detection.message_ocr_auto_install_tesseract", True))
        if not auto_install or self._tesseract_install_attempted:
            self._tesseract_available = False
            return False

        self._tesseract_install_attempted = True
        winget = shutil.which("winget")
        package_ids = self.cfg.get(
            "vicious_detection.message_ocr_tesseract_winget_ids",
            ["tesseract-ocr.tesseract", "UB-Mannheim.TesseractOCR"],
        )
        if isinstance(package_ids, str):
            package_ids = [package_ids]
        timeout = max(30.0, float(self.cfg.get("vicious_detection.message_ocr_install_timeout_seconds", 240.0)))

        for package_id in package_ids if winget else []:
            package_id = str(package_id).strip()
            if not package_id:
                continue
            print(f"Tesseract OCR missing; installing {package_id} with winget...", flush=True)
            try:
                completed = subprocess.run(
                    [
                        winget,
                        "install",
                        "--id",
                        package_id,
                        "-e",
                        "--silent",
                        "--accept-package-agreements",
                        "--accept-source-agreements",
                    ],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    timeout=timeout,
                    check=False,
                )
            except Exception as exc:
                print(f"Tesseract OCR auto-install failed for {package_id}: {exc}", flush=True)
                continue

            if completed.returncode != 0:
                output = (completed.stdout or "").strip().replace("\r", "")
                print(
                    f"Tesseract OCR auto-install failed for {package_id} "
                    f"(exit {completed.returncode}): {output[-600:]}",
                    flush=True,
                )
                continue

            found = self.find_tesseract_executable()
            if found is not None:
                pytesseract.pytesseract.tesseract_cmd = str(found)
                self._tesseract_available = True
                print(f"Tesseract OCR installed: {found}", flush=True)
                return True

        found = self.install_tesseract_from_official_release()
        if found is not None:
            pytesseract.pytesseract.tesseract_cmd = str(found)
            self._tesseract_available = True
            return True

        if not winget:
            print("Tesseract OCR missing; winget unavailable and direct install failed.", flush=True)
        else:
            print("Tesseract OCR missing; winget and direct install both failed.", flush=True)
        self._tesseract_available = False
        return False

    def ocr_text_for_image(self, image: Image.Image) -> str:
        if not self.ensure_tesseract_available():
            return ""
        try:
            scale = float(self.cfg.get("vicious_detection.message_ocr_scale", 2.0))
            img = self.prepare_ocr_image(image, scale)
            return pytesseract.image_to_string(img, config="--psm 6")
        except Exception as exc:
            print(f"OCR unavailable: {exc}", flush=True)
            return ""

    def prepare_ocr_image(self, image: Image.Image, scale: float) -> Image.Image:
        img = image.convert("L")
        if scale > 1.0:
            img = img.resize(
                (max(1, int(img.width * scale)), max(1, int(img.height * scale))),
                Image.Resampling.LANCZOS,
            )
        img = ImageOps.autocontrast(img)
        img = ImageEnhance.Contrast(img).enhance(1.8)
        return img

    def prepare_message_ocr_variants(self, image: Image.Image, scale: float) -> list[tuple[str, Image.Image]]:
        variants = [("gray", self.prepare_ocr_image(image, scale))]
        if np is None:
            return variants
        try:
            crop = image.convert("RGB")
            if scale > 1.0:
                crop = crop.resize(
                    (max(1, int(crop.width * scale)), max(1, int(crop.height * scale))),
                    Image.Resampling.LANCZOS,
                )
            arr = np.array(crop).astype(np.int16)
            r = arr[:, :, 0]
            g = arr[:, :, 1]
            b = arr[:, :, 2]
            red = (r >= 120) & (r >= g + 35) & (r >= b + 35)
            yellow = (r >= 150) & (g >= 90) & (b <= 90) & (r >= b + 55)
            mask = red | yellow
            if int(np.count_nonzero(mask)) > 8:
                out = np.full(mask.shape, 255, dtype=np.uint8)
                out[mask] = 0
                mask_img = Image.fromarray(out, mode="L")
                mask_img = mask_img.filter(ImageFilter.MinFilter(3))
                variants.append(("redmask", mask_img))
        except Exception as exc:
            print(f"OCR message preprocessing unavailable: {exc}", flush=True)
        return variants

    def ocr_text_for_regions(
        self,
        image: Image.Image,
        regions: Iterable[tuple[float, float, float, float]],
        *,
        scale: float | None = None,
        psm_values: Iterable[int] = (6, 7, 11),
        variant_names: Iterable[str] | None = None,
        debug_label: str = "",
    ) -> str:
        if not self.ensure_tesseract_available():
            return ""
        base_scale = float(scale if scale is not None else self.cfg.get("vicious_detection.message_ocr_crop_scale", 4.0))
        cfg = self.cfg.get("vicious_detection", {}) or {}
        debug_enabled = bool(debug_label) or bool(cfg.get("message_ocr_debug", False))
        debug_dir = self.cfg.base_dir / "debug_vicious_ocr"
        debug_saved = 0
        texts: list[str] = []
        allowed_variants = {str(name).lower() for name in variant_names} if variant_names is not None else None
        width, height = image.size
        for index, (left, top, right, bottom) in enumerate(regions, start=1):
            box = (
                max(0, min(width - 1, int(width * float(left)))),
                max(0, min(height - 1, int(height * float(top)))),
                max(1, min(width, int(width * float(right)))),
                max(1, min(height, int(height * float(bottom)))),
            )
            if box[2] <= box[0] or box[3] <= box[1]:
                continue
            try:
                raw_crop = image.crop(box)
                variants = self.prepare_message_ocr_variants(raw_crop, base_scale)
                for variant_name, crop in variants:
                    if allowed_variants is not None and variant_name.lower() not in allowed_variants:
                        continue
                    if debug_enabled:
                        debug_dir.mkdir(exist_ok=True)
                        safe_label = re.sub(r"[^a-zA-Z0-9_.-]+", "_", debug_label or "ocr")[:60]
                        crop_path = debug_dir / f"{int(time.time() * 1000)}_{safe_label}_r{index}_{variant_name}.png"
                        crop.save(crop_path)
                        debug_saved += 1
                    for psm in psm_values:
                        text = pytesseract.image_to_string(crop, config=f"--psm {int(psm)}")
                        normalized = self.normalize_ocr_text(text)
                        if debug_enabled:
                            print(
                                f"OCR {debug_label or 'message'} region={index} box={box} "
                                f"variant={variant_name} psm={int(psm)} text={normalized[:180]!r}",
                                flush=True,
                            )
                        if text:
                            texts.append(text)
            except Exception as exc:
                print(f"OCR region unavailable: {exc}", flush=True)
        if debug_enabled:
            print(f"OCR {debug_label or 'message'} saved_debug_crops={debug_saved} dir={debug_dir}", flush=True)
        return "\n".join(texts)

    @staticmethod
    def normalize_ocr_text(text: str) -> str:
        compact = " ".join(str(text or "").lower().split())
        return re.sub(r"[^a-z0-9]+", " ", compact)

    @staticmethod
    def has_nearby_words(text: str, first: str, second: str, max_gap: int = 8) -> bool:
        words = [word for word in str(text or "").split() if word]
        first_positions = [idx for idx, word in enumerate(words) if word == first]
        second_positions = [idx for idx, word in enumerate(words) if word == second]
        return any(abs(a - b) <= max_gap for a in first_positions for b in second_positions)

    @staticmethod
    def defeated_phrase_visible_in_text(text: str) -> bool:
        normalized = Detector.normalize_ocr_text(text)
        if "vicious bee has been defeated" in normalized:
            return True
        if "vicious bee defeated" in normalized:
            return True
        if "vicious" not in normalized or "defeated" not in normalized:
            return False
        if not Detector.has_nearby_words(normalized, "vicious", "defeated", max_gap=8):
            return False
        words = normalized.split()
        for idx, word in enumerate(words):
            if word != "vicious":
                continue
            window = words[idx : idx + 10]
            if "defeated" in window and ("bee" in window or "be" in window):
                return True
        return False

    @staticmethod
    def vicious_left_phrase_visible_in_text(text: str) -> bool:
        normalized = Detector.normalize_ocr_text(text)
        left_words = {"left", "lett", "ieft", "lelt"}
        words = normalized.split()
        has_left_word = any(word in left_words or word.startswith("lef") or word.startswith("let") for word in words)
        if not has_left_word:
            return False
        if "vicious bee left" in normalized or "vicious left" in normalized or "vicious bee lett" in normalized:
            return True
        if "vicious" in normalized and "bee" in normalized:
            positions_vicious = [idx for idx, word in enumerate(words) if word == "vicious" or word.startswith("vici")]
            positions_left = [idx for idx, word in enumerate(words) if word in left_words or word.startswith("lef") or word.startswith("let")]
            if any(abs(a - b) <= 8 for a in positions_vicious for b in positions_left):
                return True
        if "vicious" in normalized and "bee" in normalized and Detector.has_nearby_words(normalized, "vicious", "left", max_gap=8):
            return True
        for idx, word in enumerate(words):
            # Tesseract sometimes damages "vicious" on the small red text, so accept a short prefix near "left".
            if not word.startswith("vici"):
                continue
            window = words[idx : idx + 9]
            if any(item in left_words or item.startswith("lef") or item.startswith("let") for item in window):
                return True
        return False

    def vicious_attack_message_visible(self, screenshot: Image.Image | None = None) -> bool:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if screenshot is None:
            now = time.monotonic()
            last_found, last_time = self._attack_message_ocr_cache
            interval = max(0.05, float(cfg.get("attack_message_ocr_interval_seconds", 0.35)))
            if now - last_time < interval:
                return last_found
        image = screenshot if screenshot is not None else self.roblox_shot()
        regions = cfg.get(
            "attack_message_ocr_live_regions",
            [
                [0.56, 0.84, 1.0, 1.0],
                [0.45, 0.76, 1.0, 1.0],
            ],
        )
        text = self.normalize_ocr_text(
            self.ocr_text_for_regions(
                image,
                regions,
                psm_values=(11,),
                variant_names=("redmask",),
            )
        )
        found = "vicious" in text and "attacking" in text
        if screenshot is None:
            self._attack_message_ocr_cache = (found, time.monotonic())
        if bool(cfg.get("attack_message_log", False)):
            print(f"Vicious attack OCR visible={found} text={text[:220]!r}", flush=True)
        return found

    def vicious_yolo_detect_result(
        self,
        field: str,
        image: np.ndarray,
        offset_x: int = 0,
        offset_y: int = 0,
        accept_roi: tuple[int, int, int, int] | None = None,
    ) -> dict:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        result = {
            "found": False,
            "confidence": 0.0,
            "threshold": float((cfg.get("yolo_field_confidence", {}) or {}).get(field, cfg.get("yolo_confidence", 0.55))),
            "box": None,
            "best_any_confidence": 0.0,
            "best_any_box": None,
            "roi_rejects": 0,
            "error": "",
        }
        if cv2 is None or np is None:
            result["error"] = "OpenCV/numpy unavailable"
            return result
        net = self.load_vicious_yolo()
        if net is None:
            result["error"] = "YOLO model unavailable"
            return result
        try:
            field_thresholds = cfg.get("yolo_field_confidence", {}) or {}
            conf_threshold = float(field_thresholds.get(field, cfg.get("yolo_confidence", 0.55)))
            result["threshold"] = conf_threshold
            engine, model, input_name, model_input_size = net
            input_size = int(model_input_size or cfg.get("yolo_input_size", 1280))
            yolo_input, scale, pad_x, pad_y = self.yolo_letterbox(image, input_size)
            blob = cv2.dnn.blobFromImage(yolo_input, 1.0 / 255.0, (input_size, input_size), swapRB=False, crop=False)
            if engine == "onnxruntime":
                output = model.run(None, {input_name: blob.astype(np.float32)})[0]
            else:
                model.setInput(blob)
                output = model.forward()
            best_score, best_box, best_any_score, best_any_box, roi_rejects, error = self.yolo_best_detection(
                output,
                input_size,
                scale,
                pad_x,
                pad_y,
                offset_x,
                offset_y,
                accept_roi,
            )
            if error:
                result["error"] = error
                return result

            result.update(
                {
                    "found": bool(best_box is not None and best_score >= conf_threshold),
                    "confidence": float(best_score),
                    "box": best_box,
                    "best_any_confidence": float(best_any_score),
                    "best_any_box": best_any_box,
                    "roi_rejects": roi_rejects,
                }
            )
            return result
        except Exception as exc:
            result["error"] = str(exc)
            return result

    def infer_vicious_field_from_path(self, image_path: Path) -> str:
        name = image_path.stem.lower().replace(" ", "").replace("-", "_")
        if "mountain" in name or "mountaintop" in name:
            return "mountaintop"
        for field in ("pepper", "spider", "cactus", "rose"):
            if field in name:
                return field
        return "manual"

    def test_vicious_image_file(self, image_path: Path) -> tuple[dict, Path]:
        if cv2 is None or np is None:
            raise RuntimeError("OpenCV/numpy lipsesc; nu pot rula YOLO.")
        image_path = Path(image_path)
        field = self.infer_vicious_field_from_path(image_path)
        image = Image.open(image_path).convert("RGB")
        arr = np.array(image)
        result = self.vicious_yolo_detect_result(field, arr, 0, 0, accept_roi=None)

        annotated = arr.copy()
        label = f"vicious {result['confidence']:.3f}/{result['threshold']:.3f}"
        color = (0, 255, 0) if result["found"] else (255, 0, 0)
        box = result.get("box")
        if box is not None:
            x, y, w, h = box
            x1 = max(0, x)
            y1 = max(0, y)
            x2 = min(annotated.shape[1] - 1, x + max(1, w))
            y2 = min(annotated.shape[0] - 1, y + max(1, h))
            cv2.rectangle(annotated, (x1, y1), (x2, y2), color, 3)
            cv2.putText(
                annotated,
                label,
                (x1, max(24, y1 - 8)),
                cv2.FONT_HERSHEY_SIMPLEX,
                0.8,
                color,
                2,
                cv2.LINE_AA,
            )
        else:
            cv2.putText(
                annotated,
                label,
                (24, 40),
                cv2.FONT_HERSHEY_SIMPLEX,
                0.9,
                color,
                2,
                cv2.LINE_AA,
            )

        debug_dir = self.cfg.base_dir / "debug_vicious_ai"
        debug_dir.mkdir(exist_ok=True)
        safe_stem = re.sub(r"[^a-zA-Z0-9_.-]+", "_", image_path.stem)[:80]
        out_path = debug_dir / (
            f"manual_yolo_{field}_found{int(result['found'])}_"
            f"{int(time.time() * 1000)}_{safe_stem}.png"
        )
        Image.fromarray(annotated).save(out_path)
        return result, out_path

    def test_vicious_message_image_file(self, image_path: Path) -> dict:
        image_path = Path(image_path)
        image = Image.open(image_path).convert("RGB")
        cfg = self.cfg.get("vicious_detection", {}) or {}
        attack_regions = cfg.get(
            "attack_message_ocr_regions",
            [
                [0.56, 0.84, 1.0, 1.0],
                [0.45, 0.76, 1.0, 1.0],
                [0.0, 0.78, 1.0, 1.0],
                [0.0, 0.0, 1.0, 1.0],
            ],
        )
        defeated_regions = cfg.get(
            "defeated_message_ocr_regions",
            [
                [0.0, 0.0, 1.0, 0.28],
                [0.18, 0.0, 0.82, 0.35],
                [0.45, 0.72, 1.0, 1.0],
                [0.0, 0.0, 1.0, 1.0],
            ],
        )
        left_regions = cfg.get(
            "vicious_left_message_ocr_regions",
            [
                [0.62, 0.78, 1.0, 1.0],
                [0.72, 0.84, 1.0, 1.0],
            ],
        )
        safe_stem = re.sub(r"[^a-zA-Z0-9_.-]+", "_", image_path.stem)[:40]
        attack_text = self.normalize_ocr_text(
            self.ocr_text_for_regions(image, attack_regions, debug_label=f"{safe_stem}_attack")
        )
        defeated_text = self.normalize_ocr_text(
            self.ocr_text_for_regions(image, defeated_regions, debug_label=f"{safe_stem}_defeated")
        )
        left_text = self.normalize_ocr_text(
            self.ocr_text_for_regions(
                image,
                left_regions,
                scale=float(cfg.get("vicious_left_message_ocr_scale", cfg.get("message_ocr_crop_scale", 4.0))),
                psm_values=tuple(int(value) for value in cfg.get("vicious_left_message_ocr_psm_values", [6, 11])),
                variant_names=cfg.get("vicious_left_message_ocr_variants", ["redmask", "gray"]),
                debug_label=f"{safe_stem}_left",
            )
        )
        attack_visible = "vicious" in attack_text and "attacking" in attack_text
        defeated_visible = self.defeated_phrase_visible_in_text(defeated_text)
        left_visible = self.vicious_left_phrase_visible_in_text(left_text)
        result = {
            "attack_message": bool(attack_visible),
            "defeated_message": bool(defeated_visible),
            "left_message": bool(left_visible),
            "attack_text": attack_text[:500],
            "defeated_text": defeated_text[:500],
            "left_text": left_text[:500],
            "image": str(image_path),
        }
        print(
            f"Vicious message test: attack={result['attack_message']} "
            f"defeated={result['defeated_message']} "
            f"left={result['left_message']} image={image_path}",
            flush=True,
        )
        print(f"Vicious message test attack_text={result['attack_text']!r}", flush=True)
        print(f"Vicious message test defeated_text={result['defeated_text']!r}", flush=True)
        print(f"Vicious message test left_text={result['left_text']!r}", flush=True)
        return result

    def load_revolution_vic_dataset(self) -> dict[str, dict] | None:
        if self._revolution_vic_dataset_loaded:
            return self._revolution_vic_dataset
        self._revolution_vic_dataset_loaded = True
        if cv2 is None or np is None or BSON is None:
            print("Revolution vic detector unavailable: cv2/numpy/bson missing", flush=True)
            return None
        path = self.revolution_vic_dataset_path()
        if not path.exists():
            print(f"Revolution vic dataset missing: {path}", flush=True)
            return None
        try:
            raw = BSON(path.read_bytes()).decode()
            fields = raw.get("fields", {}) or {}
            loaded: dict[str, dict] = {}
            for name, field_data in fields.items():
                params = field_data.get("parameters", {}) or {}
                desc = field_data.get("descriptor", {}) or {}
                rows = int(desc.get("rows", 0))
                cols = int(desc.get("cols", 0))
                mat_type = int(desc.get("type", -1))
                data = bytes(desc.get("data", b""))
                if rows <= 0 or cols <= 0 or not data:
                    continue
                if mat_type != 5:
                    print(f"Revolution vic dataset {name}: unsupported descriptor type {mat_type}", flush=True)
                    continue
                descriptors = np.frombuffer(data, dtype=np.float32).reshape((rows, cols)).copy()
                loaded[str(name).lower()] = {"params": params, "descriptors": descriptors}
            self._revolution_vic_dataset = loaded
            version = raw.get("version", "?")
            print(f"Revolution vic dataset loaded: version={version} fields={','.join(sorted(loaded))}", flush=True)
        except Exception as exc:
            print(f"Could not load Revolution vic dataset: {exc}", flush=True)
            self._revolution_vic_dataset = None
        return self._revolution_vic_dataset

    def gamma_correct_gray(self, gray, gamma: float):
        if gamma <= 0 or abs(gamma - 1.0) < 0.001:
            return gray
        # Revolution stores gamma per field; using inverse gamma brightens dark/night shots.
        inv = 1.0 / gamma
        table = np.array([((i / 255.0) ** inv) * 255 for i in range(256)], dtype=np.uint8)
        return cv2.LUT(gray, table)

    def largest_revolution_match_cluster(self, points: list[tuple[float, float]], radius: float) -> int:
        if not points:
            return 0
        best = 1
        radius_sq = radius * radius
        for px, py in points:
            count = 0
            for qx, qy in points:
                dx = px - qx
                dy = py - qy
                if dx * dx + dy * dy <= radius_sq:
                    count += 1
            if count > best:
                best = count
        return best

    def revolution_vic_visible(self, field: str, img_rgb=None) -> bool | None:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if not bool(cfg.get("revolution_enabled", False)):
            return None
        dataset = self.load_revolution_vic_dataset()
        if not dataset:
            return None
        field_key = self.revolution_vic_field_key(field)
        model = dataset.get(field_key)
        if model is None:
            print(f"Revolution vic {field}: no dataset field '{field_key}'", flush=True)
            return None
        if img_rgb is None:
            img_rgb = np.array(self.roblox_shot().convert("RGB"))
        params = model["params"]
        height, width = img_rgb.shape[:2]
        cut_top = int(params.get("cut_top", 0) or 0)
        cut_bottom = int(params.get("cut_bottom", 0) or 0)
        cut_left = int(params.get("cut_left", 0) or 0)
        cut_right = int(params.get("cut_right", 0) or 0)
        x1 = max(0, min(width - 1, cut_left))
        y1 = max(0, min(height - 1, cut_top))
        x2 = max(x1 + 1, min(width, width - cut_right))
        y2 = max(y1 + 1, min(height, height - cut_bottom))
        crop = img_rgb[y1:y2, x1:x2]
        if crop.size == 0:
            return False
        gray = cv2.cvtColor(crop, cv2.COLOR_RGB2GRAY)
        gray = self.gamma_correct_gray(gray, float(params.get("gamma", 1.0) or 1.0))
        try:
            sift = cv2.SIFT_create(
                nfeatures=0,
                nOctaveLayers=int(params.get("octave_layers", 3) or 3),
                contrastThreshold=float(params.get("contrast_threshold", 0.04) or 0.04),
                edgeThreshold=float(params.get("edge_threshold", 10.0) or 10.0),
                sigma=float(params.get("sigma", 1.6) or 1.6),
            )
            keypoints, descriptors = sift.detectAndCompute(gray, None)
        except Exception as exc:
            print(f"Revolution vic {field}: SIFT failed: {exc}", flush=True)
            return None
        if descriptors is None or len(keypoints) == 0:
            self.save_revolution_vic_debug(field_key, crop, gray, [], x1, y1, False, "no_scene_descriptors")
            print(f"Revolution vic {field}: found=False good=0 scene_kp=0 reason=no_scene_descriptors", flush=True)
            return False
        descriptors = descriptors.astype(np.float32, copy=False)
        train = model["descriptors"].astype(np.float32, copy=False)
        matcher = cv2.BFMatcher(cv2.NORM_L2)
        try:
            matches = matcher.knnMatch(train, descriptors, k=2)
        except Exception as exc:
            print(f"Revolution vic {field}: matcher failed: {exc}", flush=True)
            return None
        lowe = float(params.get("lowe_ratio", 0.6) or 0.6)
        good = []
        for pair in matches:
            if len(pair) >= 2 and pair[0].distance < lowe * pair[1].distance:
                good.append(pair[0])
        match_threshold = int(params.get("match_threshold", 3) or 3)
        radius = float(params.get("keypoint_radius", params.get("epsilon", 40.0)) or 40.0)
        min_cluster = int(params.get("min_cluster_density", match_threshold) or match_threshold)
        points = [(keypoints[m.trainIdx].pt[0], keypoints[m.trainIdx].pt[1]) for m in good if m.trainIdx < len(keypoints)]
        cluster = self.largest_revolution_match_cluster(points, radius)
        found = len(good) >= match_threshold and cluster >= min_cluster
        reason = "cluster_match" if found else "not_enough_clustered_matches"
        print(
            f"Revolution vic {field}: found={found} good={len(good)} scene_kp={len(keypoints)} "
            f"cluster={cluster}/{min_cluster} match_threshold={match_threshold} lowe={lowe:.2f} "
            f"roi=({x1},{y1},{x2},{y2}) reason={reason}",
            flush=True,
        )
        self.save_revolution_vic_debug(field_key, crop, gray, points, x1, y1, found, reason)
        return found

    def save_revolution_vic_debug(
        self,
        field: str,
        crop,
        gray,
        points: list[tuple[float, float]],
        offset_x: int,
        offset_y: int,
        found: bool,
        reason: str,
    ) -> None:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if not bool(cfg.get("revolution_debug_save", cfg.get("ai_debug_save", False))):
            return
        try:
            debug_dir = self.cfg.base_dir / "debug_vicious_ai"
            debug_dir.mkdir(exist_ok=True)
            stamp = int(time.time() * 1000)
            status = "found1" if found else "found0"
            stem = f"{field}_rev_{status}_{stamp}_{reason}_x{offset_x}_y{offset_y}_m{len(points)}"
            Image.fromarray(crop).save(debug_dir / f"{stem}_crop.png")
            mask = np.zeros(gray.shape, dtype=np.uint8)
            for px, py in points:
                cv2.circle(mask, (int(round(px)), int(round(py))), 5, 255, -1)
            Image.fromarray(mask).save(debug_dir / f"{stem}_matches.png")
        except Exception as exc:
            print(f"Could not save Revolution vic debug crop: {exc}", flush=True)

    def vicious_ai_visible(self, field: str, screenshot: Image.Image | None = None) -> bool:
        if cv2 is None or np is None:
            return False
        self._last_vicious_yolo_detection = {
            "field": field,
            "confidence": 0.0,
            "found": False,
            "box": None,
        }
        cfg = self.cfg.get("vicious_detection", {}) or {}
        field_key = str(field or "").strip().lower().replace(" ", "").replace("_", "").replace("-", "")
        field_key = {
            "mountain": "mountaintop",
            "mountaintopfield": "mountaintop",
        }.get(field_key, field_key)
        source_image = screenshot if screenshot is not None else self.roblox_shot()
        img = np.array(source_image.convert("RGB"))
        revolution_result = self.revolution_vic_visible(field, img)
        if revolution_result is True:
            return True
        height, width = img.shape[:2]
        x1, y1, x2, y2 = self.vicious_field_roi(field, width, height)
        crop = img[y1:y2, x1:x2]
        if crop.size == 0:
            return False
        yolo_result = self.vicious_yolo_visible(field_key, img, 0, 0, accept_roi=None)
        if yolo_result is True:
            return True
        if yolo_result is False and not bool(cfg.get("yolo_fallback_to_color", True)):
            return False
        if yolo_result is None:
            if revolution_result is False and not bool(cfg.get("ai_color_fallback", False)):
                return False
            if revolution_result is None and not bool(cfg.get("ai_color_fallback_when_model_missing", True)):
                return False
        hsv = cv2.cvtColor(crop, cv2.COLOR_RGB2HSV)
        h_chan, s_chan, v_chan = cv2.split(hsv)
        r_chan = crop[:, :, 0]
        g_chan = crop[:, :, 1]
        b_chan = crop[:, :, 2]

        cyan = (
            (h_chan >= int(cfg.get("ai_cyan_h_min", 78)))
            & (h_chan <= int(cfg.get("ai_cyan_h_max", 112)))
            & (s_chan >= int(cfg.get("ai_cyan_s_min", 28)))
            & (v_chan >= int(cfg.get("ai_cyan_v_min", 28)))
            & (b_chan.astype(np.int16) >= r_chan.astype(np.int16) + int(cfg.get("ai_blue_over_red_min", 8)))
        ).astype(np.uint8)
        field_shape_masks = cfg.get("field_shape_masks", {}) or {}
        shape_points = field_shape_masks.get(field_key)
        if shape_points:
            try:
                mask = np.zeros(crop.shape[:2], dtype=np.uint8)
                points = np.array(
                    [
                        [
                            int(max(0.0, min(1.0, float(px))) * (crop.shape[1] - 1)),
                            int(max(0.0, min(1.0, float(py))) * (crop.shape[0] - 1)),
                        ]
                        for px, py in shape_points
                    ],
                    dtype=np.int32,
                )
                if len(points) >= 3:
                    cv2.fillPoly(mask, [points], 1)
                    cyan = (cyan & mask).astype(np.uint8)
            except Exception as exc:
                print(f"Could not apply {field_key} field shape mask: {exc}", flush=True)
        cyan = cv2.morphologyEx(cyan, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))
        cyan = cv2.morphologyEx(cyan, cv2.MORPH_CLOSE, np.ones((3, 3), np.uint8), iterations=1)
        count, _labels, stats, centroids = cv2.connectedComponentsWithStats(cyan, 8)
        field_limits = cfg.get("ai_field_component_limits", {}) or {}
        field_limit = field_limits.get(field_key, {}) if isinstance(field_limits, dict) else {}
        min_area = int(field_limit.get("min_area", cfg.get("ai_min_cyan_area", 10)))
        max_area = int(field_limit.get("max_area", cfg.get("ai_max_cyan_area", 2200)))
        min_w = int(field_limit.get("min_width", cfg.get("ai_min_width", 3)))
        min_h = int(field_limit.get("min_height", cfg.get("ai_min_height", 3)))
        max_w = int(field_limit.get("max_width", cfg.get("ai_max_width", 90)))
        max_h = int(field_limit.get("max_height", cfg.get("ai_max_height", 90)))
        min_aspect = float(field_limit.get("min_aspect", cfg.get("ai_min_aspect", 0.15)))
        max_aspect = float(field_limit.get("max_aspect", cfg.get("ai_max_aspect", 6.0)))
        min_fill_ratio = field_limit.get("min_fill_ratio")
        max_fill_ratio = field_limit.get("max_fill_ratio")
        min_center_x_ratio = field_limit.get("min_center_x_ratio")
        min_center_y_ratio = field_limit.get("min_center_y_ratio")
        max_center_x_ratio = field_limit.get("max_center_x_ratio")
        min_score = float(field_limit.get("min_score", cfg.get("ai_min_score", 65.0)))
        min_context_signal = int(field_limit.get("min_context_signal", cfg.get("ai_min_context_signal", 130)))
        min_component_s_mean = float(cfg.get("ai_min_component_s_mean", 50.0))
        min_component_blue_red_mean = float(cfg.get("ai_min_component_blue_red_mean", 18.0))
        reject_edge_touch = bool(cfg.get("ai_reject_edge_touch", True))
        edge_margin = int(cfg.get("ai_edge_margin_px", 6))
        edge_reject_min_area = int(cfg.get("ai_edge_reject_min_area", 80))
        ignore_bottom_fields = {
            str(name).strip().lower().replace(" ", "").replace("_", "").replace("-", "")
            for name in (cfg.get("ai_ignore_bottom_band_fields", []) or [])
        }
        ignore_bottom_from = float(cfg.get("ai_ignore_bottom_band_from", 0.82))
        bottom_noise_max_height = int(cfg.get("ai_bottom_band_noise_max_height", 18))
        bottom_noise_min_aspect = float(cfg.get("ai_bottom_band_noise_min_aspect", 2.0))
        shape_filter_enabled = bool(cfg.get("ai_shape_filter_enabled", True))
        min_compactness = float(cfg.get("ai_min_compactness", 0.055))
        max_major_minor_ratio = float(cfg.get("ai_max_major_minor_ratio", 5.0))
        min_core_area = int(cfg.get("ai_min_core_area", 8))
        shape_score_weight = float(cfg.get("ai_shape_score_weight", 80.0))
        best = None
        rejects: dict[str, int] = {}

        def reject(reason: str) -> None:
            rejects[reason] = rejects.get(reason, 0) + 1

        for idx in range(1, count):
            area = int(stats[idx, cv2.CC_STAT_AREA])
            bx = int(stats[idx, cv2.CC_STAT_LEFT])
            by = int(stats[idx, cv2.CC_STAT_TOP])
            bw = int(stats[idx, cv2.CC_STAT_WIDTH])
            bh = int(stats[idx, cv2.CC_STAT_HEIGHT])
            ccx, ccy = centroids[idx]
            if min_center_x_ratio is not None and float(ccx) < crop.shape[1] * float(min_center_x_ratio):
                reject("left_of_field_roi")
                continue
            if min_center_y_ratio is not None and float(ccy) < crop.shape[0] * float(min_center_y_ratio):
                reject("above_field_roi")
                continue
            if max_center_x_ratio is not None and float(ccx) > crop.shape[1] * float(max_center_x_ratio):
                reject("right_of_field_roi")
                continue
            if area < min_area or area > max_area or bw < min_w or bh < min_h:
                reject("size")
                continue
            if bw > max_w or bh > max_h:
                reject("bbox_too_large")
                continue
            touches_edge = (
                bx <= edge_margin
                or by <= edge_margin
                or bx + bw >= crop.shape[1] - edge_margin
                or by + bh >= crop.shape[0] - edge_margin
            )
            if reject_edge_touch and touches_edge and (area >= edge_reject_min_area or bw <= 2 or bh <= 2):
                reject("edge_touch")
                continue
            aspect = bw / max(1, bh)
            fill_ratio = area / max(1, bw * bh)
            if aspect < min_aspect or aspect > max_aspect:
                reject("aspect")
                continue
            if min_fill_ratio is not None and fill_ratio < float(min_fill_ratio):
                reject("fill_low")
                continue
            if max_fill_ratio is not None and fill_ratio > float(max_fill_ratio):
                reject("fill_high")
                continue
            cc_mask = _labels[by:by + bh, bx:bx + bw] == idx
            compactness = 0.0
            major_minor_ratio = 1.0
            core_area = 0
            if shape_filter_enabled:
                cc_u8 = cc_mask.astype(np.uint8)
                contours, _hier = cv2.findContours(cc_u8 * 255, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
                if contours:
                    contour = max(contours, key=cv2.contourArea)
                    perimeter = float(cv2.arcLength(contour, True))
                    if perimeter > 0:
                        compactness = float(4.0 * math.pi * area / (perimeter * perimeter))
                    points = cv2.findNonZero(cc_u8)
                    if points is not None and len(points) >= 5:
                        (_center, (rw, rh), _angle) = cv2.minAreaRect(points)
                        major = max(float(rw), float(rh), 1.0)
                        minor = max(min(float(rw), float(rh)), 1.0)
                        major_minor_ratio = major / minor
                core_area = int(np.count_nonzero(cv2.erode(cc_u8, np.ones((2, 2), np.uint8), iterations=1)))
                if compactness < min_compactness:
                    reject("line_like")
                    continue
                if major_minor_ratio > max_major_minor_ratio:
                    reject("too_elongated")
                    continue
                if core_area < min_core_area:
                    reject("no_core_body")
                    continue
            cc_s = s_chan[by:by + bh, bx:bx + bw][cc_mask]
            cc_b = b_chan[by:by + bh, bx:bx + bw][cc_mask].astype(np.int16)
            cc_r = r_chan[by:by + bh, bx:bx + bw][cc_mask].astype(np.int16)
            if cc_s.size == 0:
                reject("empty_component")
                continue
            if float(np.mean(cc_s)) < min_component_s_mean:
                reject("low_saturation")
                continue
            if float(np.mean(cc_b - cc_r)) < min_component_blue_red_mean:
                reject("weak_blue_red")
                continue
            bottom_band_candidate = field_key in ignore_bottom_fields and (by + bh * 0.5) >= crop.shape[0] * ignore_bottom_from
            # Mountain Top has real Vicious pieces very low in the ROI. Only reject
            # bottom-band noise when it looks like a flat/long field edge, not a
            # compact body fragment.
            if bottom_band_candidate and bh <= bottom_noise_max_height and aspect >= bottom_noise_min_aspect:
                reject("bottom_band_noise")
                continue
            pad = int(cfg.get("ai_context_pad", 28))
            cx1 = max(0, bx - pad)
            cy1 = max(0, by - pad)
            cx2 = min(crop.shape[1], bx + bw + pad)
            cy2 = min(crop.shape[0], by + bh + pad)
            ctx_hsv = hsv[cy1:cy2, cx1:cx2]
            ctx_rgb = crop[cy1:cy2, cx1:cx2]
            _ch, cs, cv = cv2.split(ctx_hsv)
            cr, cg, cb = ctx_rgb[:, :, 0], ctx_rgb[:, :, 1], ctx_rgb[:, :, 2]
            dark = cv <= int(cfg.get("ai_dark_v_max", 80))
            pale_blue = (
                (cb.astype(np.int16) >= cr.astype(np.int16) + int(cfg.get("ai_blue_over_red_min", 8)))
                & (cb >= int(cfg.get("ai_pale_blue_b_min", 90)))
                & (cs <= int(cfg.get("ai_pale_blue_s_max", 130)))
            )
            bright_cyan = (ctx_hsv[:, :, 0] >= 78) & (ctx_hsv[:, :, 0] <= 112) & (cs >= 35) & (cv >= 80)
            dark_area = int(np.count_nonzero(dark))
            pale_area = int(np.count_nonzero(pale_blue))
            bright_area = int(np.count_nonzero(bright_cyan))
            if max(pale_area, bright_area) < min_context_signal:
                reject("weak_context")
                continue
            # Dark background is common under fields and around player tools, so it
            # cannot be positive evidence by itself. Favor compact cyan/pale shapes.
            shape_bonus = min(1.0, compactness * 2.0) * shape_score_weight + min(core_area, 80) * 0.45
            score = area + min(pale_area, 500) * 0.10 + min(bright_area, 500) * 0.18 + shape_bonus
            if best is None or score > best["score"]:
                best = {
                    "score": float(score),
                    "area": area,
                    "dark": dark_area,
                    "pale": pale_area,
                    "bright": bright_area,
                    "x": x1 + int(ccx),
                    "y": y1 + int(ccy),
                    "w": bw,
                    "h": bh,
                    "compactness": compactness,
                    "major_minor_ratio": major_minor_ratio,
                    "core_area": core_area,
                }
        found = best is not None and best["score"] >= min_score
        reject_text = ",".join(f"{name}:{value}" for name, value in sorted(rejects.items()))
        if best is None:
            print(f"vicious AI {field}: not found roi=({x1},{y1},{x2},{y2}) rejects={reject_text}", flush=True)
        else:
            print(
                f"vicious AI {field}: found={found} score={best['score']:.1f}/{min_score:.1f} "
                f"x={best['x']} y={best['y']} cyan={best['area']} size={best['w']}x{best['h']} "
                f"shape={best['compactness']:.3f} elong={best['major_minor_ratio']:.2f} core={best['core_area']} "
                f"dark={best['dark']} pale={best['pale']} bright={best['bright']} roi=({x1},{y1},{x2},{y2}) "
                f"rejects={reject_text}",
                flush=True,
            )
        if bool(cfg.get("ai_debug_save", False)):
            try:
                debug_dir = self.cfg.base_dir / "debug_vicious_ai"
                debug_dir.mkdir(exist_ok=True)
                stamp = int(time.time() * 1000)
                status = "found1" if found else "found0"
                if bool(cfg.get("ai_debug_save_full_window", False)):
                    self.roblox_client_shot().save(debug_dir / f"{field}_{status}_{stamp}_window.png")
                else:
                    Image.fromarray(crop).save(debug_dir / f"{field}_{status}_{stamp}_crop.png")
                if bool(cfg.get("ai_debug_save_mask", False)):
                    Image.fromarray((cyan * 255).astype(np.uint8)).save(debug_dir / f"{field}_{status}_{stamp}_mask.png")
            except Exception as exc:
                print(f"Could not save vicious AI debug crop: {exc}", flush=True)
        return found

    def vicious_field_image_visible(self, field: str, screenshot: Image.Image | None = None) -> bool:
        if self.vicious_ai_visible(field, screenshot=screenshot):
            return True
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if not bool(cfg.get("field_image_template_fallback", False)):
            return False
        paths = self.field_image_candidates(field)
        if not paths:
            print(f"vicious image {field}: no template in {self.vic_find_dir()}", flush=True)
            return False
        scales = cfg.get("field_image_scales", [0.70, 0.80, 0.90, 1.0, 1.10, 1.20, 1.35])
        threshold = float(cfg.get("field_image_threshold", 0.72))
        source = str(cfg.get("field_image_source", "roblox") or "roblox")
        color = bool(cfg.get("field_image_color_match", True))
        path, score, x, y = self.best_external_template_match(paths, scales=scales, source=source, color=color)
        if path is not None:
            print(f"vicious image {field}: {path.name} score={score:.3f} x={x} y={y}", flush=True)
        return score >= threshold

    def white_mask_template(self, name: str):
        if name in self._white_mask_template_cache:
            return self._white_mask_template_cache[name]
        path = self.template_dir / name
        if not path.exists() or cv2 is None or np is None:
            self._white_mask_template_cache[name] = None
            return None
        try:
            rgba = np.array(Image.open(path).convert("RGBA"))
        except Exception:
            self._white_mask_template_cache[name] = None
            return None
        alpha = (rgba[:, :, 3] > 0).astype(np.uint8) * 255
        self._white_mask_template_cache[name] = alpha
        return alpha

    def roblox_window_rect(self) -> tuple[int, int, int, int] | None:
        try:
            wins = [w for w in gw.getWindowsWithTitle("Roblox") if w.width > 100 and w.height > 100]
        except Exception:
            return None
        if not wins:
            return None
        win = wins[0]
        return win.left, win.top, win.width, win.height

    def natro_prompt_bounds(self) -> tuple[int, int, int, int]:
        screen_w, screen_h = self.screen.size()
        rect = self.roblox_window_rect()
        if rect is None:
            left, top, width, height = 0, 0, screen_w, screen_h
        else:
            left, top, width, height = rect
        cfg = self.cfg.get("hive", {}) or {}
        crop_w = int(cfg.get("natro_prompt_crop_width", 900))
        crop_h = int(cfg.get("natro_prompt_crop_height", 210))
        offset_y = int(cfg.get("natro_prompt_offset_y", 28))
        center_x = left + width // 2
        x1 = max(0, center_x - crop_w // 2)
        y1 = max(0, top + offset_y)
        return x1, y1, min(screen_w, x1 + crop_w), min(screen_h, y1 + crop_h)

    def natro_white_text_match(
        self,
        names: Iterable[str],
        threshold: float,
        log: bool = True,
    ) -> tuple[str | None, float, int, int]:
        if cv2 is None or np is None:
            return None, 0.0, 0, 0
        x1, y1, x2, y2 = self.natro_prompt_bounds()
        crop = self.screen.shot_box_bgr(x1, y1, x2 - x1, y2 - y1)
        b, g, r = cv2.split(crop)
        max_ch = np.maximum(np.maximum(r, g), b)
        min_ch = np.minimum(np.minimum(r, g), b)
        white = ((min_ch >= 220) & ((max_ch - min_ch) <= 38)).astype(np.uint8) * 255
        best_name = None
        best_score = 0.0
        best_x = 0
        best_y = 0
        for name in names:
            template = self.white_mask_template(name)
            if template is None:
                continue
            th, tw = template.shape[:2]
            if th > white.shape[0] or tw > white.shape[1]:
                continue
            result = cv2.matchTemplate(white, template, cv2.TM_CCORR_NORMED)
            result = np.nan_to_num(result, nan=0.0, posinf=0.0, neginf=0.0)
            _, max_val, _, max_loc = cv2.minMaxLoc(result)
            if max_val > best_score:
                best_name = name
                best_score = float(max_val)
                best_x = x1 + int(max_loc[0])
                best_y = y1 + int(max_loc[1])
        if log and best_name is not None:
            print(f"Natro prompt scan {best_name}: score={best_score:.3f} x={best_x} y={best_y}", flush=True)
        if best_score < threshold:
            return None, best_score, best_x, best_y
        return best_name, best_score, best_x, best_y

    def revolution_template(self, name: str):
        if name in self._rgba_template_cache:
            return self._rgba_template_cache[name]
        path = self.template_dir / name
        if not path.exists() or np is None:
            self._rgba_template_cache[name] = None
            return None
        try:
            rgba = np.array(Image.open(path).convert("RGBA"))
        except Exception:
            self._rgba_template_cache[name] = None
            return None
        ys, xs = np.nonzero(rgba[:, :, 3] > 0)
        colors = rgba[ys, xs, :3].astype(np.int16)
        data = (ys.astype(np.int32), xs.astype(np.int32), colors)
        self._rgba_template_cache[name] = data
        return data

    def revolution_search(
        self,
        names: Iterable[str],
        variance: int,
        bounds: tuple[int, int, int, int] | None = None,
    ) -> tuple[str, int, int] | None:
        if np is None:
            return None
        haystack = np.array(self.screen.shot().convert("RGB")).astype(np.int16)
        height, width = haystack.shape[:2]
        if bounds is None:
            x1, y1, x2, y2 = 0, 0, width, height
        else:
            x1, y1, x2, y2 = bounds
            if x2 == 0:
                x2 = width
            if y2 == 0:
                y2 = height
            x1, y1 = max(0, x1), max(0, y1)
            x2, y2 = min(width, x2), min(height, y2)
        for name in names:
            template = self.revolution_template(name)
            if template is None:
                continue
            ys, xs, colors = template
            if len(xs) == 0:
                continue
            tw = int(xs.max()) + 1
            th = int(ys.max()) + 1
            max_x = x2 - tw
            max_y = y2 - th
            if max_x < x1 or max_y < y1:
                continue
            for y in range(y1, max_y + 1):
                for x in range(x1, max_x + 1):
                    sample = haystack[y + ys, x + xs]
                    if np.all(np.abs(sample - colors) <= variance):
                        print(f"revolution image {name} found at x={x} y={y} variance={variance}", flush=True)
                        return name, x, y
            print(f"revolution image {name} not found in {x1},{y1},{x2},{y2}", flush=True)
        return None

    def honey_offset(self) -> tuple[int, int] | None:
        cached, cached_at = self._honey_offset_cache
        ttl = float(self.cfg.get("hive.honey_offset_cache_seconds", 0.5))
        if time.time() - cached_at < ttl:
            return cached

        img = self.screen.shot()
        top_limit = int(img.size[1] * float(self.cfg.get("hive.honey_offset_top_ratio", 0.35)))
        top_limit = max(150, min(img.size[1], top_limit))
        found = self.revolution_search(["tophoney.png"], variance=5, bounds=(0, 0, 0, top_limit))
        if found is None:
            scales = self.cfg.get("hive.honey_offset_scales", [0.8, 0.9, 1.0, 1.1, 1.25, 1.5, 1.75, 2.0])
            threshold = float(self.cfg.get("hive.honey_offset_threshold", 0.70))
            name, score, x, y = self.best_template_match(
                ["tophoney.png"],
                scales=scales,
                masked=True,
                bounds=(0, 0, 0, top_limit),
            )
            if name is not None:
                print(f"honey offset fallback {name}: {score:.3f} at x={x} y={y}", flush=True)
            if score < threshold:
                self._honey_offset_cache = (None, time.time())
                return None
            result = (x, y)
            self._honey_offset_cache = (result, time.time())
            return result
        _name, x, y = found
        result = (x, y)
        self._honey_offset_cache = (result, time.time())
        return result

    def revolution_hive_prompt(self, claim_only: bool = False) -> str | None:
        if self.claim_hive_blue_prompt_visible():
            return "claimhive.png"
        offset = self.honey_offset()
        if offset is None:
            print("revolution honey offset not found; trying direct hive prompt scan", flush=True)
            return self.revolution_hive_prompt_anywhere(claim_only=claim_only)
        hx, hy = offset
        if claim_only:
            names = ["claimhive.png"]
            variance = 1
            right = hx + 500
        else:
            names = ["claimhive.png", "sendtrade.png", "tradelocked.png", "tradedisabled.png"]
            variance = 0
            right = hx + 600
        bounds = (hx + 110, 0, right, hy + 23)
        found = self.revolution_search(names, variance=variance, bounds=bounds)
        if found:
            return found[0]
        return self.revolution_hive_prompt_anywhere(claim_only=claim_only)

    def revolution_hive_prompt_anywhere(self, claim_only: bool = False) -> str | None:
        names = ["claimhive.png"] if claim_only else [
            "claimhive.png",
            "sendtrade.png",
            "tradelocked.png",
            "tradedisabled.png",
        ]
        img = self.screen.shot()
        top_ratio = float(self.cfg.get("hive.prompt_fallback_top_ratio", 0.55))
        bounds = (0, 0, img.size[0], int(img.size[1] * top_ratio))
        scales = self.cfg.get("hive.prompt_fallback_scales", [0.75, 0.9, 1.0, 1.1, 1.25, 1.5, 1.75, 2.0, 2.5])
        threshold = float(self.cfg.get("hive.prompt_fallback_threshold", 0.68))
        name, score, x, y = self.best_template_match(names, scales=scales, masked=True, bounds=bounds)
        if name is not None:
            print(f"hive prompt fallback {name}: {score:.3f} at x={x} y={y}", flush=True)
        if score < threshold or name is None:
            return None
        return name.split("@", 1)[0]

    def claim_hive_blue_prompt_visible(self) -> bool:
        return self.claim_hive_blue_prompt_state() == "full"

    def claim_hive_blue_prompt_partial(self) -> bool:
        return self.claim_hive_blue_prompt_state(log=False) in {"partial", "full"}

    def claim_hive_blue_prompt_state(self, log: bool = True) -> str | None:
        if cv2 is None or np is None:
            return None
        width, height = self.screen.size()
        top = int(height * float(self.cfg.get("hive.blue_prompt_top_ratio", 0.06)))
        bottom = int(height * float(self.cfg.get("hive.blue_prompt_bottom_ratio", 0.22)))
        left = int(width * float(self.cfg.get("hive.blue_prompt_left_ratio", 0.30)))
        right = int(width * float(self.cfg.get("hive.blue_prompt_right_ratio", 0.70)))
        crop = self.screen.shot_box_bgr(left, top, right - left, bottom - top)
        hsv = cv2.cvtColor(crop, cv2.COLOR_BGR2HSV)
        lower = np.array(self.cfg.get("hive.blue_prompt_hsv_lower", [95, 45, 80]), dtype=np.uint8)
        upper = np.array(self.cfg.get("hive.blue_prompt_hsv_upper", [120, 255, 255]), dtype=np.uint8)
        mask = cv2.inRange(hsv, lower, upper)
        ys, xs = np.nonzero(mask)
        area = int(xs.size)
        min_area = int(self.cfg.get("hive.blue_prompt_min_area", 3000))
        partial_area = int(self.cfg.get("hive.blue_prompt_partial_min_area", 650))
        if area < partial_area:
            return None
        min_x = int(xs.min())
        max_x = int(xs.max())
        min_y = int(ys.min())
        max_y = int(ys.max())
        w = max_x - min_x + 1
        h = max_y - min_y + 1
        if area < min_area:
            return "partial"
        min_width = int(width * float(self.cfg.get("hive.blue_prompt_min_width_ratio", 0.12)))
        max_width = int(width * float(self.cfg.get("hive.blue_prompt_max_width_ratio", 0.35)))
        min_height = int(height * float(self.cfg.get("hive.blue_prompt_min_height_ratio", 0.035)))
        max_height = int(height * float(self.cfg.get("hive.blue_prompt_max_height_ratio", 0.11)))
        if w < min_width or w > max_width or h < min_height or h > max_height:
            return "partial"
        ratio = w / max(1, h)
        if 3.0 <= ratio <= 10.0:
            cx = int((min_x + max_x) / 2)
            cy = int((min_y + max_y) / 2)
            if log:
                print(f"blue claim prompt found x={left + cx} y={top + cy} w={w} h={h} area={area}", flush=True)
            return "full"
        return "partial"

    def template_found(
        self,
        names: Iterable[str],
        threshold: float = 0.86,
        scales: Iterable[float] | None = None,
        masked: bool = True,
    ) -> bool:
        best_name, best_score = self.best_template_score(names, scales=scales, masked=masked)
        if best_name is not None:
            print(f"template score {best_name}: {best_score:.3f}", flush=True)
        return best_score >= threshold

    def active_speed_multiplier(self, force: bool = False) -> float:
        multiplier, _flat_bonus = self.active_speed_adjustment(force=force)
        return multiplier

    def active_speed_adjustment(
        self,
        force: bool = False,
        speed_image: Image.Image | None = None,
    ) -> tuple[float, float]:
        cfg = self.cfg.get("speed_buffs", {}) or {}
        if not force and not bool(cfg.get("enabled", False)):
            return 1.0, 0.0
        now = time.time()
        if not force:
            cache_seconds = float(cfg.get("cache_seconds", 0.35))
            cached_adjustment, cached_at = self._speed_multiplier_cache
            if now - cached_at < cache_seconds:
                return cached_adjustment

        buffs = [] if bool(cfg.get("only_natro_haste", False)) else (cfg.get("buffs", []) or [])
        global_threshold = float(cfg.get("threshold", 0.84))
        global_scales = cfg.get("scales", [0.85, 0.95, 1.0, 1.05, 1.15])
        global_bounds = cfg.get("bounds")
        combine = str(cfg.get("combine", "multiply")).lower()
        flat_combine = str(cfg.get("flat_combine", "sum")).lower()
        max_multiplier = float(cfg.get("max_multiplier", 5.0))
        max_flat_bonus = float(cfg.get("max_flat_bonus", 120.0))
        log = bool(cfg.get("log", False))
        debug_lines: list[str] = []
        best_scores: list[tuple[float, str, str | None]] = []
        source_name = str(cfg.get("source", "roblox"))
        if source_name == "roblox" and self.roblox_window_rect() is None:
            self._last_speed_detection_lines = ["source: roblox window not found", "detected: none"]
            return 1.0, 0.0
        debug_lines.append(f"source: {source_name}")
        found_multipliers: list[tuple[str, float]] = []
        found_flat_bonuses: list[tuple[str, float]] = []

        if speed_image is None:
            speed_image = self.speed_buff_roi_image(cfg)

        natro_multiplier, natro_lines = self.natro_haste_speed_multiplier(speed_image)
        debug_lines.extend(natro_lines)
        if natro_multiplier > 1.0:
            found_multipliers.append(("natro_haste", natro_multiplier))

        for buff in buffs:
            if not isinstance(buff, dict):
                continue
            if not bool(buff.get("enabled", True)):
                continue
            templates = buff.get("templates", []) or []
            if isinstance(templates, str):
                templates = [templates]
            if not templates:
                continue
            threshold = float(buff.get("threshold", global_threshold))
            scales = buff.get("scales", global_scales)
            bounds = buff.get("bounds", global_bounds)
            if isinstance(bounds, list) and len(bounds) == 4:
                bounds = tuple(int(value) for value in bounds)
            elif not isinstance(bounds, tuple):
                bounds = None
            if speed_image is not None and str(buff.get("source", source_name)) == source_name:
                name, score, _rect = self.best_template_match_in_image(
                    speed_image,
                    templates,
                    scales=scales,
                    masked=bool(buff.get("masked", True)),
                    color=bool(buff.get("color", cfg.get("color", False))),
                )
            else:
                name, score, _x, _y = self.best_template_match(
                    templates,
                    scales=scales,
                    masked=bool(buff.get("masked", True)),
                    bounds=bounds,
                    source=str(buff.get("source", source_name)),
                    color=bool(buff.get("color", cfg.get("color", False))),
                )
            label = str(buff.get("name", name or "speed_buff"))
            best_scores.append((score, label, name))
            detected_now = score >= threshold
            hold_seconds = max(0.0, float(buff.get("hold_seconds", 0.0)))
            if detected_now:
                self._speed_buff_seen_at[label] = now
            last_seen = self._speed_buff_seen_at.get(label, 0.0)
            held = not detected_now and hold_seconds > 0.0 and now - last_seen <= hold_seconds
            state = "detected" if detected_now else (f"held {now - last_seen:.1f}s" if held else "absent")
            debug_lines.append(
                f"{label}: score={score:.3f}, threshold={threshold:.3f}, best={name}, state={state}"
            )
            if log:
                print(f"speed buff {label}: score={score:.3f} threshold={threshold:.3f}", flush=True)
            if detected_now or held:
                multiplier_value = max(0.1, float(buff.get("multiplier", 1.0)))
                flat_value = max(0.0, float(buff.get("flat_bonus", buff.get("add_speed", 0.0))))
                if multiplier_value != 1.0:
                    found_multipliers.append((label, multiplier_value))
                if flat_value > 0.0:
                    found_flat_bonuses.append((label, flat_value))

        if not found_multipliers:
            multiplier = 1.0
        elif combine == "max":
            multiplier = max(value for _label, value in found_multipliers)
        else:
            multiplier = 1.0
            for _label, value in found_multipliers:
                multiplier *= value

        if not found_flat_bonuses:
            flat_bonus = 0.0
        elif flat_combine == "max":
            flat_bonus = max(value for _label, value in found_flat_bonuses)
        else:
            flat_bonus = sum(value for _label, value in found_flat_bonuses)

        multiplier = min(max_multiplier, max(0.1, multiplier))
        flat_bonus = min(max_flat_bonus, max(0.0, flat_bonus))
        adjustment = (multiplier, flat_bonus)
        if not force:
            self._speed_multiplier_cache = (adjustment, now)
        if log and (found_multipliers or found_flat_bonuses):
            multiplier_detail = ", ".join(f"{label}=x{value:.2f}" for label, value in found_multipliers)
            flat_detail = ", ".join(f"{label}=+{value:.1f}" for label, value in found_flat_bonuses)
            detail = "; ".join(part for part in (multiplier_detail, flat_detail) if part)
            print(f"active speed adjustment x{multiplier:.2f} +{flat_bonus:.1f}: {detail}", flush=True)
        if found_multipliers or found_flat_bonuses:
            multiplier_detail = ", ".join(f"{label}=x{value:.2f}" for label, value in found_multipliers)
            flat_detail = ", ".join(f"{label}=+{value:.1f}" for label, value in found_flat_bonuses)
            detail = "; ".join(part for part in (multiplier_detail, flat_detail) if part)
            debug_lines.append(f"detected: x{multiplier:.2f} +{flat_bonus:.1f} ({detail})")
        else:
            debug_lines.append("detected: none")
        if best_scores:
            top_scores = sorted(best_scores, reverse=True)[:5]
            debug_lines.append(
                "best scores: "
                + ", ".join(
                    f"{label}={score:.3f} ({name or 'no_template'})"
                    for score, label, name in top_scores
                )
            )
        self._last_speed_detection_lines = debug_lines
        return adjustment

    def blue_loading_visible(self) -> bool:
        if not self.cfg.get("load_detection.blue_color_detection", True):
            return False
        ratio = self.blue_loading_color_ratio()
        min_ratio = float(self.cfg.get("load_detection.blue_min_ratio", 0.03))
        print(f"blue lower-half ratio {ratio:.4f} threshold={min_ratio:.4f}", flush=True)
        if ratio >= min_ratio:
            return True
        if not self.cfg.get("load_detection.blue_template_fallback", False):
            return False
        threshold = float(self.cfg.get("load_detection.texture_threshold", 0.90))
        template_min_ratio = float(self.cfg.get("load_detection.blue_template_min_ratio", 0.12))
        names = self.cfg.get("load_detection.blue_loading_templates", []) or []
        name, score = self.best_template_score(names)
        if name is not None:
            print(f"blue loading score {score:.3f} template_min_ratio={template_min_ratio:.4f}", flush=True)
        if ratio < template_min_ratio:
            return False
        return score >= threshold

    def loading_roi_image(self) -> Image.Image:
        img = self.roblox_shot()
        width, height = img.size
        crop_top = int(height * float(self.cfg.get("load_detection.blue_screen_top_ratio", 0.45)))
        crop_bottom = int(height * float(self.cfg.get("load_detection.blue_screen_bottom_ratio", 0.88)))
        crop_bottom = max(crop_top + 1, min(height, crop_bottom))
        return img.crop((0, crop_top, width, crop_bottom))

    def blue_ratio_for_image(self, img: Image.Image) -> float:
        # Downsample for speed; color ratio is scale-invariant enough for this loading screen.
        img = img.resize((240, 135))
        pixels = img.load()
        target = self.cfg.get("load_detection.blue_rgb", [37, 91, 164])
        tr, tg, tb = [int(v) for v in target[:3]]
        tolerance = int(self.cfg.get("load_detection.blue_tolerance", 35))
        matches = 0
        total = img.size[0] * img.size[1]
        for y in range(img.size[1]):
            for x in range(img.size[0]):
                r, g, b = pixels[x, y]
                if abs(r - tr) <= tolerance and abs(g - tg) <= tolerance and abs(b - tb) <= tolerance:
                    matches += 1
        return matches / total if total else 0.0

    def blue_loading_color_ratio(self) -> float:
        return self.blue_ratio_for_image(self.loading_roi_image())

    def loaded_screen_visible(self) -> bool:
        return self.loaded_hud_marker_visible()

    def loaded_hud_marker_visible(self) -> bool:
        img = self.roblox_shot()
        width, height = img.size
        roi = self.cfg.get("load_detection.loaded_marker_roi", {}) or {}
        left = int(width * float(roi.get("left", 0.0)))
        top = int(height * float(roi.get("top", 0.055)))
        right = int(width * float(roi.get("right", 0.18)))
        bottom = int(height * float(roi.get("bottom", 0.16)))
        right = max(left + 1, min(width, right))
        bottom = max(top + 1, min(height, bottom))
        small = img.crop((left, top, right, bottom)).resize((240, 100))
        pixels = small.load()
        matches = 0
        total = small.size[0] * small.size[1]
        for y in range(small.size[1]):
            for x in range(small.size[0]):
                r, g, b = pixels[x, y]
                if r >= 175 and 85 <= g <= 215 and b <= 95 and r > g + 18 and g > b + 25:
                    matches += 1
        ratio = matches / total if total else 0.0
        threshold = float(self.cfg.get("load_detection.loaded_marker_min_ratio", 0.010))
        top_ratio = self.loaded_top_bar_ratio(img)
        top_threshold = float(self.cfg.get("load_detection.loaded_top_bar_min_ratio", 0.045))
        print(
            f"loaded HUD check orange={ratio:.4f}/{threshold:.4f} "
            f"topbar={top_ratio:.4f}/{top_threshold:.4f}",
            flush=True,
        )
        return ratio >= threshold or top_ratio >= top_threshold

    def loaded_top_bar_ratio(self, img: Image.Image) -> float:
        width, height = img.size
        roi = self.cfg.get("load_detection.loaded_top_bar_roi", {}) or {}
        left = int(width * float(roi.get("left", 0.30)))
        top = int(height * float(roi.get("top", 0.035)))
        right = int(width * float(roi.get("right", 0.70)))
        bottom = int(height * float(roi.get("bottom", 0.105)))
        right = max(left + 1, min(width, right))
        bottom = max(top + 1, min(height, bottom))
        small = img.crop((left, top, right, bottom)).resize((240, 60))
        pixels = small.load()
        matches = 0
        total = small.size[0] * small.size[1]
        for y in range(small.size[1]):
            for x in range(small.size[0]):
                r, g, b = pixels[x, y]
                bright_bar = r >= 215 and g >= 215 and b >= 200
                grey_bar = 70 <= r <= 185 and 70 <= g <= 185 and 65 <= b <= 185 and max(r, g, b) - min(r, g, b) <= 35
                if bright_bar or grey_bar:
                    matches += 1
        return matches / total if total else 0.0

    def loaded_texture_visible(self) -> bool:
        return self.loaded_screen_visible()

    def vicious_under_field_visible(self, log: bool = True) -> bool:
        if cv2 is None or np is None:
            return False
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if not bool(cfg.get("under_field_enabled", True)):
            return False
        img = np.array(self.screen.shot().convert("RGB"))
        height, width = img.shape[:2]
        roi_cfg = cfg.get("under_field_roi", {}) or {}
        x1 = int(width * float(roi_cfg.get("left", 0.04)))
        x2 = int(width * float(roi_cfg.get("right", 0.96)))
        y1 = int(height * float(roi_cfg.get("top", 0.34)))
        y2 = int(height * float(roi_cfg.get("bottom", 0.82)))
        x1, y1 = max(0, x1), max(0, y1)
        x2, y2 = min(width, x2), min(height, y2)
        if x2 <= x1 or y2 <= y1:
            return False
        crop = img[y1:y2, x1:x2]
        hsv = cv2.cvtColor(crop, cv2.COLOR_RGB2HSV)
        h_chan, s_chan, v_chan = cv2.split(hsv)
        cyan = (
            (h_chan >= int(cfg.get("under_field_cyan_h_min", 82)))
            & (h_chan <= int(cfg.get("under_field_cyan_h_max", 112)))
            & (s_chan >= int(cfg.get("under_field_cyan_s_min", 35)))
            & (v_chan >= int(cfg.get("under_field_cyan_v_min", 35)))
        ).astype(np.uint8)
        cyan = cv2.morphologyEx(cyan, cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))
        cyan = cv2.morphologyEx(cyan, cv2.MORPH_CLOSE, np.ones((5, 5), np.uint8), iterations=1)
        count, _labels, stats, centroids = cv2.connectedComponentsWithStats(cyan, 8)
        min_area = int(cfg.get("under_field_min_cyan_area", 45))
        max_area = int(cfg.get("under_field_max_cyan_area", 2200))
        min_w = int(cfg.get("under_field_min_width", 6))
        min_h = int(cfg.get("under_field_min_height", 6))
        best = None
        for idx in range(1, count):
            area = int(stats[idx, cv2.CC_STAT_AREA])
            bx = int(stats[idx, cv2.CC_STAT_LEFT])
            by = int(stats[idx, cv2.CC_STAT_TOP])
            bw = int(stats[idx, cv2.CC_STAT_WIDTH])
            bh = int(stats[idx, cv2.CC_STAT_HEIGHT])
            if area < min_area or area > max_area or bw < min_w or bh < min_h:
                continue
            pad = int(cfg.get("under_field_context_pad", 24))
            cx1 = max(0, bx - pad)
            cy1 = max(0, by - pad)
            cx2 = min(crop.shape[1], bx + bw + pad)
            cy2 = min(crop.shape[0], by + bh + pad)
            ctx_hsv = hsv[cy1:cy2, cx1:cx2]
            _ch, cs, cv = cv2.split(ctx_hsv)
            bright = (cv >= int(cfg.get("under_field_bright_v_min", 125))) & (cs <= int(cfg.get("under_field_bright_s_max", 110)))
            dark = cv <= int(cfg.get("under_field_dark_v_max", 65))
            bright_area = int(np.count_nonzero(bright))
            dark_area = int(np.count_nonzero(dark))
            score = area + int(bright_area * 0.25) + int(min(dark_area, 500) * 0.05)
            if best is None or score > best["score"]:
                ccx, ccy = centroids[idx]
                best = {
                    "score": score,
                    "area": area,
                    "bright": bright_area,
                    "dark": dark_area,
                    "x": x1 + int(ccx),
                    "y": y1 + int(ccy),
                    "w": bw,
                    "h": bh,
                }
        found = best is not None
        if log:
            if found:
                print(
                    f"vicious under-field visual found x={best['x']} y={best['y']} "
                    f"cyan_area={best['area']} size={best['w']}x{best['h']} "
                    f"bright={best['bright']} dark={best['dark']} score={best['score']}",
                    flush=True,
                )
            else:
                print("vicious under-field visual not found", flush=True)
        return found

    def vicious_visible(self, field: str) -> bool:
        names = self.cfg.get(f"vicious_templates.{field}", []) or []
        if names and self.template_found(names, threshold=0.80):
            return True
        if self.vicious_under_field_visible():
            return True
        return self.battle_active()

    def defeated_yellow_banner_visible(self, image: Image.Image, log: bool = False) -> bool:
        self._last_defeated_banner_crop = None
        if np is None or cv2 is None:
            return False
        cfg = self.cfg.get("vicious_detection", {}) or {}
        width, height = image.size
        region = cfg.get("defeated_yellow_banner_region", [0.68, 0.50, 1.0, 0.92])
        try:
            left, top, right, bottom = [float(value) for value in region]
        except Exception:
            left, top, right, bottom = 0.68, 0.50, 1.0, 0.92
        x1 = max(0, min(width - 1, int(width * left)))
        y1 = max(0, min(height - 1, int(height * top)))
        x2 = max(x1 + 1, min(width, int(width * right)))
        y2 = max(y1 + 1, min(height, int(height * bottom)))
        crop = image.crop((x1, y1, x2, y2)).convert("RGB")
        arr = np.array(crop).astype(np.int16)
        r = arr[:, :, 0]
        g = arr[:, :, 1]
        b = arr[:, :, 2]
        yellow = (
            (r >= int(cfg.get("defeated_yellow_r_min", 190)))
            & (g >= int(cfg.get("defeated_yellow_g_min", 145)))
            & (b <= int(cfg.get("defeated_yellow_b_max", 90)))
            & ((r - b) >= int(cfg.get("defeated_yellow_rb_min_delta", 110)))
            & ((g - b) >= int(cfg.get("defeated_yellow_gb_min_delta", 70)))
        ).astype(np.uint8)
        yellow = cv2.morphologyEx(yellow, cv2.MORPH_CLOSE, np.ones((7, 5), np.uint8), iterations=2)
        yellow = cv2.morphologyEx(yellow, cv2.MORPH_OPEN, np.ones((5, 3), np.uint8), iterations=1)
        count, _labels, stats, _centroids = cv2.connectedComponentsWithStats(yellow, 8)
        image_area = max(1, crop.width * crop.height)
        min_area = int(cfg.get("defeated_yellow_min_area", 1200))
        min_width = int(cfg.get("defeated_yellow_min_width", 260))
        max_width = int(cfg.get("defeated_yellow_max_width", 460))
        min_height = int(cfg.get("defeated_yellow_min_height", 16))
        max_height = int(cfg.get("defeated_yellow_max_height", 36))
        min_aspect = float(cfg.get("defeated_yellow_min_aspect", 10.0))
        max_aspect = float(cfg.get("defeated_yellow_max_aspect", 24.0))
        max_area_ratio = float(cfg.get("defeated_yellow_max_area_ratio", 0.16))
        min_right_edge_ratio = float(cfg.get("defeated_yellow_min_right_edge_ratio", 0.92))
        min_text_pixels = int(cfg.get("defeated_yellow_min_text_pixels", 35))
        best: dict[str, float | int] | None = None
        for idx in range(1, count):
            bx, by, bw, bh, area = [int(value) for value in stats[idx]]
            if area < min_area or bw < min_width or bw > max_width or bh < min_height or bh > max_height:
                continue
            aspect = bw / max(1, bh)
            if aspect < min_aspect or aspect > max_aspect:
                continue
            if area / image_area > max_area_ratio:
                continue
            abs_right = x1 + bx + bw
            if abs_right < width * min_right_edge_ratio:
                continue
            candidate = arr[by : by + bh, bx : bx + bw, :]
            cr = candidate[:, :, 0]
            cg = candidate[:, :, 1]
            cb = candidate[:, :, 2]
            dark_text = (cr < 85) & (cg < 85) & (cb < 85)
            red_or_pink_text = (cr > 150) & (cg < 110) & (cb < 150) & ((cr - cg) > 55)
            text_pixels = int(np.count_nonzero(dark_text | red_or_pink_text))
            if text_pixels < min_text_pixels:
                continue
            if best is None or area > int(best["area"]):
                best = {
                    "x": x1 + bx,
                    "y": y1 + by,
                    "w": bw,
                    "h": bh,
                    "area": area,
                    "aspect": aspect,
                    "text": text_pixels,
                }
        if best is not None:
            pad_x = int(cfg.get("defeated_yellow_ocr_pad_x", 8))
            pad_y = int(cfg.get("defeated_yellow_ocr_pad_y", 4))
            crop_box = (
                max(0, int(best["x"]) - pad_x),
                max(0, int(best["y"]) - pad_y),
                min(width, int(best["x"]) + int(best["w"]) + pad_x),
                min(height, int(best["y"]) + int(best["h"]) + pad_y),
            )
            with contextlib.suppress(Exception):
                self._last_defeated_banner_crop = image.crop(crop_box)
            if log or bool(cfg.get("defeated_yellow_banner_log", True)):
                print(
                    "Vicious defeated yellow banner detected "
                    f"x={best['x']} y={best['y']} size={best['w']}x{best['h']} "
                    f"area={best['area']} aspect={float(best['aspect']):.1f} text={best['text']}",
                    flush=True,
                )
            return True
        if log or bool(cfg.get("defeated_yellow_banner_log_misses", False)):
            print("Vicious defeated yellow banner not detected", flush=True)
        return False

    def defeated_yellow_banner_ocr_confirmed(self) -> bool:
        crop = self._last_defeated_banner_crop
        if crop is None:
            return False
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if not self.ensure_tesseract_available():
            print("Vicious defeated OCR confirm unavailable: Tesseract missing.", flush=True)
            return False
        text = self.normalize_ocr_text(
            self.ocr_text_for_regions(
                crop,
                [(0.0, 0.0, 1.0, 1.0)],
                scale=float(cfg.get("defeated_yellow_ocr_scale", 4.0)),
                psm_values=tuple(int(value) for value in cfg.get("defeated_yellow_ocr_psm_values", [7, 6])),
                variant_names=cfg.get("defeated_yellow_ocr_variants", ["gray"]),
            )
        )
        found = self.defeated_phrase_visible_in_text(text)
        if bool(cfg.get("defeated_yellow_ocr_log", True)):
            print(f"Vicious defeated yellow OCR confirmed={found} text={text[:220]!r}", flush=True)
        return found

    def defeated(self) -> bool:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        now = time.monotonic()
        last_found, last_time = self._defeated_message_ocr_cache
        interval = max(0.05, float(cfg.get("defeated_message_poll_seconds", 0.2)))
        if now - last_time < interval:
            return last_found
        image = self.roblox_shot()
        if bool(cfg.get("defeated_yellow_banner_enabled", True)) and self.defeated_yellow_banner_visible(image):
            if bool(cfg.get("defeated_yellow_ocr_confirm_enabled", True)):
                found = self.defeated_yellow_banner_ocr_confirmed()
                self._defeated_message_ocr_cache = (found, time.monotonic())
                return found
            self._defeated_message_ocr_cache = (True, time.monotonic())
            return True
        if bool(cfg.get("defeated_message_ocr_live_enabled", True)) is False:
            self._defeated_message_ocr_cache = (False, time.monotonic())
            return False
        regions = cfg.get(
            "defeated_message_ocr_live_regions",
            [
                [0.0, 0.0, 1.0, 0.28],
                [0.18, 0.0, 0.82, 0.35],
            ],
        )
        debug_enabled = bool(cfg.get("defeated_message_live_debug", False))
        debug_interval = max(0.5, float(cfg.get("defeated_message_live_debug_interval_seconds", 2.0)))
        debug_max = max(0, int(float(cfg.get("defeated_message_live_debug_max_samples", 120))))
        should_debug = (
            debug_enabled
            and self._defeated_live_debug_count < debug_max
            and now - self._defeated_live_debug_last >= debug_interval
        )
        debug_label = ""
        if should_debug:
            self._defeated_live_debug_last = now
            self._defeated_live_debug_count += 1
            debug_label = f"live_defeated_{self._defeated_live_debug_count:03d}"
            try:
                debug_dir = self.cfg.base_dir / "debug_vicious_ocr"
                debug_dir.mkdir(exist_ok=True)
                image.save(debug_dir / f"{int(time.time() * 1000)}_{debug_label}_screen.png")
            except Exception as exc:
                print(f"Vicious defeated OCR debug screenshot save failed: {exc}", flush=True)
        text = self.normalize_ocr_text(
            self.ocr_text_for_regions(
                image,
                regions,
                psm_values=(6, 11),
                variant_names=("gray", "redmask"),
                debug_label=debug_label,
            )
        )
        found = self.defeated_phrase_visible_in_text(text)
        self._defeated_message_ocr_cache = (found, time.monotonic())
        if bool(cfg.get("defeated_message_log", False)) or should_debug:
            suffix = f" debug_sample={self._defeated_live_debug_count}/{debug_max}" if should_debug else ""
            print(f"Vicious defeated OCR visible={found}{suffix} text={text[:300]!r}", flush=True)
        return found

    def vicious_left_red_precheck(self, image: Image.Image) -> tuple[bool, dict[str, object]]:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if not bool(cfg.get("vicious_left_red_precheck_enabled", True)):
            return True, {"enabled": False, "reason": "disabled"}
        width, height = image.size
        region = cfg.get("vicious_left_red_precheck_region", [0.62, 0.78, 1.0, 1.0])
        try:
            left, top, right, bottom = [float(value) for value in region]
        except Exception:
            left, top, right, bottom = 0.62, 0.78, 1.0, 1.0
        box = (
            max(0, min(width - 1, int(width * left))),
            max(0, min(height - 1, int(height * top))),
            max(1, min(width, int(width * right))),
            max(1, min(height, int(height * bottom))),
        )
        if box[2] <= box[0] or box[3] <= box[1]:
            return False, {"enabled": True, "reason": "empty_box", "box": box}
        crop = image.crop(box).convert("RGB")
        arr = np.array(crop) if np is not None else None
        if arr is None:
            return True, {"enabled": True, "reason": "numpy_unavailable", "box": box}
        r = arr[:, :, 0].astype(np.int16)
        g = arr[:, :, 1].astype(np.int16)
        b = arr[:, :, 2].astype(np.int16)
        red_mask = (
            (r >= int(cfg.get("vicious_left_red_min_r", 130)))
            & (g <= int(cfg.get("vicious_left_red_max_g", 95)))
            & (b <= int(cfg.get("vicious_left_red_max_b", 95)))
            & ((r - g) >= int(cfg.get("vicious_left_red_min_rg_delta", 45)))
            & ((r - b) >= int(cfg.get("vicious_left_red_min_rb_delta", 45)))
        )
        red_pixels = int(np.count_nonzero(red_mask))
        total_pixels = int(red_mask.size)
        red_ratio = red_pixels / max(1, total_pixels)
        min_pixels = int(cfg.get("vicious_left_red_min_pixels", 35))
        min_ratio = float(cfg.get("vicious_left_red_min_ratio", 0.00025))
        passed = red_pixels >= min_pixels and red_ratio >= min_ratio
        return passed, {
            "enabled": True,
            "box": box,
            "red_pixels": red_pixels,
            "red_ratio": red_ratio,
            "min_pixels": min_pixels,
            "min_ratio": min_ratio,
        }

    def vicious_left_message_visible(self, screenshot: Image.Image | None = None) -> bool:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        now = time.monotonic()
        if screenshot is None:
            last_found, last_time = self._vicious_left_message_ocr_cache
            interval = max(0.05, float(cfg.get("vicious_left_message_poll_seconds", cfg.get("defeated_message_poll_seconds", 0.2))))
            if now - last_time < interval:
                return last_found
        image = screenshot if screenshot is not None else self.roblox_shot()
        precheck_ok, precheck = self.vicious_left_red_precheck(image)
        log_enabled = bool(cfg.get("vicious_left_precheck_log", False))
        log_interval = max(0.5, float(cfg.get("vicious_left_precheck_log_interval_seconds", 5.0)))
        should_log_precheck = (
            log_enabled
            and (precheck_ok or now - self._vicious_left_precheck_log_last >= log_interval)
        )
        if should_log_precheck:
            self._vicious_left_precheck_log_last = now
            print(
                "Vicious left precheck "
                f"passed={precheck_ok} red_pixels={precheck.get('red_pixels', '?')} "
                f"red_ratio={float(precheck.get('red_ratio', 0.0) or 0.0):.6f} "
                f"box={precheck.get('box', '?')}",
                flush=True,
            )
        if not precheck_ok:
            if screenshot is None:
                self._vicious_left_message_ocr_cache = (False, time.monotonic())
            return False
        regions = cfg.get(
            "vicious_left_message_ocr_regions",
            [
                [0.62, 0.78, 1.0, 1.0],
                [0.72, 0.84, 1.0, 1.0],
            ],
        )
        text = self.normalize_ocr_text(
            self.ocr_text_for_regions(
                image,
                regions,
                scale=float(cfg.get("vicious_left_message_ocr_scale", cfg.get("message_ocr_crop_scale", 4.0))),
                psm_values=tuple(int(value) for value in cfg.get("vicious_left_message_ocr_psm_values", [6, 11])),
                variant_names=cfg.get("vicious_left_message_ocr_variants", ["redmask", "gray"]),
            )
        )
        found = self.vicious_left_phrase_visible_in_text(text)
        if screenshot is None:
            self._vicious_left_message_ocr_cache = (found, time.monotonic())
        if found or bool(cfg.get("vicious_left_message_log", False)):
            print(
                f"Vicious left OCR visible={found} "
                f"precheck_red={precheck.get('red_pixels', '?')} "
                f"text={text[:300]!r}",
                flush=True,
            )
        return found

    def claim_hive_visible(self) -> bool:
        if self.natro_claim_hive_visible():
            return True
        if self.cfg.get("hive.use_revolution_detection", True):
            return self.detector_revolution_claim_hive_visible()
        threshold = float(self.cfg.get("hive.claim_threshold", 0.86))
        scales = self.cfg.get("hive.template_scales", [0.50, 0.60, 0.70, 0.80, 0.90, 1.0, 1.10, 1.20, 1.35, 1.50, 1.75, 2.0, 2.50, 3.0])
        return self.template_found(["claimhive.png"], threshold=threshold, scales=scales, masked=True)

    def any_hive_prompt_visible(self) -> bool:
        if self.claim_hive_blue_prompt_visible():
            return True
        if self.cfg.get("hive.use_revolution_detection", True):
            return self.revolution_hive_prompt(claim_only=False) is not None
        threshold = float(self.cfg.get("hive.claim_threshold", 0.86))
        scales = self.cfg.get("hive.template_scales", [0.50, 0.60, 0.70, 0.80, 0.90, 1.0, 1.10, 1.20, 1.35, 1.50, 1.75, 2.0, 2.50, 3.0])
        return self.template_found(
            ["claimhive.png", "sendtrade.png", "tradedisabled.png", "tradelocked.png"],
            threshold=threshold,
            scales=scales,
            masked=True,
        )

    def detector_revolution_claim_hive_visible(self) -> bool:
        return self.revolution_hive_prompt(claim_only=True) == "claimhive.png"

    def natro_claim_hive_visible(self, log: bool = True) -> bool:
        if self.claim_hive_blue_prompt_visible():
            return True
        threshold = float(self.cfg.get("hive.natro_claim_template_threshold", 0.72))
        name, _score, _x, _y = self.natro_white_text_match(["natro_claimhive.png"], threshold=threshold, log=log)
        return name is not None

    def natro_at_hive_visible(self, log: bool = True) -> bool:
        threshold = float(self.cfg.get("hive.natro_hive_confirm_threshold", 0.70))
        name, _score, _x, _y = self.natro_white_text_match(
            ["natro_makehoney.png", "natro_collectpollen.png"],
            threshold=threshold,
            log=log,
        )
        return name is not None

    def _detect_hive_red_arrow_slots(self, img, cfg: dict) -> tuple[list[tuple[int, int, int, int]], list[dict]]:
        if cv2 is None or np is None:
            return [], []
        height, width = img.shape[:2]
        ratios = cfg.get(
            "empty_hive_red_arrow_slot_x_ratios",
            [0.770, 0.635, 0.500, 0.364, 0.232, 0.095],
        )
        y_top = int(height * float(cfg.get("empty_hive_red_arrow_roi_top_ratio", 0.135)))
        y_bottom = int(height * float(cfg.get("empty_hive_red_arrow_roi_bottom_ratio", 0.305)))
        half_w = int(width * float(cfg.get("empty_hive_red_arrow_roi_half_width_ratio", 0.060)))
        min_area = int(cfg.get("empty_hive_red_arrow_min_area", 180))
        min_ratio = float(cfg.get("empty_hive_red_arrow_min_ratio", 0.006))
        max_total_ratio = float(cfg.get("empty_hive_red_arrow_max_total_ratio", 0.16))
        max_total_area = int(cfg.get("empty_hive_red_arrow_max_total_area", 12000))
        max_component_ratio = float(cfg.get("empty_hive_red_arrow_max_component_ratio", 0.11))
        max_component_area = int(cfg.get("empty_hive_red_arrow_max_component_area", 6500))
        min_width = int(cfg.get("empty_hive_red_arrow_min_width", 16))
        min_height = int(cfg.get("empty_hive_red_arrow_min_height", 8))
        min_line_width_ratio = float(cfg.get("empty_hive_red_arrow_min_line_width_ratio", 0.18))
        min_line_height_ratio = float(cfg.get("empty_hive_red_arrow_min_line_height_ratio", 0.26))
        max_edge_touch_ratio = float(cfg.get("empty_hive_red_arrow_max_edge_touch_ratio", 0.35))
        head_top_ratio = float(cfg.get("empty_hive_red_arrow_head_top_ratio", 0.72))
        head_min_area = int(cfg.get("empty_hive_red_arrow_head_min_area", 500))
        head_min_width = int(cfg.get("empty_hive_red_arrow_head_min_width", 30))
        head_min_height = int(cfg.get("empty_hive_red_arrow_head_min_height", 16))
        head_max_area = int(cfg.get("empty_hive_red_arrow_head_max_area", 1400))
        head_max_width = int(cfg.get("empty_hive_red_arrow_head_max_width", 90))
        head_max_height = int(cfg.get("empty_hive_red_arrow_head_max_height", 60))
        head_min_aspect = float(cfg.get("empty_hive_red_arrow_head_min_aspect", 1.15))
        head_max_aspect = float(cfg.get("empty_hive_red_arrow_head_max_aspect", 4.5))
        line_min_angle = float(cfg.get("empty_hive_red_arrow_line_min_angle", 18.0))
        line_max_angle = float(cfg.get("empty_hive_red_arrow_line_max_angle", 92.0))
        hough_threshold = int(cfg.get("empty_hive_red_arrow_hough_threshold", 35))
        hough_gap = int(cfg.get("empty_hive_red_arrow_hough_max_gap", 8))
        hough_min_length_ratio = float(cfg.get("empty_hive_red_arrow_hough_min_length_ratio", 0.24))
        hough_max_mid_y_ratio = float(cfg.get("empty_hive_red_arrow_hough_max_mid_y_ratio", 0.74))
        hough_max_top_y_ratio = float(cfg.get("empty_hive_red_arrow_hough_max_top_y_ratio", 0.62))
        allow_line_only = bool(cfg.get("empty_hive_red_arrow_allow_line_only", False))
        head_zone_left_ratio = float(cfg.get("empty_hive_red_arrow_head_zone_left_ratio", 0.15))
        head_zone_right_ratio = float(cfg.get("empty_hive_red_arrow_head_zone_right_ratio", 0.82))
        head_zone_top_ratio = float(cfg.get("empty_hive_red_arrow_head_zone_top_ratio", 0.20))
        head_zone_bottom_ratio = float(cfg.get("empty_hive_red_arrow_head_zone_bottom_ratio", 0.66))
        head_zone_min_area = int(cfg.get("empty_hive_red_arrow_head_zone_min_area", 350))
        available: list[tuple[int, int, int, int]] = []
        debug: list[dict] = []
        debug_dir = None
        if bool(cfg.get("empty_hive_red_arrow_debug_save_crops", False)):
            try:
                debug_dir = self.cfg.base_dir / "debug_hive_pads"
                debug_dir.mkdir(exist_ok=True)
            except Exception as exc:
                print(f"Could not prepare hive pad debug folder: {exc}", flush=True)
                debug_dir = None

        for slot, ratio in enumerate(ratios[:6], start=1):
            anchor_x = int(width * float(ratio))
            x1 = max(0, anchor_x - half_w)
            x2 = min(width, anchor_x + half_w)
            y1 = max(0, y_top)
            y2 = min(height, y_bottom)
            roi = img[y1:y2, x1:x2]
            if roi.size == 0:
                debug.append({"slot": slot, "anchor_x": anchor_x, "red_area": 0, "red_ratio": 0.0, "found": False})
                continue
            hsv = cv2.cvtColor(roi, cv2.COLOR_RGB2HSV)
            h_chan = hsv[:, :, 0]
            s_chan = hsv[:, :, 1]
            v_chan = hsv[:, :, 2]
            red = (((h_chan <= 10) | (h_chan >= 168)) & (s_chan >= 70) & (v_chan >= 70)).astype(np.uint8)
            red = cv2.morphologyEx(red, cv2.MORPH_OPEN, np.ones((3, 3), np.uint8))
            red = cv2.morphologyEx(red, cv2.MORPH_CLOSE, np.ones((5, 5), np.uint8), iterations=2)
            line_mask = (red * 255).astype(np.uint8)
            count, _labels, stats, centroids = cv2.connectedComponentsWithStats(red, 8)
            best = None
            roi_h, roi_w = red.shape[:2]
            red_area = int(np.count_nonzero(red))
            red_ratio = float(red_area) / max(1, red.size)
            largest_area = 0
            largest_w = 0
            largest_h = 0
            largest_touch_ratio = 0.0
            for idx in range(1, count):
                comp_area = int(stats[idx, cv2.CC_STAT_AREA])
                comp_x = int(stats[idx, cv2.CC_STAT_LEFT])
                comp_y = int(stats[idx, cv2.CC_STAT_TOP])
                comp_w = int(stats[idx, cv2.CC_STAT_WIDTH])
                comp_h = int(stats[idx, cv2.CC_STAT_HEIGHT])
                if comp_area <= largest_area:
                    continue
                touches = (
                    int(comp_x <= 1)
                    + int(comp_y <= 1)
                    + int(comp_x + comp_w >= roi_w - 2)
                    + int(comp_y + comp_h >= roi_h - 2)
                )
                largest_area = comp_area
                largest_w = comp_w
                largest_h = comp_h
                largest_touch_ratio = touches / 4.0
            largest_ratio = float(largest_area) / max(1, red.size)
            # Real free-slot arrows are thin strokes. Red hive skins make big blobs
            # and curved patches, so reject those before Hough can find a stray line.
            skin_reject = (
                red_ratio > max_total_ratio
                or red_area > max_total_area
                or largest_ratio > max_component_ratio
                or largest_area > max_component_area
            )
            hz_x1 = max(0, min(roi_w - 1, int(roi_w * head_zone_left_ratio)))
            hz_x2 = max(hz_x1 + 1, min(roi_w, int(roi_w * head_zone_right_ratio)))
            hz_y1 = max(0, min(roi_h - 1, int(roi_h * head_zone_top_ratio)))
            hz_y2 = max(hz_y1 + 1, min(roi_h, int(roi_h * head_zone_bottom_ratio)))
            head_zone_area = int(np.count_nonzero(red[hz_y1:hz_y2, hz_x1:hz_x2]))
            head_zone_ok = head_zone_area >= head_zone_min_area
            min_line_length = int(max(roi_w, roi_h) * hough_min_length_ratio)
            best_line = None
            lines = cv2.HoughLinesP(
                line_mask,
                1,
                np.pi / 180,
                threshold=hough_threshold,
                minLineLength=min_line_length,
                maxLineGap=hough_gap,
            )
            if lines is not None:
                for raw_line in lines:
                    lx1, ly1, lx2, ly2 = [int(v) for v in raw_line[0]]
                    line_len = float(((lx2 - lx1) ** 2 + (ly2 - ly1) ** 2) ** 0.5)
                    angle = abs(float(np.degrees(np.arctan2(ly2 - ly1, lx2 - lx1))))
                    if angle > 90:
                        angle = 180 - angle
                    if not (line_min_angle <= angle <= line_max_angle):
                        continue
                    line_mid_y = (ly1 + ly2) / 2.0
                    line_top_y = min(ly1, ly2)
                    if line_mid_y > roi_h * hough_max_mid_y_ratio or line_top_y > roi_h * hough_max_top_y_ratio:
                        continue
                    if best_line is None or line_len > best_line["length"]:
                        best_line = {
                            "length": line_len,
                            "angle": angle,
                            "x": x1 + int((lx1 + lx2) / 2),
                            "y": y1 + int((ly1 + ly2) / 2),
                            "mid_y_ratio": line_mid_y / max(1, roi_h),
                            "top_y_ratio": line_top_y / max(1, roi_h),
                        }
            for idx in range(1, count):
                area = int(stats[idx, cv2.CC_STAT_AREA])
                bx = int(stats[idx, cv2.CC_STAT_LEFT])
                by = int(stats[idx, cv2.CC_STAT_TOP])
                bw = int(stats[idx, cv2.CC_STAT_WIDTH])
                bh = int(stats[idx, cv2.CC_STAT_HEIGHT])
                if area < min_area or bw < min_width or bh < min_height:
                    continue
                touches_left = bx <= 1
                touches_right = bx + bw >= roi_w - 2
                touches_top = by <= 1
                touches_bottom = by + bh >= roi_h - 2
                edge_touches = int(touches_left) + int(touches_right) + int(touches_top) + int(touches_bottom)
                edge_touch_ratio = edge_touches / 4.0
                line_ok = (
                    bw >= int(roi_w * min_line_width_ratio)
                    and bh >= int(roi_h * min_line_height_ratio)
                    and by <= int(roi_h * 0.74)
                    and by + bh >= int(roi_h * 0.36)
                    and bx + bw >= int(roi_w * 0.30)
                    and bx <= int(roi_w * 0.82)
                    and edge_touch_ratio <= max_edge_touch_ratio
                )
                head_ok = (
                    area >= head_min_area
                    and area <= head_max_area
                    and bw >= head_min_width
                    and bw <= head_max_width
                    and bh >= head_min_height
                    and bh <= head_max_height
                    and head_min_aspect <= (bw / max(1, bh)) <= head_max_aspect
                    and by <= int(roi_h * head_top_ratio)
                    and bx + bw >= int(roi_w * 0.28)
                    and bx <= int(roi_w * 0.82)
                    and edge_touches == 0
                )
                line_ok = line_ok and best_line is not None
                if not head_ok:
                    continue
                if best is None or area > best["area"]:
                    cx, cy = centroids[idx]
                    best = {
                        "area": area,
                        "x": x1 + int(cx),
                        "y": y1 + int(cy),
                        "w": bw,
                        "h": bh,
                        "line_ok": line_ok,
                        "head_ok": head_ok,
                        "edge_touch_ratio": edge_touch_ratio,
                    }
            line_can_claim = best_line is not None and (allow_line_only or head_zone_ok) and not skin_reject
            if line_can_claim and (best is None or int(best_line["length"]) > int(best["area"])):
                best = {
                    "area": int(best_line["length"]),
                    "x": int(best_line["x"]),
                    "y": int(best_line["y"]),
                    "w": int(best_line["length"]),
                    "h": 1,
                    "line_ok": True,
                    "head_ok": bool(head_zone_ok),
                    "edge_touch_ratio": 0.0,
                    "line_angle": float(best_line["angle"]),
                    "line_length": float(best_line["length"]),
                    "line_mid_y_ratio": float(best_line.get("mid_y_ratio", 0.0)),
                    "line_top_y_ratio": float(best_line.get("top_y_ratio", 0.0)),
                }
            found = (
                best is not None
                and red_ratio >= min_ratio
                and not skin_reject
                and bool(best.get("line_ok", False))
            )
            debug.append(
                {
                    "slot": slot,
                    "anchor_x": anchor_x,
                    "roi": (x1, y1, x2, y2),
                    "red_area": red_area,
                    "red_ratio": red_ratio,
                    "largest_area": largest_area,
                    "largest_ratio": largest_ratio,
                    "largest_w": largest_w,
                    "largest_h": largest_h,
                    "largest_touch_ratio": largest_touch_ratio,
                    "skin_reject": bool(skin_reject),
                    "best_area": int(best["area"]) if best else 0,
                    "best_w": int(best["w"]) if best else 0,
                    "best_h": int(best["h"]) if best else 0,
                    "line_ok": bool(best["line_ok"]) if best else False,
                    "head_ok": bool(best["head_ok"]) if best else False,
                    "edge_touch_ratio": float(best["edge_touch_ratio"]) if best else 0.0,
                    "line_angle": float(best.get("line_angle", 0.0)) if best else 0.0,
                    "line_length": float(best.get("line_length", 0.0)) if best else 0.0,
                    "line_mid_y_ratio": float(best.get("line_mid_y_ratio", 0.0)) if best else 0.0,
                    "line_top_y_ratio": float(best.get("line_top_y_ratio", 0.0)) if best else 0.0,
                    "head_zone_area": head_zone_area,
                    "head_zone_ok": bool(head_zone_ok),
                    "found": found,
                }
            )
            if debug_dir is not None:
                try:
                    status = "found1" if found else "found0"
                    ratio_i = int(round(red_ratio * 10000))
                    name = (
                        f"pad_hive{slot}_{status}_anchor{anchor_x}_"
                        f"x{x1}-{x2}_y{y1}-{y2}_red{red_area}_ratio{ratio_i}_best{int(best['area']) if best else 0}.png"
                    )
                    Image.fromarray(roi).save(debug_dir / name)
                    if bool(cfg.get("empty_hive_red_arrow_debug_save_mask", True)):
                        mask_name = (
                            f"pad_hive{slot}_{status}_anchor{anchor_x}_"
                            f"x{x1}-{x2}_y{y1}-{y2}_red{red_area}_ratio{ratio_i}_mask.png"
                        )
                        Image.fromarray((red * 255).astype(np.uint8)).save(debug_dir / mask_name)
                except Exception as exc:
                    print(f"Could not save hive pad debug crop: {exc}", flush=True)
            if found:
                available.append((slot, int(best["x"]), int(best["y"]), int(best["area"])))
        return available, debug

    def empty_hive_marker(self) -> tuple[int, int, int, int] | None:
        if cv2 is None or np is None:
            return None
        img = np.array(self.screen.shot().convert("RGB"))
        height, width = img.shape[:2]
        cfg = self.cfg.get("hive", {}) or {}
        if not bool(cfg.get("empty_hive_use_red_arrow_slots", True)):
            print("Hive red arrow detection disabled. returning None.", flush=True)
            return None

        arrow_candidates, arrow_debug = self._detect_hive_red_arrow_slots(img, cfg)
        debug_text = ", ".join(
            f"hive {item['slot']}: anchor_x={item['anchor_x']} red_area={item['red_area']} "
            f"red_ratio={item['red_ratio']:.4f} best_area={item['best_area']} "
            f"largest={item.get('largest_area', 0)}:{item.get('largest_ratio', 0.0):.4f} "
            f"skin_reject={item.get('skin_reject', False)} "
            f"best={item.get('best_w', 0)}x{item.get('best_h', 0)} "
            f"line={item.get('line_ok', False)} head={item.get('head_ok', False)} "
            f"head_zone={item.get('head_zone_area', 0)}:{item.get('head_zone_ok', False)} "
            f"angle={item.get('line_angle', 0.0):.1f} len={item.get('line_length', 0.0):.0f} "
            f"mid_y={item.get('line_mid_y_ratio', 0.0):.2f} top_y={item.get('line_top_y_ratio', 0.0):.2f} "
            f"edge={item.get('edge_touch_ratio', 0.0):.2f} found={item['found']}"
            for item in arrow_debug
        )
        print(f"hive red arrow scan: {debug_text}", flush=True)
        if not arrow_candidates:
            fallback_slot6 = bool(cfg.get("empty_hive_red_arrow_fallback_slot6_when_1_to_5_blocked", False))
            scanned_first_five = {
                int(item.get("slot", 0))
                for item in arrow_debug
                if 1 <= int(item.get("slot", 0)) <= 5
            }
            found_first_five = any(
                bool(item.get("found", False)) and 1 <= int(item.get("slot", 0)) <= 5
                for item in arrow_debug
            )
            if fallback_slot6 and len(scanned_first_five) == 5 and not found_first_five:
                ratios = cfg.get(
                    "empty_hive_red_arrow_slot_x_ratios",
                    [0.770, 0.635, 0.500, 0.364, 0.232, 0.095],
                )
                if len(ratios) >= 6:
                    y_top = int(height * float(cfg.get("empty_hive_red_arrow_roi_top_ratio", 0.135)))
                    y_bottom = int(height * float(cfg.get("empty_hive_red_arrow_roi_bottom_ratio", 0.305)))
                    anchor_x = int(width * float(ratios[5]))
                    anchor_y = int((y_top + y_bottom) / 2)
                    print(
                        "No free hive detected in slots 1-5; RDP fallback selecting hive 6.",
                        flush=True,
                    )
                    return (anchor_x, anchor_y, 0, 6)
            print("No red arrow/free hive pad detected. returning None.", flush=True)
            return None

        pick_mode = str(cfg.get("empty_hive_pick", "rightmost")).lower()
        if pick_mode == "largest":
            best_arrow = max(arrow_candidates, key=lambda item: item[3])
        elif pick_mode == "center":
            screen_center = width // 2
            best_arrow = min(arrow_candidates, key=lambda item: abs(item[1] - screen_center))
        else:
            best_arrow = max(arrow_candidates, key=lambda item: item[1])

        available_detail = ", ".join(
            f"hive {slot}: x={x} y={y} red_area={area}"
            for slot, x, y, area in arrow_candidates
        )
        print(
            f"available hives by red arrows: {available_detail}; "
            f"selected hive slot {best_arrow[0]} pick={pick_mode}",
            flush=True,
        )
        return (best_arrow[1], best_arrow[2], best_arrow[3], best_arrow[0])

    def screen_text(self) -> str:
        if not self.ensure_tesseract_available():
            return ""
        img = self.screen.shot()
        gray = img.convert("L")
        try:
            return pytesseract.image_to_string(gray)
        except Exception as exc:
            print(f"OCR unavailable: {exc}", flush=True)
            return ""

    def rejoin_status_visible(self) -> str | None:
        phrases = [str(p).lower() for p in self.cfg.get("rejoin_status_phrases", [])]
        if not phrases:
            return None
        text = self.screen_text().lower()
        if not text:
            return None
        compact = " ".join(text.split())
        for phrase in phrases:
            if phrase in compact:
                return phrase
        return None

    def loading_text_visible(self) -> bool:
        phrases = [str(p).lower() for p in self.cfg.get("load_detection.loading_phrases", [])]
        if not phrases:
            return False
        text = self.screen_text().lower()
        if not text:
            return False
        compact = " ".join(text.split())
        return any(phrase in compact for phrase in phrases)

    def screenshot_diff(self, a: Image.Image, b: Image.Image) -> float:
        a_small = a.resize((160, 90)).convert("L")
        b_small = b.resize((160, 90)).convert("L")
        diff = ImageChops.difference(a_small, b_small)
        return float(ImageStat.Stat(diff).mean[0])


class ViciousFarm:
    def __init__(self, cfg: Config, dry_run: bool, stop_event: Event | None = None):
        self.cfg = cfg
        self.input = Input(cfg, dry_run, stop_event)
        self.detector = Detector(cfg, Screen())
        self.input.speed_multiplier_provider = self.current_speed_adjustment
        self.servers = RobloxServers(cfg)
        self.dry_run = dry_run
        self.claimed_hive_slot: int | None = None
        self._stats_lock = Lock()
        self._stats_started_at = time.monotonic()
        self._stats_started_cpu = time.process_time()
        self._stats_counts = {
            "server_rejoins": 0,
            "night_servers": 0,
            "vicious_detected": 0,
            "field_scans": 0,
        }
        self._hourly_previous_counts = dict(self._stats_counts)
        self._hourly_previous_at = self._stats_started_at
        self._hourly_previous_cpu = self._stats_started_cpu
        self._hourly_previous_all_process_cpu = self.all_macro_process_cpu_seconds()
        self._hourly_previous_system_cpu = self.system_cpu_times()
        self._stats_history: list[dict] = []
        self.append_stats_sample()
        self._hourly_stop = Event()
        self._hourly_thread: Thread | None = None
        self._speed_monitor_stop = Event()
        self._speed_monitor_thread: Thread | None = None
        self._speed_monitor_lock = Lock()
        self._speed_monitor_adjustment: tuple[float, float] = (1.0, 0.0)
        self._speed_monitor_details = "detected: none"
        self._speed_monitor_updated_at = 0.0
        self._discord_queue: "queue.Queue[tuple[str, dict, bytes | None]]" = queue.Queue(maxsize=30)
        self._discord_worker_lock = Lock()
        self._discord_worker_thread: Thread | None = None
        self._hive_slot_path_missing = False
        self._stinger_templates: list[tuple[str, np.ndarray]] | None = None
        self._stinger_initial: int | None = None
        self._stinger_last: int | None = None
        self._stinger_session_gained = 0
        self._stinger_gain_events: list[tuple[float, int]] = []
        self._global_defeated_monitor_stop = Event()
        self._global_defeated_detected = Event()
        self._global_defeated_notified = Event()
        self._global_defeated_monitor_thread: Thread | None = None
        self._global_vicious_end_reason = ""
        self._spike_avoid_last = 0.0
        self._spike_avoid_log_last = 0.0
        self._spike_last_direction = ""
        self._spike_drift_x = 0.0
        self._spike_drift_y = 0.0

    def start_speed_monitor(self) -> None:
        speed_cfg = self.cfg.get("speed_buffs", {}) or {}
        if self.dry_run or not bool(speed_cfg.get("enabled", False)) or not bool(speed_cfg.get("monitor_enabled", True)):
            return
        if self._speed_monitor_thread is not None and self._speed_monitor_thread.is_alive():
            return
        self._speed_monitor_stop.clear()
        with self._speed_monitor_lock:
            self._speed_monitor_adjustment = (1.0, 0.0)
            self._speed_monitor_details = "detected: none"
            self._speed_monitor_updated_at = 0.0
        try:
            speed_image = self.detector.speed_buff_roi_image(speed_cfg)
            initial_adjustment = self.detector.active_speed_adjustment(
                force=True,
                speed_image=speed_image,
            )
            initial_lines = list(self.detector._last_speed_detection_lines)
            initial_detail = "; ".join(
                line for line in initial_lines
                if line.startswith("detected:")
            ) or "detected: none"
            with self._speed_monitor_lock:
                self._speed_monitor_adjustment = initial_adjustment
                self._speed_monitor_details = initial_detail
                self._speed_monitor_updated_at = time.time()
            if bool(speed_cfg.get("log_changes", True)):
                print(
                    f"Speed buff initial scan: x{initial_adjustment[0]:.2f} "
                    f"+{initial_adjustment[1]:.1f} ({initial_detail})",
                    flush=True,
                )
        except Exception as exc:
            print(f"Speed buff initial scan failed: {exc}", flush=True)
        print("Speed buff monitor started.", flush=True)

        def monitor_loop() -> None:
            interval = max(0.15, float(speed_cfg.get("monitor_interval_seconds", 0.5)))
            with self._speed_monitor_lock:
                last_detail = self._speed_monitor_details
            last_debug_log = 0.0
            while not self._speed_monitor_stop.is_set():
                try:
                    speed_image = self.detector.speed_buff_roi_image(speed_cfg)
                    adjustment = self.detector.active_speed_adjustment(
                        force=True,
                        speed_image=speed_image,
                    )
                    detail_lines = list(self.detector._last_speed_detection_lines)
                    detail = "; ".join(
                        line for line in detail_lines
                        if line.startswith("detected:")
                    ) or "detected: none"
                    with self._speed_monitor_lock:
                        self._speed_monitor_adjustment = adjustment
                        self._speed_monitor_details = detail
                        self._speed_monitor_updated_at = time.time()
                    if bool(speed_cfg.get("log_changes", True)) and detail != last_detail:
                        print(f"Speed buff monitor: x{adjustment[0]:.2f} +{adjustment[1]:.1f} ({detail})", flush=True)
                        last_detail = detail
                    if bool(speed_cfg.get("debug", False)):
                        now = time.time()
                        debug_interval = max(1.0, float(speed_cfg.get("debug_interval_seconds", 8.0)))
                        if now - last_debug_log >= debug_interval:
                            best_line = next((line for line in detail_lines if line.startswith("best scores:")), "")
                            print(f"Speed buff debug: {best_line or detail}", flush=True)
                            if bool(speed_cfg.get("debug_crops", False)):
                                path = self.detector.save_speed_buff_debug_crop("monitor")
                                if path is not None:
                                    print(f"Speed buff debug crop: {path}", flush=True)
                            last_debug_log = now
                except Exception as exc:
                    print(f"Speed buff monitor failed: {exc}", flush=True)
                self._speed_monitor_stop.wait(interval)

        self._speed_monitor_thread = Thread(target=monitor_loop, daemon=True)
        self._speed_monitor_thread.start()

    def stop_speed_monitor(self) -> None:
        self._speed_monitor_stop.set()
        if self._speed_monitor_thread is not None:
            self._speed_monitor_thread.join(timeout=0.75)

    def current_monitored_speed_adjustment(self) -> tuple[float, float]:
        speed_cfg = self.cfg.get("speed_buffs", {}) or {}
        max_age = max(0.5, float(speed_cfg.get("monitor_max_age_seconds", 2.0)))
        with self._speed_monitor_lock:
            adjustment = self._speed_monitor_adjustment
            updated_at = self._speed_monitor_updated_at
        if updated_at <= 0.0 or time.time() - updated_at > max_age:
            return 1.0, 0.0
        return adjustment

    def start_global_defeated_monitor(self) -> None:
        cfg = self.cfg.get("vicious_detection", {}) or {}
        if self.dry_run or not bool(cfg.get("global_defeated_monitor_enabled", True)):
            return
        if self._global_defeated_monitor_thread is not None and self._global_defeated_monitor_thread.is_alive():
            return
        self._global_defeated_detected.clear()
        self._global_defeated_notified.clear()
        self._global_defeated_monitor_stop.clear()
        self._global_vicious_end_reason = ""
        print("Global Vicious end monitor started.", flush=True)

        def monitor_loop() -> None:
            poll_seconds = max(0.05, float(cfg.get("global_defeated_monitor_poll_seconds", cfg.get("defeated_message_poll_seconds", 0.2))))
            while not self._global_defeated_monitor_stop.is_set() and not self._global_defeated_detected.is_set():
                try:
                    if self.detector.defeated():
                        self._global_vicious_end_reason = "defeated"
                        self._global_defeated_detected.set()
                        self.input.release_path_keys()
                        print("Global Vicious end monitor detected: defeated banner/message.", flush=True)
                        return
                    if self.detector.vicious_left_message_visible():
                        self._global_vicious_end_reason = "left"
                        self._global_defeated_detected.set()
                        self.input.release_path_keys()
                        print("Global Vicious end monitor detected: Vicious Bee left message.", flush=True)
                        return
                except Exception as exc:
                    print(f"Global Vicious end monitor failed: {exc}", flush=True)
                self._global_defeated_monitor_stop.wait(poll_seconds)

        self._global_defeated_monitor_thread = Thread(target=monitor_loop, daemon=True)
        self._global_defeated_monitor_thread.start()

    def stop_global_defeated_monitor(self) -> None:
        self._global_defeated_monitor_stop.set()
        if self._global_defeated_monitor_thread is not None:
            self._global_defeated_monitor_thread.join(timeout=0.5)
        self._global_defeated_monitor_thread = None
        print("Global Vicious end monitor stopped.", flush=True)

    def global_vicious_defeated_detected(self) -> bool:
        return self._global_defeated_detected.is_set()

    def notify_global_vicious_defeated_once(self, field: str = "unknown") -> None:
        if self._global_defeated_notified.is_set():
            return
        self._global_defeated_notified.set()
        reason = self._global_vicious_end_reason or "defeated"
        print(f"Vicious ended by global monitor: {reason}.", flush=True)
        if reason == "left":
            self.discord_notify_vicious_left(field)
        else:
            self.discord_notify_vicious_defeated(field, source="global")

    def raise_if_global_vicious_defeated(self, field: str = "unknown") -> None:
        if not self.global_vicious_defeated_detected():
            return
        self.notify_global_vicious_defeated_once(field)
        reason = self._global_vicious_end_reason or "ended"
        raise RejoinRequested(f"Vicious {reason} in {field}; rejoining")

    def spike_avoidance_config(self) -> dict:
        return self.cfg.get("spike_avoidance", {}) or {}

    def spike_avoidance_enabled(self) -> bool:
        return bool(self.spike_avoidance_config().get("enabled", True)) and not self.dry_run

    def detect_spike_danger(self, screenshot: Image.Image | None = None) -> dict[str, object] | None:
        if cv2 is None or np is None or not self.spike_avoidance_enabled():
            return None
        cfg = self.spike_avoidance_config()
        image = screenshot if screenshot is not None else self.detector.roblox_shot()
        width, height = image.size
        roi = cfg.get("roi", [0.18, 0.18, 0.86, 0.88])
        try:
            left, top, right, bottom = [float(value) for value in roi]
        except Exception:
            left, top, right, bottom = 0.18, 0.18, 0.86, 0.88
        x1 = max(0, min(width - 1, int(width * left)))
        y1 = max(0, min(height - 1, int(height * top)))
        x2 = max(x1 + 1, min(width, int(width * right)))
        y2 = max(y1 + 1, min(height, int(height * bottom)))
        crop = image.crop((x1, y1, x2, y2)).convert("RGB")
        arr = np.array(crop)
        red = arr[:, :, 0].astype(np.int16)
        green = arr[:, :, 1].astype(np.int16)
        blue = arr[:, :, 2].astype(np.int16)
        mask = (
            (red >= int(cfg.get("red_min_r", 180)))
            & (green <= int(cfg.get("red_max_g", 90)))
            & (blue <= int(cfg.get("red_max_b", 90)))
            & ((red - green) >= int(cfg.get("red_min_rg_delta", 80)))
            & ((red - blue) >= int(cfg.get("red_min_rb_delta", 80)))
        ).astype(np.uint8)
        if int(np.count_nonzero(mask)) < int(cfg.get("min_total_red_pixels", 120)):
            return None
        kernel = np.ones((5, 5), np.uint8)
        mask = cv2.morphologyEx(mask, cv2.MORPH_OPEN, kernel)
        mask = cv2.morphologyEx(mask, cv2.MORPH_CLOSE, kernel, iterations=2)
        count, _labels, stats, centroids = cv2.connectedComponentsWithStats(mask, 8)
        player_x = width * float(cfg.get("player_x_ratio", 0.50))
        player_y = height * float(cfg.get("player_y_ratio", 0.56))
        danger_radius = float(cfg.get("danger_radius_ratio", 0.085)) * min(width, height)
        min_area = int(cfg.get("min_component_area", 450))
        max_area = int(cfg.get("max_component_area", 50000))
        best: dict[str, object] | None = None
        best_score = 0.0
        for label in range(1, count):
            area = int(stats[label, cv2.CC_STAT_AREA])
            if area < min_area or area > max_area:
                continue
            cx = float(centroids[label][0] + x1)
            cy = float(centroids[label][1] + y1)
            box_left = float(stats[label, cv2.CC_STAT_LEFT] + x1)
            box_top = float(stats[label, cv2.CC_STAT_TOP] + y1)
            box_width = float(stats[label, cv2.CC_STAT_WIDTH])
            box_height = float(stats[label, cv2.CC_STAT_HEIGHT])
            box_right = box_left + box_width
            box_bottom = box_top + box_height
            dx = player_x - cx
            dy = player_y - cy
            distance = math.hypot(dx, dy)
            if distance > danger_radius:
                continue
            score = area / max(1.0, distance + 1.0)
            if score > best_score:
                best_score = score
                best = {
                    "area": area,
                    "center": (cx, cy),
                    "distance": distance,
                    "dx": dx,
                    "dy": dy,
                    "player": (player_x, player_y),
                    "box": (box_left, box_top, box_right, box_bottom),
                    "image_size": (width, height),
                    "roi": (x1, y1, x2, y2),
                }
        return best

    def spike_screen_direction_map(self) -> dict[str, str]:
        cfg = self.spike_avoidance_config()
        return {
            "left": str(cfg.get("screen_left_direction", "left")),
            "right": str(cfg.get("screen_right_direction", "right")),
            "up": str(cfg.get("screen_up_direction", "forward")),
            "down": str(cfg.get("screen_down_direction", "backward")),
        }

    def spike_escape_direction(self, danger: dict[str, object]) -> tuple[str, str]:
        mapping = self.spike_screen_direction_map()
        cfg = self.spike_avoidance_config()
        player_x, player_y = danger.get("player", (0.0, 0.0))
        try:
            px = float(player_x)
            py = float(player_y)
        except (TypeError, ValueError):
            px = py = 0.0
        box = danger.get("box")
        if isinstance(box, (tuple, list)) and len(box) == 4:
            left, top, right, bottom = [float(value) for value in box]
            image_size = danger.get("image_size", (right - left, bottom - top))
            try:
                image_width, image_height = [float(value) for value in image_size]
            except Exception:
                image_width, image_height = right - left, bottom - top
            margin = float(cfg.get("edge_margin_ratio", 0.05)) * max(1.0, min(image_width, image_height))
            if left - margin <= px <= right + margin and top - margin <= py <= bottom + margin:
                distances = [
                    ("left", max(0.0, px - left)),
                    ("right", max(0.0, right - px)),
                    ("up", max(0.0, py - top)),
                    ("down", max(0.0, bottom - py)),
                ]
                edge, _distance = min(distances, key=lambda item: item[1])
                return mapping.get(edge, edge), f"nearest_{edge}_edge"
        dx = float(danger.get("dx", 0.0) or 0.0)
        dy = float(danger.get("dy", 0.0) or 0.0)
        if abs(dx) >= abs(dy):
            edge = "right" if dx >= 0 else "left"
        else:
            edge = "down" if dy >= 0 else "up"
        return mapping.get(edge, edge), f"radial_{edge}"

    def spike_direction_vector(self, direction: str) -> tuple[float, float]:
        if direction == "right":
            return 1.0, 0.0
        if direction == "left":
            return -1.0, 0.0
        if direction == "forward":
            return 0.0, 1.0
        if direction == "backward":
            return 0.0, -1.0
        return 0.0, 0.0

    def avoid_spikes_if_needed(self, *, force: bool = False) -> bool:
        if not self.spike_avoidance_enabled():
            return False
        cfg = self.spike_avoidance_config()
        now = time.monotonic()
        interval = max(0.05, float(cfg.get("check_interval_seconds", 0.12)))
        if not force and now - self._spike_avoid_last < interval:
            return False
        self._spike_avoid_last = now
        danger = self.detect_spike_danger()
        if danger is None:
            return False
        direction, reason = self.spike_escape_direction(danger)
        self._spike_last_direction = direction
        hold = max(0.03, float(cfg.get("escape_hold_seconds", 0.16)))
        cooldown = max(0.0, float(cfg.get("escape_cooldown_seconds", 0.05)))
        log_interval = max(0.1, float(cfg.get("log_interval_seconds", 2.0)))
        if bool(cfg.get("log", True)) and now - self._spike_avoid_log_last >= log_interval:
            self._spike_avoid_log_last = now
            cx, cy = danger.get("center", (0, 0))
            print(
                f"Spike avoidance: direction={direction} reason={reason} area={danger.get('area')} "
                f"center=({float(cx):.0f},{float(cy):.0f}) distance={float(danger.get('distance', 0.0)):.1f}",
                flush=True,
            )
        self.input.release_path_keys()
        self.input.key_down(direction)
        try:
            self.input.sleep(hold)
        finally:
            self.input.key_up(direction)
        vx, vy = self.spike_direction_vector(direction)
        self._spike_drift_x += vx * hold
        self._spike_drift_y += vy * hold
        if cooldown > 0:
            self.input.sleep(cooldown)
        return True

    def compensate_spike_drift(self, label: str = "kill loop") -> None:
        if not self.spike_avoidance_enabled():
            return
        cfg = self.spike_avoidance_config()
        if not bool(cfg.get("compensate_drift_enabled", True)):
            return
        threshold = max(0.01, float(cfg.get("compensate_drift_threshold_seconds", 0.08)))
        max_hold = max(0.02, float(cfg.get("compensate_drift_max_hold_seconds", 0.28)))
        x = float(self._spike_drift_x)
        y = float(self._spike_drift_y)
        moves: list[tuple[str, float]] = []
        if abs(x) >= threshold:
            moves.append(("left" if x > 0 else "right", min(max_hold, abs(x))))
        if abs(y) >= threshold:
            moves.append(("backward" if y > 0 else "forward", min(max_hold, abs(y))))
        if not moves:
            return
        print(
            f"Spike drift compensation ({label}): x={x:.2f}s y={y:.2f}s moves="
            + ",".join(f"{direction}:{hold:.2f}s" for direction, hold in moves),
            flush=True,
        )
        self.input.release_path_keys()
        for direction, hold in moves:
            self.input.key_down(direction)
            try:
                self.input.sleep(hold)
            finally:
                self.input.key_up(direction)
        self._spike_drift_x = 0.0
        self._spike_drift_y = 0.0

    def discord_notify(
        self,
        event: str,
        message: str,
        screenshot: Image.Image | None = None,
    ) -> None:
        """Queue a Discord webhook update without pausing macro movement."""
        discord_cfg = self.cfg.get("discord", {}) or {}
        if not bool(discord_cfg.get("enabled", False)):
            return
        webhook_url = str(discord_cfg.get("webhook_url", "") or "").strip()
        if not webhook_url:
            print("Discord webhook enabled but URL is empty.", flush=True)
            return

        image_bytes: bytes | None = None
        # A screenshot is sent only for events that explicitly provide one.
        # Status-only updates such as rejoin and loading must remain text-only.
        if screenshot is not None and bool(discord_cfg.get("send_screenshots", True)):
            try:
                frame = screenshot.copy()
                buffer = io.BytesIO()
                frame.save(buffer, format="PNG")
                image_bytes = buffer.getvalue()
            except Exception as exc:
                print(f"Discord screenshot unavailable: {exc}", flush=True)

        payload = self.discord_embed_payload(event, message, image_bytes is not None)
        ping_text = self.discord_ping_text_for_event(event)
        if ping_text:
            payload["content"] = ping_text
            payload["allowed_mentions"] = self.discord_allowed_mentions_for_ping(ping_text)
        self._queue_discord_webhook(webhook_url, payload, image_bytes)

    def _queue_discord_webhook(self, webhook_url: str, payload: dict, image_bytes: bytes | None) -> None:
        with self._discord_worker_lock:
            if self._discord_worker_thread is None or not self._discord_worker_thread.is_alive():
                self._discord_worker_thread = Thread(target=self._discord_worker_loop, daemon=True)
                self._discord_worker_thread.start()
        try:
            self._discord_queue.put_nowait((webhook_url, payload, image_bytes))
        except queue.Full:
            print("Discord queue full; dropping webhook message to protect memory.", flush=True)

    def _discord_worker_loop(self) -> None:
        while True:
            webhook_url, payload, image_bytes = self._discord_queue.get()
            try:
                self._post_discord_webhook(webhook_url, payload, image_bytes)
            finally:
                self._discord_queue.task_done()

    @staticmethod
    def discord_event_color(event: str, message: str) -> int:
        text = f"{event} {message}".lower()
        if "failed" in text or "error" in text or "timeout" in text:
            return 0xED4245
        if "daytime" in text:
            return 0xFEE75C
        if "vicious detected" in text or "night detected" in text or "hive slot" in text:
            return 0x57F287
        if "finding" in text or "hopping" in text or "going" in text or "rejoin" in text or "scanning" in text or "scan" in text:
            return 0x5865F2
        return 0x9B84EE

    @classmethod
    def discord_embed_payload(cls, event: str, message: str, has_image: bool = False) -> dict:
        description = str(message or "").strip()
        if len(description) > 4096:
            description = description[:4093] + "..."
        embed = {
            "title": str(event or "Status")[:256],
            "description": description,
            "color": cls.discord_event_color(event, message),
            "timestamp": datetime.now().astimezone().isoformat(timespec="seconds"),
            "footer": {"text": "Vicious Bee Farm"},
        }
        if has_image:
            embed["image"] = {"url": "attachment://roblox.png"}
        return {"embeds": [embed]}

    def discord_ping_text_for_event(self, event: str) -> str:
        discord_cfg = self.cfg.get("discord", {}) or {}
        if str(event or "").strip().lower() != "vicious detected":
            return ""
        if not bool(discord_cfg.get("ping_on_vicious_detected", True)):
            return ""
        return self.normalize_discord_ping(str(discord_cfg.get("vicious_detected_ping", "@everyone") or "").strip())

    @staticmethod
    def normalize_discord_ping(ping_text: str) -> str:
        text = str(ping_text or "").strip()
        if not text:
            return ""
        if text in ("@everyone", "@here") or re.search(r"<@!?\d+>|<@&\d+>", text):
            return text
        user_match = re.fullmatch(r"@?(\d{15,25})", text)
        if user_match:
            return f"<@{user_match.group(1)}>"
        role_match = re.fullmatch(r"@?&(\d{15,25})", text)
        if role_match:
            return f"<@&{role_match.group(1)}>"
        return text

    @staticmethod
    def discord_allowed_mentions_for_ping(ping_text: str) -> dict:
        text = str(ping_text or "")
        parse: list[str] = []
        if "@everyone" in text or "@here" in text:
            parse.append("everyone")
        if re.search(r"<@!?\d+>", text):
            parse.append("users")
        if re.search(r"<@&\d+>", text):
            parse.append("roles")
        return {"parse": parse}

    @staticmethod
    def _post_discord_webhook(webhook_url: str, payload: dict, image_bytes: bytes | None) -> None:
        try:
            if image_bytes is None:
                response = requests.post(webhook_url, json=payload, timeout=12)
            else:
                response = requests.post(
                    webhook_url,
                    data={"payload_json": json.dumps(payload)},
                    files={"file": ("roblox.png", image_bytes, "image/png")},
                    timeout=12,
                )
            response.raise_for_status()
        except Exception as exc:
            print(f"Discord webhook failed: {exc}", flush=True)

    def test_discord_webhook(self) -> None:
        self.discord_notify("Test", "Webhook connected. Screenshots are enabled according to your setting.")
        print("Discord webhook test queued.", flush=True)

    def discord_notify_vicious_left(self, field: str) -> None:
        screenshot: Image.Image | None = None
        if not self.dry_run:
            with contextlib.suppress(Exception):
                screenshot = self.detector.roblox_shot()
        self.discord_notify(
            "Vicious Left",
            f"{field.title()} - Vicious Bee left the field/server",
            screenshot=screenshot,
        )

    def discord_notify_vicious_defeated(self, field: str, source: str = "kill") -> None:
        screenshot: Image.Image | None = None
        if not self.dry_run:
            with contextlib.suppress(Exception):
                screenshot = self.detector.roblox_shot()
        stingers = self.update_stinger_tracking_after_kill(screenshot=screenshot)
        message = field.title()
        if source == "global":
            message = f"{field.title()} - detected during chain/background monitor"
        discord_screenshot = self.stinger_hotbar_display_crop(screenshot) if screenshot is not None else None
        if stingers is not None:
            kill_text = self.format_optional_count(stingers["kill"])
            message = f"Stingers this kill: {kill_text}"
            if source == "global":
                message += "\nDetected during chain/background monitor."
            if stingers["kill"] is None:
                message += "\nCould not read Stinger reward from notifications."
        self.discord_notify("Vicious Defeated", message, screenshot=discord_screenshot)

    @staticmethod
    def format_optional_count(value: int | None) -> str:
        return "unknown" if value is None else str(value)

    def stinger_config(self) -> dict:
        return self.cfg.get("stinger_tracking", {}) or {}

    def stinger_tracking_enabled(self) -> bool:
        return bool(self.stinger_config().get("enabled", True))

    def load_stinger_templates(self) -> list[tuple[str, np.ndarray]]:
        if self._stinger_templates is not None:
            return self._stinger_templates
        templates: list[tuple[str, np.ndarray]] = []
        if cv2 is None or np is None:
            self._stinger_templates = templates
            return templates
        template_dir = self.cfg.base_dir / str(self.stinger_config().get("template_dir", "templates/stingers"))
        for path in sorted(template_dir.glob("*.png")):
            try:
                img = Image.open(path).convert("RGB")
                gray = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2GRAY)
                templates.append((path.name, gray))
            except Exception as exc:
                print(f"Could not load Stinger template {path}: {exc}", flush=True)
        self._stinger_templates = templates
        return templates

    def stinger_hotbar_slot_boxes(self, image: Image.Image) -> list[tuple[int, int, int, int]]:
        cfg = self.stinger_config()
        width, height = image.size
        slot_count = max(1, int(cfg.get("hotbar_slots", 7)))
        slot_size = int(max(44, min(86, round(height * float(cfg.get("slot_size_height_ratio", 0.079))))))
        gap = int(max(6, min(16, round(slot_size * float(cfg.get("slot_gap_ratio", 0.16))))))
        total_width = slot_count * slot_size + (slot_count - 1) * gap
        start_x = int((width - total_width) / 2)
        y_min = int(height * float(cfg.get("hotbar_y_min_ratio", 0.74)))
        y_max = int(height * float(cfg.get("hotbar_y_max_ratio", 0.91)))
        best_y = int(height * float(cfg.get("hotbar_y_default_ratio", 0.83)))
        if cv2 is not None and np is not None:
            try:
                arr = np.array(image.convert("RGB"))
                detected = self.detect_hotbar_slot_boxes_from_image(arr, slot_count)
                if len(detected) == slot_count:
                    centered = self.refine_centered_hotbar_slot_boxes(image, start_x, best_y, slot_size, gap, slot_count)
                    return self.choose_best_stinger_box_set(image, detected, centered)
                hsv = cv2.cvtColor(arr, cv2.COLOR_RGB2HSV)
                best_score = -1
                step = max(2, int(cfg.get("hotbar_y_scan_step", 4)))
                border = max(3, int(slot_size * 0.08))
                for y in range(max(0, y_min), min(height - slot_size, y_max), step):
                    score = 0
                    for index in range(slot_count):
                        x = start_x + index * (slot_size + gap)
                        if x < 0 or x + slot_size >= width:
                            continue
                        bands = (
                            hsv[y : y + border, x : x + slot_size],
                            hsv[y + slot_size - border : y + slot_size, x : x + slot_size],
                            hsv[y : y + slot_size, x : x + border],
                            hsv[y : y + slot_size, x + slot_size - border : x + slot_size],
                        )
                        for band in bands:
                            score += int(np.count_nonzero((band[:, :, 1] < 100) & (band[:, :, 2] > 115)))
                    if score > best_score:
                        best_score = score
                        best_y = y
            except Exception as exc:
                print(f"Stinger hotbar slot scan failed: {exc}", flush=True)
        return [(start_x + index * (slot_size + gap), best_y, slot_size, slot_size) for index in range(slot_count)]

    def refine_centered_hotbar_slot_boxes(
        self,
        image: Image.Image,
        start_x: int,
        default_y: int,
        slot_size: int,
        gap: int,
        slot_count: int,
    ) -> list[tuple[int, int, int, int]]:
        if cv2 is None or np is None:
            return [(start_x + index * (slot_size + gap), default_y, slot_size, slot_size) for index in range(slot_count)]
        cfg = self.stinger_config()
        width, height = image.size
        try:
            arr = np.array(image.convert("RGB"))
            hsv = cv2.cvtColor(arr, cv2.COLOR_RGB2HSV)
            y_min = int(height * float(cfg.get("hotbar_y_min_ratio", 0.74)))
            y_max = int(height * float(cfg.get("hotbar_y_max_ratio", 0.91)))
            best_y = default_y
            best_score = -1
            step = max(2, int(cfg.get("hotbar_y_scan_step", 4)))
            border = max(3, int(slot_size * 0.08))
            for y in range(max(0, y_min), min(height - slot_size, y_max), step):
                score = 0
                for index in range(slot_count):
                    x = start_x + index * (slot_size + gap)
                    if x < 0 or x + slot_size >= width:
                        continue
                    bands = (
                        hsv[y : y + border, x : x + slot_size],
                        hsv[y + slot_size - border : y + slot_size, x : x + slot_size],
                        hsv[y : y + slot_size, x : x + border],
                        hsv[y : y + slot_size, x + slot_size - border : x + slot_size],
                    )
                    for band in bands:
                        score += int(np.count_nonzero((band[:, :, 1] < 100) & (band[:, :, 2] > 115)))
                if score > best_score:
                    best_score = score
                    best_y = y
            return [(start_x + index * (slot_size + gap), best_y, slot_size, slot_size) for index in range(slot_count)]
        except Exception:
            return [(start_x + index * (slot_size + gap), default_y, slot_size, slot_size) for index in range(slot_count)]

    def choose_best_stinger_box_set(
        self,
        image: Image.Image,
        first: list[tuple[int, int, int, int]],
        second: list[tuple[int, int, int, int]],
    ) -> list[tuple[int, int, int, int]]:
        def best_score(boxes: list[tuple[int, int, int, int]]) -> float:
            score = 0.0
            for x, y, size, _h in boxes:
                if x < 0 or y < 0 or x + size > image.width or y + size > image.height:
                    continue
                slot_image = image.crop((x, y, x + size, y + size)).convert("RGB")
                slot_score, _template = self.stinger_template_score(slot_image)
                score = max(score, slot_score)
            return score

        first_score = best_score(first)
        second_score = best_score(second)
        return first if first_score >= second_score else second

    def detect_hotbar_slot_boxes_from_image(self, arr: np.ndarray, slot_count: int) -> list[tuple[int, int, int, int]]:
        if cv2 is None or np is None:
            return []
        cfg = self.stinger_config()
        height, width = arr.shape[:2]
        y_min = int(height * float(cfg.get("hotbar_y_min_ratio", 0.74)))
        y_max = int(height * float(cfg.get("hotbar_y_max_ratio", 0.91)))
        crop = arr[max(0, y_min) : min(height, y_max), :]
        if crop.size == 0:
            return []
        hsv = cv2.cvtColor(crop, cv2.COLOR_RGB2HSV)
        light = ((hsv[:, :, 1] < 95) & (hsv[:, :, 2] > 120)).astype(np.uint8) * 255
        light = cv2.morphologyEx(light, cv2.MORPH_CLOSE, np.ones((5, 5), np.uint8), iterations=2)
        contours, _hierarchy = cv2.findContours(light, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        min_size = int(height * 0.045)
        max_size = int(height * 0.12)
        candidates: list[tuple[int, int, int, int]] = []
        for contour in contours:
            x, y, w, h = cv2.boundingRect(contour)
            abs_y = y + y_min
            if w < min_size or h < min_size or w > max_size or h > max_size:
                continue
            aspect = w / max(1, h)
            if aspect < 0.65 or aspect > 1.35:
                continue
            if abs_y < height * 0.70:
                continue
            candidates.append((x, abs_y, w, h))
        if len(candidates) < 2:
            return []

        candidates.sort(key=lambda box: box[0])
        median_size = int(round(float(np.median([max(w, h) for _x, _y, w, h in candidates]))))
        median_size = max(44, min(86, median_size))
        centers = [x + w / 2.0 for x, _y, w, _h in candidates]
        spacings = [
            centers[index + 1] - centers[index]
            for index in range(len(centers) - 1)
            if median_size * 0.85 <= centers[index + 1] - centers[index] <= median_size * 1.45
        ]
        spacing = int(round(float(np.median(spacings)))) if spacings else int(round(median_size * 1.16))
        spacing = max(median_size + 4, min(median_size + 18, spacing))

        best_boxes: list[tuple[int, int, int, int]] = []
        best_score = -1
        for anchor_index, anchor in enumerate(candidates):
            anchor_center = anchor[0] + anchor[2] / 2.0
            for slot_position in range(slot_count):
                first_center = anchor_center - slot_position * spacing
                boxes: list[tuple[int, int, int, int]] = []
                score = 0
                y_values: list[int] = []
                for index in range(slot_count):
                    expected_center = first_center + index * spacing
                    nearest = min(
                        candidates,
                        key=lambda box: abs((box[0] + box[2] / 2.0) - expected_center),
                    )
                    distance = abs((nearest[0] + nearest[2] / 2.0) - expected_center)
                    if distance <= spacing * 0.28:
                        x, y, w, h = nearest
                        score += 3
                        y_values.append(y)
                    else:
                        x = int(round(expected_center - median_size / 2.0))
                        y = int(round(np.median(y_values))) if y_values else anchor[1]
                    boxes.append((int(x), int(y), median_size, median_size))
                if boxes[0][0] < -median_size * 0.25 or boxes[-1][0] + median_size > width + median_size * 0.25:
                    score -= 20
                if score > best_score:
                    best_score = score
                    best_boxes = boxes
        if best_score < 6:
            return []
        return best_boxes

    def stinger_template_score(self, slot_image: Image.Image) -> tuple[float, str]:
        if cv2 is None or np is None:
            return 0.0, ""
        templates = self.load_stinger_templates()
        if not templates:
            return 0.0, ""
        gray = cv2.cvtColor(np.array(slot_image.convert("RGB")), cv2.COLOR_RGB2GRAY)
        best_score = 0.0
        best_template = ""
        scales = self.stinger_config().get("template_scales", [0.85, 0.95, 1.05, 1.15, 1.3])
        for template_name, template in templates:
            for scale in scales:
                try:
                    factor = float(scale)
                    resized = cv2.resize(
                        template,
                        (
                            max(8, int(template.shape[1] * factor)),
                            max(8, int(template.shape[0] * factor)),
                        ),
                    )
                    if resized.shape[0] >= gray.shape[0] or resized.shape[1] >= gray.shape[1]:
                        continue
                    score = float(cv2.matchTemplate(gray, resized, cv2.TM_CCOEFF_NORMED).max())
                    if score > best_score:
                        best_score = score
                        best_template = template_name
                except Exception:
                    continue
        return best_score, best_template

    def find_stinger_icon_match(self, image: Image.Image) -> dict[str, object] | None:
        if cv2 is None or np is None:
            return None
        templates = self.load_stinger_templates()
        if not templates:
            return None
        cfg = self.stinger_config()
        width, height = image.size
        roi_box = (
            max(0, int(width * float(cfg.get("icon_search_left_ratio", 0.22)))),
            max(0, int(height * float(cfg.get("icon_search_top_ratio", 0.72)))),
            min(width, int(width * float(cfg.get("icon_search_right_ratio", 0.82)))),
            min(height, int(height * float(cfg.get("icon_search_bottom_ratio", 0.94)))),
        )
        left, top, right, bottom = roi_box
        if right <= left or bottom <= top:
            return None
        roi = image.crop(roi_box).convert("RGB")
        gray = cv2.cvtColor(np.array(roi), cv2.COLOR_RGB2GRAY)
        best: dict[str, object] | None = None
        scales = cfg.get("template_scales", [0.85, 0.95, 1.05, 1.15, 1.3])
        for template_name, template in templates:
            for scale in scales:
                try:
                    factor = float(scale)
                    resized = cv2.resize(
                        template,
                        (
                            max(8, int(template.shape[1] * factor)),
                            max(8, int(template.shape[0] * factor)),
                        ),
                    )
                    th, tw = resized.shape[:2]
                    if th >= gray.shape[0] or tw >= gray.shape[1]:
                        continue
                    result = cv2.matchTemplate(gray, resized, cv2.TM_CCOEFF_NORMED)
                    _min_val, max_val, _min_loc, max_loc = cv2.minMaxLoc(result)
                    score = float(max_val)
                    if best is None or score > float(best["score"]):
                        x, y = max_loc
                        best = {
                            "score": score,
                            "template": template_name,
                            "scale": factor,
                            "box": (left + x, top + y, left + x + tw, top + y + th),
                            "roi": roi_box,
                        }
                except Exception:
                    continue
        return best

    def stinger_ocr_box_from_icon_match(
        self,
        image: Image.Image,
        match: dict[str, object],
    ) -> tuple[int, int, int, int]:
        cfg = self.stinger_config()
        width, height = image.size
        x1, y1, x2, y2 = match["box"]  # type: ignore[misc]
        icon_w = max(1, int(x2) - int(x1))
        icon_h = max(1, int(y2) - int(y1))
        left_pad = int(icon_w * float(cfg.get("icon_ocr_left_pad_ratio", 0.65)))
        right_pad = int(icon_w * float(cfg.get("icon_ocr_right_pad_ratio", 1.75)))
        top_pad = int(icon_h * float(cfg.get("icon_ocr_top_pad_ratio", 0.20)))
        bottom_pad = int(icon_h * float(cfg.get("icon_ocr_bottom_pad_ratio", 1.15)))
        return (
            max(0, int(x1) - left_pad),
            max(0, int(y1) - top_pad),
            min(width, int(x2) + right_pad),
            min(height, int(y2) + bottom_pad),
        )

    def stinger_hotbar_debug_image(
        self,
        image: Image.Image,
        scores: list[dict[str, object]] | None = None,
        ocr_box: tuple[int, int, int, int] | None = None,
        icon_match: dict[str, object] | None = None,
    ) -> Image.Image:
        width, height = image.size
        pad_x = int(self.stinger_config().get("debug_crop_pad_x", 72))
        pad_top = int(self.stinger_config().get("debug_crop_pad_top", 44))
        pad_bottom = int(self.stinger_config().get("debug_crop_pad_bottom", 34))
        if icon_match is not None:
            ix1, iy1, ix2, iy2 = icon_match["box"]  # type: ignore[misc]
            crop_boxes = [(int(ix1), int(iy1), int(ix2), int(iy2))]
            if ocr_box is not None:
                crop_boxes.append(ocr_box)
            left = max(0, min(box[0] for box in crop_boxes) - pad_x)
            top = max(0, min(box[1] for box in crop_boxes) - pad_top)
            right = min(width, max(box[2] for box in crop_boxes) + pad_x)
            bottom = min(height, max(box[3] for box in crop_boxes) + pad_bottom)
        else:
            boxes = self.stinger_hotbar_slot_boxes(image)
            if not boxes:
                return image.copy()
            top = max(0, min(y for _x, y, _s, _h in boxes) - pad_top)
            bottom = min(height, max(y + size for _x, y, size, _h in boxes) + pad_bottom)
            left = max(0, min(x for x, _y, _s, _h in boxes) - pad_x)
            right = min(width, max(x + size for x, _y, size, _h in boxes) + pad_x)
        debug = image.crop((left, top, right, bottom)).convert("RGB")
        draw = ImageDraw.Draw(debug)
        score_by_slot = {int(item["slot"]): item for item in (scores or [])}
        font = self.font(12, bold=True)
        if icon_match is not None:
            ix1, iy1, ix2, iy2 = icon_match["box"]  # type: ignore[misc]
            score = float(icon_match.get("score", 0.0))
            color = (87, 242, 135) if score >= float(self.stinger_config().get("icon_match_threshold", 0.68)) else (237, 66, 69)
            draw.rectangle((int(ix1) - left, int(iy1) - top, int(ix2) - left, int(iy2) - top), outline=color, width=3)
            draw.text((int(ix1) - left, max(0, int(iy1) - top - 16)), f"icon {score:.2f}", fill=color, font=font)
        else:
            boxes = self.stinger_hotbar_slot_boxes(image)
            for slot_index, (x, y, size, _h) in enumerate(boxes, start=1):
                dx = x - left
                dy = y - top
                item = score_by_slot.get(slot_index)
                score = float(item["score"]) if item is not None else 0.0
                color = (87, 242, 135) if score >= float(self.stinger_config().get("template_threshold", 0.68)) else (237, 66, 69)
                draw.rectangle((dx, dy, dx + size, dy + size), outline=color, width=3)
                draw.text((dx, max(0, dy - 16)), f"{slot_index}: {score:.2f}", fill=color, font=font)
        if ocr_box is not None:
            ox1, oy1, ox2, oy2 = ocr_box
            draw.rectangle((ox1 - left, oy1 - top, ox2 - left, oy2 - top), outline=(255, 230, 80), width=3)
            draw.text((ox1 - left, min(debug.height - 14, max(0, oy2 - top + 2))), "OCR", fill=(255, 230, 80), font=font)
        return debug

    def read_stinger_number_from_slot(self, slot_image: Image.Image) -> int | None:
        if pytesseract is None or not self.detector.ensure_tesseract_available():
            print("Could not read Stingers from hotbar: Tesseract OCR unavailable.", flush=True)
            return None
        cfg = self.stinger_config()
        try:
            width, height = slot_image.size
            crops = [
                slot_image.crop((0, int(height * 0.58), width, height)),
                slot_image.crop((0, int(height * 0.60), width, height)),
                slot_image.crop((0, int(height * 0.62), width, height)),
                slot_image.crop((0, int(height * 0.55), width, height)),
                slot_image.crop((0, int(height * 0.50), width, height)),
            ]
            scale = float(cfg.get("number_ocr_scale", 5.0))
            x_candidates: list[tuple[int, str]] = []
            candidates: list[tuple[int, str]] = []
            texts: list[str] = []
            for crop in crops:
                if scale > 1.0:
                    crop = crop.resize(
                        (max(1, int(crop.width * scale)), max(1, int(crop.height * scale))),
                        Image.Resampling.LANCZOS,
                    )
                base_gray = ImageOps.autocontrast(crop.convert("L"))
                gray = ImageEnhance.Contrast(base_gray).enhance(float(cfg.get("number_ocr_contrast", 2.8)))
                variants = [gray, ImageEnhance.Contrast(base_gray).enhance(4.0)]
                if len(x_candidates) < 2:
                    for threshold in (180, 220):
                        variants.append(base_gray.point(lambda pixel, t=threshold: 0 if pixel > t else 255))
                for variant in variants:
                    variant = ImageOps.expand(variant, border=max(4, int(min(variant.size) * 0.08)), fill=255)
                    for psm in (7, 10, 6, 13, 8):
                        text = pytesseract.image_to_string(
                            variant,
                            config=f"--psm {psm} -c tessedit_char_whitelist=xX0123456789",
                        )
                        normalized = (text or "").strip()
                        texts.append(normalized)
                        x_matches = re.findall(r"[xX]+[ \t]*([0-9][0-9,. \t]*)", normalized)
                        plain_matches: list[str] = []
                        if not x_matches and bool(cfg.get("number_ocr_accept_without_x", False)):
                            plain_matches = re.findall(r"([0-9][0-9,.\s]*)", normalized)
                        for match in x_matches:
                            digits = re.sub(r"\D", "", match)
                            if digits:
                                x_candidates.append((int(digits), normalized))
                                counts = Counter(value for value, _text in x_candidates)
                                if len(digits) >= 4 and counts[int(digits)] >= 2:
                                    return int(digits)
                        for match in plain_matches:
                            digits = re.sub(r"\D", "", match)
                            if digits:
                                candidates.append((int(digits), normalized))
            if x_candidates:
                counts = Counter(value for value, _text in x_candidates)
                best_count = max(counts.values())
                winners = [value for value, count in counts.items() if count == best_count]
                winners.sort(key=lambda value: (len(str(value)), value), reverse=True)
                return winners[0]
            if not candidates:
                print(f"Could not read Stingers number from hotbar OCR text={texts[:6]!r}", flush=True)
                return None
            candidates.sort(key=lambda item: (len(str(item[0])), item[0]), reverse=True)
            return candidates[0][0]
        except Exception as exc:
            print(f"Could not read Stingers number from hotbar: {exc}", flush=True)
            return None

    def read_stingers_from_hotbar(
        self,
        screenshot: Image.Image | None = None,
    ) -> tuple[int | None, Image.Image | None, Image.Image | None]:
        if not self.stinger_tracking_enabled():
            return None, None, None
        image = screenshot if screenshot is not None else self.detector.roblox_shot()
        threshold = float(self.stinger_config().get("icon_match_threshold", self.stinger_config().get("template_threshold", 0.68)))
        best = self.find_stinger_icon_match(image)
        ocr_box = self.stinger_ocr_box_from_icon_match(image, best) if best is not None else None
        ocr_image = image.crop(ocr_box).convert("RGB") if ocr_box is not None else None
        debug_image = self.stinger_hotbar_debug_image(image, ocr_box=ocr_box, icon_match=best)
        if best is None or float(best["score"]) < threshold:
            score_text = "none" if best is None else f"{float(best['score']):.3f}"
            print(f"Could not find Stingers in hotbar. best_score={score_text}", flush=True)
            return None, None, debug_image
        value = self.read_stinger_number_from_slot(ocr_image) if ocr_image is not None else None
        if value is None:
            print(
                "Could not read Stingers from hotbar icon "
                f"score={float(best['score']):.3f} template={best['template']}",
                flush=True,
            )
            return None, ocr_image, debug_image
        print(
            f"Stingers hotbar read: {value} "
            f"score={float(best['score']):.3f} template={best['template']}",
            flush=True,
        )
        return value, ocr_image, debug_image

    def initialize_stinger_tracking(self) -> None:
        if self._stinger_initial is not None or not self.stinger_tracking_enabled() or self.dry_run:
            return
        value, _slot, debug_image = self.read_stingers_from_hotbar()
        if value is None:
            print("Could not save initial Stingers value.", flush=True)
            if bool(self.stinger_config().get("discord_debug_on_initial_fail", False)):
                self.discord_notify(
                    "Stinger Read Failed",
                    "Could not save initial Stingers value. Debug hotbar crop attached.",
                    screenshot=debug_image,
                )
            return
        self._stinger_initial = value
        self._stinger_last = value
        print(f"Initial Stingers saved: {value}", flush=True)

    def update_stinger_tracking_after_kill(self, screenshot: Image.Image | None = None) -> dict[str, object] | None:
        if not self.stinger_tracking_enabled() or self.dry_run:
            return None
        now = time.monotonic()
        gained, debug_image = self.read_stinger_reward_from_notifications(screenshot=screenshot)
        if gained is None:
            return {
                "kill": None,
                "session": self._stinger_session_gained,
                "hour": self.stingers_gained_last_hour(now),
                "current": None,
                "debug_image": debug_image,
            }
        if gained > 0:
            self._stinger_session_gained += gained
            self._stinger_gain_events.append((now, gained))
        cutoff = now - 2 * 3600.0
        self._stinger_gain_events = [item for item in self._stinger_gain_events if item[0] >= cutoff]
        return {
            "kill": gained,
            "session": self._stinger_session_gained,
            "hour": self.stingers_gained_last_hour(now),
            "current": None,
            "debug_image": debug_image,
        }

    def stinger_reward_crop(self, image: Image.Image) -> Image.Image:
        cfg = self.stinger_config()
        width, height = image.size
        region = cfg.get("reward_notification_region", [0.62, 0.56, 1.0, 0.98])
        try:
            left, top, right, bottom = [float(value) for value in region]
        except Exception:
            left, top, right, bottom = 0.62, 0.56, 1.0, 0.98
        box = (
            max(0, min(width - 1, int(width * left))),
            max(0, min(height - 1, int(height * top))),
            max(1, min(width, int(width * right))),
            max(1, min(height, int(height * bottom))),
        )
        if box[2] <= box[0] or box[3] <= box[1]:
            return image.copy()
        return image.crop(box).convert("RGB")

    def stinger_hotbar_display_crop(self, image: Image.Image) -> Image.Image | None:
        match = self.find_stinger_icon_match(image)
        if match is None:
            return None
        width, height = image.size
        x1, y1, x2, y2 = match["box"]  # type: ignore[misc]
        icon_w = max(1, int(x2) - int(x1))
        icon_h = max(1, int(y2) - int(y1))
        box = (
            max(0, int(x1) - int(icon_w * 1.3)),
            max(0, int(y1) - int(icon_h * 0.7)),
            min(width, int(x2) + int(icon_w * 1.3)),
            min(height, int(y2) + int(icon_h * 1.1)),
        )
        return image.crop(box).convert("RGB")

    def vicious_defeated_discord_image(
        self,
        screenshot: Image.Image,
        reward_crop: object | None = None,
    ) -> Image.Image:
        full = screenshot.convert("RGB")
        hotbar_crop = self.stinger_hotbar_display_crop(full)
        reward_img = reward_crop if isinstance(reward_crop, Image.Image) else self.stinger_reward_crop(full)
        sections: list[tuple[str, Image.Image]] = [("Full screen", full)]
        if hotbar_crop is not None:
            sections.append(("Stinger slot", hotbar_crop))
        if isinstance(reward_img, Image.Image):
            sections.append(("Reward messages", reward_img.convert("RGB")))
        return self.stack_discord_images(sections)

    def stack_discord_images(self, sections: list[tuple[str, Image.Image]]) -> Image.Image:
        max_width = int(self.stinger_config().get("defeated_discord_image_width", 1280))
        label_h = 28
        gap = 10
        prepared: list[tuple[str, Image.Image]] = []
        for label, image in sections:
            img = image.convert("RGB")
            if img.width > max_width:
                ratio = max_width / img.width
                img = img.resize((max_width, max(1, int(img.height * ratio))), Image.Resampling.LANCZOS)
            prepared.append((label, img))
        width = max((img.width for _label, img in prepared), default=max_width)
        height = sum(label_h + img.height for _label, img in prepared) + gap * max(0, len(prepared) - 1)
        canvas = Image.new("RGB", (width, max(1, height)), (18, 19, 23))
        draw = ImageDraw.Draw(canvas)
        font = self.font(18, bold=True)
        y = 0
        for label, img in prepared:
            draw.text((10, y + 4), label, fill=(235, 235, 245), font=font)
            y += label_h
            canvas.paste(img, ((width - img.width) // 2, y))
            y += img.height + gap
        return canvas

    def read_stinger_reward_from_notifications(
        self,
        screenshot: Image.Image | None = None,
    ) -> tuple[int | None, Image.Image | None]:
        image = screenshot if screenshot is not None else self.detector.roblox_shot()
        reward_crop = self.stinger_reward_crop(image)
        if pytesseract is None or not self.detector.ensure_tesseract_available():
            print("Could not read Stinger reward: Tesseract OCR unavailable.", flush=True)
            return None, reward_crop
        cfg = self.stinger_config()
        scale = float(cfg.get("reward_ocr_scale", 3.0))
        try:
            crop = reward_crop
            if scale > 1.0:
                crop = crop.resize(
                    (max(1, int(crop.width * scale)), max(1, int(crop.height * scale))),
                    Image.Resampling.LANCZOS,
                )
            gray = ImageEnhance.Contrast(ImageOps.autocontrast(crop.convert("L"))).enhance(
                float(cfg.get("reward_ocr_contrast", 2.4))
            )
            variants = [gray]
            if np is not None:
                arr = np.array(crop.convert("RGB")).astype(np.int16)
                r, g, b = arr[:, :, 0], arr[:, :, 1], arr[:, :, 2]
                blue_or_yellow = (
                    ((b > 95) & (b > r + 20) & (b > g + 5))
                    | ((r > 150) & (g > 100) & (b < 120))
                    | ((r > 170) & (g > 170) & (b > 170))
                )
                if int(np.count_nonzero(blue_or_yellow)) > 20:
                    mask = np.full(blue_or_yellow.shape, 255, dtype=np.uint8)
                    mask[blue_or_yellow] = 0
                    variants.append(Image.fromarray(mask, mode="L").filter(ImageFilter.MinFilter(3)))
            raw_texts: list[str] = []
            reward_candidates: list[int] = []
            for variant in variants:
                for psm in tuple(int(value) for value in cfg.get("reward_ocr_psm_values", [6, 11, 12, 4])):
                    text = pytesseract.image_to_string(variant, config=f"--psm {psm}")
                    if text:
                        raw_texts.append(text)
                        candidate = self.parse_stinger_reward_text(text)
                        if candidate is not None:
                            reward_candidates.append(candidate)
            gained = self.choose_stinger_reward_candidate(reward_candidates)
            text_preview = " ".join("\n".join(raw_texts).split())[:260]
            if gained is None:
                print(f"Could not read Stinger reward from notifications. text={text_preview!r}", flush=True)
                return None, reward_crop
            print(f"Stinger reward read: {gained} text={text_preview!r}", flush=True)
            return gained, reward_crop
        except Exception as exc:
            print(f"Could not read Stinger reward from notifications: {exc}", flush=True)
            return None, reward_crop

    @staticmethod
    def choose_stinger_reward_candidate(candidates: list[int]) -> int | None:
        valid = [value for value in candidates if 0 < int(value) <= 20]
        if not valid:
            return None
        counts = Counter(valid)
        best_count = max(counts.values())
        winners = [value for value, count in counts.items() if count == best_count]
        winners.sort(reverse=True)
        return winners[0]

    @staticmethod
    def parse_stinger_reward_text(text: str) -> int | None:
        values: list[int] = []
        for line in str(text or "").splitlines():
            lowered = line.lower()
            if "stinger" not in lowered and "st1nger" not in lowered:
                continue
            if "vicious" not in lowered and "viclous" not in lowered and "vic1ous" not in lowered:
                continue
            cleaned = line.replace("]", "1").replace("|", "1")
            cleaned = re.sub(r"\bI(?=\d|\s*st)", "1", cleaned)
            match = re.search(r"(?:\+|¥|y|v)?\s*([0-9]{1,2})\s*[A-Za-z]*\s*St[i1]ngers?", cleaned, re.IGNORECASE)
            if not match:
                match = re.search(r"(?:\+|¥|y|v)\s*([0-9]{1,2})", cleaned)
            if match:
                amount = int(match.group(1))
                if 0 < amount <= 15:
                    values.append(amount)
        if values:
            return sum(values)
        compact = " ".join(str(text or "").split())
        for match in re.finditer(
            r"(?:\+|¥|y|v)?\s*([0-9]{1,2})\s*[A-Za-z]*\s*St[i1]ngers?.{0,45}?(?:Vicious|Viclous|Vic1ous)",
            compact,
            re.IGNORECASE,
        ):
            amount = int(match.group(1))
            if 0 < amount <= 15:
                values.append(amount)
        return sum(values) if values else None

    def stingers_gained_last_hour(self, now: float | None = None) -> int:
        now = time.monotonic() if now is None else now
        cutoff = now - 3600.0
        return sum(amount for stamp, amount in self._stinger_gain_events if stamp >= cutoff)

    def test_stingers_hotbar(self) -> None:
        if not self.stinger_tracking_enabled():
            print("Stinger tracking is disabled in config.", flush=True)
            return
        screenshot = self.detector.roblox_shot()
        self.test_stingers_hotbar_image(screenshot, source_name="live")

    def test_stingers_hotbar_image_file(self, image_path: Path) -> None:
        if not self.stinger_tracking_enabled():
            print("Stinger tracking is disabled in config.", flush=True)
            return
        try:
            screenshot = Image.open(image_path).convert("RGB")
        except Exception as exc:
            print(f"Could not open Stinger test image {image_path}: {exc}", flush=True)
            return
        self.test_stingers_hotbar_image(screenshot, source_name=image_path.stem)

    def test_stingers_hotbar_image(self, screenshot: Image.Image, source_name: str = "image") -> None:
        value, slot_image, debug_image = self.read_stingers_from_hotbar(screenshot=screenshot)
        debug_dir = self.cfg.base_dir / "debug_stingers"
        debug_dir.mkdir(exist_ok=True)
        safe_source = re.sub(r"[^a-zA-Z0-9_.-]+", "_", source_name or "image")[:50]
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")[:-3]
        debug_path = debug_dir / f"{stamp}_{safe_source}_stinger_hotbar_debug.png"
        screen_path = debug_dir / f"{stamp}_{safe_source}_stinger_screen.png"
        slot_path = debug_dir / f"{stamp}_{safe_source}_stinger_ocr_crop.png"
        try:
            screenshot.save(screen_path)
            if debug_image is not None:
                debug_image.save(debug_path)
            if slot_image is not None:
                slot_image.save(slot_path)
        except Exception as exc:
            print(f"Could not save Stinger debug images: {exc}", flush=True)
        print("Stinger hotbar test finished.", flush=True)
        print(f"Stingers detected: {self.format_optional_count(value)}", flush=True)
        print(f"Stinger debug image: {debug_path if debug_image is not None else 'unavailable'}", flush=True)
        print(f"Stinger OCR crop: {slot_path if slot_image is not None else 'unavailable'}", flush=True)
        print(f"Stinger full screenshot: {screen_path}", flush=True)

    def stats_increment(self, name: str) -> None:
        with self._stats_lock:
            self._stats_counts[name] = self._stats_counts.get(name, 0) + 1

    def stats_snapshot(self) -> dict:
        with self._stats_lock:
            counts = dict(self._stats_counts)
        return {
            "monotonic": time.monotonic(),
            "wall": time.time(),
            "counts": counts,
            "self_cpu": time.process_time(),
            "all_macro_cpu": self.all_macro_process_cpu_seconds(),
            "system_cpu": self.system_cpu_times(),
        }

    def append_stats_sample(self) -> None:
        sample = self.stats_snapshot()
        with self._stats_lock:
            self._stats_history.append(sample)
            cutoff = sample["monotonic"] - 4 * 3600.0
            self._stats_history = [item for item in self._stats_history if item["monotonic"] >= cutoff]

    @staticmethod
    def sample_cpu_percent(previous: dict, current: dict, cores: int) -> tuple[float, float, float]:
        elapsed = max(0.001, float(current["monotonic"]) - float(previous["monotonic"]))
        self_cpu = max(0.0, float(current["self_cpu"]) - float(previous["self_cpu"])) / elapsed * 100.0 / cores
        all_cpu = (
            max(0.0, float(current["all_macro_cpu"][0]) - float(previous["all_macro_cpu"][0]))
            / elapsed
            * 100.0
            / cores
        )
        idle_delta = max(0.0, float(current["system_cpu"][0]) - float(previous["system_cpu"][0]))
        total_delta = max(0.001, float(current["system_cpu"][1]) - float(previous["system_cpu"][1]))
        system_cpu = max(0.0, min(100.0, (total_delta - idle_delta) / total_delta * 100.0))
        return self_cpu, all_cpu, system_cpu

    @staticmethod
    def font(size: int, bold: bool = False):
        names = (
            "arialbd.ttf" if bold else "arial.ttf",
            "segoeuib.ttf" if bold else "segoeui.ttf",
        )
        for name in names:
            try:
                return ImageFont.truetype(name, size)
            except Exception:
                continue
        return ImageFont.load_default()

    @staticmethod
    def format_short_time(ts: float) -> str:
        return time.strftime("%H:%M", time.localtime(ts))

    @staticmethod
    def draw_chart_grid(draw: ImageDraw.ImageDraw, box: tuple[int, int, int, int], lines: int = 4) -> None:
        x1, y1, x2, y2 = box
        for index in range(lines + 1):
            y = int(y1 + (y2 - y1) * index / max(1, lines))
            draw.line((x1, y, x2, y), fill=(48, 48, 54), width=1)
        for index in range(7):
            x = int(x1 + (x2 - x1) * index / 6)
            draw.line((x, y1, x, y2), fill=(38, 38, 44), width=1)

    def draw_time_axis(
        self,
        draw: ImageDraw.ImageDraw,
        box: tuple[int, int, int, int],
        start_wall: float,
        end_wall: float,
        font: ImageFont.ImageFont,
        color: tuple[int, int, int],
    ) -> None:
        x1, _y1, x2, y2 = box
        span = max(1.0, end_wall - start_wall)
        first_tick = math.ceil(start_wall / 900.0) * 900.0
        tick = first_tick
        while tick <= end_wall + 1:
            x = int(x1 + (tick - start_wall) / span * (x2 - x1))
            draw.line((x, y2 + 3, x, y2 + 9), fill=(66, 66, 76), width=1)
            label = self.format_short_time(tick)
            bbox = draw.textbbox((0, 0), label, font=font)
            draw.text((x - (bbox[2] - bbox[0]) / 2, y2 + 12), label, fill=color, font=font)
            tick += 900.0

    @staticmethod
    def draw_line_series(
        draw: ImageDraw.ImageDraw,
        points: list[tuple[float, float]],
        box: tuple[int, int, int, int],
        color: tuple[int, int, int],
        y_max: float,
        width: int = 3,
    ) -> None:
        if len(points) < 2:
            return
        x1, y1, x2, y2 = box
        t0 = points[0][0]
        t1 = points[-1][0]
        span = max(1.0, t1 - t0)
        coords = []
        for t, value in points:
            x = x1 + (t - t0) / span * (x2 - x1)
            y = y2 - min(max(value, 0.0), y_max) / max(1.0, y_max) * (y2 - y1)
            coords.append((int(x), int(y)))
        draw.line(coords, fill=color, width=width, joint="curve")

    @staticmethod
    def draw_activity_bars(
        draw: ImageDraw.ImageDraw,
        bars: list[tuple[float, int, int, int, int]],
        box: tuple[int, int, int, int],
    ) -> None:
        if not bars:
            return
        x1, y1, x2, y2 = box
        max_total = max(1, max(sum(values[1:]) for values in bars))
        inner_pad = 18
        inner_x1 = x1 + inner_pad
        inner_x2 = x2 - inner_pad
        slot_w = max(1.0, (inner_x2 - inner_x1) / max(1, len(bars)))
        bar_w = max(3, int(slot_w * 0.66))
        colors = ((88, 101, 242), (87, 242, 135), (254, 231, 92), (237, 66, 69))
        for index, item in enumerate(bars):
            x = int(inner_x1 + index * slot_w + (slot_w - bar_w) * 0.5)
            bottom = y2
            for value, color in zip(item[1:], colors):
                if value <= 0:
                    continue
                h = int((y2 - y1) * value / max_total)
                draw.rectangle((x, bottom - h, x + bar_w, bottom), fill=color)
                bottom -= h

    def draw_activity_buckets(
        self,
        draw: ImageDraw.ImageDraw,
        bars: list[tuple[float, int, int, int, int]],
        box: tuple[int, int, int, int],
        start_wall: float,
        end_wall: float,
        font: ImageFont.ImageFont,
        label_color: tuple[int, int, int],
    ) -> None:
        x1, y1, x2, y2 = box
        bucket_count = 12
        bucket_span = max(1.0, (end_wall - start_wall) / bucket_count)
        buckets = [[0, 0, 0, 0] for _ in range(bucket_count)]
        for item in bars:
            index = int((item[0] - start_wall) / bucket_span)
            index = max(0, min(bucket_count - 1, index))
            for value_index, value in enumerate(item[1:]):
                buckets[index][value_index] += int(value)

        max_value = max(1, max(max(bucket) for bucket in buckets))
        draw.text((x1 - 54, y1 - 22), "events / 5 min", fill=label_color, font=font)
        draw.text((x1 - 12, y2 - 8), "0", fill=label_color, font=font)
        tick_step = 1 if max_value <= 8 else max(1, math.ceil(max_value / 6))
        tick_values = list(range(tick_step, max_value + 1, tick_step))
        if not tick_values or tick_values[-1] != max_value:
            tick_values.append(max_value)
        for value in tick_values:
            y = int(y2 - value / max_value * (y2 - y1))
            draw.text((x1 - 24, y - 8), str(value), fill=label_color, font=font)

        colors = ((88, 101, 242), (87, 242, 135), (254, 231, 92), (237, 66, 69))
        inner_pad = 12
        bucket_w = (x2 - x1 - inner_pad * 2) / bucket_count
        bar_w = max(3, int(bucket_w / 6))
        group_w = bar_w * 4 + 6
        for index, bucket in enumerate(buckets):
            base_x = int(x1 + inner_pad + index * bucket_w + (bucket_w - group_w) / 2)
            for value_index, value in enumerate(bucket):
                if value <= 0:
                    continue
                h = int((y2 - y1) * value / max_value)
                bx = base_x + value_index * (bar_w + 2)
                draw.rectangle((bx, y2 - h, bx + bar_w, y2), fill=colors[value_index])

        for index in range(bucket_count):
            tick = start_wall + index * bucket_span
            x = int(x1 + inner_pad + index * bucket_w + bucket_w / 2)
            draw.line((x, y2 + 3, x, y2 + 9), fill=(66, 66, 76), width=1)
            label = self.format_short_time(tick)
            bbox = draw.textbbox((0, 0), label, font=font)
            draw.text((x - (bbox[2] - bbox[0]) / 2, y2 + 12), label, fill=label_color, font=font)
        draw.text((x1, y2 + 34), "Each group = 5 minutes", fill=label_color, font=font)

    def render_stats_dashboard(
        self,
        samples: list[dict],
        hourly: dict[str, int],
        counts: dict[str, int],
        hourly_cpu: float,
        all_process_hourly_cpu: float,
        system_hourly_cpu: float,
        all_process_count: int,
        system_process_count: int,
        total_elapsed: float,
        stingers_hour: int = 0,
        stingers_session: int = 0,
    ) -> Image.Image:
        width, height = 1400, 940
        img = Image.new("RGB", (width, height), (13, 14, 18))
        draw = ImageDraw.Draw(img)
        title_font = self.font(30, True)
        label_font = self.font(17, True)
        metric_font = self.font(30, True)
        small_font = self.font(15)
        tiny_font = self.font(13)
        panel = (30, 31, 38)
        panel_alt = (35, 36, 44)
        border = (54, 57, 69)
        grid = (43, 45, 54)
        text = (236, 238, 244)
        muted = (160, 164, 178)
        faint = (104, 109, 124)
        blue = (91, 123, 255)
        green = (73, 224, 119)
        yellow = (255, 224, 85)
        red = (245, 67, 78)
        violet = (167, 139, 250)

        def card(box, title: str | None = None):
            draw.rounded_rectangle(box, radius=14, fill=panel, outline=border, width=1)
            draw.line((box[0] + 1, box[1] + 1, box[2] - 1, box[1] + 1), fill=(70, 72, 84), width=1)
            if title:
                draw.text((box[0] + 22, box[1] + 18), title, fill=text, font=label_font)

        def legend_item(x: int, y: int, name: str, color: tuple[int, int, int]):
            draw.rounded_rectangle((x, y, x + 14, y + 14), radius=4, fill=color)
            draw.text((x + 22, y - 3), name, fill=muted, font=small_font)

        def metric_tile(box, label: str, value: str, color: tuple[int, int, int]):
            draw.rounded_rectangle(box, radius=10, fill=panel_alt, outline=(48, 50, 60), width=1)
            draw.rectangle((box[0], box[1] + 10, box[0] + 4, box[3] - 10), fill=color)
            draw.text((box[0] + 16, box[1] + 12), label, fill=muted, font=small_font)
            value_bbox = draw.textbbox((0, 0), value, font=metric_font)
            draw.text((box[2] - 18 - (value_bbox[2] - value_bbox[0]), box[1] + 26), value, fill=text, font=metric_font)

        def info_row(x: int, y: int, label: str, value: str, color: tuple[int, int, int] | None = None):
            if color is not None:
                draw.rounded_rectangle((x, y + 6, x + 8, y + 14), radius=3, fill=color)
                label_x = x + 18
            else:
                label_x = x
            draw.text((label_x, y), label, fill=muted, font=small_font)
            value_bbox = draw.textbbox((0, 0), value, font=small_font)
            draw.text((x + 260 - (value_bbox[2] - value_bbox[0]), y), value, fill=text, font=small_font)

        draw.text((34, 24), "Vicious Bee Farm", fill=text, font=title_font)
        draw.text((34, 60), "Hourly dashboard", fill=muted, font=small_font)
        period = f"{self.format_short_time(time.time() - 3600)} - {self.format_short_time(time.time())}"
        period_bbox = draw.textbbox((0, 0), period, font=small_font)
        pill = (width - 34 - (period_bbox[2] - period_bbox[0]) - 34, 28, width - 34, 58)
        draw.rounded_rectangle(pill, radius=15, fill=(27, 29, 36), outline=border, width=1)
        draw.text((pill[0] + 17, pill[1] + 6), period, fill=muted, font=small_font)

        left = (30, 96, 930, 378)
        card(left, "CPU Last Hour")
        chart = (left[0] + 58, left[1] + 66, left[2] - 28, left[3] - 48)
        self.draw_chart_grid(draw, chart)

        cores = max(1, os.cpu_count() or 1)
        cpu_points_self: list[tuple[float, float]] = []
        cpu_points_all: list[tuple[float, float]] = []
        cpu_points_system: list[tuple[float, float]] = []
        for previous, current in zip(samples, samples[1:]):
            self_cpu, all_cpu, system_cpu = self.sample_cpu_percent(previous, current, cores)
            cpu_points_self.append((float(current["wall"]), self_cpu))
            cpu_points_all.append((float(current["wall"]), all_cpu))
            cpu_points_system.append((float(current["wall"]), system_cpu))
        axis_start = samples[0]["wall"] if samples else time.time() - 3600
        axis_end = samples[-1]["wall"] if samples else time.time()
        y_max = max(20.0, *(p[1] for p in cpu_points_system + cpu_points_all + cpu_points_self)) if cpu_points_system else 100.0
        y_max = min(100.0, max(20.0, math.ceil(y_max / 10.0) * 10.0))
        self.draw_line_series(draw, cpu_points_system, chart, yellow, y_max, 3)
        self.draw_line_series(draw, cpu_points_all, chart, green, y_max, 3)
        self.draw_line_series(draw, cpu_points_self, chart, blue, y_max, 2)
        self.draw_time_axis(draw, chart, float(axis_start), float(axis_end), small_font, muted)
        draw.text((chart[0] - 42, chart[1] - 8), f"{y_max:.0f}%", fill=muted, font=small_font)
        draw.text((chart[0] - 28, chart[3] - 8), "0%", fill=muted, font=small_font)
        legend_item(left[0] + 390, left[1] + 22, "Laptop", yellow)
        legend_item(left[0] + 520, left[1] + 22, "All macro", green)
        legend_item(left[0] + 680, left[1] + 22, "This macro", blue)

        activity = (30, 408, 930, 884)
        card(activity, "Activity Last Hour")
        activity_chart = (activity[0] + 58, activity[1] + 98, activity[2] - 28, activity[3] - 68)
        self.draw_chart_grid(draw, activity_chart)
        bars: list[tuple[float, int, int, int, int]] = []
        for previous, current in zip(samples, samples[1:]):
            prev_counts = previous["counts"]
            cur_counts = current["counts"]
            bars.append(
                (
                    float(current["wall"]),
                    max(0, cur_counts.get("server_rejoins", 0) - prev_counts.get("server_rejoins", 0)),
                    max(0, cur_counts.get("night_servers", 0) - prev_counts.get("night_servers", 0)),
                    max(0, cur_counts.get("field_scans", 0) - prev_counts.get("field_scans", 0)),
                    max(0, cur_counts.get("vicious_detected", 0) - prev_counts.get("vicious_detected", 0)),
                )
            )
        self.draw_activity_buckets(draw, bars, activity_chart, float(axis_start), float(axis_end), tiny_font, muted)
        activity_legend = [
            ("Rejoins / server hops", blue),
            ("Night servers", green),
            ("Field scans", yellow),
            ("Vicious found", red),
        ]
        lx = activity[0] + 300
        for index, (name, color) in enumerate(activity_legend):
            x = lx + (index % 2) * 240
            y = activity[1] + 18 + (index // 2) * 24
            legend_item(x, y, name, color)

        last_hour_panel = (960, 96, 1370, 412)
        card(last_hour_panel, "Last Hour")
        tile_w = 174
        tile_h = 72
        tile_gap = 16
        tile_x = last_hour_panel[0] + 24
        tile_y = last_hour_panel[1] + 62
        metrics = [
            ("Rejoins", str(hourly.get("server_rejoins", 0)), blue),
            ("Night", str(hourly.get("night_servers", 0)), green),
            ("Fields", str(hourly.get("field_scans", 0)), yellow),
            ("Vicious", str(hourly.get("vicious_detected", 0)), red),
            ("Stingers", str(stingers_hour), violet),
        ]
        for index, (name, value, color) in enumerate(metrics):
            col = index % 2
            row = index // 2
            metric_tile(
                (
                    tile_x + col * (tile_w + tile_gap),
                    tile_y + row * (tile_h + 14),
                    tile_x + col * (tile_w + tile_gap) + tile_w,
                    tile_y + row * (tile_h + 14) + tile_h,
                ),
                name,
                value,
                color,
            )

        cpu_panel = (960, 434, 1370, 616)
        card(cpu_panel, "CPU")
        y = cpu_panel[1] + 62
        cpu_rows = [
            ("This macro", f"{hourly_cpu:.1f}%", blue),
            ("All macros", f"{all_process_hourly_cpu:.1f}%", green),
            ("Laptop", f"{system_hourly_cpu:.1f}%", yellow),
            ("Macro procs", str(all_process_count), None),
            ("Laptop procs", str(system_process_count), None),
        ]
        for name, value, color in cpu_rows:
            info_row(cpu_panel[0] + 28, y, name, value, color)
            y += 24

        session_panel = (960, 642, 1370, 884)
        card(session_panel, "Session")
        y = session_panel[1] + 62
        session_rows = [
            ("Time", self.format_session_duration(total_elapsed), None),
            ("Rejoins", str(counts.get("server_rejoins", 0)), blue),
            ("Night servers", str(counts.get("night_servers", 0)), green),
            ("Field scans", str(counts.get("field_scans", 0)), yellow),
            ("Vicious", str(counts.get("vicious_detected", 0)), red),
            ("Stingers", str(stingers_session), violet),
        ]
        for name, value, color in session_rows:
            info_row(session_panel[0] + 28, y, name, value, color)
            y += 30

        return img

    @staticmethod
    def format_session_duration(seconds: float) -> str:
        total = max(0, int(seconds))
        hours, remainder = divmod(total, 3600)
        minutes, seconds = divmod(remainder, 60)
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"

    @staticmethod
    def all_macro_process_cpu_seconds() -> tuple[float, int]:
        total, count = ViciousFarm.process_cpu_seconds_by_name("viciousbeefarm.exe")
        if count <= 0:
            return time.process_time(), 1
        return total, count

    @staticmethod
    def process_cpu_seconds_by_name(exe_name: str | None = None) -> tuple[float, int]:
        if not sys.platform.startswith("win"):
            return time.process_time(), 1
        target_name = exe_name.lower() if exe_name else None
        try:
            kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
            kernel32.CreateToolhelp32Snapshot.argtypes = (wintypes.DWORD, wintypes.DWORD)
            kernel32.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
            kernel32.Process32FirstW.argtypes = (wintypes.HANDLE, ctypes.c_void_p)
            kernel32.Process32FirstW.restype = wintypes.BOOL
            kernel32.Process32NextW.argtypes = (wintypes.HANDLE, ctypes.c_void_p)
            kernel32.Process32NextW.restype = wintypes.BOOL
            kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
            kernel32.CloseHandle.restype = wintypes.BOOL
            snapshot = kernel32.CreateToolhelp32Snapshot(0x00000002, 0)
            if snapshot in (0, -1):
                return time.process_time(), 1

            class PROCESSENTRY32W(ctypes.Structure):
                _fields_ = (
                    ("dwSize", wintypes.DWORD),
                    ("cntUsage", wintypes.DWORD),
                    ("th32ProcessID", wintypes.DWORD),
                    ("th32DefaultHeapID", ULONG_PTR),
                    ("th32ModuleID", wintypes.DWORD),
                    ("cntThreads", wintypes.DWORD),
                    ("th32ParentProcessID", wintypes.DWORD),
                    ("pcPriClassBase", ctypes.c_long),
                    ("dwFlags", wintypes.DWORD),
                    ("szExeFile", wintypes.WCHAR * 260),
                )

            entry = PROCESSENTRY32W()
            entry.dwSize = ctypes.sizeof(PROCESSENTRY32W)
            total_cpu = 0.0
            count = 0
            ok = kernel32.Process32FirstW(snapshot, ctypes.byref(entry))
            while ok:
                if target_name is None or str(entry.szExeFile).lower() == target_name:
                    cpu = ViciousFarm.process_cpu_seconds(int(entry.th32ProcessID), kernel32)
                    if cpu is not None:
                        total_cpu += cpu
                        count += 1
                ok = kernel32.Process32NextW(snapshot, ctypes.byref(entry))
            kernel32.CloseHandle(snapshot)
            return total_cpu, count
        except Exception:
            return time.process_time(), 1

    @staticmethod
    def system_cpu_times() -> tuple[float, float, int]:
        """Return idle CPU seconds, total CPU seconds, and process count."""
        process_count = ViciousFarm.windows_process_count()
        if not sys.platform.startswith("win"):
            now = time.process_time()
            return 0.0, now, process_count
        try:
            kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
            kernel32.GetSystemTimes.argtypes = (
                ctypes.POINTER(wintypes.FILETIME),
                ctypes.POINTER(wintypes.FILETIME),
                ctypes.POINTER(wintypes.FILETIME),
            )
            kernel32.GetSystemTimes.restype = wintypes.BOOL
            idle = wintypes.FILETIME()
            kernel = wintypes.FILETIME()
            user = wintypes.FILETIME()
            if not kernel32.GetSystemTimes(ctypes.byref(idle), ctypes.byref(kernel), ctypes.byref(user)):
                now = time.process_time()
                return 0.0, now, process_count

            def filetime_seconds(value: wintypes.FILETIME) -> float:
                ticks = (int(value.dwHighDateTime) << 32) | int(value.dwLowDateTime)
                return ticks / 10_000_000.0

            idle_seconds = filetime_seconds(idle)
            total_seconds = filetime_seconds(kernel) + filetime_seconds(user)
            return idle_seconds, total_seconds, process_count
        except Exception:
            now = time.process_time()
            return 0.0, now, process_count

    @staticmethod
    def windows_process_count() -> int:
        if not sys.platform.startswith("win"):
            return 1
        try:
            kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
            kernel32.CreateToolhelp32Snapshot.argtypes = (wintypes.DWORD, wintypes.DWORD)
            kernel32.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
            kernel32.Process32FirstW.argtypes = (wintypes.HANDLE, ctypes.c_void_p)
            kernel32.Process32FirstW.restype = wintypes.BOOL
            kernel32.Process32NextW.argtypes = (wintypes.HANDLE, ctypes.c_void_p)
            kernel32.Process32NextW.restype = wintypes.BOOL
            kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
            kernel32.CloseHandle.restype = wintypes.BOOL
            snapshot = kernel32.CreateToolhelp32Snapshot(0x00000002, 0)
            if snapshot in (0, -1):
                return 0

            class PROCESSENTRY32W(ctypes.Structure):
                _fields_ = (
                    ("dwSize", wintypes.DWORD),
                    ("cntUsage", wintypes.DWORD),
                    ("th32ProcessID", wintypes.DWORD),
                    ("th32DefaultHeapID", ULONG_PTR),
                    ("th32ModuleID", wintypes.DWORD),
                    ("cntThreads", wintypes.DWORD),
                    ("th32ParentProcessID", wintypes.DWORD),
                    ("pcPriClassBase", ctypes.c_long),
                    ("dwFlags", wintypes.DWORD),
                    ("szExeFile", wintypes.WCHAR * 260),
                )

            entry = PROCESSENTRY32W()
            entry.dwSize = ctypes.sizeof(PROCESSENTRY32W)
            count = 0
            ok = kernel32.Process32FirstW(snapshot, ctypes.byref(entry))
            while ok:
                count += 1
                ok = kernel32.Process32NextW(snapshot, ctypes.byref(entry))
            kernel32.CloseHandle(snapshot)
            return count
        except Exception:
            return 0

    @staticmethod
    def process_cpu_seconds(pid: int, kernel32=None) -> float | None:
        try:
            if kernel32 is None:
                kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
            kernel32.OpenProcess.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
            kernel32.OpenProcess.restype = wintypes.HANDLE
            kernel32.GetProcessTimes.argtypes = (
                wintypes.HANDLE,
                ctypes.POINTER(wintypes.FILETIME),
                ctypes.POINTER(wintypes.FILETIME),
                ctypes.POINTER(wintypes.FILETIME),
                ctypes.POINTER(wintypes.FILETIME),
            )
            kernel32.GetProcessTimes.restype = wintypes.BOOL
            kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
            kernel32.CloseHandle.restype = wintypes.BOOL
            handle = kernel32.OpenProcess(0x1000, False, pid)
            if not handle:
                return None
            creation = wintypes.FILETIME()
            exit_time = wintypes.FILETIME()
            kernel = wintypes.FILETIME()
            user = wintypes.FILETIME()
            try:
                if not kernel32.GetProcessTimes(
                    handle,
                    ctypes.byref(creation),
                    ctypes.byref(exit_time),
                    ctypes.byref(kernel),
                    ctypes.byref(user),
                ):
                    return None
                kernel_ticks = (int(kernel.dwHighDateTime) << 32) | int(kernel.dwLowDateTime)
                user_ticks = (int(user.dwHighDateTime) << 32) | int(user.dwLowDateTime)
                return (kernel_ticks + user_ticks) / 10_000_000.0
            finally:
                kernel32.CloseHandle(handle)
        except Exception:
            return None

    def send_hourly_report(self) -> None:
        self.append_stats_sample()
        now = time.monotonic()
        cpu_now = time.process_time()
        all_process_cpu_now = self.all_macro_process_cpu_seconds()
        system_cpu_now = self.system_cpu_times()
        with self._stats_lock:
            counts = dict(self._stats_counts)
            previous_counts = dict(self._hourly_previous_counts)
            self._hourly_previous_counts = dict(counts)
            previous_at = self._hourly_previous_at
            previous_cpu = self._hourly_previous_cpu
            previous_all_process_cpu = self._hourly_previous_all_process_cpu
            previous_system_cpu = self._hourly_previous_system_cpu
            self._hourly_previous_at = now
            self._hourly_previous_cpu = cpu_now
            self._hourly_previous_all_process_cpu = all_process_cpu_now
            self._hourly_previous_system_cpu = system_cpu_now
            sample_cutoff = now - 3600.0
            samples = [item for item in self._stats_history if item["monotonic"] >= sample_cutoff]

        cores = max(1, os.cpu_count() or 1)
        hour_elapsed = max(0.001, now - previous_at)
        total_elapsed = max(0.001, now - self._stats_started_at)
        hourly_cpu = max(0.0, (cpu_now - previous_cpu) / hour_elapsed * 100.0 / cores)
        total_cpu = max(0.0, (cpu_now - self._stats_started_cpu) / total_elapsed * 100.0 / cores)
        all_cpu_delta = max(0.0, all_process_cpu_now[0] - previous_all_process_cpu[0])
        all_process_hourly_cpu = all_cpu_delta / hour_elapsed * 100.0 / cores
        all_process_count = all_process_cpu_now[1]
        system_idle_delta = max(0.0, system_cpu_now[0] - previous_system_cpu[0])
        system_total_delta = max(0.001, system_cpu_now[1] - previous_system_cpu[1])
        system_hourly_cpu = max(0.0, min(100.0, (system_total_delta - system_idle_delta) / system_total_delta * 100.0))
        system_process_count = system_cpu_now[2]
        hourly = {name: counts.get(name, 0) - previous_counts.get(name, 0) for name in counts}
        stingers_hour = self.stingers_gained_last_hour(now)
        message = (
            "Last hour:\n"
            f"- Vicious detected: {hourly['vicious_detected']}\n"
            f"- Servers rejoined: {hourly['server_rejoins']}\n"
            f"- Night servers: {hourly['night_servers']}\n"
            f"- Fields scanned: {hourly['field_scans']}\n"
            f"- Stingers gained last hour: {stingers_hour}\n"
            f"- Average macro CPU: {hourly_cpu:.1f}%\n"
            f"- All macro processes CPU: {all_process_hourly_cpu:.1f}% ({all_process_count} processes)\n"
            f"- All laptop CPU: {system_hourly_cpu:.1f}% ({system_process_count} processes)\n\n"
            "Session:\n"
            f"- Time: {self.format_session_duration(total_elapsed)}\n"
            f"- Vicious detected: {counts['vicious_detected']}\n"
            f"- Servers rejoined: {counts['server_rejoins']}\n"
            f"- Night servers: {counts['night_servers']}\n"
            f"- Fields scanned: {counts['field_scans']}\n"
            f"- Stingers gained session: {self._stinger_session_gained}\n"
            f"- Average macro CPU: {total_cpu:.1f}%"
        )
        dashboard = None
        try:
            dashboard = self.render_stats_dashboard(
                samples,
                hourly,
                counts,
                hourly_cpu,
                all_process_hourly_cpu,
                system_hourly_cpu,
                all_process_count,
                system_process_count,
                total_elapsed,
                stingers_hour,
                self._stinger_session_gained,
            )
        except Exception as exc:
            print(f"Could not render Discord dashboard: {exc}", flush=True)
        self.discord_notify("Hourly Report", message, screenshot=dashboard)
        print("Discord hourly report queued.", flush=True)

    def _hourly_report_loop(self) -> None:
        # Align reports to the wall-clock hour, for example 03:00, 04:00, 05:00.
        while not self._hourly_stop.is_set():
            now = time.time()
            seconds_until_hour = max(0.1, 3600.0 - (now % 3600.0))
            wait_seconds = min(60.0, seconds_until_hour)
            if self._hourly_stop.wait(wait_seconds):
                break
            self.append_stats_sample()
            if seconds_until_hour <= 60.0:
                self.send_hourly_report()

    def start_hourly_reports(self) -> None:
        discord_cfg = self.cfg.get("discord", {}) or {}
        if not bool(discord_cfg.get("enabled", False)) or not bool(discord_cfg.get("hourly_reports_enabled", True)):
            return
        if self._hourly_thread is not None and self._hourly_thread.is_alive():
            return
        self._hourly_stop.clear()
        self._hourly_thread = Thread(target=self._hourly_report_loop, daemon=True)
        self._hourly_thread.start()

    def stop_hourly_reports(self) -> None:
        self._hourly_stop.set()

    def current_speed_multiplier(self) -> float:
        return self.detector.active_speed_multiplier()

    def current_speed_adjustment(self) -> tuple[float, float]:
        speed_cfg = self.cfg.get("speed_buffs", {}) or {}
        if not bool(speed_cfg.get("apply_to_walk", False)):
            return 1.0, 0.0
        if bool(speed_cfg.get("monitor_enabled", True)):
            return self.current_monitored_speed_adjustment()
        return self.detector.active_speed_adjustment()

    def test_speed_detection(self, duration_seconds: float | None = None, interval: float = 0.5):
        speed_cfg = self.cfg.get("speed_buffs", {}) or {}
        duration = float(
            speed_cfg.get("test_duration_seconds", 60.0)
            if duration_seconds is None
            else duration_seconds
        )
        duration = max(5.0, min(3600.0, duration))
        log_name = str(speed_cfg.get("log_file", "speed_detection_log.txt") or "speed_detection_log.txt")
        log_path = Path(log_name)
        if not log_path.is_absolute():
            log_path = self.cfg.base_dir / log_path
        log_path.parent.mkdir(parents=True, exist_ok=True)

        print(f"Speed detection test: {duration:g}s. Log file: {log_path}", flush=True)
        self.input.focus_roblox()
        self.input.sleep(0.35)
        started_at = time.monotonic()
        deadline = started_at + duration
        index = 0
        with log_path.open("a", encoding="utf-8") as fh:
            fh.write(
                f"\n=== speed detection {time.strftime('%Y-%m-%d %H:%M:%S')} "
                f"duration={duration:g}s ===\n"
            )
            while time.monotonic() < deadline:
                if self.input.stopped():
                    print("Speed detection test stopped.", flush=True)
                    fh.write("stopped\n")
                    break
                index += 1
                self.input.focus_roblox()
                self.input.sleep(0.08)
                speed_image = self.detector.speed_buff_roi_image(speed_cfg)
                multiplier, flat_bonus = self.detector.active_speed_adjustment(
                    force=True,
                    speed_image=speed_image,
                )
                speed, speed_info = effective_walk_speed(
                    float(self.cfg.get("move_speed_studs_per_second", 29.0)),
                    multiplier,
                    flat_bonus,
                )
                time_multiplier = path_movement_time_multiplier(self.cfg)
                path_scale = PATH_REFERENCE_SPEED / speed * time_multiplier
                line = (
                    f"sample {index}: manual={speed_info.input_speed:.1f}, "
                    f"base={speed_info.base_speed:.1f}, perm=x{speed_info.permanent_multiplier:.3f}, "
                    f"buff=x{multiplier:.2f} +{flat_bonus:.1f}, speed={speed:.1f}, "
                    f"cal=x{time_multiplier:.3f}, "
                    f"path_time_scale={path_scale:.3f} vs base {PATH_REFERENCE_SPEED:g}"
                )
                print(line, flush=True)
                fh.write(line + "\n")
                for detail in self.detector._last_speed_detection_lines:
                    print(f"  {detail}", flush=True)
                    fh.write(f"  {detail}\n")
                if bool(speed_cfg.get("debug_crops", True)):
                    crop_path = self.detector.save_speed_buff_debug_crop(
                        f"test_{index:02d}",
                        image=speed_image,
                    )
                    if crop_path is not None:
                        crop_line = f"  debug crop: {crop_path}"
                        print(crop_line, flush=True)
                        fh.write(crop_line + "\n")
                fh.flush()
                remaining = max(0.0, deadline - time.monotonic())
                if remaining > 0:
                    self.input.sleep(min(float(interval), remaining))
        elapsed = time.monotonic() - started_at
        print(f"Speed detection test done: {index} samples in {elapsed:.1f}s.", flush=True)

    def maybe_detect(self, field: str) -> bool:
        found = self.detector.vicious_visible(field)
        print(f"detection {field}: {found}", flush=True)
        return found

    def input_test(self):
        print("Starting input test", flush=True)
        self.input.focus_roblox()
        self.input.sleep(0.5)
        self.input.walk("forward", 18)
        self.input.walk("left", 18)
        self.input.walk("backward", 18)
        self.input.walk("right", 18)
        self.input.press("space", repeats=2, interval=0.25)
        cfg = self.cfg.get("camera_setup", {}) or {}
        hold = float(cfg.get("key_hold_seconds", 0.12))
        gap = float(cfg.get("between_keys_seconds", 0.08))
        self.input.press_camera_key("rot_down", 2, hold, gap)
        self.input.press_camera_key("rot_up", 2, hold, gap)
        print("Input test finished", flush=True)

    def search(self):
        self.start_hourly_reports()
        self.start_speed_monitor()
        try:
            self._search()
        finally:
            self.stop_speed_monitor()
            self.stop_hourly_reports()

    def _search(self):
        if not self.cfg.get("server_hop", True):
            self.claimed_hive_slot = None
            self.input.focus_roblox()
            self.detect_night_or_stop()
            self.initialize_stinger_tracking()
            self.start_global_defeated_monitor()
            try:
                self.vic_path()
            finally:
                self.stop_global_defeated_monitor()
            return

        max_rejoins = int(self.cfg.get("max_night_rejoins", 25))
        for attempt in range(1, max_rejoins + 1):
            try:
                self.claimed_hive_slot = None
                print(f"Night search attempt {attempt}/{max_rejoins}", flush=True)
                self.stats_increment("server_rejoins")
                self.discord_notify(
                    "Finding New Server",
                    f"Attempt {attempt}/{max_rejoins}",
                )
                self.servers.close_roblox(self.dry_run)
                pre_join_sleep = float(self.cfg.get("rejoin_pre_join_sleep_seconds", 2.0))
                if pre_join_sleep > 0:
                    self.input.sleep(pre_join_sleep)
                try:
                    server = self.servers.next_server()
                except ApiRateLimited:
                    self.discord_notify("Hopping Server", "Random public server")
                    self.servers.join_random_public(self.dry_run)
                else:
                    self.discord_notify("Hopping Server", "Public server")
                    self.servers.join(server, self.dry_run)
                self.input.wait_for_roblox(10)
                self.input.focus_roblox()
                self.wait_until_loaded()
                self.initialize_stinger_tracking()
                self.discord_notify(
                    "Game Loaded",
                    "Checking night",
                )
                status = self.detector.rejoin_status_visible()
                if status:
                    print(f"Detected '{status}'. Rejoin pe alt server.", flush=True)
                    continue
                is_night = self.dry_run or self.detect_night()
                night_screenshot = self.detector.roblox_shot() if is_night else None
                self.discord_notify(
                    "Night Detected" if is_night else "Daytime Detected",
                    "Starting hive and fields"
                    if is_night
                    else "Rejoining",
                    screenshot=night_screenshot,
                )
                if is_night:
                    self.stats_increment("night_servers")
                    print("Night detected. Starting Vicious search.", flush=True)
                    self.start_global_defeated_monitor()
                    try:
                        self.claim_hive_if_needed()
                        self.raise_if_global_vicious_defeated("field chain")
                        self.input.reset_camera_after_hive_claim()
                        self.raise_if_global_vicious_defeated("field chain")
                        self.vic_path()
                    finally:
                        self.stop_global_defeated_monitor()
                    return
                print("Nu este noapte. Rejoin pe alt server.", flush=True)
            except RejoinRequested as exc:
                print(f"{exc}. Rejoin pe alt server.", flush=True)
                continue
        raise RuntimeError(f"Nu am gasit noapte dupa {max_rejoins} rejoin-uri.")

    def wait_after_join(self, seconds: float):
        if self.dry_run:
            self.input.sleep(seconds)
            return
        interval = float(self.cfg.get("status_check_interval_seconds", 4))
        end = time.time() + seconds
        while time.time() < end:
            self.input.sleep(min(interval, end - time.time()))
            if self.dry_run:
                continue
            status = self.detector.rejoin_status_visible()
            if status:
                raise RejoinRequested(f"Detected '{status}'")

    def wait_until_loaded(self) -> None:
        if self.dry_run:
            self.input.sleep(float(self.cfg.get("join_wait_seconds", 18)))
            return
        if not self.cfg.get("load_detection.enabled", True):
            self.wait_after_join(float(self.cfg.get("join_wait_seconds", 18)))
            return

        cfg = self.cfg.get("load_detection", {}) or {}
        timeout = float(cfg.get("timeout_seconds", 60))
        timeout_after_blue = max(timeout, float(cfg.get("timeout_after_blue_seconds", 45)))
        transition_grace = float(cfg.get("join_transition_grace_seconds", 15.0))
        interval = float(cfg.get("sample_interval_seconds", 1))

        require_appear = bool(cfg.get("blue_loading_appear_required", True))
        disappear_needed = int(cfg.get("blue_disappear_samples", 2))
        loaded_needed = int(cfg.get("loaded_required_samples", 2))

        print("Waiting for real load state: join transition, blue screen gone, and Bee Swarm HUD visible", flush=True)
        start = time.time()
        appeared = False
        disappeared_samples = 0
        loaded_samples = 0
        while time.time() - start < (timeout_after_blue if appeared else timeout):
            self.input.sleep(interval)
            status = self.detector.rejoin_status_visible()
            if status:
                raise RejoinRequested(f"Detected '{status}'")
            visible = self.detector.blue_loading_visible()
            elapsed = time.time() - start
            if visible:
                appeared = True
                disappeared_samples = 0
                loaded_samples = 0
                print(f"load check: {elapsed:.0f}s blue loading visible", flush=True)
                continue
            loaded_visible = self.detector.loaded_screen_visible()
            if not appeared and elapsed < transition_grace:
                loaded_samples = 0
                print(
                    f"load check: {elapsed:.1f}s waiting for join transition "
                    f"{elapsed:.1f}/{transition_grace:.1f}s before accepting HUD",
                    flush=True,
                )
                continue
            if appeared:
                disappeared_samples += 1
                print(
                    f"load check: {elapsed:.0f}s blue disappeared {disappeared_samples}/{disappear_needed}",
                    flush=True,
                )
                if disappeared_samples < disappear_needed or not loaded_visible:
                    loaded_samples = 0
                    print(f"load check: {elapsed:.0f}s waiting for Bee Swarm HUD after blue", flush=True)
                    continue
            if loaded_visible:
                loaded_samples += 1
                print(
                    f"load check: {elapsed:.0f}s Bee Swarm HUD visible {loaded_samples}/{loaded_needed}",
                    flush=True,
                )
                if loaded_samples >= loaded_needed:
                    print("Bee Swarm HUD detected. Game is loaded.", flush=True)
                    return
            else:
                loaded_samples = 0
                print(f"load check: {elapsed:.0f}s waiting for blue loading or Bee Swarm HUD", flush=True)
        if cfg.get("rejoin_on_timeout", True):
            raise RejoinRequested(f"Game/textures did not load within {timeout:.0f}s")
        print("Load wait timed out; continuing with night check.", flush=True)

    def prepare_night_check_camera(self):
        self.input.focus_roblox()
        self.input.setup_camera_for_night_check()
        self.input.sleep(float(self.cfg.get("camera_setup.night_after_camera_delay_seconds", 0.04)))

    def restore_after_night_check_camera(self):
        cfg = self.cfg.get("camera_setup", {}) or {}
        if not cfg.get("restore_after_night_check", True):
            return
        hold = float(cfg.get("night_key_hold_seconds", cfg.get("key_hold_seconds", 0.06)))
        gap = float(cfg.get("night_between_keys_seconds", cfg.get("between_keys_seconds", 0.025)))
        rot_up_presses = int(cfg.get("night_restore_rot_up_presses", cfg.get("rot_down_presses", 3)))
        zoom_out_presses = int(cfg.get("night_restore_zoom_out_presses", 2))
        if rot_up_presses > 0:
            self.input.press_camera_key("rot_up", rot_up_presses, hold, gap)
        if zoom_out_presses > 0:
            self.input.press_camera_key("zoom_out", zoom_out_presses, hold, gap)

    def detect_night(self, restore_camera: bool = True) -> bool:
        self.prepare_night_check_camera()
        night = self.detector.is_night()
        print(f"Night detected: {night}", flush=True)
        if restore_camera:
            self.restore_after_night_check_camera()
        return night

    def detect_night_or_stop(self):
        if not self.dry_run and not self.detect_night():
            raise RuntimeError("Nu pare sa fie noapte. Vicious Bee apare doar noaptea.")
        print("Night detected or dry-run active.", flush=True)

    def custom_path_dir(self) -> Path:
        folder = str(self.cfg.get("paths.folder", "paths") or "paths")
        path = Path(folder)
        if not path.is_absolute():
            path = self.cfg.base_dir / path
        return path

    def custom_path_file(self) -> Path | None:
        selected = str(self.cfg.get("paths.active", "") or "").strip()
        if not selected:
            return None
        path = Path(selected)
        if not path.is_absolute():
            path = self.custom_path_dir() / path
        return path

    def run_custom_path_if_enabled(self) -> bool:
        if not self.cfg.get("paths.enabled", False):
            return False
        path = self.custom_path_file()
        if path is None:
            print("Custom paths enabled, dar paths.active este gol.", flush=True)
            return False
        self.run_custom_path(path)
        return True

    def find_named_path(self, stem: str) -> Path | None:
        folder = self.custom_path_dir()
        for suffix in (".ahk", ".txt", ".json"):
            candidate = folder / f"{stem}{suffix}"
            if candidate.exists():
                return candidate
        return None

    def hive_slot_path_dir(self) -> Path:
        folder = str(self.cfg.get("hive.slot_path_folder", "paths/hives") or "paths/hives")
        path = Path(folder)
        if not path.is_absolute():
            path = self.cfg.base_dir / path
        return path

    def find_hive_slot_path(self, slot: int) -> Path | None:
        stem = f"hive{slot}"
        folders = [self.hive_slot_path_dir(), self.custom_path_dir()]
        seen: set[Path] = set()
        for folder in folders:
            if folder in seen:
                continue
            seen.add(folder)
            for suffix in (".ahk", ".txt", ".json"):
                candidate = folder / f"{stem}{suffix}"
                if candidate.exists():
                    return candidate
        return None

    def run_custom_path(
        self,
        path: Path,
        focus_first: bool = True,
        variables: dict | None = None,
        monitor_callback: Callable[[], bool] | None = None,
        monitor_label: str = "path monitor",
        monitor_during_sleep: bool = True,
        monitor_stop_mode: str = "immediate",
        spike_avoidance: bool = False,
    ) -> str:
        if not path.exists():
            raise FileNotFoundError(f"Path file missing: {path}")
        variables = dict(variables or {})
        if "HiveSlot" not in variables and "hiveslot" not in variables and self.claimed_hive_slot is not None:
            variables["HiveSlot"] = self.claimed_hive_slot
            print(f"Path variable HiveSlot={self.claimed_hive_slot} from claimed hive.", flush=True)
        if "HiveSlot" not in variables:
            match = re.search(r"(?i)hive\s*([1-6])", path.stem)
            if match:
                variables["HiveSlot"] = int(match.group(1))
        text = path.read_text(encoding="utf-8-sig")
        if path.suffix.lower() == ".json" or text.lstrip().startswith(("{", "[")):
            data = json.loads(text)
            if isinstance(data, dict):
                name = str(data.get("name", path.stem))
                steps = data.get("steps", [])
            else:
                name = path.stem
                steps = data
        else:
            name = path.stem
            steps = self.parse_simple_path(text, path, variables=variables)
        if not isinstance(steps, list):
            raise ValueError(f"Path file invalid: {path}. 'steps' trebuie sa fie lista.")
        print(f"Running custom path '{name}' from {path} dry_run={self.dry_run}", flush=True)
        old_input_verbose = getattr(self.input, "verbose", True)
        self.input.verbose = bool(self.cfg.get("paths.verbose_input", False))
        result = "finished"
        safe_point_index = 0
        self.last_path_safepoint_index = None
        speed_monitor_started_here = False
        if self._speed_monitor_thread is None or not self._speed_monitor_thread.is_alive():
            self.start_speed_monitor()
            speed_monitor_started_here = self._speed_monitor_thread is not None and self._speed_monitor_thread.is_alive()
        using_global_defeated_monitor = False
        if monitor_callback is None and self.global_vicious_defeated_detected():
            monitor_callback = self.global_vicious_defeated_detected
            monitor_label = "Global Vicious defeated message"
            monitor_during_sleep = True
            monitor_stop_mode = "immediate"
            using_global_defeated_monitor = True
        elif monitor_callback is None and self._global_defeated_monitor_thread is not None:
            monitor_callback = self.global_vicious_defeated_detected
            monitor_label = "Global Vicious defeated message"
            monitor_during_sleep = True
            monitor_stop_mode = "immediate"
            using_global_defeated_monitor = True
        monitor_stop_mode = str(monitor_stop_mode or "immediate").lower().strip()
        try:
            if focus_first:
                self.input.focus_roblox()
                self.input.sleep(float(self.cfg.get("paths.focus_wait_seconds", 0.35)))
            try:
                for index, step in enumerate(steps, start=1):
                    self.input.check_stop()
                    self.run_path_step(
                        index,
                        step,
                        monitor_callback=monitor_callback,
                        monitor_label=monitor_label,
                        monitor_during_sleep=monitor_during_sleep and monitor_stop_mode == "immediate",
                        spike_avoidance=spike_avoidance,
                    )
                    if monitor_callback is not None and monitor_stop_mode == "safe_point":
                        action = str(step.get("action", "")).lower().strip() if isinstance(step, dict) else ""
                        if action == "safe_point":
                            safe_point_index += 1
                        if action == "safe_point" and monitor_callback():
                            self.last_path_safepoint_index = safe_point_index
                            raise PathMonitorTriggered(f"{monitor_label}: detected at safe point")
                    if monitor_callback is not None and not monitor_during_sleep:
                        action = str(step.get("action", "")).lower().strip() if isinstance(step, dict) else ""
                        if action in {"walk", "walk_combo", "hold", "hold_combo", "movement_sleep", "key_up", "press", "camera", "goto_ramp"}:
                            if monitor_callback():
                                raise PathMonitorTriggered(f"{monitor_label}: detected")
            except PathMonitorTriggered as exc:
                result = "monitor_triggered"
                self.input.release_path_keys()
                print(str(exc), flush=True)
            except PathComplete as exc:
                result = "path_complete"
                self.input.release_path_keys()
                print(str(exc), flush=True)
        finally:
            if speed_monitor_started_here:
                self.stop_speed_monitor()
            self.input.verbose = old_input_verbose
        print(f"Custom path '{name}' finished ({result}).", flush=True)
        if using_global_defeated_monitor and self.global_vicious_defeated_detected():
            self.raise_if_global_vicious_defeated("field chain")
        return result

    def parse_simple_path(self, text: str, path: Path, variables: dict | None = None) -> list[dict]:
        steps: list[dict] = []
        variables = dict(variables or {})
        if "HiveSlot" not in variables and "hiveslot" not in variables:
            match = re.search(r"(?i)hive\s*([1-6])", path.stem)
            if match:
                variables["HiveSlot"] = int(match.group(1))
        aliases = {
            "fwdkey": "forward",
            "forwardkey": "forward",
            "w": "forward",
            "backkey": "backward",
            "backwardkey": "backward",
            "s": "backward",
            "leftkey": "left",
            "a": "left",
            "rightkey": "right",
            "d": "right",
            "space": "space",
            "spacekey": "space",
            "sc_space": "space",
            "e": "e",
            "sc_e": "e",
            "r": "r",
            "sc_r": "r",
            "enter": "enter",
            "return": "enter",
            "sc_enter": "enter",
            "escape": "escape",
            "esc": "escape",
            "shift": "shift",
            "lshift": "shift",
            "rshift": "shift",
            "shiftleft": "shift",
            "shiftright": "shift",
            "sc_lshift": "shift",
            "sc_rshift": "shift",
            "rotleft": "rot_left",
            "rotright": "rot_right",
            "rotdown": "rot_down",
            "pagedown": "rot_down",
            "pgdn": "rot_down",
            "sc_pagedown": "rot_down",
            "sc_pgdn": "rot_down",
            "rotup": "rot_up",
            "pageup": "rot_up",
            "pgup": "rot_up",
            "sc_pageup": "rot_up",
            "sc_pgup": "rot_up",
            "zoomin": "zoom_in",
            "zoomout": "zoom_out",
        }

        def clean_line(raw: str) -> str:
            in_quote = False
            out = []
            for ch in raw.strip():
                if ch == '"':
                    in_quote = not in_quote
                if ch == ";" and not in_quote:
                    break
                out.append(ch)
            return "".join(out).strip()

        def key_name(token: str) -> str:
            key = token.strip().strip("{}").strip().lower()
            key = key.replace(" ", "").replace("_", "")
            return aliases.get(key, token.strip().strip("{}").strip().lower())

        def hive_slot_value(default: int = 3) -> int:
            value = variables.get("HiveSlot", variables.get("hiveslot", default))
            try:
                slot = int(float(value))
            except (TypeError, ValueError):
                slot = default
            return max(1, min(6, slot))

        movement_keys = {"forward", "backward", "left", "right"}
        active_keys: set[str] = set()
        speed_scale_enabled = True

        for line_no, raw in enumerate(text.splitlines(), start=1):
            line = clean_line(raw)
            if not line or line in {"{", "}"}:
                continue

            speed_scale = re.fullmatch(
                r"(?i)(?:SpeedScale|MoveSpeedScale|ScaleMovement|ScaleSleep)\s*\(\s*(on|off|true|false|1|0)?\s*\)",
                line,
            )
            if speed_scale:
                value = (speed_scale.group(1) or "on").lower()
                speed_scale_enabled = value in {"on", "true", "1"}
                steps.append({
                    "action": "log",
                    "message": f"Speed scaling {'ON' if speed_scale_enabled else 'OFF'} at {path.name}:{line_no}",
                    "note": f"{path.name}:{line_no}",
                })
                continue

            speed_scale_off = re.fullmatch(r"(?i)(?:SpeedScaleOff|NoSpeedScale|GliderStart|StartGlider)\s*\(\s*\)", line)
            if speed_scale_off:
                speed_scale_enabled = False
                steps.append({
                    "action": "log",
                    "message": f"Speed scaling OFF at {path.name}:{line_no}",
                    "note": f"{path.name}:{line_no}",
                })
                continue

            speed_scale_on = re.fullmatch(r"(?i)(?:SpeedScaleOn|UseSpeedScale|GliderEnd|EndGlider)\s*\(\s*\)", line)
            if speed_scale_on:
                speed_scale_enabled = True
                steps.append({
                    "action": "log",
                    "message": f"Speed scaling ON at {path.name}:{line_no}",
                    "note": f"{path.name}:{line_no}",
                })
                continue

            safe_point = re.fullmatch(r"(?i)(?:SafePoint|Safe_Point|VicSafePoint|Checkpoint)\s*\(\s*\)", line)
            if safe_point:
                steps.append({"action": "safe_point", "note": f"{path.name}:{line_no}"})
                continue

            stop_path = re.fullmatch(r"(?i)(?:StopPath|PathStop|StopHere)\s*\(\s*\)", line)
            if stop_path:
                steps.append({"action": "stop_path", "note": f"{path.name}:{line_no}"})
                continue

            test_vicious_found = re.fullmatch(
                r"(?i)(?:TestViciousFound|TriggerViciousFound|FakeViciousFound)\s*\(\s*\)",
                line,
            )
            if test_vicious_found:
                steps.append({"action": "test_vicious_found", "note": f"{path.name}:{line_no}"})
                continue

            goto_ramp = re.fullmatch(r"(?i)nm_gotoRamp\s*\(\s*(?:(\d+))?\s*\)", line)
            if goto_ramp:
                slot = int(goto_ramp.group(1)) if goto_ramp.group(1) else hive_slot_value()
                steps.append({"action": "goto_ramp", "hive_slot": max(1, min(6, slot)), "note": f"{path.name}:{line_no}"})
                continue

            camera = re.fullmatch(
                r"(?i)nm_Camera\s*\(\s*([A-Za-z_]+)\s*(?:,\s*([0-9]+))?\s*\)",
                line,
            )
            if camera:
                camera_key = key_name(camera.group(1))
                camera_aliases = {
                    "left": "rot_left",
                    "right": "rot_right",
                    "down": "rot_down",
                    "up": "rot_up",
                    "rotleft": "rot_left",
                    "rotright": "rot_right",
                    "rotdown": "rot_down",
                    "rotup": "rot_up",
                }
                camera_key = camera_aliases.get(camera_key.replace("_", ""), camera_key)
                if camera_key not in {"rot_left", "rot_right", "rot_down", "rot_up", "zoom_in", "zoom_out"}:
                    raise ValueError(f"nm_Camera invalid in {path}, linia {line_no}: key '{camera.group(1)}'")
                presses = int(camera.group(2)) if camera.group(2) else 1
                steps.append({"action": "camera", "key": camera_key, "presses": max(0, presses), "note": f"{path.name}:{line_no}"})
                continue

            walk = re.fullmatch(r"(?i)nm_Walk\s*\(\s*([0-9]+(?:\.[0-9]+)?)\s*,\s*(.+?)\s*\)", line)
            if walk:
                studs = float(walk.group(1))
                keys = [key_name(part) for part in walk.group(2).split(",") if part.strip()]
                if not speed_scale_enabled and len(keys) == 1:
                    steps.append({
                        "action": "hold",
                        "key": keys[0],
                        "seconds": studs / PATH_REFERENCE_SPEED,
                        "note": f"{path.name}:{line_no}",
                    })
                elif not speed_scale_enabled and len(keys) > 1:
                    steps.append({
                        "action": "hold_combo",
                        "keys": keys,
                        "seconds": studs / PATH_REFERENCE_SPEED,
                        "note": f"{path.name}:{line_no}",
                    })
                elif len(keys) == 1:
                    steps.append({"action": "walk", "direction": keys[0], "studs": studs, "note": f"{path.name}:{line_no}"})
                elif len(keys) > 1:
                    steps.append({"action": "walk_combo", "keys": keys, "studs": studs, "note": f"{path.name}:{line_no}"})
                continue

            sleep = re.fullmatch(r"(?i)(?:HyperSleep|Sleep)\s*\(\s*([0-9]+(?:\.[0-9]+)?)\s*\)", line)
            if sleep:
                seconds = float(sleep.group(1)) / 1000.0
                moving_keys = sorted(active_keys & movement_keys)
                if moving_keys:
                    steps.append({
                        "action": "movement_sleep",
                        "seconds": seconds,
                        "keys": moving_keys,
                        "scale": speed_scale_enabled,
                        "note": f"{path.name}:{line_no}",
                    })
                else:
                    steps.append({"action": "sleep", "seconds": seconds, "note": f"{path.name}:{line_no}"})
                continue

            send = re.fullmatch(r"(?i)(?:send|sendinput)\s+\"?\{([^}]+)\}\"?", line)
            if send:
                parts = send.group(1).strip().split()
                key = key_name(parts[0])
                mode = parts[1].lower() if len(parts) > 1 else ""
                if mode == "down":
                    steps.append({"action": "key_down", "key": key, "note": f"{path.name}:{line_no}"})
                    active_keys.add(key)
                elif mode == "up":
                    steps.append({"action": "key_up", "key": key, "note": f"{path.name}:{line_no}"})
                    active_keys.discard(key)
                else:
                    repeats = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 1
                    steps.append({"action": "press", "key": key, "repeats": repeats, "note": f"{path.name}:{line_no}"})
                continue

            detect = re.fullmatch(r"(?i)detect\s*\(\s*([a-z_]+)\s*(?:,\s*(kill|stop|continue))?\s*\)", line)
            if detect:
                mode = (detect.group(2) or "stop").lower()
                steps.append({
                    "action": "detect",
                    "field": detect.group(1).lower(),
                    "kill_if_found": mode == "kill",
                    "stop_if_found": mode != "continue",
                    "note": f"{path.name}:{line_no}",
                })
                continue

            chain = re.fullmatch(r"(?i)(?:detect_vicious_chain|vicious_chain|vic_chain)\s*\(\s*([a-z_]+)\s*\)", line)
            if chain:
                steps.append({
                    "action": "detect_vicious_chain",
                    "field": chain.group(1).lower(),
                    "note": f"{path.name}:{line_no}",
                })
                continue

            raise ValueError(f"Path simplu invalid in {path}, linia {line_no}: {raw}")
        return steps

    def monitored_path_sleep(
        self,
        seconds: float,
        monitor_callback: Callable[[], bool] | None = None,
        monitor_label: str = "path monitor",
        spike_avoidance: bool = False,
    ) -> None:
        try:
            requested = float(seconds)
        except (TypeError, ValueError):
            return
        if requested <= 0:
            return
        if monitor_callback is None:
            end = time.time() + requested
            while time.time() < end:
                self.input.check_stop()
                if self.global_vicious_defeated_detected():
                    raise PathMonitorTriggered("Global Vicious defeated message: detected")
                if spike_avoidance and self.avoid_spikes_if_needed():
                    end = time.time() + max(0.0, end - time.time())
                self.input.sleep(min(0.05, max(0.0, end - time.time())))
            return
        end = time.time() + requested
        interval_key = (
            "vicious_detection.defeated_message_poll_seconds"
            if "defeated" in str(monitor_label).lower()
            else "vicious_detection.attack_message_poll_seconds"
        )
        default_interval = 0.2 if "defeated" in str(monitor_label).lower() else 0.05
        interval = max(0.02, float(self.cfg.get(interval_key, default_interval)))
        while time.time() < end:
            self.input.check_stop()
            if self.global_vicious_defeated_detected():
                raise PathMonitorTriggered("Global Vicious defeated message: detected")
            if monitor_callback():
                raise PathMonitorTriggered(f"{monitor_label}: detected")
            if spike_avoidance and self.avoid_spikes_if_needed():
                end = time.time() + max(0.0, end - time.time())
            self.input.sleep(min(interval, max(0.0, end - time.time())))

    def monitored_scaled_movement_sleep(
        self,
        reference_seconds: float,
        scale_provider: Callable[[], tuple[float, float, float, SpeedAnalysis]],
        monitor_callback: Callable[[], bool] | None = None,
        monitor_label: str = "path monitor",
        spike_avoidance: bool = False,
    ) -> dict[str, float]:
        """Consume path time using measured wall time, like Natro's distance integrator."""
        target = max(0.0, float(reference_seconds))
        if target <= 0.0:
            return {"wall_seconds": 0.0, "reference_seconds": 0.0, "speed_min": 0.0, "speed_max": 0.0}

        interval = max(0.005, min(0.05, float(self.cfg.get("paths.movement_integrator_interval_seconds", 0.015))))
        applied_scale, multiplier, flat_bonus, _speed_info = scale_provider()
        speed, _ = effective_walk_speed(
            float(self.cfg.get("move_speed_studs_per_second", 29.0)),
            multiplier,
            flat_bonus,
        )
        previous_rate = 1.0 / max(0.001, applied_scale)
        progress = 0.0
        speed_min = speed
        speed_max = speed
        started_at = time.perf_counter()
        previous_at = started_at

        while progress < target:
            self.input.check_stop()
            if self.global_vicious_defeated_detected():
                raise PathMonitorTriggered("Global Vicious defeated message: detected")
            if monitor_callback is not None and monitor_callback():
                raise PathMonitorTriggered(f"{monitor_label}: detected")
            if spike_avoidance:
                self.avoid_spikes_if_needed()

            applied_scale, multiplier, flat_bonus, _speed_info = scale_provider()
            speed, _ = effective_walk_speed(
                float(self.cfg.get("move_speed_studs_per_second", 29.0)),
                multiplier,
                flat_bonus,
            )
            speed_min = min(speed_min, speed)
            speed_max = max(speed_max, speed)
            current_rate = 1.0 / max(0.001, applied_scale)
            now = time.perf_counter()
            elapsed = max(0.0, now - previous_at)
            progress += elapsed * (previous_rate + current_rate) * 0.5
            previous_at = now
            previous_rate = current_rate
            if progress >= target:
                break

            remaining_wall = (target - progress) / max(0.001, current_rate)
            self.input.sleep(min(interval, remaining_wall))

        return {
            "wall_seconds": max(0.0, time.perf_counter() - started_at),
            "reference_seconds": progress,
            "speed_min": speed_min,
            "speed_max": speed_max,
        }

    def run_path_step(
        self,
        index: int,
        step: dict,
        monitor_callback: Callable[[], bool] | None = None,
        monitor_label: str = "path monitor",
        monitor_during_sleep: bool = True,
        spike_avoidance: bool = False,
    ):
        if not isinstance(step, dict):
            raise ValueError(f"Path step {index} invalid: trebuie object JSON.")
        action = str(step.get("action", "")).lower().strip()
        note = str(step.get("note", "") or "")
        suffix = f" - {note}" if note else ""
        if bool(self.cfg.get("paths.verbose_steps", False)):
            print(f"path step {index}: {action}{suffix}", flush=True)
        if self.global_vicious_defeated_detected():
            raise PathMonitorTriggered("Global Vicious defeated message: detected")
        if spike_avoidance:
            self.avoid_spikes_if_needed()

        if action == "walk":
            if spike_avoidance:
                self.input.walk(
                    str(step["direction"]),
                    float(step["studs"]),
                    tick_callback=self.avoid_spikes_if_needed,
                    tick_interval=float(self.cfg.get("spike_avoidance.walk_tick_seconds", 0.05)),
                )
            else:
                self.input.walk(str(step["direction"]), float(step["studs"]))
            if spike_avoidance:
                self.avoid_spikes_if_needed()
            return
        if action == "hold":
            key = str(step["key"])
            seconds = float(step.get("seconds", 0.1))
            self.input.key_down(key)
            try:
                self.monitored_path_sleep(
                    seconds,
                    monitor_callback if monitor_during_sleep else None,
                    monitor_label,
                    spike_avoidance=spike_avoidance,
                )
            finally:
                self.input.key_up(key)
            return
        if action == "hold_combo":
            keys = [str(key) for key in step.get("keys", [])]
            seconds = float(step.get("seconds", 0.1))
            for key in keys:
                self.input.key_down(key)
            try:
                self.monitored_path_sleep(
                    seconds,
                    monitor_callback if monitor_during_sleep else None,
                    monitor_label,
                    spike_avoidance=spike_avoidance,
                )
            finally:
                for key in reversed(keys):
                    self.input.key_up(key)
            return
        if action == "walk_combo":
            keys = [str(key) for key in step.get("keys", [])]
            studs = float(step.get("studs", 0.0))
            multiplier, flat_bonus = self.current_speed_adjustment()
            speed, speed_info = effective_walk_speed(
                float(self.cfg.get("move_speed_studs_per_second", 29.0)),
                multiplier,
                flat_bonus,
            )
            time_multiplier = path_movement_time_multiplier(self.cfg)
            seconds = max(0.02, studs / speed * time_multiplier)
            self.input.log(
                f"walk combo {','.join(keys) or '?'} {studs:.1f} studs "
                f"(speed {speed:.1f}, manual {speed_info.input_speed:.1f}, "
                f"buff x{multiplier:.2f}, +{flat_bonus:.1f}, cal x{time_multiplier:.3f}, "
                f"scale {PATH_REFERENCE_SPEED / speed * time_multiplier:.3f}, {seconds:.2f}s)"
            )
            for key in keys:
                self.input.key_down(key)
            try:
                self.monitored_path_sleep(
                    seconds,
                    monitor_callback if monitor_during_sleep else None,
                    monitor_label,
                    spike_avoidance=spike_avoidance,
                )
            finally:
                for key in reversed(keys):
                    self.input.key_up(key)
            return
        if action == "goto_ramp":
            self.goto_ramp(int(step.get("hive_slot", 3)))
            return
        if action == "key_down":
            self.input.key_down(str(step["key"]))
            return
        if action == "key_up":
            self.input.key_up(str(step["key"]))
            return
        if action == "press":
            self.input.press(
                str(step["key"]),
                repeats=int(step.get("repeats", 1)),
                interval=float(step.get("interval", 0.08)),
            )
            return
        if action == "camera":
            cfg = self.cfg.get("camera_setup", {}) or {}
            self.input.press_camera_key(
                str(step["key"]),
                int(step.get("presses", 1)),
                float(step.get("hold", cfg.get("key_hold_seconds", 0.12))),
                float(step.get("gap", cfg.get("between_keys_seconds", 0.08))),
            )
            return
        if action == "sleep":
            self.monitored_path_sleep(
                float(step.get("seconds", 0.1)),
                monitor_callback if monitor_during_sleep else None,
                monitor_label,
                spike_avoidance=spike_avoidance,
            )
            return
        if action == "movement_sleep":
            original_seconds = float(step.get("seconds", 0.1))
            scale_enabled = bool(step.get("scale", True))
            strength = max(0.0, min(1.0, float(self.cfg.get("paths.movement_sleep_speed_scale_strength", 1.0))))
            time_multiplier = path_movement_time_multiplier(self.cfg)

            def current_scale() -> tuple[float, float, float, SpeedAnalysis]:
                multiplier, flat_bonus = self.current_speed_adjustment()
                speed, speed_info = effective_walk_speed(
                    float(self.cfg.get("move_speed_studs_per_second", 29.0)),
                    multiplier,
                    flat_bonus,
                )
                raw_scale = PATH_REFERENCE_SPEED / speed
                applied_scale = (
                    1.0
                    if not scale_enabled
                    else (1.0 + (raw_scale - 1.0) * strength) * time_multiplier
                )
                return max(0.001, applied_scale), multiplier, flat_bonus, speed_info

            applied_scale, multiplier, flat_bonus, speed_info = current_scale()
            speed, _ = effective_walk_speed(
                float(self.cfg.get("move_speed_studs_per_second", 29.0)),
                multiplier,
                flat_bonus,
            )
            raw_scale = PATH_REFERENCE_SPEED / speed
            scaled_seconds = max(0.001, original_seconds * applied_scale)
            keys = ",".join(str(key) for key in step.get("keys", []))
            self.input.log(
                f"movement sleep {keys or '?'} {original_seconds:.3f}s -> {scaled_seconds:.3f}s "
                f"(speed {speed:.1f}, manual {speed_info.input_speed:.1f}, "
                f"buff x{multiplier:.2f}, +{flat_bonus:.1f}, "
                f"scale {applied_scale:.3f}, raw {raw_scale:.3f}, cal x{time_multiplier:.3f}, "
                f"strength {strength:.2f}, "
                f"{'enabled' if scale_enabled else 'disabled'})"
            )
            if not scale_enabled:
                self.monitored_path_sleep(
                    scaled_seconds,
                    monitor_callback if monitor_during_sleep else None,
                    monitor_label,
                    spike_avoidance=spike_avoidance,
                )
                return

            timing = self.monitored_scaled_movement_sleep(
                original_seconds,
                current_scale,
                monitor_callback if monitor_during_sleep else None,
                monitor_label,
                spike_avoidance=spike_avoidance,
            )
            if bool(self.cfg.get("paths.log_movement_timing", True)):
                print(
                    f"PATH_MOVE keys={keys or '?'} source={original_seconds:.6f}s "
                    f"actual={timing['wall_seconds']:.6f}s integrated={timing['reference_seconds']:.6f}s "
                    f"speed={timing['speed_min']:.3f}..{timing['speed_max']:.3f} "
                    f"target_scale={applied_scale:.6f}{suffix}",
                    flush=True,
                )
            return
        if action == "safe_point":
            return
        if action == "stop_path":
            raise PathComplete(f"Path oprit manual la {note or index}.")
        if action == "test_vicious_found":
            raise PathMonitorTriggered(f"Vicious attack message: test trigger at {note or index}")
        if action == "detect":
            field = str(step.get("field", ""))
            found = self.maybe_detect(field)
            if found and bool(step.get("kill_if_found", False)):
                print(f"Vicious detected in {field}. Starting kill loop.", flush=True)
                self.kill_loop()
                raise PathComplete(f"Vicious din '{field}' terminat. Path oprit.")
            if found and bool(step.get("stop_if_found", True)):
                raise PathComplete(f"Vicious detectat in field '{field}'. Path oprit.")
            return
        if action == "detect_vicious_chain":
            print("detect_vicious_chain din path este ignorat; chain-ul de fielduri este controlat de macro.", flush=True)
            return
        if action == "log":
            print(str(step.get("message", "")), flush=True)
            return
        raise ValueError(f"Path step {index}: action necunoscut '{action}'")

    def normalize_field_name(self, field: str) -> str:
        field_key = str(field or "").lower().replace(" ", "").replace("_", "")
        aliases = {
            "mountain": "mountaintop",
            "mountaintopfield": "mountaintop",
            "mountaintop": "mountaintop",
            "pepperpatch": "pepper",
            "pepper": "pepper",
            "spiderfield": "spider",
            "spider": "spider",
            "cactusfield": "cactus",
            "cactus": "cactus",
            "rosefield": "rose",
            "rose": "rose",
        }
        return aliases.get(field_key, field_key)

    def field_path_candidates(self, field: str) -> list[str]:
        normalized = self.normalize_field_name(field)
        if normalized == "mountaintop":
            return ["mountaintop", "mountain"]
        return [normalized]

    def find_field_path(self, field: str) -> Path | None:
        folders = [self.custom_path_dir()]
        hive_folder = self.hive_slot_path_dir()
        if hive_folder not in folders:
            folders.append(hive_folder)
        for folder in folders:
            for stem in self.field_path_candidates(field):
                for suffix in (".ahk", ".txt", ".json"):
                    candidate = folder / f"{stem}{suffix}"
                    if candidate.exists():
                        return candidate
        return None

    def vicious_path_dirs(self) -> list[Path]:
        folders = []
        for value in (
            self.cfg.get("vicious_detection.vicfind_path_folder", "paths/vicfind"),
            self.cfg.get("paths.folder", "paths"),
        ):
            folder = Path(str(value or ""))
            if not folder.is_absolute():
                folder = self.cfg.base_dir / folder
            if folder not in folders:
                folders.append(folder)
        return folders

    def find_vicious_spawn_path(self, field: str) -> Path | None:
        normalized = self.normalize_field_name(field)
        names_by_field = {
            "pepper": ["PepAndMtVicFind", "pepperVicFind", "pepper_vicfind"],
            "mountaintop": ["PepAndMtVicFind", "mountaintopVicFind", "mountainVicFind", "mountaintop_vicfind"],
            "cactus": ["cacVicFind", "cactusVicFind", "cactus_vicfind"],
            "rose": ["roseVicFind", "rose_vicfind"],
            "spider": ["spiderVicFind", "spider_vicfind"],
        }
        for folder in self.vicious_path_dirs():
            for stem in names_by_field.get(normalized, [f"{normalized}VicFind", f"{normalized}_vicfind"]):
                for suffix in (".ahk", ".txt", ".json"):
                    candidate = folder / f"{stem}{suffix}"
                    if candidate.exists():
                        return candidate
        return None

    def find_vicious_kill_path(self) -> Path | None:
        for folder in self.vicious_path_dirs():
            for stem in ("killVic", "viciousKill", "vicKill", "kill_vic"):
                for suffix in (".ahk", ".txt", ".json"):
                    candidate = folder / f"{stem}{suffix}"
                    if candidate.exists():
                        return candidate
        return None

    def find_vicious_after_found_path(self, field: str, safepoint_index: int | None = None) -> Path | None:
        normalized = self.normalize_field_name(field)
        suffixes: list[str] = []
        if safepoint_index is not None:
            try:
                index = int(safepoint_index)
            except (TypeError, ValueError):
                index = 0
            if index > 0:
                suffixes = [str(index), f"_{index}", f"SafePoint{index}", f"SP{index}"]
        names_by_field = {
            "pepper": ["pepperVicAfterFound", "pepperAfterFound", "pepperToKillVic", "PepAndMtVicAfterFound"],
            "mountaintop": [
                "mountaintopVicAfterFound",
                "mountainVicAfterFound",
                "mountaintopAfterFound",
                "mountainAfterFound",
                "mountaintopToKillVic",
                "mountainToKillVic",
                "PepAndMtVicAfterFound",
            ],
            "cactus": ["cactusVicAfterFound", "cacVicAfterFound", "cactusAfterFound", "cactusToKillVic"],
            "rose": ["roseVicAfterFound", "roseAfterFound", "roseToKillVic"],
            "spider": ["spiderVicAfterFound", "spiderAfterFound", "spiderToKillVic"],
        }
        fallback_names = [
            f"{normalized}VicAfterFound",
            f"{normalized}AfterFound",
            f"{normalized}ToKillVic",
            "vicAfterFound",
            "afterFoundVic",
        ]
        for folder in self.vicious_path_dirs():
            base_stems = names_by_field.get(normalized, fallback_names)
            stems: list[str] = []
            for stem in base_stems:
                for suffix in suffixes:
                    stems.append(f"{stem}{suffix}")
                stems.append(stem)
            for stem in stems:
                for suffix in (".ahk", ".txt", ".json"):
                    candidate = folder / f"{stem}{suffix}"
                    if candidate.exists():
                        return candidate
        return None

    def infer_vicious_field_from_path(self, path: Path) -> str:
        stem = path.stem.lower().replace("_", "").replace("-", "")
        name = path.name.lower().replace("_", "").replace("-", "")
        if "spider" in name:
            return "spider"
        if "rose" in name:
            return "rose"
        if "cactus" in name or stem.startswith("cac"):
            return "cactus"
        if "mountain" in name or "mt" in stem:
            return "mountaintop"
        if "pep" in name:
            return "pepper"
        return "pepper"

    def test_vicious_safepoint_path(self, path: Path, safepoint_index: int, field: str | None = None) -> str:
        if not path.exists():
            raise FileNotFoundError(f"Path file missing: {path}")
        text = path.read_text(encoding="utf-8-sig")
        steps = self.parse_simple_path(text, path)
        target = max(1, int(safepoint_index))
        safepoint_count = 0
        field = self.normalize_field_name(field) if field else self.infer_vicious_field_from_path(path)
        print(f"Testing SafePoint {target} from {path.name} field={field}", flush=True)

        old_input_verbose = getattr(self.input, "verbose", True)
        self.input.verbose = bool(self.cfg.get("paths.verbose_input", False))
        try:
            self.input.focus_roblox()
            self.input.sleep(float(self.cfg.get("paths.focus_wait_seconds", 0.35)))
            for index, step in enumerate(steps, start=1):
                self.input.check_stop()
                self.run_path_step(index, step)
                action = str(step.get("action", "")).lower().strip() if isinstance(step, dict) else ""
                if action == "safe_point":
                    safepoint_count += 1
                    print(f"Reached SafePoint {safepoint_count}/{target} at {step.get('note', path.name)}", flush=True)
                    if safepoint_count >= target:
                        self.input.release_path_keys()
                        after_found_path = self.find_vicious_after_found_path(field, target)
                        if after_found_path is None:
                            print(f"No after-found path for {field}. Test stopped at SafePoint {target}.", flush=True)
                            return "safe_point_only"
                        print(f"Running after-found path for {field}: {after_found_path}", flush=True)
                        result = self.run_custom_path(after_found_path, focus_first=False)
                        print(f"SafePoint test finished after after-found path ({result}).", flush=True)
                        return "after_found_finished"
            self.input.release_path_keys()
            print(f"SafePoint {target} not found. Path only has {safepoint_count} SafePoint markers.", flush=True)
            return "safe_point_missing"
        finally:
            self.input.release_path_keys()
            self.input.verbose = old_input_verbose

    def run_path_with_background_monitor(
        self,
        path: Path,
        *,
        focus_first: bool,
        monitor_callback: Callable[[], bool],
        monitor_label: str,
        poll_seconds: float,
        stop_mode: str = "immediate",
    ) -> str:
        detected = Event()
        stop_monitor = Event()
        stop_mode = str(stop_mode or "immediate").lower().strip()

        def monitor_loop():
            while not stop_monitor.is_set() and not detected.is_set():
                try:
                    if monitor_callback():
                        detected.set()
                        if stop_mode == "immediate":
                            self.input.release_path_keys()
                        return
                except Exception as exc:
                    print(f"{monitor_label}: monitor failed: {exc}", flush=True)
                stop_monitor.wait(max(0.05, float(poll_seconds)))

        monitor_thread = Thread(target=monitor_loop, daemon=True)
        monitor_thread.start()
        try:
            result = self.run_custom_path(
                path,
                focus_first=focus_first,
                monitor_callback=detected.is_set,
                monitor_label=monitor_label,
                monitor_during_sleep=True,
                monitor_stop_mode=stop_mode,
            )
            if result == "finished" and detected.is_set():
                return "monitor_triggered"
            return result
        finally:
            stop_monitor.set()
            monitor_thread.join(timeout=0.5)

    def run_vicious_spawn_and_kill(self, field: str) -> bool:
        normalized = self.normalize_field_name(field)
        spawn_path = self.find_vicious_spawn_path(normalized)
        if spawn_path is None:
            print(f"Vicious spawn path missing for {normalized}; skipping spawn/kill phase.", flush=True)
            return False
        print(f"Running Vicious spawn path for {normalized}: {spawn_path}", flush=True)
        self.discord_notify(f"Spawn {normalized.title()}", "Running field path")
        result = self.run_path_with_background_monitor(
            spawn_path,
            focus_first=True,
            monitor_callback=(lambda: False) if self.dry_run else self.detector.vicious_attack_message_visible,
            monitor_label="Vicious attack message",
            poll_seconds=float(self.cfg.get("vicious_detection.attack_message_ocr_interval_seconds", 0.2)),
            stop_mode=str(self.cfg.get("vicious_detection.spawn_path_monitor_stop_mode", "safe_point")),
        )
        if self.global_vicious_defeated_detected():
            self.notify_global_vicious_defeated_once(normalized)
            return True
        if result != "monitor_triggered":
            print(f"Vicious attack message not detected during {normalized} spawn path.", flush=True)
            return False

        self.discord_notify("Vicious Spawned", f"{normalized.title()} - attack message detected")
        safepoint_index = getattr(self, "last_path_safepoint_index", None)
        after_found_path = self.find_vicious_after_found_path(normalized, safepoint_index)
        if after_found_path is not None:
            print(f"Running Vicious after-found path for {normalized}: {after_found_path}", flush=True)
            safepoint_text = f" SafePoint {safepoint_index}" if safepoint_index else ""
            self.discord_notify("Vicious Positioning", f"{normalized.title()}{safepoint_text} - moving to kill start")
            after_found_result = self.run_custom_path(after_found_path, focus_first=False)
            if self.global_vicious_defeated_detected():
                self.notify_global_vicious_defeated_once(normalized)
                return True
            if after_found_result == "path_complete":
                print(f"Vicious after-found path stopped manually for {normalized}; skipping kill path.", flush=True)
                return False
        else:
            print(f"No Vicious after-found path for {normalized}; starting kill path from safe point.", flush=True)
        kill_path = self.find_vicious_kill_path()
        if kill_path is None:
            print("Vicious kill path missing; using built-in kill loop.", flush=True)
            self.kill_loop()
            return True

        timeout = float(self.cfg.get("vicious_detection.kill_path_timeout_seconds", 300.0))
        end = time.time() + max(5.0, timeout)
        round_index = 0
        print(f"Running Vicious kill path loop: {kill_path}", flush=True)
        defeated_detected = Event()
        stop_defeated_monitor = Event()

        def defeated_monitor_loop():
            poll_seconds = max(0.05, float(self.cfg.get("vicious_detection.defeated_message_poll_seconds", 0.2)))
            while not stop_defeated_monitor.is_set() and not defeated_detected.is_set():
                try:
                    if not self.dry_run and self.detector.defeated():
                        defeated_detected.set()
                        self.input.release_path_keys()
                        return
                except Exception as exc:
                    print(f"Vicious defeated message: monitor failed: {exc}", flush=True)
                stop_defeated_monitor.wait(poll_seconds)

        defeated_monitor_thread = Thread(target=defeated_monitor_loop, daemon=True)
        defeated_monitor_thread.start()
        try:
            while time.time() < end:
                self.input.check_stop()
                if self.global_vicious_defeated_detected():
                    self.notify_global_vicious_defeated_once(normalized)
                    return True
                if defeated_detected.is_set():
                    print("Vicious Bee defeated.", flush=True)
                    self.discord_notify_vicious_defeated(normalized)
                    return True
                round_index += 1
                result = self.run_custom_path(
                    kill_path,
                    focus_first=(round_index == 1),
                    monitor_callback=defeated_detected.is_set,
                    monitor_label="Vicious defeated message",
                    monitor_during_sleep=True,
                    spike_avoidance=True,
                )
                if result == "monitor_triggered" or defeated_detected.is_set():
                    print("Vicious Bee defeated.", flush=True)
                    self.discord_notify_vicious_defeated(normalized)
                    return True
                self.compensate_spike_drift(f"{normalized} kill loop {round_index}")
        finally:
            stop_defeated_monitor.set()
            defeated_monitor_thread.join(timeout=0.5)
        print(f"Vicious kill timed out after {timeout:.0f}s; rejoining.", flush=True)
        self.discord_notify("Vicious Timeout", f"{normalized.title()} - rejoining")
        raise RejoinRequested(f"Vicious kill timed out after {timeout:.0f}s")

    def detect_vicious_chain(self, field: str):
        print("detect_vicious_chain este dezactivat; foloseste chain-ul automat pepper->mountaintop->spider->cactus->rose.", flush=True)

    def field_chain_order(self) -> list[str]:
        values = self.cfg.get("vicious_detection.field_chain", ["pepper", "mountaintop", "spider", "cactus", "rose"])
        return [self.normalize_field_name(item) for item in values]

    def annotate_vicious_screenshot(self, screenshot: Image.Image, yolo_result: dict) -> Image.Image:
        """Return the detection frame with its YOLO box and confidence overlaid."""
        annotated = screenshot.copy().convert("RGB")
        confidence = float(yolo_result.get("confidence", 0.0) or 0.0)
        box = yolo_result.get("box")
        if not isinstance(box, (tuple, list)) or len(box) != 4:
            return annotated
        x, y, width, height = (int(value) for value in box)
        image_width, image_height = annotated.size
        x1 = max(0, min(image_width - 1, x))
        y1 = max(0, min(image_height - 1, y))
        x2 = max(x1 + 1, min(image_width - 1, x + max(1, width)))
        y2 = max(y1 + 1, min(image_height - 1, y + max(1, height)))
        draw = ImageDraw.Draw(annotated)
        draw.rectangle((x1, y1, x2, y2), outline=(255, 35, 35), width=4)
        draw.text((x1, max(4, y1 - 18)), f"VICIOUS {confidence:.3f}", fill=(255, 35, 35))
        return annotated

    def record_vicious_detection(
        self,
        field: str,
        yolo_result: dict | None = None,
        screenshot: Image.Image | None = None,
        source: str = "live",
    ) -> None:
        """Append confirmed Vicious events and save their annotated source image."""
        minimum_confidence = float(self.cfg.get("vicious_detection.yolo_event_log_min_confidence", 0.30))
        if yolo_result is None:
            yolo_result = self.detector.last_vicious_yolo_detection()
        confidence = float(yolo_result.get("confidence", 0.0) or 0.0)
        if not bool(yolo_result.get("found", False)) or confidence < minimum_confidence:
            return
        now = time.localtime()
        readable_time = time.strftime("%Y-%m-%d %H:%M:%S", now)
        stamp = f"{time.strftime('%Y%m%d_%H%M%S', now)}_{int(time.time() * 1000) % 1000:03d}"
        log_path = self.cfg.base_dir / "vicious_detections.txt"
        screenshot_path: Path | None = None
        if bool(self.cfg.get("vicious_detection.save_detection_screenshots", False)):
            screenshot_dir = self.cfg.base_dir / "vicious_detection_screenshots"
            try:
                screenshot_dir.mkdir(exist_ok=True)
                screenshot_path = screenshot_dir / f"{stamp}_{field}_{source}_vicious_conf{confidence:.3f}.png"
                raw_frame = screenshot if screenshot is not None else self.detector.roblox_shot()
                annotated = self.annotate_vicious_screenshot(raw_frame, yolo_result)
                annotated.save(screenshot_path)
            except Exception as exc:
                print(f"Could not save Vicious detection screenshot: {exc}", flush=True)
                screenshot_path = None
        try:
            details = f" screenshot={screenshot_path.name}" if screenshot_path else " screenshot=unavailable"
            with log_path.open("a", encoding="utf-8") as handle:
                handle.write(
                    f"[{readable_time}] VICIOUS DETECTED field={field} "
                    f"confidence={confidence:.3f} source={source}{details}\n"
                )
        except Exception as exc:
            print(f"Could not write Vicious detection log: {exc}", flush=True)

    def save_vicious_field_scan(self, field: str, screenshot: Image.Image) -> None:
        """Keep one raw scan frame per field, separate from confirmed Vicious events."""
        if not bool(self.cfg.get("vicious_detection.save_field_scan_debug_images", False)):
            return
        try:
            debug_dir = self.cfg.base_dir / "debug_vicious_ai"
            debug_dir.mkdir(exist_ok=True)
            now = time.localtime()
            stamp = f"{time.strftime('%Y%m%d_%H%M%S', now)}_{int(time.time() * 1000) % 1000:03d}"
            screenshot.save(debug_dir / f"{stamp}_{field}_field_scan.png")
        except Exception as exc:
            print(f"Could not save Vicious field scan: {exc}", flush=True)

    def detect_vicious_field_image(self, field: str) -> bool:
        normalized = self.normalize_field_name(field)
        shift_mode = str(self.cfg.get("vicious_detection.shift_detection_mode", "toggle") or "toggle").lower()
        use_shift = shift_mode not in {"off", "false", "0", "none"}
        moving_right = False
        if use_shift and not self.dry_run:
            self.input.release_shift()
            if shift_mode == "hold":
                self.input.key_down("shift")
            else:
                self.input.fast_tap(
                    "shift",
                    repeats=1,
                    hold=float(self.cfg.get("vicious_detection.shift_tap_hold_seconds", 0.035)),
                    interval=0.0,
                )
            # Keep the camera movement requested for the field scan active until Shift is released.
            self.input.key_down("right")
            moving_right = True
            if normalized == "rose" and bool(self.cfg.get("vicious_detection.rose_zoom_out_before_detection", True)):
                print("Rose detection: zoom out max after shift.", flush=True)
                self.input.sleep(float(self.cfg.get("vicious_detection.rose_shift_zoom_delay_seconds", 0.60)))
                self.input.zoom_out_max()
            self.input.sleep(float(self.cfg.get("vicious_detection.shift_detect_settle_seconds", 0.10)))
        scan_window = max(0.05, float(self.cfg.get("vicious_detection.field_detection_window_seconds", 0.9)))
        max_samples = max(1, int(self.cfg.get("vicious_detection.field_detection_samples", 1)))
        sample_delay = max(0.0, float(self.cfg.get("vicious_detection.field_detection_sample_delay_seconds", 0.18)))
        found = False
        try:
            deadline = time.monotonic() + scan_window
            sample = 0
            while sample < max_samples:
                screenshot = self.detector.roblox_shot()
                if sample == 0:
                    self.stats_increment("field_scans")
                    self.save_vicious_field_scan(normalized, screenshot)
                    self.discord_notify(
                        f"Scanning {normalized.title()}",
                        "Vicious check",
                        screenshot=screenshot,
                    )
                if self.detector.vicious_field_image_visible(normalized, screenshot=screenshot):
                    found = True
                    self.stats_increment("vicious_detected")
                    yolo_result = self.detector.last_vicious_yolo_detection()
                    # Save the exact frame that produced the positive result
                    # while Shift and D are still active. Taking a fresh
                    # screenshot after the finally block captures a different
                    # camera position.
                    self.record_vicious_detection(
                        normalized,
                        yolo_result=yolo_result,
                        screenshot=screenshot,
                        source="live_scan",
                    )
                    self.discord_notify(
                        "Vicious Detected",
                        f"{normalized.title()} - {float(yolo_result.get('confidence', 0.0) or 0.0):.3f}",
                        screenshot=self.annotate_vicious_screenshot(screenshot, yolo_result),
                    )
                    break
                sample += 1
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    break
                if sample_delay > 0:
                    self.input.sleep(min(sample_delay, remaining))
        finally:
            if moving_right:
                self.input.key_up("right")
            if use_shift and not self.dry_run:
                if shift_mode != "hold":
                    self.input.fast_tap(
                        "shift",
                        repeats=1,
                        hold=float(self.cfg.get("vicious_detection.shift_tap_hold_seconds", 0.035)),
                        interval=0.0,
                    )
                self.input.release_shift()
        print(f"field image detection {normalized}: {found}", flush=True)
        return found

    def test_vicious_detection(self):
        order = self.field_chain_order()
        self.input.focus_roblox()
        found_any = False
        print(f"Testing Vicious detection on fields: {', '.join(order)}", flush=True)
        for field in order:
            found = self.detect_vicious_field_image(field)
            if found:
                found_any = True
                print(f"VICIOUS_FOUND_ALERT:{field}", flush=True)
        if not found_any:
            print("Vicious detection test: nothing found.", flush=True)

    def test_vicious_image_file(self, image_path: Path):
        result, annotated_path = self.detector.test_vicious_image_file(Path(image_path))
        field = self.detector.infer_vicious_field_from_path(Path(image_path))
        box = result.get("box") or result.get("best_any_box")
        if result.get("error"):
            print(f"Manual YOLO image {field}: error={result['error']}", flush=True)
        else:
            print(
                f"Manual YOLO image {field}: found={result['found']} "
                f"confidence={result['confidence']:.3f}/{result['threshold']:.3f} "
                f"box={box} saved={annotated_path}",
                flush=True,
            )
            if result["found"]:
                with Image.open(image_path) as source_image:
                    frame = source_image.convert("RGB")
                    self.record_vicious_detection(
                        field,
                        yolo_result=result,
                        screenshot=frame,
                        source="manual",
                    )
                    self.discord_notify(
                        "Vicious Detected",
                        f"{field.title()} - {float(result.get('confidence', 0.0) or 0.0):.3f}",
                        screenshot=self.annotate_vicious_screenshot(frame, result),
                    )
                print(f"VICIOUS_FOUND_ALERT:{field}", flush=True)
        with contextlib.suppress(Exception):
            os.startfile(str(annotated_path))  # type: ignore[attr-defined]

    def test_vicious_message_image_file(self, image_path: Path):
        return self.detector.test_vicious_message_image_file(Path(image_path))

    def run_vicious_field_chain(self):
        order = self.field_chain_order()
        self.input.focus_roblox()
        continue_after_found = bool(self.cfg.get("vicious_detection.continue_after_vicious_found", True))
        found_fields: list[str] = []
        for index, field in enumerate(order, start=1):
            self.raise_if_global_vicious_defeated(field)
            path = self.find_field_path(field)
            if path is None:
                print(f"Field path missing for {field}; skipping.", flush=True)
                continue
            print(f"Vicious field chain {index}/{len(order)}: running {field} path ({path})", flush=True)
            self.discord_notify(
                f"Going {field.title()}",
                "Running path",
            )
            self.run_custom_path(path, focus_first=(index == 1))
            self.raise_if_global_vicious_defeated(field)
            if self.detect_vicious_field_image(field):
                self.raise_if_global_vicious_defeated(field)
                found_fields.append(field)
                print(f"VICIOUS_FOUND_ALERT:{field}", flush=True)
                if self.run_vicious_spawn_and_kill(field):
                    raise RejoinRequested(f"Vicious defeated in {field}; rejoining")
                if bool(self.cfg.get("vicious_detection.rejoin_after_spawn_detection_failure", True)):
                    raise RejoinRequested(
                        f"Vicious detected in {field}, but attack/left message was not confirmed"
                    )
                if continue_after_found:
                    print(f"Vicious found in {field}. Continuing collection mode.", flush=True)
                    continue
                print(f"Vicious found in {field}. Waiting for next instruction.", flush=True)
                return
            print(f"Vicious not found in {field}. Moving to next field.", flush=True)
            self.raise_if_global_vicious_defeated(field)
        self.raise_if_global_vicious_defeated("field chain")
        if found_fields and continue_after_found:
            raise RejoinRequested(f"Collection mode finished; found Vicious in {', '.join(found_fields)}")
        raise RejoinRequested("Vicious not found in pepper/mountaintop/spider/cactus/rose")

    def goto_ramp(self, hive_slot: int):
        slot = max(1, min(6, int(hive_slot)))
        forward_studs = float(self.cfg.get("paths.ramp_forward_studs", 35.0))
        right_base = float(self.cfg.get("paths.ramp_right_base_studs", 23.5))
        right_per_slot = float(self.cfg.get("paths.ramp_right_per_slot_studs", 70.0))
        right_studs = max(0.0, right_base + right_per_slot * (slot - 1))
        print(
            f"nm_gotoRamp: HiveSlot={slot}, forward={forward_studs:.1f}, "
            f"right={right_studs:.1f} (base={right_base:.1f}, per_slot={right_per_slot:.1f})",
            flush=True,
        )
        self.input.focus_roblox()
        self.input.walk("forward", forward_studs)
        self.input.walk("right", right_studs)

    def claim_hive_if_needed(self):
        if not self.cfg.get("hive.enabled", True):
            return
        print("Claiming hive slot", flush=True)
        self.input.focus_roblox()
        if self.cfg.get("hive.use_slot_path_detection", True):
            print("Using detected hive slot path routine.", flush=True)
            if self.claim_hive_by_detected_slot_path():
                return
            print("Detected hive slot path routine failed; falling back to normal hive claim.", flush=True)
        if self.cfg.get("hive.use_revolution_detection", True):
            print("Using Revolution hive claim routine.", flush=True)
            if self.claim_hive_revolution():
                return
            print("Revolution hive routine failed; falling back to prompt scan.", flush=True)
        else:
            self.input.zoom_out_max()
            if self.claim_empty_hive_by_red_arrow():
                return
            print("Empty hive red arrow not claimed; falling back to prompt scan.", flush=True)
        timeout = float(self.cfg.get("hive.approach_timeout_seconds", 18))
        end = time.time() + timeout
        step = float(self.cfg.get("hive.approach_step_seconds", 0.30))
        pause = float(self.cfg.get("hive.detect_pause_seconds", 0.10))
        while time.time() < end:
            if self.dry_run or self.detector.any_hive_prompt_visible():
                break
            self.input.key_down("forward")
            try:
                self.input.sleep(step)
            finally:
                self.input.key_up("forward")
            scan_until = time.time() + pause
            while time.time() < scan_until:
                self.input.sleep(0.03)
                if self.dry_run or self.detector.any_hive_prompt_visible():
                    break
            else:
                continue
            break
        else:
            print("Hive prompt not found while approaching.", flush=True)
            return

        self.input.walk("backward", 2)
        if self.try_claim_current_hive(slot=3):
            return

        checked = 1
        checking_slot = 3
        direction = -1
        max_slots = int(self.cfg.get("hive.max_slots_to_check", 6))
        while checked < max_slots:
            if checking_slot <= 1 and direction == -1:
                direction = 1
            key = "left" if direction == 1 else "right"
            checking_slot += 1 if direction == 1 else -1
            print(f"Checking hive slot {checking_slot}", flush=True)
            self.move_to_next_hive_prompt(key)
            if self.try_claim_current_hive(slot=checking_slot):
                return
            checked += 1
        print("Failed to claim hive; continuing anyway.", flush=True)

    def claim_hive_by_detected_slot_path(self) -> bool:
        attempts = max(1, int(self.cfg.get("hive.slot_path_claim_max_attempts", 2)))
        retry_enabled = bool(self.cfg.get("hive.slot_path_retry_on_missing_confirm", True))
        for attempt in range(1, attempts + 1):
            if attempt > 1:
                print(f"Hive slot path: retry attempt {attempt}/{attempts}.", flush=True)
            self._hive_slot_path_missing = False
            if self.claim_hive_by_detected_slot_path_once():
                return True
            if self._hive_slot_path_missing:
                print("Hive slot path: path file missing; skipping reset retry and using fallback claim.", flush=True)
                break
            if not retry_enabled or attempt >= attempts:
                break
            self.reset_character_after_failed_hive_claim()
        return False

    def claim_hive_by_detected_slot_path_once(self) -> bool:
        self.input.zoom_out_max()
        self.prepare_hive_red_arrow_camera()
        self.input.sleep(float(self.cfg.get("hive.slot_path_detect_settle_seconds", 0.25)))
        self.discord_notify(
            "Hive Scan",
            "Finding slot",
            screenshot=self.detector.roblox_shot(),
        )
        marker = self.detector.empty_hive_marker()
        if marker is None:
            print("Hive slot path: no available hive detected.", flush=True)
            return False

        _x, _y, _area, slot = marker
        self.claimed_hive_slot = slot
        print(f"Hive slot path: current HiveSlot set to {slot}.", flush=True)
        path = self.find_hive_slot_path(slot)
        if path is None:
            self._hive_slot_path_missing = True
            print(
                f"Hive slot path: detected hive{slot}, but no hive{slot}.ahk/.txt/.json exists in "
                f"{self.hive_slot_path_dir()} or {self.custom_path_dir()}",
                flush=True,
            )
            return False

        print(f"Hive slot path: detected available hive{slot}. Running {path}", flush=True)
        self.discord_notify(
            "Hive Slot",
            f"Slot {slot}",
        )
        if self.cfg.get("hive.slot_path_zoom_in_before_run", True):
            self.input.zoom_in_after_hive_scan()
        self.run_custom_path(
            path,
            focus_first=bool(self.cfg.get("hive.slot_path_refocus_before_run", False)),
            variables={"HiveSlot": slot},
        )
        if self.cfg.get("hive.slot_path_auto_claim", True):
            return self.claim_after_slot_path(slot)
        return True

    def prepare_hive_red_arrow_camera(self):
        if not self.cfg.get("hive.empty_hive_use_red_arrow_slots", True):
            return
        cfg = self.cfg.get("camera_setup", {}) or {}
        presses = int(cfg.get("hive_red_arrow_rot_up_presses", 2))
        if presses <= 0 or self.dry_run:
            return
        hold = float(cfg.get("hive_zoom_key_hold_seconds", cfg.get("key_hold_seconds", 0.12)))
        gap = float(cfg.get("hive_zoom_gap_seconds", cfg.get("between_keys_seconds", 0.08)))
        print(f"hive red arrow camera: rot_up {presses}", flush=True)
        self.input.press_camera_key("rot_up", presses, hold, gap)
        self.input.sleep(float(cfg.get("hive_red_arrow_after_delay_seconds", 0.04)))

    def reset_character_after_failed_hive_claim(self):
        print("Hive slot path: claim confirm missing. Resetting character before retry.", flush=True)
        if self.dry_run:
            return
        self.input.focus_roblox()
        self.input.press("escape", repeats=1, interval=0.12)
        self.input.press("r", repeats=1, interval=0.12)
        self.input.press("enter", repeats=1, interval=0.12)
        self.input.sleep(float(self.cfg.get("hive.slot_path_reset_respawn_seconds", 5.0)))

    def wait_for_hive_claim_confirmation(self, slot: int, timeout: float | None = None) -> bool:
        if timeout is None:
            timeout = float(self.cfg.get("hive.slot_path_confirm_timeout_seconds", 2.5))
        end = time.time() + max(0.1, timeout)
        print(f"Hive slot path: waiting for Make Honey/Collect Pollen confirmation for hive{slot}.", flush=True)
        while time.time() < end:
            self.input.check_stop()
            if self.detector.natro_at_hive_visible(log=False):
                print(f"Hive slot path: claim confirmed for hive{slot}.", flush=True)
                self.claimed_hive_slot = max(1, min(6, int(slot)))
                return True
            self.input.sleep(0.04)
        print(f"Hive slot path: claim confirmation not visible for hive{slot}.", flush=True)
        return False

    def claim_after_slot_path(self, slot: int) -> bool:
        timeout = float(self.cfg.get("hive.slot_path_claim_timeout_seconds", 4.0))
        end = time.time() + timeout
        repeats = int(self.cfg.get("hive.drive_to_claim_press_repeats", 5))
        print(f"Hive slot path: checking Claim Hive prompt for hive{slot}.", flush=True)
        if self.cfg.get("hive.slot_path_blind_claim_after_run", True):
            delay = float(self.cfg.get("hive.slot_path_blind_claim_delay_seconds", 0.15))
            self.input.sleep(delay)
            print(f"Hive slot path: blind pressing E for hive{slot}.", flush=True)
            self.input.fast_tap(
                "e",
                repeats=max(1, repeats),
                hold=float(self.cfg.get("hive.drive_to_claim_fast_tap_hold_seconds", 0.025)),
                interval=0.006,
            )
            if self.wait_for_hive_claim_confirmation(slot):
                return True
        while time.time() < end:
            self.input.check_stop()
            if self.detector.natro_at_hive_visible(log=False):
                print(f"Hive slot path: hive{slot} already claimed/at hive.", flush=True)
                self.claimed_hive_slot = max(1, min(6, int(slot)))
                return True
            if self.detector.natro_claim_hive_visible(log=False) or self.detector.claim_hive_blue_prompt_visible():
                print(f"Hive slot path: Claim Hive visible for hive{slot}. Pressing E.", flush=True)
                self.press_claim_hive(repeats, 0.0)
                return self.wait_for_hive_claim_confirmation(slot)
            self.input.sleep(0.05)
        print(f"Hive slot path: no Claim Hive prompt after running hive{slot} path.", flush=True)
        return False

    def claim_hive_revolution(self) -> bool:
        timeout = float(self.cfg.get("hive.drive_to_claim_timeout_seconds", self.cfg.get("hive.revolution_claim_timeout_seconds", 35)))
        scan_interval = float(self.cfg.get("hive.drive_to_claim_scan_interval_seconds", 0.0))
        press_delay = float(self.cfg.get("hive.drive_to_claim_press_delay_seconds", 0.0))
        press_repeats = int(self.cfg.get("hive.drive_to_claim_press_repeats", 5))
        spam_e = bool(self.cfg.get("hive.drive_to_claim_spam_e_while_moving", True))
        spam_interval = float(self.cfg.get("hive.drive_to_claim_spam_e_interval_seconds", 0.045))
        spam_hold = float(self.cfg.get("hive.drive_to_claim_spam_e_hold_seconds", 0.010))
        align_enabled = bool(self.cfg.get("hive.align_to_empty_hive_before_drive", True))
        print(
            f"Hive drive routine start: align={align_enabled} timeout={timeout:.1f}s scan_interval={scan_interval:.3f}s continuous_w=True natro_prompt_scan=True spam_e={spam_e}",
            flush=True,
        )

        if self.dry_run:
            print("Dry run: would hold W until Claim Hive is visible, then press E.", flush=True)
            return True

        if align_enabled:
            self.align_to_empty_hive_red_arrow()
        else:
            print("Hive red-arrow align skipped by config.", flush=True)

        print("Revolution: holding W continuously until Claim Hive appears.", flush=True)
        started_at = time.time()
        end = time.time() + timeout
        next_status = time.time() + 1.0
        next_e_tap = time.perf_counter()
        scans = 0
        e_taps = 0
        prompt_hint_started_at = None
        forward_down = False
        self.input.key_down("forward")
        forward_down = True
        try:
            while time.time() < end:
                self.input.check_stop()
                scans += 1
                if self.detector.natro_at_hive_visible(log=False):
                    if not self.dry_run:
                        self.input.send_key("forward", down=False)
                    forward_down = False
                    print("Natro: Make Honey/Collect Pollen visible. Hive claim confirmed.", flush=True)
                    return True
                if self.detector.natro_claim_hive_visible(log=False):
                    if not self.dry_run:
                        self.input.send_key("forward", down=False)
                    forward_down = False
                    print("Natro Claim Hive prompt visible. Stopped and pressing E.", flush=True)
                    self.press_claim_hive(press_repeats, press_delay)
                    return True
                prompt_state = self.detector.claim_hive_blue_prompt_state()
                if prompt_state == "full":
                    if not self.dry_run:
                        self.input.send_key("forward", down=False)
                    forward_down = False
                    print("Claim Hive visible while holding W. Stopped and pressing E.", flush=True)
                    self.press_claim_hive(press_repeats, press_delay)
                    return True
                if prompt_state == "partial" and prompt_hint_started_at is None:
                    prompt_hint_started_at = time.time()
                    e_taps = 0
                    print("Claim Hive partial blue detected. Starting fast E taps while W stays down.", flush=True)
                now_perf = time.perf_counter()
                elapsed = time.time() - started_at
                if spam_e and prompt_hint_started_at is not None and now_perf >= next_e_tap:
                    self.input.fast_tap_silent("e", hold=spam_hold)
                    e_taps += 1
                    next_e_tap = now_perf + spam_interval
                if time.time() >= next_status:
                    name, score, x, y = self.detector.natro_white_text_match(
                        ["natro_claimhive.png", "natro_makehoney.png", "natro_collectpollen.png"],
                        threshold=0.0,
                        log=False,
                    )
                    natro_status = f", best_natro={name} {score:.3f} at {x},{y}" if name else ""
                    print(
                        f"prompt scan active: {scans} checks, elapsed={elapsed:.1f}s, e_taps={e_taps}, Claim Hive not visible yet{natro_status}",
                        flush=True,
                    )
                    next_status = time.time() + 1.0
                if scan_interval > 0:
                    time.sleep(scan_interval)
        finally:
            if forward_down:
                self.input.key_up("forward")

        print("Claim Hive did not appear while walking forward.", flush=True)
        return False

    def press_claim_hive(self, repeats: int, delay: float):
        if delay > 0:
            time.sleep(delay)
        hold = float(self.cfg.get("hive.drive_to_claim_fast_tap_hold_seconds", 0.025))
        self.input.fast_tap("e", repeats=max(1, repeats), hold=hold, interval=0.006)
        verify_until = time.time() + float(self.cfg.get("hive.drive_to_claim_post_press_scan_seconds", 0.60))
        extra_pressed = False
        while time.time() < verify_until:
            self.input.check_stop()
            if self.detector.natro_at_hive_visible(log=False):
                print("Hive claim verified by Natro Make Honey/Collect Pollen prompt.", flush=True)
                return
            if self.detector.natro_claim_hive_visible(log=False):
                print("Claim Hive still visible after press; pressing E again.", flush=True)
                self.input.fast_tap("e", repeats=max(1, repeats), hold=hold, interval=0.006)
                extra_pressed = True
            time.sleep(0.015)
        if extra_pressed:
            print("Claim Hive prompt was pressed again; continuing after verify window.", flush=True)

    def align_to_empty_hive_red_arrow(self):
        timeout = float(self.cfg.get("hive.empty_hive_align_timeout_seconds", 2.5))
        tolerance = int(self.cfg.get("hive.empty_hive_align_tolerance_px", 90))
        side_step = float(self.cfg.get("hive.empty_hive_side_step_seconds", 0.12))
        end = time.time() + timeout
        print(
            f"Scanning visible hive red arrows before drive. timeout={timeout:.1f}s tolerance={tolerance}px",
            flush=True,
        )
        self.input.zoom_out_max()
        self.prepare_hive_red_arrow_camera()
        scan_count = 0
        while time.time() < end:
            self.input.check_stop()
            scan_count += 1
            marker = self.detector.empty_hive_marker()
            if marker is None:
                print(f"Hive red-arrow scan {scan_count}: no empty hive slot detected.", flush=True)
                self.input.sleep(0.10)
                continue
            x, _y, _area, slot = marker
            rect = self.input.roblox_window_rect()
            center_x = (rect[0] + rect[2] // 2) if rect is not None else self.screen_center_x()
            delta = x - center_x
            print(f"aligning to detected hive slot {slot}; delta={delta}", flush=True)
            if abs(delta) <= tolerance:
                break
            key = "right" if delta > 0 else "left"
            self.input.key_down(key)
            try:
                self.input.sleep(side_step)
            finally:
                self.input.key_up(key)
        print("Hive red-arrow align finished.", flush=True)
        self.input.zoom_in_after_hive_scan()

    def try_claim_revolution_slot(self, slot: int, blind: bool = False) -> bool:
        if not self.dry_run and self.detector.claim_hive_blue_prompt_visible():
            print(f"Blue Claim Hive prompt visible at slot {slot}. Pressing E.", flush=True)
            self.input.press("e", repeats=int(self.cfg.get("hive.drive_to_claim_press_repeats", 3)), interval=0.04)
            return True
        if blind:
            print(f"Revolution: blind claim attempt at slot {slot}", flush=True)
            self.input.press("e")
            self.input.sleep(0.35)
            return False
        if self.dry_run or self.detector.revolution_hive_prompt(claim_only=True) == "claimhive.png":
            print(f"Revolution: claim hive found at slot {slot}", flush=True)
            self.input.press("e", repeats=int(self.cfg.get("hive.drive_to_claim_press_repeats", 3)), interval=0.04)
            return True
        return False

    def move_to_next_hive_revolution(self, key: str, slot: int, end_time: float, blind: bool = False) -> tuple[bool, bool]:
        if blind:
            self.input.key_down(key)
            try:
                self.input.sleep(float(self.cfg.get("hive.revolution_blind_slot_move_seconds", 1.2)))
            finally:
                self.input.key_up(key)
            return self.try_claim_revolution_slot(slot, blind=True), True

        self.input.key_down(key)
        try:
            while time.time() < end_time:
                if self.dry_run:
                    self.input.sleep(0.2)
                    return True, True
                if self.detector.revolution_hive_prompt(claim_only=False) is None:
                    break
                self.input.sleep(0.01)

            while time.time() < end_time:
                prompt = self.detector.revolution_hive_prompt(claim_only=False)
                if prompt == "claimhive.png":
                    self.input.key_up(key)
                    print(f"Revolution: claim hive found at slot {slot}", flush=True)
                    self.input.press("e", repeats=int(self.cfg.get("hive.drive_to_claim_press_repeats", 3)), interval=0.04)
                    return True, True
                if prompt in {"sendtrade.png", "tradedisabled.png", "tradelocked.png"}:
                    return False, True
                self.input.sleep(0.01)
            return False, False
        finally:
            self.input.key_up(key)

    def claim_empty_hive_by_red_arrow(self) -> bool:
        if not self.cfg.get("hive.empty_hive_red_arrow_detection", True):
            return False
        timeout = float(self.cfg.get("hive.empty_hive_timeout_seconds", 16))
        align_tolerance = int(self.cfg.get("hive.empty_hive_align_tolerance_px", 90))
        drive_step = float(self.cfg.get("hive.empty_hive_drive_step_seconds", 0.24))
        forward_step = float(self.cfg.get("hive.empty_hive_forward_step_seconds", 0.35))
        end = time.time() + timeout
        zoomed_in_for_drive = False

        while time.time() < end:
            if self.dry_run:
                print("Dry run: would claim empty hive by red arrow.", flush=True)
                return True
            if self.detector.claim_hive_visible():
                self.input.press("e", repeats=int(self.cfg.get("hive.drive_to_claim_press_repeats", 3)), interval=0.04)
                self.claimed_hive_slot = 3
                return True

            marker = self.detector.empty_hive_marker()
            if marker is None:
                self.input.walk("forward", 4)
                continue

            x, _y, _area, slot = marker
            self.claimed_hive_slot = max(1, min(6, int(slot)))
            rect = self.input.roblox_window_rect()
            if rect is not None:
                left, _top, width, _height = rect
                center_x = left + width // 2
            else:
                center_x = self.screen_center_x()
            delta = x - center_x
            side_key = None
            if abs(delta) > align_tolerance:
                side_key = "right" if delta > 0 else "left"
            print(f"driving to detected hive slot {slot}; delta={delta}", flush=True)

            if not zoomed_in_for_drive:
                self.input.zoom_in_after_hive_scan()
                zoomed_in_for_drive = True

            self.input.key_down("forward")
            if side_key is not None:
                self.input.key_down(side_key)
            try:
                self.input.sleep(drive_step if side_key is not None else forward_step)
            finally:
                self.input.key_up("forward")
                if side_key is not None:
                    self.input.key_up(side_key)
            if self.detector.claim_hive_visible() or self.detector.any_hive_prompt_visible():
                self.input.press("e", repeats=int(self.cfg.get("hive.drive_to_claim_press_repeats", 3)), interval=0.04)
                self.claimed_hive_slot = max(1, min(6, int(slot)))
                return True
        return False

    def screen_center_x(self) -> int:
        img = self.detector.screen.shot()
        return img.size[0] // 2

    def move_to_next_hive_prompt(self, key: str):
        timeout = float(self.cfg.get("hive.slot_move_seconds", 1.35))
        end = time.time() + timeout
        prompt_was_visible = False
        self.input.key_down(key)
        try:
            while time.time() < end:
                self.input.check_stop()
                if self.dry_run:
                    self.input.sleep(timeout)
                    return
                if self.detector.any_hive_prompt_visible():
                    prompt_was_visible = True
                elif prompt_was_visible:
                    break
                self.input.sleep(0.03)

            end = time.time() + timeout
            while time.time() < end:
                self.input.check_stop()
                if self.detector.any_hive_prompt_visible():
                    return
                self.input.sleep(0.03)
        finally:
            self.input.key_up(key)

    def try_claim_current_hive(self, slot: int) -> bool:
        if self.dry_run or self.detector.claim_hive_visible():
            print(f"Claim hive found at slot {slot}", flush=True)
            self.input.press("e", repeats=int(self.cfg.get("hive.drive_to_claim_press_repeats", 3)), interval=0.04)
            self.claimed_hive_slot = max(1, min(6, int(slot)))
            return True
        return False

    def kill_loop(self, timeout_seconds: int = 300):
        speed_monitor_started_here = False
        if self._speed_monitor_thread is None or not self._speed_monitor_thread.is_alive():
            self.start_speed_monitor()
            speed_monitor_started_here = self._speed_monitor_thread is not None and self._speed_monitor_thread.is_alive()
        start = time.time()
        try:
            while time.time() - start < timeout_seconds:
                self.avoid_spikes_if_needed()
                self.input.walk("forward", 16)
                self.avoid_spikes_if_needed()
                self.input.walk("left", 16)
                self.avoid_spikes_if_needed()
                self.input.walk("backward", 16)
                self.avoid_spikes_if_needed()
                self.input.walk("right", 16)
                self.avoid_spikes_if_needed()
                self.compensate_spike_drift("built-in kill loop")
                status = None if self.dry_run else self.detector.rejoin_status_visible()
                if status:
                    raise RejoinRequested(f"Detected '{status}'")
                if not self.dry_run and self.detector.defeated():
                    print("Vicious Bee defeated.", flush=True)
                    return
                if not self.dry_run and not self.detector.battle_active():
                    self.input.sleep(1.0)
            raise RejoinRequested(f"Vicious kill timed out after {timeout_seconds:.0f}s")
        finally:
            if speed_monitor_started_here:
                self.stop_speed_monitor()

    def engage_if_found(self, field: str) -> bool:
        if self.maybe_detect(field):
            print(f"Vicious detected in {field}. Starting kill loop.", flush=True)
            self.kill_loop()
            return True
        return False

    def vic_path(self):
        self.run_vicious_field_chain()

    def walk_cannon(self):
        self.input.press("zoom_in", repeats=2)
        self.input.walk("forward", 83.2)
        self.input.walk("backward", 6)
        self.input.walk("right", 4)
        self.input.sleep(0.1)
        self.input.walk("right", 94)
        self.input.walk("forward", 4)
        self.input.press("space")
        self.input.press("e")

    def walk_mountain(self) -> bool:
        print("Searching: Mountain Top", flush=True)
        self.input.sleep(0.5)
        self.input.press("e")
        self.input.press("rot_left", repeats=4)
        self.input.sleep(1.1)
        self.input.press("space", repeats=2)
        self.input.key_down("right")
        self.input.sleep(2.6)
        self.input.key_up("right")
        self.input.key_down("forward")
        self.input.sleep(1.8)
        self.input.press("space")
        self.input.key_up("forward")
        self.input.walk("forward", 130)
        self.input.walk("left", 196)
        self.input.walk("backward", 13)
        self.input.press("shift")
        self.input.press("rot_right", repeats=2)
        self.input.press("rot_down", repeats=9)
        self.input.press("rot_up", repeats=2)
        return self.engage_if_found("mountain")

    def walk_spider(self) -> bool:
        print("Searching: Spider", flush=True)
        self.input.press("rot_left", repeats=4)
        self.input.press("rot_up", repeats=2)
        self.input.walk("backward", 197)
        self.input.walk("left", 93.6)
        self.input.press("space")
        self.input.sleep(0.35)
        self.input.press("space")
        self.input.sleep(3.2)
        self.input.walk("forward", 78)
        self.input.walk("right", 26)
        self.input.walk("forward", 56)
        self.input.press("shift")
        self.input.press("rot_down", repeats=9)
        self.input.press("rot_up", repeats=5)
        self.input.press("zoom_out", repeats=10)
        return self.engage_if_found("spider")

    def walk_cactus(self) -> bool:
        print("Searching: Cactus", flush=True)
        self.input.press("rot_up", repeats=2)
        self.input.walk("left", 2.6)
        self.input.walk("backward", 14)
        self.input.walk("left", 30)
        self.input.press("space")
        self.input.walk("forward", 26)
        self.input.walk("right", 39)
        self.input.walk("forward", 130)
        self.input.walk("right", 130)
        self.input.walk("forward", 20)
        self.input.press("space")
        self.input.walk("forward", 46)
        self.input.walk("forward", 90)
        self.input.walk("right", 30)
        self.input.press("shift")
        self.input.press("rot_down", repeats=9)
        self.input.walk("backward", 15.6)
        self.input.walk("right", 10)
        if self.engage_if_found("cactus"):
            return True
        self.input.walk("backward", 50.7)
        self.input.walk("right", 10)
        return self.engage_if_found("cactus")

    def walk_rose(self) -> bool:
        print("Searching: Rose", flush=True)
        self.input.press("rot_up", repeats=6)
        self.input.walk("left", 104)
        self.input.press("space")
        self.input.walk("left", 70.2)
        self.input.walk("forward", 39)
        self.input.press("shift")
        self.input.press("rot_left", repeats=2)
        self.input.walk("backward", 46.8)
        self.input.press("rot_down", repeats=9)
        self.input.press("rot_up", repeats=5)
        self.input.walk("right", 1.3)
        self.input.walk("backward", 1.3)
        self.input.press("zoom_out", repeats=10)
        if self.engage_if_found("rose"):
            return True
        self.input.press("zoom_in", repeats=2)
        return self.engage_if_found("rose")

    def walk_pepper(self) -> bool:
        print("Searching: Pepper", flush=True)
        self.input.walk("right", 70)
        self.input.press("space", repeats=2)
        self.input.walk("right", 16)
        self.input.walk("forward", 12)
        self.input.press("space", repeats=2)
        self.input.walk("forward", 58)
        self.input.walk("right", 20)
        self.input.press("zoom_out", repeats=4)
        self.input.key_down("forward")
        self.input.press("space")
        self.input.sleep(0.8)
        self.input.press("space")
        self.input.sleep(1.8)
        self.input.key_up("forward")
        self.input.key_down("forward")
        self.input.press("space")
        self.input.sleep(2.6)
        self.input.key_down("right")
        self.input.sleep(1.0)
        self.input.key_up("forward")
        self.input.press("space", repeats=2)
        self.input.sleep(3.0)
        self.input.key_up("right")
        self.input.walk("backward", 7.8)
        self.input.press("zoom_in", repeats=5)
        self.input.press("rot_down", repeats=2)
        self.input.press("shift")
        return self.engage_if_found("pepper")

    def walk_cannon_from_pepper(self):
        self.input.walk("backward", 20)
        self.input.press("space")
        self.input.sleep(0.5)
        self.input.press("space")
        self.input.key_down("backward")
        self.input.sleep(1.6)
        self.input.press("space")
        self.input.key_up("backward")
        self.input.walk("backward", 16)
        self.input.walk("left", 40)
        self.input.walk("right", 16)
        self.input.walk("forward", 16)
        self.input.press("rot_right", repeats=6)
        self.input.walk("forward", 96)
        self.input.walk("left", 40)
        self.input.walk("forward", 80)
        self.input.press("e")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Vicious Bee farm / stinger hop helper.")
    parser.add_argument("command", choices=["search", "kill", "night", "input-test", "hive-test"], help="Routine to run.")
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--dry-run", action="store_true", help="Print actions without pressing keys.")
    args = parser.parse_args(argv)

    cfg = Config(args.config)
    farm = ViciousFarm(cfg, args.dry_run)
    commands: dict[str, Callable[[], object]] = {
        "search": farm.search,
        "kill": farm.kill_loop,
        "night": lambda: print(farm.detect_night()),
        "input-test": farm.input_test,
        "hive-test": farm.claim_hive_if_needed,
    }
    commands[args.command]()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
