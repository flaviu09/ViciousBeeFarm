from __future__ import annotations

import contextlib
import io
import json
import math
import queue
import re
import sys
import threading
import time
import traceback
from pathlib import Path
from tkinter import (
    BOTH,
    DISABLED,
    END,
    LEFT,
    NORMAL,
    RIGHT,
    Button,
    Checkbutton,
    Entry,
    Frame,
    IntVar,
    Label,
    LabelFrame,
    StringVar,
    Scrollbar,
    Text,
    Tk,
    Toplevel,
    Y,
    filedialog,
    messagebox,
    simpledialog,
)

from main import Config, DEFAULT_CONFIG, ViciousFarm

try:
    import keyboard
except Exception:  # pragma: no cover - optional global hotkeys
    keyboard = None


APP_TITLE = "Vicious Bee Farm"
MAX_LOG_LINES = 1500
MAX_RUN_LOG_BYTES = 8 * 1024 * 1024


def app_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


class QueueWriter(io.TextIOBase):
    def __init__(self, log_queue: "queue.Queue[str]", log_path: Path | None = None):
        self.log_queue = log_queue
        self.log_path = log_path

    def write(self, text: str) -> int:
        if text:
            self.log_queue.put(text)
            if self.log_path is not None:
                try:
                    with self.log_path.open("a", encoding="utf-8", errors="replace") as handle:
                        handle.write(text)
                except Exception:
                    pass
        return len(text)

    def flush(self) -> None:
        pass


class App:
    def __init__(self):
        self.root = Tk()
        self.root.title(APP_TITLE)
        self.root.geometry("920x700")
        self.root.minsize(820, 620)

        self.base = app_dir()
        self.config_path = self.base / "config.json"
        if not self.config_path.exists() and DEFAULT_CONFIG.exists():
            self.config_path.write_text(DEFAULT_CONFIG.read_text(encoding="utf-8-sig"), encoding="utf-8")

        self.config_data = self.load_config()
        self.log_queue: "queue.Queue[str]" = queue.Queue()
        self.run_log_path = self.base / "macro_run.log"
        self._log_line_start = True
        self.worker: threading.Thread | None = None
        self.stop_event = threading.Event()

        self.enabled = IntVar(value=1)
        self.dry_run = IntVar(value=0)
        self.server_hop = IntVar(value=1 if self.config_data.get("server_hop", True) else 0)
        self.exclude_full = IntVar(value=1 if self.config_data.get("exclude_full_games", True) else 0)
        self.close_before_rejoin = IntVar(value=1 if self.config_data.get("close_before_rejoin", False) else 0)
        self.load_detect = IntVar(value=1 if self.config_data.get("load_detection", {}).get("enabled", True) else 0)
        self.hive_enabled = IntVar(value=1 if self.config_data.get("hive", {}).get("enabled", True) else 0)
        self.rejoin_load_timeout = IntVar(
            value=1 if self.config_data.get("load_detection", {}).get("rejoin_on_timeout", True) else 0
        )
        self.place_id = StringVar(value=str(self.config_data.get("roblox_place_id", 1537690962)))
        self.max_rejoins = StringVar(value=str(self.config_data.get("max_night_rejoins", 25)))
        self.launch_method = StringVar(value=str(self.config_data.get("launch_method", "protocol")))
        self.api_wait = StringVar(value=str(self.config_data.get("api_rate_limit_wait_seconds", 20)))
        load_cfg = self.config_data.get("load_detection", {})
        self.load_timeout = StringVar(value=str(load_cfg.get("timeout_seconds", 60)))
        self.join_transition_grace = StringVar(value=str(load_cfg.get("join_transition_grace_seconds", 15.0)))
        self.texture_threshold = StringVar(value=str(load_cfg.get("texture_threshold", 0.72)))
        self.blue_min_ratio = StringVar(value=str(load_cfg.get("blue_min_ratio", 0.22)))
        hive_cfg = self.config_data.get("hive", {})
        self.hive_threshold = StringVar(value=str(hive_cfg.get("claim_threshold", 0.86)))
        self.hive_timeout = StringVar(value=str(hive_cfg.get("approach_timeout_seconds", 18)))
        self.hive_slot_move = StringVar(value=str(hive_cfg.get("slot_move_seconds", 1.35)))
        self.ramp_slot = StringVar(value="1")
        self.move_speed = StringVar(value=str(self.config_data.get("move_speed_studs_per_second", 29.0)))
        speed_cfg = self.config_data.get("speed_buffs", {}) or {}
        self.speed_test_duration = StringVar(value=str(speed_cfg.get("test_duration_seconds", 60)))
        self.speed_test_countdown = StringVar(value="")
        self.speed_test_overlay_text = StringVar(value="")
        self.speed_test_deadline: float | None = None
        self.speed_test_overlay: Toplevel | None = None
        self.night_threshold = StringVar(
            value=str(self.config_data.get("night_probe", {}).get("max_average_rgb", 58))
        )
        self.red_pixels = StringVar(
            value=str(self.config_data.get("battle_scan", {}).get("min_red_pixels", 180))
        )
        camera = self.config_data.get("camera_setup", {})
        self.zoom_in = StringVar(value=str(camera.get("zoom_in_presses", 4)))
        self.zoom_out = StringVar(value=str(camera.get("zoom_out_presses", 2)))
        self.rot_down = StringVar(value=str(camera.get("rot_down_presses", 3)))
        self.rot_up_after = StringVar(value=str(camera.get("rot_up_after_detect", 2)))
        self.key_hold = StringVar(value=str(camera.get("key_hold_seconds", 0.12)))
        discord_cfg = self.config_data.get("discord", {}) or {}
        self.discord_enabled = IntVar(value=1 if discord_cfg.get("enabled", False) else 0)
        self.discord_screenshots = IntVar(value=1 if discord_cfg.get("send_screenshots", True) else 0)
        self.discord_hourly_reports = IntVar(value=1 if discord_cfg.get("hourly_reports_enabled", True) else 0)
        self.discord_webhook_url = StringVar(value=str(discord_cfg.get("webhook_url", "") or ""))
        self.status = StringVar(value="Ready")
        self.last_vicious_alert = ""

        self.build_ui()
        self.register_hotkeys()
        self.root.after(100, self.drain_log)

    def load_config(self) -> dict:
        if not self.config_path.exists():
            return {}
        try:
            return json.loads(self.config_path.read_text(encoding="utf-8-sig"))
        except Exception:
            return {}

    def save_config(self) -> bool:
        try:
            data = self.load_config()
            data["roblox_place_id"] = int(self.place_id.get())
            data["max_night_rejoins"] = int(self.max_rejoins.get())
            data["launch_method"] = self.launch_method.get().strip() or "protocol"
            data["server_hop"] = bool(self.server_hop.get())
            data["exclude_full_games"] = bool(self.exclude_full.get())
            data["close_before_rejoin"] = bool(self.close_before_rejoin.get())
            data["api_rate_limit_wait_seconds"] = float(self.api_wait.get())
            data["move_speed_studs_per_second"] = float(self.move_speed.get())
            data.setdefault("speed_buffs", {})["test_duration_seconds"] = float(self.speed_test_duration.get())
            data.setdefault("hive", {})["enabled"] = bool(self.hive_enabled.get())
            data.setdefault("hive", {})["claim_threshold"] = float(self.hive_threshold.get())
            data.setdefault("hive", {})["approach_timeout_seconds"] = float(self.hive_timeout.get())
            data.setdefault("hive", {})["slot_move_seconds"] = float(self.hive_slot_move.get())
            data.setdefault("hive", {})["max_slots_to_check"] = 6
            data.setdefault("load_detection", {})["enabled"] = bool(self.load_detect.get())
            data.setdefault("load_detection", {})["timeout_seconds"] = float(self.load_timeout.get())
            data.setdefault("load_detection", {})["timeout_after_blue_seconds"] = 45.0
            data.setdefault("load_detection", {})["join_transition_grace_seconds"] = float(self.join_transition_grace.get())
            data.setdefault("load_detection", {})["rejoin_on_timeout"] = bool(self.rejoin_load_timeout.get())
            data.setdefault("load_detection", {})["blue_loading_templates"] = ["blue_loading.png"]
            data.setdefault("load_detection", {})["blue_color_detection"] = True
            data.setdefault("load_detection", {})["blue_rgb"] = [37, 91, 164]
            data.setdefault("load_detection", {})["blue_tolerance"] = 32
            data.setdefault("load_detection", {})["blue_min_ratio"] = float(self.blue_min_ratio.get())
            data.setdefault("load_detection", {})["blue_screen_top_ratio"] = 0.45
            data.setdefault("load_detection", {})["blue_screen_bottom_ratio"] = 0.88
            data.setdefault("load_detection", {})["blue_template_fallback"] = False
            data.setdefault("load_detection", {})["blue_template_min_ratio"] = 0.12
            data.setdefault("load_detection", {})["blue_loading_appear_required"] = True
            data.setdefault("load_detection", {})["blue_disappear_samples"] = 1
            data.setdefault("load_detection", {})["loaded_blue_max_ratio"] = 0.08
            data.setdefault("load_detection", {})["loaded_texture_stddev_min"] = 14.0
            data.setdefault("load_detection", {})["loaded_required_samples"] = 2
            data.setdefault("load_detection", {})["loaded_marker_min_ratio"] = 0.010
            data.setdefault("load_detection", {})["loaded_marker_roi"] = {
                "left": 0.0,
                "right": 0.18,
                "top": 0.055,
                "bottom": 0.16,
            }
            data.setdefault("load_detection", {})["loaded_top_bar_min_ratio"] = 0.045
            data.setdefault("load_detection", {})["loaded_top_bar_roi"] = {
                "left": 0.30,
                "right": 0.70,
                "top": 0.035,
                "bottom": 0.105,
            }
            data.setdefault("load_detection", {})["texture_threshold"] = float(self.texture_threshold.get())
            data.setdefault("load_detection", {})["sample_interval_seconds"] = 0.18
            data.setdefault("load_detection", {})["stable_fallback_enabled"] = False
            data.setdefault("load_detection", {})["loading_phrases"] = [
                "loading",
                "joining server",
                "waiting for an available server",
                "requesting server",
            ]
            data.setdefault("night_probe", {})["max_average_rgb"] = float(self.night_threshold.get())
            data.setdefault("battle_scan", {})["min_red_pixels"] = int(self.red_pixels.get())
            data.setdefault("camera_setup", {})["zoom_in_presses"] = int(self.zoom_in.get())
            data.setdefault("camera_setup", {})["zoom_out_presses"] = int(self.zoom_out.get())
            data.setdefault("camera_setup", {})["rot_down_presses"] = int(self.rot_down.get())
            data.setdefault("camera_setup", {})["rot_up_after_detect"] = int(self.rot_up_after.get())
            data.setdefault("camera_setup", {})["key_hold_seconds"] = float(self.key_hold.get())
            data.setdefault("camera_setup", {})["between_keys_seconds"] = 0.025
            data.setdefault("camera_setup", {})["click_center"] = True
            discord = data.setdefault("discord", {})
            discord["enabled"] = bool(self.discord_enabled.get())
            discord["webhook_url"] = self.discord_webhook_url.get().strip()
            discord["send_screenshots"] = bool(self.discord_screenshots.get())
            discord["hourly_reports_enabled"] = bool(self.discord_hourly_reports.get())
            discord["hourly_report_interval_seconds"] = 3600
            self.config_path.write_text(json.dumps(data, indent=2), encoding="utf-8")
            self.config_data = data
            self.log(f"Saved settings to {self.config_path}\n")
            return True
        except Exception as exc:
            messagebox.showerror(APP_TITLE, f"Nu pot salva setarile:\n{exc}")
            return False

    def build_ui(self):
        outer = Frame(self.root, padx=14, pady=8)
        outer.pack(fill=BOTH, expand=True)

        header = Frame(outer)
        header.pack(fill="x")
        Label(header, text=APP_TITLE, font=("Segoe UI", 18, "bold")).pack(side=LEFT)
        Label(header, textvariable=self.status, font=("Segoe UI", 10), fg="#0b6b47").pack(side=RIGHT)
        Label(header, textvariable=self.speed_test_countdown, font=("Segoe UI", 10, "bold"), fg="#165a9e").pack(
            side=RIGHT, padx=(0, 18)
        )
        Label(header, text="F1 Start  |  F2 Stop", font=("Segoe UI", 10), fg="#555").pack(side=RIGHT, padx=18)

        switches = LabelFrame(outer, text="Run Mode", padx=10, pady=0)
        switches.pack(fill="x", pady=(5, 3))
        Checkbutton(switches, text="Enabled", variable=self.enabled).grid(row=0, column=0, sticky="w", padx=(0, 24))
        Checkbutton(switches, text="Dry run (nu apasa taste)", variable=self.dry_run).grid(row=0, column=1, sticky="w", padx=(0, 24))
        Checkbutton(switches, text="Server hop", variable=self.server_hop).grid(row=0, column=2, sticky="w", padx=(0, 24))
        Checkbutton(switches, text="Exclude full servers", variable=self.exclude_full).grid(row=0, column=3, sticky="w")
        Checkbutton(switches, text="Close before rejoin", variable=self.close_before_rejoin).grid(row=1, column=0, sticky="w", padx=(0, 24))
        Checkbutton(switches, text="Detect loaded", variable=self.load_detect).grid(row=1, column=1, sticky="w", padx=(0, 24))
        Checkbutton(switches, text="Rejoin if load timeout", variable=self.rejoin_load_timeout).grid(row=1, column=2, sticky="w", padx=(0, 24))
        Checkbutton(switches, text="Claim hive", variable=self.hive_enabled).grid(row=1, column=3, sticky="w")

        settings = LabelFrame(outer, text="Settings", padx=10, pady=0)
        settings.pack(fill="x", pady=3)
        self.field(settings, "Roblox place id", self.place_id, 0, 0)
        self.field(settings, "Max load wait sec", self.load_timeout, 0, 2)
        self.field(settings, "Move speed", self.move_speed, 0, 4)
        self.field(settings, "Night threshold", self.night_threshold, 1, 0)
        self.field(settings, "Min red pixels", self.red_pixels, 1, 2)
        self.field(settings, "Max rejoins", self.max_rejoins, 1, 4)
        self.field(settings, "Launch method", self.launch_method, 2, 0)
        self.field(settings, "Zoom in presses", self.zoom_in, 2, 2)
        self.field(settings, "Zoom out presses", self.zoom_out, 2, 4)
        self.field(settings, "Rot down presses", self.rot_down, 3, 0)
        self.field(settings, "Rot up after", self.rot_up_after, 3, 2)
        self.field(settings, "Key hold sec", self.key_hold, 3, 4)
        self.field(settings, "API rate-limit wait", self.api_wait, 4, 0)
        self.field(settings, "Texture threshold", self.texture_threshold, 4, 2)
        self.field(settings, "Blue min ratio", self.blue_min_ratio, 4, 4)
        self.field(settings, "Hive threshold", self.hive_threshold, 5, 0)
        self.field(settings, "Hive approach sec", self.hive_timeout, 5, 2)
        self.field(settings, "Hive move sec", self.hive_slot_move, 5, 4)
        self.field(settings, "Join grace sec", self.join_transition_grace, 6, 0)
        self.field(settings, "Ramp slot test", self.ramp_slot, 6, 2)
        self.field(settings, "Speed test sec", self.speed_test_duration, 6, 4)

        discord = LabelFrame(outer, text="Discord", padx=10, pady=0)
        discord.pack(fill="x", pady=3)
        Checkbutton(discord, text="Enable webhook", variable=self.discord_enabled).grid(row=0, column=0, sticky="w", padx=(0, 18))
        Checkbutton(discord, text="Send screenshots", variable=self.discord_screenshots).grid(row=0, column=1, sticky="w", padx=(0, 18))
        Checkbutton(discord, text="Hourly reports", variable=self.discord_hourly_reports).grid(row=0, column=2, sticky="w")
        Label(discord, text="Webhook URL").grid(row=1, column=0, sticky="w", pady=(2, 0))
        Entry(discord, textvariable=self.discord_webhook_url, width=48).grid(
            row=1, column=1, sticky="we", padx=(8, 8), pady=(2, 0)
        )
        self.discord_test_btn = Button(discord, text="Test Discord", width=14, command=self.test_discord)
        self.discord_test_btn.grid(row=1, column=2, sticky="e", pady=(2, 0))
        discord.columnconfigure(1, weight=1)

        actions = Frame(outer)
        actions.pack(fill="x", pady=3)
        self.start_btn = Button(actions, text="Start Search", command=self.start_search)
        self.start_btn.grid(row=0, column=0, sticky="ew", padx=2, pady=0)
        self.kill_btn = Button(actions, text="Kill Loop", command=self.start_kill)
        self.kill_btn.grid(row=0, column=1, sticky="ew", padx=2, pady=0)
        self.night_btn = Button(actions, text="Test Night", command=self.test_night)
        self.night_btn.grid(row=0, column=2, sticky="ew", padx=2, pady=0)
        self.input_btn = Button(actions, text="Test Input", command=self.test_input)
        self.input_btn.grid(row=0, column=3, sticky="ew", padx=2, pady=0)
        self.hive_btn = Button(actions, text="Test Hive", command=self.test_hive)
        self.hive_btn.grid(row=0, column=4, sticky="ew", padx=2, pady=0)
        self.path_btn = Button(actions, text="Test Path", command=self.test_path)
        self.path_btn.grid(row=0, column=5, sticky="ew", padx=2, pady=0)
        self.ramp_btn = Button(actions, text="Test Ramp", command=self.test_ramp)
        self.ramp_btn.grid(row=0, column=6, sticky="ew", padx=2, pady=0)
        self.speed_btn = Button(actions, text="Test Speed", command=self.test_speed)
        self.speed_btn.grid(row=1, column=0, sticky="ew", padx=2, pady=0)
        self.vicious_btn = Button(actions, text="Test Vicious", command=self.test_vicious)
        self.vicious_btn.grid(row=1, column=1, sticky="ew", padx=2, pady=0)
        self.vicious_msg_btn = Button(actions, text="Test Vic Msg", command=self.test_vicious_message)
        self.vicious_msg_btn.grid(row=1, column=2, sticky="ew", padx=2, pady=0)
        self.stingers_btn = Button(actions, text="Test Stingers", command=self.test_stingers)
        self.stingers_btn.grid(row=1, column=3, sticky="ew", padx=2, pady=0)
        self.safepoint_btn = Button(actions, text="Test SafePoint", command=self.test_safepoint)
        self.safepoint_btn.grid(row=1, column=4, sticky="ew", padx=2, pady=0)
        Button(actions, text="Save Settings", command=self.save_config).grid(
            row=1, column=5, sticky="ew", padx=2, pady=0
        )
        self.stop_btn = Button(actions, text="Stop", state=DISABLED, command=self.request_stop)
        self.stop_btn.grid(row=1, column=6, sticky="ew", padx=2, pady=0)
        for column in range(7):
            actions.columnconfigure(column, weight=1)

        log_frame = LabelFrame(outer, text="Log", padx=5, pady=4)
        log_frame.pack(fill=BOTH, expand=True, pady=(3, 0))
        log_inner = Frame(log_frame)
        log_inner.pack(fill=BOTH, expand=True)
        scrollbar = Scrollbar(log_inner)
        scrollbar.pack(side=RIGHT, fill=Y)
        self.log_box = Text(log_inner, height=16, wrap="word", font=("Consolas", 9), yscrollcommand=scrollbar.set)
        self.log_box.pack(side=LEFT, fill=BOTH, expand=True)
        scrollbar.config(command=self.log_box.yview)
        self.log(
            "Pregateste Roblox/Bee Swarm, apoi apasa Start Search.\n"
            "Hotkeys: F1 Start, F2 Stop. Oprire urgenta: muta mouse-ul in coltul stanga-sus.\n\n"
        )

    def register_hotkeys(self):
        self.root.bind("<F1>", lambda _event: self.start_search())
        self.root.bind("<F2>", lambda _event: self.request_stop())
        if keyboard is None:
            self.log("Global hotkeys indisponibile; F1/F2 merg cand fereastra este focusata.\n")
            return
        try:
            keyboard.add_hotkey("f1", lambda: self.root.after(0, self.start_search))
            keyboard.add_hotkey("f2", lambda: self.root.after(0, self.request_stop))
            self.root.protocol("WM_DELETE_WINDOW", self.close)
        except Exception as exc:
            self.log(f"Global hotkeys indisponibile ({exc}); F1/F2 merg cand fereastra este focusata.\n")

    def field(self, parent: Frame, label: str, var: StringVar, row: int, col: int):
        Label(parent, text=label).grid(row=row, column=col, sticky="w", padx=(0, 5), pady=1)
        Entry(parent, textvariable=var, width=12).grid(row=row, column=col + 1, sticky="w", padx=(0, 10), pady=1)

    def timestamp_log_text(self, text: str) -> str:
        out: list[str] = []
        for chunk in text.splitlines(keepends=True):
            if self._log_line_start and chunk not in ("\n", "\r\n"):
                out.append(f"[{time.strftime('%H:%M:%S')}] ")
            out.append(chunk)
            self._log_line_start = chunk.endswith(("\n", "\r\n"))
        return "".join(out)

    def log(self, text: str):
        self.log_box.insert(END, self.timestamp_log_text(text))
        self.trim_log()
        self.log_box.see(END)

    def trim_log(self):
        try:
            line_count = int(float(self.log_box.index("end-1c").split(".")[0]))
            if line_count <= MAX_LOG_LINES:
                return
            delete_to = max(1, line_count - MAX_LOG_LINES + 1)
            self.log_box.delete("1.0", f"{delete_to}.0")
        except Exception:
            pass

    def drain_log(self):
        while True:
            try:
                text = self.log_queue.get_nowait()
            except queue.Empty:
                break
            self.log(text)
            self.handle_vicious_alert(text)
        self.root.after(100, self.drain_log)

    def handle_vicious_alert(self, text: str):
        match = re.search(r"VICIOUS_FOUND_ALERT:([a-z_]+)", text)
        if not match:
            return
        cfg = self.config_data.get("vicious_detection", {}) or {}
        field = match.group(1)
        if field == self.last_vicious_alert:
            return
        self.last_vicious_alert = field
        self.status.set(f"Vicious found: {field}")
        if bool(cfg.get("alert_sound_enabled", False)):
            with contextlib.suppress(Exception):
                self.root.bell()

    def set_running(self, running: bool):
        state = DISABLED if running else NORMAL
        self.start_btn.config(state=state)
        self.kill_btn.config(state=state)
        self.night_btn.config(state=state)
        self.input_btn.config(state=state)
        self.hive_btn.config(state=state)
        self.path_btn.config(state=state)
        self.ramp_btn.config(state=state)
        self.speed_btn.config(state=state)
        self.vicious_btn.config(state=state)
        self.vicious_msg_btn.config(state=state)
        self.stingers_btn.config(state=state)
        self.safepoint_btn.config(state=state)
        self.discord_test_btn.config(state=state)
        self.stop_btn.config(state=NORMAL if running else DISABLED)
        self.status.set("Running" if running else "Ready")
        if not running:
            self.speed_test_deadline = None
            self.speed_test_countdown.set("")
            self.hide_speed_test_overlay()

    def make_farm(self) -> ViciousFarm:
        self.save_config()
        cfg = Config(self.config_path)
        return ViciousFarm(cfg, dry_run=bool(self.dry_run.get()), stop_event=self.stop_event)

    def test_discord(self):
        if not self.discord_enabled.get():
            messagebox.showwarning(APP_TITLE, "Activeaza Enable webhook mai intai.")
            return
        if not self.discord_webhook_url.get().strip():
            messagebox.showwarning(APP_TITLE, "Pune URL-ul webhook-ului Discord.")
            return
        self.run_worker("Discord Test", lambda: self.make_farm().test_discord_webhook())

    def run_worker(self, name: str, fn) -> bool:
        if not self.enabled.get():
            messagebox.showwarning(APP_TITLE, "Toggle-ul Enabled este oprit.")
            return False
        if self.worker and self.worker.is_alive():
            messagebox.showwarning(APP_TITLE, "Deja ruleaza o rutina.")
            return False
        self.stop_event.clear()
        self.last_vicious_alert = ""
        self.set_running(True)
        self.rotate_run_log()
        self.log(f"\n=== {name} ===\n")
        self.write_run_log(f"\n=== {name} started {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n")

        def target():
            try:
                with contextlib.redirect_stdout(QueueWriter(self.log_queue, self.run_log_path)), contextlib.redirect_stderr(
                    QueueWriter(self.log_queue, self.run_log_path)
                ):
                    fn()
                done = f"\n{name} finished.\n"
                self.log_queue.put(done)
                self.write_run_log(done)
            except RuntimeError as exc:
                if "Stopped by user" in str(exc):
                    stopped = f"\n{name} stopped.\n"
                    self.log_queue.put(stopped)
                    self.write_run_log(stopped)
                else:
                    error_path = self.base / "last_error.txt"
                    error_path.write_text(traceback.format_exc(), encoding="utf-8")
                    error = f"\nERROR. Detalii in {error_path}\n"
                    self.log_queue.put(error)
                    self.write_run_log(error)
            except Exception:
                error_path = self.base / "last_error.txt"
                error_path.write_text(traceback.format_exc(), encoding="utf-8")
                error = f"\nERROR. Detalii in {error_path}\n"
                self.log_queue.put(error)
                self.write_run_log(error)
            finally:
                self.root.after(0, lambda: self.set_running(False))

        self.worker = threading.Thread(target=target, daemon=True)
        self.worker.start()
        return True

    def start_speed_test_countdown(self, duration_seconds: float) -> None:
        deadline = time.monotonic() + max(1.0, float(duration_seconds))
        self.speed_test_deadline = deadline
        self.show_speed_test_overlay()

        def tick() -> None:
            if self.speed_test_deadline != deadline:
                return
            remaining = max(0, int(math.ceil(deadline - time.monotonic())))
            minutes, seconds = divmod(remaining, 60)
            self.speed_test_countdown.set(f"Speed test {minutes:02d}:{seconds:02d}")
            self.speed_test_overlay_text.set(f"SPEED TEST\n{minutes:02d}:{seconds:02d}")
            if self.worker is not None and self.worker.is_alive():
                self.root.after(200, tick)

        tick()

    def show_speed_test_overlay(self) -> None:
        self.hide_speed_test_overlay()
        overlay = Toplevel(self.root)
        overlay.overrideredirect(True)
        overlay.configure(bg="#0f1720")
        overlay.attributes("-topmost", True)
        with contextlib.suppress(Exception):
            overlay.attributes("-toolwindow", True)
        Label(
            overlay,
            textvariable=self.speed_test_overlay_text,
            font=("Segoe UI", 16, "bold"),
            fg="#ffffff",
            bg="#0f1720",
            justify="center",
            padx=18,
            pady=9,
            relief="solid",
            borderwidth=2,
        ).pack()
        overlay.update_idletasks()
        # Remote Desktop and Windows DPI scaling can report the requested widget
        # size in a different scale than the screen coordinates. Keep a large,
        # fixed inset and place the overlay midway down the right side.
        x = max(20, overlay.winfo_screenwidth() - 340)
        y = max(20, (overlay.winfo_screenheight() - overlay.winfo_reqheight()) // 2)
        overlay.geometry(f"+{x}+{y}")
        overlay.lift()
        with contextlib.suppress(Exception):
            overlay.attributes("-disabled", True)
        self.speed_test_overlay = overlay

    def hide_speed_test_overlay(self) -> None:
        overlay = self.speed_test_overlay
        self.speed_test_overlay = None
        if overlay is not None:
            with contextlib.suppress(Exception):
                overlay.destroy()

    def rotate_run_log(self):
        try:
            if self.run_log_path.exists() and self.run_log_path.stat().st_size > MAX_RUN_LOG_BYTES:
                backup = self.base / "macro_run.old.log"
                if backup.exists():
                    backup.unlink()
                self.run_log_path.replace(backup)
        except Exception:
            pass

    def write_run_log(self, text: str):
        try:
            with self.run_log_path.open("a", encoding="utf-8", errors="replace") as handle:
                handle.write(text)
        except Exception:
            pass

    def start_search(self):
        self.run_worker("Search", lambda: self.make_farm().search())

    def start_kill(self):
        self.run_worker("Kill Loop", lambda: self.make_farm().kill_loop())

    def test_night(self):
        def task():
            farm = self.make_farm()
            print(f"Night detected: {farm.detect_night()}", flush=True)

        self.run_worker("Night Test", task)

    def test_input(self):
        self.run_worker("Input Test", lambda: self.make_farm().input_test())

    def test_hive(self):
        self.run_worker("Hive Test", lambda: self.make_farm().claim_hive_if_needed())

    def test_path(self):
        if self.dry_run.get():
            messagebox.showwarning(APP_TITLE, "Dry run este pornit. Debifeaza-l daca vrei sa apese taste in Roblox.")
            return
        initial_dir = self.base / "paths"
        initial_dir.mkdir(exist_ok=True)
        selected = filedialog.askopenfilename(
            title="Alege path",
            initialdir=str(initial_dir),
            filetypes=(("Path files", "*.txt *.ahk *.json"), ("Simple path", "*.txt *.ahk"), ("Path JSON", "*.json"), ("All files", "*.*")),
        )
        if not selected:
            return
        path = Path(selected)
        self.run_worker("Path Test", lambda: self.make_farm().run_custom_path(path))

    def test_ramp(self):
        if self.dry_run.get():
            messagebox.showwarning(APP_TITLE, "Dry run este pornit. Debifeaza-l daca vrei sa apese taste in Roblox.")
            return
        try:
            slot = int(float(self.ramp_slot.get()))
        except ValueError:
            messagebox.showerror(APP_TITLE, "Ramp slot trebuie sa fie un numar intre 1 si 6.")
            return
        slot = max(1, min(6, slot))
        self.ramp_slot.set(str(slot))
        self.run_worker("Ramp Test", lambda: self.make_farm().goto_ramp(slot))

    def test_speed(self):
        try:
            duration = float(self.speed_test_duration.get())
        except ValueError:
            messagebox.showerror(APP_TITLE, "Speed test sec trebuie sa fie un numar intre 5 si 3600.")
            return
        duration = max(5.0, min(3600.0, duration))
        self.speed_test_duration.set(str(int(duration) if duration.is_integer() else duration))
        started = self.run_worker(
            "Speed Detection Test",
            lambda: self.make_farm().test_speed_detection(duration_seconds=duration),
        )
        if started:
            self.start_speed_test_countdown(duration)

    def test_vicious(self):
        selected = filedialog.askopenfilename(
            title="Alege poza pentru Vicious YOLO",
            initialdir=str(self.base),
            filetypes=(
                ("Image files", "*.png *.jpg *.jpeg *.bmp *.webp"),
                ("PNG", "*.png"),
                ("JPEG", "*.jpg *.jpeg"),
                ("All files", "*.*"),
            ),
        )
        if not selected:
            return
        image_path = Path(selected)
        self.run_worker("Vicious Image Test", lambda: self.make_farm().test_vicious_image_file(image_path))

    def test_vicious_message(self):
        selected = filedialog.askopenfilename(
            title="Alege poza pentru Vicious message/defeated",
            initialdir=str(self.base),
            filetypes=(
                ("Image files", "*.png *.jpg *.jpeg *.bmp *.webp"),
                ("PNG", "*.png"),
                ("JPEG", "*.jpg *.jpeg"),
                ("All files", "*.*"),
            ),
        )
        if not selected:
            return
        image_path = Path(selected)
        self.run_worker("Vicious Message Test", lambda: self.make_farm().test_vicious_message_image_file(image_path))

    def test_stingers(self):
        selected = filedialog.askopenfilename(
            title="Alege poza pentru Stingers hotbar",
            initialdir=str(self.base),
            filetypes=(
                ("Image files", "*.png *.jpg *.jpeg *.bmp *.webp"),
                ("PNG", "*.png"),
                ("JPEG", "*.jpg *.jpeg"),
                ("All files", "*.*"),
            ),
        )
        if not selected:
            return
        image_path = Path(selected)
        self.run_worker("Stingers Image Test", lambda: self.make_farm().test_stingers_hotbar_image_file(image_path))

    def test_safepoint(self):
        if self.dry_run.get():
            messagebox.showwarning(APP_TITLE, "Dry run este pornit. Debifeaza-l daca vrei sa apese taste in Roblox.")
            return
        initial_dir = self.base / "paths" / "vicfind"
        initial_dir.mkdir(parents=True, exist_ok=True)
        selected = filedialog.askopenfilename(
            title="Alege path VicFind pentru SafePoint",
            initialdir=str(initial_dir),
            filetypes=(("AHK path", "*.ahk"), ("Path files", "*.txt *.ahk *.json"), ("All files", "*.*")),
        )
        if not selected:
            return
        path = Path(selected)
        try:
            text = path.read_text(encoding="utf-8-sig")
        except Exception as exc:
            messagebox.showerror(APP_TITLE, f"Nu pot citi pathul:\n{exc}")
            return
        count = len(re.findall(r"(?im)^\s*(?:SafePoint|Safe_Point|VicSafePoint|Checkpoint)\s*\(\s*\)", text))
        if count <= 0:
            messagebox.showwarning(APP_TITLE, "Pathul ales nu are SafePoint().")
            return
        index = simpledialog.askinteger(
            APP_TITLE,
            f"Ce SafePoint vrei sa testezi? (1-{count})",
            parent=self.root,
            minvalue=1,
            maxvalue=count,
        )
        if index is None:
            return
        field = None
        normalized_name = path.name.lower().replace("_", "").replace("-", "")
        if "pepandmt" in normalized_name:
            field_answer = simpledialog.askstring(
                APP_TITLE,
                "Pentru pathul comun, ce field testezi? Scrie pepper sau mountaintop.",
                parent=self.root,
            )
            if field_answer is None:
                return
            field_answer = field_answer.strip().lower().replace(" ", "")
            if field_answer not in {"pepper", "mountaintop", "mountain"}:
                messagebox.showwarning(APP_TITLE, "Scrie doar pepper sau mountaintop.")
                return
            field = "mountaintop" if field_answer == "mountain" else field_answer
        self.run_worker("SafePoint Test", lambda: self.make_farm().test_vicious_safepoint_path(path, index, field))

    def request_stop(self):
        self.log("\nStop requested. Rutina se opreste la urmatorul pas.\n")
        self.stop_event.set()

    def close(self):
        self.stop_event.set()
        if keyboard is not None:
            with contextlib.suppress(Exception):
                keyboard.unhook_all_hotkeys()
        self.root.destroy()

    def run(self) -> int:
        self.root.mainloop()
        return 0


def main() -> int:
    return App().run()


if __name__ == "__main__":
    raise SystemExit(main())
