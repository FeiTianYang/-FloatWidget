import os
import random
import tkinter as tk
from tkinter import filedialog, Toplevel, ttk
from PIL import Image, ImageTk, ImageDraw
import math
import json
import time
import gc
import hashlib
import threading
from concurrent.futures import ThreadPoolExecutor
from functools import wraps
from collections import OrderedDict
import sys
import platform

try:
    import pystray
    from pystray import MenuItem as item
    PYSTRAY_AVAILABLE = True
except ImportError:
    PYSTRAY_AVAILABLE = False

# ═══════════════════ 全局常量 ═══════════════════

COLORS = {
    'bg_primary': '#131316',
    'bg_secondary': '#1c1c22',
    'bg_elevated': '#26262e',
    'bg_hover': '#2e2e38',
    'text_primary': '#eaeaf0',
    'text_secondary': '#8a8a9a',
    'text_muted': '#5a5a6a',
    'accent': '#6c9fff',
    'accent_hover': '#8bb4ff',
    'accent_dim': '#3d5a99',
    'success': '#5cd67a',
    'warning': '#ffb84d',
    'error': '#ff6b6b',
    'border': '#333340',
    'border_light': '#3d3d4a',
    'shadow': '#0a0a0d',
}
FONTS = {
    'title': ("Microsoft YaHei UI", 13, "bold"),
    'subtitle': ("Microsoft YaHei UI", 10, "bold"),
    'body': ("Microsoft YaHei UI", 9),
    'small': ("Microsoft YaHei UI", 8),
    'mono': ("Cascadia Code", 9),
    'icon': ("Segoe UI", 24, "bold"),
    'section': ("Microsoft YaHei UI", 11, "bold"),
}
ICONS = {
    'play': '▶', 'pause': '⏸', 'prev': '◀', 'next': '▶',
    'settings': '⚙', 'home': '🏠', 'delete': '🗑', 'folder': '📁',
    'shuffle': '🔀', 'fullscreen': '⛶', 'check': '✔', 'cross': '✕',
    'favorite': '❤️', 'unfavorite': '🤍',
}
BG_RGBA = (19, 19, 22, 255)
TARGET_FPS = 60
FRAME_DELAY_MS = max(1, int(1000 / TARGET_FPS))
_TRANS_NAMES = ["无", "淡入淡出", "左滑", "右滑", "上滑", "下滑", "缩放", "旋转缩放"]
VALID_EXT = (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp")


class ModernButton(tk.Button):
    def __init__(self, master, **kwargs):
        style = kwargs.pop('style', 'default')
        super().__init__(master, **kwargs)
        if style == 'accent':
            self.config(bg=COLORS['accent'], fg='#ffffff',
                        activebackground=COLORS['accent_hover'], activeforeground='#ffffff',
                        relief='flat', borderwidth=0, padx=14, pady=7, font=FONTS['body'], cursor='hand2')
            self.bind('<Enter>', lambda e: self.config(bg=COLORS['accent_hover']))
            self.bind('<Leave>', lambda e: self.config(bg=COLORS['accent']))
        elif style == 'danger':
            self.config(bg=COLORS['bg_elevated'], fg=COLORS['error'],
                        activebackground=COLORS['error'], activeforeground='#ffffff',
                        relief='flat', borderwidth=0, padx=14, pady=7, font=FONTS['body'], cursor='hand2')
            self.bind('<Enter>', lambda e: self.config(bg=COLORS['error'], fg='#ffffff'))
            self.bind('<Leave>', lambda e: self.config(bg=COLORS['bg_elevated'], fg=COLORS['error']))
        else:
            self.config(bg=COLORS['bg_elevated'], fg=COLORS['text_primary'],
                        activebackground=COLORS['accent'], activeforeground='#ffffff',
                        relief='flat', borderwidth=0, padx=14, pady=7, font=FONTS['body'], cursor='hand2')
            self.bind('<Enter>', lambda e: self.config(bg=COLORS['bg_hover']))
            self.bind('<Leave>', lambda e: self.config(bg=COLORS['bg_elevated']))


def synchronized(lock):
    def decorator(func):
        @wraps(func)
        def wrapper(self, *args, **kwargs):
            with getattr(self, lock):
                return func(self, *args, **kwargs)
        return wrapper
    return decorator


class LRUCache(OrderedDict):
    def __init__(self, maxsize=128):
        self.maxsize = maxsize
        super().__init__()

    def __getitem__(self, key):
        value = super().__getitem__(key)
        self.move_to_end(key)
        return value

    def __setitem__(self, key, value):
        if key in self:
            self.move_to_end(key)
        super().__setitem__(key, value)
        if len(self) > self.maxsize:
            del self[next(iter(self))]


class WidgetManager:
    _instance = None

    def __new__(cls, root):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._initialized = False
        return cls._instance

    def __init__(self, root):
        if self._initialized:
            return
        self.root = root
        self.widgets = []
        self.home_window = None
        self.collision_enabled = False
        self.collision_margin = 5
        self.mouse_through = False
        self.high_framerate = False
        self._id_map = {}
        self._allocated_ids = set()
        self._max_id = 0
        self._initialized = True
        self._tray_icon = None
        self.global_config_file = "global_config.json"
        self._load_global_config()
        self._scan_existing_ids()

    def _scan_existing_ids(self):
        for f in os.listdir('.'):
            if f.startswith('widget_') and f.endswith('.json'):
                try:
                    n = int(f[7:-5])
                    self._allocated_ids.add(n)
                    self._max_id = max(self._max_id, n)
                except:
                    pass

    def _allocate_id(self):
        for i in range(1, self._max_id + 2):
            if i not in self._allocated_ids:
                return i
        return self._max_id + 1

    def _release_id(self, n):
        self._allocated_ids.discard(n)

    def register_widget(self, w):
        if w.widget_id not in self._id_map:
            self._id_map[w.widget_id] = w
            self.widgets.append(w)
            self.widgets.sort(key=lambda x: x.widget_id)
            if self.home_window and self.home_window.winfo_exists():
                self.home_window.add_widget_preview(w)

    def unregister_widget(self, w):
        if w.widget_id in self._id_map:
            del self._id_map[w.widget_id]
            if w in self.widgets:
                self.widgets.remove(w)
            if self.home_window and self.home_window.winfo_exists():
                self.home_window.remove_widget_preview(w)

    def delete_widget(self, w):
        if w.widget_id in self._id_map:
            self._release_id(w.widget_id)
            self.unregister_widget(w)
            try:
                if os.path.exists(w.config_file):
                    os.remove(w.config_file)
                if os.path.exists(w.favorites_file):
                    os.remove(w.favorites_file)
            except:
                pass
            w.destroy()

    def get_visual_rect(self, w):
        p = 5
        return (w.winfo_x() + p, w.winfo_y() + p,
                w.winfo_width() - 2 * p, w.winfo_height() - 2 * p)

    def check_overlap(self, widget, nx, ny):
        if not self.collision_enabled:
            return False, None
        p = 5
        w = widget.winfo_width() - 2 * p
        h = widget.winfo_height() - 2 * p
        rect = (nx + p, ny + p, nx + p + w, ny + p + h)
        margin = self.collision_margin
        for o in self.widgets:
            if o is widget or not o.winfo_exists():
                continue
            ox, oy, ow, oh = self.get_visual_rect(o)
            orect = (ox - margin, oy - margin, ox + ow + margin, oy + oh + margin)
            if (rect[0] < orect[2] and rect[2] > orect[0] and
                    rect[1] < orect[3] and rect[3] > orect[1]):
                return True, (o, (max(rect[0], orect[0]), max(rect[1], orect[1]),
                                  min(rect[2], orect[2]), min(rect[3], orect[3])))
        return False, None

    def resolve_overlap(self, widget, nx, ny, dx, dy):
        p = 5
        w = widget.winfo_width() - 2 * p
        h = widget.winfo_height() - 2 * p
        orig_x, orig_y = nx, ny
        ov, info = self.check_overlap(widget, nx, ny)
        if not ov:
            return nx, ny, True, 0
        other, orect = info
        if max(orect[2] - orect[0], orect[3] - orect[1]) >= self.collision_margin + 3:
            return orig_x, orig_y, False, 0
        dirs = [(-1, 0), (1, 0)] if abs(dx) > abs(dy) else [(0, -1), (0, 1)]
        bx, by, bd = nx, ny, float('inf')
        for ddx, ddy in dirs:
            for i in range(1, 11):
                tx, ty = nx + ddx * 2 * i, ny + ddy * 2 * i
                if not self.check_overlap(widget, tx, ty)[0]:
                    d = abs(tx - nx) + abs(ty - ny)
                    if d < bd:
                        bx, by, bd = tx, ty, d
                    break
        if bd < float('inf'):
            return bx, by, True, 1
        for _ in range(10):
            ov, info = self.check_overlap(widget, nx, ny)
            if not ov:
                return nx, ny, True, 0
            other, orect = info
            if abs(dx) > abs(dy):
                dl = (orect[2] - (nx + p) + self.collision_margin) if dx > 0 else \
                    ((nx + p + w) - orect[0] + self.collision_margin)
                nx += dl
            else:
                dl = (orect[3] - (ny + p) + self.collision_margin) if dy > 0 else \
                    ((ny + p + h) - orect[1] + self.collision_margin)
                ny += dl
        return nx, ny, True, 0

    def set_collision(self, en, margin=None):
        self.collision_enabled = en
        if margin is not None:
            self.collision_margin = margin
        self._save_global_config()

    def set_mouse_through(self, en):
        if platform.system() != 'Windows':
            return
        self.mouse_through = en
        for w in self.widgets:
            self._apply_mouse_through(w, en)
        self._save_global_config()

    def _apply_mouse_through(self, w, en):
        try:
            import ctypes
            hwnd = ctypes.windll.user32.GetParent(w.winfo_id())
            s = ctypes.windll.user32.GetWindowLongW(hwnd, -20)
            if en:
                s |= 0x00000020
            else:
                s &= ~0x00000020
            ctypes.windll.user32.SetWindowLongW(hwnd, -20, s)
            ctypes.windll.user32.SetWindowPos(hwnd, 0, 0, 0, 0, 0, 0x0027)
        except:
            pass

    def set_high_framerate(self, en):
        self.high_framerate = en
        self._apply_timer_resolution(en)
        self._save_global_config()

    def _apply_timer_resolution(self, hi):
        if platform.system() != 'Windows':
            return
        try:
            import ctypes
            if hi:
                ctypes.windll.winmm.timeBeginPeriod(1)
            else:
                ctypes.windll.winmm.timeEndPeriod(1)
        except:
            pass

    def show_home(self):
        if self.home_window and self.home_window.winfo_exists():
            self.home_window.lift()
            self.home_window.focus_force()
        else:
            self.home_window = HomeWindow(self.root, self)

    def get_widget_by_id(self, i):
        return self._id_map.get(i)

    def create_widget_from_id(self, i):
        e = self.get_widget_by_id(i)
        if e and e.winfo_exists():
            return e
        w = FloatWidget(self.root, self, widget_id=i)
        if self.mouse_through and platform.system() == 'Windows':
            self._apply_mouse_through(w, True)
        return w

    def create_new_widget(self):
        w = FloatWidget(self.root, self)
        if self.mouse_through and platform.system() == 'Windows':
            self._apply_mouse_through(w, True)
        return w

    def load_existing_widgets(self):
        for wid in sorted(self._allocated_ids):
            if wid not in self._id_map:
                try:
                    self.create_widget_from_id(wid)
                except:
                    pass

    def quit_app(self):
        if self.high_framerate and platform.system() == 'Windows':
            self._apply_timer_resolution(False)
        if self._tray_icon:
            try:
                threading.Thread(target=lambda: self._tray_icon.stop(), daemon=True).start()
            except:
                pass
        for w in self.widgets[:]:
            try:
                w.destroy()
            except:
                pass
        if self.home_window and self.home_window.winfo_exists():
            self.home_window.destroy()
        self.root.quit()
        self.root.destroy()

    def _load_global_config(self):
        try:
            if os.path.exists(self.global_config_file):
                with open(self.global_config_file, 'r', encoding='utf-8') as f:
                    cfg = json.load(f)
                self.collision_enabled = cfg.get('collision_enabled', False)
                self.collision_margin = cfg.get('collision_margin', 5)
                self.mouse_through = cfg.get('mouse_through', False)
                self.high_framerate = cfg.get('high_framerate', False)
                if self.high_framerate:
                    self._apply_timer_resolution(True)
        except:
            pass

    def _save_global_config(self):
        try:
            with open(self.global_config_file, 'w', encoding='utf-8') as f:
                json.dump({'collision_enabled': self.collision_enabled,
                           'collision_margin': self.collision_margin,
                           'mouse_through': self.mouse_through,
                           'high_framerate': self.high_framerate}, f, indent=2)
        except:
            pass

    def create_tray_icon(self):
        if not PYSTRAY_AVAILABLE:
            return
        try:
            im = Image.new('RGB', (16, 16), color=COLORS['accent'])
            m = pystray.Menu(
                item("显示主页", lambda: self.root.after(0, self.show_home)),
                item("新建部件", lambda: self.root.after(0, self.create_new_widget)),
                item("退出程序", lambda: self.root.after(0, self.quit_app)))
            self._tray_icon = pystray.Icon("FloatPicWidget", im, "浮动图片浏览器", m)
            threading.Thread(target=self._tray_icon.run, daemon=True).start()
        except:
            pass


class HomeWindow(Toplevel):
    def __init__(self, master, manager):
        super().__init__(master)
        self.withdraw()
        self.manager = manager
        self.title("部件管理器")
        self.geometry("1000x700")
        self.configure(bg=COLORS['bg_primary'])
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        self.geometry(f"+{(sw - 1000) // 2}+{(sh - 700) // 2}")
        self.attributes('-alpha', 0.0)
        self._init_ui()
        self.preview_items = {}
        for w in self.manager.widgets:
            self.add_widget_preview(w)
        self._update_empty_state()
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.deiconify()
        self._fade_in()

    def _fade_in(self, step=0.06):
        a = self.attributes('-alpha')
        if a < 1.0:
            self.attributes('-alpha', min(1.0, a + step))
            self.after(FRAME_DELAY_MS, self._fade_in, step)

    def _init_ui(self):
        toolbar = tk.Frame(self, bg=COLORS['bg_secondary'], height=52)
        toolbar.pack(fill='x')
        toolbar.pack_propagate(False)
        inner = tk.Frame(toolbar, bg=COLORS['bg_secondary'])
        inner.pack(fill='both', expand=True, padx=16, pady=8)
        tk.Label(inner, text="部件管理器", font=FONTS['title'],
                 fg=COLORS['text_primary'], bg=COLORS['bg_secondary']).pack(side='left', padx=(0, 20))
        ModernButton(inner, text=f"{ICONS['home']} 新建部件",
                     command=self.create_new_widget, style='accent').pack(side='left')
        tk.Frame(self, bg=COLORS['border'], height=1).pack(fill='x')
        cf = tk.Frame(self, bg=COLORS['bg_primary'])
        cf.pack(fill='both', expand=True)
        self.canvas = tk.Canvas(cf, bg=COLORS['bg_primary'], highlightthickness=0)
        sb = ttk.Scrollbar(cf, orient='vertical', command=self.canvas.yview)
        self.scrollable_frame = tk.Frame(self.canvas, bg=COLORS['bg_primary'])
        self.scrollable_frame.bind("<Configure>",
                                   lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.create_window((0, 0), window=self.scrollable_frame, anchor='nw')
        self.canvas.configure(yscrollcommand=sb.set)
        self.canvas.pack(side='left', fill='both', expand=True)
        sb.pack(side='right', fill='y')
        self.canvas.bind_all("<MouseWheel>",
                             lambda e: self.canvas.yview_scroll(-1 * (e.delta // 120), "units"))

    def _update_empty_state(self):
        if hasattr(self, '_empty_label'):
            try: self._empty_label.destroy()
            except: pass
        if not self.manager.widgets:
            self._empty_label = tk.Frame(self.scrollable_frame, bg=COLORS['bg_primary'])
            self._empty_label.pack(expand=True, pady=80)
            tk.Label(self._empty_label, text="暂无部件", font=FONTS['title'],
                     fg=COLORS['text_muted'], bg=COLORS['bg_primary']).pack()
            tk.Label(self._empty_label, text="点击「新建部件」开始使用", font=FONTS['body'],
                     fg=COLORS['text_muted'], bg=COLORS['bg_primary']).pack(pady=(8, 0))

    def create_new_widget(self):
        self.manager.create_new_widget()

    def add_widget_preview(self, widget):
        if hasattr(self, '_empty_label'):
            try: self._empty_label.destroy()
            except: pass
        card = tk.Frame(self.scrollable_frame, bg=COLORS['bg_secondary'],
                        highlightbackground=COLORS['border'], highlightthickness=1)
        card.pack(side='top', fill='x', padx=16, pady=6)
        card.bind('<Enter>', lambda e: card.config(highlightbackground=COLORS['accent']))
        card.bind('<Leave>', lambda e: card.config(highlightbackground=COLORS['border']))
        pl = tk.Label(card, bg=COLORS['bg_elevated'])
        pl.grid(row=0, column=0, rowspan=3, padx=12, pady=12)
        info = tk.Frame(card, bg=COLORS['bg_secondary'])
        info.grid(row=0, column=1, sticky='nw', padx=12, pady=12)
        tk.Label(info, text=f"部件 {widget.widget_id}", fg=COLORS['text_primary'],
                 bg=COLORS['bg_secondary'], font=FONTS['subtitle']).pack(anchor='w', pady=(0, 4))
        folder = getattr(widget, 'folder_path', '')
        fs = folder[:40] + "..." if len(folder) > 40 else folder
        tk.Label(info, text=f"📁 {fs}", fg=COLORS['text_secondary'],
                 bg=COLORS['bg_secondary'], font=FONTS['mono']).pack(anchor='w', pady=2)
        al = tk.Label(info, text="● 已激活" if widget.active else "○ 未激活",
                      fg=COLORS['success'] if widget.active else COLORS['error'],
                      bg=COLORS['bg_secondary'], font=FONTS['body'])
        al.pack(anchor='w', pady=2)
        bf = tk.Frame(card, bg=COLORS['bg_secondary'])
        bf.grid(row=1, column=1, sticky='nw', padx=12, pady=8)

        def toggle():
            widget.active = not widget.active
            if widget.active:
                widget.deiconify(); al.config(text="● 已激活", fg=COLORS['success'])
            else:
                widget.withdraw(); al.config(text="○ 未激活", fg=COLORS['error'])
            widget.save_config()

        ModernButton(bf, text="激活/停用", command=toggle).pack(side='left', padx=2)
        ModernButton(bf, text=f"{ICONS['delete']} 删除",
                     command=lambda: self.delete_widget(widget), style='danger').pack(side='left', padx=2)
        photo = ImageTk.PhotoImage(Image.new("RGB", (200, 150), (38, 38, 46)))
        pl.config(image=photo); pl.image = photo
        self.preview_items[widget] = (card, pl, photo, info, al)
        widget.request_preview_update()

    def update_widget_preview(self, widget, image_tk):
        if widget in self.preview_items:
            _, pl, _, info, _ = self.preview_items[widget]
            pl.config(image=image_tk); pl.image = image_tk
            folder = getattr(widget, 'folder_path', '')
            fs = folder[:40] + "..." if len(folder) > 40 else folder
            for c in info.winfo_children():
                if isinstance(c, tk.Label) and c.cget('text').startswith("📁"):
                    c.config(text=f"📁 {fs}"); break

    def remove_widget_preview(self, widget):
        if widget in self.preview_items:
            self.preview_items[widget][0].destroy()
            del self.preview_items[widget]
        self._update_empty_state()

    def delete_widget(self, widget):
        self.manager.delete_widget(widget)

    def on_close(self):
        self.manager.home_window = None
        self.destroy()


class FloatWidget(Toplevel):
    PADDING = 5

    def __init__(self, master, manager=None, widget_id=None):
        super().__init__(master)
        self.withdraw()
        self.master = master
        self.manager = manager or WidgetManager(master)
        try:
            if widget_id is not None:
                self.widget_id = widget_id
                if widget_id not in self.manager._allocated_ids:
                    self.manager._allocated_ids.add(widget_id)
                    self.manager._max_id = max(self.manager._max_id, widget_id)
            else:
                self.widget_id = self.manager._allocate_id()
            self.config_file = f"widget_{self.widget_id}.json"
            self.favorites_file = f"favorites_{self.widget_id}.json"
            self.title("浮动图片浏览器")
            self.overrideredirect(True)
            self.attributes('-transparentcolor', COLORS['bg_primary'])
            self.attributes('-alpha', 1.0)
            self.screen_width = self.winfo_screenwidth()
            self.screen_height = self.winfo_screenheight()
            self._init_attributes()
            self.load_config()
            self._init_ui()
            self._bind_events()
            self.executor = ThreadPoolExecutor(max_workers=2)
            self._start_cleanup_timer()
            self._load_favorites()
            if self.folder_path and os.path.isdir(self.folder_path):
                self._start_slideshow_from_config()
                self._start_folder_watch()
            else:
                self._show_start_tip()
            self.settings_window = None
            self._settings_closing = False
            self.manager.register_widget(self)
            self.after(100, self._update_saved_position)
            if not self.active:
                self.withdraw()
            else:
                self.deiconify()
            self.save_config()
        except Exception as e:
            self.manager.unregister_widget(self)
            self.destroy()
            raise e

    def _update_saved_position(self):
        self.window_start_x = self.winfo_x()
        self.window_start_y = self.winfo_y()

    def _init_attributes(self):
        self.corner_radius = 12
        self.image_mode = 0
        self.interval = 3000
        self.is_topmost = False
        self.folder_path = ""
        self.active = True
        self.after_id = None
        self.playing = False
        self.cleanup_timer = None
        self._temp_msg_timer = None
        self._mouse_button_held = False
        self.click_start_time = None
        self.click_start_pos = None
        self.is_long_press = False
        self.long_press_threshold = 300
        self.dragging = False
        self.drag_started = False
        self.drag_moved = False
        self.drag_offset_x = 0
        self.drag_offset_y = 0
        self.drag_threshold_sq = 100
        self.snap_enabled = True
        self.snap_zone = 15
        self.snap_target_x = None
        self.snap_target_y = None
        self.last_click_time = 0
        self.double_click_threshold = 350
        self._last_click_zone = None
        self._long_press_timer_id = None
        self.is_fullscreen_open = False
        self.fullscreen_close_time = 0
        self.fullscreen_ignore_time = 150
        self.fullscreen_window = None
        self.fullscreen_canvas = None
        self.fullscreen_playing = False
        self.fullscreen_after_id = None
        self._fullscreen_lock = threading.Lock()
        self._fullscreen_anim_id = None
        self._fullscreen_anim_gen = 0
        self._fullscreen_anim_reverse = False
        self._fullscreen_anim_positions = []
        self._fullscreen_anim_bilinear = []
        self._fullscreen_anim_bilinear_done = False
        self._fullscreen_anim_base_img = None
        self._fullscreen_anim_total = 0
        self._fullscreen_anim_duration_s = 0.0
        self._fullscreen_anim_start_time = 0.0
        self._fullscreen_anim_rev_start_time = 0.0
        self._fullscreen_anim_rev_start_t = 0.0
        self._fullscreen_image_id = None
        self._fullscreen_closing = False
        self._folder_watch_enabled = True
        self._folder_watch_interval = 2000
        self._folder_watch_timer = None
        self._known_files = set()
        self._folder_mtime = 0
        self._favorites = set()
        self.images = []
        self.index = 0
        self.current_image_index = 0
        self._lock = threading.RLock()
        self._original_cache = LRUCache(5)
        self._processed_cache = LRUCache(8)
        self._fullscreen_cache = LRUCache(3)
        self._mask_cache = LRUCache(5)
        self._thumbnail_cache = LRUCache(10)
        self._photo_refs = []
        self._last_width = 0
        self._last_height = 0
        self._loading_future = None
        self._stop_loading = threading.Event()
        self._preload_stop = threading.Event()
        self._preload_thread = None
        self._rect_coords_cache = {}
        self.transition_type = 0
        self.transition_duration = 400
        self._transition_running = False
        self._transition_timer = None
        self._transition_cancel = False
        self._transition_gen = 0
        self._fullscreen_zoom_level = 1.0
        self._fullscreen_zoom_target = 1.0
        self._fullscreen_zoom_min = 1.0
        self._fullscreen_zoom_max = 5.0
        self._fullscreen_zoom_step = 0.15
        self._fullscreen_zoom_lerp = 0.35
        self._fullscreen_zoom_anim_id = None
        self._fullscreen_pan_x = 0
        self._fullscreen_pan_y = 0
        self._fullscreen_panning = False
        self._fullscreen_pan_start = None
        self._fullscreen_base_img = None
        self._fullscreen_left_start = None
        self._fullscreen_left_dragging = False
        self._fullscreen_cached_photo = None
        self._fullscreen_cached_zw = 0
        self._fullscreen_cached_zh = 0

    @staticmethod
    def _ease_in_cubic(t): return t ** 3
    @staticmethod
    def _ease_out_cubic(t): return 1 - (1 - t) ** 3
    @staticmethod
    def _ease_in_out_cubic(t):
        return 4 * t * t * t if t < 0.5 else 1 - (-2 * t + 2) ** 3 / 2
    @staticmethod
    def _ease_out_quart(t): return 1 - (1 - t) ** 4
    @staticmethod
    def _ease_in_out_quart(t):
        return 8 * t ** 4 if t < 0.5 else 1 - (-2 * t + 2) ** 4 / 2
    @staticmethod
    def _ease_out_back(t):
        c1, c3 = 1.3, 2.3
        return 1 + c3 * (t - 1) ** 3 + c1 * (t - 1) ** 2

    # ═══════════════════ 收藏系统 ═══════════════════

    def _load_favorites(self):
        try:
            if os.path.exists(self.favorites_file):
                with open(self.favorites_file, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                self._favorites = set(data.keys())
        except:
            pass

    def _save_favorites(self):
        try:
            data = {}
            for path in self._favorites:
                if os.path.exists(path):
                    data[path] = {"timestamp": time.time(), "filename": os.path.basename(path)}
            with open(self.favorites_file, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2)
        except:
            pass

    def _toggle_favorite(self):
        if not self.images:
            return
        path = self.images[self.current_image_index]
        if path in self._favorites:
            self._favorites.discard(path)
            self._show_temp_message("已取消收藏")
        else:
            self._favorites.add(path)
            self._show_temp_message("已收藏")
        self._save_favorites()

    def _is_favorited(self, path):
        return path in self._favorites

    def _play_favorites(self):
        fav = [p for p in self._favorites if os.path.exists(p)]
        if not fav:
            self._show_temp_message("收藏夹为空")
            return
        self.images = fav
        random.shuffle(self.images)
        self.index = 0
        self.current_image_index = 0
        self.playing = True
        with self._lock:
            self._processed_cache.clear()
        self._stop_all_timers()
        self._show_first_image()

    def _show_favorites_window(self):
        fav = [p for p in self._favorites if os.path.exists(p)]
        if not fav:
            self._show_temp_message("收藏夹为空")
            return
        win = Toplevel(self)
        win.title(f"收藏夹 ({len(fav)}张)")
        win.geometry("400x500")
        win.configure(bg=COLORS['bg_secondary'])
        win.attributes('-topmost', True)
        frame = tk.Frame(win, bg=COLORS['bg_secondary'])
        frame.pack(fill='both', expand=True, padx=5, pady=5)
        listbox = tk.Listbox(frame, bg=COLORS['bg_primary'], fg=COLORS['text_primary'],
                             selectbackground=COLORS['accent'], font=FONTS['body'],
                             bd=0, highlightthickness=0)
        scrollbar = tk.Scrollbar(frame, command=listbox.yview)
        listbox.config(yscrollcommand=scrollbar.set)
        sorted_fav = sorted(fav)
        for p in sorted_fav:
            listbox.insert('end', os.path.basename(p))
        listbox.pack(side='left', fill='both', expand=True)
        scrollbar.pack(side='right', fill='y')
        btn_frame = tk.Frame(win, bg=COLORS['bg_secondary'])
        btn_frame.pack(fill='x', padx=5, pady=5)

        def play_selected():
            sel = listbox.curselection()
            if sel:
                path = sorted_fav[sel[0]]
                if path in self.images:
                    idx = self.images.index(path)
                    self.index = idx
                    self.current_image_index = idx
                    self._show_image_for_index(idx)

        def play_all():
            self._play_favorites()
            win.destroy()

        ModernButton(btn_frame, text="跳转到选中", command=play_selected).pack(side='left', padx=5)
        ModernButton(btn_frame, text="播放全部收藏", command=play_all).pack(side='left', padx=5)

    # ═══════════════════ 播放控制 ═══════════════════

    def _start_slideshow_from_config(self):
        self.images = [os.path.join(self.folder_path, f)
                       for f in os.listdir(self.folder_path) if f.lower().endswith(VALID_EXT)]
        if self.images:
            random.shuffle(self.images)
            self.index = 0; self.current_image_index = 0
            self.playing = True
            self._show_first_image()
            self._start_preload_thread()
        else:
            self._show_start_tip()

    def _show_start_tip(self):
        self.playing = False
        self.title("右键选择图片文件夹")
        try:
            w = max(100, self.image_label.winfo_width())
            h = max(100, self.image_label.winfo_height())
            tip = Image.new("RGBA", (w, h), (0, 0, 0, 0))
            ImageDraw.Draw(tip).text((w // 2 - 80, h // 2 - 20),
                                     "右键选择图片文件夹", fill=(90, 90, 106, 200))
            photo = ImageTk.PhotoImage(tip)
            self.image_label.config(image=photo)
            self._photo_refs.append(photo)
        except:
            pass

    def _start_cleanup_timer(self):
        def cleanup():
            while len(self._photo_refs) > 20:
                self._photo_refs.pop(0)
            gc.collect()
            self.cleanup_timer = self.after(60000, cleanup)
        self.cleanup_timer = self.after(60000, cleanup)

    def _toggle_play_pause(self):
        if not self.images: return
        self.playing = not self.playing
        if self.playing:
            self._stop_all_timers()
            self.after_id = self.after(self.interval, self._show_image)
            self._start_preload_thread()
        if hasattr(self, 'play_pause_var'):
            self.play_pause_var.set("暂停" if self.playing else "开始")

    def next_image(self):
        if not self.images:
            return
        self._cancel_transition()
        self._stop_all_timers()
        target = (self.current_image_index + 1) % len(self.images)
        self.index = (target + 1) % len(self.images)
        self._show_image_for_index(target)
        if self.playing:
            self.after_id = self.after(self.interval, self._show_image)

    def previous_image(self):
        if not self.images:
            return
        self._cancel_transition()
        self._stop_all_timers()
        target = (self.current_image_index - 1) % len(self.images)
        if target < 0:
            target = len(self.images) - 1
        self.index = (target + 1) % len(self.images)
        self._show_image_for_index(target)
        if self.playing:
            self.after_id = self.after(self.interval, self._show_image)

    def shuffle_images(self):
        if not self.images: return
        random.shuffle(self.images)
        self.index = 0; self.current_image_index = 0
        self._show_image_for_index(0)
        self._show_temp_message("已随机排序")

    def set_image_mode(self, mode_str):
        self.image_mode = {"全图显示": 0, "拉伸": 1, "填充": 2}.get(mode_str, 0)
        with self._lock: self._processed_cache.clear()
        if self.images:
            self._show_image_for_index(self.current_image_index)
        self.save_config()

    def _browse_folder(self):
        if self.settings_window and self.settings_window.winfo_exists():
            self.settings_window.attributes('-topmost', False)
        folder = filedialog.askdirectory(title="选择图片文件夹")
        if self.settings_window and self.settings_window.winfo_exists():
            self.settings_window.attributes('-topmost', True)
        if folder:
            self._apply_folder(folder)
            if hasattr(self, 'folder_path_var'):
                self.folder_path_var.set(folder)

    def _apply_folder(self, folder):
        self.folder_path = folder
        self.images = [os.path.join(folder, f)
                       for f in os.listdir(folder) if f.lower().endswith(VALID_EXT)]
        if self.images:
            random.shuffle(self.images)
            self.index = 0; self.current_image_index = 0
            self.playing = True
            with self._lock:
                self._processed_cache.clear(); self._original_cache.clear()
            self._show_first_image()
            self._start_preload_thread()
            self._start_folder_watch()
        else:
            self._show_temp_message("文件夹中没有图片")
        self.save_config()

    def _stop_all_timers(self):
        for attr in ('after_id', 'cleanup_timer'):
            t = getattr(self, attr, None)
            if t:
                try: self.after_cancel(t)
                except: pass
                setattr(self, attr, None)

    # ═══════════════════ 右键菜单（已删除收藏功能）═══════════════════

    def show_context_menu(self, event):
        menu = tk.Menu(self, tearoff=0, bg=COLORS['bg_secondary'],
                       fg=COLORS['text_primary'],
                       activebackground=COLORS['accent'], activeforeground='#ffffff',
                       font=FONTS['body'], relief='flat', bd=0)
        menu.add_command(label=f"{ICONS['folder']} 选择文件夹", command=self._browse_folder)
        menu.add_separator()
        menu.add_command(label=f"{ICONS['prev']} 上一张", command=self.previous_image)
        menu.add_command(label=f"{ICONS['next']} 下一张", command=self.next_image)
        menu.add_command(label=(f"{ICONS['pause']} 暂停" if self.playing
                                else f"{ICONS['play']} 播放"), command=self._toggle_play_pause)
        menu.add_command(label=f"{ICONS['shuffle']} 随机排序", command=self.shuffle_images)
        menu.add_separator()
        menu.add_command(label="全屏查看", command=self.show_fullscreen)
        menu.add_separator()
        menu.add_command(label=f"{ICONS['settings']} 设置", command=self.open_settings_window)
        menu.add_command(label=f"{ICONS['delete']} 删除此部件",
                         command=lambda: self.manager.delete_widget(self))
        menu.tk_popup(event.x_root, event.y_root)

    # ═══════════════════ 键盘 ═══════════════════

    def _on_key_press(self, event):
        k = event.keysym
        if k in ('Left', 'Up'):
            self.previous_image()
        elif k in ('Right', 'Down'):
            self.next_image()
        elif k == 'space':
            self._toggle_play_pause()
        elif k == 'f':
            self.show_fullscreen()
        elif k == 's':
            self.shuffle_images()
        elif k == 'Escape' and self.is_fullscreen_open:
            self._force_close_fullscreen()

    def _on_close(self):
        self._stop_all_timers(); self._cancel_long_press_timer()
        self._cancel_transition(); self._stop_folder_watch()
        self._preload_stop.set()
        self._cancel_fullscreen_anim()
        if self.executor: self.executor.shutdown(wait=False)
        if self.fullscreen_window:
            try:
                if self.fullscreen_window.winfo_exists():
                    self.fullscreen_window.destroy()
            except: pass
        self.manager.unregister_widget(self)
        self.destroy()

    def _quit_app(self):
        self.manager.quit_app()

    # ═══════════════════ 设置应用方法 ═══════════════════

    def _apply_interval(self, *_):
        try:
            val = self.interval_var.get()
            self.interval = max(500, val * 1000)
            if self.playing:
                self._stop_all_timers()
                self.after_id = self.after(self.interval, self._show_image)
            self.save_config()
        except: pass

    def _apply_corner_radius(self, *_):
        try:
            r = self.radius_var.get()
            max_r = min(self.winfo_width(), self.winfo_height()) // 2
            r = min(r, max_r) if max_r > 0 else r
            if r != self.corner_radius:
                self.corner_radius = r
                with self._lock:
                    self._processed_cache.clear()
                    self._mask_cache.clear()
                if self.images:
                    self._show_image_for_index(self.current_image_index)
                self.save_config()
        except: pass

    def _apply_topmost(self):
        self.is_topmost = self.topmost_var.get()
        self.attributes('-topmost', self.is_topmost)
        self.save_config()

    def _apply_window_size(self, *_):
        try:
            w, h = self.width_var.get(), self.height_var.get()
            if w >= 100 and h >= 100:
                self.geometry(f"{w}x{h}")
                self.save_config()
        except: pass

    def _apply_global_collision(self):
        self.manager.set_collision(self.global_collision_var.get(), self.global_margin_var.get())

    def _apply_global_margin(self, *_):
        try: self.manager.set_collision(self.global_collision_var.get(), self.global_margin_var.get())
        except: pass

    def _apply_mouse_through(self):
        self.manager.set_mouse_through(self.mouse_through_var.get())

    def _apply_high_framerate(self):
        self.manager.set_high_framerate(self.hf_var.get())

    def reset_position(self):
        self.geometry(f"+{self.screen_width - self.winfo_width() - 20}+0")
        self.save_config()

    def _is_autostart_enabled(self):
        if platform.system() != 'Windows': return False
        try:
            import winreg
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                r"Software\Microsoft\Windows\CurrentVersion\Run", 0, winreg.KEY_READ)
            winreg.QueryValueEx(key, "FloatPicWidget")
            winreg.CloseKey(key); return True
        except: return False

    def _toggle_autostart(self):
        if platform.system() != 'Windows': return
        try:
            import winreg
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                r"Software\Microsoft\Windows\CurrentVersion\Run", 0, winreg.KEY_SET_VALUE)
            if self.autostart_var.get():
                winreg.SetValueEx(key, "FloatPicWidget", 0, winreg.REG_SZ,
                                  f'pythonw "{os.path.abspath(sys.argv[0])}"')
            else:
                try: winreg.DeleteValue(key, "FloatPicWidget")
                except: pass
            winreg.CloseKey(key)
        except: pass

    # ═══════════════════ 设置窗口（使用Notebook分页，来自备份文件）═══════════════════

    def _validate_entry_input(self, P, min_val, max_val):
        if P == "":
            return True
        try:
            val = int(P)
            return min_val <= val <= max_val
        except ValueError:
            return False

    def _create_labeled_scale_with_entry(self, parent, label_text, variable, from_, to_, row, unit=""):
        tk.Label(parent, text=label_text, fg=COLORS['text_primary'],
                 bg=COLORS['bg_primary'], font=FONTS['body']).grid(row=row, column=0, sticky="w", padx=10, pady=5)
        scale = tk.Scale(parent, from_=from_, to=to_, orient=tk.HORIZONTAL, variable=variable,
                         bg=COLORS['bg_elevated'], fg=COLORS['text_primary'], length=200,
                         troughcolor=COLORS['bg_secondary'], highlightthickness=0,
                         activebackground=COLORS['accent'], showvalue=False)
        scale.grid(row=row, column=1, padx=5, pady=5)
        vcmd = (parent.register(lambda P: self._validate_entry_input(P, from_, to_)), '%P')
        entry = tk.Entry(parent, textvariable=variable, width=6,
                         bg=COLORS['bg_elevated'], fg=COLORS['text_primary'],
                         insertbackground=COLORS['text_primary'], relief='flat',
                         highlightbackground=COLORS['border'], highlightthickness=1,
                         validate='key', validatecommand=vcmd)
        entry.grid(row=row, column=2, padx=5, pady=5)
        if unit:
            tk.Label(parent, text=unit, fg=COLORS['text_secondary'],
                     bg=COLORS['bg_primary'], font=FONTS['body']).grid(row=row, column=3, sticky="w")
        return scale, entry

    def open_settings_window(self):
        if self.settings_window and self.settings_window.winfo_exists():
            self.settings_window.lift()
            self.settings_window.focus_force()
            return

        self.settings_window = Toplevel(self)
        self.settings_window.title(f"设置 - 部件{self.widget_id}")
        self.settings_window.geometry("550x750")
        self.settings_window.configure(bg=COLORS['bg_primary'])
        self.settings_window.attributes('-topmost', True)

        self._settings_closing = False

        def on_settings_close():
            if self._settings_closing:
                return
            self._settings_closing = True
            self._close_settings_window()

        self.settings_window.protocol("WM_DELETE_WINDOW", on_settings_close)

        style = ttk.Style()
        style.theme_use('clam')
        style.configure('TNotebook', background=COLORS['bg_primary'])
        style.configure('TNotebook.Tab', background=COLORS['bg_secondary'],
                        foreground=COLORS['text_primary'], padding=[20, 10])
        style.map('TNotebook.Tab', background=[('selected', COLORS['accent'])])

        notebook = ttk.Notebook(self.settings_window)
        notebook.pack(fill="both", expand=True, padx=10, pady=10)

        # ===== 播放控制页 =====
        frame_play = tk.Frame(notebook, bg=COLORS['bg_primary'])
        notebook.add(frame_play, text="播放控制")
        tk.Label(frame_play, text="图片文件夹:", fg=COLORS['text_primary'], bg=COLORS['bg_primary'],
                 font=FONTS['body']).grid(row=0, column=0, sticky="w", padx=10, pady=5)
        self.folder_path_var = tk.StringVar(value=self.folder_path)
        entry_folder = tk.Entry(frame_play, textvariable=self.folder_path_var, width=40,
                                bg=COLORS['bg_elevated'], fg=COLORS['text_primary'],
                                insertbackground=COLORS['text_primary'], relief='flat',
                                highlightbackground=COLORS['border'], highlightthickness=1)
        entry_folder.grid(row=0, column=1, padx=5, pady=5)
        ModernButton(frame_play, text=f"{ICONS['folder']} 浏览", command=self._browse_folder).grid(row=0, column=2, padx=5)

        self.play_pause_var = tk.StringVar(value="暂停" if self.playing else "开始")
        ModernButton(frame_play, textvariable=self.play_pause_var, command=self._toggle_play_pause,
                     width=10).grid(row=1, column=0, padx=10, pady=10, sticky="w")
        ModernButton(frame_play, text="随机排序", command=self.shuffle_images).grid(row=1, column=1, padx=5, pady=10, sticky="w")

        # ===== 外观页 =====
        frame_app = tk.Frame(notebook, bg=COLORS['bg_primary'])
        notebook.add(frame_app, text="外观")

        self.radius_var = tk.IntVar(value=self.corner_radius)
        self._create_labeled_scale_with_entry(frame_app, "圆角半径:", self.radius_var, 0, 100, 0, "像素")
        self.radius_var.trace_add('write', lambda *a: self._apply_corner_radius())

        self.topmost_var = tk.BooleanVar(value=self.is_topmost)
        tk.Checkbutton(frame_app, text="置顶显示", variable=self.topmost_var,
                       command=self._apply_topmost, bg=COLORS['bg_primary'], fg=COLORS['text_primary'],
                       selectcolor=COLORS['bg_primary']).grid(row=1, column=0, sticky="w", padx=10, pady=10)

        tk.Label(frame_app, text="图片显示方式:", fg=COLORS['text_primary'],
                 bg=COLORS['bg_primary']).grid(row=2, column=0, sticky="w", padx=10, pady=5)
        self.mode_var = tk.StringVar(value=["全图显示", "拉伸", "填充"][self.image_mode])
        mode_combo = ttk.Combobox(frame_app, textvariable=self.mode_var,
                                  values=["全图显示", "拉伸", "填充"], state="readonly", width=15)
        mode_combo.grid(row=2, column=1, padx=5, pady=5, sticky="w")
        mode_combo.bind("<<ComboboxSelected>>", lambda e: self.set_image_mode(self.mode_var.get()))

        self.width_var = tk.IntVar(value=self.winfo_width())
        self._create_labeled_scale_with_entry(frame_app, "窗口宽度:", self.width_var, 100, 1920, 3, "像素")
        self.width_var.trace_add('write', lambda *a: self._apply_window_size())

        self.height_var = tk.IntVar(value=self.winfo_height())
        self._create_labeled_scale_with_entry(frame_app, "窗口高度:", self.height_var, 100, 1080, 4, "像素")
        self.height_var.trace_add('write', lambda *a: self._apply_window_size())

        btn_frame = tk.Frame(frame_app, bg=COLORS['bg_primary'])
        btn_frame.grid(row=5, column=0, columnspan=4, pady=10)
        ModernButton(btn_frame, text="重置窗口位置", command=self.reset_position).pack(side='left', padx=5)
        self.autostart_var = tk.BooleanVar(value=self._is_autostart_enabled())
        autostart_cb = tk.Checkbutton(btn_frame, text="开机自启动", variable=self.autostart_var,
                                      command=self._toggle_autostart, bg=COLORS['bg_primary'],
                                      fg=COLORS['text_primary'], selectcolor=COLORS['bg_primary'])
        autostart_cb.pack(side='left', padx=5)
        if platform.system() != 'Windows':
            autostart_cb.config(state='disabled')
            tk.Label(btn_frame, text="(仅Windows支持)", fg=COLORS['text_secondary'],
                     bg=COLORS['bg_primary']).pack(side='left', padx=5)

        # ===== 播放间隔页 =====
        frame_interval = tk.Frame(notebook, bg=COLORS['bg_primary'])
        notebook.add(frame_interval, text="播放间隔")
        self.interval_var = tk.IntVar(value=self.interval // 1000)
        self._create_labeled_scale_with_entry(frame_interval, "显示时间:", self.interval_var, 1, 3600, 0, "秒")
        self.interval_var.trace_add('write', lambda *a: self._apply_interval())

        # ===== 全局设置页 =====
        frame_global = tk.Frame(notebook, bg=COLORS['bg_primary'])
        notebook.add(frame_global, text="全局设置")
        self.global_collision_var = tk.BooleanVar(value=self.manager.collision_enabled)
        tk.Checkbutton(frame_global, text="避免部件重叠", variable=self.global_collision_var,
                       command=self._apply_global_collision, bg=COLORS['bg_primary'],
                       fg=COLORS['text_primary'], selectcolor=COLORS['bg_primary']).grid(row=0, column=0, sticky="w", padx=10, pady=10)

        self.global_margin_var = tk.IntVar(value=self.manager.collision_margin)
        self._create_labeled_scale_with_entry(frame_global, "碰撞间距:", self.global_margin_var, 0, 50, 1, "像素")
        self.global_margin_var.trace_add('write', lambda *a: self._apply_global_margin())

        self.mouse_through_var = tk.BooleanVar(value=self.manager.mouse_through)
        mouse_through_cb = tk.Checkbutton(
            frame_global, text="鼠标穿透（仅Windows）", variable=self.mouse_through_var,
            command=self._apply_mouse_through, bg=COLORS['bg_primary'],
            fg=COLORS['text_primary'], selectcolor=COLORS['bg_primary']
        )
        mouse_through_cb.grid(row=2, column=0, sticky="w", padx=10, pady=10)
        if platform.system() != 'Windows':
            mouse_through_cb.config(state='disabled')
            tk.Label(frame_global, text="(仅Windows支持)", fg=COLORS['text_secondary'],
                     bg=COLORS['bg_primary']).grid(row=2, column=1, sticky="w", padx=5)

        # 底部操作栏
        frame_bottom = tk.Frame(self.settings_window, bg=COLORS['bg_secondary'])
        frame_bottom.pack(side="bottom", fill="x", pady=10)
        ModernButton(frame_bottom, text="保存配置", command=self.save_config, width=12).pack(side='left', padx=20)
        ModernButton(frame_bottom, text="退出程序", command=self._quit_app, width=12).pack(side='right', padx=20)

    def _close_settings_window(self):
        if self.settings_window:
            try:
                if self.settings_window.winfo_exists():
                    self.settings_window.destroy()
            except:
                pass
            self.settings_window = None
        self._settings_closing = False

    def _show_save_feedback(self):
        if not self.settings_window or not self.settings_window.winfo_exists():
            return
        if hasattr(self, '_save_feedback_label') and self._save_feedback_label:
            try: self._save_feedback_label.destroy()
            except: pass
        label = tk.Label(self.settings_window, text="✓ 已保存",
                         fg=COLORS['success'], bg=COLORS['bg_secondary'], font=FONTS['body'])
        label.place(relx=0.5, rely=0.97, anchor='center')
        self._save_feedback_label = label

        def cleanup():
            try: label.destroy()
            except: pass
            if hasattr(self, '_save_feedback_label') and self._save_feedback_label is label:
                self._save_feedback_label = None
        self.settings_window.after(1500, cleanup)

    def _show_temp_message(self, msg, duration=1500):
        if hasattr(self, '_temp_msg_timer') and self._temp_msg_timer:
            try: self.after_cancel(self._temp_msg_timer)
            except: pass
        self.title(msg)
        def restore():
            self.title("浮动图片浏览器")
            self._temp_msg_timer = None
        self._temp_msg_timer = self.after(duration, restore)

    # ═══════════════════ 配置持久化 ═══════════════════

    def _apply_config(self, cfg):
        try: self.corner_radius = int(cfg.get('corner_radius', 12))
        except: self.corner_radius = 12
        try: self.image_mode = int(cfg.get('image_mode', 0))
        except: self.image_mode = 0
        try: self.interval = max(500, int(cfg.get('interval', 3000)))
        except: self.interval = 3000
        try: self.is_topmost = bool(cfg.get('is_topmost', False))
        except: self.is_topmost = False
        try: self.folder_path = str(cfg.get('folder_path', ''))
        except: self.folder_path = ''
        try: self.active = bool(cfg.get('active', True))
        except: self.active = True
        try: self.transition_type = int(cfg.get('transition_type', 0))
        except: self.transition_type = 0
        try: self.transition_duration = max(100, int(cfg.get('transition_duration', 400)))
        except: self.transition_duration = 400
        try: self.snap_enabled = bool(cfg.get('snap_enabled', True))
        except: self.snap_enabled = True
        try: self.long_press_threshold = max(100, int(cfg.get('long_press_threshold', 300)))
        except: self.long_press_threshold = 300
        try:
            w = max(100, int(cfg.get('window_width', 420)))
            h = max(100, int(cfg.get('window_height', 320)))
            x = int(cfg.get('window_x', self.screen_width - w - 20))
            y = int(cfg.get('window_y', 20))
            x = max(0, min(x, self.screen_width - w))
            y = max(0, min(y, self.screen_height - h))
            self.geometry(f"{w}x{h}+{x}+{y}")
        except:
            self.geometry(f"420x320+{self.screen_width - 440}+20")

    def save_config(self):
        try:
            geom = self.geometry().split('+')
            wh = geom[0].split('x')
            w, h = int(wh[0]), int(wh[1])
            x = int(geom[1]) if len(geom) > 1 else self.winfo_x()
            y = int(geom[2]) if len(geom) > 2 else self.winfo_y()
            cfg = {
                'widget_id': self.widget_id,
                'window_x': x, 'window_y': y,
                'window_width': w, 'window_height': h,
                'folder_path': self.folder_path,
                'interval': self.interval,
                'image_mode': self.image_mode,
                'corner_radius': self.corner_radius,
                'is_topmost': self.is_topmost,
                'active': self.active,
                'transition_type': self.transition_type,
                'transition_duration': self.transition_duration,
                'snap_enabled': self.snap_enabled,
                'long_press_threshold': self.long_press_threshold,
            }
            with open(self.config_file, 'w', encoding='utf-8') as f:
                json.dump(cfg, f, indent=2, ensure_ascii=False)
            if self.settings_window and self.settings_window.winfo_exists():
                self._show_save_feedback()
        except Exception as e:
            print(f"[FloatWidget] 保存配置失败: {e}")

    def load_config(self):
        cfg = {}
        try:
            if os.path.exists(self.config_file):
                with open(self.config_file, 'r', encoding='utf-8') as f:
                    content = f.read().strip()
                    if content:
                        cfg = json.loads(content)
            elif os.path.exists("float_widget_config.json"):
                with open("float_widget_config.json", 'r', encoding='utf-8') as f:
                    content = f.read().strip()
                    if content:
                        cfg = json.loads(content)
        except Exception as e:
            print(f"[FloatWidget] 配置文件解析失败，使用默认值: {e}")
            cfg = {}
        self._apply_config(cfg)

    # ═══════════════════ 切换动画 ═══════════════════

    def _cancel_transition(self):
        self._transition_gen += 1; self._transition_cancel = True
        if self._transition_timer:
            try: self.after_cancel(self._transition_timer)
            except: pass
            self._transition_timer = None
        self._transition_running = False

    def _transition_to(self, target_idx, callback=None):
        if not self.images or target_idx < 0 or target_idx >= len(self.images):
            if callback: callback(); return
        cur = self.current_image_index
        if (self.transition_type == 0 or len(self.images) < 2
                or cur == target_idx or cur < 0 or cur >= len(self.images)):
            self._show_image_for_index(target_idx)
            if callback: callback(); return
        self._cancel_transition()
        self._transition_running = True; self._transition_cancel = False
        my_gen = self._transition_gen
        cur_path, new_path = self.images[cur], self.images[target_idx]
        disp_w = max(100, self.image_label.winfo_width())
        disp_h = max(100, self.image_label.winfo_height())
        total_frames = max(10, self.transition_duration // FRAME_DELAY_MS)

        def prepare():
            try:
                if self._transition_cancel or self._transition_gen != my_gen: return
                ci = self._get_original_image(cur_path)
                ni = self._get_original_image(new_path)
                if not ci or not ni or self._transition_cancel or self._transition_gen != my_gen:
                    self.after(0, lambda: self._transition_done(target_idx, callback, my_gen)); return
                p1 = self._process_image(ci, self.image_mode, disp_w, disp_h)
                p2 = self._process_image(ni, self.image_mode, disp_w, disp_h)
                if not p1 or not p2:
                    self.after(0, lambda: self._transition_done(target_idx, callback, my_gen)); return
                if self.corner_radius > 0:
                    p1 = self._apply_rounded_corners_with_mask(p1, self.corner_radius)
                    p2 = self._apply_rounded_corners_with_mask(p2, self.corner_radius)
                if self._transition_cancel or self._transition_gen != my_gen: return
                frames = self._build_frames(p1, p2, disp_w, disp_h, total_frames)
                if self._transition_cancel or self._transition_gen != my_gen or not frames:
                    self.after(0, lambda: self._transition_done(target_idx, callback, my_gen)); return
                self.after(0, lambda: self._play_frames(frames, target_idx, callback, my_gen, self.transition_duration))
            except Exception as e:
                print(f"[FloatWidget] 动画准备失败: {e}")
                self.after(0, lambda: self._transition_done(target_idx, callback, my_gen))
        threading.Thread(target=prepare, daemon=True).start()

    def _transition_done(self, target_idx, callback=None, gen=None):
        if gen is not None and gen != self._transition_gen: return
        self._transition_running = False; self._transition_cancel = False
        self._show_image_for_index(target_idx)
        if callback: callback()

    def _play_frames(self, frames, target_idx, callback=None, gen=None, duration_ms=400):
        total = len(frames)
        if total == 0: self._transition_done(target_idx, callback, gen); return
        self._transition_cancel = False
        start_time = time.perf_counter()
        total_dur = duration_ms / 1000.0; last_fi = -1
        def on_done(): self._transition_done(target_idx, callback, gen)
        def step():
            nonlocal last_fi
            if self._transition_cancel or self._transition_gen != gen: on_done(); return
            t = min((time.perf_counter() - start_time) / total_dur, 1.0)
            fi = min(int(t * total), total - 1)
            if fi != last_fi:
                last_fi = fi
                try:
                    photo = ImageTk.PhotoImage(frames[fi])
                    self.image_label.config(image=photo)
                    self._photo_refs.append(photo)
                    if len(self._photo_refs) > 10: self._photo_refs.pop(0)
                except: on_done(); return
            if t >= 1.0: on_done()
            else: self._transition_timer = self.after(FRAME_DELAY_MS, step)
        step()

    def _build_frames(self, a, b, w, h, n):
        tt = self.transition_type
        if tt == 1: return self._gen_fade(a, b, w, h, n)
        elif tt == 2: return self._gen_slide(a, b, w, h, n, 'left')
        elif tt == 3: return self._gen_slide(a, b, w, h, n, 'right')
        elif tt == 4: return self._gen_slide(a, b, w, h, n, 'up')
        elif tt == 5: return self._gen_slide(a, b, w, h, n, 'down')
        elif tt == 6: return self._gen_zoom(a, b, w, h, n)
        elif tt == 7: return self._gen_rotate_zoom(a, b, w, h, n)
        return []

    def _gen_fade(self, a, b, w, h, n):
        frames = []
        for i in range(n + 1):
            if self._transition_cancel: return []
            frames.append(Image.blend(a, b, self._ease_in_out_quart(i / n)))
        return frames

    def _gen_slide(self, a, b, w, h, n, d):
        frames = []
        for i in range(n + 1):
            if self._transition_cancel: return []
            t = self._ease_out_back(i / n)
            c = Image.new("RGBA", (w, h), BG_RGBA)
            if d == 'left':
                o = int(t * w); c.paste(a, (-o, 0)); c.paste(b, (w - o, 0))
            elif d == 'right':
                o = int(t * w); c.paste(a, (o, 0)); c.paste(b, (-w + o, 0))
            elif d == 'up':
                o = int(t * h); c.paste(a, (0, -o)); c.paste(b, (0, h - o))
            elif d == 'down':
                o = int(t * h); c.paste(a, (0, o)); c.paste(b, (0, -h + o))
            frames.append(c)
        return frames

    def _gen_zoom(self, a, b, w, h, n):
        if a.mode != "RGBA": a = a.convert("RGBA")
        if b.mode != "RGBA": b = b.convert("RGBA")
        b_r, b_g, b_b, b_a = b.split()
        frames = []
        for i in range(n + 1):
            if self._transition_cancel: return []
            t = self._ease_out_cubic(i / n)
            canvas = Image.new("RGBA", (w, h), BG_RGBA)
            scale = 1.0 - 0.2 * t
            nw_o, nh_o = max(1, int(w * scale)), max(1, int(h * scale))
            old = a.resize((nw_o, nh_o), Image.Resampling.BILINEAR)
            if old.mode != "RGBA": old = old.convert("RGBA")
            r, g, bc, al = old.split()
            al = al.point(lambda x: int(x * (1.0 - t)))
            merged = Image.merge("RGBA", (r, g, bc, al))
            canvas.paste(merged, ((w - nw_o) // 2, (h - nh_o) // 2), merged)
            new_img = Image.merge("RGBA", (b_r, b_g, b_b, b_a.point(lambda x: int(x * t))))
            canvas.paste(new_img, (0, 0), new_img)
            frames.append(canvas)
        return frames

    def _gen_rotate_zoom(self, a, b, w, h, n):
        if a.mode != "RGBA": a = a.convert("RGBA")
        if b.mode != "RGBA": b = b.convert("RGBA")
        b_r, b_g, b_b, b_a = b.split()
        frames = []
        for i in range(n + 1):
            if self._transition_cancel: return []
            t = self._ease_out_cubic(min(1.0, i / n))
            canvas = Image.new("RGBA", (w, h), BG_RGBA)
            ns = max(1, int(max(w, h) * (1.0 - 0.3 * t)))
            old = a.resize((ns, ns), Image.Resampling.BILINEAR)
            if old.mode != "RGBA": old = old.convert("RGBA")
            old = old.rotate(-10 * t, expand=True, resample=Image.BILINEAR)
            r, g, bc, al = old.split()
            al = al.point(lambda x: int(x * (1.0 - t)))
            merged = Image.merge("RGBA", (r, g, bc, al))
            canvas.paste(merged, ((w - old.width) // 2, (h - old.height) // 2), merged)
            new_img = Image.merge("RGBA", (b_r, b_g, b_b, b_a.point(lambda x: int(x * t))))
            canvas.paste(new_img, (0, 0), new_img)
            frames.append(canvas)
        return frames

    def _preview_transition(self):
        if not self.images or len(self.images) < 2: return
        self._cancel_transition(); self._stop_all_timers()
        was_playing = self.playing
        cur = max(0, min(self.current_image_index, len(self.images) - 1))
        target = (cur + 1) % len(self.images)
        self.index = (target + 1) % len(self.images)
        def after_preview():
            self.index = (target + 1) % len(self.images)
            if was_playing:
                self.playing = True; self._stop_all_timers()
                self.after_id = self.after(self.interval, self._show_image)
        self._transition_to(target, callback=after_preview)

    # ═══════════════════ 全屏 ═══════════════════

    def _cancel_fullscreen_anim(self):
        self._fullscreen_anim_gen += 1
        if self._fullscreen_anim_id:
            try:
                if self.fullscreen_window and self.fullscreen_window.winfo_exists():
                    self.fullscreen_window.after_cancel(self._fullscreen_anim_id)
            except: pass
            self._fullscreen_anim_id = None
        self._fullscreen_anim_reverse = False
        self._fullscreen_anim_positions = []
        self._fullscreen_anim_bilinear = []
        self._fullscreen_anim_bilinear_done = False
        self._fullscreen_anim_base_img = None
        self._fullscreen_anim_total = 0
        self._fullscreen_image_id = None

    def _cancel_fullscreen_zoom_anim(self):
        if self._fullscreen_zoom_anim_id:
            try:
                if self.fullscreen_window and self.fullscreen_window.winfo_exists():
                    self.fullscreen_window.after_cancel(self._fullscreen_zoom_anim_id)
            except: pass
            self._fullscreen_zoom_anim_id = None

    def _fullscreen_cleanup(self):
        self._cancel_fullscreen_anim(); self._cancel_fullscreen_zoom_anim()
        self._stop_fullscreen_auto()
        self._fullscreen_closing = False
        self._fullscreen_zoom_level = 1.0; self._fullscreen_zoom_target = 1.0
        self._fullscreen_pan_x = 0; self._fullscreen_pan_y = 0
        self._fullscreen_base_img = None
        self._fullscreen_panning = False; self._fullscreen_pan_start = None
        self._fullscreen_left_start = None; self._fullscreen_left_dragging = False
        self._fullscreen_cached_photo = None
        self._fullscreen_cached_zw = 0; self._fullscreen_cached_zh = 0
        if self.fullscreen_window:
            try:
                if self.fullscreen_window.winfo_exists(): self.fullscreen_window.destroy()
            except: pass
            self.fullscreen_window = None; self.fullscreen_canvas = None
            self.is_fullscreen_open = False
            self.fullscreen_close_time = time.time() * 1000

    def _force_close_fullscreen(self):
        self._cancel_fullscreen_anim(); self._cancel_fullscreen_zoom_anim()
        self._stop_fullscreen_auto()
        self._fullscreen_closing = False
        self._fullscreen_zoom_level = 1.0; self._fullscreen_zoom_target = 1.0
        self._fullscreen_pan_x = 0; self._fullscreen_pan_y = 0
        self._fullscreen_base_img = None
        self._fullscreen_left_start = None; self._fullscreen_left_dragging = False
        self._fullscreen_cached_photo = None
        self._fullscreen_cached_zw = 0; self._fullscreen_cached_zh = 0
        if self.fullscreen_window:
            try:
                if self.fullscreen_window.winfo_exists(): self.fullscreen_window.destroy()
            except: pass
            self.fullscreen_window = None; self.fullscreen_canvas = None
            self.is_fullscreen_open = False
            self.fullscreen_close_time = time.time() * 1000

    def show_fullscreen(self):
        with self._fullscreen_lock:
            if not self.images: return
            if self._fullscreen_closing: return
            if self.fullscreen_window: self._force_close_fullscreen()
            self._show_fullscreen_impl()

    def _show_fullscreen_impl(self):
        idx = self.current_image_index
        if not self.images or idx >= len(self.images): return
        widget_x = self.winfo_rootx(); widget_y = self.winfo_rooty()
        widget_w = self.winfo_width() - 2 * self.PADDING
        widget_h = self.winfo_height() - 2 * self.PADDING
        sw = self.winfo_screenwidth(); sh = self.winfo_screenheight()
        image_mode = self.image_mode
        total_duration_ms = self.transition_duration
        total_frames = max(10, total_duration_ms // FRAME_DELAY_MS)
        self.fullscreen_window = Toplevel(self)
        self.fullscreen_window.title("")
        self.fullscreen_window.attributes('-topmost', True)
        self.fullscreen_window.configure(bg='black')
        self.fullscreen_window.geometry(f"{sw}x{sh}+0+0")
        self.fullscreen_window.overrideredirect(True)
        self.fullscreen_window.attributes('-alpha', 0.0)
        self.fullscreen_window.lift()
        self.fullscreen_canvas = tk.Canvas(self.fullscreen_window, bg='black', highlightthickness=0)
        self.fullscreen_canvas.pack(fill="both", expand=True)
        self.is_fullscreen_open = True
        self._fullscreen_anim_bilinear = []; self._fullscreen_anim_bilinear_done = False
        self._fullscreen_zoom_level = 1.0; self._fullscreen_zoom_target = 1.0
        self._fullscreen_pan_x = 0; self._fullscreen_pan_y = 0
        self._fullscreen_left_dragging = False; self._fullscreen_left_start = None

        def prepare():
            try:
                path = self.images[idx]
                orig = self._get_original_image(path)
                if orig is None: self.after(0, self._force_close_fullscreen); return
                iw, ih = orig.size
                if image_mode == 0:
                    ratio = min(widget_w / iw, widget_h / ih) if iw > 0 and ih > 0 else 1
                    img_w, img_h = round(iw * ratio), round(ih * ratio)
                    img_x, img_y = (widget_w - img_w) // 2, (widget_h - img_h) // 2
                elif image_mode == 1:
                    img_w, img_h, img_x, img_y = widget_w, widget_h, 0, 0
                else:
                    ratio = max(widget_w / iw, widget_h / ih) if iw > 0 and ih > 0 else 1
                    img_w, img_h = round(iw * ratio), round(ih * ratio)
                    img_x, img_y = (widget_w - img_w) // 2, (widget_h - img_h) // 2
                full_ratio = min(sw / iw, sh / ih) if iw > 0 and ih > 0 else 1
                full_w, full_h = round(iw * full_ratio), round(ih * full_ratio)
                full_x, full_y = (sw - full_w) // 2, (sh - full_h) // 2
                start_x, start_y = widget_x + img_x, widget_y + img_y
                start_w, start_h = img_w, img_h
                max_base = max(sw, sh) // 3
                base_img = orig.copy()
                if max(iw, ih) > max_base:
                    base_img.thumbnail((max_base, max_base), Image.Resampling.LANCZOS)
                positions = []
                for i in range(total_frames):
                    t = i / max(total_frames - 1, 1)
                    eased = self._ease_out_quart(t)
                    cw = max(1, round(start_w + (full_w - start_w) * eased))
                    ch = max(1, round(start_h + (full_h - start_h) * eased))
                    cx = round(start_x + (full_x - start_x) * eased)
                    cy = round(start_y + (full_y - start_y) * eased)
                    alpha = min(1.0, 0.3 + 0.7 * min(1.0, eased * 1.5))
                    positions.append((cw, ch, cx, cy, alpha))
                self.after(0, lambda: self._play_open_animation(idx, base_img, positions, total_duration_ms))
                bl = []
                for i in range(total_frames):
                    cw, ch = positions[i][0], positions[i][1]
                    s = base_img.resize((cw, ch), Image.Resampling.BILINEAR)
                    if s.mode != "RGBA": s = s.convert("RGBA")
                    bl.append((s, positions[i][2], positions[i][3], positions[i][4]))
                self._fullscreen_anim_bilinear = bl; self._fullscreen_anim_bilinear_done = True
            except Exception as e:
                print(f"[FloatWidget] 全屏动画准备失败: {e}")
                self.after(0, self._force_close_fullscreen)
        threading.Thread(target=prepare, daemon=True).start()

    def _get_anim_frame(self, positions, base_img, s):
        if self._fullscreen_anim_bilinear_done and s < len(self._fullscreen_anim_bilinear):
            return self._fullscreen_anim_bilinear[s]
        cw, ch, cx, cy, alpha = positions[s]
        scaled = base_img.resize((cw, ch), Image.Resampling.NEAREST)
        if scaled.mode != "RGBA": scaled = scaled.convert("RGBA")
        return (scaled, cx, cy, alpha)

    def _play_open_animation(self, idx, base_img, positions, total_duration_ms):
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists(): return
        total = len(positions)
        if total == 0: self._force_close_fullscreen(); return
        duration_s = total_duration_ms / 1000.0
        start_time = time.perf_counter()
        my_gen = self._fullscreen_anim_gen
        pil_img, cx, cy, alpha = self._get_anim_frame(positions, base_img, 0)
        photo = ImageTk.PhotoImage(pil_img)
        self.fullscreen_canvas.delete("all")
        self._fullscreen_image_id = self.fullscreen_canvas.create_image(cx, cy, anchor='nw', image=photo)
        self.fullscreen_window.photo = photo
        self.fullscreen_window.attributes('-alpha', alpha)
        self._fullscreen_anim_reverse = False
        self._fullscreen_anim_base_img = base_img
        self._fullscreen_anim_positions = positions
        self._fullscreen_anim_total = total
        self._fullscreen_anim_duration_s = duration_s
        self._fullscreen_anim_start_time = start_time
        self._fullscreen_anim_id = None

        def animate():
            if self._fullscreen_anim_gen != my_gen: self._fullscreen_anim_id = None; return
            if not self.fullscreen_window or not self.fullscreen_window.winfo_exists(): self._fullscreen_anim_id = None; return
            now = time.perf_counter()
            if self._fullscreen_anim_reverse:
                rev_elapsed = now - self._fullscreen_anim_rev_start_time
                rev_dur = self._fullscreen_anim_rev_start_t * duration_s
                if rev_dur <= 0.001: self._fullscreen_cleanup(); return
                t_linear = min(rev_elapsed / rev_dur, 1.0)
                t_visual = self._fullscreen_anim_rev_start_t * (1.0 - self._ease_in_out_cubic(t_linear))
                s = max(0, min(round(t_visual * (total - 1)), total - 1))
                pil_img, cx, cy, alpha = self._get_anim_frame(positions, base_img, s)
                photo = ImageTk.PhotoImage(pil_img)
                self.fullscreen_canvas.itemconfig(self._fullscreen_image_id, image=photo)
                self.fullscreen_canvas.coords(self._fullscreen_image_id, cx, cy)
                self.fullscreen_window.photo = photo
                self.fullscreen_window.attributes('-alpha', alpha)
                if t_linear >= 1.0: self._fullscreen_cleanup(); return
                self._fullscreen_anim_id = self.fullscreen_window.after(FRAME_DELAY_MS, animate)
            else:
                elapsed = now - start_time
                t = min(elapsed / duration_s, 1.0)
                s = min(round(t * (total - 1)), total - 1)
                pil_img, cx, cy, alpha = self._get_anim_frame(positions, base_img, s)
                photo = ImageTk.PhotoImage(pil_img)
                self.fullscreen_canvas.itemconfig(self._fullscreen_image_id, image=photo)
                self.fullscreen_canvas.coords(self._fullscreen_image_id, cx, cy)
                self.fullscreen_window.photo = photo
                self.fullscreen_window.attributes('-alpha', alpha)
                if t >= 1.0: self._on_zoom_animation_complete(idx); return
                self._fullscreen_anim_id = self.fullscreen_window.after(FRAME_DELAY_MS, animate)
        self._fullscreen_anim_id = self.fullscreen_window.after(FRAME_DELAY_MS, animate)

        def interrupt_and_close(event=None):
            with self._fullscreen_lock:
                if self._fullscreen_anim_reverse: return
                if self._fullscreen_anim_id:
                    self._fullscreen_anim_reverse = True
                    self._fullscreen_anim_rev_start_time = time.perf_counter()
                    self._fullscreen_anim_rev_start_t = min((time.perf_counter() - start_time) / duration_s, 1.0)
                    self._stop_fullscreen_auto()
                else:
                    self._stop_fullscreen_auto()
                    self._start_close_animation()
        self.fullscreen_window.bind("<Escape>", interrupt_and_close)
        self.fullscreen_window.protocol("WM_DELETE_WINDOW", interrupt_and_close)
        self.fullscreen_window.bind("<Button-1>", interrupt_and_close)
        if self.fullscreen_canvas: self.fullscreen_canvas.bind("<Button-1>", interrupt_and_close)

        def on_left(event):
            if self._fullscreen_anim_reverse: return
            if self._fullscreen_anim_id:
                self._fullscreen_anim_reverse = True
                self._fullscreen_anim_rev_start_time = time.perf_counter()
                self._fullscreen_anim_rev_start_t = min((time.perf_counter() - start_time) / duration_s, 1.0)
            else: self._fullscreen_previous()
        def on_right(event):
            if self._fullscreen_anim_reverse: return
            if self._fullscreen_anim_id:
                self._fullscreen_anim_reverse = True
                self._fullscreen_anim_rev_start_time = time.perf_counter()
                self._fullscreen_anim_rev_start_t = min((time.perf_counter() - start_time) / duration_s, 1.0)
            else: self._fullscreen_next()
        self.fullscreen_window.bind("<Left>", on_left)
        self.fullscreen_window.bind("<Right>", on_right)
        self.fullscreen_window.bind("<space>",
            lambda e: self._toggle_fullscreen_auto() if not self._fullscreen_anim_id else None)

    def _start_close_animation(self):
        if self._fullscreen_closing: return
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists():
            self._fullscreen_cleanup(); return
        self._fullscreen_closing = True
        self.fullscreen_close_time = time.time() * 1000
        self._cancel_fullscreen_anim(); self._cancel_fullscreen_zoom_anim()
        idx = self.current_image_index
        widget_x = self.winfo_rootx(); widget_y = self.winfo_rooty()
        widget_w = self.winfo_width() - 2 * self.PADDING
        widget_h = self.winfo_height() - 2 * self.PADDING
        sw = self.winfo_screenwidth(); sh = self.winfo_screenheight()
        image_mode = self.image_mode
        total_duration_ms = self.transition_duration
        total_frames = max(10, total_duration_ms // FRAME_DELAY_MS)
        self._fullscreen_anim_bilinear = []; self._fullscreen_anim_bilinear_done = False

        def prepare():
            try:
                path = self.images[idx]
                orig = self._get_original_image(path)
                if orig is None: self.after(0, self._fullscreen_cleanup); return
                iw, ih = orig.size
                if image_mode == 0:
                    ratio = min(widget_w / iw, widget_h / ih) if iw > 0 and ih > 0 else 1
                    img_w, img_h = round(iw * ratio), round(ih * ratio)
                    img_x, img_y = (widget_w - img_w) // 2, (widget_h - img_h) // 2
                elif image_mode == 1:
                    img_w, img_h, img_x, img_y = widget_w, widget_h, 0, 0
                else:
                    ratio = max(widget_w / iw, widget_h / ih) if iw > 0 and ih > 0 else 1
                    img_w, img_h = round(iw * ratio), round(ih * ratio)
                    img_x, img_y = (widget_w - img_w) // 2, (widget_h - img_h) // 2
                full_ratio = min(sw / iw, sh / ih) if iw > 0 and ih > 0 else 1
                full_w, full_h = round(iw * full_ratio), round(ih * full_ratio)
                full_x, full_y = (sw - full_w) // 2, (sh - full_h) // 2
                end_x, end_y = widget_x + img_x, widget_y + img_y
                end_w, end_h = img_w, img_h
                max_base = max(sw, sh) // 3
                base_img = orig.copy()
                if max(iw, ih) > max_base:
                    base_img.thumbnail((max_base, max_base), Image.Resampling.LANCZOS)
                positions = []
                for i in range(total_frames):
                    t = i / max(total_frames - 1, 1)
                    eased = self._ease_in_out_cubic(t)
                    cw = max(1, round(full_w + (end_w - full_w) * eased))
                    ch = max(1, round(full_h + (end_h - full_h) * eased))
                    cx = round(full_x + (end_x - full_x) * eased)
                    cy = round(full_y + (end_y - full_y) * eased)
                    alpha = 1.0 - 0.7 * eased
                    positions.append((cw, ch, cx, cy, alpha))
                self.after(0, lambda: self._play_close_animation(base_img, positions, total_duration_ms))
                bl = []
                for i in range(total_frames):
                    cw, ch = positions[i][0], positions[i][1]
                    s = base_img.resize((cw, ch), Image.Resampling.BILINEAR)
                    if s.mode != "RGBA": s = s.convert("RGBA")
                    bl.append((s, positions[i][2], positions[i][3], positions[i][4]))
                self._fullscreen_anim_bilinear = bl; self._fullscreen_anim_bilinear_done = True
            except Exception as e:
                print(f"[FloatWidget] 关闭动画失败: {e}")
                self.after(0, self._fullscreen_cleanup)
        threading.Thread(target=prepare, daemon=True).start()

    def _play_close_animation(self, base_img, positions, total_duration_ms):
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists(): self._fullscreen_cleanup(); return
        total = len(positions)
        if total == 0: self._fullscreen_cleanup(); return
        duration_s = total_duration_ms / 1000.0
        start_time = time.perf_counter()
        my_gen = self._fullscreen_anim_gen
        self._fullscreen_anim_positions = positions; self._fullscreen_anim_base_img = base_img
        pil_img, cx, cy, alpha = self._get_anim_frame(positions, base_img, 0)
        photo = ImageTk.PhotoImage(pil_img)
        if self._fullscreen_image_id is not None:
            self.fullscreen_canvas.itemconfig(self._fullscreen_image_id, image=photo)
            self.fullscreen_canvas.coords(self._fullscreen_image_id, cx, cy)
        else:
            self.fullscreen_canvas.delete("all")
            self._fullscreen_image_id = self.fullscreen_canvas.create_image(cx, cy, anchor='nw', image=photo)
        self.fullscreen_window.photo = photo
        self.fullscreen_window.attributes('-alpha', alpha)
        def animate_close():
            if self._fullscreen_anim_gen != my_gen: self._fullscreen_anim_id = None; return
            if not self.fullscreen_window or not self.fullscreen_window.winfo_exists(): self._fullscreen_cleanup(); return
            t = min((time.perf_counter() - start_time) / duration_s, 1.0)
            s = min(round(t * (total - 1)), total - 1)
            pil_img, cx, cy, alpha = self._get_anim_frame(positions, base_img, s)
            photo = ImageTk.PhotoImage(pil_img)
            self.fullscreen_canvas.itemconfig(self._fullscreen_image_id, image=photo)
            self.fullscreen_canvas.coords(self._fullscreen_image_id, cx, cy)
            self.fullscreen_window.photo = photo
            self.fullscreen_window.attributes('-alpha', alpha)
            if t >= 1.0: self._fullscreen_cleanup(); return
            self._fullscreen_anim_id = self.fullscreen_window.after(FRAME_DELAY_MS, animate_close)
        self._fullscreen_anim_id = self.fullscreen_window.after(FRAME_DELAY_MS, animate_close)

    def _on_zoom_animation_complete(self, idx):
        self._fullscreen_anim_id = None
        self._fullscreen_anim_positions = []
        self._fullscreen_anim_bilinear = []
        self._fullscreen_anim_bilinear_done = False
        self._fullscreen_anim_base_img = None
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists(): return
        self.fullscreen_window.unbind("<Button-1>")
        self.fullscreen_window.unbind("<Left>")
        self.fullscreen_window.unbind("<Right>")
        self.fullscreen_window.unbind("<space>")
        self._load_fullscreen_image_async(idx)
        self._create_fullscreen_navigation(idx)
        self.fullscreen_playing = self.playing
        self._update_fullscreen_auto_label()
        self._bind_fullscreen_zoom()
        self._fullscreen_left_dragging = False; self._fullscreen_left_start = None
        if self.fullscreen_canvas:
            self.fullscreen_canvas.bind("<Button-1>", self._on_fs_left_down)
            self.fullscreen_canvas.bind("<B1-Motion>", self._on_fs_left_motion)
            self.fullscreen_canvas.bind("<ButtonRelease-1>", self._on_fs_left_up)
        self.fullscreen_window.bind("<Escape>", lambda e: self._force_close_fullscreen())
        self.fullscreen_window.protocol("WM_DELETE_WINDOW", self._force_close_fullscreen)

    def _on_fs_left_down(self, event):
        self._fullscreen_left_start = (event.x, event.y)
        self._fullscreen_left_dragging = False
    def _on_fs_left_motion(self, event):
        if not self._fullscreen_left_start: return
        dx = event.x - self._fullscreen_left_start[0]
        dy = event.y - self._fullscreen_left_start[1]
        if not self._fullscreen_left_dragging:
            if abs(dx) >= 2 or abs(dy) >= 2: self._fullscreen_left_dragging = True
            else: return
        self._fullscreen_left_start = (event.x, event.y)
        if self._fullscreen_zoom_level > self._fullscreen_zoom_min:
            self._fullscreen_pan_x += dx; self._fullscreen_pan_y += dy
            self._render_fullscreen_zoomed()
    def _on_fs_left_up(self, event):
        dragged = self._fullscreen_left_dragging
        self._fullscreen_left_start = None; self._fullscreen_left_dragging = False
        if dragged: return
        if not self._fullscreen_closing: self._start_close_animation()

    def _bind_fullscreen_zoom(self):
        win = self.fullscreen_window
        if not win or not win.winfo_exists(): return
        win.bind("<MouseWheel>", self._on_fullscreen_scroll)
        win.bind("<Button-4>", lambda e: self._on_fullscreen_scroll_linux(e, 1))
        win.bind("<Button-5>", lambda e: self._on_fullscreen_scroll_linux(e, -1))
        win.bind("<Button-2>", self._on_pan_start)
        win.bind("<B2-Motion>", self._on_pan_move)
        win.bind("<ButtonRelease-2>", self._on_pan_end)
        win.bind("<Button-3>", lambda e: self._force_close_fullscreen() if not self._fullscreen_closing else None)

    def _on_fullscreen_scroll(self, event):
        self._apply_fullscreen_zoom(1 if event.delta > 0 else -1)
    def _on_fullscreen_scroll_linux(self, event, delta):
        self._apply_fullscreen_zoom(delta)

    def _apply_fullscreen_zoom(self, direction):
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists(): return
        if not self._fullscreen_base_img: return
        factor = (1 + self._fullscreen_zoom_step) if direction > 0 else 1 / (1 + self._fullscreen_zoom_step)
        self._fullscreen_zoom_target = max(self._fullscreen_zoom_min,
            min(self._fullscreen_zoom_target * factor, self._fullscreen_zoom_max))
        if not self._fullscreen_zoom_anim_id:
            self._zoom_anim_loop()

    def _zoom_anim_loop(self):
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists():
            self._fullscreen_zoom_anim_id = None; return
        if self._fullscreen_panning:
            self._fullscreen_zoom_anim_id = self.fullscreen_window.after(FRAME_DELAY_MS, self._zoom_anim_loop)
            return
        diff = self._fullscreen_zoom_target - self._fullscreen_zoom_level
        if abs(diff) < 0.005:
            self._fullscreen_zoom_level = self._fullscreen_zoom_target
            self._render_fullscreen_zoomed(force=True)
            self._fullscreen_zoom_anim_id = None; return
        self._fullscreen_zoom_level += diff * self._fullscreen_zoom_lerp
        if self._fullscreen_zoom_level <= self._fullscreen_zoom_min + 0.01:
            self._fullscreen_pan_x = 0; self._fullscreen_pan_y = 0
        self._render_zoom_frame()
        self._fullscreen_zoom_anim_id = self.fullscreen_window.after(FRAME_DELAY_MS, self._zoom_anim_loop)

    def _render_zoom_frame(self):
        if not self._fullscreen_base_img or not self.fullscreen_canvas: return
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists(): return
        base = self._fullscreen_base_img
        bw, bh = base.size
        sw = self.fullscreen_window.winfo_screenwidth()
        sh = self.fullscreen_window.winfo_screenheight()
        zl = self._fullscreen_zoom_level
        zw = max(1, int(bw * zl)); zh = max(1, int(bh * zl))
        ox = (sw - zw) // 2 + self._fullscreen_pan_x
        oy = (sh - zh) // 2 + self._fullscreen_pan_y
        vx1 = max(0, -ox); vy1 = max(0, -oy)
        vx2 = min(zw, sw - ox); vy2 = min(zh, sh - oy)
        if vx1 >= vx2 or vy1 >= vy2: return
        bx1 = max(0, min(bw, int(vx1 / zl)))
        by1 = max(0, min(bh, int(vy1 / zl)))
        bx2 = max(0, min(bw, int(math.ceil(vx2 / zl))))
        by2 = max(0, min(bh, int(math.ceil(vy2 / zl))))
        if bx1 >= bx2 or by1 >= by2: return
        crop = base.crop((bx1, by1, bx2, by2))
        out_w = max(1, vx2 - vx1); out_h = max(1, vy2 - vy1)
        if crop.size != (out_w, out_h):
            crop = crop.resize((out_w, out_h), Image.Resampling.NEAREST)
        if crop.mode != "RGBA": crop = crop.convert("RGBA")
        photo = ImageTk.PhotoImage(crop)
        cx = max(0, ox); cy = max(0, oy)
        if self._fullscreen_image_id is not None:
            self.fullscreen_canvas.itemconfig(self._fullscreen_image_id, image=photo)
            self.fullscreen_canvas.coords(self._fullscreen_image_id, cx, cy)
        else:
            self.fullscreen_canvas.delete("all")
            self._fullscreen_image_id = self.fullscreen_canvas.create_image(cx, cy, image=photo, anchor="nw")
        self.fullscreen_window.photo = photo
        self._update_zoom_label()

    def _render_fullscreen_zoomed(self, force=False):
        if not self._fullscreen_base_img or not self.fullscreen_canvas: return
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists(): return
        base = self._fullscreen_base_img
        bw, bh = base.size
        sw = self.fullscreen_window.winfo_screenwidth()
        sh = self.fullscreen_window.winfo_screenheight()
        zl = self._fullscreen_zoom_level
        zw = max(1, int(bw * zl)); zh = max(1, int(bh * zl))
        if force or zw != self._fullscreen_cached_zw or zh != self._fullscreen_cached_zh:
            scaled = base.resize((zw, zh), Image.Resampling.BILINEAR)
            if scaled.mode != "RGBA": scaled = scaled.convert("RGBA")
            photo = ImageTk.PhotoImage(scaled)
            self._fullscreen_cached_photo = photo
            self._fullscreen_cached_zw = zw; self._fullscreen_cached_zh = zh
        else:
            photo = self._fullscreen_cached_photo
        if photo is None: return
        ox = (sw - zw) // 2 + self._fullscreen_pan_x
        oy = (sh - zh) // 2 + self._fullscreen_pan_y
        if self._fullscreen_image_id is not None:
            self.fullscreen_canvas.itemconfig(self._fullscreen_image_id, image=photo)
            self.fullscreen_canvas.coords(self._fullscreen_image_id, ox, oy)
        else:
            self.fullscreen_canvas.delete("all")
            self._fullscreen_image_id = self.fullscreen_canvas.create_image(ox, oy, image=photo, anchor="nw")
        self.fullscreen_window.photo = photo
        self._update_zoom_label()

    def _update_zoom_label(self):
        if (self.fullscreen_window and self.fullscreen_window.winfo_exists()
                and hasattr(self.fullscreen_window, 'zoom_label')):
            self.fullscreen_window.zoom_label.config(text=f"{int(self._fullscreen_zoom_level * 100)}%")

    def _on_pan_start(self, event):
        if self._fullscreen_zoom_level > self._fullscreen_zoom_min:
            self._fullscreen_panning = True
            self._fullscreen_pan_start = (event.x, event.y)
    def _on_pan_move(self, event):
        if not self._fullscreen_panning or not self._fullscreen_pan_start: return
        dx = event.x - self._fullscreen_pan_start[0]
        dy = event.y - self._fullscreen_pan_start[1]
        self._fullscreen_pan_x += dx; self._fullscreen_pan_y += dy
        self._fullscreen_pan_start = (event.x, event.y)
        if self._fullscreen_cached_photo and self.fullscreen_canvas:
            sw = self.fullscreen_window.winfo_screenwidth()
            sh = self.fullscreen_window.winfo_screenheight()
            ox = (sw - self._fullscreen_cached_zw) // 2 + self._fullscreen_pan_x
            oy = (sh - self._fullscreen_cached_zh) // 2 + self._fullscreen_pan_y
            if self._fullscreen_image_id is not None:
                self.fullscreen_canvas.coords(self._fullscreen_image_id, ox, oy)
            self._update_zoom_label()
    def _on_pan_end(self, event):
        self._fullscreen_panning = False; self._fullscreen_pan_start = None
        self._render_fullscreen_zoomed(force=True)

    def _create_fullscreen_navigation(self, initial_index):
        win = self.fullscreen_window
        if not win or not win.winfo_exists(): return
        win.current_index = initial_index; win._nav_visible = False
        left_btn = ModernButton(win, text="◀", font=FONTS['icon'], width=3, height=2, padx=0, pady=0)
        left_btn.bind("<Button-1>", lambda e: self._fullscreen_previous())
        right_btn = ModernButton(win, text="▶", font=FONTS['icon'], width=3, height=2, padx=0, pady=0)
        right_btn.bind("<Button-1>", lambda e: self._fullscreen_next())
        win.left_btn = left_btn; win.right_btn = right_btn
        def on_mouse_move(event):
            if event.x < 100 or event.x > win.winfo_width() - 100:
                if not win._nav_visible:
                    win._nav_visible = True
                    left_btn.place(x=20, rely=0.5, anchor="w")
                    right_btn.place(relx=1.0, x=-20, rely=0.5, anchor="e")
            else:
                if win._nav_visible:
                    win._nav_visible = False
                    left_btn.place_forget(); right_btn.place_forget()
        win.bind('<Motion>', on_mouse_move)
        info_frame = tk.Frame(win, bg=COLORS['bg_secondary'], bd=0)
        info_frame.place(x=20, y=20)
        win.info_label = tk.Label(info_frame, text=f"{initial_index + 1} / {len(self.images)}",
            font=FONTS['body'], bg=COLORS['bg_secondary'], fg=COLORS['text_primary'], padx=12, pady=6)
        win.info_label.pack(side="left")
        win.auto_label = tk.Label(info_frame, text="自动播放", font=FONTS['body'],
            bg=COLORS['bg_secondary'], fg=COLORS['text_secondary'], padx=8)
        win.auto_label.pack(side="left")
        win.zoom_label = tk.Label(info_frame, text="100%", font=FONTS['body'],
            bg=COLORS['bg_secondary'], fg=COLORS['accent'], padx=8)
        win.zoom_label.pack(side="left")
        self._update_fullscreen_auto_label()

    def _update_fullscreen_auto_label(self):
        if (self.fullscreen_window and self.fullscreen_window.winfo_exists()
                and hasattr(self.fullscreen_window, 'auto_label')):
            try:
                self.fullscreen_window.auto_label.config(
                    text="自动播放中" if self.fullscreen_playing else "暂停",
                    fg=COLORS['success'] if self.fullscreen_playing else COLORS['error'])
            except: pass

    def _toggle_fullscreen_auto(self, event=None):
        if not self.fullscreen_window or self._fullscreen_anim_id: return
        if self.fullscreen_playing: self._stop_fullscreen_auto()
        else: self._start_fullscreen_auto()
    def _start_fullscreen_auto(self):
        if self.fullscreen_playing or self._fullscreen_anim_id: return
        self.fullscreen_playing = True
        self._update_fullscreen_auto_label()
        self._schedule_fullscreen_auto()
    def _stop_fullscreen_auto(self):
        if not self.fullscreen_playing: return
        self.fullscreen_playing = False
        if self.fullscreen_after_id:
            try:
                if self.fullscreen_window and self.fullscreen_window.winfo_exists():
                    self.fullscreen_window.after_cancel(self.fullscreen_after_id)
            except: pass
            self.fullscreen_after_id = None
        self._update_fullscreen_auto_label()

    def _schedule_fullscreen_auto(self):
        if not self.fullscreen_playing or not self.fullscreen_window:
            return
        try:
            self.fullscreen_after_id = self.fullscreen_window.after(
                self.interval, self._fullscreen_auto_next)
        except:
            pass

    def _fullscreen_auto_next(self):
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists() or \
           not self.fullscreen_playing or self._fullscreen_anim_id:
            return
        self._fullscreen_next()
        self._schedule_fullscreen_auto()

    def _fullscreen_previous(self):
        if not self.images or not self.fullscreen_window or \
           not self.fullscreen_window.winfo_exists():
            return
        if self._fullscreen_anim_id:
            self._force_close_fullscreen()
            self.show_fullscreen()
            return
        new_idx = (self.fullscreen_window.current_index - 1) % len(self.images)
        self.fullscreen_window.current_index = new_idx
        self.index = new_idx
        self.current_image_index = new_idx
        self._cancel_fullscreen_zoom_anim()
        self._fullscreen_zoom_level = 1.0; self._fullscreen_zoom_target = 1.0
        self._fullscreen_pan_x = 0; self._fullscreen_pan_y = 0
        self._fullscreen_base_img = None
        self._fullscreen_cached_photo = None
        self._fullscreen_cached_zw = 0; self._fullscreen_cached_zh = 0
        if hasattr(self.fullscreen_window, 'info_label'):
            try:
                self.fullscreen_window.info_label.config(text=f"{new_idx + 1} / {len(self.images)}")
            except: pass
        self._update_zoom_label()
        self._load_fullscreen_image_async(new_idx)
        self.after(50, lambda: self._show_image_for_index(new_idx))
        if self.fullscreen_playing:
            if self.fullscreen_after_id:
                try: self.fullscreen_window.after_cancel(self.fullscreen_after_id)
                except: pass
            self._schedule_fullscreen_auto()

    def _fullscreen_next(self):
        if not self.images or not self.fullscreen_window or \
           not self.fullscreen_window.winfo_exists():
            return
        if self._fullscreen_anim_id:
            self._force_close_fullscreen()
            self.show_fullscreen()
            return
        new_idx = (self.fullscreen_window.current_index + 1) % len(self.images)
        self.fullscreen_window.current_index = new_idx
        self.index = new_idx
        self.current_image_index = new_idx
        self._cancel_fullscreen_zoom_anim()
        self._fullscreen_zoom_level = 1.0; self._fullscreen_zoom_target = 1.0
        self._fullscreen_pan_x = 0; self._fullscreen_pan_y = 0
        self._fullscreen_base_img = None
        self._fullscreen_cached_photo = None
        self._fullscreen_cached_zw = 0; self._fullscreen_cached_zh = 0
        if hasattr(self.fullscreen_window, 'info_label'):
            try:
                self.fullscreen_window.info_label.config(text=f"{new_idx + 1} / {len(self.images)}")
            except: pass
        self._update_zoom_label()
        self._load_fullscreen_image_async(new_idx)
        self.after(50, lambda: self._show_image_for_index(new_idx))
        if self.fullscreen_playing:
            if self.fullscreen_after_id:
                try: self.fullscreen_window.after_cancel(self.fullscreen_after_id)
                except: pass
            self._schedule_fullscreen_auto()

    def _load_fullscreen_image_async(self, idx):
        if self._loading_future and not self._loading_future.done():
            self._stop_loading.set()
            self._loading_future.cancel()
        self._stop_loading.clear()
        self._loading_future = self.executor.submit(self._load_fullscreen_image_worker, idx)

    def _load_fullscreen_image_worker(self, idx):
        if self._stop_loading.is_set(): return
        if idx < 0 or idx >= len(self.images): return
        path = self.images[idx]
        if not self.fullscreen_window or not self.fullscreen_window.winfo_exists(): return
        try:
            sw = self.fullscreen_window.winfo_screenwidth()
            sh = self.fullscreen_window.winfo_screenheight()
        except: return
        key = hashlib.md5(f"full_{path}_{sw}_{sh}".encode()).hexdigest()
        def generate():
            if self._stop_loading.is_set(): return None
            orig = self._get_original_image(path)
            if orig is None: return None
            w, h = orig.size
            ratio = min(sw / w, sh / h) if w > 0 and h > 0 else 1
            nw, nh = int(w * ratio), int(h * ratio)
            if nw <= 0 or nh <= 0: return None
            resized = orig.resize((nw, nh), Image.Resampling.LANCZOS)
            bg = Image.new("RGBA", (sw, sh), BG_RGBA)
            x, y = (sw - nw) // 2, (sh - nh) // 2
            if resized.mode != "RGBA": resized = resized.convert("RGBA")
            bg.paste(resized, (x, y))
            return bg
        full_img = self._get_fullscreen_image(key, generate)
        if full_img is None or self._stop_loading.is_set(): return
        self.after(0, lambda: self._update_fullscreen_image(full_img))

    # ===== 修复：全屏高清图加载后重置坐标到(0,0) =====
    def _update_fullscreen_image(self, img):
        self._fullscreen_base_img = img
        if self.fullscreen_window and self.fullscreen_window.winfo_exists() and self.fullscreen_canvas:
            try:
                photo = ImageTk.PhotoImage(img)
                if self._fullscreen_image_id is not None:
                    self.fullscreen_canvas.itemconfig(self._fullscreen_image_id, image=photo)
                    self.fullscreen_canvas.coords(self._fullscreen_image_id, 0, 0)
                else:
                    self.fullscreen_canvas.delete("all")
                    self._fullscreen_image_id = self.fullscreen_canvas.create_image(0, 0, image=photo, anchor="nw")
                self.fullscreen_window.photo = photo
            except: pass

    # ═══════════════════ 部件鼠标交互 ═══════════════════

    def _bind_events(self):
        self.canvas.bind("<Button-3>", self.show_context_menu)
        self.image_label.bind("<Button-3>", self.show_context_menu)
        self.bind("<Button-3>", self.show_context_menu)
        self.bind("<Button-1>", self._on_left_down)
        self.bind("<ButtonRelease-1>", self._on_left_up)
        self.bind("<B1-Motion>", self._on_left_motion)
        self.bind("<KeyPress>", self._on_key_press)
        self.bind("<Configure>", self._on_resize_throttled)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    def _on_left_down(self, event):
        self.click_start_time = time.time() * 1000
        self.click_start_pos = (event.x_root, event.y_root)
        self.is_long_press = False
        self.dragging = False
        self.drag_started = False
        self.drag_moved = False
        win_x, win_y = self.winfo_x(), self.winfo_y()
        self.drag_offset_x = event.x_root - win_x
        self.drag_offset_y = event.y_root - win_y
        self.window_start_x, self.window_start_y = win_x, win_y
        self._long_press_timer_id = self.after(self.long_press_threshold, self._check_long_press)

    def _check_long_press(self):
        if self.click_start_time and (time.time() * 1000 - self.click_start_time >= self.long_press_threshold):
            if not self.drag_started:
                self.is_long_press = True
                self.dragging = True
                self.drag_started = True
                self._on_drag_start()
        self._long_press_timer_id = None

    def _cancel_long_press_timer(self):
        if self._long_press_timer_id:
            try: self.after_cancel(self._long_press_timer_id)
            except: pass
            self._long_press_timer_id = None

    def _on_left_motion(self, event):
        if self.click_start_pos is None: return
        if not self.drag_started:
            dx = event.x_root - self.click_start_pos[0]
            dy = event.y_root - self.click_start_pos[1]
            if dx * dx + dy * dy >= self.drag_threshold_sq:
                self.dragging = True; self.drag_started = True; self.drag_moved = True
                self.drag_offset_x = event.x_root - self.winfo_x()
                self.drag_offset_y = event.y_root - self.winfo_y()
                self._on_drag_start()
            return
        if not self.dragging: return
        target_x = event.x_root - self.drag_offset_x
        target_y = event.y_root - self.drag_offset_y
        if self.manager.collision_enabled:
            cur_x, cur_y = self.winfo_x(), self.winfo_y()
            dx, dy = target_x - cur_x, target_y - cur_y
            new_x, _, ok_h, _ = self.manager.resolve_overlap(self, target_x, cur_y, dx, 0)
            if not ok_h: new_x = cur_x
            final_x, final_y, ok_v, _ = self.manager.resolve_overlap(self, new_x, target_y, 0, dy)
            if not ok_v: final_y = cur_y
        else:
            final_x, final_y = target_x, target_y
        if self.snap_enabled:
            final_x, final_y = self._apply_edge_snap(final_x, final_y)
        pad = self.PADDING
        w, h = self.winfo_width() - 2 * pad, self.winfo_height() - 2 * pad
        final_x = max(-pad, min(final_x, self.screen_width - w - pad))
        final_y = max(-pad, min(final_y, self.screen_height - h - pad))
        self.geometry(f"+{int(final_x)}+{int(final_y)}")
        self._update_drag_title(final_x, final_y)

    def _on_left_up(self, event):
        self._cancel_long_press_timer()
        if self.dragging:
            self.dragging = False; self.drag_started = False
            self._on_drag_end()
            self.after_idle(self.save_config)
        else:
            if not self.is_long_press:
                if self.fullscreen_close_time > 0 and \
                   (time.time() * 1000 - self.fullscreen_close_time < self.fullscreen_ignore_time):
                    self.click_start_time = None; self.click_start_pos = None
                    return
                self._handle_click(event)
        self.click_start_time = None; self.click_start_pos = None
        self.is_long_press = False

    def _on_drag_start(self):
        try: self.config(cursor="fleur")
        except: pass

    def _on_drag_end(self):
        try: self.config(cursor="")
        except: pass
        self.title("浮动图片浏览器")

    def _update_drag_title(self, x, y):
        snap = " | 吸附" if (self.snap_target_x is not None or self.snap_target_y is not None) else ""
        self.title(f"({int(x)}, {int(y)}){snap}")

    def _apply_edge_snap(self, x, y):
        self.snap_target_x = self.snap_target_y = None
        zone = self.snap_zone
        w, h = self.winfo_width(), self.winfo_height()
        if abs(x) < zone:
            x = 0; self.snap_target_x = 0
        elif abs(x - (self.screen_width - w)) < zone:
            x = self.screen_width - w; self.snap_target_x = x
        if abs(y) < zone:
            y = 0; self.snap_target_y = 0
        elif abs(y - (self.screen_height - h)) < zone:
            y = self.screen_height - h; self.snap_target_y = y
        return x, y

    def _handle_click(self, event):
        try:
            lx = self.image_label.winfo_x()
            ly = self.image_label.winfo_y()
            lw = self.image_label.winfo_width()
            lh = self.image_label.winfo_height()
            x_in, y_in = event.x - lx, event.y - ly
            if 0 <= x_in < lw and 0 <= y_in < lh:
                third = lw / 3
                if x_in < third:
                    self.previous_image(); self.last_click_time = 0
                elif x_in >= 2 * third:
                    self.next_image(); self.last_click_time = 0
                else:
                    self.show_fullscreen(); self.last_click_time = 0
            else:
                now = time.time() * 1000
                if now - self.last_click_time < self.double_click_threshold:
                    self.last_click_time = 0; self.show_fullscreen()
                else:
                    self.last_click_time = now
        except Exception as e:
            print(f"[FloatWidget] 处理点击出错: {e}")

    # ═══════════════════ UI 初始化 ═══════════════════

    def _init_ui(self):
        self.attributes('-topmost', self.is_topmost)
        self.attributes('-alpha', 1.0)
        self.canvas = tk.Canvas(self, bg=COLORS['bg_primary'], highlightthickness=0, bd=0)
        self.canvas.pack(fill="both", expand=True)
        self.image_label = tk.Label(self.canvas, bg=COLORS['bg_primary'], bd=0, highlightthickness=0)
        self.update_idletasks()
        w, h = self.winfo_width(), self.winfo_height()
        if w <= 0 or h <= 0: w, h = 420, 320
        self._place_image_label(w, h)

    def _place_image_label(self, width, height):
        pad = self.PADDING
        self.image_label.place(x=pad, y=pad, width=width - 2 * pad, height=height - 2 * pad)

    def _on_resize_throttled(self, event):
        if event.widget == self:
            if hasattr(self, '_resize_timer'):
                try: self.after_cancel(self._resize_timer)
                except: pass
            self._resize_timer = self.after(100, lambda: self._on_resize(event))

    def _on_resize(self, event):
        if event.widget == self and event.width > 0 and event.height > 0:
            if event.width == self._last_width and event.height == self._last_height: return
            self._on_resize_impl(event.width, event.height)

    def _on_resize_impl(self, width, height):
        self._last_width, self._last_height = width, height
        with self._lock: self._processed_cache.clear()
        self._place_image_label(width, height)
        if self.playing and self.images:
            self.after(50, self._update_current_image)

    def _update_current_image(self):
        if self.playing and self.images:
            self._show_image_for_index(self.current_image_index)

    # ═══════════════════ 图片处理核心 ═══════════════════

    def _get_rounded_mask(self, width, height, radius):
        key = (width, height, radius)
        if key in self._mask_cache: return self._mask_cache[key]
        scale = 4
        sw, sh = width * scale, height * scale
        sr = radius * scale
        mask = Image.new("L", (sw, sh), 0)
        draw = ImageDraw.Draw(mask)
        draw.rounded_rectangle([(0, 0), (sw, sh)], radius=sr, fill=255)
        mask = mask.resize((width, height), Image.Resampling.NEAREST)
        self._mask_cache[key] = mask
        if len(self._mask_cache) > 10:
            self._mask_cache.pop(next(iter(self._mask_cache)))
        return mask

    def _apply_rounded_corners_with_mask(self, img, radius):
        if radius <= 0: return img
        w, h = img.size
        mask = self._get_rounded_mask(w, h, radius)
        if img.mode != "RGBA": img = img.convert("RGBA")
        img.putalpha(mask)
        return img

    @synchronized('_lock')
    def _get_original_image(self, path):
        if path in self._original_cache: return self._original_cache[path]
        try:
            with Image.open(path) as img:
                img = img.copy()
                self._original_cache[path] = img
                return img
        except Exception as e:
            print(f"[FloatWidget] 加载原始图片失败 {path}: {e}")
            return None

    @synchronized('_lock')
    def _get_processed_image(self, key, loader):
        if key in self._processed_cache: return self._processed_cache[key]
        img = loader()
        if img is not None: self._processed_cache[key] = img
        return img

    @synchronized('_lock')
    def _get_fullscreen_image(self, key, loader):
        if key in self._fullscreen_cache: return self._fullscreen_cache[key]
        img = loader()
        if img is not None: self._fullscreen_cache[key] = img
        return img

    @synchronized('_lock')
    def _get_thumbnail(self, path, size=(200, 150)):
        key = (path, size)
        if key in self._thumbnail_cache: return self._thumbnail_cache[key]
        orig = self._get_original_image(path)
        if orig is None: return None
        thumb = orig.copy()
        thumb.thumbnail(size, Image.Resampling.LANCZOS)
        self._thumbnail_cache[key] = thumb
        return thumb

    def _process_image(self, img, mode, disp_w, disp_h):
        if mode == 0: return self._process_full_view(img, disp_w, disp_h)
        elif mode == 1: return self._process_stretch(img, disp_w, disp_h)
        else: return self._process_fill(img, disp_w, disp_h)

    @staticmethod
    def _process_full_view(img, w, h):
        iw, ih = img.size
        if iw <= 0 or ih <= 0: return Image.new("RGBA", (w, h), BG_RGBA)
        ratio = min(w / iw, h / ih)
        nw, nh = int(iw * ratio), int(ih * ratio)
        if nw <= 0 or nh <= 0: return Image.new("RGBA", (w, h), BG_RGBA)
        img = img.resize((nw, nh), Image.Resampling.LANCZOS)
        if img.mode != "RGBA": img = img.convert("RGBA")
        res = Image.new("RGBA", (w, h), BG_RGBA)
        x, y = (w - nw) // 2, (h - nh) // 2
        res.paste(img, (x, y))
        return res

    @staticmethod
    def _process_stretch(img, w, h):
        if w <= 0 or h <= 0: return Image.new("RGBA", (1, 1), BG_RGBA)
        img = img.resize((w, h), Image.Resampling.LANCZOS)
        if img.mode != "RGBA": img = img.convert("RGBA")
        return img

    @staticmethod
    def _process_fill(img, w, h):
        iw, ih = img.size
        if iw <= 0 or ih <= 0: return Image.new("RGBA", (w, h), BG_RGBA)
        ratio = max(w / iw, h / ih)
        nw, nh = int(iw * ratio), int(ih * ratio)
        if nw <= 0 or nh <= 0: return Image.new("RGBA", (w, h), BG_RGBA)
        img = img.resize((nw, nh), Image.Resampling.LANCZOS)
        left = (nw - w) // 2; top = (nh - h) // 2
        img = img.crop((left, top, left + w, top + h))
        if img.mode != "RGBA": img = img.convert("RGBA")
        return img

    def _show_image_for_index(self, idx):
        if not self.images or idx < 0 or idx >= len(self.images): return
        path = self.images[idx]
        disp_w = max(100, self.image_label.winfo_width())
        disp_h = max(100, self.image_label.winfo_height())
        key = hashlib.md5(f"{path}_{self.image_mode}_{disp_w}_{disp_h}_{self.corner_radius}".encode()).hexdigest()
        def loader():
            orig = self._get_original_image(path)
            if orig is None: return None
            proc = self._process_image(orig, self.image_mode, disp_w, disp_h)
            if self.corner_radius > 0:
                proc = self._apply_rounded_corners_with_mask(proc, self.corner_radius)
            return proc
        processed = self._get_processed_image(key, loader)
        if processed is None: return
        photo = ImageTk.PhotoImage(processed)
        self.image_label.config(image=photo)
        self._photo_refs.append(photo)
        if len(self._photo_refs) > 20: self._photo_refs.pop(0)
        self.current_image_index = idx
        self._update_preview_for_manager()

    def _update_preview_for_manager(self):
        if self.manager and self.manager.home_window and self.manager.home_window.winfo_exists():
            try:
                thumb = self._get_thumbnail(self.images[self.current_image_index])
                if thumb:
                    thumb_photo = ImageTk.PhotoImage(thumb)
                    self.manager.home_window.update_widget_preview(self, thumb_photo)
            except: pass

    def request_preview_update(self):
        if self.images and self.current_image_index < len(self.images):
            self._update_preview_for_manager()

    def _show_first_image(self):
        if self.images:
            self.update_idletasks()
            self._show_image_for_index(self.current_image_index)
            if self.playing:
                self._stop_all_timers()
                self.after_id = self.after(self.interval, self._show_image)

    def _show_image(self):
        if not self.images or not self.playing: return
        target = self.index
        self.index = (self.index + 1) % len(self.images)
        def after_trans():
            if self.playing:
                self._stop_all_timers()
                self.after_id = self.after(self.interval, self._show_image)
        self._transition_to(target, callback=after_trans)

    # ═══════════════════ 预加载 & 文件夹监听 ═══════════════════

    def _start_preload_thread(self):
        if self._preload_thread and self._preload_thread.is_alive(): return
        self._preload_stop.clear()
        self._preload_thread = threading.Thread(target=self._preload_worker, daemon=True)
        self._preload_thread.start()

    def _preload_worker(self):
        while not self._preload_stop.is_set() and self.playing:
            if not self.images:
                time.sleep(0.5); continue
            idx = self.current_image_index
            preload = [(idx + d) % len(self.images) for d in (1, -1, 2, -2)]
            for p in preload:
                if self._preload_stop.is_set(): break
                self._get_original_image(self.images[p])
            self._preload_stop.wait(0.5)

    def _start_folder_watch(self):
        if self._folder_watch_timer:
            try: self.after_cancel(self._folder_watch_timer)
            except: pass
        if not self._folder_watch_enabled or not self.folder_path: return
        self._update_known_files()
        self._folder_watch_timer = self.after(self._folder_watch_interval, self._folder_watch_check)

    def _stop_folder_watch(self):
        if self._folder_watch_timer:
            try: self.after_cancel(self._folder_watch_timer)
            except: pass
            self._folder_watch_timer = None

    def _update_known_files(self):
        if not self.folder_path or not os.path.isdir(self.folder_path):
            self._known_files = set(); return
        try:
            self._known_files = set(os.listdir(self.folder_path))
            self._folder_mtime = os.path.getmtime(self.folder_path)
        except: self._known_files = set()

    def _folder_watch_check(self):
        if not self.folder_path or not os.path.isdir(self.folder_path):
            self._folder_watch_timer = self.after(self._folder_watch_interval, self._folder_watch_check)
            return
        try:
            cur_mtime = os.path.getmtime(self.folder_path)
            if cur_mtime == self._folder_mtime:
                self._folder_watch_timer = self.after(self._folder_watch_interval, self._folder_watch_check)
                return
            self._folder_mtime = cur_mtime
            cur_files = set(os.listdir(self.folder_path))
            cur_images = {f for f in cur_files if f.lower().endswith(VALID_EXT)}
            old_images = {f for f in self._known_files if f.lower().endswith(VALID_EXT)}
            if cur_images != old_images:
                self._on_folder_changed(cur_images)
            self._known_files = cur_files
        except Exception as e:
            print(f"[FloatWidget] 文件夹监听出错: {e}")
        self._folder_watch_timer = self.after(self._folder_watch_interval, self._folder_watch_check)

    def _on_folder_changed(self, new_image_set):
        cur_path = None
        if self.images and self.current_image_index < len(self.images):
            cur_path = self.images[self.current_image_index]
        old_count = len(self.images)
        self.images = [os.path.join(self.folder_path, f)
                       for f in os.listdir(self.folder_path) if f.lower().endswith(VALID_EXT)]
        new_count = len(self.images)
        cur_removed = cur_path and cur_path not in self.images
        if new_count > old_count:
            random.shuffle(self.images)
            self._show_temp_message(f"+{new_count - old_count} 张新图片")
        elif new_count < old_count:
            if cur_removed: self._show_temp_message("当前图片已移除")
            else: self._show_temp_message(f"{old_count - new_count} 张图片已移除")
        if cur_path and cur_path in self.images:
            self.index = self.images.index(cur_path)
            self.current_image_index = self.index
        elif self.images:
            self.index = 0; self.current_image_index = 0
        else:
            self._show_start_tip(); return
        with self._lock:
            valid = set(self.images)
            for key in list(self._original_cache.keys()):
                if key not in valid: del self._original_cache[key]
        if not self.images: self._show_start_tip()
        elif self.playing: self._show_image_for_index(self.current_image_index)


# ═══════════════════ 程序入口 ═══════════════════

def main():
    root = tk.Tk()
    root.withdraw()
    manager = WidgetManager(root)
    manager.create_tray_icon()
    manager.load_existing_widgets()
    if not manager.widgets:
        manager.create_new_widget()
    root.mainloop()


if __name__ == "__main__":
    main()