import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk
import numpy as np
import math
from functools import partial
import random
import threading
import cProfile
import pstats
import io
from concurrent.futures import ThreadPoolExecutor
import time
from collections import deque
import os
import gc
import tracemalloc
import datetime

class TextGridEditor:

    def __init__(self, root, cell_width=20, cell_height=20):
        self.root = root
        self.base_cell_width = cell_width
        self.base_cell_height = cell_height
        self.cell_width = cell_width
        self.cell_height = cell_height
        self.zoom_factor = 1.0
        self.zoom_percentage = tk.IntVar(value=100)

        self.paintbrush_size = 1  # Default paintbrush size

        self._currently_painting = False
        self.canvas_operation_count = 0
        self.cleanup_threshold = 2000
        self._selection_update_id = None
        self._cleanup_after_painting_id = None
        self._debug_update_pending = False

        self.colors = {
            '#': 'dim gray',       # Wall (was 'gray25', now valid)
            '.': 'white',          # Floor
            '@': 'yellow',         # Player
            '*': 'red',            # Item
            '^': 'magenta',        # Item
            'w': 'light blue',     # Shallow Water
            'W': 'blue',           # Deep Water
            'h': 'brown',          # Hill
            'H': 'saddle brown',   # Mountain
            's': 'light yellow',   # Sand
            'f': 'green',          # Sparse Trees
            'F': 'dark green',     # Dense Trees
            'x': 'dark red',       # Special Feature

            # **âœ… Sand Biome Colors**
            ',': 'goldenrod',          # Light sand
            '`': 'goldenrod',          # Wind-blown light sand
            'z': 'goldenrod',      # Small dunes
            'd': 'dark goldenrod',           # Taller dunes
            'D': 'dark goldenrod', # Sand plateaus
        }



        self.char_to_color = {}
        self.setup_default_char_colors()

        self.grid = None
        self.rows = 0
        self.cols = 0
        self.rect_start = None
        self.rect_end = None
        self.selected_cells = set()
        self.region_selected = False
        self.alt_pressed = False
        self.selection_mode = 'rectangle'
        self.is_selecting = False

        self.show_all_chars = tk.BooleanVar(value=False)

        self.canvas_objects = {}
        self.redraw_after_id = None
        self.resize_after_id = None
        self.scroll_refresh_after_id = None

        self.forest_shape = "ellipse"  # Default shape
        self.explosion_percentages = [10, 20, 30, 30, 10]  # ['.', '.', 'f', 'F', '.']
        self.implosion_percentages = [30, 30, 30, 10]  # ['F', 'f', '.', '.']
        self.randomness = tk.IntVar(value=0)  # Changed from DoubleVar to IntVar
        self.extra_spaces = tk.IntVar(value=0)

        self.setup_menu()
        self.setup_ui()
        self.setup_bindings()

        self.undo_stack = []
        self.max_undo = 50

        self.select_spaces_only = False
        self.smart_select_pending = None

        self.previous_visible_range = set()  # Track previous visible rows
        self.init_memory_debugger()

        print("TextGridEditor initialized")

    def init_memory_debugger(self):
        """Low-overhead periodic memory diagnostics for leak hunting."""
        self.mem_debug_enabled = False
        self.mem_debug_interval_ms = 20000
        self.mem_debug_after_id = None
        self.mem_debug_tick_count = 0
        self.mem_debug_start_time = time.time()
        self.mem_debug_prev_snapshot = None
        self.mem_debug_heavy = False
        self.mem_debug_echo_stdout = False
        self.mem_debug_log_path = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "map_editor5_memdebug.log"
        )
        self._psutil_process = None

        try:
            import psutil  # Optional, better RSS reporting if installed
            self._psutil_process = psutil.Process(os.getpid())
        except Exception:
            self._psutil_process = None

        if tracemalloc.is_tracing():
            tracemalloc.stop()

        self._write_memory_log("=== Memory debug initialized (disabled by default) ===")

    def set_memory_debug_enabled(self, enabled, heavy=False):
        self.mem_debug_enabled = bool(enabled)
        self.mem_debug_heavy = bool(heavy)
        if self.mem_debug_enabled:
            if self.mem_debug_heavy and (not tracemalloc.is_tracing()):
                tracemalloc.start(25)
            self._write_memory_log("Memory debug ENABLED")
            self.schedule_memory_debug_tick()
            self.debug_label.config(text="Memory debug enabled")
        else:
            if self.mem_debug_after_id is not None:
                try:
                    self.root.after_cancel(self.mem_debug_after_id)
                except Exception:
                    pass
                self.mem_debug_after_id = None
            if tracemalloc.is_tracing():
                tracemalloc.stop()
            self._write_memory_log("Memory debug DISABLED")
            self.debug_label.config(text="Memory debug disabled")

    def schedule_memory_debug_tick(self):
        if not self.mem_debug_enabled:
            return
        if self.mem_debug_after_id is not None:
            return
        self.mem_debug_after_id = self.root.after(self.mem_debug_interval_ms, self._memory_debug_tick)

    def _write_memory_log(self, line):
        timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        text = f"[{timestamp}] {line}"
        if self.mem_debug_echo_stdout:
            print(text)
        try:
            with open(self.mem_debug_log_path, "a", encoding="utf-8") as fh:
                fh.write(text + "\n")
        except OSError:
            pass

    def _get_process_rss_mb(self):
        if self._psutil_process is not None:
            try:
                return self._psutil_process.memory_info().rss / (1024.0 * 1024.0)
            except Exception:
                pass

        # Windows stdlib fallback (no psutil dependency).
        try:
            import ctypes
            from ctypes import wintypes

            class PROCESS_MEMORY_COUNTERS(ctypes.Structure):
                _fields_ = [
                    ("cb", wintypes.DWORD),
                    ("PageFaultCount", wintypes.DWORD),
                    ("PeakWorkingSetSize", ctypes.c_size_t),
                    ("WorkingSetSize", ctypes.c_size_t),
                    ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                    ("PagefileUsage", ctypes.c_size_t),
                    ("PeakPagefileUsage", ctypes.c_size_t),
                ]

            GetCurrentProcess = ctypes.windll.kernel32.GetCurrentProcess
            GetProcessMemoryInfo = ctypes.windll.psapi.GetProcessMemoryInfo
            counters = PROCESS_MEMORY_COUNTERS()
            counters.cb = ctypes.sizeof(PROCESS_MEMORY_COUNTERS)
            ok = GetProcessMemoryInfo(GetCurrentProcess(), ctypes.byref(counters), counters.cb)
            if ok:
                return counters.WorkingSetSize / (1024.0 * 1024.0)
        except Exception:
            pass

        return -1.0

    def _estimate_undo_cells(self):
        if not hasattr(self, "undo_stack") or not self.undo_stack:
            return 0
        total = 0
        for action in self.undo_stack:
            try:
                total += len(action)
            except Exception:
                pass
        return total

    def dump_memory_snapshot(self):
        """Force an immediate diagnostic sample."""
        self._memory_debug_tick(force=True)

    def _memory_debug_tick(self, force=False):
        self.mem_debug_after_id = None
        if not self.mem_debug_enabled and not force:
            return

        self.mem_debug_tick_count += 1
        elapsed = time.time() - self.mem_debug_start_time

        rss_mb = self._get_process_rss_mb()
        traced_cur_mb = -1.0
        traced_peak_mb = -1.0
        if tracemalloc.is_tracing():
            traced_cur, traced_peak = tracemalloc.get_traced_memory()
            traced_cur_mb = traced_cur / (1024.0 * 1024.0)
            traced_peak_mb = traced_peak / (1024.0 * 1024.0)

        canvas_item_count = -1
        try:
            canvas_item_count = len(self.canvas.find_all())
        except Exception:
            pass

        line = (
            f"uptime={elapsed:.1f}s rss_mb={rss_mb:.2f} traced_mb={traced_cur_mb:.2f}/{traced_peak_mb:.2f} "
            f"canvas_items={canvas_item_count} canvas_cells={len(self.canvas_objects)} "
            f"selected={len(self.selected_cells)} prev_visible={len(self.previous_visible_range)} "
            f"undo_actions={len(self.undo_stack)} undo_cells={self._estimate_undo_cells()} "
            f"gc_counts={gc.get_count()}"
        )
        self._write_memory_log(line)

        # Heavy mode only: capture growth stats from tracemalloc snapshots.
        if self.mem_debug_heavy and tracemalloc.is_tracing() and (self.mem_debug_tick_count % 6 == 0 or force):
            try:
                snapshot = tracemalloc.take_snapshot()
                if self.mem_debug_prev_snapshot is not None:
                    growth = snapshot.compare_to(self.mem_debug_prev_snapshot, "lineno")
                    top_growth = []
                    for stat in growth[:5]:
                        size_kib = stat.size_diff / 1024.0
                        count_diff = stat.count_diff
                        if size_kib <= 0 and count_diff <= 0:
                            continue
                        top_growth.append(
                            f"{stat.traceback.format()[-1].strip()} +{size_kib:.1f}KiB ({count_diff:+d})"
                        )
                    if top_growth:
                        self._write_memory_log("top_growth: " + " | ".join(top_growth))
                self.mem_debug_prev_snapshot = snapshot
            except Exception as e:
                self._write_memory_log(f"snapshot_error: {e}")

        if self.mem_debug_enabled:
            self.schedule_memory_debug_tick()


    def setup_menu(self):
        menu = tk.Menu(self.root)
        self.root.config(menu=menu)

        file_menu = tk.Menu(menu, tearoff=0)
        menu.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Open", command=self.open_file)
        file_menu.add_command(label="Default Map", command=self.create_default_map_dialog)
        file_menu.add_command(label="Save", command=self.save_to_file)

        view_menu = tk.Menu(menu, tearoff=0)
        menu.add_cascade(label="View", menu=view_menu)
        view_menu.add_checkbutton(label="Show All Characters", variable=self.show_all_chars, command=self.redraw_visible_cells)

        # Shortcuts menu
        shortcuts_menu = tk.Menu(menu, tearoff=0)
        menu.add_cascade(label="Shortcuts", menu=shortcuts_menu)
        shortcuts_menu.add_command(label="Toggle Selection Mode (Alt + a)", command=self.toggle_selection_mode)
        shortcuts_menu.add_command(label="Clear Selection (Escape)", command=self.clear_selection)
        shortcuts_menu.add_command(label="Undo (Ctrl + z)", command=self.undo)
        shortcuts_menu.add_command(label="Toggle Space Selection (Tab)", command=self.toggle_space_selection)     
        
        # Brush size menu
        brush_menu = tk.Menu(menu, tearoff=0)
        menu.add_cascade(label="Brush Size", menu=brush_menu)
        for size in [1, 2, 4, 8, 10]:
            brush_menu.add_command(label=f"{size}x{size}", command=partial(self.set_paintbrush_size, size))

        diagnostics_menu = tk.Menu(menu, tearoff=0)
        menu.add_cascade(label="Diagnostics", menu=diagnostics_menu)
        diagnostics_menu.add_command(label="Dump Memory Snapshot", command=self.dump_memory_snapshot)
        diagnostics_menu.add_command(
            label="Enable Memory Debug (Light)",
            command=lambda: self.set_memory_debug_enabled(True, heavy=False)
        )
        diagnostics_menu.add_command(
            label="Enable Memory Debug (Heavy)",
            command=lambda: self.set_memory_debug_enabled(True, heavy=True)
        )
        diagnostics_menu.add_command(label="Disable Memory Debug", command=lambda: self.set_memory_debug_enabled(False))
        diagnostics_menu.add_command(
            label="Show Memory Log Path",
            command=lambda: messagebox.showinfo("Memory Log", self.mem_debug_log_path)
        )

    def set_paintbrush_size(self, size):
        """Set the size of the paintbrush."""
        self.paintbrush_size = size
        self.debug_label.config(text=f"Paintbrush size set to {size}x{size}")


    def setup_ui(self):
        self.setup_zoom_slider()
        self.setup_randomness_slider()

        self.canvas_frame = tk.Frame(self.root)
        self.canvas_frame.pack(fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(self.canvas_frame, bg="black")
        self.canvas.grid(row=0, column=0, sticky="nsew")

        self.v_scroll = tk.Scrollbar(self.canvas_frame, orient=tk.VERTICAL, command=self.on_vertical_scroll)
        self.v_scroll.grid(row=0, column=1, sticky="ns")

        self.h_scroll = tk.Scrollbar(self.canvas_frame, orient=tk.HORIZONTAL, command=self.on_horizontal_scroll)
        self.h_scroll.grid(row=1, column=0, sticky="ew")

        self.canvas.config(yscrollcommand=self.v_scroll.set, xscrollcommand=self.h_scroll.set)

        self.canvas_frame.grid_rowconfigure(0, weight=1)
        self.canvas_frame.grid_columnconfigure(0, weight=1)

        self.debug_label = tk.Label(self.root, text="Debug Info", anchor="w", justify="left")
        self.debug_label.pack(side=tk.BOTTOM, fill=tk.X)

        # Bottom control bar
        bottom_frame = ttk.Frame(self.root)
        bottom_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=5)

        # Add biome generation buttons
        biome_options = [
            ("Forest", "forest"),
            ("Grasslands", "grasslands"),
            ("Swamp", "swamp"),
            ("Sand", "sand"),
            ("Dry Sand", "dry_sand"),
        ]

        for label, biome_type in biome_options:
            menu_btn = ttk.Menubutton(bottom_frame, text=label, direction="below")
            menu_btn.pack(side=tk.LEFT, padx=5)

            menu = tk.Menu(menu_btn, tearoff=0)

            for shape in BIOME_PROFILES[biome_type]["shapes"]:
                menu.add_command(label=f"{shape.replace('_', ' ').title()}", 
                                command=lambda b=biome_type, s=shape: self.generate_biome(b, s))
            menu.add_command(label="Thin Out", command=lambda: self.thin_out_forest("thin"))
            menu.add_command(label="Heavy Thin Out", command=lambda: self.thin_out_forest("heavy"))
            
            menu_btn["menu"] = menu  # Attach the menu to the button

        smart_select_btn = ttk.Menubutton(bottom_frame, text="Smart Select", direction="below")
        smart_select_btn.pack(side=tk.LEFT, padx=5)
        smart_select_menu = tk.Menu(smart_select_btn, tearoff=0)
        smart_select_menu.add_command(
            label="Region Flood: Balanced (run >= 5, adjacency 2)",
            command=lambda: self.arm_smart_select(
                mode="region_flood",
                min_run=5,
                adjacency_threshold=2,
                min_region_size=18,
                replace_selection=False
            )
        )
        smart_select_menu.add_command(
            label="Region Flood: Strict (run >= 8, adjacency 3)",
            command=lambda: self.arm_smart_select(
                mode="region_flood",
                min_run=8,
                adjacency_threshold=3,
                min_region_size=28,
                replace_selection=False
            )
        )
        smart_select_menu.add_command(label="Region Flood: Custom...", command=self.arm_smart_select_custom)
        smart_select_menu.add_separator()
        smart_select_menu.add_command(
            label="Path Corona: Blank (radius 1)",
            command=lambda: self.arm_smart_select(
                mode="path_corona",
                corona_radius=1,
                replace_selection=False
            )
        )
        smart_select_menu.add_command(
            label="Path Corona: Blank (radius 3)",
            command=lambda: self.arm_smart_select(
                mode="path_corona",
                corona_radius=3,
                replace_selection=False
            )
        )
        smart_select_menu.add_command(
            label="Path Corona: Blank + Adjacent Filled (radius 1)",
            command=lambda: self.arm_smart_select(
                mode="path_corona",
                corona_radius=1,
                include_adjacent_filled=True,
                replace_selection=False
            )
        )
        smart_select_menu.add_command(label="Path Corona: Custom...", command=self.arm_smart_select_path_custom)
        smart_select_menu.add_separator()
        smart_select_menu.add_command(
            label="Similar Type Radius: 3",
            command=lambda: self.arm_smart_select(
                mode="type_radius",
                type_radius=3,
                replace_selection=False
            )
        )
        smart_select_menu.add_command(
            label="Similar Type Radius: 6",
            command=lambda: self.arm_smart_select(
                mode="type_radius",
                type_radius=6,
                replace_selection=False
            )
        )
        smart_select_menu.add_command(
            label="Similar Type Radius: Custom...",
            command=self.arm_smart_select_type_radius_custom
        )
        smart_select_btn["menu"] = smart_select_menu

    def setup_zoom_slider(self):
        zoom_frame = ttk.Frame(self.root)
        zoom_frame.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)

        ttk.Label(zoom_frame, text="Zoom:").pack(side=tk.LEFT)
        self.zoom_slider = ttk.Scale(zoom_frame, from_=10, to=190, orient=tk.HORIZONTAL, 
                                     command=self.on_zoom, variable=self.zoom_percentage,
                                     length=150)
        self.zoom_slider.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        
        zoom_label = ttk.Label(zoom_frame, textvariable=self.zoom_percentage)
        zoom_label.pack(side=tk.LEFT)
        ttk.Label(zoom_frame, text="%").pack(side=tk.LEFT)

    def setup_randomness_slider(self):
        controls_row = ttk.Frame(self.root)
        controls_row.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)

        randomness_frame = ttk.Frame(controls_row)
        randomness_frame.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 8))
        ttk.Label(randomness_frame, text="Randomness:").pack(side=tk.LEFT)
        self.randomness_slider = ttk.Scale(
            randomness_frame,
            from_=0,
            to=50,
            orient=tk.HORIZONTAL,
            command=self.on_randomness_change,
            variable=self.randomness,
            length=130
        )
        self.randomness_slider.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        randomness_label = ttk.Label(randomness_frame, textvariable=self.randomness, width=3)
        randomness_label.pack(side=tk.LEFT)
        ttk.Label(randomness_frame, text="%").pack(side=tk.LEFT)

        spaces_frame = ttk.Frame(controls_row)
        spaces_frame.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(8, 0))
        ttk.Label(spaces_frame, text="Extra Spaces:").pack(side=tk.LEFT)
        self.extra_spaces_slider = ttk.Scale(
            spaces_frame,
            from_=0,
            to=100,
            orient=tk.HORIZONTAL,
            command=self.on_extra_spaces_change,
            variable=self.extra_spaces,
            length=130
        )
        self.extra_spaces_slider.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        spaces_label = ttk.Label(spaces_frame, textvariable=self.extra_spaces, width=3)
        spaces_label.pack(side=tk.LEFT)
        ttk.Label(spaces_frame, text="%").pack(side=tk.LEFT)

    def on_mouse_motion(self, event):
        """Fixed hover preview with canvas boundary checking."""
        # **âœ… GET CANVAS BOUNDARIES**
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        
        # **âœ… CHECK IF MOUSE IS OUTSIDE CANVAS AREA**
        if (event.x < 0 or event.x >= canvas_width or 
            event.y < 0 or event.y >= canvas_height):
            # **âœ… CLEAR HOVER PREVIEW WHEN OUTSIDE CANVAS**
            self.canvas.delete('hover_preview')
            return  # Don't show hover outside canvas

        col = int(self.canvas.canvasx(event.x) // self.cell_width)
        row = int(self.canvas.canvasy(event.y) // self.cell_height)

        # **âœ… ADDITIONAL GRID BOUNDARY CHECK**
        if (row < 0 or row >= self.rows or col < 0 or col >= self.cols):
            self.canvas.delete('hover_preview')
            return  # Don't show hover outside grid

        # Always update hover preview immediately for cursor tracking
        current_hover = (row, col)
        if hasattr(self, '_last_hover') and self._last_hover == current_hover:
            return
        
        self._last_hover = current_hover
        
        # **âœ… ALWAYS DELETE PREVIOUS HOVER PREVIEW FIRST**
        self.canvas.delete('hover_preview')
        
        # **âœ… CHECK SPACE-ONLY MODE**
        if not hasattr(self, 'select_spaces_only'):
            self.select_spaces_only = False

        # **âœ… ONLY CREATE HOVER PREVIEW FOR VALID CELLS**
        for d_row in range(self.paintbrush_size):
            for d_col in range(self.paintbrush_size):
                # **âœ… CORRECT COORDINATE CALCULATION**
                target_row = row + d_row
                target_col = col + d_col
                
                # **âœ… STRICT BOUNDARY CHECK FOR HOVER PREVIEW**
                if not (0 <= target_row < self.rows and 0 <= target_col < self.cols):
                    continue  # Skip cells outside grid
                    
                # **âœ… SPACE-ONLY MODE CHECK FOR HOVER**
                if self.select_spaces_only:
                    current_char = chr(self.grid[target_row, target_col])
                    if not current_char.isspace() and current_char != ' ':
                        continue  # Skip non-space characters in hover too
                
                # **âœ… CORRECT VISUAL COORDINATE CALCULATION**
                x1 = target_col * self.cell_width
                y1 = target_row * self.cell_height
                x2 = x1 + self.cell_width
                y2 = y1 + self.cell_height
                
                # **âœ… VALIDATE PIXEL COORDINATES ARE WITHIN CANVAS**
                if (x1 >= 0 and y1 >= 0 and x2 > x1 and y2 > y1 and
                    x1 < self.cols * self.cell_width and y1 < self.rows * self.cell_height):
                    # **âœ… DIFFERENT HOVER COLOR FOR SPACE-ONLY MODE**
                    hover_color = 'yellow' if self.select_spaces_only else 'light cyan'
                    self.canvas.create_rectangle(x1, y1, x2, y2, outline=hover_color, 
                                            tags='hover_preview', width=1)

    def setup_bindings(self):
        self.canvas.bind("<Button-1>", self.on_click)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<Motion>", self.on_mouse_motion)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        self.canvas.bind("<MouseWheel>", self.on_mousewheel)
        self.root.bind("<Key>", self.on_keypress)
        self.root.bind("<Alt-a>", self.toggle_selection_mode)  # Use Alt + A to toggle selection mode
        self.root.bind("<Escape>", self.clear_selection)  # Escape clears selection
        self.root.bind("<Control-z>", self.undo)
        self.canvas.bind("<Configure>", self.on_canvas_configure)
        self.root.bind("<Tab>", self.toggle_space_selection)
        self.root.bind("<Control-Shift-D>", lambda e: self.debug_canvas_state())
        self.root.bind("<Control-Shift-S>", lambda e: self.debug_space_selection())
        self.root.bind("<Control-Shift-G>", lambda e: self.debug_grid_integrity())
        
    def toggle_selection_mode(self, event=None):
        """Toggles between freeform and rectangular selection mode when Alt + A is pressed."""
        if self.selection_mode == 'rectangle':
            self.selection_mode = 'freeform'
            self.debug_label.config(text="Freeform selection mode ON (Alt + A toggled)")
        else:
            self.selection_mode = 'rectangle'
            self.debug_label.config(text="Rectangle selection mode ON (Alt + A toggled)")

    def clear_selection(self, event=None):
        """Simple clear selection with performance mode handling."""
        selection_size = len(self.selected_cells)
        print(f"ðŸ”„ CLEARING SELECTION: {selection_size} cells...")
        
        # **âœ… EXIT PERFORMANCE MODE IF ACTIVE**
        if hasattr(self, '_performance_mode') and self._performance_mode:
            self.exit_performance_mode()
        
        # Clear the selection set
        self.selected_cells.clear()
        
        # **âœ… SIMPLE: Just delete all selection objects**
        self.canvas.delete('selection')
        self.canvas.delete('hover_preview')
        
        # Reset selection state
        self.rect_start = None
        self.rect_end = None
        self.region_selected = False
        self.is_selecting = False
        
        # Force canvas update
        self.canvas.update_idletasks()
        
        self.debug_label.config(text=f"Selection cleared ({selection_size} cells)")
        print(f"âœ… SELECTION CLEARED: {selection_size} cells")

    def on_vertical_scroll(self, *args):
        """Enhanced vertical scroll that maintains selection sync."""
        self.canvas.yview(*args)
        self._schedule_scroll_refresh()

    def on_horizontal_scroll(self, *args):
        """Enhanced horizontal scroll that maintains selection sync."""
        self.canvas.xview(*args)
        self._schedule_scroll_refresh()

    def _schedule_scroll_refresh(self):
        """Throttle scroll-triggered redraw/selection sync to keep highlights accurate."""
        if self.scroll_refresh_after_id is not None:
            try:
                self.root.after_cancel(self.scroll_refresh_after_id)
            except Exception:
                pass
            self.scroll_refresh_after_id = None

        self.root.after_idle(self._redraw_visible_cells)
        self.scroll_refresh_after_id = self.root.after(16, self._run_scroll_refresh)

    def _run_scroll_refresh(self):
        self.scroll_refresh_after_id = None
        self._sync_selection_after_scroll()

    def _sync_selection_after_scroll(self):
        """SAFE selection sync that only affects visuals, never grid data."""
        try:
            if not self.selected_cells:
                self.canvas.delete('selection')
                return

            print("ðŸ”„ SYNCING SELECTION AFTER SCROLL...")
            
            # **âœ… ONLY CLEAR SELECTION VISUALS, NOT GRID DATA**
            self.canvas.delete('selection')
            # **ðŸš¨ NEVER TOUCH GRID DATA OR CANVAS_OBJECTS HERE**
            
            # Use latest visible range from redraw when available.
            if self.previous_visible_range:
                visible_area = self.previous_visible_range
                visible_start_row = min(r for r, _ in visible_area)
                visible_end_row = max(r for r, _ in visible_area) + 1
                visible_start_col = min(c for _, c in visible_area)
                visible_end_col = max(c for _, c in visible_area) + 1
            else:
                canvas_width = self.canvas.winfo_width()
                canvas_height = self.canvas.winfo_height()
                x1, y1 = self.canvas.canvasx(0), self.canvas.canvasy(0)
                x2, y2 = x1 + canvas_width, y1 + canvas_height
                visible_start_row = max(0, int(y1 // self.cell_height))
                visible_end_row = min(self.rows, int(y2 // self.cell_height) + 1)
                visible_start_col = max(0, int(x1 // self.cell_width))
                visible_end_col = min(self.cols, int(x2 // self.cell_width) + 1)
                visible_area = {
                    (r, c)
                    for r in range(visible_start_row, visible_end_row)
                    for c in range(visible_start_col, visible_end_col)
                }

            # **âœ… FIND SELECTED CELLS IN VISIBLE AREA**
            visible_selected = self.selected_cells & visible_area
            
            print(f"  ðŸ“Š VISIBLE AREA: rows {visible_start_row}-{visible_end_row}, cols {visible_start_col}-{visible_end_col}")
            print(f"  ðŸ“Š SELECTED CELLS: {len(self.selected_cells)} total, {len(visible_selected)} visible")

            # **âœ… ONLY RECREATE SELECTION VISUAL RECTANGLES**
            if visible_selected:
                outline_color = 'orange' if (hasattr(self, 'select_spaces_only') and self.select_spaces_only) else 'cyan'
                
                for row, col in visible_selected:
                    if 0 <= row < self.rows and 0 <= col < self.cols:
                        x1 = col * self.cell_width
                        y1 = row * self.cell_height
                        x2 = x1 + self.cell_width
                        y2 = y1 + self.cell_height
                        self.canvas.create_rectangle(x1, y1, x2, y2, outline=outline_color, 
                                                tags='selection', width=2)

            print(f"âœ… SELECTION SYNC COMPLETE: {len(visible_selected)} selection rectangles recreated")
            
        except Exception as e:
            print(f"âŒ Selection sync error: {e}")

    def setup_default_char_colors(self):
        """Directly apply color mappings."""
        self.char_to_color = self.colors  # No need to copy; just reference it directly

    def set_forest_shape(self, shape):
        self.forest_shape = shape.lower()
        print(f"Forest shape set to: {self.forest_shape}")

    def set_char_color(self, char, color_key):
        if color_key in self.colors:
            self.char_to_color[char] = self.colors[color_key]
        else:
            raise ValueError(f"Invalid color key: {color_key}")

    def get_char_color(self, char):
        if char in self.char_to_color:
            return self.char_to_color[char]
        elif char.isspace():
            return 'black'
        else:
            return 'gray50'

    def open_file(self):
        filepath = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if filepath:
            self.load_text_file(filepath)

    def create_default_map_dialog(self):
        """Prompt for X/Y size and create a new blank map."""
        default_x = self.cols if self.cols > 0 else 120
        default_y = self.rows if self.rows > 0 else 60

        x_size = simpledialog.askinteger(
            "Default Map",
            "X size (columns):",
            initialvalue=default_x,
            minvalue=1,
            maxvalue=10000
        )
        if x_size is None:
            return

        y_size = simpledialog.askinteger(
            "Default Map",
            "Y size (rows):",
            initialvalue=default_y,
            minvalue=1,
            maxvalue=10000
        )
        if y_size is None:
            return

        self.create_default_map(x_size, y_size)

    def create_default_map(self, x_size, y_size):
        """Create a blank map and refresh the canvas."""
        self.cols = int(x_size)
        self.rows = int(y_size)
        self.grid = np.full((self.rows, self.cols), ord(' '), dtype=np.uint32)
        self.undo_stack.clear()

        self._reset_after_new_grid()
        self.debug_label.config(text=f"Default blank map created: {self.cols}x{self.rows} (XxY)")
        print(f"Default blank map created: cols={self.cols}, rows={self.rows}")

    def _reset_after_new_grid(self):
        """Reset canvas/selection state after loading or creating a grid."""
        self.canvas.delete("all")
        self.canvas_objects.clear()
        self.selected_cells.clear()
        self.previous_visible_range = set()
        self.rect_start = None
        self.rect_end = None
        self.region_selected = False
        self.is_selecting = False
        self.smart_select_pending = None

        if hasattr(self, 'canvas_operation_count'):
            self.canvas_operation_count = 0

        self.update_scrollregion()
        self.canvas.update_idletasks()
        self._redraw_visible_cells_force_complete()
        self.canvas.xview_moveto(0)
        self.canvas.yview_moveto(0)
        self.root.after(100, self._redraw_visible_cells_force_complete)

    def load_text_file(self, filepath):
        try:
            with open(filepath, 'r', encoding='utf-8') as file:
                # Keep trailing spaces, but strip line endings consistently across LF/CRLF files.
                lines = [line.rstrip('\r\n') for line in file]

            if not lines:
                raise ValueError("File is empty.")

            self.rows = len(lines)
            self.cols = max(len(line) for line in lines)

            self.grid = np.full((self.rows, self.cols), ord(' '), dtype=np.uint32)

            for row, line in enumerate(lines):
                for col, char in enumerate(line):
                    self.grid[row, col] = ord(char)

            print(f"File loaded. Rows: {self.rows}, Cols: {self.cols}")
            self.debug_label.config(text=f"File loaded. Rows: {self.rows}, Cols: {self.cols}")

            # **âœ… COMPLETE RESET AND REDRAW**
            self.canvas.delete("all")  # Clear everything
            self.canvas_objects.clear()  # Clear tracking
            self.selected_cells.clear()  # Clear selection
            self.previous_visible_range = set()  # Reset visible tracking
            
            # Reset cleanup counters
            if hasattr(self, 'canvas_operation_count'):
                self.canvas_operation_count = 0
            
            # **âœ… FORCE IMMEDIATE COMPLETE REDRAW**
            self.update_scrollregion()
            self.canvas.update_idletasks()  # Process pending operations
            
            # **âœ… FORCE FULL VISIBLE AREA REDRAW**
            self._redraw_visible_cells_force_complete()
            
            # Set scrollbars to top-left
            self.canvas.xview_moveto(0)
            self.canvas.yview_moveto(0)
            
            # **âœ… SECOND REDRAW AFTER SCROLL TO ENSURE VISIBILITY**
            self.root.after(100, self._redraw_visible_cells_force_complete)

        except Exception as e:
            messagebox.showerror("Error", f"Could not load file: {e}")
            self.debug_label.config(text=f"Error loading file: {e}")
            print(f"Error loading file: {e}")

    def _redraw_visible_cells_force_complete(self):
        """Force complete redraw of all visible cells - no optimizations."""
        try:
            # Get visible area
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            x1, y1 = self.canvas.canvasx(0), self.canvas.canvasy(0)
            x2, y2 = x1 + canvas_width, y1 + canvas_height

            start_col = max(0, int(x1 // self.cell_width))
            start_row = max(0, int(y1 // self.cell_height))
            end_col = min(self.cols, int(x2 // self.cell_width) + 2)  # +2 for safety margin
            end_row = min(self.rows, int(y2 // self.cell_height) + 2)

            print(f"ðŸ”„ FORCE REDRAW: rows {start_row}-{end_row}, cols {start_col}-{end_col}")

            # Force redraw every visible cell
            for row in range(start_row, end_row):
                for col in range(start_col, end_col):
                    if 0 <= row < self.rows and 0 <= col < self.cols:
                        char = chr(self.grid[row, col])
                        color = self.get_char_color(char)
                        self.update_canvas_object(row, col, char, color)

            # Update tracking
            self.previous_visible_range = set((r, c) for r in range(start_row, end_row) for c in range(start_col, end_col))
            
            # Ensure text is on top
            self.canvas.tag_raise('text')
            
            print(f"âœ… FORCE REDRAW COMPLETE: {len(self.previous_visible_range)} cells drawn")
            
        except Exception as e:
            print(f"âŒ Force redraw error: {e}")

    def save_to_file(self):
        filepath = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt")])
        if filepath:
            try:
                with open(filepath, 'w', encoding='utf-8') as file:
                    for row in range(self.rows):
                        file.write(''.join(chr(self.grid[row, col]) for col in range(self.cols)) + '\n')
                messagebox.showinfo("Success", "File saved successfully!")
                self.debug_label.config(text=f"File saved: {filepath}")
            except Exception as e:
                messagebox.showerror("Error", f"Could not save file: {e}")
                self.debug_label.config(text=f"Error saving file: {e}")

    def reset_canvas(self):
        self.canvas.delete("all")
        self.canvas_objects.clear()
        self.update_scrollregion()
        print("Canvas reset.")

    def center_viewport(self):
        self.canvas.xview_moveto(0.5)
        self.canvas.yview_moveto(0.5)

    def update_scrollregion(self):
        canvas_width = max(self.cols * self.cell_width, self.canvas.winfo_width())
        canvas_height = max(self.rows * self.cell_height, self.canvas.winfo_height())
        
        old_scrollregion = self.canvas.cget('scrollregion')
        new_scrollregion = (0, 0, canvas_width, canvas_height)
        
        self.canvas.config(scrollregion=new_scrollregion)
        
        print(f"ðŸ“ SCROLL REGION: {old_scrollregion} â†’ {new_scrollregion}")
        print(f"ðŸ“ GRID SIZE: {self.rows}x{self.cols} cells = {canvas_height}x{canvas_width} pixels")

    def redraw_all_cells(self):
        print("Redrawing all visible cells")
        self.canvas.delete("all")
        self._redraw_visible_cells()

    def redraw_visible_cells(self):
        """Throttle redraw to limit excessive UI updates."""
        if self.redraw_after_id:
            self.root.after_cancel(self.redraw_after_id)
        # Batch defer redraw to happen 100 milliseconds later
        self.redraw_after_id = self.root.after(100, self._redraw_visible_cells)

    def _redraw_visible_cells(self):
        """Simple fast visible cell redraw."""
        self.redraw_after_id = None

        try:
            # Get visible area
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            x1, y1 = self.canvas.canvasx(0), self.canvas.canvasy(0)
            x2, y2 = x1 + canvas_width, y1 + canvas_height

            start_col = max(0, int(x1 // self.cell_width))
            start_row = max(0, int(y1 // self.cell_height))
            end_col = min(self.cols, int(x2 // self.cell_width) + 1)
            end_row = min(self.rows, int(y2 // self.cell_height) + 1)

            visible_set = set((r, c) for r in range(start_row, end_row) for c in range(start_col, end_col))
            delta_set = visible_set - self.previous_visible_range

            # **âœ… SIMPLE: Just update new visible cells directly**
            for row, col in delta_set:
                if 0 <= row < self.rows and 0 <= col < self.cols:
                    char = chr(self.grid[row, col])
                    color = self.get_char_color(char)
                    self.simple_update_canvas_object(row, col, char, color)

            self.previous_visible_range = visible_set
            self.canvas.tag_raise('text')
            
        except Exception as e:
            print(f"âŒ Redraw error: {e}")

    def progressive_redraw_visible(self, delta_set, visible_set):
        """Progressive redraw for large visible areas."""
        # **âœ… CONVERT TO LIST FOR BATCHING**
        delta_list = list(delta_set)
        batch_size = 50
        
        # **âœ… SCHEDULE BATCHED RENDERING**
        for i in range(0, len(delta_list), batch_size):
            batch = delta_list[i:i + batch_size]
            delay = i // batch_size * 5  # 5ms between batches
            self.root.after(delay, self.render_visible_batch, batch)
        
        # **âœ… UPDATE TRACKING AFTER ALL BATCHES**
        self.root.after(len(delta_list) // batch_size * 5 + 10, 
                    lambda: setattr(self, 'previous_visible_range', visible_set))
        
    def render_visible_batch(self, batch):
        """Render a batch of visible cells."""
        try:
            for row, col in batch:
                if 0 <= row < self.rows and 0 <= col < self.cols:
                    char = chr(self.grid[row, col])
                    color = self.get_char_color(char)
                    self.safe_update_canvas_object(row, col, char, color)
            
            # Update canvas after batch
            self.canvas.update_idletasks()
            
        except Exception as e:
            print(f"âŒ Visible batch render error: {e}")

    def safe_update_canvas_object(self, row, col, char, color):
        """SAFE canvas object update that preserves grid data integrity."""
        # **âœ… VALIDATE INPUTS**
        if not (0 <= row < self.rows and 0 <= col < self.cols):
            return

        # **ðŸš¨ CRITICAL: ALWAYS READ CURRENT GRID DATA**
        actual_char = chr(self.grid[row, col])
        actual_color = self.get_char_color(actual_char)
        
        # **âœ… USE ACTUAL DATA, NOT PASSED PARAMETERS**
        key = (row, col)
        x1 = col * self.cell_width
        y1 = row * self.cell_height
        x2 = x1 + self.cell_width
        y2 = y1 + self.cell_height

        # **âœ… VALIDATE COORDINATES**
        if x1 < 0 or y1 < 0 or x2 <= x1 or y2 <= y1:
            return

        try:
            if key in self.canvas_objects:
                rect_id, text_id = self.canvas_objects[key]
                
                # **âœ… VERIFY OBJECTS STILL EXIST AND UPDATE SAFELY**
                try:
                    current_text = self.canvas.itemcget(text_id, 'text')
                    current_fill = self.canvas.itemcget(text_id, 'fill')
                    
                    # **âœ… ONLY UPDATE IF VISUAL DIFFERS FROM ACTUAL DATA**
                    if current_text != actual_char or current_fill != actual_color:
                        self.canvas.itemconfig(text_id, text=actual_char, fill=actual_color)
                        
                except tk.TclError:
                    # **âœ… CANVAS OBJECTS WERE DELETED - RECREATE SAFELY**
                    del self.canvas_objects[key]
                    self.create_safe_canvas_object(row, col, actual_char, actual_color, x1, y1, x2, y2)
            else:
                # **âœ… CREATE NEW CANVAS OBJECTS SAFELY**
                self.create_safe_canvas_object(row, col, actual_char, actual_color, x1, y1, x2, y2)
                
        except Exception as e:
            print(f"âŒ Safe canvas object update error at ({row}, {col}): {e}")

    def create_safe_canvas_object(self, row, col, char, color, x1, y1, x2, y2):
        """Create canvas objects safely with actual grid data."""
        try:
            # **ðŸš¨ DOUBLE-CHECK: Always read current grid data**
            if 0 <= row < self.rows and 0 <= col < self.cols:
                actual_char = chr(self.grid[row, col])
                actual_color = self.get_char_color(actual_char)
                
                rect_id = self.canvas.create_rectangle(x1, y1, x2, y2, fill='black', outline='')
                text_id = self.canvas.create_text(
                    x1 + self.cell_width // 2, y1 + self.cell_height // 2,
                    text=actual_char, font=('Arial', int(12 * self.zoom_factor)), 
                    fill=actual_color, tags='text'
                )
                self.canvas_objects[(row, col)] = (rect_id, text_id)
                
                print(f"ðŸ”§ SAFELY CREATED: ({row}, {col}) = '{actual_char}'")
            
        except Exception as e:
            print(f"âŒ Failed to safely create canvas objects at ({row}, {col}): {e}")


    def update_canvas_object(self, row, col, char, color):
        """Enhanced canvas object update with error recovery."""
        # **âœ… VALIDATE INPUTS**
        if not (0 <= row < self.rows and 0 <= col < self.cols):
            return

        key = (row, col)
        x1 = col * self.cell_width
        y1 = row * self.cell_height
        x2 = x1 + self.cell_width
        y2 = y1 + self.cell_height

        # **âœ… VALIDATE COORDINATES**
        if x1 < 0 or y1 < 0 or x2 <= x1 or y2 <= y1:
            return

        try:
            if key in self.canvas_objects:
                rect_id, text_id = self.canvas_objects[key]
                
                # **âœ… VERIFY OBJECTS STILL EXIST**
                try:
                    current_text = self.canvas.itemcget(text_id, 'text')
                    if current_text != char:
                        self.canvas.itemconfig(text_id, text=char, fill=color)
                except tk.TclError:
                    # Objects were deleted - remove from tracking and recreate
                    del self.canvas_objects[key]
                    self.create_new_canvas_object(row, col, char, color, x1, y1, x2, y2)
            else:
                # **âœ… CREATE NEW CANVAS OBJECTS**
                self.create_new_canvas_object(row, col, char, color, x1, y1, x2, y2)
                
        except Exception as e:
            print(f"âŒ Canvas object update error at ({row}, {col}): {e}")

    def create_new_canvas_object(self, row, col, char, color, x1, y1, x2, y2):
        """Create new canvas objects and track them."""
        try:
            rect_id = self.canvas.create_rectangle(x1, y1, x2, y2, fill='black', outline='')
            text_id = self.canvas.create_text(
                x1 + self.cell_width // 2, y1 + self.cell_height // 2,
                text=char, font=('Arial', int(12 * self.zoom_factor)), fill=color, tags='text'
            )
            self.canvas_objects[(row, col)] = (rect_id, text_id)
            
        except Exception as e:
            print(f"âŒ Failed to create canvas objects at ({row}, {col}): {e}")

    def batch_redraw_cells(self, cell_positions):
        """Batch redraw multiple cells efficiently."""
        if not cell_positions:
            return
        
        # Group operations to minimize canvas calls
        updates_needed = []
        for row, col in cell_positions:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                char = chr(self.grid[row, col])
                color = self.get_char_color(char)
                updates_needed.append((row, col, char, color))
        
        # Apply all updates in a single batch
        for row, col, char, color in updates_needed:
            self.update_canvas_object(row, col, char, color)

    def batch_update_cells(self, updates):
        """Batch update cells with given updates."""
        canvas_updates = []
        for row, col, value in updates:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                old_value = self.grid[row, col]
                if old_value != value:
                    self.grid[row, col] = value
                    canvas_updates.append((row, col))

        self.redraw_cells(canvas_updates)

    def redraw_cells(self, updates):
        for row, col in updates:
            self.redraw_cell(row, col)

    def redraw_cell(self, row, col):
        """Enhanced cell redraw that handles missing canvas objects."""
        if not (0 <= row < self.rows and 0 <= col < self.cols):
            return

        try:
            char = chr(self.grid[row, col])
            color = self.get_char_color(char)
            
            cell_key = (row, col)
            
            # **âœ… CHECK IF CANVAS OBJECTS EXIST**
            if cell_key in self.canvas_objects:
                rect_id, text_id = self.canvas_objects[cell_key]
                
                # **âœ… VERIFY OBJECTS STILL EXIST ON CANVAS**
                try:
                    current_text = self.canvas.itemcget(text_id, 'text')
                    current_fill = self.canvas.itemcget(text_id, 'fill')
                    
                    # Update if different
                    if current_text != char or current_fill != color:
                        self.canvas.itemconfig(text_id, text=char, fill=color)
                        print(f"ðŸ“ UPDATED CELL: ({row}, {col}) = '{char}'")
                        
                except tk.TclError:
                    # Canvas objects were deleted - remove from tracking and recreate
                    print(f"ðŸ”§ RECREATING MISSING CANVAS OBJECTS: ({row}, {col})")
                    del self.canvas_objects[cell_key]
                    self.update_canvas_object(row, col, char, color)
            else:
                # **âœ… CREATE MISSING CANVAS OBJECTS**
                print(f"ðŸ”§ CREATING MISSING CANVAS OBJECTS: ({row}, {col})")
                self.update_canvas_object(row, col, char, color)
                
        except Exception as e:
            print(f"âŒ Redraw cell error at ({row}, {col}): {e}")

    def on_zoom(self, value):
        if self.resize_after_id:
            self.root.after_cancel(self.resize_after_id)
        
        self.resize_after_id = self.root.after(100, self._on_zoom)

    def _on_zoom(self):
        self.resize_after_id = None
        zoom_percentage = self.zoom_percentage.get()
        
        # **âœ… STORE OLD CELL SIZES**
        old_cell_width = self.cell_width
        old_cell_height = self.cell_height
        
        # Calculate new zoom factor and cell sizes
        self.zoom_factor = zoom_percentage / 100
        self.cell_width = int(self.base_cell_width * self.zoom_factor)
        self.cell_height = int(self.base_cell_height * self.zoom_factor)
        
        print(f"ðŸ” ZOOM: {old_cell_width}x{old_cell_height} â†’ {self.cell_width}x{self.cell_height}")

        # Calculate the center of the visible area BEFORE zooming (using OLD cell sizes)
        try:
            visible_center_x = self.canvas.canvasx(0) + self.canvas.winfo_width() / 2
            visible_center_y = self.canvas.canvasy(0) + self.canvas.winfo_height() / 2

            # Convert center coordinates to grid coordinates using OLD cell sizes
            center_col = int(visible_center_x / old_cell_width)
            center_row = int(visible_center_y / old_cell_height)
            
            print(f"ðŸŽ¯ CENTER: ({center_row}, {center_col}) based on old cell size")
        except:
            center_col, center_row = self.cols // 2, self.rows // 2
            print(f"ðŸŽ¯ CENTER: Using fallback ({center_row}, {center_col})")

        # **âœ… COMPLETE CANVAS RESET**
        print("ðŸ§¹ Clearing all canvas objects...")
        self.canvas.delete("all")
        self.canvas_objects.clear()
        
        # **âœ… FORCE RESET VISIBLE RANGE TRACKING**
        self.previous_visible_range = set()
        
        # **âœ… RESET CLEANUP COUNTERS**
        if hasattr(self, 'canvas_operation_count'):
            self.canvas_operation_count = 0

        # Update scroll region with new cell sizes
        self.update_scrollregion()
        
        # **âœ… FORCE IMMEDIATE CANVAS UPDATE**
        self.canvas.update_idletasks()

        # Calculate new scroll position to keep the center point (using NEW cell sizes)
        new_scroll_x = center_col * self.cell_width - self.canvas.winfo_width() / 2
        new_scroll_y = center_row * self.cell_height - self.canvas.winfo_height() / 2

        # Apply new scroll position
        total_width = self.cols * self.cell_width
        total_height = self.rows * self.cell_height
        
        if total_width > 0:
            scroll_x_fraction = max(0, min(1, new_scroll_x / total_width))
            self.canvas.xview_moveto(scroll_x_fraction)
        
        if total_height > 0:
            scroll_y_fraction = max(0, min(1, new_scroll_y / total_height))
            self.canvas.yview_moveto(scroll_y_fraction)

        print(f"ðŸ“ SCROLL: Moving to ({scroll_x_fraction:.3f}, {scroll_y_fraction:.3f})")

        # **âœ… FORCE COMPLETE REDRAW AFTER ZOOM**
        self.root.after_idle(self._force_complete_redraw_after_zoom)

        print(f"âœ… ZOOM COMPLETE: {self.zoom_factor:.2f}x, centered at ({center_col}, {center_row})")

    def _force_complete_redraw_after_zoom(self):
        """Force complete redraw after zoom with expanded area calculation."""
        try:
            print("ðŸ”„ FORCE REDRAW AFTER ZOOM...")
            
            # **âœ… GET CURRENT VISIBLE AREA WITH NEW CELL SIZES**
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            x1, y1 = self.canvas.canvasx(0), self.canvas.canvasy(0)
            x2, y2 = x1 + canvas_width, y1 + canvas_height

            # **âœ… CALCULATE WITH GENEROUS BUFFER FOR ZOOM**
            buffer_cells = 10  # Extra buffer for zoom
            start_col = max(0, int(x1 // self.cell_width) - buffer_cells)
            start_row = max(0, int(y1 // self.cell_height) - buffer_cells)
            end_col = min(self.cols, int(x2 // self.cell_width) + buffer_cells + 1)
            end_row = min(self.rows, int(y2 // self.cell_height) + buffer_cells + 1)

            print(f"ðŸ”„ REDRAW AREA: rows {start_row}-{end_row}, cols {start_col}-{end_col}")
            print(f"ðŸ”„ CELL SIZE: {self.cell_width}x{self.cell_height}")

            # **âœ… FORCE REDRAW EVERY CELL IN EXPANDED AREA**
            cells_drawn = 0
            for row in range(start_row, end_row):
                for col in range(start_col, end_col):
                    if 0 <= row < self.rows and 0 <= col < self.cols:
                        char = chr(self.grid[row, col])
                        color = self.get_char_color(char)
                        self.update_canvas_object(row, col, char, color)
                        cells_drawn += 1

            # **âœ… UPDATE VISIBLE RANGE TRACKING**
            self.previous_visible_range = set((r, c) for r in range(start_row, end_row) for c in range(start_col, end_col))
            
            # Ensure text is on top
            self.canvas.tag_raise('text')
            
            print(f"âœ… ZOOM REDRAW COMPLETE: {cells_drawn} cells drawn")
            
            # **âœ… SECOND PASS AFTER BRIEF DELAY**
            self.root.after(200, self._second_pass_redraw)
            
        except Exception as e:
            print(f"âŒ Zoom redraw error: {e}")
            # Fallback to regular redraw
            self._redraw_visible_cells()

    def _second_pass_redraw(self):
        """Second pass redraw to ensure nothing was missed."""
        try:
            print("ðŸ”„ SECOND PASS REDRAW...")
            
            # Get current visible area again (in case user scrolled)
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            x1, y1 = self.canvas.canvasx(0), self.canvas.canvasy(0)
            x2, y2 = x1 + canvas_width, y1 + canvas_height

            start_col = max(0, int(x1 // self.cell_width))
            start_row = max(0, int(y1 // self.cell_height))
            end_col = min(self.cols, int(x2 // self.cell_width) + 2)
            end_row = min(self.rows, int(y2 // self.cell_height) + 2)

            # Check for any missing cells in visible area
            missing_cells = 0
            for row in range(start_row, end_row):
                for col in range(start_col, end_col):
                    if 0 <= row < self.rows and 0 <= col < self.cols:
                        key = (row, col)
                        if key not in self.canvas_objects:
                            char = chr(self.grid[row, col])
                            color = self.get_char_color(char)
                            self.update_canvas_object(row, col, char, color)
                            missing_cells += 1

            if missing_cells > 0:
                print(f"ðŸ”§ SECOND PASS: Fixed {missing_cells} missing cells")
            else:
                print("âœ… SECOND PASS: No missing cells found")
                
        except Exception as e:
            print(f"âŒ Second pass error: {e}")

    def on_canvas_configure(self, event):
        """Enhanced canvas configure handling."""
        print(f"ðŸ“º CANVAS CONFIGURE: {event.width}x{event.height}")
        
        # Update scroll region
        self.update_scrollregion()
        
        # Force redraw after brief delay to let things settle
        self.root.after(100, self._redraw_visible_cells)

    def on_click(self, event):
        """Fixed click that separates brush painting from rectangle selection."""
        col = int(self.canvas.canvasx(event.x) // self.cell_width)
        row = int(self.canvas.canvasy(event.y) // self.cell_height)
        ctrl_held = event.state & 0x4

        # **âœ… IMMEDIATELY CLEAR HOVER PREVIEW**
        self.canvas.delete('hover_preview')

        # **âœ… CHECK SPACE-ONLY MODE**
        if not hasattr(self, 'select_spaces_only'):
            self.select_spaces_only = False

        print(f"ðŸ–±ï¸ CLICK: ({row}, {col}), Ctrl: {ctrl_held}, Space-only: {self.select_spaces_only}")

        if self.smart_select_pending and not ctrl_held:
            settings = self.smart_select_pending
            self.smart_select_pending = None
            self.smart_select_at(
                row=row,
                col=col,
                **settings,
            )
            return

        if ctrl_held:  # Ctrl+Click to remove from selection
            cells_to_remove = set()
            for d_row in range(self.paintbrush_size):
                for d_col in range(self.paintbrush_size):
                    target_row = row + d_row
                    target_col = col + d_col
                    if (0 <= target_row < self.rows and 0 <= target_col < self.cols):
                        if (target_row, target_col) in self.selected_cells:
                            cells_to_remove.add((target_row, target_col))
            
            if cells_to_remove:
                self.selected_cells -= cells_to_remove
                print(f"  âŒ DE-SELECTED: {len(cells_to_remove)} cells")
                self.update_selection()
            return

        # **âœ… ALWAYS USE BRUSH PAINTING - NO RECTANGLE MODE**
        self.apply_brush(event)

        # **âœ… NEVER SET RECTANGLE START DURING BRUSH PAINTING**
        # Rectangle selection is only for keyboard shortcuts or special modes
        self.rect_start = None
        self.rect_end = None
        
        print(f"ðŸ–Œï¸ BRUSH PAINT: Applied to ({row}, {col})")
        self.update_selection()

    def apply_brush(self, event):
        """Optimized apply_brush that maintains fast painting regardless of selection size."""
        # **âœ… BOUNDARY CHECKS**
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        
        if (event.x < 0 or event.x >= canvas_width or 
            event.y < 0 or event.y >= canvas_height):
            return
        
        col = int(self.canvas.canvasx(event.x) // self.cell_width)
        row = int(self.canvas.canvasy(event.y) // self.cell_height)

        if (row < 0 or row >= self.rows or col < 0 or col >= self.cols):
            return

        self.canvas.delete('hover_preview')

        if not hasattr(self, 'select_spaces_only'):
            self.select_spaces_only = False

        new_selections = set()
        for d_row in range(self.paintbrush_size):
            for d_col in range(self.paintbrush_size):
                target_row = row + d_row
                target_col = col + d_col
                
                if not (0 <= target_row < self.rows and 0 <= target_col < self.cols):
                    continue
                
                if self.select_spaces_only:
                    current_char = chr(self.grid[target_row, target_col])
                    if current_char != ' ':
                        continue
                            
                new_selections.add((target_row, target_col))
                
                # **âœ… ALWAYS CREATE SELECTION VISUALS FOR NEW SELECTIONS**
                if (target_row, target_col) not in self.selected_cells:
                    x1 = target_col * self.cell_width
                    y1 = target_row * self.cell_height
                    x2 = x1 + self.cell_width
                    y2 = y1 + self.cell_height
                    
                    if (x1 >= 0 and y1 >= 0 and x2 > x1 and y2 > y1):
                        outline_color = 'orange' if self.select_spaces_only else 'cyan'
                        self.canvas.create_rectangle(x1, y1, x2, y2, outline=outline_color, 
                                                tags='selection', width=2)
        
        # **âœ… ADD TO SELECTION**
        if new_selections:
            old_size = len(self.selected_cells)
            self.selected_cells.update(new_selections)
            new_size = len(self.selected_cells)
            
            print(f"ðŸ–Œï¸ PAINTED: {len(new_selections)} new cells, total: {new_size}")

    def safe_cleanup_canvas_objects(self):
        """SAFE cleanup that only removes canvas objects, never grid data."""
        try:
            if not hasattr(self, 'canvas_objects') or len(self.canvas_objects) < 1000:
                return
            
            print(f"ðŸ§¹ SAFE CLEANUP: Current count: {len(self.canvas_objects)}")
            
            # **âœ… GET VISIBLE AREA**
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            x1, y1 = self.canvas.canvasx(0), self.canvas.canvasy(0)
            x2, y2 = x1 + canvas_width, y1 + canvas_height
            
            buffer_cells = 50
            visible_start_row = max(0, int(y1 // self.cell_height) - buffer_cells)
            visible_end_row = min(self.rows, int(y2 // self.cell_height) + buffer_cells)
            visible_start_col = max(0, int(x1 // self.cell_width) - buffer_cells)
            visible_end_col = min(self.cols, int(x2 // self.cell_width) + buffer_cells)
            
            # **âœ… ONLY REMOVE CANVAS OBJECTS, PRESERVE GRID DATA**
            to_remove = []
            removed_count = 0
            
            for (row, col), (rect_id, text_id) in self.canvas_objects.items():
                if (row < visible_start_row or row > visible_end_row or
                    col < visible_start_col or col > visible_end_col):
                    try:
                        # **ðŸš¨ ONLY DELETE CANVAS OBJECTS, NOT GRID DATA**
                        self.canvas.delete(rect_id)
                        self.canvas.delete(text_id)
                        to_remove.append((row, col))
                        removed_count += 1
                    except:
                        to_remove.append((row, col))
            
            # **âœ… REMOVE FROM CANVAS TRACKING ONLY**
            for key in to_remove:
                if key in self.canvas_objects:
                    del self.canvas_objects[key]
            
            print(f"âœ… SAFE CLEANUP COMPLETE: Removed {removed_count} canvas objects. Grid data preserved.")
            
        except Exception as e:
            print(f"âŒ Safe cleanup error: {e}")

    def _finish_brush_update(self):
        """Complete brush update after all mouse movements are done."""
        self._brush_update_pending = False
        self.update_selection()


    def on_drag(self, event):
        """Fixed drag that only does brush painting, no rectangles."""
        # Safe initialization
        if not hasattr(self, '_currently_painting'):
            self._currently_painting = False
        if not hasattr(self, '_cleanup_after_painting_id'):
            self._cleanup_after_painting_id = None
        
        # Mark that we're actively painting
        self._currently_painting = True
        
        # SAFE: Cancel any pending cleanup only if ID is valid
        if self._cleanup_after_painting_id is not None:
            try:
                self.root.after_cancel(self._cleanup_after_painting_id)
                self._cleanup_after_painting_id = None
            except ValueError:
                self._cleanup_after_painting_id = None
        
        # **âœ… ONLY BRUSH PAINTING DURING DRAG**
        self.apply_brush(event)
        
        col = int(self.canvas.canvasx(event.x) // self.cell_width)
        row = int(self.canvas.canvasy(event.y) // self.cell_height)
        
        # **âœ… IMMEDIATE: Update hover preview so cursor follows**
        self.on_mouse_motion(event)
        
        # **âœ… ENSURE NO RECTANGLE SELECTION DURING DRAG**
        self.rect_start = None
        self.rect_end = None
        
        # THROTTLED: Update debug label (non-critical)
        if not hasattr(self, '_debug_update_pending'):
            self._debug_update_pending = False
        
        if not self._debug_update_pending:
            self._debug_update_pending = True
            self.root.after_idle(self._update_debug_label, row, col)
        
        # Schedule cleanup for after painting stops
        self._cleanup_after_painting_id = self.root.after(500, self._finish_painting_session)

    def debug_grid_integrity(self):
        """Debug method to check for grid data corruption."""
        print(f"\nðŸ” GRID INTEGRITY CHECK:")
        
        if not hasattr(self, 'grid') or self.grid is None:
            print("  âŒ NO GRID DATA")
            return False
        
        # Check for corrupted data in selected region
        black_cells = []
        space_cells = []
        valid_chars = []
        
        for row, col in self.selected_cells:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                char_code = self.grid[row, col]
                char = chr(char_code)
                
                if char_code == 0:
                    black_cells.append((row, col))
                elif char == ' ':
                    space_cells.append((row, col))
                else:
                    valid_chars.append((row, col, char))
        
        print(f"  Selected cells: {len(self.selected_cells)}")
        print(f"  Black/corrupted cells: {len(black_cells)}")
        print(f"  Space cells: {len(space_cells)}")
        print(f"  Valid character cells: {len(valid_chars)}")
        
        if black_cells:
            print(f"  âŒ CORRUPTION DETECTED: {black_cells[:5]}...")  # Show first 5
            return False
        else:
            print("  âœ… Grid integrity OK")
            return True


    def debug_space_selection(self):
        """Debug method to check space selection accuracy."""
        if not hasattr(self, 'select_spaces_only'):
            self.select_spaces_only = False
            
        print(f"\nðŸ” SPACE SELECTION DEBUG:")
        print(f"  Mode: {'SPACE-ONLY' if self.select_spaces_only else 'NORMAL'}")
        print(f"  Selected cells: {len(self.selected_cells)}")
        
        if self.select_spaces_only and self.selected_cells:
            invalid_selections = []
            for row, col in self.selected_cells:
                if 0 <= row < self.rows and 0 <= col < self.cols:
                    char = chr(self.grid[row, col])
                    if char != ' ':
                        invalid_selections.append((row, col, char, ord(char)))
            
            if invalid_selections:
                print(f"  âŒ INVALID SELECTIONS: {len(invalid_selections)}")
                for row, col, char, ascii_val in invalid_selections[:5]:  # Show first 5
                    print(f"    ({row}, {col}): '{char}' (ASCII {ascii_val})")
            else:
                print(f"  âœ… ALL SELECTIONS VALID (spaces only)")
        
        print()

    def debug_canvas_state(self):
        """Debug method to check canvas state."""
        try:
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            x1, y1 = self.canvas.canvasx(0), self.canvas.canvasy(0)
            x2, y2 = x1 + canvas_width, y1 + canvas_height
            
            visible_start_row = max(0, int(y1 // self.cell_height))
            visible_end_row = min(self.rows, int(y2 // self.cell_height) + 1)
            visible_start_col = max(0, int(x1 // self.cell_width))
            visible_end_col = min(self.cols, int(x2 // self.cell_width) + 1)
            
            expected_cells = (visible_end_row - visible_start_row) * (visible_end_col - visible_start_col)
            actual_cells = len([k for k in self.canvas_objects.keys() 
                            if visible_start_row <= k[0] < visible_end_row 
                            and visible_start_col <= k[1] < visible_end_col])
            
            print(f"ðŸ” DEBUG STATE:")
            print(f"  Canvas: {canvas_width}x{canvas_height}")
            print(f"  Scroll: ({x1:.1f}, {y1:.1f}) to ({x2:.1f}, {y2:.1f})")
            print(f"  Visible: rows {visible_start_row}-{visible_end_row}, cols {visible_start_col}-{visible_end_col}")
            print(f"  Cells: {actual_cells}/{expected_cells} objects exist")
            print(f"  Cell size: {self.cell_width}x{self.cell_height}")
            print(f"  Zoom: {self.zoom_factor:.2f}x")
            
            if actual_cells < expected_cells * 0.9:  # Less than 90% of expected cells
                print("âš ï¸  MISSING CELLS DETECTED!")
                return False
            return True
            
        except Exception as e:
            print(f"âŒ Debug state error: {e}")
            return False

    def _finish_painting_session(self):
        """Modified finish painting session that ensures visual updates."""
        try:
            self._currently_painting = False
            
            # Safety check
            if not hasattr(self, 'canvas_operation_count'):
                self.canvas_operation_count = 0
            if not hasattr(self, 'cleanup_threshold'):
                self.cleanup_threshold = 2000
            
            selection_size = len(self.selected_cells) if hasattr(self, 'selected_cells') else 0
            print(f"ðŸ PAINTING SESSION COMPLETE: {selection_size} total selected cells")
            
            # **âœ… ALWAYS ALLOW SOME CLEANUP FOR CANVAS HEALTH**
            if self.canvas_operation_count > self.cleanup_threshold:
                # **âœ… GENTLE CLEANUP EVEN WITH LARGE SELECTIONS**
                if hasattr(self, 'safe_cleanup_canvas_objects'):
                    self.safe_cleanup_canvas_objects()
                self.canvas_operation_count = 0
                print("ðŸ§¹ GENTLE CLEANUP PERFORMED")
            
            # **âœ… FORCE CANVAS UPDATE TO ENSURE VISUALS ARE CURRENT**
            self.canvas.update_idletasks()
                    
        except Exception as e:
            print(f"âŒ Error in _finish_painting_session: {e}")
            self._currently_painting = False
            if hasattr(self, 'canvas_operation_count'):
                self.canvas_operation_count = 0

    def _update_debug_label(self, row, col):
        """Deferred debug label update."""
        self._debug_update_pending = False
        self.debug_label.config(text=f"Drag to ({row}, {col}), Selection mode: {self.selection_mode}")


    def on_release(self, event):
        """Fixed release that never creates rectangles after brush painting."""
        col = int(self.canvas.canvasx(event.x) // self.cell_width)
        row = int(self.canvas.canvasy(event.y) // self.cell_height)
        ctrl_held = event.state & 0x4
        
        print(f"ðŸ–± Release at ({row}, {col}) - Brush painting complete")

        if ctrl_held:
            return

        # **âœ… NEVER DO RECTANGLE SELECTION AFTER BRUSH PAINTING**
        # Rectangle selection is disabled for mouse painting
        
        # Mark painting session as finished
        self._currently_painting = False
        self.is_selecting = False
        
        # **âœ… ENSURE RECTANGLE STATE IS CLEARED**
        self.rect_start = None
        self.rect_end = None
        
        # Schedule cleanup now that painting is done
        self.root.after(100, self._finish_painting_session)
        
        print("âœ… PAINTING SESSION COMPLETE - No rectangles created")

    def on_keypress(self, event):
        """Optimized keypress handling that's fast regardless of selection size."""
        char = event.char
        if not char:
            return

        if not self.selected_cells:
            return

        selection_size = len(self.selected_cells)
        print(f"ðŸ”¤ KEYPRESS: '{char}' for {selection_size} selected cells")

        # **âœ… DIRECT GRID UPDATES - ALWAYS FAST**
        undo_action = []
        cells_changed = 0
        visible_updates = []

        # Get visible area for immediate visual updates
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        x1, y1 = self.canvas.canvasx(0), self.canvas.canvasy(0)
        x2, y2 = x1 + canvas_width, y1 + canvas_height

        visible_start_row = max(0, int(y1 // self.cell_height))
        visible_end_row = min(self.rows, int(y2 // self.cell_height) + 1)
        visible_start_col = max(0, int(x1 // self.cell_width))
        visible_end_col = min(self.cols, int(x2 // self.cell_width) + 1)

        visible_area = set((r, c) for r in range(visible_start_row, visible_end_row) 
                        for c in range(visible_start_col, visible_end_col))

        for row, col in self.selected_cells:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                old_char = chr(self.grid[row, col])
                new_char = self.apply_extra_spaces_to_char(char)
                if old_char != new_char:
                    undo_action.append((row, col, old_char))
                    self.grid[row, col] = ord(new_char)  # Direct fast update
                    cells_changed += 1
                    
                    # **âœ… TRACK VISIBLE CELLS FOR IMMEDIATE UPDATE**
                    if (row, col) in visible_area:
                        visible_updates.append((row, col))

        print(f"  ðŸ“ UPDATED: {cells_changed} cells, {len(visible_updates)} visible")

        # **âœ… ADD TO UNDO STACK**
        if undo_action:
            if not hasattr(self, 'undo_stack'):
                self.undo_stack = []
            self.undo_stack.append(undo_action)
            if len(self.undo_stack) > self.max_undo:
                self.undo_stack.pop(0)

        # **âœ… IMMEDIATE VISUAL UPDATES FOR VISIBLE CELLS ONLY**
        if visible_updates:
            for row, col in visible_updates:
                if 0 <= row < self.rows and 0 <= col < self.cols:
                    char = chr(self.grid[row, col])
                    color = self.get_char_color(char)
                    self.simple_update_canvas_object(row, col, char, color)
            
            # **âœ… SINGLE CANVAS UPDATE**
            self.canvas.update_idletasks()

        print(f"âœ… KEYPRESS COMPLETE: {cells_changed} cells changed, {len(visible_updates)} visible updates")


    def simple_cleanup_check(self):
        """Modified cleanup check that allows cleanup even with large selections."""
        # **âœ… ONLY DISABLE CLEANUP IF EXTREMELY LARGE SELECTION AND ACTIVELY PAINTING**
        if (hasattr(self, 'selected_cells') and len(self.selected_cells) > 2000 and 
            hasattr(self, '_currently_painting') and self._currently_painting):
            print("â¸ï¸  CLEANUP DISABLED: Very large selection and actively painting")
            return False
        
        # **âœ… ALLOW CLEANUP FOR CANVAS MANAGEMENT**
        if hasattr(self, 'canvas_objects') and len(self.canvas_objects) > 3000:
            print("ðŸ§¹ CLEANUP NEEDED: Too many canvas objects")
            return True
        
        return True

    def simple_update_canvas_object(self, row, col, char, color):
        """Simple fast canvas object update."""
        key = (row, col)
        
        if key in self.canvas_objects:
            rect_id, text_id = self.canvas_objects[key]
            try:
                self.canvas.itemconfig(text_id, text=char, fill=color)
                return
            except tk.TclError:
                # Object was deleted, remove from tracking
                del self.canvas_objects[key]
        
        # Create new objects if needed
        x1 = col * self.cell_width
        y1 = row * self.cell_height
        x2 = x1 + self.cell_width
        y2 = y1 + self.cell_height
        
        try:
            rect_id = self.canvas.create_rectangle(x1, y1, x2, y2, fill='black', outline='')
            text_id = self.canvas.create_text(
                x1 + self.cell_width // 2, y1 + self.cell_height // 2,
                text=char, font=('Arial', int(12 * self.zoom_factor)), fill=color, tags='text'
            )
            self.canvas_objects[key] = (rect_id, text_id)
        except Exception as e:
            print(f"âŒ Failed to create canvas object at ({row}, {col}): {e}")
            
    def handle_normal_selection_keypress(self, char, selection_size):
        """Handle normal-sized selections with immediate rendering."""
        updates = []
        undo_action = []
        cells_changed = 0

        for row, col in self.selected_cells:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                old_char = chr(self.grid[row, col])
                new_char = self.apply_extra_spaces_to_char(char)
                if old_char != new_char:
                    undo_action.append((row, col, old_char))
                    updates.append((row, col, ord(new_char)))
                    cells_changed += 1

        if updates:
            # **âœ… IMMEDIATE UPDATE FOR SMALL SELECTIONS**
            self.batch_update_cells(updates)
            
            # Force redraw visible cells
            for row, col, _ in updates:
                if (row, col) in self.previous_visible_range:
                    self.redraw_cell(row, col)
            
            # Add to undo stack
            if undo_action:
                if not hasattr(self, 'undo_stack'):
                    self.undo_stack = []
                self.undo_stack.append(undo_action)
                if len(self.undo_stack) > self.max_undo:
                    self.undo_stack.pop(0)
            
            print(f"âœ… NORMAL KEYPRESS: {cells_changed} cells updated immediately")

    def handle_large_selection_keypress(self, char, selection_size):
        """Handle large selections with progressive batched rendering."""
        print(f"ðŸ”„ PROCESSING LARGE SELECTION: {selection_size} cells...")
        
        # **âœ… UPDATE GRID DATA FIRST (FAST)**
        updates = []
        undo_action = []
        cells_changed = 0

        for row, col in self.selected_cells:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                old_char = chr(self.grid[row, col])
                new_char = self.apply_extra_spaces_to_char(char)
                if old_char != new_char:
                    undo_action.append((row, col, old_char))
                    self.grid[row, col] = ord(new_char)  # Direct grid update
                    updates.append((row, col))
                    cells_changed += 1

        print(f"  ðŸ“ GRID UPDATED: {cells_changed} cells changed")

        # **âœ… ADD TO UNDO STACK**
        if undo_action:
            if not hasattr(self, 'undo_stack'):
                self.undo_stack = []
            self.undo_stack.append(undo_action)
            if len(self.undo_stack) > self.max_undo:
                self.undo_stack.pop(0)

        # **âœ… PROGRESSIVE VISUAL RENDERING**
        if updates:
            self.progressive_visual_update(updates)
        
        print(f"âœ… LARGE SELECTION COMPLETE: {cells_changed} cells processed")
    def render_cell_batch(self, batch):
        """Render a batch of cells without overwhelming the canvas."""
        try:
            for row, col in batch:
                if 0 <= row < self.rows and 0 <= col < self.cols:
                    # **âœ… SAFE CELL REDRAW**
                    char = chr(self.grid[row, col])
                    color = self.get_char_color(char)
                    self.safe_update_canvas_object(row, col, char, color)
            
            # Force canvas update for this batch
            self.canvas.update_idletasks()
            
        except Exception as e:
            print(f"âŒ Batch render error: {e}")

    def rebuild_large_selection_visuals(self):
        """Rebuild selection visuals for large selections."""
        try:
            print("ðŸ”„ REBUILDING LARGE SELECTION VISUALS...")
            
            # **âœ… CLEAR EXISTING SELECTION VISUALS**
            self.canvas.delete('selection')
            
            # **âœ… ONLY REBUILD VISIBLE SELECTION**
            visible_selected = self.selected_cells & self.previous_visible_range
            
            if visible_selected:
                outline_color = 'orange' if (hasattr(self, 'select_spaces_only') and self.select_spaces_only) else 'cyan'
                
                # **âœ… CREATE SELECTION VISUALS IN BATCHES**
                batch_size = 50
                selected_list = list(visible_selected)
                
                for i in range(0, len(selected_list), batch_size):
                    batch = selected_list[i:i + batch_size]
                    self.root.after(i // batch_size * 5, self.create_selection_batch, batch, outline_color)
            
            print(f"âœ… SELECTION VISUALS SCHEDULED: {len(visible_selected)} visible selections")
            
        except Exception as e:
            print(f"âŒ Selection rebuild error: {e}")

    def create_selection_batch(self, batch, outline_color):
        """Create a batch of selection rectangles."""
        try:
            for row, col in batch:
                if 0 <= row < self.rows and 0 <= col < self.cols:
                    x1 = col * self.cell_width
                    y1 = row * self.cell_height
                    x2 = x1 + self.cell_width
                    y2 = y1 + self.cell_height
                    
                    self.canvas.create_rectangle(x1, y1, x2, y2, outline=outline_color, 
                                            tags='selection', width=2)
            
            # Update canvas after each batch
            self.canvas.update_idletasks()
            
        except Exception as e:
            print(f"âŒ Selection batch error: {e}")

    def progressive_visual_update(self, updates):
        """Progressive visual update for large selections to prevent canvas overload."""
        # **âœ… ONLY UPDATE VISIBLE CELLS IMMEDIATELY**
        visible_updates = [(row, col) for row, col in updates 
                        if (row, col) in self.previous_visible_range]
        
        print(f"  ðŸŽ¨ VISUAL UPDATE: {len(visible_updates)} visible cells of {len(updates)} total")
        
        # **âœ… BATCH VISIBLE UPDATES**
        batch_size = 100  # Process 100 cells at a time
        for i in range(0, len(visible_updates), batch_size):
            batch = visible_updates[i:i + batch_size]
            
            # Schedule batch update
            self.root.after(i // batch_size * 10, self.render_cell_batch, batch)
        
        # **âœ… CLEAR AND REBUILD SELECTION VISUALS**
        self.root.after(50, self.rebuild_large_selection_visuals)

    def on_mousewheel(self, event):
        units = int(-1 * (event.delta / 120))
        if units == 0:
            if event.delta > 0:
                units = -1
            elif event.delta < 0:
                units = 1
        if units != 0:
            self.canvas.yview_scroll(units, "units")
            self._schedule_scroll_refresh()

    def alt_pressed_callback(self, event):
        """Toggles between freeform and rectangle selection when Alt is pressed."""
        if self.selection_mode == 'rectangle':
            self.selection_mode = 'freeform'
            self.debug_label.config(text="Freeform selection mode (Alt toggled ON)")
        else:
            self.selection_mode = 'rectangle'
            self.debug_label.config(text="Rectangle selection mode (Alt toggled OFF)")


    def alt_released_callback(self, event):
        """Does nothing to prevent clearing selection on Alt release."""
        pass  # No need to reset anything, just keep selection mode as toggled

    def undo(self, event=None):
        """Reverts the last selection change (Ctrl+Z)."""
        if not self.undo_stack:
            print("UNDO STACK EMPTY âŒ")  # ðŸ”¥ Debug print
            return  # âœ… No actions to undo

        print("UNDO TRIGGERED âœ…")  # ðŸ”¥ Debug print
        last_action = self.undo_stack.pop()

        for row, col, old_char in last_action:
            self.grid[row, col] = ord(old_char)  # âœ… Restore old value
            self.redraw_cell(row, col)

        self.update_selection()
        self.debug_label.config(text=f"Undo performed, {len(last_action)} cells restored.")

    def toggle_space_selection(self, event=None):
        """Enhanced toggle with immediate cleanup of invalid selections."""
        if not hasattr(self, 'select_spaces_only'):
            self.select_spaces_only = False
            
        self.select_spaces_only = not self.select_spaces_only
        status = "ON" if self.select_spaces_only else "OFF"
        
        # **âœ… IMMEDIATE CLEANUP WHEN TURNING ON SPACE-ONLY MODE**
        if self.select_spaces_only and self.selected_cells:
            valid_selections = set()
            removed_count = 0
            
            for row, col in self.selected_cells:
                if (0 <= row < self.rows and 0 <= col < self.cols):
                    current_char = chr(self.grid[row, col])
                    if current_char == ' ':  # Only keep actual spaces
                        valid_selections.add((row, col))
                    else:
                        removed_count += 1
            
            self.selected_cells = valid_selections
            print(f"ðŸ”„ FILTERED: Removed {removed_count} non-space selections")
        
        # **âœ… CLEAR ALL VISUAL ARTIFACTS AND REDRAW**
        self.canvas.delete('selection')
        self.canvas.delete('hover_preview')
        self.update_selection()
        
        self.debug_label.config(text=f"Space-Only Selection: {status}")
        print(f"ðŸŽ¯ SPACE-ONLY MODE: {status}")
        
        return 'break'

    def cleanup_canvas_objects(self):
        """Enhanced cleanup that removes stray objects and invalid colors."""
        try:
            if not hasattr(self, 'canvas_objects') or len(self.canvas_objects) < 1000:
                # **âœ… EVEN FOR SMALL CLEANUP, REMOVE STRAY COLORED OBJECTS**
                self.remove_stray_colored_objects()
                return
            
            print(f"ðŸ§¹ Enhanced cleanup. Current count: {len(self.canvas_objects)}")
            
            # **âœ… REMOVE STRAY COLORED OBJECTS FIRST**
            self.remove_stray_colored_objects()
            
            # Continue with normal cleanup...
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            x1, y1 = self.canvas.canvasx(0), self.canvas.canvasy(0)
            x2, y2 = x1 + canvas_width, y1 + canvas_height
            
            buffer_cells = 50
            visible_start_row = max(0, int(y1 // self.cell_height) - buffer_cells)
            visible_end_row = min(self.rows, int(y2 // self.cell_height) + buffer_cells)
            visible_start_col = max(0, int(x1 // self.cell_width) - buffer_cells)
            visible_end_col = min(self.cols, int(x2 // self.cell_width) + buffer_cells)
            
            to_remove = []
            removed_count = 0
            
            for (row, col), (rect_id, text_id) in self.canvas_objects.items():
                if (row < visible_start_row or row > visible_end_row or
                    col < visible_start_col or col > visible_end_col):
                    try:
                        self.canvas.delete(rect_id)
                        self.canvas.delete(text_id)
                        to_remove.append((row, col))
                        removed_count += 1
                    except:
                        to_remove.append((row, col))
            
            for key in to_remove:
                if key in self.canvas_objects:
                    del self.canvas_objects[key]
            
            print(f"âœ… Enhanced cleanup complete. Removed {removed_count} objects. Remaining: {len(self.canvas_objects)}")
            
        except Exception as e:
            print(f"âŒ Enhanced cleanup error: {e}")
            self.canvas_operation_count = 0

    def remove_stray_colored_objects(self):
        """Remove any stray red/gray/colored objects that shouldn't exist."""
        try:
            all_items = self.canvas.find_all()
            removed_count = 0
            
            for item in all_items:
                try:
                    # **âœ… CHECK FOR INVALID COLORS**
                    fill = self.canvas.itemcget(item, 'fill')
                    outline = self.canvas.itemcget(item, 'outline')
                    
                    # **âœ… REMOVE OBJECTS WITH ERROR COLORS**
                    invalid_colors = ['red', 'gray', 'grey', 'pink', 'purple']
                    if (fill in invalid_colors or outline in invalid_colors):
                        self.canvas.delete(item)
                        removed_count += 1
                        continue
                    
                    # **âœ… CHECK FOR OBJECTS OUTSIDE VALID GRID AREA**
                    coords = self.canvas.coords(item)
                    if len(coords) >= 4:
                        x1, y1 = coords[0], coords[1]
                        # Calculate grid position
                        grid_col = int(x1 // self.cell_width) if self.cell_width > 0 else -1
                        grid_row = int(y1 // self.cell_height) if self.cell_height > 0 else -1
                        
                        # **âœ… REMOVE OBJECTS OUTSIDE GRID BOUNDS**
                        if (grid_row < 0 or grid_row >= self.rows or 
                            grid_col < 0 or grid_col >= self.cols):
                            self.canvas.delete(item)
                            removed_count += 1
                            continue
                        
                        # **âœ… REMOVE OBJECTS WITH INVALID COORDINATES**
                        if (x1 < -100 or y1 < -100 or 
                            x1 > self.cols * self.cell_width + 100 or 
                            y1 > self.rows * self.cell_height + 100):
                            self.canvas.delete(item)
                            removed_count += 1
                            continue
                    
                except Exception as e:
                    # If we can't inspect the object, it might be corrupted - remove it
                    try:
                        self.canvas.delete(item)
                        removed_count += 1
                    except:
                        pass
            
            if removed_count > 0:
                print(f"ðŸ§¹ REMOVED {removed_count} stray colored/invalid objects")
                
        except Exception as e:
            print(f"âŒ Error removing stray objects: {e}")

    def update_selection(self):
        """Enhanced selection update with space-only mode colors."""
        # Safe attribute access
        if not hasattr(self, '_currently_painting'):
            self._currently_painting = False
        if not hasattr(self, '_selection_update_id'):
            self._selection_update_id = None
        if not hasattr(self, 'select_spaces_only'):
            self.select_spaces_only = False
        
        # If we're actively painting, skip heavy updates
        if self._currently_painting:
            return
        
        # Only do full selection updates when not painting
        if self._selection_update_id:
            try:
                self.root.after_cancel(self._selection_update_id)
            except ValueError:
                pass
            self._selection_update_id = None
        
        # Defer heavy selection updates
        self._selection_update_id = self.root.after(100, self._update_selection_with_colors)

    def _update_selection_with_colors(self):
        """Update selection with appropriate colors for space-only mode."""
        self._selection_update_id = None
        
        if hasattr(self, '_currently_painting') and self._currently_painting:
            return
        
        # Clear existing selection visuals
        self.canvas.delete('selection')
        
        # Get color based on mode
        if not hasattr(self, 'select_spaces_only'):
            self.select_spaces_only = False
        
        outline_color = 'orange' if self.select_spaces_only else 'cyan'
        
        # Only redraw visible selected cells
        if hasattr(self, 'previous_visible_range'):
            visible_selected = self.selected_cells & self.previous_visible_range
        else:
            visible_selected = self.selected_cells

        for row, col in visible_selected:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                x1 = col * self.cell_width
                y1 = row * self.cell_height
                x2 = x1 + self.cell_width
                y2 = y1 + self.cell_height
                self.canvas.create_rectangle(x1, y1, x2, y2, outline=outline_color, tags='selection')

        print(f"ðŸ”„ SELECTION UPDATE: {len(visible_selected)} cells, color: {outline_color}")

    def _update_selection_deferred(self):
        """Heavy selection update - only when not actively painting."""
        self._selection_update_id = None
        
        if hasattr(self, '_currently_painting') and self._currently_painting:
            return  # Skip if still painting
        
        # Clean up any duplicate selection rectangles
        existing_selection_items = self.canvas.find_withtag('selection')
        existing_coords = set()
        items_to_delete = []
        
        for item in existing_selection_items:
            coords = self.canvas.coords(item)
            if len(coords) == 4:
                coord_key = (coords[0], coords[1])
                if coord_key in existing_coords:
                    items_to_delete.append(item)  # Duplicate
                else:
                    existing_coords.add(coord_key)
        
        # Remove duplicates
        for item in items_to_delete:
            self.canvas.delete(item)

    def _update_selection_now(self):
        """Actual selection update with optimizations."""
        self._selection_update_id = None
        
        # Only update visible selected cells
        visible_selected = self.selected_cells & self.previous_visible_range
        
        # Get existing selection objects to avoid recreating
        existing_selection = set()
        for item in self.canvas.find_withtag('selection'):
            coords = self.canvas.coords(item)
            if len(coords) == 4:
                col = int(coords[0] // self.cell_width)
                row = int(coords[1] // self.cell_height)
                existing_selection.add((row, col))
        
        # Only create new selection rectangles for cells that don't have them
        new_selections = visible_selected - existing_selection
        for row, col in new_selections:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                x1 = col * self.cell_width
                y1 = row * self.cell_height
                x2 = x1 + self.cell_width
                y2 = y1 + self.cell_height
                self.canvas.create_rectangle(x1, y1, x2, y2, outline='cyan', tags='selection')
        
        # Remove selection rectangles for cells no longer selected
        obsolete_selections = existing_selection - visible_selected
        if obsolete_selections:
            for item in self.canvas.find_withtag('selection'):
                coords = self.canvas.coords(item)
                if len(coords) == 4:
                    col = int(coords[0] // self.cell_width)
                    row = int(coords[1] // self.cell_height)
                    if (row, col) in obsolete_selections:
                        self.canvas.delete(item)


    def fill_selection(self, char):
        """Fills the selected region with the given character while supporting undo."""
        if self.grid is None or not self.selected_cells:
            return

        undo_action = []

        for row, col in self.selected_cells:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                old_char = chr(self.grid[row, col])
                new_char = self.apply_extra_spaces_to_char(char)
                if old_char != new_char:
                    undo_action.append((row, col, old_char))  # âœ… Store only changed cells
                    self.grid[row, col] = ord(new_char)
                    self.redraw_cell(row, col)

        if undo_action:
            self.undo_stack.append(undo_action)  # âœ… Add to undo stack
            print(f"UNDO STACK UPDATED: {len(self.undo_stack)} actions stored.")  # ðŸ”¥ Debug print
            if len(self.undo_stack) > self.max_undo:
                self.undo_stack.pop(0)  # âœ… Limit stack size to prevent memory issues

        self.update_selection()

    def _count_neighbors(self, mask, include_diagonal=True):
        padded = np.pad(mask.astype(np.uint8), 1, mode='constant')
        count = (
            padded[:-2, 1:-1] +
            padded[2:, 1:-1] +
            padded[1:-1, :-2] +
            padded[1:-1, 2:]
        )

        if include_diagonal:
            count = (
                count +
                padded[:-2, :-2] +
                padded[:-2, 2:] +
                padded[2:, :-2] +
                padded[2:, 2:]
            )

        return count

    def _compute_blank_run_lengths(self, mask):
        rows, cols = mask.shape
        horiz = np.zeros((rows, cols), dtype=np.int32)
        vert = np.zeros((rows, cols), dtype=np.int32)

        for row in range(rows):
            col = 0
            while col < cols:
                if not mask[row, col]:
                    col += 1
                    continue
                start = col
                while col < cols and mask[row, col]:
                    col += 1
                run_len = col - start
                horiz[row, start:col] = run_len

        for col in range(cols):
            row = 0
            while row < rows:
                if not mask[row, col]:
                    row += 1
                    continue
                start = row
                while row < rows and mask[row, col]:
                    row += 1
                run_len = row - start
                vert[start:row, col] = run_len

        return horiz, vert

    def _flood_fill_component_mask(self, mask, seed_row, seed_col, include_diagonal=False):
        rows, cols = mask.shape
        connected = np.zeros_like(mask, dtype=bool)
        queue = deque()

        if not (0 <= seed_row < rows and 0 <= seed_col < cols):
            return connected
        if not mask[seed_row, seed_col]:
            return connected

        directions = [(-1, 0), (1, 0), (0, -1), (0, 1)]
        if include_diagonal:
            directions.extend([(-1, -1), (-1, 1), (1, -1), (1, 1)])

        connected[seed_row, seed_col] = True
        queue.append((seed_row, seed_col))

        while queue:
            row, col = queue.popleft()

            for d_row, d_col in directions:
                next_row = row + d_row
                next_col = col + d_col
                if (
                    0 <= next_row < rows and
                    0 <= next_col < cols and
                    mask[next_row, next_col] and
                    not connected[next_row, next_col]
                ):
                    connected[next_row, next_col] = True
                    queue.append((next_row, next_col))

        return connected

    def _flood_fill_blank_component(self, blank_mask, seed_row, seed_col):
        return self._flood_fill_component_mask(blank_mask, seed_row, seed_col, include_diagonal=False)

    def _flood_fill_touching_blank_path(self, touching_blank, filled_mask, seed_row, seed_col):
        """Flood blank boundary path with diagonal support and corner-wrap prevention."""
        rows, cols = touching_blank.shape
        connected = np.zeros_like(touching_blank, dtype=bool)
        queue = deque()

        if not (0 <= seed_row < rows and 0 <= seed_col < cols):
            return connected
        if not touching_blank[seed_row, seed_col]:
            return connected

        directions = [
            (-1, 0), (1, 0), (0, -1), (0, 1),
            (-1, -1), (-1, 1), (1, -1), (1, 1),
        ]

        connected[seed_row, seed_col] = True
        queue.append((seed_row, seed_col))

        while queue:
            row, col = queue.popleft()

            for d_row, d_col in directions:
                next_row = row + d_row
                next_col = col + d_col
                if not (0 <= next_row < rows and 0 <= next_col < cols):
                    continue
                if not touching_blank[next_row, next_col] or connected[next_row, next_col]:
                    continue

                # Diagonal allowed, but do not cut around a filled corner.
                if d_row != 0 and d_col != 0:
                    side_a = filled_mask[row, next_col]
                    side_b = filled_mask[next_row, col]
                    if side_a and side_b:
                        continue

                connected[next_row, next_col] = True
                queue.append((next_row, next_col))

        return connected

    def _expand_blank_layer_with_corner_guard(self, frontier_mask, allowed_blank_mask, filled_mask, selected_mask):
        """Expand one layer in blank space while preventing diagonal corner-wrap."""
        rows, cols = allowed_blank_mask.shape
        new_layer = np.zeros_like(allowed_blank_mask, dtype=bool)

        directions = [
            (-1, 0), (1, 0), (0, -1), (0, 1),
            (-1, -1), (-1, 1), (1, -1), (1, 1),
        ]

        for row, col in np.argwhere(frontier_mask):
            row = int(row)
            col = int(col)
            for d_row, d_col in directions:
                next_row = row + d_row
                next_col = col + d_col
                if not (0 <= next_row < rows and 0 <= next_col < cols):
                    continue
                if selected_mask[next_row, next_col]:
                    continue
                if not allowed_blank_mask[next_row, next_col]:
                    continue

                if d_row != 0 and d_col != 0:
                    side_a = filled_mask[row, next_col]
                    side_b = filled_mask[next_row, col]
                    if side_a and side_b:
                        continue

                new_layer[next_row, next_col] = True

        return new_layer

    def _compute_blank_mask(self):
        """Treat common whitespace and zero-value cells as blank."""
        if self.grid is None:
            return None
        blank_values = np.array([
            0,
            ord(' '),
            ord('\t'),
            ord('\r'),
            ord('\n'),
        ], dtype=self.grid.dtype)
        return np.isin(self.grid, blank_values)

    def arm_smart_select(
        self,
        mode="region_flood",
        min_run=5,
        adjacency_threshold=2,
        min_region_size=18,
        corona_radius=1,
        type_radius=3,
        include_adjacent_filled=False,
        replace_selection=False
    ):
        if self.grid is None or self.rows == 0 or self.cols == 0:
            messagebox.showwarning("No Map", "Load a map first.")
            return

        mode = (mode or "region_flood").lower()

        if mode == "path_corona":
            self.smart_select_pending = {
                "mode": "path_corona",
                "corona_radius": max(1, int(corona_radius)),
                "include_adjacent_filled": bool(include_adjacent_filled),
                "replace_selection": False,
            }
            include_note = " + adjacent filled" if self.smart_select_pending["include_adjacent_filled"] else ""
            self.debug_label.config(
                text=(
                    "Smart Select armed: Path Corona Blank "
                    f"(radius {self.smart_select_pending['corona_radius']}{include_note}). "
                    "Click a blank cell touching filled terrain. (adds to selection)"
                )
            )
            return

        if mode == "type_radius":
            self.smart_select_pending = {
                "mode": "type_radius",
                "type_radius": max(1, int(type_radius)),
                "replace_selection": False,
            }
            self.debug_label.config(
                text=(
                    "Smart Select armed: Similar Type Radius "
                    f"(radius {self.smart_select_pending['type_radius']}). "
                    "Click a populated cell. (adds to selection)"
                )
            )
            return

        self.smart_select_pending = {
            "mode": "region_flood",
            "min_run": max(1, int(min_run)),
            "adjacency_threshold": max(1, min(8, int(adjacency_threshold))),
            "min_region_size": max(1, int(min_region_size)),
            "replace_selection": False,
        }
        self.debug_label.config(
            text=(
                "Smart Select armed: Region Flood. "
                f"Click a blank cell (run>={self.smart_select_pending['min_run']}, "
                f"adjacency>={self.smart_select_pending['adjacency_threshold']}). "
                "(adds to selection)"
            )
        )

    def arm_smart_select_custom(self):
        if self.grid is None:
            messagebox.showwarning("No Map", "Load a map first.")
            return

        default_max = max(10, self.rows, self.cols)
        min_run = simpledialog.askinteger(
            "Smart Select",
            "Minimum blank run length:",
            initialvalue=5,
            minvalue=1,
            maxvalue=default_max
        )
        if min_run is None:
            return

        adjacency_threshold = simpledialog.askinteger(
            "Smart Select",
            "Adjacency threshold (1-8):",
            initialvalue=2,
            minvalue=1,
            maxvalue=8
        )
        if adjacency_threshold is None:
            return

        min_region_size = simpledialog.askinteger(
            "Smart Select",
            "Minimum selected cells:",
            initialvalue=18,
            minvalue=1,
            maxvalue=max(1, self.rows * self.cols)
        )
        if min_region_size is None:
            return

        self.arm_smart_select(
            mode="region_flood",
            min_run=min_run,
            adjacency_threshold=adjacency_threshold,
            min_region_size=min_region_size,
            replace_selection=False,
        )

    def arm_smart_select_path_custom(self):
        if self.grid is None:
            messagebox.showwarning("No Map", "Load a map first.")
            return

        max_radius = max(1, max(self.rows, self.cols))
        corona_radius = simpledialog.askinteger(
            "Path Corona",
            "Blank corona radius (cells):",
            initialvalue=1,
            minvalue=1,
            maxvalue=max_radius
        )
        if corona_radius is None:
            return

        self.arm_smart_select(
            mode="path_corona",
            corona_radius=corona_radius,
            replace_selection=False,
        )

    def arm_smart_select_type_radius_custom(self):
        if self.grid is None:
            messagebox.showwarning("No Map", "Load a map first.")
            return

        max_radius = max(1, max(self.rows, self.cols))
        type_radius = simpledialog.askinteger(
            "Type Radius",
            "Same-type radius (cells):",
            initialvalue=3,
            minvalue=1,
            maxvalue=max_radius
        )
        if type_radius is None:
            return

        self.arm_smart_select(
            mode="type_radius",
            type_radius=type_radius,
            replace_selection=False,
        )

    def _compute_smart_select_mask(self, seed_row, seed_col, min_run, adjacency_threshold):
        blank_mask = self._compute_blank_mask()
        if blank_mask is None:
            return None, "No grid loaded."
        if not blank_mask[seed_row, seed_col]:
            return None, "Smart Select only starts on blank cells."

        component = self._flood_fill_blank_component(blank_mask, seed_row, seed_col)
        component_size = int(np.count_nonzero(component))
        if component_size == 0:
            return None, "No blank region found at click location."

        horiz_runs, vert_runs = self._compute_blank_run_lengths(component)
        run_ok = (
            ((horiz_runs >= min_run) & (vert_runs >= 2)) |
            ((vert_runs >= min_run) & (horiz_runs >= 2))
        )
        component_neighbors = self._count_neighbors(component, include_diagonal=True)
        dense_mask = component_neighbors >= (adjacency_threshold + 1)
        core_mask = component & (run_ok | dense_mask)

        seed_is_core = bool(core_mask[seed_row, seed_col])
        if not seed_is_core:
            return None, "Clicked blank is too narrow for smart select."

        fill_mask = np.zeros_like(component, dtype=bool)
        fill_mask[seed_row, seed_col] = True

        max_iterations = max(self.rows, self.cols)
        for _ in range(max_iterations):
            neighbor_count = self._count_neighbors(fill_mask, include_diagonal=True)
            new_fill = (
                core_mask &
                (~fill_mask) &
                (neighbor_count >= 1)
            )
            if not np.any(new_fill):
                break
            fill_mask |= new_fill

        for _ in range(max_iterations):
            neighbor_count = self._count_neighbors(fill_mask, include_diagonal=True)
            new_fill = (
                component &
                (~fill_mask) &
                (neighbor_count >= adjacency_threshold)
            )
            if not np.any(new_fill):
                break
            fill_mask |= new_fill

        return fill_mask, None

    def _compute_path_corona_mask(self, seed_row, seed_col, corona_radius=1, include_adjacent_filled=False):
        blank_mask = self._compute_blank_mask()
        if blank_mask is None:
            return None, "No grid loaded."
        if not blank_mask[seed_row, seed_col]:
            return None, "Path Corona starts on a blank cell."

        filled_mask = ~blank_mask
        rows, cols = blank_mask.shape
        adjacent_filled = []
        for d_row in (-1, 0, 1):
            for d_col in (-1, 0, 1):
                if d_row == 0 and d_col == 0:
                    continue
                next_row = seed_row + d_row
                next_col = seed_col + d_col
                if (
                    0 <= next_row < rows and
                    0 <= next_col < cols and
                    filled_mask[next_row, next_col]
                ):
                    adjacent_filled.append((next_row, next_col))

        if not adjacent_filled:
            return None, "Clicked blank must touch a filled cell."

        # Anchor to contiguous filled component(s) that touch the clicked blank.
        target_filled = np.zeros_like(filled_mask, dtype=bool)
        for f_row, f_col in adjacent_filled:
            if target_filled[f_row, f_col]:
                continue
            target_filled |= self._flood_fill_component_mask(
                filled_mask,
                f_row,
                f_col,
                include_diagonal=True
            )

        target_neighbors = self._count_neighbors(target_filled, include_diagonal=True)
        target_boundary_blank = blank_mask & (target_neighbors >= 1)
        if not target_boundary_blank[seed_row, seed_col]:
            return None, "Clicked blank is not on the target component boundary."

        boundary_path = self._flood_fill_touching_blank_path(
            target_boundary_blank,
            filled_mask,
            seed_row,
            seed_col,
        )
        if not np.any(boundary_path):
            return None, "No path corona cells found at click location."

        corona_radius = max(1, int(corona_radius))
        selection_mask = boundary_path.copy()
        frontier_mask = boundary_path.copy()

        non_target_filled = filled_mask & (~target_filled)
        if np.any(non_target_filled):
            near_non_target = self._count_neighbors(non_target_filled, include_diagonal=True) >= 1
            allowed_blank = blank_mask & (~near_non_target)
            allowed_blank |= boundary_path  # Always keep the explicitly traced boundary path.
        else:
            allowed_blank = blank_mask

        for _ in range(corona_radius - 1):
            new_layer = self._expand_blank_layer_with_corner_guard(
                frontier_mask=frontier_mask,
                allowed_blank_mask=allowed_blank,
                filled_mask=filled_mask,
                selected_mask=selection_mask,
            )
            if not np.any(new_layer):
                break
            selection_mask |= new_layer
            frontier_mask = new_layer

        if include_adjacent_filled:
            touch_selection = self._count_neighbors(selection_mask, include_diagonal=True) >= 1
            adjacent_filled_mask = target_filled & touch_selection
            selection_mask |= adjacent_filled_mask

        return selection_mask, None

    def _compute_same_type_radius_mask(self, seed_row, seed_col, type_radius=3):
        if self.grid is None:
            return None, None, "No grid loaded."

        target_ord = int(self.grid[seed_row, seed_col])
        target_char = chr(target_ord)
        if target_char.isspace():
            return None, None, "Type Radius starts on a populated (non-space) cell."

        same_mask = (self.grid == target_ord)
        seed_component = self._flood_fill_component_mask(
            same_mask,
            seed_row,
            seed_col,
            include_diagonal=True
        )
        if not np.any(seed_component):
            return None, None, "No matching type component found at click location."

        type_radius = max(1, int(type_radius))
        selection_mask = seed_component.copy()
        frontier_mask = seed_component.copy()

        for _ in range(type_radius):
            neighbor_touch = self._count_neighbors(frontier_mask, include_diagonal=True) >= 1
            new_layer = same_mask & (~selection_mask) & neighbor_touch
            if not np.any(new_layer):
                break
            selection_mask |= new_layer
            frontier_mask = new_layer

        return selection_mask, target_char, None

    def smart_select_at(
        self,
        row,
        col,
        mode="region_flood",
        min_run=5,
        adjacency_threshold=2,
        min_region_size=18,
        corona_radius=1,
        type_radius=3,
        include_adjacent_filled=False,
        replace_selection=False
    ):
        if self.grid is None or self.rows == 0 or self.cols == 0:
            messagebox.showwarning("No Map", "Load a map first.")
            return

        if not (0 <= row < self.rows and 0 <= col < self.cols):
            self.debug_label.config(text="Smart Select: click inside the map bounds.")
            return

        mode = (mode or "region_flood").lower()
        min_run = max(1, int(min_run))
        adjacency_threshold = max(1, min(8, int(adjacency_threshold)))
        min_region_size = max(1, int(min_region_size))
        corona_radius = max(1, int(corona_radius))
        type_radius = max(1, int(type_radius))
        include_adjacent_filled = bool(include_adjacent_filled)
        selected_type_char = None

        if mode == "path_corona":
            fill_mask, error = self._compute_path_corona_mask(
                seed_row=row,
                seed_col=col,
                corona_radius=corona_radius,
                include_adjacent_filled=include_adjacent_filled,
            )
        elif mode == "type_radius":
            fill_mask, selected_type_char, error = self._compute_same_type_radius_mask(
                seed_row=row,
                seed_col=col,
                type_radius=type_radius,
            )
        else:
            fill_mask, error = self._compute_smart_select_mask(
                seed_row=row,
                seed_col=col,
                min_run=min_run,
                adjacency_threshold=adjacency_threshold,
            )
        if fill_mask is None:
            self.debug_label.config(text=f"Smart Select: {error}")
            print(f"Smart Select rejected at ({row}, {col}): {error}")
            return

        selected_count = int(np.count_nonzero(fill_mask))
        if mode == "region_flood" and selected_count < min_region_size:
            self.debug_label.config(
                text=f"Smart Select canceled: region too small ({selected_count} < {min_region_size})."
            )
            print(
                f"Smart Select canceled at ({row}, {col}): selected={selected_count}, min_required={min_region_size}"
            )
            return

        selected_cells = {(int(r), int(c)) for r, c in np.argwhere(fill_mask)}
        self.selected_cells.update(selected_cells)

        self.canvas.delete('selection')
        self.update_selection()
        if mode == "path_corona":
            include_note = " + adjacent filled" if include_adjacent_filled else ""
            self.debug_label.config(
                text=(
                    "Smart Select Path Corona complete: "
                    f"{selected_count} cells (radius {corona_radius}{include_note})."
                )
            )
            print(
                f"Smart Select Path Corona complete at ({row}, {col}): selected={selected_count}, "
                f"radius={corona_radius}, include_adjacent_filled={include_adjacent_filled}, append=True"
            )
        elif mode == "type_radius":
            self.debug_label.config(
                text=(
                    f"Smart Select Type Radius complete: {selected_count} '{selected_type_char}' cells "
                    f"(radius {type_radius})."
                )
            )
            print(
                f"Smart Select Type Radius complete at ({row}, {col}): selected={selected_count}, "
                f"char='{selected_type_char}', radius={type_radius}, append=True"
            )
        else:
            self.debug_label.config(
                text=(
                    f"Smart Select Region Flood complete: {selected_count} blank cells selected "
                    f"(run>={min_run}, adjacency>={adjacency_threshold})."
                )
            )
            print(
                f"Smart Select Region Flood complete at ({row}, {col}): selected={selected_count}, "
                f"run>={min_run}, adjacency>={adjacency_threshold}, append=True"
            )

    def get_rectangular_selection(self):
        if not (self.rect_start and self.rect_end):
            return set()
        start_row, start_col = self.rect_start
        end_row, end_col = self.rect_end
        return {(row, col) 
                for row in range(min(start_row, end_row), max(start_row, end_row) + 1)
                for col in range(min(start_col, end_col), max(start_col, end_col) + 1)}
    
    def on_randomness_change(self, value):
        # No additional processing needed as the value is directly stored in self.randomness
        pass

    def on_extra_spaces_change(self, value):
        # No additional processing needed as the value is directly stored in self.extra_spaces
        pass

    def apply_extra_spaces_to_char(self, char):
        """Apply per-cell chance to convert inserted output into spaces."""
        if char == ' ':
            return char
        chance = max(0.0, min(1.0, self.extra_spaces.get() / 100.0))
        if chance <= 0.0:
            return char
        return ' ' if random.random() < chance else char

    def _generate_random_fork_region_mask(self, width, height):
        """Build multiple fork-friendly dry patches instead of one merged blob."""
        region_mask = np.zeros((height, width), dtype=bool)
        area = width * height
        if area <= 0:
            return region_mask

        patch_count = max(6, min(260, int(area * 0.0038)))
        min_r = max(3, int(min(width, height) * 0.06))
        max_r = max(min_r + 2, int(min(width, height) * 0.16))

        yy, xx = np.indices((height, width))

        for _ in range(patch_count):
            cx = random.randint(0, width - 1)
            cy = random.randint(0, height - 1)
            rx = random.randint(min_r, max_r)
            ry = random.randint(min_r, max_r)
            patch = (((xx - cx) / max(1, rx)) ** 2 + ((yy - cy) / max(1, ry)) ** 2) <= 1.0
            # Ragged patch edge so regions are natural and not perfect circles.
            if random.random() < 0.7:
                jitter = np.random.random((height, width)) > 0.14
                patch &= jitter
            region_mask |= patch

        # Light cleanup: keep coherent patch interiors, avoid tiny speckles.
        mask_i = region_mask.astype(np.uint8)
        p = np.pad(mask_i, 1, mode='edge')
        neighbors = (
            p[:-2, :-2] + p[:-2, 1:-1] + p[:-2, 2:] +
            p[1:-1, :-2] + p[1:-1, 1:-1] + p[1:-1, 2:] +
            p[2:, :-2] + p[2:, 1:-1] + p[2:, 2:]
        )
        region_mask = neighbors >= 3

        return region_mask

    def _generate_random_forks_crack_mask(self, width, height, region_mask=None):
        """Generate many thin, longer fork paths with less blob-like spread."""
        crack_mask = np.zeros((height, width), dtype=bool)
        area = width * height
        if area <= 0:
            return crack_mask

        if region_mask is not None:
            region_mask = np.asarray(region_mask, dtype=bool)
            if region_mask.shape != (height, width) or not region_mask.any():
                region_mask = None

        if region_mask is not None:
            allowed_points = np.argwhere(region_mask)
        else:
            allowed_points = np.argwhere(np.ones((height, width), dtype=bool))

        if allowed_points.size == 0:
            return crack_mask

        start_count = max(12, min(420, int(area * 0.0105)))
        min_len = max(10, int(min(width, height) * 0.28))
        max_len = max(min_len + 8, int(min(width, height) * 0.72))
        max_carved = min(max(120, int(area * 0.23)), 90000)
        carved = 0

        directions = [
            (-1, -1), (-1, 0), (-1, 1),
            (0, -1),           (0, 1),
            (1, -1),  (1, 0),  (1, 1),
        ]

        starts = []
        for _ in range(start_count * 3):
            if len(starts) >= start_count:
                break
            ay, ax = allowed_points[random.randrange(len(allowed_points))]
            y = int(ay)
            x = int(ax)
            y0 = max(0, y - 2)
            y1 = min(height, y + 3)
            x0 = max(0, x - 2)
            x1 = min(width, x + 3)
            if np.any(crack_mask[y0:y1, x0:x1]):
                continue
            starts.append((x, y))

        branches = []
        for x, y in starts:
            dx, dy = random.choice(directions)
            branches.append([x, y, dx, dy, random.randint(min_len, max_len)])

        while branches and carved < max_carved:
            x, y, dx, dy, steps = branches.pop()
            for step_idx in range(steps):
                if not (0 <= x < width and 0 <= y < height):
                    break
                if region_mask is not None and not region_mask[y, x]:
                    break

                if not crack_mask[y, x]:
                    crack_mask[y, x] = True
                    carved += 1
                    if carved >= max_carved:
                        break

                remain = steps - step_idx
                if remain > 8 and random.random() < 0.18:
                    ndx, ndy = random.choice(directions)
                    child_len = max(6, int(remain * random.uniform(0.42, 0.75)))
                    branches.append([x, y, ndx, ndy, child_len])

                if random.random() < 0.22:
                    ndx, ndy = random.choice(directions)
                    if (ndx, ndy) != (0, 0):
                        dx, dy = ndx, ndy

                x += dx
                y += dy

                if random.random() < 0.08:
                    x += random.choice([-1, 0, 1])
                    y += random.choice([-1, 0, 1])

        return crack_mask

    def _generate_dry_crack_mask(
        self,
        width,
        height,
        mode="random",
        allowed_mask=None,
        density_scale=1.0,
        length_scale=1.0,
        carve_scale=1.0
    ):
        """Create branching crack paths for dry terrain."""
        crack_mask = np.zeros((height, width), dtype=bool)
        area = width * height
        if area <= 0:
            return crack_mask

        if allowed_mask is not None:
            allowed_mask = np.asarray(allowed_mask, dtype=bool)
            if allowed_mask.shape != (height, width):
                allowed_mask = None
            elif not allowed_mask.any():
                return crack_mask

        if allowed_mask is not None and mode in ("radiate", "converge"):
            # Allowed-region carving is path-based random mode only.
            mode = "random"

        if mode in ("radiate", "converge"):
            center_x = (width - 1) / 2.0
            center_y = (height - 1) / 2.0
            start_count = max(8, min(320, int(math.sqrt(area) * 0.42)))
            min_len = min(max(12, int(min(width, height) * 0.5)), 120)
            max_len = max(min_len, min(max(min_len + 10, int((width + height) * 0.55)), 210))
            max_carved = min(max(40, int(area * 0.085)), 38000)
            carved = 0

            branches = []
            for _ in range(start_count):
                angle = random.uniform(0, 2 * math.pi)
                if mode == "radiate":
                    start_radius = random.uniform(0, max(2.0, min(width, height) * 0.12))
                    x = center_x + math.cos(angle) * start_radius
                    y = center_y + math.sin(angle) * start_radius
                    heading = angle + random.uniform(-0.25, 0.25)
                else:
                    edge_radius = max(width, height)
                    x = center_x + math.cos(angle) * edge_radius
                    y = center_y + math.sin(angle) * edge_radius
                    x = max(0.0, min(width - 1.0, x))
                    y = max(0.0, min(height - 1.0, y))
                    heading = math.atan2(center_y - y, center_x - x) + random.uniform(-0.22, 0.22)

                length = random.randint(min_len, max_len)
                branches.append([x, y, heading, length])

            while branches and carved < max_carved:
                x, y, heading, steps = branches.pop()
                for _ in range(steps):
                    ix = int(round(x))
                    iy = int(round(y))
                    if not (0 <= ix < width and 0 <= iy < height):
                        break

                    if not crack_mask[iy, ix]:
                        crack_mask[iy, ix] = True
                        carved += 1
                        if carved >= max_carved:
                            break

                    if random.random() < 0.18:
                        side_angle = heading + random.choice([math.pi / 2, -math.pi / 2])
                        sx = int(round(x + math.cos(side_angle)))
                        sy = int(round(y + math.sin(side_angle)))
                        if 0 <= sx < width and 0 <= sy < height and not crack_mask[sy, sx]:
                            crack_mask[sy, sx] = True
                            carved += 1
                            if carved >= max_carved:
                                break

                    if random.random() < 0.14 and steps > 10:
                        branch_heading = heading + random.uniform(-0.8, 0.8)
                        branch_len = max(8, (steps // 2) + random.randint(-3, 4))
                        branches.append([x, y, branch_heading, branch_len])

                    if mode == "radiate":
                        target_heading = math.atan2(y - center_y, x - center_x)
                    else:
                        target_heading = math.atan2(center_y - y, center_x - x)
                    heading = (0.78 * heading) + (0.22 * target_heading) + random.uniform(-0.12, 0.12)

                    x += math.cos(heading)
                    y += math.sin(heading)

                    if random.random() < 0.14:
                        x += random.uniform(-0.55, 0.55)
                        y += random.uniform(-0.55, 0.55)

            return crack_mask

        start_count = max(3, min(420, int(area * 0.0013 * max(0.25, density_scale))))
        min_len = min(max(8, int(min(width, height) * 0.45 * max(0.6, length_scale))), 110)
        max_len = max(
            min_len,
            min(
                max(min_len + 8, int((width + height) * 0.5 * max(0.6, length_scale))),
                220
            )
        )
        directions = [(1, 0), (-1, 0), (0, 1), (0, -1)]

        allowed_points = None
        if allowed_mask is not None:
            allowed_points = np.argwhere(allowed_mask)
            if allowed_points.size == 0:
                return crack_mask

        branches = []
        for _ in range(start_count):
            if allowed_points is not None:
                ay, ax = allowed_points[random.randrange(len(allowed_points))]
                x = int(ax)
                y = int(ay)
            else:
                x = random.randint(0, width - 1)
                y = random.randint(0, height - 1)
            dx, dy = random.choice(directions)
            length = random.randint(min_len, max_len)
            branches.append([x, y, dx, dy, length])

        max_carved = min(max(24, int(area * 0.055 * max(0.25, carve_scale))), 52000)
        carved = 0

        while branches and carved < max_carved:
            x, y, dx, dy, steps = branches.pop()
            for _ in range(steps):
                if not (0 <= x < width and 0 <= y < height):
                    break
                if allowed_mask is not None and (not allowed_mask[y, x]):
                    break

                if not crack_mask[y, x]:
                    crack_mask[y, x] = True
                    carved += 1
                    if carved >= max_carved:
                        break

                if random.random() < 0.18:
                    sx, sy = x + dy, y + dx
                    if (
                        0 <= sx < width and 0 <= sy < height and
                        (allowed_mask is None or allowed_mask[sy, sx]) and
                        not crack_mask[sy, sx]
                    ):
                        crack_mask[sy, sx] = True
                        carved += 1
                        if carved >= max_carved:
                            break

                if random.random() < 0.16 and steps > 6:
                    ndx, ndy = random.choice([(-dy, dx), (dy, -dx), (dx, dy)])
                    next_len = max(6, (steps // 2) + random.randint(-3, 3))
                    branches.append([x, y, ndx, ndy, next_len])

                if random.random() < 0.25:
                    dx, dy = random.choice([(dx, dy), (-dy, dx), (dy, -dx)])

                x += dx
                y += dy
                if allowed_mask is not None and (0 <= x < width and 0 <= y < height):
                    if not allowed_mask[y, x]:
                        break

                if random.random() < 0.2:
                    nx = x + random.choice([-1, 0, 1])
                    ny = y + random.choice([-1, 0, 1])
                    if 0 <= nx < width and 0 <= ny < height:
                        if allowed_mask is None or allowed_mask[ny, nx]:
                            x, y = nx, ny

        return crack_mask

    def generate_biome(self, biome_type, shape_type):
        if not self.selected_cells:
            messagebox.showwarning("No Selection", "Please select an area first.")
            return

        if biome_type not in BIOME_PROFILES or shape_type not in SHAPE_GENERATORS:
            messagebox.showerror("Error", f"Invalid biome ({biome_type}) or shape ({shape_type})")
            return

        selected_cells = tuple(self.selected_cells)
        selected_rows = [row for row, _ in selected_cells]
        selected_cols = [col for _, col in selected_cells]

        min_row = min(selected_rows)
        max_row = max(selected_rows)
        min_col = min(selected_cols)
        max_col = max(selected_cols)

        width = max_col - min_col + 1
        height = max_row - min_row + 1
        randomness = self.randomness.get() / 100.0
        extra_space_chance = max(0.0, min(1.0, self.extra_spaces.get() / 100.0))

        shape_mask = SHAPE_GENERATORS[shape_type](width, height)

        crack_mask = None
        fork_region_mask = None
        if biome_type == "dry_sand":
            crack_mode = "random"
            if shape_type == "explosion":
                crack_mode = "radiate"
            elif shape_type == "implosion":
                crack_mode = "converge"
            if shape_type == "random_forks":
                fork_region_mask = self._generate_random_fork_region_mask(width, height)
                crack_mask = self._generate_random_forks_crack_mask(
                    width,
                    height,
                    region_mask=fork_region_mask
                )
            else:
                crack_mask = self._generate_dry_crack_mask(width, height, mode=crack_mode)

        undo_action = []
        visible_changes = []
        rand = random.random
        choice = random.choice

        for row, col in selected_cells:
            local_row = row - min_row
            local_col = col - min_col
            mask_value = float(shape_mask[local_row][local_col])

            if biome_type == "forest":
                if mask_value < 0.2:
                    base_char = '.'
                    adjacent_chars = ['.', 'f']
                elif mask_value < 0.5:
                    base_char = 'f'
                    adjacent_chars = ['.', 'f', 'F']
                else:
                    base_char = 'F'
                    adjacent_chars = ['f', 'F']

            elif biome_type == "grasslands":
                if mask_value < 0.68:
                    base_char = '.'
                    adjacent_chars = ['.', '.', '.', '.', ',', ',']
                else:
                    base_char = ','
                    adjacent_chars = ['.', '.', ',', ',', ',']

                tree_chance = 0.012 + max(0.0, mask_value - 0.75) * 0.03
                if rand() < min(0.04, tree_chance):
                    base_char = 'f'
                    adjacent_chars = ['.', ',', 'f']

            elif biome_type == "swamp":
                if mask_value < 0.2:
                    base_char = 'W'
                    adjacent_chars = ['W', 'w']
                elif mask_value < 0.5:
                    base_char = 'w'
                    adjacent_chars = ['W', 'w', '.']
                elif mask_value < 1.0:
                    base_char = '.'
                    adjacent_chars = ['w', '.', 'f']
                else:
                    base_char = '.'
                    adjacent_chars = ['.', 'f']

            elif biome_type == "sand":
                if mask_value < 0.2:
                    base_char = ','
                    adjacent_chars = [',', '`']
                elif mask_value < 0.5:
                    base_char = 'z'
                    adjacent_chars = [',', 'z']
                elif mask_value < 0.8:
                    base_char = 'd'
                    adjacent_chars = ['z', 'd']
                else:
                    base_char = 'D'
                    adjacent_chars = ['d', 'D']

            elif biome_type == "dry_sand":
                if shape_type == "random_forks":
                    in_fork_region = fork_region_mask[local_row, local_col] if fork_region_mask is not None else False
                    if in_fork_region:
                        if mask_value < 0.44:
                            base_char = '.'
                            adjacent_chars = ['.', '.', ',', ',']
                        elif mask_value < 0.82:
                            base_char = ','
                            adjacent_chars = ['.', ',', ',', ' ']
                        else:
                            base_char = ' '
                            adjacent_chars = [' ', '.', ',']
                    elif mask_value < 0.32:
                        base_char = ' '
                        adjacent_chars = [' ', ' ', '.', ',']
                    elif mask_value < 0.72:
                        base_char = '.'
                        adjacent_chars = [' ', '.', '.', ',']
                    else:
                        base_char = ','
                        adjacent_chars = [' ', '.', ',', ',']
                elif mask_value < 0.3:
                    base_char = ' '
                    adjacent_chars = [' ', '.', ',']
                elif mask_value < 0.6:
                    base_char = '.'
                    adjacent_chars = [' ', '.', ',']
                elif mask_value < 0.9:
                    base_char = ','
                    adjacent_chars = [' ', '.', ',', 'd']
                else:
                    base_char = ' '
                    adjacent_chars = [' ', '.', ',']

            else:
                base_char = '.'
                adjacent_chars = ['.']

            new_char = choice(adjacent_chars) if rand() < randomness else base_char

            if biome_type == "dry_sand":
                if crack_mask[local_row, local_col]:
                    new_char = 'd' if rand() < 0.82 else 'D'
                elif new_char == ' ' and rand() < (0.06 + randomness * 0.25):
                    new_char = choice(['.', ','])

            if new_char != ' ' and extra_space_chance > 0.0 and rand() < extra_space_chance:
                new_char = ' '

            old_char = chr(self.grid[row, col])
            if old_char != new_char:
                undo_action.append((row, col, old_char))
                self.grid[row, col] = ord(new_char)
                if (row, col) in self.previous_visible_range:
                    visible_changes.append((row, col))

        if undo_action:
            self.undo_stack.append(undo_action)
            if len(self.undo_stack) > self.max_undo:
                self.undo_stack.pop(0)

        if visible_changes:
            if len(visible_changes) > 2000:
                self._redraw_visible_cells_force_complete()
            else:
                for row, col in visible_changes:
                    char = chr(self.grid[row, col])
                    color = self.get_char_color(char)
                    self.update_canvas_object(row, col, char, color)

        self.update_selection()


    def create_explosion_landscape(self, width, height, layers, is_explosion=True):
        if is_explosion:
            layers = ['.'] + layers + ['.']  # 5 layers for explosion: ['.', '.', 'f', 'F', '.']
            percentages = self.explosion_percentages
        else:
            layers = ['F', 'f', '.', '.']  # 4 layers for implosion: ['F', 'f', '.', '.']
            percentages = self.implosion_percentages
        
        # Create the layered landscape
        landscape = [[layers[-1] for _ in range(width)] for _ in range(height)]
        
        # Create thresholds based on percentages
        thresholds = [sum(percentages[:i+1]) / 100 for i in range(len(percentages))]

        # Generate random parameters for this specific forest
        random_params = {
            'crescent_angle': random.uniform(0, 2*math.pi),
            'irregular_seed': random.randint(0, 1000),
            'patchy_seed': random.randint(0, 1000),
        }

        for y in range(height):
            for x in range(width):
                distance = self.get_shape_distance(x, y, width, height, self.forest_shape, random_params, is_explosion)
                
                # Determine the appropriate layer based on distance
                for i, threshold in enumerate(thresholds):
                    if distance <= threshold:
                        landscape[y][x] = layers[i]
                        break

        # Apply randomness to '.' spaces
        randomness_value = self.randomness.get() / 100
        for y in range(height):
            for x in range(width):
                if landscape[y][x] == '.':
                    if random.random() < randomness_value:
                        landscape[y][x] = random.choice(['f', 'F'])

        return landscape
    
    def enter_performance_mode(self):
        """Modified performance mode that doesn't completely disable visuals."""
        print("ðŸš€ ENTERING PERFORMANCE MODE")
        
        # **âœ… REDUCE EXPENSIVE FEATURES BUT KEEP BASIC VISUALS**
        self._performance_mode = True
        
        # **âœ… DON'T CLEAR SELECTION VISUALS - KEEP PAINTING RESPONSIVE**
        # Just mark that we're in performance mode for other optimizations
        
        self.debug_label.config(text="Performance Mode: Large selection - optimized rendering")

    def exit_performance_mode(self):
        """Exit performance mode and restore normal operation."""
        print("ðŸ EXITING PERFORMANCE MODE")
        
        self._performance_mode = False
        
        # **âœ… ENSURE SELECTION IS PROPERLY VISIBLE**
        if hasattr(self, 'selected_cells') and self.selected_cells:
            # Only update selection if not actively painting
            if not (hasattr(self, '_currently_painting') and self._currently_painting):
                self.update_selection()
        
        self.debug_label.config(text="Normal Mode: Performance mode disabled")

    def get_shape_distance(self, x, y, width, height, shape, random_params, is_explosion):
        center_x, center_y = width / 2, height / 2
        normalized_x = (x - center_x) / (width / 2)
        normalized_y = (y - center_y) / (height / 2)
        
        base_distance = math.sqrt(normalized_x**2 + normalized_y**2)
        
        if shape == "ellipse":
            distance = base_distance
        elif shape == "crescent":
            angle = math.atan2(normalized_y, normalized_x) - random_params['crescent_angle']
            # Create a C-shape
            angle_factor = (math.cos(angle) + 1) / 2  # 0 to 1, with 1 at the opening of the C
            if angle_factor > 0.5:  # This is the opening of the C
                distance = 0 if is_explosion else 1  # Layer 1 for explosion, Layer 4 for implosion
            else:
                distance = base_distance
        elif shape == "irregular":
            angle = math.atan2(normalized_y, normalized_x)
            irregularity = 0.2 * math.sin(5 * angle + random_params['irregular_seed']) + \
                           0.1 * math.sin(7 * angle + random_params['irregular_seed'])
            distance = base_distance + irregularity
        elif shape == "patchy":
            patchy_factor = 0.3 * (math.sin(8*normalized_x + random_params['patchy_seed']) * 
                                   math.sin(8*normalized_y + random_params['patchy_seed']))
            distance = base_distance + patchy_factor
        else:
            distance = base_distance  # Default to ellipse

        # Add some randomness
        randomness = random.uniform(-0.05, 0.05)
        distance = max(0, min(1, distance + randomness))
        
        return distance
    
    def thin_out_forest(self, mode="thin"):
        """Randomly thin out selected forest cells (f/F â†’ . or space)."""
        if not self.selected_cells:
            messagebox.showwarning("No Selection", "Please select an area first.")
            return

        # Adjustable thinning probabilities
        if mode == "thin":
            chance_to_thin = 0.25   # 25% of selected forest cells
            dot_vs_space = 0.7      # 70% -> '.', 30% -> ' '
        elif mode == "heavy":
            chance_to_thin = 0.45   # 45% of selected forest cells
            dot_vs_space = 0.3      # 40% '.' vs 60% space
        else:
            return

        undo_action = []
        for row, col in self.selected_cells:
            if 0 <= row < self.rows and 0 <= col < self.cols:
                current_char = chr(self.grid[row, col])
                if current_char in ('f', 'F', '.'):   
                    if random.random() < chance_to_thin:
                        new_char = '.' if random.random() < dot_vs_space else ' '
                        if current_char != new_char:
                            undo_action.append((row, col, current_char))
                            self.grid[row, col] = ord(new_char)
                            self.redraw_cell(row, col)

        if undo_action:
            self.undo_stack.append(undo_action)
            if len(self.undo_stack) > self.max_undo:
                self.undo_stack.pop(0)

        self.update_selection()
        print(f"ðŸŒ² Forest thinned with mode={mode}, changes={len(undo_action)}")

BIOME_PROFILES = {
    "forest": {
        "layers": ['.', 'f', 'F'],
        "probabilities": [70, 25, 5],  # Mostly grass, some trees, rare dense trees
        "shapes": ["crescent", "irregular", "patchy", "spotty", "explosion", "implosion"],
    },
    "grasslands": {
        "layers": [' ', '.', ',', 'f'],
        "probabilities": [6, 80, 13, 1],  # Mostly '.', some ',', very rare 'f'
        "shapes": ["crescent", "irregular", "patchy", "spotty", "explosion", "implosion"],
    },
    "swamp": {
        "layers": ['.', 'w', 'W', '.'],  # Muddy land, shallow water, deep water, sparse trees
        "probabilities": [30, 40, 20, 10],  # Mostly shallow water, some deep water, scattered land
        "shapes": ["swamp_meandering", "swamp_irregular", "swamp_patchy"], 
    },
    "sand": {
        "layers": [',', 'z', 'd', 'D'],  # Light sand â†’ Small dunes â†’ Tall dunes â†’ Sand plateaus
        "probabilities": [60, 20, 15, 5],  # Mostly light sand, fewer dunes
        "shapes": ["dune_horizontal", "dune_vertical", "patchy", "explosion", "implosion"],
    },
    "dry_sand": {
        "layers": [' ', '.', ',', 'd', 'D'],
        "probabilities": [45, 28, 19, 6, 2],  # Sparse dry ground with occasional darker crack chars
        "shapes": ["patchy", "irregular", "spotty", "random_forks", "explosion", "implosion"],
    },
}


def generate_spotty_shape(width, height):
    """Creates a mostly empty shape with small scattered clusters."""
    shape_mask = [[1 for _ in range(width)] for _ in range(height)]

    for y in range(height):
        for x in range(width):
            if random.random() < 0.05:  # 5% chance of a small patch
                shape_mask[y][x] = random.uniform(0, 0.3)  # Dense clusters (low values)

            elif random.random() < 0.1:  # 10% chance of scattered objects
                shape_mask[y][x] = random.uniform(0.3, 0.6)  # Medium density

    return shape_mask

def generate_random_forks_shape(width, height):
    """Dry-sand base mask tuned for region-based random fork overlays."""
    shape_mask = np.random.choice(
        np.array([0.22, 0.5, 0.76, 0.95], dtype=np.float32),
        size=(height, width),
        p=[0.24, 0.42, 0.24, 0.10]
    ).astype(np.float32)

    # Light smoothing keeps the background natural but still noisy.
    p = np.pad(shape_mask, 1, mode='edge')
    shape_mask = (
        p[:-2, :-2] + p[:-2, 1:-1] + p[:-2, 2:] +
        p[1:-1, :-2] + p[1:-1, 1:-1] + p[1:-1, 2:] +
        p[2:, :-2] + p[2:, 1:-1] + p[2:, 2:]
    ) / 9.0

    return shape_mask

def generate_patchy_shape(width, height):
    """Creates patchy terrain with randomly shaped clusters."""
    shape_mask = np.ones((height, width), dtype=np.float32)
    area = width * height
    if area <= 0:
        return shape_mask

    # Cap patch count to prevent long stalls on very large selections.
    patch_count = int(area * 0.06)
    patch_count = max(80, min(14000, patch_count))

    for _ in range(patch_count):
        patch_x = random.randint(0, width - 1)
        patch_y = random.randint(0, height - 1)
        shape_mask[patch_y, patch_x] = min(shape_mask[patch_y, patch_x], random.uniform(0, 0.3))

        spread_steps = random.randint(2, 5)
        for _ in range(spread_steps):
            dx, dy = random.randint(-2, 2), random.randint(-2, 2)
            nx, ny = patch_x + dx, patch_y + dy
            if 0 <= nx < width and 0 <= ny < height:
                shape_mask[ny, nx] = min(shape_mask[ny, nx], 0.5)

    return shape_mask



def generate_ellipse_shape_explosion(width, height):
    """Creates an explosion effect with numeric shape values (0 = center, 1 = edges)."""
    shape_mask = [[1 for _ in range(width)] for _ in range(height)]
    center_x, center_y = width / 2, height / 2

    for y in range(height):
        for x in range(width):
            norm_x = (x - center_x) / (width / 2)
            norm_y = (y - center_y) / (height / 2)
            distance = math.sqrt(norm_x**2 + norm_y**2)

            shape_mask[y][x] = min(1, distance)  # Numeric value from 0 (center) to 1 (edge)

    return shape_mask

def generate_ellipse_shape_implosion(width, height):
    """Generates an implosion-like ellipse shape with numeric values (1=center, 0=edge)."""
    shape_mask = [[1 for _ in range(width)] for _ in range(height)]
    center_x, center_y = width / 2, height / 2

    for y in range(height):
        for x in range(width):
            norm_x = (x - center_x) / (width / 2)
            norm_y = (y - center_y) / (height / 2)
            distance = math.sqrt(norm_x**2 + norm_y**2)

            # **ðŸš€ Inverted Scaling**
            shape_mask[y][x] = max(0, 1 - distance)  # Now 1 at center, 0 at edges (Implosion)
    
    return shape_mask


def generate_crescent_shape(width, height):
    shape_mask = [[1 for _ in range(width)] for _ in range(height)]
    center_x, center_y = width / 2, height / 2
    crescent_angle = random.uniform(0, 2 * math.pi)

    for y in range(height):
        for x in range(width):
            norm_x = (x - center_x) / (width / 2)
            norm_y = (y - center_y) / (height / 2)
            angle = math.atan2(norm_y, norm_x) - crescent_angle
            distance = math.sqrt(norm_x**2 + norm_y**2)
            angle_factor = (math.cos(angle) + 1) / 2  # 1 at open part, 0 at curve

            # Crescent effect: Keep one side more open
            if angle_factor > 0.5:
                shape_mask[y][x] = 1  # Empty space
            else:
                shape_mask[y][x] = max(0, distance * 0.8)  # ðŸ”¥ Scale down

    return shape_mask



def generate_irregular_shape(width, height):
    """Returns a shape with irregular noise patterns."""
    shape_mask = np.random.uniform(0.5, 1.0, (height, width)).astype(np.float32)
    area = width * height

    # Adaptive smoothing count to keep large regions responsive.
    if area <= 50000:
        iterations = 8
    elif area <= 200000:
        iterations = 5
    else:
        iterations = 3

    for _ in range(iterations):
        p = np.pad(shape_mask, 1, mode='edge')
        shape_mask = (
            p[:-2, :-2] + p[:-2, 1:-1] + p[:-2, 2:] +
            p[1:-1, :-2] + p[1:-1, 1:-1] + p[1:-1, 2:] +
            p[2:, :-2] + p[2:, 1:-1] + p[2:, 2:]
        ) / 9.0

    return shape_mask
def generate_meandering_shape(width, height):
    shape_mask = [[random.uniform(0.5, 1) for _ in range(width)] for _ in range(height)]

    for y in range(1, height - 1):
        for x in range(1, width - 1):
            if random.random() < 0.2:
                shape_mask[y][x] = 0.2  # Some areas are lowlands (potential water)
            elif random.random() < 0.1:
                shape_mask[y][x] = 0  # Rare deeper water pockets

    return shape_mask

def generate_dune_horizontal_shape(width, height):
    """Creates horizontal sand dunes using sine waves."""
    shape_mask = [[1 for _ in range(width)] for _ in range(height)]
    
    for y in range(height):
        for x in range(width):
            shape_mask[y][x] = 0.5 + 0.4 * math.sin((x / width) * math.pi * 4)  # 4 dune ridges across width

    return shape_mask

def generate_dune_vertical_shape(width, height):
    """Creates vertical sand dunes using sine waves."""
    shape_mask = [[1 for _ in range(width)] for _ in range(height)]
    
    for y in range(height):
        for x in range(width):
            shape_mask[y][x] = 0.5 + 0.4 * math.sin((y / height) * math.pi * 4)  # 4 dune ridges across height

    return shape_mask


def generate_swamp_meandering_shape(width, height):
    """Creates winding swamp rivers with numeric values (0=deep water, 1=dry land)."""
    shape_mask = [[1 for _ in range(width)] for _ in range(height)]  # Default dry land (1)

    num_rivers = random.randint(1, 3)  # 1-3 winding rivers
    for _ in range(num_rivers):
        x, y = random.randint(0, width - 1), random.randint(0, height - 1)
        for _ in range(width * 2):  # Number of steps for path
            shape_mask[y][x] = 0  # Deep water (0)
            if random.random() < 0.5:
                x += random.choice([-1, 1])
            else:
                y += random.choice([-1, 1])
            x = max(0, min(width - 1, x))
            y = max(0, min(height - 1, y))

    # Expand deep water outward into shallow water (0.3)
    for y in range(height):
        for x in range(width):
            if shape_mask[y][x] == 0:  # If deep water
                for dy in [-1, 0, 1]:
                    for dx in [-1, 0, 1]:
                        ny, nx = y + dy, x + dx
                        if 0 <= ny < height and 0 <= nx < width and shape_mask[ny][nx] == 1:
                            shape_mask[ny][nx] = 0.3  # Shallow water

    return shape_mask

def generate_swamp_patchy_shape(width, height):
    """Creates a swampy area with deep water (W), shallow water (w), small patches of land (.), and sparse trees (f)."""
    shape_mask = [[0 for _ in range(width)] for _ in range(height)]  # Start with deep water (0)

    num_land_patches = int((width * height) * 0.07)  # 7% of the area will be land patches

    for _ in range(num_land_patches):
        # Choose a random small land patch center
        px, py = random.randint(2, width - 3), random.randint(2, height - 3)

        # Land patch radius (keep small for scattered effect)
        radius = random.randint(1, 2)

        for y in range(height):
            for x in range(width):
                dist = math.sqrt((x - px) ** 2 + (y - py) ** 2)
                if dist < radius:
                    shape_mask[y][x] = 1  # Land (1)

    # Convert deep water near land into shallow water (w)
    for y in range(height):
        for x in range(width):
            if shape_mask[y][x] == 1:  # If it's land
                for dy in [-1, 0, 1]:
                    for dx in [-1, 0, 1]:
                        ny, nx = y + dy, x + dx
                        if 0 <= ny < height and 0 <= nx < width and shape_mask[ny][nx] == 0:
                            shape_mask[ny][nx] = 0.3  # Convert deep water to shallow water

    # Ensure deep water remains farthest from land
    for y in range(height):
        for x in range(width):
            if shape_mask[y][x] == 0:  # Deep water
                near_land = any(
                    0.3 <= shape_mask[y + dy][x + dx] <= 1
                    for dy in [-2, -1, 0, 1, 2]
                    for dx in [-2, -1, 0, 1, 2]
                    if 0 <= y + dy < height and 0 <= x + dx < width
                )
                if not near_land:
                    shape_mask[y][x] = 0  # Ensure deep water stays deep

    # Scatter sparse trees (f) on land, ensuring they remain separate
    for y in range(height):
        for x in range(width):
            if shape_mask[y][x] == 1 and random.random() < 0.05:  # 5% chance for trees
                shape_mask[y][x] = 1.1  # Tree-covered land

    return shape_mask

def generate_swamp_irregular_shape(width, height):
    """Creates a noise-based swamp terrain with numeric values (0=deep water, 1=dry land)."""
    shape_mask = [[1 for _ in range(width)] for _ in range(height)]  # Start with dry land

    for y in range(height):
        for x in range(width):
            noise_value = random.uniform(0, 1)  # Noise-based randomness

            if noise_value < 0.4:
                shape_mask[y][x] = 0  # Deep water
            elif noise_value < 0.6:
                shape_mask[y][x] = 0.3  # Shallow water
            elif noise_value < 0.8:
                shape_mask[y][x] = 0.7  # Muddy land
            else:
                shape_mask[y][x] = 1  # Sparse trees

    return shape_mask


# Register available shapes
SHAPE_GENERATORS = {
    "explosion": generate_ellipse_shape_explosion, 
    "implosion": generate_ellipse_shape_implosion, 
    "crescent": generate_crescent_shape,
    "irregular": generate_irregular_shape,
    "patchy": generate_patchy_shape,
    "spotty": generate_spotty_shape,
    "random_forks": generate_random_forks_shape,
    "meandering": generate_meandering_shape,

    # **New Sand Patterns**
    "dune_horizontal": generate_dune_horizontal_shape,
    "dune_vertical": generate_dune_vertical_shape,

    "swamp_irregular": generate_swamp_irregular_shape,
    "swamp_patchy": generate_swamp_patchy_shape,
    "swamp_meandering": generate_swamp_meandering_shape,    
}

def main():
    root = tk.Tk()
    root.title("MUD Map Editor")
    root.geometry("800x600")  # Set an initial window size
    editor = TextGridEditor(root)
    print("Main window created")
    root.mainloop()

if __name__ == "__main__":
    # Create a cProfile object and collect statistics
    pr = cProfile.Profile()
    pr.enable()    

    main()

    pr.disable()
    # Create a StringIO object to capture the output
    s = io.StringIO()
    sortby = 'cumulative'
    ps = pstats.Stats(pr, stream=s).sort_stats(sortby)
    ps.print_stats()

    # Print the profiler's statistics
    print(s.getvalue())

