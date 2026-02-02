"""
Planar Graph Triangulation Widget

A Tkinter-based application for:
1. Drawing an outline shape by clicking vertices
2. Generating random points inside the shape
3. Creating a Delaunay triangulation of those points
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, colorchooser
import random
import math
import json
import os
import xml.etree.ElementTree as ET
from typing import List, Tuple, Optional

Point = Tuple[float, float]
Triangle = Tuple[int, int, int]

# Config file path in user's home directory
CONFIG_FILE = os.path.join(os.path.expanduser("~"), ".planar_graph_widget.json")


class DelaunayTriangulation:
    """Implements Bowyer-Watson algorithm for Delaunay triangulation."""

    def __init__(self, points: List[Point]):
        self.points = list(points)
        self.triangles: List[Triangle] = []

    def triangulate(self) -> List[Triangle]:
        """Perform Delaunay triangulation using Bowyer-Watson algorithm."""
        if len(self.points) < 3:
            return []

        # Create super-triangle that contains all points
        min_x = min(p[0] for p in self.points)
        max_x = max(p[0] for p in self.points)
        min_y = min(p[1] for p in self.points)
        max_y = max(p[1] for p in self.points)

        dx = max_x - min_x
        dy = max_y - min_y
        delta_max = max(dx, dy) * 2

        mid_x = (min_x + max_x) / 2
        mid_y = (min_y + max_y) / 2

        # Super-triangle vertices
        p1 = (mid_x - delta_max, mid_y - delta_max)
        p2 = (mid_x + delta_max, mid_y - delta_max)
        p3 = (mid_x, mid_y + delta_max * 2)

        # Add super-triangle vertices to points list
        super_idx = len(self.points)
        self.points.extend([p1, p2, p3])

        # Initialize with super-triangle
        self.triangles = [(super_idx, super_idx + 1, super_idx + 2)]

        # Add each point one at a time
        for i in range(super_idx):
            self._add_point(i)

        # Remove triangles that share vertices with super-triangle
        self.triangles = [
            t for t in self.triangles
            if all(idx < super_idx for idx in t)
        ]

        # Remove super-triangle vertices
        self.points = self.points[:super_idx]

        return self.triangles

    def _add_point(self, point_idx: int):
        """Add a point to the triangulation."""
        point = self.points[point_idx]
        bad_triangles = []

        # Find all triangles whose circumcircle contains the point
        for tri in self.triangles:
            if self._point_in_circumcircle(point, tri):
                bad_triangles.append(tri)

        # Find the boundary of the polygonal hole
        polygon = []
        for tri in bad_triangles:
            for i in range(3):
                edge = (tri[i], tri[(i + 1) % 3])
                # Check if edge is shared by another bad triangle
                is_shared = False
                for other_tri in bad_triangles:
                    if other_tri == tri:
                        continue
                    if self._edge_in_triangle(edge, other_tri):
                        is_shared = True
                        break
                if not is_shared:
                    polygon.append(edge)

        # Remove bad triangles
        for tri in bad_triangles:
            self.triangles.remove(tri)

        # Re-triangulate the hole
        for edge in polygon:
            new_tri = (edge[0], edge[1], point_idx)
            self.triangles.append(new_tri)

    def _point_in_circumcircle(self, point: Point, triangle: Triangle) -> bool:
        """Check if point lies inside the circumcircle of a triangle."""
        p1 = self.points[triangle[0]]
        p2 = self.points[triangle[1]]
        p3 = self.points[triangle[2]]

        ax, ay = p1[0] - point[0], p1[1] - point[1]
        bx, by = p2[0] - point[0], p2[1] - point[1]
        cx, cy = p3[0] - point[0], p3[1] - point[1]

        det = (
            (ax * ax + ay * ay) * (bx * cy - cx * by) -
            (bx * bx + by * by) * (ax * cy - cx * ay) +
            (cx * cx + cy * cy) * (ax * by - bx * ay)
        )

        # Check orientation of triangle
        orient = (p2[0] - p1[0]) * (p3[1] - p1[1]) - (p2[1] - p1[1]) * (p3[0] - p1[0])

        if orient > 0:
            return det > 0
        return det < 0

    def _edge_in_triangle(self, edge: Tuple[int, int], triangle: Triangle) -> bool:
        """Check if an edge (in either direction) is part of a triangle."""
        for i in range(3):
            tri_edge = (triangle[i], triangle[(i + 1) % 3])
            if (edge[0] == tri_edge[0] and edge[1] == tri_edge[1]) or \
               (edge[0] == tri_edge[1] and edge[1] == tri_edge[0]):
                return True
        return False


class PlanarGraphWidget:
    """Main application widget for planar graph generation."""

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Planar Graph Triangulation Widget")
        self.root.geometry("900x700")

        # State
        self.outline_points: List[Point] = []
        self.outline_closed = False
        self.random_points: List[Point] = []
        self.triangles: List[Triangle] = []

        # Freehand drawing state
        self.is_drawing = False
        self.raw_points: List[Point] = []  # Raw points before simplification

        # Outer face vertex marking state
        # Maps vertex index (in _all_triangulation_points) to set: None, 'red', or 'black'
        self.outer_face_vertices: set = set()  # Indices of vertices on outer face
        self.vertex_sets: dict = {}  # vertex_idx -> 'red' | 'black' | None

        # Graph structure (edges) for re-embedding
        self.edges: set = set()  # Set of (i, j) tuples where i < j

        # Path finding state
        self.computed_paths: List[List[int]] = []  # List of paths (each path is list of vertex indices)
        self.path_vertices: set = set()  # Vertices on any path
        self.forbidden_vertices: set = set()  # Vertices within distance d of any path
        self.path_selection_mode = False
        self.path_source: Optional[int] = None  # Selected source vertex for path
        self.last_path_alternative: Optional[List[int]] = None  # Alternative route for last path
        self.last_path_d: int = 1  # Distance d used for last path (for toggling)

        # Display settings
        self.show_outline = True

        # Default drawing colors
        self._default_colors = {
            "outline_color": "#2196F3",
            "random_point_color": "#4CAF50",
            "triangle_fill_color": "#FFF3E0",
            "edge_color": "#333333",
            "red_set_color": "#E53935",
            "black_set_color": "#212121",
            "path_color": "#9C27B0",
            "forbidden_color": "#FFCDD2",
            "path_vertex_color": "#7B1FA2",
        }

        # Load colors from config or use defaults
        self._load_config()

        self._setup_menu()
        self._setup_ui()
        self._bind_events()

    def _setup_ui(self):
        """Set up the user interface."""
        # Main frame
        main_frame = ttk.Frame(self.root, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)

        # Control panel
        control_frame = ttk.LabelFrame(main_frame, text="Controls", padding="10")
        control_frame.pack(fill=tk.X, pady=(0, 10))

        # Instructions
        self.instructions_var = tk.StringVar()
        self.instructions_label = ttk.Label(
            control_frame,
            textvariable=self.instructions_var,
            font=("Segoe UI", 9)
        )
        self.instructions_label.pack(anchor=tk.W)

        # Drawing mode frame
        mode_frame = ttk.Frame(control_frame)
        mode_frame.pack(fill=tk.X, pady=(5, 0))

        ttk.Label(mode_frame, text="Drawing Mode:").pack(side=tk.LEFT)
        self.draw_mode_var = tk.StringVar(value="freehand")
        self.polygon_radio = ttk.Radiobutton(
            mode_frame, text="Polygon (click vertices)",
            variable=self.draw_mode_var, value="polygon",
            command=self._update_instructions
        )
        self.polygon_radio.pack(side=tk.LEFT, padx=(10, 5))
        self.freehand_radio = ttk.Radiobutton(
            mode_frame, text="Freehand (drag to draw)",
            variable=self.draw_mode_var, value="freehand",
            command=self._update_instructions
        )
        self.freehand_radio.pack(side=tk.LEFT, padx=5)

        # Simplification tolerance slider
        ttk.Label(mode_frame, text="Smoothing:").pack(side=tk.LEFT, padx=(20, 5))
        self.simplify_var = tk.DoubleVar(value=3.0)
        self.simplify_slider = ttk.Scale(
            mode_frame, from_=1.0, to=15.0,
            variable=self.simplify_var, orient=tk.HORIZONTAL, length=100
        )
        self.simplify_slider.pack(side=tk.LEFT)

        # Button frame
        btn_frame = ttk.Frame(control_frame)
        btn_frame.pack(fill=tk.X, pady=(10, 0))

        # Number of points
        ttk.Label(btn_frame, text="Points:").pack(side=tk.LEFT)
        self.num_points_var = tk.StringVar(value="20")
        self.num_points_entry = ttk.Entry(btn_frame, textvariable=self.num_points_var, width=6)
        self.num_points_entry.pack(side=tk.LEFT, padx=(5, 15))

        # Buttons
        self.generate_btn = ttk.Button(
            btn_frame, text="Generate Points", command=self._generate_points
        )
        self.generate_btn.pack(side=tk.LEFT, padx=5)

        self.triangulate_btn = ttk.Button(
            btn_frame, text="Triangulate", command=self._triangulate
        )
        self.triangulate_btn.pack(side=tk.LEFT, padx=5)

        self.clear_points_btn = ttk.Button(
            btn_frame, text="Clear Points", command=self._clear_points
        )
        self.clear_points_btn.pack(side=tk.LEFT, padx=5)

        self.clear_all_btn = ttk.Button(
            btn_frame, text="Clear All", command=self._clear_all
        )
        self.clear_all_btn.pack(side=tk.LEFT, padx=5)

        # Include outline vertices checkbox
        self.include_outline_var = tk.BooleanVar(value=True)
        self.include_outline_cb = ttk.Checkbutton(
            btn_frame, text="Include outline in triangulation",
            variable=self.include_outline_var
        )
        self.include_outline_cb.pack(side=tk.LEFT, padx=15)

        # Vertex marking frame
        mark_frame = ttk.Frame(control_frame)
        mark_frame.pack(fill=tk.X, pady=(10, 0))

        ttk.Label(mark_frame, text="Outer Face Marking:").pack(side=tk.LEFT)
        self.mark_mode_var = tk.StringVar(value="none")
        self.mark_none_radio = ttk.Radiobutton(
            mark_frame, text="Off",
            variable=self.mark_mode_var, value="none"
        )
        self.mark_none_radio.pack(side=tk.LEFT, padx=(10, 5))
        self.mark_red_radio = ttk.Radiobutton(
            mark_frame, text="Mark Red (square)",
            variable=self.mark_mode_var, value="red"
        )
        self.mark_red_radio.pack(side=tk.LEFT, padx=5)
        self.mark_black_radio = ttk.Radiobutton(
            mark_frame, text="Mark Black (triangle)",
            variable=self.mark_mode_var, value="black"
        )
        self.mark_black_radio.pack(side=tk.LEFT, padx=5)

        self.clear_marks_btn = ttk.Button(
            mark_frame, text="Clear Marks", command=self._clear_marks
        )
        self.clear_marks_btn.pack(side=tk.LEFT, padx=15)

        # Graph operations frame
        graph_frame = ttk.Frame(control_frame)
        graph_frame.pack(fill=tk.X, pady=(10, 0))

        ttk.Label(graph_frame, text="Graph:").pack(side=tk.LEFT)

        self.reembed_btn = ttk.Button(
            graph_frame, text="Re-embed", command=self._reembed_graph
        )
        self.reembed_btn.pack(side=tk.LEFT, padx=(10, 5))

        self.show_outline_var = tk.BooleanVar(value=True)
        self.show_outline_cb = ttk.Checkbutton(
            graph_frame, text="Show outline",
            variable=self.show_outline_var,
            command=self._toggle_outline
        )
        self.show_outline_cb.pack(side=tk.LEFT, padx=15)

        self.export_btn = ttk.Button(
            graph_frame, text="Export GraphML", command=self._export_graphml
        )
        self.export_btn.pack(side=tk.LEFT, padx=5)

        self.export_pdf_btn = ttk.Button(
            graph_frame, text="Export PDF", command=self._export_pdf
        )
        self.export_pdf_btn.pack(side=tk.LEFT, padx=5)

        ttk.Label(graph_frame, text="Vertex:").pack(side=tk.LEFT, padx=(15, 2))
        self.vertex_size_var = tk.DoubleVar(value=3.0)
        self.vertex_size_slider = ttk.Scale(
            graph_frame, from_=1.0, to=8.0,
            variable=self.vertex_size_var, orient=tk.HORIZONTAL, length=60,
            command=lambda _: self._redraw()
        )
        self.vertex_size_slider.pack(side=tk.LEFT)

        ttk.Label(graph_frame, text="Marker:").pack(side=tk.LEFT, padx=(10, 2))
        self.marker_size_var = tk.DoubleVar(value=6.0)
        self.marker_size_slider = ttk.Scale(
            graph_frame, from_=3.0, to=15.0,
            variable=self.marker_size_var, orient=tk.HORIZONTAL, length=60,
            command=lambda _: self._redraw()
        )
        self.marker_size_slider.pack(side=tk.LEFT)

        ttk.Label(graph_frame, text="Path:").pack(side=tk.LEFT, padx=(10, 2))
        self.path_width_var = tk.DoubleVar(value=4.0)
        self.path_width_slider = ttk.Scale(
            graph_frame, from_=1.0, to=10.0,
            variable=self.path_width_var, orient=tk.HORIZONTAL, length=60,
            command=lambda _: self._redraw()
        )
        self.path_width_slider.pack(side=tk.LEFT)

        self.delete_mode_var = tk.BooleanVar(value=False)
        self.delete_mode_cb = ttk.Checkbutton(
            graph_frame, text="Delete mode",
            variable=self.delete_mode_var
        )
        self.delete_mode_cb.pack(side=tk.LEFT, padx=(15, 5))

        # Path finding frame
        path_frame = ttk.Frame(control_frame)
        path_frame.pack(fill=tk.X, pady=(10, 0))

        ttk.Label(path_frame, text="Path Finding:").pack(side=tk.LEFT)

        ttk.Label(path_frame, text="Distance d:").pack(side=tk.LEFT, padx=(10, 2))
        self.path_distance_var = tk.StringVar(value="1")
        self.path_distance_entry = ttk.Entry(
            path_frame, textvariable=self.path_distance_var, width=4
        )
        self.path_distance_entry.pack(side=tk.LEFT, padx=(0, 10))

        self.select_path_btn = ttk.Button(
            path_frame, text="Select Path Endpoints", command=self._start_path_selection
        )
        self.select_path_btn.pack(side=tk.LEFT, padx=5)

        self.clear_paths_btn = ttk.Button(
            path_frame, text="Clear Paths", command=self._clear_paths
        )
        self.clear_paths_btn.pack(side=tk.LEFT, padx=5)

        self.toggle_path_btn = ttk.Button(
            path_frame, text="Toggle Last Path (T)", command=self._toggle_last_path
        )
        self.toggle_path_btn.pack(side=tk.LEFT, padx=5)

        self.path_status_var = tk.StringVar(value="")
        self.path_status_label = ttk.Label(
            path_frame, textvariable=self.path_status_var,
            font=("Segoe UI", 9, "italic")
        )
        self.path_status_label.pack(side=tk.LEFT, padx=15)

        # Canvas
        canvas_frame = ttk.LabelFrame(main_frame, text="Canvas", padding="5")
        canvas_frame.pack(fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(
            canvas_frame,
            bg="white",
            highlightthickness=1,
            highlightbackground="#cccccc"
        )
        self.canvas.pack(fill=tk.BOTH, expand=True)

        # Status bar
        self.status_var = tk.StringVar(value="Click to start drawing an outline shape")
        status_bar = ttk.Label(
            main_frame, textvariable=self.status_var, relief=tk.SUNKEN, anchor=tk.W
        )
        status_bar.pack(fill=tk.X, pady=(10, 0))

        # Initialize instructions
        self._update_instructions()

    def _bind_events(self):
        """Bind mouse and keyboard events."""
        self.canvas.bind("<Button-1>", self._on_left_click)
        self.canvas.bind("<ButtonRelease-1>", self._on_left_release)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<Button-3>", self._on_right_click)
        self.canvas.bind("<Motion>", self._on_mouse_move)
        # Keyboard bindings (bind to root to work regardless of focus)
        self.root.bind("<t>", lambda _: self._toggle_last_path())
        self.root.bind("<T>", lambda _: self._toggle_last_path())

    def _load_config(self):
        """Load colors from config file or use defaults."""
        # Start with defaults
        for key, value in self._default_colors.items():
            setattr(self, key, value)

        # Try to load from config file
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, 'r') as f:
                    config = json.load(f)
                    colors = config.get('colors', {})
                    for key, value in colors.items():
                        if key in self._default_colors:
                            setattr(self, key, value)
            except (json.JSONDecodeError, IOError):
                pass  # Use defaults if config is invalid

    def _save_config(self):
        """Save current colors to config file."""
        colors = {key: getattr(self, key) for key in self._default_colors}
        config = {'colors': colors}
        try:
            with open(CONFIG_FILE, 'w') as f:
                json.dump(config, f, indent=2)
        except IOError:
            pass  # Silently fail if can't write config

    def _setup_menu(self):
        """Set up the menu bar."""
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)

        # Colors menu
        colors_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Colors", menu=colors_menu)

        colors_menu.add_command(
            label="Outline Color...",
            command=lambda: self._pick_color('outline_color', "Outline Color")
        )
        colors_menu.add_command(
            label="Vertex Color...",
            command=lambda: self._pick_color('random_point_color', "Vertex Color")
        )
        colors_menu.add_command(
            label="Triangle Fill Color...",
            command=lambda: self._pick_color('triangle_fill_color', "Triangle Fill Color")
        )
        colors_menu.add_command(
            label="Edge Color...",
            command=lambda: self._pick_color('edge_color', "Edge Color")
        )

        colors_menu.add_separator()

        colors_menu.add_command(
            label="Red Set Color...",
            command=lambda: self._pick_color('red_set_color', "Red Set Color")
        )
        colors_menu.add_command(
            label="Black Set Color...",
            command=lambda: self._pick_color('black_set_color', "Black Set Color")
        )

        colors_menu.add_separator()

        colors_menu.add_command(
            label="Path Color...",
            command=lambda: self._pick_color('path_color', "Path Color")
        )
        colors_menu.add_command(
            label="Path Vertex Color...",
            command=lambda: self._pick_color('path_vertex_color', "Path Vertex Color")
        )
        colors_menu.add_command(
            label="Forbidden Region Color...",
            command=lambda: self._pick_color('forbidden_color', "Forbidden Region Color")
        )

        colors_menu.add_separator()

        colors_menu.add_command(
            label="Reset to Defaults",
            command=self._reset_colors
        )

    def _pick_color(self, attr_name: str, title: str):
        """Open color picker for a specific color attribute."""
        current_color = getattr(self, attr_name)
        result = colorchooser.askcolor(color=current_color, title=title)

        if result[1]:  # result is ((r, g, b), '#hexcolor') or (None, None) if cancelled
            setattr(self, attr_name, result[1])
            self._save_config()
            self._redraw()

    def _reset_colors(self):
        """Reset all colors to defaults."""
        for key, value in self._default_colors.items():
            setattr(self, key, value)
        self._save_config()
        self._redraw()

    def _get_point_radius(self) -> int:
        """Get the current point radius from the slider."""
        return int(self.vertex_size_var.get())

    def _get_marker_size(self) -> int:
        """Get the current marker size from the slider."""
        return int(self.marker_size_var.get())

    def _get_path_width(self) -> int:
        """Get the current path width from the slider."""
        return int(self.path_width_var.get())

    def _update_instructions(self):
        """Update instructions based on drawing mode."""
        if self.draw_mode_var.get() == "polygon":
            self.instructions_var.set(
                "1. Click to add outline vertices  2. Right-click to close shape  "
                "3. Generate points  4. Triangulate"
            )
        else:
            self.instructions_var.set(
                "1. Click and drag to draw outline  2. Release to close shape  "
                "3. Generate points  4. Triangulate"
            )

    def _on_left_click(self, event):
        """Handle left click - start drawing, add point, mark vertex, or select path endpoint."""
        # Check if we're in path selection mode
        if self.path_selection_mode and self.triangles:
            clicked_vertex = self._find_clicked_marked_vertex(event.x, event.y)
            if clicked_vertex is not None:
                self._handle_path_vertex_selection(clicked_vertex)
                return

        # Check if we're in marking mode and have a triangulation
        if self.mark_mode_var.get() != "none" and self.triangles:
            clicked_vertex = self._find_clicked_outer_vertex(event.x, event.y)
            if clicked_vertex is not None:
                self._toggle_vertex_mark(clicked_vertex)
                return

        if self.outline_closed:
            return

        if self.draw_mode_var.get() == "freehand":
            # Start freehand drawing
            self.is_drawing = True
            self.raw_points = [(event.x, event.y)]
            self.outline_points = []
        else:
            # Polygon mode - add single point
            point = (event.x, event.y)
            self.outline_points.append(point)

        self._redraw()
        self._update_status()

    def _on_drag(self, event):
        """Handle mouse drag - add points in freehand mode."""
        if not self.is_drawing or self.outline_closed:
            return

        if self.draw_mode_var.get() == "freehand":
            self.raw_points.append((event.x, event.y))
            # Draw the raw stroke in real-time
            self._redraw_freehand_preview()

    def _on_left_release(self, event):
        """Handle left button release - finish freehand drawing."""
        if not self.is_drawing:
            return

        if self.draw_mode_var.get() == "freehand" and len(self.raw_points) >= 3:
            # Simplify the path and close it
            self.outline_points = self._simplify_path(self.raw_points)
            self.outline_closed = True
            self.is_drawing = False
            self._redraw()
            self._update_status()
        elif self.draw_mode_var.get() == "freehand":
            # Not enough points, reset
            self.is_drawing = False
            self.raw_points = []

    def _on_right_click(self, event):
        """Handle right click - close outline, exit path selection, or delete vertex."""
        # Exit path selection mode if active
        if self.path_selection_mode:
            self.path_selection_mode = False
            self.path_source = None
            self.path_status_var.set("")
            self._redraw()
            return

        # Check for delete mode
        if self.delete_mode_var.get() and self.triangles:
            clicked_vertex = self._find_clicked_vertex(event.x, event.y)
            if clicked_vertex is not None:
                self._delete_vertex(clicked_vertex)
                return

        if self.draw_mode_var.get() == "polygon":
            if len(self.outline_points) >= 3 and not self.outline_closed:
                self.outline_closed = True
                self._redraw()
                self._update_status()

    def _on_mouse_move(self, event):
        """Handle mouse movement - show preview line in polygon mode."""
        if self.draw_mode_var.get() == "polygon":
            if not self.outline_closed and len(self.outline_points) > 0:
                self._redraw()
                # Draw preview line
                last_point = self.outline_points[-1]
                self.canvas.create_line(
                    last_point[0], last_point[1], event.x, event.y,
                    fill="#999999", dash=(4, 4), tags="preview"
                )

    def _redraw_freehand_preview(self):
        """Draw the freehand stroke in real-time."""
        self.canvas.delete("all")

        if len(self.raw_points) >= 2:
            # Draw smooth line through raw points
            coords = []
            for p in self.raw_points:
                coords.extend([p[0], p[1]])
            self.canvas.create_line(
                coords,
                fill=self.outline_color,
                width=2,
                smooth=True,
                splinesteps=36
            )

    def _simplify_path(self, points: List[Point]) -> List[Point]:
        """Simplify a path using Ramer-Douglas-Peucker algorithm."""
        if len(points) < 3:
            return points

        tolerance = self.simplify_var.get()
        return self._rdp_simplify(points, tolerance)

    def _rdp_simplify(self, points: List[Point], epsilon: float) -> List[Point]:
        """Ramer-Douglas-Peucker path simplification."""
        if len(points) < 3:
            return points

        # Find the point with maximum distance from line between first and last
        start, end = points[0], points[-1]
        max_dist = 0
        max_idx = 0

        for i in range(1, len(points) - 1):
            dist = self._point_line_distance(points[i], start, end)
            if dist > max_dist:
                max_dist = dist
                max_idx = i

        # If max distance is greater than epsilon, recursively simplify
        if max_dist > epsilon:
            left = self._rdp_simplify(points[:max_idx + 1], epsilon)
            right = self._rdp_simplify(points[max_idx:], epsilon)
            return left[:-1] + right
        else:
            return [start, end]

    def _point_line_distance(self, point: Point, line_start: Point, line_end: Point) -> float:
        """Calculate perpendicular distance from point to line."""
        x0, y0 = point
        x1, y1 = line_start
        x2, y2 = line_end

        dx = x2 - x1
        dy = y2 - y1

        if dx == 0 and dy == 0:
            return math.sqrt((x0 - x1) ** 2 + (y0 - y1) ** 2)

        t = max(0, min(1, ((x0 - x1) * dx + (y0 - y1) * dy) / (dx * dx + dy * dy)))
        proj_x = x1 + t * dx
        proj_y = y1 + t * dy

        return math.sqrt((x0 - proj_x) ** 2 + (y0 - proj_y) ** 2)

    def _generate_points(self):
        """Generate random points inside the outline."""
        if not self.outline_closed:
            messagebox.showwarning("Warning", "Please close the outline first (right-click)")
            return

        try:
            num_points = int(self.num_points_var.get())
            if num_points < 1:
                raise ValueError()
        except ValueError:
            messagebox.showerror("Error", "Please enter a valid positive number")
            return

        # Get bounding box
        min_x = min(p[0] for p in self.outline_points)
        max_x = max(p[0] for p in self.outline_points)
        min_y = min(p[1] for p in self.outline_points)
        max_y = max(p[1] for p in self.outline_points)

        # Generate random points inside polygon
        self.random_points = []
        attempts = 0
        max_attempts = num_points * 100

        while len(self.random_points) < num_points and attempts < max_attempts:
            x = random.uniform(min_x, max_x)
            y = random.uniform(min_y, max_y)

            if self._point_in_polygon((x, y), self.outline_points):
                self.random_points.append((x, y))

            attempts += 1

        self.triangles = []  # Clear existing triangulation
        self._redraw()
        self._update_status()

    def _point_in_polygon(self, point: Point, polygon: List[Point]) -> bool:
        """Check if a point is inside a polygon using ray casting."""
        x, y = point
        n = len(polygon)
        inside = False

        j = n - 1
        for i in range(n):
            xi, yi = polygon[i]
            xj, yj = polygon[j]

            if ((yi > y) != (yj > y)) and (x < (xj - xi) * (y - yi) / (yj - yi) + xi):
                inside = not inside

            j = i

        return inside

    def _triangulate(self):
        """Perform Delaunay triangulation."""
        if not self.outline_closed:
            messagebox.showwarning("Warning", "Please close the outline first")
            return

        # Collect all points for triangulation
        all_points = list(self.random_points)

        if self.include_outline_var.get():
            all_points.extend(self.outline_points)

        if len(all_points) < 3:
            messagebox.showwarning("Warning", "Need at least 3 points to triangulate")
            return

        # Perform triangulation
        delaunay = DelaunayTriangulation(all_points)
        triangles = delaunay.triangulate()

        # Filter triangles to only include those inside the outline
        self.triangles = []
        for tri in triangles:
            if self._triangle_inside_outline(tri, all_points):
                self.triangles.append(tri)

        # Store all points for drawing
        self._all_triangulation_points = all_points

        # Build edge set from triangles
        self.edges = set()
        for tri in self.triangles:
            for i in range(3):
                edge = tuple(sorted([tri[i], tri[(i + 1) % 3]]))
                self.edges.add(edge)

        # Compute outer face vertices and clear old marks
        self._compute_outer_face_vertices()
        self.vertex_sets = {}

        self._redraw()
        self._update_status()

    def _triangle_inside_outline(self, triangle: Triangle, points: List[Point]) -> bool:
        """Check if a triangle's centroid is inside the outline polygon."""
        p1 = points[triangle[0]]
        p2 = points[triangle[1]]
        p3 = points[triangle[2]]

        # Calculate centroid
        centroid = (
            (p1[0] + p2[0] + p3[0]) / 3,
            (p1[1] + p2[1] + p3[1]) / 3
        )

        return self._point_in_polygon(centroid, self.outline_points)

    def _compute_outer_face_vertices(self):
        """Compute which vertices are on the outer face of the triangulation."""
        if not self.triangles or not hasattr(self, '_all_triangulation_points'):
            self.outer_face_vertices = set()
            return

        # Build edge count - outer face edges appear in only one triangle
        edge_count = {}
        for tri in self.triangles:
            for i in range(3):
                edge = tuple(sorted([tri[i], tri[(i + 1) % 3]]))
                edge_count[edge] = edge_count.get(edge, 0) + 1

        # Outer edges are those that appear exactly once
        outer_edges = [edge for edge, count in edge_count.items() if count == 1]

        # Collect vertices from outer edges
        self.outer_face_vertices = set()
        for edge in outer_edges:
            self.outer_face_vertices.add(edge[0])
            self.outer_face_vertices.add(edge[1])

    def _find_clicked_outer_vertex(self, x: float, y: float) -> Optional[int]:
        """Find if a click is on an outer face vertex. Returns vertex index or None."""
        if not hasattr(self, '_all_triangulation_points'):
            return None

        click_radius = self._get_point_radius() + 6  # Slightly larger hit area

        for vertex_idx in self.outer_face_vertices:
            vx, vy = self._all_triangulation_points[vertex_idx]
            dist = math.sqrt((x - vx) ** 2 + (y - vy) ** 2)
            if dist <= click_radius:
                return vertex_idx

        return None

    def _toggle_vertex_mark(self, vertex_idx: int):
        """Toggle the mark on an outer face vertex."""
        current_mark = self.vertex_sets.get(vertex_idx)
        new_mark = self.mark_mode_var.get()

        if current_mark == new_mark:
            # Clicking same mode removes the mark
            del self.vertex_sets[vertex_idx]
        else:
            # Set the new mark
            self.vertex_sets[vertex_idx] = new_mark

        self._redraw()
        self._update_status()

    def _clear_marks(self):
        """Clear all vertex marks."""
        self.vertex_sets = {}
        self._redraw()
        self._update_status()

    def _start_path_selection(self):
        """Toggle path selection mode."""
        # If already in path selection mode, exit it
        if self.path_selection_mode:
            self.path_selection_mode = False
            self.path_source = None
            self.path_status_var.set("")
            self._redraw()
            return

        if not self.triangles:
            messagebox.showwarning("Warning", "Please create a triangulation first")
            return

        # Check if we have both red and black marked vertices
        red_vertices = [v for v, c in self.vertex_sets.items() if c == 'red']
        black_vertices = [v for v, c in self.vertex_sets.items() if c == 'black']

        if not red_vertices or not black_vertices:
            messagebox.showwarning(
                "Warning",
                "Please mark at least one red vertex and one black vertex on the outer face"
            )
            return

        self.path_selection_mode = True
        self.path_source = None
        self.path_status_var.set("PATH MODE: Click red/black vertices to create paths. Right-click to exit.")
        self._redraw()

    def _find_clicked_marked_vertex(self, x: float, y: float) -> Optional[int]:
        """Find if a click is on a marked (red/black) vertex."""
        if not hasattr(self, '_all_triangulation_points'):
            return None

        click_radius = self._get_point_radius() + 8

        for vertex_idx, color in self.vertex_sets.items():
            if color in ('red', 'black'):
                vx, vy = self._all_triangulation_points[vertex_idx]
                dist = math.sqrt((x - vx) ** 2 + (y - vy) ** 2)
                if dist <= click_radius:
                    return vertex_idx

        return None

    def _find_clicked_vertex(self, x: float, y: float) -> Optional[int]:
        """Find if a click is on any vertex. Returns vertex index or None."""
        if not hasattr(self, '_all_triangulation_points'):
            return None

        click_radius = self._get_point_radius() + 6

        for idx, point in enumerate(self._all_triangulation_points):
            vx, vy = point
            dist = math.sqrt((x - vx) ** 2 + (y - vy) ** 2)
            if dist <= click_radius:
                return idx

        return None

    def _delete_vertex(self, vertex_idx: int):
        """Delete a vertex and update all related data structures."""
        if not hasattr(self, '_all_triangulation_points'):
            return

        n = len(self._all_triangulation_points)
        if vertex_idx < 0 or vertex_idx >= n:
            return

        # Remove the vertex from the points list
        del self._all_triangulation_points[vertex_idx]

        # Helper to remap index after deletion
        def remap(idx):
            if idx < vertex_idx:
                return idx
            elif idx > vertex_idx:
                return idx - 1
            else:
                return None  # This index was deleted

        # Remove triangles containing this vertex, remap others
        new_triangles = []
        for tri in self.triangles:
            if vertex_idx in tri:
                continue  # Skip triangles containing deleted vertex
            new_tri = tuple(remap(i) for i in tri)
            new_triangles.append(new_tri)
        self.triangles = new_triangles

        # Rebuild edges from remaining triangles
        self.edges = set()
        for tri in self.triangles:
            for i in range(3):
                edge = tuple(sorted([tri[i], tri[(i + 1) % 3]]))
                self.edges.add(edge)

        # Remap outer face vertices
        new_outer = set()
        for v in self.outer_face_vertices:
            new_v = remap(v)
            if new_v is not None:
                new_outer.add(new_v)
        self.outer_face_vertices = new_outer

        # Recompute outer face (some edges may now be on boundary)
        self._compute_outer_face_vertices()

        # Remap vertex sets (red/black marks)
        new_vertex_sets = {}
        for v, color in self.vertex_sets.items():
            new_v = remap(v)
            if new_v is not None:
                new_vertex_sets[new_v] = color
        self.vertex_sets = new_vertex_sets

        # Remap path vertices
        new_path_vertices = set()
        for v in self.path_vertices:
            new_v = remap(v)
            if new_v is not None:
                new_path_vertices.add(new_v)
        self.path_vertices = new_path_vertices

        # Remap forbidden vertices
        new_forbidden = set()
        for v in self.forbidden_vertices:
            new_v = remap(v)
            if new_v is not None:
                new_forbidden.add(new_v)
        self.forbidden_vertices = new_forbidden

        # Remap computed paths
        new_paths = []
        for path in self.computed_paths:
            new_path = []
            valid = True
            for v in path:
                new_v = remap(v)
                if new_v is None:
                    valid = False  # Path contains deleted vertex
                    break
                new_path.append(new_v)
            if valid:
                new_paths.append(new_path)
        self.computed_paths = new_paths

        # Remap last_path_alternative
        if self.last_path_alternative is not None:
            new_alt = []
            valid = True
            for v in self.last_path_alternative:
                new_v = remap(v)
                if new_v is None:
                    valid = False
                    break
                new_alt.append(new_v)
            self.last_path_alternative = new_alt if valid else None

        self._redraw()
        self._update_status()

    def _handle_path_vertex_selection(self, vertex_idx: int):
        """Handle selection of a vertex for path finding."""
        vertex_color = self.vertex_sets.get(vertex_idx)

        if self.path_source is None:
            # Selecting source
            self.path_source = vertex_idx
            self.path_status_var.set(
                f"Source: {vertex_color}. Click a different color vertex as target..."
            )
        else:
            # Selecting target
            source_color = self.vertex_sets.get(self.path_source)

            if vertex_color == source_color:
                self.path_status_var.set(
                    f"Target must be different color! Click a non-{source_color} vertex..."
                )
                return

            # Compute path
            self._compute_path(self.path_source, vertex_idx)

            # Stay in path selection mode, ready for next path
            self.path_source = None
            self.path_status_var.set(
                "PATH MODE: Path added. Click next source vertex, or right-click to exit."
            )

        self._redraw()

    def _compute_path(self, source: int, target: int):
        """Compute a path from source to target along the outer face of the remaining graph."""
        try:
            d = int(self.path_distance_var.get())
            if d < 0:
                raise ValueError()
        except ValueError:
            messagebox.showerror("Error", "Distance d must be a non-negative integer")
            return

        # Find both paths along the outer face of the graph remaining after removing forbidden vertices
        path, alt_path = self._find_both_paths_on_remaining_outer_face(
            source, target, self.forbidden_vertices
        )

        if path is None:
            messagebox.showwarning(
                "No Path Found",
                "Could not find a valid path along the outer face of the remaining graph."
            )
            return

        # Store the path and the alternative for toggling
        self.computed_paths.append(path)
        self.last_path_alternative = alt_path
        self.last_path_d = d

        # Mark path vertices
        for v in path:
            self.path_vertices.add(v)

        # Compute and mark vertices within distance d of the path
        adjacency = self._build_adjacency_list()
        self._mark_path_neighborhood(path, d, adjacency)

        self._redraw()
        self._update_status()

    def _find_both_paths_on_remaining_outer_face(
        self,
        source: int,
        target: int,
        forbidden: set
    ) -> Tuple[Optional[List[int]], Optional[List[int]]]:
        """Find both paths from source to target along the outer face of the remaining graph.

        Returns (path1, path2) where path1 is the shorter path, or (None, None) if no path exists.
        """
        # Check if source or target is forbidden
        if source in forbidden or target in forbidden:
            return None, None

        # Find triangles that don't contain any forbidden vertices
        remaining_triangles = [
            tri for tri in self.triangles
            if not any(v in forbidden for v in tri)
        ]

        if not remaining_triangles:
            return None, None

        # Find edges that appear in exactly one remaining triangle (outer face edges)
        edge_count = {}
        for tri in remaining_triangles:
            for i in range(3):
                edge = tuple(sorted([tri[i], tri[(i + 1) % 3]]))
                edge_count[edge] = edge_count.get(edge, 0) + 1

        # Outer face edges of remaining graph
        outer_edges = {edge for edge, count in edge_count.items() if count == 1}

        # Vertices on the outer face of remaining graph
        outer_vertices = set()
        for edge in outer_edges:
            outer_vertices.add(edge[0])
            outer_vertices.add(edge[1])

        # Check if source and target are on the outer face
        if source not in outer_vertices or target not in outer_vertices:
            return None, None

        # Build adjacency for outer face edges only
        adjacency = {v: [] for v in outer_vertices}
        for i, j in outer_edges:
            adjacency[i].append(j)
            adjacency[j].append(i)

        # The outer face forms a cycle. Find both paths around the cycle.
        # First, find all paths using DFS (there should be exactly 2 on a cycle)
        all_paths = []

        def dfs(current, target, visited, path):
            if current == target:
                all_paths.append(path[:])
                return
            for neighbor in adjacency.get(current, []):
                if neighbor not in visited:
                    visited.add(neighbor)
                    path.append(neighbor)
                    dfs(neighbor, target, visited, path)
                    path.pop()
                    visited.remove(neighbor)

        dfs(source, target, {source}, [source])

        if len(all_paths) == 0:
            return None, None
        elif len(all_paths) == 1:
            return all_paths[0], None
        else:
            # Sort by length, return shorter first
            all_paths.sort(key=len)
            return all_paths[0], all_paths[1]

    def _build_adjacency_list(self) -> dict:
        """Build adjacency list from edges."""
        adjacency = {}
        n = len(self._all_triangulation_points)
        for i in range(n):
            adjacency[i] = []

        for i, j in self.edges:
            adjacency[i].append(j)
            adjacency[j].append(i)

        return adjacency

    def _mark_path_neighborhood(self, path: List[int], d: int, adjacency: dict):
        """Mark all vertices within distance d of the path as forbidden."""
        from collections import deque

        # BFS from all path vertices
        dist = {v: float('inf') for v in adjacency}
        queue = deque()

        for v in path:
            dist[v] = 0
            queue.append(v)

        while queue:
            u = queue.popleft()
            if dist[u] >= d:
                continue
            for v in adjacency[u]:
                if dist[v] == float('inf'):
                    dist[v] = dist[u] + 1
                    queue.append(v)

        # Mark vertices within distance d as forbidden (excluding the path itself for d=0)
        for v, distance in dist.items():
            if distance <= d:
                self.forbidden_vertices.add(v)

    def _clear_paths(self):
        """Clear all computed paths."""
        self.computed_paths = []
        self.path_vertices = set()
        self.forbidden_vertices = set()
        self.path_selection_mode = False
        self.path_source = None
        self.last_path_alternative = None
        self.path_status_var.set("")
        self._redraw()
        self._update_status()

    def _toggle_last_path(self):
        """Toggle the last computed path to use the alternative route."""
        if not self.computed_paths:
            return  # No paths to toggle

        if self.last_path_alternative is None:
            return  # No alternative available

        # Get the last path
        old_path = self.computed_paths[-1]

        # Remove the old path's contribution to path_vertices
        # (but keep vertices that are part of other paths)
        other_path_vertices = set()
        for p in self.computed_paths[:-1]:
            other_path_vertices.update(p)

        # Recompute forbidden vertices from scratch
        # First, clear everything related to the last path
        self.path_vertices = other_path_vertices.copy()
        self.forbidden_vertices = set()

        # Recompute forbidden for all paths except the last
        adjacency = self._build_adjacency_list()
        for p in self.computed_paths[:-1]:
            self._mark_path_neighborhood(p, self.last_path_d, adjacency)

        # Swap the paths
        new_path = self.last_path_alternative
        self.last_path_alternative = old_path
        self.computed_paths[-1] = new_path

        # Add the new path's vertices
        for v in new_path:
            self.path_vertices.add(v)

        # Mark the new path's neighborhood
        self._mark_path_neighborhood(new_path, self.last_path_d, adjacency)

        self._redraw()
        self._update_status()

    def _toggle_outline(self):
        """Toggle outline visibility."""
        self.show_outline = self.show_outline_var.get()
        self._redraw()

    def _export_graphml(self):
        """Export the graph as a GraphML file."""
        if not self.triangles or not hasattr(self, '_all_triangulation_points'):
            messagebox.showwarning("Warning", "No triangulation to export")
            return

        # Ask for file location
        filepath = filedialog.asksaveasfilename(
            defaultextension=".graphml",
            filetypes=[("GraphML files", "*.graphml"), ("All files", "*.*")],
            title="Export Graph as GraphML"
        )

        if not filepath:
            return  # User cancelled

        # Create GraphML structure
        graphml = ET.Element('graphml')
        graphml.set('xmlns', 'http://graphml.graphdrawing.org/xmlns')
        graphml.set('xmlns:xsi', 'http://www.w3.org/2001/XMLSchema-instance')
        graphml.set('xsi:schemaLocation',
                    'http://graphml.graphdrawing.org/xmlns '
                    'http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd')

        # Define node attribute keys
        key_x = ET.SubElement(graphml, 'key')
        key_x.set('id', 'x')
        key_x.set('for', 'node')
        key_x.set('attr.name', 'x')
        key_x.set('attr.type', 'double')

        key_y = ET.SubElement(graphml, 'key')
        key_y.set('id', 'y')
        key_y.set('for', 'node')
        key_y.set('attr.name', 'y')
        key_y.set('attr.type', 'double')

        key_outer = ET.SubElement(graphml, 'key')
        key_outer.set('id', 'outer_face')
        key_outer.set('for', 'node')
        key_outer.set('attr.name', 'outer_face')
        key_outer.set('attr.type', 'boolean')

        key_set = ET.SubElement(graphml, 'key')
        key_set.set('id', 'color_set')
        key_set.set('for', 'node')
        key_set.set('attr.name', 'color_set')
        key_set.set('attr.type', 'string')

        # Create graph element
        graph = ET.SubElement(graphml, 'graph')
        graph.set('id', 'G')
        graph.set('edgedefault', 'undirected')

        # Add nodes
        for idx, point in enumerate(self._all_triangulation_points):
            node = ET.SubElement(graph, 'node')
            node.set('id', f'n{idx}')

            # Position
            data_x = ET.SubElement(node, 'data')
            data_x.set('key', 'x')
            data_x.text = str(point[0])

            data_y = ET.SubElement(node, 'data')
            data_y.set('key', 'y')
            data_y.text = str(point[1])

            # Outer face membership
            data_outer = ET.SubElement(node, 'data')
            data_outer.set('key', 'outer_face')
            data_outer.text = 'true' if idx in self.outer_face_vertices else 'false'

            # Color set (red/black/none)
            color_set = self.vertex_sets.get(idx, '')
            if color_set:
                data_set = ET.SubElement(node, 'data')
                data_set.set('key', 'color_set')
                data_set.text = color_set

        # Add edges
        edge_id = 0
        for i, j in self.edges:
            edge = ET.SubElement(graph, 'edge')
            edge.set('id', f'e{edge_id}')
            edge.set('source', f'n{i}')
            edge.set('target', f'n{j}')
            edge_id += 1

        # Write to file
        tree = ET.ElementTree(graphml)
        ET.indent(tree, space='  ')
        tree.write(filepath, encoding='utf-8', xml_declaration=True)

        messagebox.showinfo("Export Complete", f"Graph exported to:\n{filepath}")

    def _export_pdf(self):
        """Export the graph as a vector PDF file."""
        if not self.triangles or not hasattr(self, '_all_triangulation_points'):
            messagebox.showwarning("Warning", "No triangulation to export")
            return

        try:
            from reportlab.pdfgen import canvas as pdf_canvas
            from reportlab.lib.colors import HexColor
        except ImportError:
            messagebox.showerror(
                "Missing Dependency",
                "The 'reportlab' library is required for PDF export.\n\n"
                "Install it with: pip install reportlab"
            )
            return

        # Ask for file location
        filepath = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")],
            title="Export Graph as PDF"
        )

        if not filepath:
            return  # User cancelled

        # Get canvas dimensions
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        if canvas_width < 100:
            canvas_width = 800
        if canvas_height < 100:
            canvas_height = 500

        # Create PDF with same dimensions as canvas
        c = pdf_canvas.Canvas(filepath, pagesize=(canvas_width, canvas_height))

        # Helper to convert hex color to reportlab color
        def hex_to_color(hex_color):
            return HexColor(hex_color)

        # Helper to flip y coordinate (Tkinter: y=0 at top, PDF: y=0 at bottom)
        def flip_y(y):
            return canvas_height - y

        # Draw white background
        c.setFillColor(HexColor("#FFFFFF"))
        c.rect(0, 0, canvas_width, canvas_height, fill=True, stroke=False)

        # Draw triangulation (filled triangles)
        if self.triangles and hasattr(self, '_all_triangulation_points'):
            for tri in self.triangles:
                points = [self._all_triangulation_points[i] for i in tri]

                # Determine fill color
                if any(v in self.forbidden_vertices for v in tri):
                    fill_color = self.forbidden_color
                else:
                    fill_color = self.triangle_fill_color

                # Draw filled triangle
                path = c.beginPath()
                path.moveTo(points[0][0], flip_y(points[0][1]))
                path.lineTo(points[1][0], flip_y(points[1][1]))
                path.lineTo(points[2][0], flip_y(points[2][1]))
                path.close()

                c.setFillColor(hex_to_color(fill_color))
                c.setStrokeColor(hex_to_color(self.edge_color))
                c.setLineWidth(1)
                c.drawPath(path, fill=True, stroke=True)

        # Draw path edges
        if self.computed_paths and hasattr(self, '_all_triangulation_points'):
            c.setStrokeColor(hex_to_color(self.path_color))
            c.setLineWidth(self._get_path_width())
            for path in self.computed_paths:
                for i in range(len(path) - 1):
                    p1 = self._all_triangulation_points[path[i]]
                    p2 = self._all_triangulation_points[path[i + 1]]
                    c.line(p1[0], flip_y(p1[1]), p2[0], flip_y(p2[1]))

        # Draw outline (if visible)
        should_draw_outline = self.show_outline or not self.triangles
        if should_draw_outline and len(self.outline_points) >= 2:
            c.setStrokeColor(hex_to_color(self.outline_color))
            c.setLineWidth(2)

            for i in range(len(self.outline_points) - 1):
                p1, p2 = self.outline_points[i], self.outline_points[i + 1]
                c.line(p1[0], flip_y(p1[1]), p2[0], flip_y(p2[1]))

            # Close the outline if closed
            if self.outline_closed:
                p1, p2 = self.outline_points[-1], self.outline_points[0]
                c.line(p1[0], flip_y(p1[1]), p2[0], flip_y(p2[1]))

        # Draw vertices
        def draw_circle(point, color, radius):
            x, y = point
            c.setFillColor(hex_to_color(color))
            c.setStrokeColor(hex_to_color(color))
            c.circle(x, flip_y(y), radius, fill=True, stroke=False)

        def draw_square(point, color, size):
            x, y = point
            c.setFillColor(hex_to_color(color))
            c.setStrokeColor(hex_to_color(color))
            c.rect(x - size, flip_y(y) - size, size * 2, size * 2, fill=True, stroke=False)

        def draw_triangle_marker(point, color, size):
            x, y = point
            # Equilateral triangle pointing up (in PDF coordinates, down in screen coords)
            path = c.beginPath()
            path.moveTo(x, flip_y(y - size))  # Top
            path.lineTo(x - size, flip_y(y + size * 0.7))  # Bottom left
            path.lineTo(x + size, flip_y(y + size * 0.7))  # Bottom right
            path.close()
            c.setFillColor(hex_to_color(color))
            c.drawPath(path, fill=True, stroke=False)

        def draw_ring(point, color, radius):
            x, y = point
            c.setStrokeColor(hex_to_color(color))
            c.setLineWidth(2)
            c.circle(x, flip_y(y), radius, fill=False, stroke=True)

        if self.triangles and hasattr(self, '_all_triangulation_points'):
            # Collect path endpoints (first and last vertex of each path)
            path_endpoints = set()
            for p in self.computed_paths:
                if p:
                    path_endpoints.add(p[0])
                    path_endpoints.add(p[-1])

            for idx, point in enumerate(self._all_triangulation_points):
                if idx in self.path_vertices:
                    mark = self.vertex_sets.get(idx)
                    is_endpoint = idx in path_endpoints
                    if mark == 'red':
                        draw_square(point, self.red_set_color, self._get_point_radius() + 3)
                        if not is_endpoint:
                            draw_ring(point, self.path_color, self._get_point_radius() + 5)
                    elif mark == 'black':
                        draw_triangle_marker(point, self.black_set_color, self._get_point_radius() + 3)
                        if not is_endpoint:
                            draw_ring(point, self.path_color, self._get_point_radius() + 5)
                    else:
                        draw_circle(point, self.path_vertex_color, self._get_point_radius() + 2)
                elif idx in self.outer_face_vertices:
                    mark = self.vertex_sets.get(idx)
                    if mark == 'red':
                        draw_square(point, self.red_set_color, self._get_point_radius() + 3)
                    elif mark == 'black':
                        draw_triangle_marker(point, self.black_set_color, self._get_point_radius() + 3)
                    elif self.show_outline:
                        draw_circle(point, self.outline_color, self._get_point_radius() + 2)
                    else:
                        draw_circle(point, self.random_point_color, self._get_point_radius())
                else:
                    draw_circle(point, self.random_point_color, self._get_point_radius())
        else:
            for point in self.outline_points:
                draw_circle(point, self.outline_color, self._get_point_radius() + 2)
            for point in self.random_points:
                draw_circle(point, self.random_point_color, self._get_point_radius())

        # Save the PDF
        c.save()

        messagebox.showinfo("Export Complete", f"PDF exported to:\n{filepath}")

    def _reembed_graph(self):
        """Re-embed the graph using force-directed layout."""
        if not self.triangles or not hasattr(self, '_all_triangulation_points'):
            messagebox.showwarning("Warning", "No triangulation to re-embed")
            return

        # Get canvas dimensions for bounds
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        if canvas_width < 100:
            canvas_width = 800
        if canvas_height < 100:
            canvas_height = 500

        margin = 50
        target_width = canvas_width - 2 * margin
        target_height = canvas_height - 2 * margin

        # Run force-directed layout
        new_positions = self._force_directed_layout(
            self._all_triangulation_points,
            self.edges,
            iterations=200,
            width=target_width,
            height=target_height
        )

        # Offset to center in canvas
        for i in range(len(new_positions)):
            x, y = new_positions[i]
            new_positions[i] = (x + margin, y + margin)

        # Update positions
        self._all_triangulation_points = new_positions

        # Hide outline after re-embedding
        self.show_outline_var.set(False)
        self.show_outline = False

        self._redraw()
        self._update_status()

    def _force_directed_layout(
        self,
        positions: List[Point],
        edges: set,
        iterations: int = 200,
        width: float = 600,
        height: float = 400
    ) -> List[Point]:
        """Apply force-directed layout algorithm (Fruchterman-Reingold)."""
        n = len(positions)
        if n == 0:
            return []

        # Initialize with current positions, normalized to target area
        min_x = min(p[0] for p in positions)
        max_x = max(p[0] for p in positions)
        min_y = min(p[1] for p in positions)
        max_y = max(p[1] for p in positions)

        old_width = max(max_x - min_x, 1)
        old_height = max(max_y - min_y, 1)

        # Scale and center positions
        pos = []
        for p in positions:
            x = (p[0] - min_x) / old_width * width
            y = (p[1] - min_y) / old_height * height
            pos.append([x, y])

        # Optimal distance between vertices
        area = width * height
        k = math.sqrt(area / n) * 0.8

        # Temperature for simulated annealing
        temp = min(width, height) / 10

        for iteration in range(iterations):
            # Calculate repulsive forces between all pairs
            disp = [[0.0, 0.0] for _ in range(n)]

            for i in range(n):
                for j in range(i + 1, n):
                    dx = pos[i][0] - pos[j][0]
                    dy = pos[i][1] - pos[j][1]
                    dist = math.sqrt(dx * dx + dy * dy)
                    if dist < 0.01:
                        dist = 0.01

                    # Repulsive force
                    repulsion = (k * k) / dist
                    fx = (dx / dist) * repulsion
                    fy = (dy / dist) * repulsion

                    disp[i][0] += fx
                    disp[i][1] += fy
                    disp[j][0] -= fx
                    disp[j][1] -= fy

            # Calculate attractive forces for edges
            for edge in edges:
                i, j = edge
                dx = pos[i][0] - pos[j][0]
                dy = pos[i][1] - pos[j][1]
                dist = math.sqrt(dx * dx + dy * dy)
                if dist < 0.01:
                    dist = 0.01

                # Attractive force
                attraction = (dist * dist) / k
                fx = (dx / dist) * attraction
                fy = (dy / dist) * attraction

                disp[i][0] -= fx
                disp[i][1] -= fy
                disp[j][0] += fx
                disp[j][1] += fy

            # Apply displacements with temperature limiting
            for i in range(n):
                dx, dy = disp[i]
                dist = math.sqrt(dx * dx + dy * dy)
                if dist > 0:
                    # Limit displacement by temperature
                    limited_dist = min(dist, temp)
                    pos[i][0] += (dx / dist) * limited_dist
                    pos[i][1] += (dy / dist) * limited_dist

                # Keep within bounds
                pos[i][0] = max(0, min(width, pos[i][0]))
                pos[i][1] = max(0, min(height, pos[i][1]))

            # Cool down temperature
            temp *= 0.95

        return [(p[0], p[1]) for p in pos]

    def _clear_points(self):
        """Clear random points and triangulation."""
        self.random_points = []
        self.triangles = []
        self.edges = set()
        self.outer_face_vertices = set()
        self.vertex_sets = {}
        self.computed_paths = []
        self.path_vertices = set()
        self.forbidden_vertices = set()
        self.path_selection_mode = False
        self.path_source = None
        self.last_path_alternative = None
        self.path_status_var.set("")
        self._redraw()
        self._update_status()

    def _clear_all(self):
        """Clear everything."""
        self.outline_points = []
        self.outline_closed = False
        self.random_points = []
        self.triangles = []
        self.edges = set()
        self.is_drawing = False
        self.raw_points = []
        self.outer_face_vertices = set()
        self.vertex_sets = {}
        self.computed_paths = []
        self.path_vertices = set()
        self.forbidden_vertices = set()
        self.path_selection_mode = False
        self.path_source = None
        self.last_path_alternative = None
        self.path_status_var.set("")
        self.show_outline_var.set(True)
        self.show_outline = True
        self._redraw()
        self._update_status()

    def _redraw(self):
        """Redraw the entire canvas."""
        self.canvas.delete("all")

        # Draw triangulation
        if self.triangles and hasattr(self, '_all_triangulation_points'):
            for tri in self.triangles:
                points = [self._all_triangulation_points[i] for i in tri]
                coords = []
                for p in points:
                    coords.extend([p[0], p[1]])

                # Determine fill color based on whether any vertex is in forbidden region
                if any(v in self.forbidden_vertices for v in tri):
                    fill_color = self.forbidden_color
                else:
                    fill_color = self.triangle_fill_color

                # Draw filled triangle
                self.canvas.create_polygon(
                    coords,
                    fill=fill_color,
                    outline=self.edge_color,
                    width=1
                )

        # Draw path edges
        if self.computed_paths and hasattr(self, '_all_triangulation_points'):
            for path in self.computed_paths:
                for i in range(len(path) - 1):
                    p1 = self._all_triangulation_points[path[i]]
                    p2 = self._all_triangulation_points[path[i + 1]]
                    self.canvas.create_line(
                        p1[0], p1[1], p2[0], p2[1],
                        fill=self.path_color, width=self._get_path_width()
                    )

        # Draw outline (if visible and not yet triangulated, or if show_outline is True)
        should_draw_outline = self.show_outline or not self.triangles
        if should_draw_outline and len(self.outline_points) >= 2:
            for i in range(len(self.outline_points) - 1):
                p1, p2 = self.outline_points[i], self.outline_points[i + 1]
                self.canvas.create_line(
                    p1[0], p1[1], p2[0], p2[1],
                    fill=self.outline_color, width=2
                )

            # Close the outline if closed
            if self.outline_closed:
                p1, p2 = self.outline_points[-1], self.outline_points[0]
                self.canvas.create_line(
                    p1[0], p1[1], p2[0], p2[1],
                    fill=self.outline_color, width=2
                )

        # Draw vertices based on triangulation state
        if self.triangles and hasattr(self, '_all_triangulation_points'):
            # Collect path endpoints (first and last vertex of each path)
            path_endpoints = set()
            for path in self.computed_paths:
                if path:
                    path_endpoints.add(path[0])
                    path_endpoints.add(path[-1])

            # Draw all triangulation vertices with appropriate shapes
            for idx, point in enumerate(self._all_triangulation_points):
                # First check for path vertices (highest priority for non-marked)
                if idx in self.path_vertices:
                    # Check if this is also a marked vertex
                    mark = self.vertex_sets.get(idx)
                    is_endpoint = idx in path_endpoints
                    if mark == 'red':
                        self._draw_square(point, self.red_set_color, self._get_marker_size())
                        # Draw path indicator ring only for non-endpoints
                        if not is_endpoint:
                            self._draw_ring(point, self.path_color, self._get_marker_size() + 2)
                    elif mark == 'black':
                        self._draw_triangle_marker(point, self.black_set_color, self._get_marker_size())
                        if not is_endpoint:
                            self._draw_ring(point, self.path_color, self._get_marker_size() + 2)
                    else:
                        # Path vertex without red/black mark
                        self._draw_point(point, self.path_vertex_color, self._get_point_radius() + 2)
                elif idx in self.outer_face_vertices:
                    # Outer face vertex - check for marks
                    mark = self.vertex_sets.get(idx)
                    if mark == 'red':
                        self._draw_square(point, self.red_set_color, self._get_marker_size())
                    elif mark == 'black':
                        self._draw_triangle_marker(point, self.black_set_color, self._get_marker_size())
                    elif self.show_outline:
                        # Unmarked outer face vertex with outline visible - draw with highlight
                        self._draw_point(point, self.outline_color, self._get_point_radius() + 2)
                    else:
                        # Unmarked outer face vertex with outline hidden - draw as normal
                        self._draw_point(point, self.random_point_color, self._get_point_radius())
                else:
                    # Interior vertex
                    self._draw_point(point, self.random_point_color, self._get_point_radius())
        else:
            # No triangulation yet - draw outline and random points normally
            for point in self.outline_points:
                self._draw_point(point, self.outline_color, self._get_point_radius() + 2)

            for point in self.random_points:
                self._draw_point(point, self.random_point_color, self._get_point_radius())

    def _draw_point(self, point: Point, color: str, radius: int):
        """Draw a circular point on the canvas."""
        x, y = point
        self.canvas.create_oval(
            x - radius, y - radius, x + radius, y + radius,
            fill=color, outline=color
        )

    def _draw_square(self, point: Point, color: str, size: int):
        """Draw a square marker on the canvas."""
        x, y = point
        self.canvas.create_rectangle(
            x - size, y - size, x + size, y + size,
            fill=color, outline=color
        )

    def _draw_triangle_marker(self, point: Point, color: str, size: int):
        """Draw a triangle marker on the canvas."""
        x, y = point
        # Equilateral triangle pointing up
        coords = [
            x, y - size,  # Top
            x - size, y + size * 0.7,  # Bottom left
            x + size, y + size * 0.7   # Bottom right
        ]
        self.canvas.create_polygon(coords, fill=color, outline=color)

    def _draw_ring(self, point: Point, color: str, radius: int):
        """Draw a ring (unfilled circle) around a point."""
        x, y = point
        self.canvas.create_oval(
            x - radius, y - radius, x + radius, y + radius,
            fill='', outline=color, width=2
        )

    def _update_status(self):
        """Update the status bar."""
        if not self.outline_closed:
            if self.is_drawing:
                self.status_var.set(f"Drawing... {len(self.raw_points)} points captured")
            elif len(self.outline_points) == 0:
                if self.draw_mode_var.get() == "freehand":
                    self.status_var.set("Click and drag to draw an outline shape")
                else:
                    self.status_var.set("Click to start drawing an outline shape")
            elif len(self.outline_points) < 3:
                self.status_var.set(
                    f"Outline: {len(self.outline_points)} points - "
                    f"Add at least {3 - len(self.outline_points)} more"
                )
            else:
                self.status_var.set(
                    f"Outline: {len(self.outline_points)} points - "
                    f"Right-click to close shape"
                )
        else:
            status = f"Outline: {len(self.outline_points)} vertices (closed)"
            if self.random_points:
                status += f" | Random points: {len(self.random_points)}"
            if self.triangles:
                status += f" | Triangles: {len(self.triangles)}"
                # Count marked vertices
                red_count = sum(1 for v in self.vertex_sets.values() if v == 'red')
                black_count = sum(1 for v in self.vertex_sets.values() if v == 'black')
                if red_count or black_count:
                    status += f" | Red: {red_count}, Black: {black_count}"
                # Show path count
                if self.computed_paths:
                    status += f" | Paths: {len(self.computed_paths)}"
            self.status_var.set(status)


def main():
    root = tk.Tk()
    app = PlanarGraphWidget(root)
    root.mainloop()


if __name__ == "__main__":
    main()
