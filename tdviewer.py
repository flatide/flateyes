#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""tdviewer - minimal single-instance-per-display image viewer.

Designed for closed-network Linux hosts where only stock GNOME libraries
(GTK3, GdkPixbuf, PyGObject) are available.

Behaviour:
  * One viewer window per DISPLAY.  The first invocation opens the window;
    later invocations on the same DISPLAY hand the image path to the running
    window over a unix socket and exit immediately.
  * Different DISPLAY values get independent windows, so many user displays
    can be served at the same time.

Usage:
  DISPLAY=:1 tdviewer.py /path/to/image.jpg
"""

import errno
import math
import os
import signal
import socket
import sys
import tempfile
import time

APP = "tdviewer"

# GTK modules are imported lazily (only when this process becomes the window
# owner) so the frequent "forward and exit" path stays fast.
Gtk = Gdk = GdkPixbuf = GLib = None


# ---------------------------------------------------------------------------
# single-instance plumbing
# ---------------------------------------------------------------------------

def normalize_display(display):
    """':1.0' and ':1' are the same X display; drop the screen suffix."""
    display = display.strip()
    host, _, num = display.rpartition(":")
    if "." in num:
        num = num.split(".", 1)[0]
    return "%s:%s" % (host, num)


def socket_address(display):
    key = "%s-%d-%s" % (APP, os.getuid(), normalize_display(display))
    if sys.platform.startswith("linux"):
        # Abstract namespace: no socket file on disk, vanishes with the
        # process, so stale sockets are impossible.
        return "\0" + key
    base = os.environ.get("XDG_RUNTIME_DIR") or tempfile.gettempdir()
    return os.path.join(base, key.replace("/", "_") + ".sock")


def try_forward(addr, request):
    """Hand the request line ("image[\\tlegend]") to a running instance.

    Returns an exit code if an instance handled (or failed to handle) the
    request, or None when no instance is listening.
    """
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    sock.settimeout(5.0)
    try:
        sock.connect(addr)
    except OSError:
        sock.close()
        return None
    try:
        sock.sendall(request.encode("utf-8") + b"\n")
        reply = b""
        while b"\n" not in reply and len(reply) < 65536:
            chunk = sock.recv(4096)
            if not chunk:
                break
            reply += chunk
    except OSError:
        sys.stderr.write("%s: existing instance did not respond\n" % APP)
        return 1
    finally:
        sock.close()
    text = reply.decode("utf-8", "replace").strip()
    if text.startswith("OK"):
        return 0
    sys.stderr.write("%s\n" % (text or "%s: empty reply from existing instance" % APP))
    return 1


def try_bind(addr):
    """Become the instance owner.  Returns a listening socket or None if
    another process owns (or just grabbed) the address."""
    for _ in range(2):
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            sock.bind(addr)
            sock.listen(8)
            return sock
        except OSError as exc:
            sock.close()
            if exc.errno != errno.EADDRINUSE:
                raise
            if addr.startswith("\0"):
                return None
            # Filesystem socket: unlink only if nothing is listening there,
            # otherwise we would steal a live instance's socket.
            probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            probe.settimeout(1.0)
            try:
                probe.connect(addr)
            except OSError:
                pass  # dead leftover; safe to remove
            else:
                return None
            finally:
                probe.close()
            try:
                os.unlink(addr)
            except OSError:
                return None
    return None


# ---------------------------------------------------------------------------
# stack manifest (mip-map style multi-magnification sets)
# ---------------------------------------------------------------------------

def parse_stack_file(path):
    """Parse a stack manifest: one key=value per line, "#" comments.

      unit=um            optional, ruler unit for the whole stack
      level=IMAGE_PATH   starts a level (path relative to the manifest)
      ppu=N              required per level: pixels per unit
      center=X,Y         optional per level: center offset in units,
                         to correct slightly misaligned captures

    Returns (levels, unit, error); levels sorted by ascending ppu.
    """
    try:
        with open(path, "r", encoding="utf-8") as handle:
            lines = handle.read().splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        return None, None, "ERR %s: %s" % (path, exc)
    base_dir = os.path.dirname(os.path.abspath(path))
    unit = None
    levels = []
    for number, raw in enumerate(lines, 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        key, sep, value = line.partition("=")
        key, value = key.strip(), value.strip()
        if not sep or not value:
            return None, None, "ERR %s:%d: expected key=value" % (path, number)
        if key == "unit":
            unit = value
        elif key == "level":
            if not os.path.isabs(value):
                value = os.path.normpath(os.path.join(base_dir, value))
            levels.append({"path": value, "ppu": None, "center": (0.0, 0.0)})
        elif key == "ppu":
            if not levels:
                return None, None, "ERR %s:%d: ppu before any level" \
                    % (path, number)
            try:
                ppu = float(value)
            except ValueError:
                ppu = 0
            if ppu <= 0:
                return None, None, "ERR %s:%d: bad ppu: %s" \
                    % (path, number, value)
            levels[-1]["ppu"] = ppu
        elif key == "center":
            if not levels:
                return None, None, "ERR %s:%d: center before any level" \
                    % (path, number)
            try:
                x, y = [float(v) for v in value.split(",")]
            except ValueError:
                return None, None, "ERR %s:%d: bad center: %s" \
                    % (path, number, value)
            levels[-1]["center"] = (x, y)
        # unknown keys are ignored for forward compatibility
    if not levels:
        return None, None, "ERR %s: no levels" % path
    for level in levels:
        if level["ppu"] is None:
            return None, None, "ERR %s: missing ppu for %s" \
                % (path, level["path"])
        if not os.path.isfile(level["path"]):
            return None, None, "ERR no such file: %s" % level["path"]
    levels.sort(key=lambda level: level["ppu"])
    return levels, unit, None


# ---------------------------------------------------------------------------
# viewer window (GTK)
# ---------------------------------------------------------------------------

def import_gtk():
    global Gtk, Gdk, GdkPixbuf, GLib
    try:
        import gi
        gi.require_version("Gtk", "3.0")
        gi.require_version("GdkPixbuf", "2.0")
        from gi.repository import Gtk as _Gtk, Gdk as _Gdk, \
            GdkPixbuf as _GdkPixbuf, GLib as _GLib
    except (ImportError, ValueError) as exc:
        sys.stderr.write(
            "%s: PyGObject/GTK3 is required to open a window (%s)\n"
            "  verify with: python3 -c 'import gi; gi.require_version(\"Gtk\", \"3.0\")'\n"
            % (APP, exc))
        sys.exit(3)
    Gtk, Gdk, GdkPixbuf, GLib = _Gtk, _Gdk, _GdkPixbuf, _GLib


def workarea_size():
    try:
        display = Gdk.Display.get_default()
        monitor = display.get_primary_monitor() or display.get_monitor(0)
        area = monitor.get_workarea()
        return area.width, area.height
    except AttributeError:  # GTK < 3.22
        screen = Gdk.Screen.get_default()
        return screen.get_width(), screen.get_height()


class Viewer(object):
    ZOOM_STEP = 1.25
    ZOOM_MIN = 0.05
    ZOOM_MAX = 2.0
    LEGEND_FRACTION = 1.0 / 3.0  # max legend size relative to the window
    RULER_CASING = 0x000000B4    # guide line outline, 0xRRGGBBAA
    RULER_CORE = 0xFFD819FF      # guide line core
    HINT_CASING = 0x00000090     # next-level coverage outline
    HINT_CORE = 0x33BBFFFF

    def __init__(self, server_sock, first_path, first_legend=None,
                 ppu=None, unit=None, stack=False, levels=None):
        self.server_sock = server_sock
        self.path = None
        self.pixbuf = None          # active level (already orientation-fixed)
        self.animation = None       # animated image (shown unscaled)
        self.fit_mode = True
        self.scale_shown = 1.0      # rendered scale of the active level
        self.rendered_size = None
        self.ppu = ppu              # pixels per unit (single-image ruler)
        self.unit = unit or "um"
        # A single image is a one-level stack with ppu=1, so "world"
        # coordinates equal its pixels.  Real stacks put every level into
        # a shared world (units around the common capture center) and the
        # zoom state is view_scale: screen pixels per world unit.
        self.stack_mode = False
        self.levels = []            # [{path, ppu, center, pixbuf}] by ppu
        self.level_index = 0
        self.view_scale = 1.0
        self.pending_center = None  # world point to re-center on after render
        # Overlay visibility: per-element switches plus a master switch
        # (Tab) that hides everything without losing the per-element state.
        self.aux_visible = True     # Tab
        self.legend_enabled = True  # "l"
        self.hint_enabled = True    # "o"

        self.window = Gtk.Window(title=APP)
        self.window.connect("destroy", lambda *a: Gtk.main_quit())
        self.window.connect("key-press-event", self.on_key)
        self.window.connect("focus-in-event", self.on_focus_in)

        self.image = Gtk.Image()
        self.scroll = Gtk.ScrolledWindow()
        self.scroll.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        self.scroll.add(self.image)
        self.scroll.add_events(Gdk.EventMask.SCROLL_MASK |
                               Gdk.EventMask.SMOOTH_SCROLL_MASK |
                               Gdk.EventMask.BUTTON_PRESS_MASK |
                               Gdk.EventMask.BUTTON_RELEASE_MASK |
                               Gdk.EventMask.POINTER_MOTION_MASK |
                               Gdk.EventMask.BUTTON1_MOTION_MASK)
        self.scroll.connect("scroll-event", self.on_scroll)
        self.scroll.connect("button-press-event", self.on_button_press)
        self.scroll.connect("motion-notify-event", self.on_motion)
        self.scroll.connect("button-release-event", self.on_button_release)
        self.scroll.connect("size-allocate", self.on_size_allocate)
        self.drag_origin = None
        self.rescale_pending = None
        self.image.connect("size-allocate", self.on_image_allocate)

        # Ruler: points live in world coordinates so they stay
        # anchored to the picture across zooming and scrolling.  The line
        # and the readout are overlay widgets placed in viewport
        # coordinates: the target hosts lack pycairo, so nothing can be
        # painted from a "draw" signal handler.
        self.ruler_active = False
        self.ruler_start = None
        self.ruler_end = None       # second point, once fixed
        self.ruler_cursor = None    # live preview point while picking
        self.ruler_drawn = None     # geometry of the rendered overlays
        self.ruler_line = Gtk.Image()
        self.ruler_label = Gtk.Label()
        # Stack hint: outline of the area the next magnification covers.
        self.hint_drawn = None
        self.hint_image = Gtk.Image()
        for widget in (self.ruler_line, self.ruler_label, self.hint_image):
            widget.set_halign(Gtk.Align.START)
            widget.set_valign(Gtk.Align.START)
            widget.set_no_show_all(True)
        self.ruler_label.set_name("tdviewer-ruler")
        css = Gtk.CssProvider()
        css.load_from_data(
            b"#tdviewer-ruler { background-color: rgba(0,0,0,0.78);"
            b" color: #ffffff; padding: 2px 7px; border-radius: 3px;"
            b" font-weight: bold; }")
        self.ruler_label.get_style_context().add_provider(
            css, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        for adj in (self.scroll.get_hadjustment(),
                    self.scroll.get_vadjustment()):
            adj.connect("value-changed",
                        lambda *a: self.update_view_overlays())

        # Legend: optional second image overlaid at the bottom-right corner.
        self.legend_pixbuf = None
        self.legend_rendered = None
        self.legend_image = Gtk.Image()
        self.legend_frame = Gtk.Frame()
        self.legend_frame.add(self.legend_image)
        self.legend_frame.set_halign(Gtk.Align.END)
        self.legend_frame.set_valign(Gtk.Align.END)
        self.legend_frame.set_margin_end(12)
        self.legend_frame.set_margin_bottom(12)
        self.legend_frame.set_no_show_all(True)

        self.overlay = Gtk.Overlay()
        self.overlay.add(self.scroll)
        self.overlay.add_overlay(self.legend_frame)
        self.overlay.add_overlay(self.hint_image)
        self.overlay.add_overlay(self.ruler_line)
        self.overlay.add_overlay(self.ruler_label)
        for child in (self.legend_frame, self.hint_image,
                      self.ruler_line, self.ruler_label):
            try:
                # Let clicks/wheel over the overlays fall through to the image.
                self.overlay.set_overlay_pass_through(child, True)
            except AttributeError:  # GTK < 3.18
                break
        self.overlay.connect("size-allocate", self.on_overlay_allocate)
        self.window.add(self.overlay)

        error = self.load(first_path, first_legend, stack=stack,
                          levels=levels)
        if error != "OK":
            sys.stderr.write("%s\n" % error)
            sys.exit(1)

        self.set_initial_size()
        self.window.show_all()

        GLib.io_add_watch(server_sock.fileno(), GLib.IO_IN, self.on_incoming)
        for signum in (signal.SIGINT, signal.SIGTERM):
            try:
                GLib.unix_signal_add(GLib.PRIORITY_DEFAULT, signum,
                                     lambda *a: (Gtk.main_quit(), False)[1])
            except AttributeError:
                pass

    # -- image loading -----------------------------------------------------

    def load(self, path, legend_path=None, ppu=None, unit=None, stack=False,
             levels=None):
        stack = stack or levels is not None
        if not os.path.isfile(path):
            return "ERR no such file: %s" % path
        # Decode the legend first so a bad legend leaves the window untouched.
        legend_pixbuf = None
        if legend_path:
            if not os.path.isfile(legend_path):
                return "ERR no such file: %s" % legend_path
            try:
                legend_pixbuf = GdkPixbuf.Pixbuf.new_from_file(legend_path)
                legend_pixbuf = legend_pixbuf.apply_embedded_orientation() \
                    or legend_pixbuf
            except GLib.Error as exc:
                return "ERR %s: %s" % (legend_path, exc.message)
        animation = None
        stack_unit = None
        if stack:
            if levels is None:  # manifest file
                metas, stack_unit, error = parse_stack_file(path)
                if error:
                    return error
            else:               # inline levels from the command line
                metas = sorted(levels, key=lambda meta: meta["ppu"] or 0)
                for meta in metas:
                    if not meta["ppu"] or meta["ppu"] <= 0:
                        return "ERR missing ppu for %s" % meta["path"]
                    if not os.path.isfile(meta["path"]):
                        return "ERR no such file: %s" % meta["path"]
            levels = []
            for meta in metas:
                try:
                    pixbuf = GdkPixbuf.Pixbuf.new_from_file(meta["path"])
                    pixbuf = pixbuf.apply_embedded_orientation() or pixbuf
                except GLib.Error as exc:
                    return "ERR %s: %s" % (meta["path"], exc.message)
                levels.append(dict(meta, pixbuf=pixbuf))
        else:
            info = GdkPixbuf.Pixbuf.get_file_info(path)
            fmt = info[0] if isinstance(info, tuple) else info
            if fmt is None:
                return "ERR unsupported image format: %s" % path
            try:
                if fmt.get_name() == "gif":
                    animation = GdkPixbuf.PixbufAnimation.new_from_file(path)
                    pixbuf = None
                else:
                    pixbuf = GdkPixbuf.Pixbuf.new_from_file(path)
                    pixbuf = pixbuf.apply_embedded_orientation() or pixbuf
            except GLib.Error as exc:
                return "ERR %s: %s" % (path, exc.message)
            levels = [{"path": path, "ppu": 1.0, "center": (0.0, 0.0),
                       "pixbuf": pixbuf}]

        self.path = path
        self.stack_mode = stack
        self.levels = levels
        self.level_index = 0
        self.animation = animation
        self.pixbuf = levels[0]["pixbuf"]
        self.fit_mode = True
        self.view_scale = levels[0]["ppu"]
        self.pending_center = None
        self.rendered_size = None
        # PPU/unit are sticky: only overwritten when the request carries
        # them.  A stack manifest wins over stickiness, an explicit request
        # field wins over the manifest.
        if stack_unit:
            self.unit = stack_unit
        if ppu is not None:
            self.ppu = ppu
        if unit is not None:
            self.unit = unit
        self.set_ruler_active(False)
        self.legend_pixbuf = legend_pixbuf
        self.legend_rendered = None
        if legend_pixbuf is not None:
            self.render_legend()
        else:
            self.legend_image.clear()
        self.legend_enabled = True  # a new request always shows its legend
        self.apply_legend_visibility()
        if self.pixbuf is not None:
            self.rescale()
        else:
            self.image.set_from_animation(self.animation)
            self.scale_shown = 1.0
            self.update_title()
        return "OK"

    def image_size(self):
        if self.pixbuf is not None:
            return self.pixbuf.get_width(), self.pixbuf.get_height()
        return self.animation.get_width(), self.animation.get_height()

    def set_initial_size(self):
        max_w, max_h = [int(v * 0.9) for v in workarea_size()]
        img_w, img_h = self.image_size()
        self.window.set_default_size(max(min(img_w + 4, max_w), 320),
                                     max(min(img_h + 4, max_h), 240))

    # -- scaling -----------------------------------------------------------

    def rescale(self, alloc=None):
        if self.pixbuf is None:
            return
        img_w, img_h = self.pixbuf.get_width(), self.pixbuf.get_height()
        if self.fit_mode:
            if alloc is None:
                alloc = self.scroll.get_allocation()
            if alloc.width < 2 or alloc.height < 2:
                scale = 1.0  # not realized yet; size-allocate will re-fit
            else:
                scale = min((alloc.width - 2.0) / img_w,
                            (alloc.height - 2.0) / img_h, 1.0)
        else:
            scale = self.view_scale / self.active_level()["ppu"]
            scale = max(self.ZOOM_MIN, min(scale, self.ZOOM_MAX))
        width = max(1, int(round(img_w * scale)))
        height = max(1, int(round(img_h * scale)))
        if (width, height) == self.rendered_size:
            return
        self.rendered_size = (width, height)
        self.scale_shown = scale
        if (width, height) == (img_w, img_h):
            self.image.set_from_pixbuf(self.pixbuf)
        else:
            self.image.set_from_pixbuf(self.pixbuf.scale_simple(
                width, height, GdkPixbuf.InterpType.BILINEAR))
        self.update_title()
        self.update_view_overlays()

    def active_level(self):
        return self.levels[self.level_index]

    def current_view_scale(self):
        """Zoom target in screen px per world unit, incl. pending ones."""
        if not self.fit_mode and self.rescale_pending is not None:
            return self.view_scale
        return self.scale_shown * self.active_level()["ppu"]

    def set_view_scale(self, value):
        if self.pixbuf is None:
            return
        self.fit_mode = False
        self.view_scale = max(self.ZOOM_MIN * self.levels[0]["ppu"],
                              min(value,
                                  self.ZOOM_MAX * self.levels[-1]["ppu"]))
        # Rescaling a large pixbuf is expensive; render once the burst of
        # zoom events (fast wheel spins) has been consumed instead of once
        # per event.
        if self.rescale_pending is None:
            self.rescale_pending = GLib.idle_add(self.on_rescale_idle)

    def on_rescale_idle(self):
        self.rescale_pending = None
        if self.pixbuf is None:
            return False
        if self.fit_mode:
            self.rescale()
            return False
        center = self.viewport_center_world()
        index = self.select_level(self.view_scale, center)
        if index != self.level_index:
            self.level_index = index
            self.pixbuf = self.levels[index]["pixbuf"]
            self.rendered_size = None
        self.pending_center = center
        before = self.rendered_size
        self.rescale()
        # Reflect the clamps applied while rendering.
        self.view_scale = self.scale_shown * self.active_level()["ppu"]
        if self.rendered_size == before:
            # No allocation change coming; re-center right away.
            self.apply_pending_center()
        return False

    def select_level(self, view_scale, center):
        """Pick the stack level for a target scale.  Prefer levels that
        cover the whole viewport without upscaling; accept center-only
        coverage rather than stalling below the deepest magnification."""
        if len(self.levels) == 1:
            return 0
        if center is None:
            return self.level_index
        view = self.scroll.get_allocation()
        half_w = view.width / 2.0 / view_scale
        half_h = view.height / 2.0 / view_scale
        eps = 2.0 / view_scale  # tolerate a couple of screen pixels
        full = []
        partial = []
        for i, level in enumerate(self.levels):
            ext_x = level["pixbuf"].get_width() / 2.0 / level["ppu"]
            ext_y = level["pixbuf"].get_height() / 2.0 / level["ppu"]
            dx = abs(center[0] - level["center"][0])
            dy = abs(center[1] - level["center"][1])
            if dx <= ext_x + eps and dy <= ext_y + eps:
                partial.append(i)
                if dx + half_w <= ext_x + eps and dy + half_h <= ext_y + eps:
                    full.append(i)
        for i in full:  # sorted by ppu: lowest sufficient level wins
            if self.levels[i]["ppu"] >= view_scale:
                return i
        # No covering level is sharp enough.  Upscaling one beats showing
        # a partial patch as long as it stays within the zoom ceiling.
        if full and view_scale / self.levels[full[-1]]["ppu"] <= self.ZOOM_MAX:
            return full[-1]
        for i in partial:
            if self.levels[i]["ppu"] >= view_scale:
                return i
        if partial:
            return partial[-1]  # deepest magnification that still covers
        return 0

    # -- world coordinates ---------------------------------------------------

    def world_from_px(self, point, index=None):
        level = self.levels[self.level_index if index is None else index]
        pixbuf = level["pixbuf"]
        return ((point[0] - pixbuf.get_width() / 2.0) / level["ppu"]
                + level["center"][0],
                (point[1] - pixbuf.get_height() / 2.0) / level["ppu"]
                + level["center"][1])

    def px_from_world(self, point, index=None):
        level = self.levels[self.level_index if index is None else index]
        pixbuf = level["pixbuf"]
        return ((point[0] - level["center"][0]) * level["ppu"]
                + pixbuf.get_width() / 2.0,
                (point[1] - level["center"][1]) * level["ppu"]
                + pixbuf.get_height() / 2.0)

    def viewport_center_world(self):
        if self.rendered_size is None:
            return None
        alloc = self.image.get_allocation()
        rend_w, rend_h = self.rendered_size
        hadj = self.scroll.get_hadjustment()
        vadj = self.scroll.get_vadjustment()
        x = hadj.get_value() + hadj.get_page_size() / 2.0 \
            - max(0, (alloc.width - rend_w) // 2)
        y = vadj.get_value() + vadj.get_page_size() / 2.0 \
            - max(0, (alloc.height - rend_h) // 2)
        return self.world_from_px((x / self.scale_shown,
                                   y / self.scale_shown))

    def apply_pending_center(self, alloc=None):
        if self.pending_center is None or self.rendered_size is None:
            return
        center = self.pending_center
        self.pending_center = None
        if alloc is None:
            alloc = self.image.get_allocation()
        px = self.px_from_world(center)
        rend_w, rend_h = self.rendered_size
        hadj = self.scroll.get_hadjustment()
        vadj = self.scroll.get_vadjustment()
        hadj.set_value(max(0, (alloc.width - rend_w) // 2)
                       + px[0] * self.scale_shown
                       - hadj.get_page_size() / 2.0)
        vadj.set_value(max(0, (alloc.height - rend_h) // 2)
                       + px[1] * self.scale_shown
                       - vadj.get_page_size() / 2.0)

    def on_image_allocate(self, widget, allocation):
        # Fires after a rescaled/swapped pixbuf got its new allocation and
        # the scroll adjustments were refreshed; safe to re-center now.
        self.apply_pending_center(allocation)

    def update_title(self):
        name = os.path.basename(self.path or "")
        img_w, img_h = self.image_size()
        if self.animation is not None:
            detail = "%dx%d animation" % (img_w, img_h)
        elif self.stack_mode:
            level = self.active_level()
            detail = "%d/%d %s  %dx%d  %d%%  %.4g px/%s" % (
                self.level_index + 1, len(self.levels),
                os.path.basename(level["path"]), img_w, img_h,
                round(self.scale_shown * 100), level["ppu"], self.unit)
        else:
            detail = "%dx%d  %d%%" % (img_w, img_h, round(self.scale_shown * 100))
        self.window.set_title("%s  (%s) - %s" % (name, detail, APP))

    # -- legend overlay ------------------------------------------------------

    def render_legend(self, alloc=None):
        """Scale the legend down (never up) to a corner-sized inset."""
        if self.legend_pixbuf is None:
            return
        if alloc is None:
            alloc = self.overlay.get_allocation()
        img_w = self.legend_pixbuf.get_width()
        img_h = self.legend_pixbuf.get_height()
        if alloc.width < 2 or alloc.height < 2:
            scale = 1.0  # not realized yet; size-allocate will re-fit
        else:
            scale = min(alloc.width * self.LEGEND_FRACTION / img_w,
                        alloc.height * self.LEGEND_FRACTION / img_h, 1.0)
        width = max(1, int(round(img_w * scale)))
        height = max(1, int(round(img_h * scale)))
        if (width, height) == self.legend_rendered:
            return
        self.legend_rendered = (width, height)
        if (width, height) == (img_w, img_h):
            self.legend_image.set_from_pixbuf(self.legend_pixbuf)
        else:
            self.legend_image.set_from_pixbuf(self.legend_pixbuf.scale_simple(
                width, height, GdkPixbuf.InterpType.BILINEAR))

    def apply_legend_visibility(self):
        if self.legend_pixbuf is not None and self.legend_enabled \
                and self.aux_visible:
            self.legend_image.show()
            self.legend_frame.show()
        else:
            self.legend_frame.hide()

    def on_overlay_allocate(self, widget, allocation):
        self.render_legend(allocation)

    # -- ruler ---------------------------------------------------------------

    def set_ruler_active(self, active):
        if active and self.pixbuf is None:
            return  # animations are shown unscaled and unmeasured
        if active and not self.aux_visible:
            self.aux_visible = True  # measuring needs the overlays back
            self.apply_legend_visibility()
        self.ruler_active = active
        self.ruler_start = self.ruler_end = self.ruler_cursor = None
        self.set_viewport_cursor("crosshair" if active else None)
        self.update_view_overlays()

    def event_to_image_px(self, event):
        """Map a pointer event to image-pixel coordinates (clamped)."""
        win = self.image.get_window()
        if win is None or self.rendered_size is None:
            return None
        _, org_x, org_y = win.get_origin()
        alloc = self.image.get_allocation()
        x = event.x_root - org_x - alloc.x
        y = event.y_root - org_y - alloc.y
        # GtkImage centers the pixbuf inside its allocation.
        rend_w, rend_h = self.rendered_size
        x -= max(0, (alloc.width - rend_w) // 2)
        y -= max(0, (alloc.height - rend_h) // 2)
        img_w, img_h = self.image_size()
        return (min(max(x / self.scale_shown, 0.0), img_w),
                min(max(y / self.scale_shown, 0.0), img_h))

    def event_to_world(self, event):
        point = self.event_to_image_px(event)
        return None if point is None else self.world_from_px(point)

    def format_distance(self, dist_world):
        if self.stack_mode:
            # world units come straight from the manifest ppu values
            px = dist_world * self.active_level()["ppu"]
            return "%.2f %s  (%d px)" % (dist_world, self.unit, round(px))
        if self.ppu:
            return "%.2f %s  (%d px)" % (dist_world / self.ppu, self.unit,
                                         round(dist_world))
        return "%d px" % round(dist_world)

    def snap_point(self, point, state):
        """Constrain to the dominant axis unless Shift asks for free angle."""
        if state & Gdk.ModifierType.SHIFT_MASK:
            return point
        ax, ay = self.ruler_start
        if abs(point[0] - ax) >= abs(point[1] - ay):
            return (point[0], ay)
        return (ax, point[1])

    def image_px_to_widget(self, point):
        alloc = self.image.get_allocation()
        rend_w, rend_h = self.rendered_size
        return (max(0, (alloc.width - rend_w) // 2) +
                point[0] * self.scale_shown,
                max(0, (alloc.height - rend_h) // 2) +
                point[1] * self.scale_shown)

    def image_px_to_view(self, point):
        """Image pixels -> coordinates inside the visible viewport."""
        wx, wy = self.image_px_to_widget(point)
        return (wx - self.scroll.get_hadjustment().get_value(),
                wy - self.scroll.get_vadjustment().get_value())

    def update_ruler_overlay(self):
        if not self.ruler_active or not self.aux_visible \
                or self.ruler_start is None or self.rendered_size is None:
            self.ruler_drawn = None
            self.ruler_line.hide()
            self.ruler_label.hide()
            return
        end = self.ruler_end if self.ruler_end is not None \
            else self.ruler_cursor
        view = self.scroll.get_allocation()
        a = self.image_px_to_view(self.px_from_world(self.ruler_start))
        b = self.image_px_to_view(self.px_from_world(end)) \
            if end is not None else a
        key = (a, b, end is None, self.ppu, self.unit, self.level_index,
               view.width, view.height)
        if key == self.ruler_drawn:
            return  # also breaks the redraw->allocate->redraw cycle
        self.ruler_drawn = key
        self.draw_ruler_line(a, b, view)
        if end is None:
            self.ruler_label.hide()
            return
        dist = math.hypot(end[0] - self.ruler_start[0],
                          end[1] - self.ruler_start[1])
        self.ruler_label.set_text(self.format_distance(dist))
        _, nat = self.ruler_label.get_preferred_size()
        x = (a[0] + b[0]) / 2 + 12
        y = (a[1] + b[1]) / 2 - nat.height - 12
        x = max(2, min(x, view.width - nat.width - 2))
        y = max(2, min(y, view.height - nat.height - 2))
        self.ruler_label.set_margin_start(int(x))
        self.ruler_label.set_margin_top(int(y))
        self.ruler_label.show()

    def draw_ruler_line(self, a, b, view):
        """Render line + end markers into a transparent pixbuf covering
        the viewport-clipped bounding box of the segment."""
        pad = 4
        x0 = int(max(min(a[0], b[0]) - pad, 0))
        y0 = int(max(min(a[1], b[1]) - pad, 0))
        x1 = int(min(max(a[0], b[0]) + pad, view.width))
        y1 = int(min(max(a[1], b[1]) + pad, view.height))
        if x1 - x0 < 1 or y1 - y0 < 1:
            self.ruler_line.hide()  # segment entirely outside the view
            return
        buf = GdkPixbuf.Pixbuf.new(GdkPixbuf.Colorspace.RGB, True, 8,
                                   x1 - x0, y1 - y0)
        buf.fill(0x00000000)
        ax, ay = a[0] - x0, a[1] - y0
        bx, by = b[0] - x0, b[1] - y0
        if a != b:
            if ay == by:    # horizontal
                self.fill_rect(buf, min(ax, bx), ay - 1,
                               abs(bx - ax) + 1, 3, self.RULER_CASING)
                self.fill_rect(buf, min(ax, bx), ay,
                               abs(bx - ax) + 1, 1, self.RULER_CORE)
            elif ax == bx:  # vertical
                self.fill_rect(buf, ax - 1, min(ay, by),
                               3, abs(by - ay) + 1, self.RULER_CASING)
                self.fill_rect(buf, ax, min(ay, by),
                               1, abs(by - ay) + 1, self.RULER_CORE)
            else:           # free angle: dense square dabs along the segment
                steps = min(int(max(abs(bx - ax), abs(by - ay)) / 2) + 1,
                            2000)
                points = [(ax + (bx - ax) * i / steps,
                           ay + (by - ay) * i / steps)
                          for i in range(steps + 1)]
                for x, y in points:
                    self.fill_rect(buf, x - 1, y - 1, 3, 3,
                                   self.RULER_CASING)
                for x, y in points:
                    self.fill_rect(buf, x, y, 1, 1, self.RULER_CORE)
        for x, y in ((ax, ay), (bx, by)):
            self.fill_rect(buf, x - 3, y - 3, 7, 7, self.RULER_CASING)
            self.fill_rect(buf, x - 2, y - 2, 5, 5, self.RULER_CORE)
        self.ruler_line.set_from_pixbuf(buf)
        self.ruler_line.set_margin_start(x0)
        self.ruler_line.set_margin_top(y0)
        self.ruler_line.show()

    @staticmethod
    def fill_rect(buf, x, y, w, h, rgba):
        x, y, w, h = int(round(x)), int(round(y)), int(round(w)), int(round(h))
        if x < 0:
            w += x
            x = 0
        if y < 0:
            h += y
            y = 0
        w = min(w, buf.get_width() - x)
        h = min(h, buf.get_height() - y)
        if w > 0 and h > 0:
            buf.new_subpixbuf(x, y, w, h).fill(rgba)

    # -- next-level coverage hint --------------------------------------------

    def update_view_overlays(self):
        self.update_ruler_overlay()
        self.update_hint_overlay()

    def update_hint_overlay(self):
        """Outline the area the next magnification level covers."""
        if not self.stack_mode or not self.hint_enabled \
                or not self.aux_visible or self.rendered_size is None \
                or self.level_index >= len(self.levels) - 1:
            self.hint_drawn = None
            self.hint_image.hide()
            return
        nxt = self.levels[self.level_index + 1]
        ext_x = nxt["pixbuf"].get_width() / 2.0 / nxt["ppu"]
        ext_y = nxt["pixbuf"].get_height() / 2.0 / nxt["ppu"]
        a = self.image_px_to_view(self.px_from_world(
            (nxt["center"][0] - ext_x, nxt["center"][1] - ext_y)))
        b = self.image_px_to_view(self.px_from_world(
            (nxt["center"][0] + ext_x, nxt["center"][1] + ext_y)))
        view = self.scroll.get_allocation()
        key = (a, b, self.level_index, view.width, view.height)
        if key == self.hint_drawn:
            return
        self.hint_drawn = key
        x0 = int(max(a[0] - 2, 0))
        y0 = int(max(a[1] - 2, 0))
        x1 = int(min(b[0] + 2, view.width))
        y1 = int(min(b[1] + 2, view.height))
        if x1 - x0 < 1 or y1 - y0 < 1:
            self.hint_image.hide()  # outline entirely outside the view
            return
        buf = GdkPixbuf.Pixbuf.new(GdkPixbuf.Colorspace.RGB, True, 8,
                                   x1 - x0, y1 - y0)
        buf.fill(0x00000000)
        ax, ay = a[0] - x0, a[1] - y0
        bx, by = b[0] - x0, b[1] - y0
        for width, rgba in ((3, self.HINT_CASING), (1, self.HINT_CORE)):
            off = width // 2
            self.fill_rect(buf, ax - off, ay - off,
                           bx - ax + width, width, rgba)   # top
            self.fill_rect(buf, ax - off, by - off,
                           bx - ax + width, width, rgba)   # bottom
            self.fill_rect(buf, ax - off, ay - off,
                           width, by - ay + width, rgba)   # left
            self.fill_rect(buf, bx - off, ay - off,
                           width, by - ay + width, rgba)   # right
        self.hint_image.set_from_pixbuf(buf)
        self.hint_image.set_margin_start(x0)
        self.hint_image.set_margin_top(y0)
        self.hint_image.show()

    def ask_ppu(self):
        dialog = Gtk.Dialog(title="PPU", transient_for=self.window,
                            modal=True)
        dialog.add_button("Cancel", Gtk.ResponseType.CANCEL)
        dialog.add_button("OK", Gtk.ResponseType.OK)
        dialog.set_default_response(Gtk.ResponseType.OK)
        entry = Gtk.Entry()
        if self.ppu:
            entry.set_text("%g" % self.ppu)
        entry.set_activates_default(True)
        box = dialog.get_content_area()
        box.set_border_width(10)
        box.set_spacing(6)
        box.pack_start(Gtk.Label(label="1 %s = ? pixels" % self.unit),
                       False, False, 0)
        box.pack_start(entry, False, False, 0)
        dialog.show_all()
        if dialog.run() == Gtk.ResponseType.OK:
            text = entry.get_text().strip()
            if not text:
                self.ppu = None  # back to plain pixel readout
            else:
                try:
                    value = float(text)
                except ValueError:
                    value = 0
                if value > 0:
                    self.ppu = value
        dialog.destroy()
        self.update_ruler_overlay()

    # -- events ------------------------------------------------------------

    def on_size_allocate(self, widget, allocation):
        if self.fit_mode:
            self.rescale(allocation)
        self.update_view_overlays()

    def on_key(self, widget, event):
        key = Gdk.keyval_name(event.keyval)
        if key in ("q", "Q"):
            Gtk.main_quit()
        elif key == "Escape":
            if self.ruler_active:
                self.set_ruler_active(False)
            else:
                Gtk.main_quit()
        elif key in ("r", "R"):
            self.set_ruler_active(not self.ruler_active)
        elif key in ("p", "P"):
            if not self.stack_mode:  # stack ppu comes from the manifest
                self.ask_ppu()
        elif key in ("plus", "equal", "KP_Add"):
            self.set_view_scale(self.current_view_scale() * self.ZOOM_STEP)
        elif key in ("minus", "KP_Subtract"):
            self.set_view_scale(self.current_view_scale() / self.ZOOM_STEP)
        elif key in ("1", "KP_1"):
            self.set_view_scale(self.active_level()["ppu"])
        elif key in ("f", "0", "KP_0"):
            self.fit_mode = True
            if self.level_index != 0:
                self.level_index = 0
                self.pixbuf = self.levels[0]["pixbuf"]
                self.rendered_size = None
            self.rescale()
        elif key in ("bracketright", "bracketleft"):
            # jump to 100% of the neighbouring magnification level
            if self.stack_mode:
                step = 1 if key == "bracketright" else -1
                target = min(max(self.level_index + step, 0),
                             len(self.levels) - 1)
                self.set_view_scale(self.levels[target]["ppu"])
        elif key in ("l", "L"):
            if self.legend_pixbuf is not None:
                self.legend_enabled = not self.legend_enabled
                self.apply_legend_visibility()
        elif key in ("o", "O"):
            if self.stack_mode:
                self.hint_enabled = not self.hint_enabled
                self.update_hint_overlay()
        elif key == "Tab":
            self.aux_visible = not self.aux_visible
            self.apply_legend_visibility()
            self.update_view_overlays()
        elif key == "F11":
            state = self.window.get_window().get_state() if self.window.get_window() else 0
            if state & Gdk.WindowState.FULLSCREEN:
                self.window.unfullscreen()
            else:
                self.window.fullscreen()
        else:
            return False
        return True

    def on_scroll(self, widget, event):
        if not event.state & Gdk.ModifierType.CONTROL_MASK:
            return False  # plain wheel keeps panning the scrolled window
        direction = 0
        if event.direction == Gdk.ScrollDirection.UP:
            direction = 1
        elif event.direction == Gdk.ScrollDirection.DOWN:
            direction = -1
        elif event.direction == Gdk.ScrollDirection.SMOOTH:
            ok, _dx, dy = event.get_scroll_deltas()
            if ok and dy:
                direction = 1 if dy < 0 else -1
        if direction > 0:
            self.set_view_scale(self.current_view_scale() * self.ZOOM_STEP)
        elif direction < 0:
            self.set_view_scale(self.current_view_scale() / self.ZOOM_STEP)
        return True

    def on_button_press(self, widget, event):
        if event.button != 1 or event.type != Gdk.EventType.BUTTON_PRESS:
            return False
        if self.ruler_active:
            point = self.event_to_world(event)
            if point is not None:
                if self.ruler_start is None or self.ruler_end is not None:
                    self.ruler_start = point       # start a new measurement
                    self.ruler_end = self.ruler_cursor = None
                else:
                    self.ruler_end = self.snap_point(point, event.state)
                self.update_ruler_overlay()
            return True
        # Root coordinates stay stable while the adjustments move underneath.
        self.drag_origin = (event.x_root, event.y_root,
                            self.scroll.get_hadjustment().get_value(),
                            self.scroll.get_vadjustment().get_value())
        self.set_viewport_cursor("grabbing")
        return True

    def on_motion(self, widget, event):
        if self.ruler_active:
            if self.ruler_start is not None and self.ruler_end is None:
                point = self.event_to_world(event)
                if point is not None:
                    self.ruler_cursor = self.snap_point(point, event.state)
                    self.update_ruler_overlay()
            return True
        if self.drag_origin is None:
            return False
        x0, y0, h0, v0 = self.drag_origin
        self.scroll.get_hadjustment().set_value(h0 - (event.x_root - x0))
        self.scroll.get_vadjustment().set_value(v0 - (event.y_root - y0))
        return True

    def on_button_release(self, widget, event):
        if event.button != 1:
            return False
        if self.ruler_active:
            # press-drag-release measures in one gesture; a click in place
            # keeps the live preview until the second click
            if self.ruler_start is not None and self.ruler_end is None:
                point = self.event_to_world(event)
                screen_per_world = self.scale_shown \
                    * self.active_level()["ppu"]
                if point is not None and \
                        (abs(point[0] - self.ruler_start[0]) +
                         abs(point[1] - self.ruler_start[1])) \
                        * screen_per_world > 5:
                    self.ruler_end = self.snap_point(point, event.state)
                    self.update_ruler_overlay()
            return True
        if self.drag_origin is None:
            return False
        self.drag_origin = None
        self.set_viewport_cursor(None)
        return True

    def set_viewport_cursor(self, name):
        win = self.scroll.get_window()
        if win is None:
            return
        cursor = None
        if name:
            display = win.get_display()
            cursor = Gdk.Cursor.new_from_name(display, name)
            if cursor is None:  # theme without named cursors
                fallback = {"grabbing": Gdk.CursorType.FLEUR,
                            "crosshair": Gdk.CursorType.CROSSHAIR}[name]
                cursor = Gdk.Cursor.new_for_display(display, fallback)
        win.set_cursor(cursor)

    def on_focus_in(self, widget, event):
        self.window.set_urgency_hint(False)
        return False

    def present(self):
        self.window.show_all()
        self.window.deiconify()
        self.window.present_with_time(Gtk.get_current_event_time() or
                                      Gdk.CURRENT_TIME)
        # If the window manager blocks focus stealing, at least flash the
        # taskbar entry.
        self.window.set_urgency_hint(True)

    # -- incoming requests from later invocations ---------------------------

    def on_incoming(self, source, condition):
        try:
            conn, _ = self.server_sock.accept()
        except OSError:
            return True
        conn.settimeout(2.0)
        try:
            data = b""
            while b"\n" not in data and len(data) < 65536:
                chunk = conn.recv(4096)
                if not chunk:
                    break
                data += chunk
            line = data.decode("utf-8", "replace").strip()
            fields = line.split("\t")
            path = fields[0].strip()
            legend = ppu = unit = None
            stack = False
            inline = []   # ppu=/center= after a level= bind to that level
            bad = None
            for field in fields[1:]:
                key, _, value = field.partition("=")
                key, value = key.strip(), value.strip()
                if key == "legend":
                    legend = value or None
                elif key == "level":
                    inline.append({"path": value, "ppu": None,
                                   "center": (0.0, 0.0)})
                elif key == "ppu":
                    try:
                        parsed = float(value)
                    except ValueError:
                        parsed = 0
                    if parsed <= 0:
                        bad = "ERR bad ppu: %s" % value
                    elif inline:
                        inline[-1]["ppu"] = parsed
                    else:
                        ppu = parsed
                elif key == "center":
                    if not inline:
                        bad = "ERR center without level"
                    else:
                        try:
                            x, y = [float(v) for v in value.split(",")]
                            inline[-1]["center"] = (x, y)
                        except ValueError:
                            bad = "ERR bad center: %s" % value
                elif key == "unit":
                    unit = value or None
                elif key == "stack":
                    stack = value not in ("", "0")
                # unknown keys are ignored for forward compatibility
            if bad:
                reply = bad
            elif inline:
                reply = self.load(inline[0]["path"], legend, None, unit,
                                  True, inline)
            elif path:
                reply = self.load(path, legend, ppu, unit, stack)
            else:
                reply = "ERR empty request"
            try:
                conn.sendall(reply.encode("utf-8") + b"\n")
            except OSError:
                pass
            if reply == "OK":
                self.present()
        finally:
            conn.close()
        return True


# ---------------------------------------------------------------------------
# entry point
# ---------------------------------------------------------------------------

def usage(stream):
    stream.write(
        "usage: %s [-l LEGEND_FILE] [-p PPU] [-u UNIT] IMAGE_FILE\n"
        "       %s [-l LEGEND_FILE] [-u UNIT] -s STACK_FILE\n"
        "       %s [-l LEGEND_FILE] [-u UNIT] --level IMG -p PPU\n"
        "                 [--center X,Y] [--level IMG -p PPU ...]\n"
        "\n"
        "Opens IMAGE_FILE in a viewer window on $DISPLAY.  If a viewer is\n"
        "already running on that display, the image replaces the one in the\n"
        "existing window and this process exits immediately.\n"
        "\n"
        "  -l, --legend LEGEND_FILE  overlay LEGEND_FILE at the bottom-right\n"
        "                            corner; a request without -l removes it\n"
        "  -p, --ppu PPU             pixels per unit: the ruler converts\n"
        "                            distances with it (sticky per window);\n"
        "                            after --level it binds to that level\n"
        "  -u, --unit UNIT           unit name for the ruler (default: um)\n"
        "  -s, --stack STACK_FILE    multi-magnification set: one key=value\n"
        "                            per line (level=IMAGE, ppu=N per level,\n"
        "                            optional center=X,Y and unit=NAME);\n"
        "                            zooming in switches to sharper levels\n"
        "  --level IMAGE_FILE        add one stack level directly on the\n"
        "                            command line (no stack file needed)\n"
        "  --center X,Y              center offset in units of the last\n"
        "                            --level, for misaligned captures\n"
        "\n"
        "keys: +/- zoom, 1 actual size, f/0 fit to window, F11 fullscreen,\n"
        "      Ctrl+wheel zoom, drag to pan, l legend, o next-level outline,\n"
        "      Tab all overlays on/off, [/] stack level, p set PPU,\n"
        "      r ruler (Shift = free angle, Esc ends), q/Esc quit\n"
        % (APP, APP, APP))


def parse_args(args):
    """Returns (path, legend, ppu, unit, is_stack, levels) or an exit code.

    path is None when inline levels are given; is_stack marks a manifest.
    """
    legend = ppu = unit = stack_file = None
    levels = []
    paths = []
    i = 0
    while i < len(args):
        arg = args[i]
        took_value = None
        if arg in ("-h", "--help"):
            usage(sys.stdout)
            return 0
        elif arg in ("-l", "--legend", "-p", "--ppu", "-u", "--unit",
                     "-s", "--stack", "--level", "--center"):
            i += 1
            if i == len(args):
                sys.stderr.write("%s: %s requires an argument\n" % (APP, arg))
                return 2
            took_value = args[i]
        elif arg.startswith(("--legend=", "--ppu=", "--unit=", "--stack=",
                             "--level=", "--center=")):
            arg, took_value = arg.split("=", 1)
        elif arg.startswith("-") and arg != "-":
            sys.stderr.write("%s: unknown option: %s\n" % (APP, arg))
            usage(sys.stderr)
            return 2
        else:
            paths.append(arg)
        if took_value is not None:
            if arg in ("-l", "--legend"):
                legend = took_value
            elif arg in ("-p", "--ppu"):
                try:
                    value = float(took_value)
                except ValueError:
                    value = 0
                if value <= 0:
                    sys.stderr.write("%s: --ppu expects a number > 0, "
                                     "got: %s\n" % (APP, took_value))
                    return 2
                if levels:
                    levels[-1]["ppu"] = value
                else:
                    ppu = value
            elif arg in ("-u", "--unit"):
                unit = took_value
            elif arg == "--level":
                levels.append({"path": took_value, "ppu": None,
                               "center": (0.0, 0.0)})
            elif arg == "--center":
                if not levels:
                    sys.stderr.write("%s: --center before any --level\n"
                                     % APP)
                    return 2
                try:
                    x, y = [float(v) for v in took_value.split(",")]
                except ValueError:
                    sys.stderr.write("%s: --center expects X,Y, got: %s\n"
                                     % (APP, took_value))
                    return 2
                levels[-1]["center"] = (x, y)
            else:
                stack_file = took_value
        i += 1
    sources = (1 if paths else 0) + (1 if stack_file else 0) \
        + (1 if levels else 0)
    if sources != 1 or len(paths) > 1:
        usage(sys.stderr)
        return 2
    if levels:
        if ppu is not None:
            sys.stderr.write("%s: --ppu before the first --level is "
                             "ambiguous\n" % APP)
            return 2
        for meta in levels:
            if meta["ppu"] is None:
                sys.stderr.write("%s: --level %s needs a --ppu\n"
                                 % (APP, meta["path"]))
                return 2
        return None, legend, None, unit, False, levels
    if stack_file is not None:
        return stack_file, legend, ppu, unit, True, None
    return paths[0], legend, ppu, unit, False, None


def main(argv):
    parsed = parse_args(argv[1:])
    if isinstance(parsed, int):
        return parsed
    path, legend, ppu, unit, stack, levels = parsed

    if levels is not None:
        for meta in levels:
            meta["path"] = os.path.abspath(meta["path"])
            if not os.path.isfile(meta["path"]):
                sys.stderr.write("%s: no such file: %s\n"
                                 % (APP, meta["path"]))
                return 1
    else:
        path = os.path.abspath(path)
        if not os.path.isfile(path):
            sys.stderr.write("%s: no such file: %s\n" % (APP, path))
            return 1
    if legend is not None:
        legend = os.path.abspath(legend)
        if not os.path.isfile(legend):
            sys.stderr.write("%s: no such file: %s\n" % (APP, legend))
            return 1

    display = os.environ.get("DISPLAY")
    if not display:
        sys.stderr.write("%s: DISPLAY is not set\n" % APP)
        return 1

    addr = socket_address(display)
    fields = [path if levels is None else ""]
    if legend is not None:
        fields.append("legend=%s" % legend)
    if ppu is not None:
        fields.append("ppu=%.10g" % ppu)
    if unit is not None:
        fields.append("unit=%s" % unit)
    if stack:
        fields.append("stack=1")
    if levels is not None:
        for meta in levels:
            fields.append("level=%s" % meta["path"])
            fields.append("ppu=%.10g" % meta["ppu"])
            if meta["center"] != (0.0, 0.0):
                fields.append("center=%.10g,%.10g" % meta["center"])
    request = "\t".join(fields)
    server = None
    for _ in range(5):
        code = try_forward(addr, request)
        if code is not None:
            return code
        server = try_bind(addr)
        if server is not None:
            break
        time.sleep(0.2)
    if server is None:
        sys.stderr.write("%s: could not create or reach the instance socket\n" % APP)
        return 1

    if not addr.startswith("\0"):
        import atexit
        atexit.register(lambda: os.path.exists(addr) and os.unlink(addr))

    import_gtk()
    Viewer(server, path if levels is None else levels[0]["path"],
           legend, ppu, unit, stack, levels)
    Gtk.main()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
