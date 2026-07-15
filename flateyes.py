#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""flateyes - minimal single-instance-per-display image viewer.

Designed for closed-network Linux hosts where only stock GNOME libraries
(GTK3, GdkPixbuf, PyGObject) are available.

Behaviour:
  * One viewer window per DISPLAY.  The first invocation opens the window;
    later invocations on the same DISPLAY hand the image path to the running
    window over a unix socket and exit immediately.
  * Different DISPLAY values get independent windows, so many user displays
    can be served at the same time.

Usage:
  DISPLAY=:1 flateyes.py /path/to/image.jpg
"""

import errno
import hashlib
import math
import os
import signal
import socket
import sys
import tempfile
import time

APP = "flateyes"

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
# built-in dubeolsik hangul composer
# ---------------------------------------------------------------------------

class HangulComposer(object):
    """Composes hangul syllables from dubeolsik key strokes.

    The closed-network hosts usually run the viewer through sudo/setsid
    launchers without an input method connection, so GTK entries cannot
    compose hangul on their own.  This is a minimal stand-in: feed() takes
    one compatibility jamo and returns (committed, preedit) where
    committed is finalized text and preedit is the syllable still being
    composed (always the trailing characters of the entry).
    """

    KEYMAP = {
        "q": "ㅂ", "w": "ㅈ", "e": "ㄷ", "r": "ㄱ", "t": "ㅅ",
        "y": "ㅛ", "u": "ㅕ", "i": "ㅑ", "o": "ㅐ", "p": "ㅔ",
        "a": "ㅁ", "s": "ㄴ", "d": "ㅇ", "f": "ㄹ", "g": "ㅎ",
        "h": "ㅗ", "j": "ㅓ", "k": "ㅏ", "l": "ㅣ",
        "z": "ㅋ", "x": "ㅌ", "c": "ㅊ", "v": "ㅍ", "b": "ㅠ",
        "n": "ㅜ", "m": "ㅡ",
        "Q": "ㅃ", "W": "ㅉ", "E": "ㄸ", "R": "ㄲ", "T": "ㅆ",
        "O": "ㅒ", "P": "ㅖ",
    }
    CONSONANTS = set("ㄱㄲㄴㄷㄸㄹㅁㅂㅃㅅㅆㅇㅈㅉㅊㅋㅌㅍㅎ")
    LEADS = "ㄱㄲㄴㄷㄸㄹㅁㅂㅃㅅㅆㅇㅈㅉㅊㅋㅌㅍㅎ"
    VOWEL_ORDER = "ㅏㅐㅑㅒㅓㅔㅕㅖㅗㅘㅙㅚㅛㅜㅝㅞㅟㅠㅡㅢㅣ"
    TAIL_ORDER = "ㄱㄲㄳㄴㄵㄶㄷㄹㄺㄻㄼㄽㄾㄿㅀㅁㅂㅄㅅㅆㅇㅈㅊㅋㅌㅍㅎ"
    VOWEL_COMBO = {("ㅗ", "ㅏ"): "ㅘ", ("ㅗ", "ㅐ"): "ㅙ", ("ㅗ", "ㅣ"): "ㅚ",
                   ("ㅜ", "ㅓ"): "ㅝ", ("ㅜ", "ㅔ"): "ㅞ", ("ㅜ", "ㅣ"): "ㅟ",
                   ("ㅡ", "ㅣ"): "ㅢ"}
    TAIL_COMBO = {("ㄱ", "ㅅ"): "ㄳ", ("ㄴ", "ㅈ"): "ㄵ", ("ㄴ", "ㅎ"): "ㄶ",
                  ("ㄹ", "ㄱ"): "ㄺ", ("ㄹ", "ㅁ"): "ㄻ", ("ㄹ", "ㅂ"): "ㄼ",
                  ("ㄹ", "ㅅ"): "ㄽ", ("ㄹ", "ㅌ"): "ㄾ", ("ㄹ", "ㅍ"): "ㄿ",
                  ("ㄹ", "ㅎ"): "ㅀ", ("ㅂ", "ㅅ"): "ㅄ"}
    TAIL_SPLIT = dict((v, k) for k, v in TAIL_COMBO.items())
    VOWEL_SPLIT = dict((v, k[0]) for k, v in VOWEL_COMBO.items())

    def __init__(self):
        self.reset()

    def reset(self):
        self.lead = self.vowel = self.tail = ""

    def pending(self):
        return bool(self.lead or self.vowel)

    def preedit(self):
        if not self.vowel:
            return self.lead
        if not self.lead:
            return self.vowel
        code = 0xAC00 + (self.LEADS.index(self.lead) * 21
                         + self.VOWEL_ORDER.index(self.vowel)) * 28
        if self.tail:
            code += self.TAIL_ORDER.index(self.tail) + 1
        return chr(code)

    def feed(self, jamo):
        if jamo in self.CONSONANTS:
            if not self.lead and not self.vowel:
                self.lead = jamo
                return "", self.preedit()
            if self.lead and not self.vowel:
                out = self.preedit()      # lone consonant: emit as jamo
                self.lead = jamo
                return out, self.preedit()
            if self.lead and not self.tail and jamo in self.TAIL_ORDER:
                self.tail = jamo
                return "", self.preedit()
            if self.tail:
                combo = self.TAIL_COMBO.get((self.tail, jamo))
                if combo:
                    self.tail = combo
                    return "", self.preedit()
            out = self.preedit()
            self.lead, self.vowel, self.tail = jamo, "", ""
            return out, self.preedit()
        # vowel
        if self.tail:
            # the (last part of the) tail becomes the next syllable's lead
            keep, move = self.TAIL_SPLIT.get(self.tail, ("", self.tail))
            self.tail = keep
            out = self.preedit()
            self.lead, self.vowel, self.tail = move, jamo, ""
            return out, self.preedit()
        if self.vowel:
            combo = self.VOWEL_COMBO.get((self.vowel, jamo))
            if combo:
                self.vowel = combo
                return "", self.preedit()
            out = self.preedit()
            self.lead, self.vowel, self.tail = "", jamo, ""
            return out, self.preedit()
        self.vowel = jamo
        return "", self.preedit()

    def backspace(self):
        """Removes one component; returns the remaining preedit text."""
        if self.tail:
            self.tail = self.TAIL_SPLIT.get(self.tail, ("", ""))[0]
        elif self.vowel:
            self.vowel = self.VOWEL_SPLIT.get(self.vowel, "")
        else:
            self.lead = ""
        return self.preedit()


class TextViewEditable(object):
    """Entry-like facade over a Gtk.TextView for the hangul composer."""

    def __init__(self, view):
        self.buffer = view.get_buffer()

    def get_text(self):
        return self.buffer.get_text(self.buffer.get_start_iter(),
                                    self.buffer.get_end_iter(), True)

    def set_text(self, text):
        self.buffer.set_text(text)

    def get_position(self):
        return self.buffer.get_property("cursor-position")

    def set_position(self, position):
        if position < 0:
            where = self.buffer.get_end_iter()
        else:
            where = self.buffer.get_iter_at_offset(position)
        self.buffer.place_cursor(where)

    def delete_selection(self):
        self.buffer.delete_selection(True, True)


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
    DRAG_SLOP = 4                # px: press-release within this is a click
    ANNO_CASING = 0x000000A0     # shape annotation outline
    ANNO_COLORS = ("#FF5040", "#FF9F1A", "#3DDC55", "#35C5FF",
                   "#FF4FD8", "#FFFFFF")  # ","/"." cycle these
    ANNO_COLOR_NAMES = ("red", "orange", "green", "sky", "pink", "white")
    HELP_KEYS = (("+/-", "zoom"), ("0", "1:1"), ("f", "fit"),
                 ("Enter", "full"), ("drag", "pan"), ("Ctrl+wheel", "zoom"),
                 ("r", "ruler"), ("b/e/l", "shape"), ("t", "text"),
                 ("c", "color"), ("u", "undo"), ("BkSp", "delete"),
                 ("Ctrl+C", "copy"), ("p", "PPU"),
                 ("o", "outline"), ("[/]", "level"), ("i", "info"),
                 ("Tab", "drawings"), ("q", "quit"))

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
        # Overlay visibility, two groups: "i" toggles the info overlays
        # (help strip, legend, next-level outline), Tab the drawing
        # overlays (ruler, annotations).  "o" keeps its own switch.
        self.info_visible = True    # "i"
        self.draw_visible = True    # Tab
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
        self.drag_panned = False
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
        self.ruler_label.set_name("flateyes-ruler")

        # Key help strip along the top edge; keys colored like the ruler
        # so they stand apart from the descriptions.
        self.help_label = Gtk.Label()
        self.help_label.set_markup(" · ".join(
            '<span foreground="#ffd819" weight="bold">%s</span> %s' % pair
            for pair in self.HELP_KEYS))
        self.help_label.set_name("flateyes-help")
        self.help_label.set_halign(Gtk.Align.CENTER)
        self.help_label.set_valign(Gtk.Align.START)
        self.help_label.set_margin_top(8)
        self.help_label.set_margin_start(8)
        self.help_label.set_margin_end(8)
        self.help_label.set_line_wrap(True)
        self.help_label.set_justify(Gtk.Justification.CENTER)
        self.help_label.set_no_show_all(True)

        # Scale/size/ppu status readout at the bottom-left corner, so the
        # window title only needs to fit the (possibly long) file name.
        self.status_label = Gtk.Label()
        self.status_label.set_name("flateyes-status")
        self.status_label.set_halign(Gtk.Align.START)
        self.status_label.set_valign(Gtk.Align.END)
        self.status_label.set_margin_start(8)
        self.status_label.set_margin_bottom(8)
        self.status_label.set_no_show_all(True)

        # Transient feedback message (e.g. after copying to the clipboard).
        self.toast_timeout = None
        self.toast_label = Gtk.Label()
        self.toast_label.set_name("flateyes-toast")
        self.toast_label.set_halign(Gtk.Align.CENTER)
        self.toast_label.set_valign(Gtk.Align.END)
        self.toast_label.set_margin_bottom(24)
        self.toast_label.set_no_show_all(True)

        css = Gtk.CssProvider()
        css.load_from_data(
            b"#flateyes-ruler { background-color: rgba(0,0,0,0.78);"
            b" color: #ffffff; padding: 2px 7px; border-radius: 3px;"
            b" font-weight: bold; }"
            b"#flateyes-help { background-color: rgba(0,0,0,0.6);"
            b" color: #f0f0f0; padding: 2px 9px; border-radius: 4px;"
            b" font-size: 11px; }"
            b"#flateyes-toast { background-color: rgba(0,0,0,0.78);"
            b" color: #ffffff; padding: 4px 12px; border-radius: 4px; }"
            b"#flateyes-status { background-color: rgba(0,0,0,0.6);"
            b" color: #f0f0f0; padding: 2px 9px; border-radius: 4px;"
            b" font-size: 11px; }")
        for widget in (self.ruler_label, self.help_label, self.toast_label,
                       self.status_label):
            widget.get_style_context().add_provider(
                css, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        # Annotations: boxes/ellipses stamped into one viewport-sized
        # overlay pixbuf, texts as Pango labels; all anchored in world
        # coordinates like the ruler.
        self.anno_tool = None       # "box" | "ellipse" | "text"
        self.anno_start = None      # first corner (world)
        self.anno_cursor = None     # preview corner (world)
        self.annotations = []       # committed shapes and texts
        self.anno_undo = []         # ("add"|"remove", annotation, index)
        self.anno_rev = 0           # bumped on add/remove for the key cache
        self.anno_drawn = None
        self.anno_font_size = 16    # last used text size (pt), sticky
        self.anno_text_bg = True    # translucent backdrop, sticky
        self.anno_color_index = 0   # "c" cycles ANNO_COLORS
        self.anno_image = Gtk.Image()
        self.anno_image.set_halign(Gtk.Align.START)
        self.anno_image.set_valign(Gtk.Align.START)
        self.anno_image.set_no_show_all(True)
        self.anno_css = Gtk.CssProvider()
        self.anno_css.load_from_data(
            b"label { background-color: rgba(0,0,0,0.35);"
            b" padding: 0px 3px; border-radius: 2px; }")

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
        self.overlay.add_overlay(self.anno_image)
        self.overlay.add_overlay(self.ruler_line)
        self.overlay.add_overlay(self.ruler_label)
        self.overlay.add_overlay(self.help_label)
        self.overlay.add_overlay(self.status_label)
        self.overlay.add_overlay(self.toast_label)
        for child in (self.legend_frame, self.hint_image, self.anno_image,
                      self.ruler_line, self.ruler_label, self.help_label,
                      self.status_label, self.toast_label):
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
        self.apply_help_visibility()

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
        self.clear_annotations()
        self.load_annotations()
        self.legend_pixbuf = legend_pixbuf
        self.legend_rendered = None
        if legend_pixbuf is not None:
            self.render_legend()
        else:
            self.legend_image.clear()
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
        # Follow the image's aspect ratio so the window opens without
        # large empty margins on either axis.
        scale = min(float(max_w) / img_w, float(max_h) / img_h, 1.0)
        self.window.set_default_size(max(int(img_w * scale) + 4, 320),
                                     max(int(img_h * scale) + 4, 240))

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
        self.window.set_title("%s - %s" % (name, APP))
        self.update_status()

    def update_status(self):
        """Scale/size/ppu readout at the bottom-left, styled like the
        help strip; the title only carries the file name."""
        value = '<span foreground="#ffd819" weight="bold">%s</span>'
        img_w, img_h = self.image_size()
        parts = []
        if self.stack_mode:
            level = self.active_level()
            parts.append(value % ("%d/%d" % (self.level_index + 1,
                                             len(self.levels)))
                         + " " + GLib.markup_escape_text(
                             os.path.basename(level["path"])))
        parts.append(value % ("%dx%d" % (img_w, img_h)))
        if self.animation is not None:
            parts.append("animation")
        else:
            parts.append(value % ("%d%%" % round(self.scale_shown * 100)))
            ppu = self.active_level()["ppu"] if self.stack_mode else self.ppu
            if ppu:
                parts.append(value % ("%.4g" % ppu) + " px/"
                             + GLib.markup_escape_text(self.unit))
        self.status_label.set_markup(" · ".join(parts))

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

    def copy_view_to_clipboard(self):
        """Copy the visible viewport, overlays included, to the clipboard."""
        win = self.window.get_window()
        if win is None:
            return
        alloc = self.overlay.get_allocation()
        pixbuf = Gdk.pixbuf_get_from_window(win, alloc.x, alloc.y,
                                            alloc.width, alloc.height)
        if pixbuf is None:
            self.show_toast("copy failed")
            return
        clipboard = Gtk.Clipboard.get(Gdk.SELECTION_CLIPBOARD)
        clipboard.set_image(pixbuf)
        clipboard.store()
        self.show_toast("copied  %dx%d" % (pixbuf.get_width(),
                                           pixbuf.get_height()))

    def show_toast(self, text, markup=False):
        if markup:
            self.toast_label.set_markup(text)
        else:
            self.toast_label.set_text(text)
        self.toast_label.show()
        if self.toast_timeout is not None:
            GLib.source_remove(self.toast_timeout)
        self.toast_timeout = GLib.timeout_add(1500, self.hide_toast)

    def hide_toast(self):
        self.toast_timeout = None
        self.toast_label.hide()
        return False

    def apply_help_visibility(self):
        if self.info_visible:
            self.help_label.show()
            self.status_label.show()
        else:
            self.help_label.hide()
            self.status_label.hide()

    def apply_legend_visibility(self):
        if self.legend_pixbuf is not None and self.info_visible:
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
        if active and self.anno_tool is not None:
            self.anno_tool = None   # tools are exclusive
            self.anno_start = self.anno_cursor = None
            self.update_anno_overlay()
        if active and not self.draw_visible:
            self.draw_visible = True  # measuring needs its overlays back
        self.ruler_active = active
        self.ruler_start = self.ruler_end = self.ruler_cursor = None
        self.set_viewport_cursor(self.tool_cursor())
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
        if not self.ruler_active or not self.draw_visible \
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
        # Show before measuring: hidden widgets report a zero preferred
        # size, which would wreck the position after a Tab off/on cycle.
        self.ruler_label.show()
        # get_preferred_size includes the widget margins, and the margins
        # hold the label's PREVIOUS position; measure the text alone or
        # the label bounces between its spot and the top of the window.
        _, nat = self.ruler_label.get_preferred_size()
        text_w = nat.width - self.ruler_label.get_margin_start()
        text_h = nat.height - self.ruler_label.get_margin_top()
        x = (a[0] + b[0]) / 2 + 12
        y = (a[1] + b[1]) / 2 - text_h - 12
        x = max(2, min(x, view.width - text_w - 2))
        y = max(2, min(y, view.height - text_h - 2))
        self.ruler_label.set_margin_start(int(x))
        self.ruler_label.set_margin_top(int(y))

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
            else:           # free angle: 1px-spaced dabs, 2x2 solid core
                seg = self.clip_segment((ax, ay), (bx, by),
                                        buf.get_width(), buf.get_height())
                if seg is not None:
                    (ax, ay), (bx, by) = seg
                    steps = min(int(max(abs(bx - ax), abs(by - ay))) + 1,
                                8000)
                    points = [(ax + (bx - ax) * i / steps,
                               ay + (by - ay) * i / steps)
                              for i in range(steps + 1)]
                    for x, y in points:
                        self.fill_rect(buf, x - 1, y - 1, 3, 3,
                                       self.RULER_CASING)
                    for x, y in points:
                        self.fill_rect(buf, x - 1, y - 1, 2, 2,
                                       self.RULER_CORE)
        for x, y in ((ax, ay), (bx, by)):
            self.fill_rect(buf, x - 3, y - 3, 7, 7, self.RULER_CASING)
            self.fill_rect(buf, x - 2, y - 2, 5, 5, self.RULER_CORE)
        self.ruler_line.set_from_pixbuf(buf)
        self.ruler_line.set_margin_start(x0)
        self.ruler_line.set_margin_top(y0)
        self.ruler_line.show()

    @staticmethod
    def clip_segment(a, b, width, height, pad=4):
        """Clip a segment to the buffer (Liang-Barsky); None if outside.

        Sampling density is derived from the segment length, so stamping
        an unclipped segment that extends far outside the buffer would
        spread the dabs thin inside it."""
        t0, t1 = 0.0, 1.0
        dx, dy = b[0] - a[0], b[1] - a[1]
        for p, q in ((-dx, a[0] + pad), (dx, width + pad - a[0]),
                     (-dy, a[1] + pad), (dy, height + pad - a[1])):
            if p == 0:
                if q < 0:
                    return None
                continue
            r = q / float(p)
            if p < 0:
                if r > t1:
                    return None
                t0 = max(t0, r)
            else:
                if r < t0:
                    return None
                t1 = min(t1, r)
        if t0 > t1:
            return None
        return ((a[0] + t0 * dx, a[1] + t0 * dy),
                (a[0] + t1 * dx, a[1] + t1 * dy))

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
        self.update_anno_overlay()

    # -- shape/text annotations ------------------------------------------

    def set_anno_tool(self, tool):
        if tool is not None and self.pixbuf is None:
            return  # animations are shown unscaled and unannotated
        if tool is not None:
            if self.ruler_active:   # tools are exclusive
                self.ruler_active = False
                self.ruler_start = self.ruler_end = self.ruler_cursor = None
                self.update_ruler_overlay()
            if not self.draw_visible:
                self.draw_visible = True  # drawing needs its overlays back
        self.anno_tool = tool
        self.anno_start = self.anno_cursor = None
        self.set_viewport_cursor(self.tool_cursor())
        self.update_view_overlays()

    def anno_color(self):
        return self.ANNO_COLORS[self.anno_color_index]

    @staticmethod
    def color_rgba(hex_color):
        """"#RRGGBB" -> the 0xRRGGBBAA pixbuf fill value."""
        return (int(hex_color[1:], 16) << 8) | 0xFF

    def constrain_corner(self, point, state):
        """Shift constrains: square/circle for shapes, 0/45/90 for lines."""
        if not state & Gdk.ModifierType.SHIFT_MASK:
            return point
        ax, ay = self.anno_start
        dx, dy = point[0] - ax, point[1] - ay
        if self.anno_tool == "line":
            if abs(dx) > 2 * abs(dy):
                return (point[0], ay)        # horizontal
            if abs(dy) > 2 * abs(dx):
                return (ax, point[1])        # vertical
        side = max(abs(dx), abs(dy))         # square/circle/45-degree line
        return (ax + (side if dx >= 0 else -side),
                ay + (side if dy >= 0 else -side))

    def update_anno_overlay(self):
        texts = [x for x in self.annotations if x["kind"] == "text"]
        shapes = [x for x in self.annotations if x["kind"] != "text"]
        preview = None
        if self.anno_tool in ("box", "ellipse", "line") \
                and self.anno_start is not None \
                and self.anno_cursor is not None:
            preview = {"kind": self.anno_tool, "a": self.anno_start,
                       "b": self.anno_cursor, "color": self.anno_color()}
        if not self.draw_visible or self.rendered_size is None \
                or not (shapes or preview or texts):
            self.anno_drawn = None
            self.anno_image.hide()
            for anno in texts:
                anno["label"].hide()
            return
        view = self.scroll.get_allocation()
        # The image allocation belongs in the key: right after a zoom/fit
        # change the overlays are drawn once against the STALE allocation,
        # and without it the corrected layout pass would hit the cache and
        # leave annotations displaced.
        img_alloc = self.image.get_allocation()
        key = (self.anno_rev, self.anno_color_index,
               preview and (preview["a"], preview["b"]),
               self.scroll.get_hadjustment().get_value(),
               self.scroll.get_vadjustment().get_value(),
               self.scale_shown, self.level_index, self.rendered_size,
               img_alloc.width, img_alloc.height,
               view.width, view.height)
        if key == self.anno_drawn:
            return  # also breaks the redraw->allocate->redraw cycle
        self.anno_drawn = key
        buf = GdkPixbuf.Pixbuf.new(GdkPixbuf.Colorspace.RGB, True, 8,
                                   max(view.width, 1), max(view.height, 1))
        buf.fill(0x00000000)
        for shape in shapes:
            self.stamp_annotation(buf, shape)
        if preview is not None:
            self.stamp_annotation(buf, preview)
        for anno in texts:
            x, y = self.image_px_to_view(self.px_from_world(anno["at"]))
            if -20 <= x <= view.width and -10 <= y <= view.height:
                anno["label"].set_margin_start(int(max(0, x)))
                anno["label"].set_margin_top(int(max(0, y)))
                anno["label"].show()
            else:
                anno["label"].hide()
        self.anno_image.set_from_pixbuf(buf)
        self.anno_image.set_margin_start(0)
        self.anno_image.set_margin_top(0)
        self.anno_image.show()

    def stamp_annotation(self, buf, shape):
        a = self.image_px_to_view(self.px_from_world(shape["a"]))
        b = self.image_px_to_view(self.px_from_world(shape["b"]))
        core = self.color_rgba(shape["color"])
        if shape["kind"] == "line":
            ax, ay = a
            bx, by = b
            if ay == by:    # horizontal
                self.fill_rect(buf, min(ax, bx), ay - 1,
                               abs(bx - ax) + 1, 3, self.ANNO_CASING)
                self.fill_rect(buf, min(ax, bx), ay,
                               abs(bx - ax) + 1, 1, core)
            elif ax == bx:  # vertical
                self.fill_rect(buf, ax - 1, min(ay, by),
                               3, abs(by - ay) + 1, self.ANNO_CASING)
                self.fill_rect(buf, ax, min(ay, by),
                               1, abs(by - ay) + 1, core)
            else:           # free angle: 1px-spaced dabs, 2x2 solid core
                seg = self.clip_segment(a, b, buf.get_width(),
                                        buf.get_height())
                if seg is None:
                    return
                (ax, ay), (bx, by) = seg
                steps = min(int(max(abs(bx - ax), abs(by - ay))) + 1, 8000)
                points = [(ax + (bx - ax) * i / steps,
                           ay + (by - ay) * i / steps)
                          for i in range(steps + 1)]
                for x, y in points:
                    self.fill_rect(buf, x - 1, y - 1, 3, 3,
                                   self.ANNO_CASING)
                for x, y in points:
                    self.fill_rect(buf, x - 1, y - 1, 2, 2, core)
            return
        x0, x1 = sorted((a[0], b[0]))
        y0, y1 = sorted((a[1], b[1]))
        if shape["kind"] == "box":
            for width, rgba in ((3, self.ANNO_CASING), (1, core)):
                off = width // 2
                self.fill_rect(buf, x0 - off, y0 - off,
                               x1 - x0 + width, width, rgba)   # top
                self.fill_rect(buf, x0 - off, y1 - off,
                               x1 - x0 + width, width, rgba)   # bottom
                self.fill_rect(buf, x0 - off, y0 - off,
                               width, y1 - y0 + width, rgba)   # left
                self.fill_rect(buf, x1 - off, y0 - off,
                               width, y1 - y0 + width, rgba)   # right
            return
        # ellipse: 1px-spaced dabs along the perimeter, 2x2 solid core
        cx, cy = (x0 + x1) / 2.0, (y0 + y1) / 2.0
        rx, ry = (x1 - x0) / 2.0, (y1 - y0) / 2.0
        buf_w, buf_h = buf.get_width(), buf.get_height()
        steps = min(max(int(6.4 * max(rx, ry)), 16), 8000)
        points = [(x, y) for x, y in
                  ((cx + rx * math.cos(2 * math.pi * i / steps),
                    cy + ry * math.sin(2 * math.pi * i / steps))
                   for i in range(steps))
                  if -3 <= x <= buf_w + 3 and -3 <= y <= buf_h + 3]
        for x, y in points:
            self.fill_rect(buf, x - 1, y - 1, 3, 3, self.ANNO_CASING)
        for x, y in points:
            self.fill_rect(buf, x - 1, y - 1, 2, 2, core)

    def ask_annotation_text(self, point):
        dialog = Gtk.Dialog(title="Text", transient_for=self.window,
                            modal=True)
        dialog.set_keep_above(True)  # stay over a fullscreen parent
        dialog.add_button("Cancel", Gtk.ResponseType.CANCEL)
        dialog.add_button("OK", Gtk.ResponseType.OK)
        dialog.set_default_response(Gtk.ResponseType.OK)
        view = Gtk.TextView()
        view.set_wrap_mode(Gtk.WrapMode.WORD_CHAR)
        editable = TextViewEditable(view)
        scroll = Gtk.ScrolledWindow()
        scroll.set_policy(Gtk.PolicyType.AUTOMATIC,
                          Gtk.PolicyType.AUTOMATIC)
        scroll.set_shadow_type(Gtk.ShadowType.IN)
        scroll.set_size_request(340, 90)  # room for a few lines
        scroll.add(view)
        spin = Gtk.SpinButton.new_with_range(6, 96, 1)
        spin.set_value(self.anno_font_size)
        # Built-in hangul input for hosts without an input method.
        hangul = Gtk.CheckButton(label="한글 (Shift+Space)")
        state = {"composer": HangulComposer(), "check": hangul,
                 "anchor": None}
        hangul.connect("toggled",
                       lambda *a: state["composer"].reset())

        def on_view_key(widget, event):
            name = Gdk.keyval_name(event.keyval)
            if name in ("Return", "KP_Enter") and \
                    event.state & Gdk.ModifierType.CONTROL_MASK:
                dialog.response(Gtk.ResponseType.OK)  # plain Enter: new line
                return True
            return self.on_text_entry_key(editable, event, state)

        view.connect("key-press-event", on_view_key)
        bgcheck = Gtk.CheckButton(label="배경")
        bgcheck.set_active(self.anno_text_bg)
        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        row.pack_start(Gtk.Label(label="size (pt)"), False, False, 0)
        row.pack_start(spin, False, False, 0)
        row.pack_start(bgcheck, False, False, 6)
        row.pack_start(hangul, False, False, 12)
        hint = Gtk.Label()
        hint.set_markup("<small>Enter: new line · Ctrl+Enter: OK</small>")
        hint.set_halign(Gtk.Align.START)
        box = dialog.get_content_area()
        box.set_border_width(10)
        box.set_spacing(6)
        box.pack_start(scroll, True, True, 0)
        box.pack_start(row, False, False, 0)
        box.pack_start(hint, False, False, 0)
        dialog.show_all()
        confirmed = dialog.run() == Gtk.ResponseType.OK
        text = editable.get_text().strip()
        size = int(spin.get_value())
        bg = bgcheck.get_active()
        dialog.destroy()
        if not confirmed or not text:
            return
        self.anno_font_size = size
        self.anno_text_bg = bg
        self.add_text_annotation(point, text, size, self.anno_color(), bg)
        self.anno_undo.append(("add", self.annotations[-1], None))
        self.update_anno_overlay()
        self.save_annotations()

    def add_text_annotation(self, point, text, size, color, bg=True):
        label = Gtk.Label()
        label.set_halign(Gtk.Align.START)
        label.set_valign(Gtk.Align.START)
        label.set_no_show_all(True)
        label.set_markup('<span font="%d" foreground="%s">%s</span>'
                         % (size, color, GLib.markup_escape_text(text)))
        if bg:
            label.get_style_context().add_provider(
                self.anno_css, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        self.overlay.add_overlay(label)
        try:
            self.overlay.set_overlay_pass_through(label, True)
        except AttributeError:  # GTK < 3.18
            pass
        self.annotations.append({"kind": "text", "at": point,
                                 "text": text, "size": size,
                                 "color": color, "bg": bg, "label": label})
        self.anno_rev += 1

    def on_text_entry_key(self, entry, event, state):
        """Hangul composition for the annotation text entry."""
        name = Gdk.keyval_name(event.keyval)
        shift = event.state & Gdk.ModifierType.SHIFT_MASK
        if name in ("Hangul", "Hangul_Hanja") or (name == "space" and shift):
            state["check"].set_active(not state["check"].get_active())
            return True
        if not state["check"].get_active():
            return False
        composer = state["composer"]
        if event.state & (Gdk.ModifierType.CONTROL_MASK |
                          Gdk.ModifierType.MOD1_MASK):
            composer.reset()  # keep shortcuts like Ctrl+A/C/V working
            state["anchor"] = None
            return False
        # A cursor that left the end of the preedit span (click, arrow
        # keys, ...) finishes that syllable; composition then restarts
        # wherever the cursor now is.
        if composer.pending() and entry.get_position() != \
                state["anchor"] + len(composer.preedit()):
            composer.reset()
            state["anchor"] = None
        if name == "BackSpace":
            if not composer.pending():
                return False
            old_len = len(composer.preedit())
            self.entry_replace(entry, state["anchor"], old_len,
                               composer.backspace())
            if not composer.pending():
                state["anchor"] = None
            return True
        code = Gdk.keyval_to_unicode(event.keyval)
        char = chr(code) if code else ""
        jamo = HangulComposer.KEYMAP.get(char) \
            or HangulComposer.KEYMAP.get(char.lower())
        if jamo is None:
            composer.reset()  # syllable done; the entry handles the key
            state["anchor"] = None
            return False
        if not composer.pending():
            entry.delete_selection()  # type over a selection, like an IME
            state["anchor"] = entry.get_position()
            old_len = 0
        else:
            old_len = len(composer.preedit())
        committed, preedit = composer.feed(jamo)
        self.entry_replace(entry, state["anchor"], old_len,
                           committed + preedit)
        state["anchor"] += len(committed)
        return True

    @staticmethod
    def entry_replace(entry, anchor, old_len, new):
        """Replace the preedit span at anchor, cursor after it."""
        text = entry.get_text()
        entry.set_text(text[:anchor] + new + text[anchor + old_len:])
        entry.set_position(anchor + len(new))

    def remove_last_annotation(self):
        if not self.annotations:
            return
        anno = self.annotations.pop()
        self.anno_undo.append(("remove", anno, len(self.annotations)))
        if anno["kind"] == "text":
            self.overlay.remove(anno["label"])
        self.anno_rev += 1
        self.update_anno_overlay()
        self.save_annotations()

    def undo_annotation(self):
        """Reverts the last add or remove ("u")."""
        if not self.anno_undo:
            self.show_toast("nothing to undo")
            return
        op, anno, index = self.anno_undo.pop()
        if op == "add":
            if anno not in self.annotations:
                return  # should not happen; the stack resets per image
            self.annotations.remove(anno)
            if anno["kind"] == "text":
                self.overlay.remove(anno["label"])
        else:  # "remove": put it back where it was
            self.annotations.insert(min(index, len(self.annotations)), anno)
            if anno["kind"] == "text":
                self.overlay.add_overlay(anno["label"])
                try:
                    self.overlay.set_overlay_pass_through(anno["label"],
                                                          True)
                except AttributeError:  # GTK < 3.18
                    pass
        self.anno_rev += 1
        self.update_anno_overlay()
        self.save_annotations()

    def clear_annotations(self):
        # runtime state only; the metadata on disk is left untouched
        for anno in self.annotations:
            if anno["kind"] == "text":
                self.overlay.remove(anno["label"])
        self.annotations = []
        self.anno_undo = []
        self.anno_rev += 1
        self.anno_tool = None
        self.anno_start = self.anno_cursor = None
        self.update_anno_overlay()

    # -- annotation metadata (persistence) ---------------------------------

    def annotation_paths(self):
        """Sidecar and cache candidates for the current path's metadata."""
        digest = hashlib.sha1(self.path.encode("utf-8")).hexdigest()
        return (self.path + ".fe",
                os.path.join(GLib.get_user_cache_dir(), "flateyes",
                             digest + ".fe"))

    def save_annotations(self):
        """Autosaved on every change: sidecar first, cache as fallback."""
        lines = []
        for anno in self.annotations:
            color = anno.get("color", self.ANNO_COLORS[0])
            if anno["kind"] == "text":
                lines.append("text=%.10g,%.10g,%d,%s,%d,%s"
                             % (anno["at"][0], anno["at"][1],
                                anno["size"], color,
                                1 if anno.get("bg", True) else 0,
                                self.escape_meta(anno["text"])))
            else:
                lines.append("%s=%.10g,%.10g,%.10g,%.10g,%s"
                             % (anno["kind"], anno["a"][0], anno["a"][1],
                                anno["b"][0], anno["b"][1], color))
        candidates = self.annotation_paths()
        if not lines:
            for path in candidates:
                try:
                    os.unlink(path)
                except OSError:
                    pass
            return
        data = "# flateyes annotations\n" + "\n".join(lines) + "\n"
        for path in candidates:
            try:
                if path != candidates[0]:
                    os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, "w", encoding="utf-8") as handle:
                    handle.write(data)
                return
            except OSError:
                continue
        self.show_toast("annotations not saved (read-only?)")

    def load_annotations(self):
        if self.pixbuf is None:
            return  # animations cannot be annotated
        for meta_path in self.annotation_paths():
            try:
                with open(meta_path, "r", encoding="utf-8") as handle:
                    lines = handle.read().splitlines()
            except OSError:
                continue
            for raw in lines:
                line = raw.strip()
                if not line or line.startswith("#"):
                    continue
                key, sep, value = line.partition("=")
                if not sep:
                    continue
                try:
                    if key == "text":
                        x, y, size, color, bg, text = value.split(",", 5)
                        text = self.unescape_meta(text)
                        if text:
                            self.add_text_annotation(
                                (float(x), float(y)), text,
                                max(6, min(int(size), 96)),
                                self.parse_color(color),
                                bg=(bg.strip() != "0"))
                    elif key in ("box", "ellipse", "line"):
                        ax, ay, bx, by, color = value.split(",", 4)
                        self.annotations.append({
                            "kind": key,
                            "a": (float(ax), float(ay)),
                            "b": (float(bx), float(by)),
                            "color": self.parse_color(color)})
                except ValueError:
                    continue  # skip malformed lines
            break  # first readable source wins
        if self.annotations:
            self.anno_rev += 1
            self.update_anno_overlay()
            self.show_toast("%d annotation%s restored"
                            % (len(self.annotations),
                               "" if len(self.annotations) == 1 else "s"))

    @staticmethod
    def escape_meta(text):
        """Keep multi-line texts on one metadata line."""
        return text.replace("\\", "\\\\").replace("\n", "\\n")

    @staticmethod
    def unescape_meta(text):
        out, i = [], 0
        while i < len(text):
            if text[i] == "\\" and i + 1 < len(text):
                if text[i + 1] == "n":
                    out.append("\n")
                    i += 2
                    continue
                if text[i + 1] == "\\":
                    out.append("\\")
                    i += 2
                    continue
            out.append(text[i])
            i += 1
        return "".join(out)

    @staticmethod
    def parse_color(text):
        text = text.strip()
        if len(text) == 7 and text.startswith("#"):
            try:
                int(text[1:], 16)
                return text
            except ValueError:
                pass
        return Viewer.ANNO_COLORS[0]

    def update_hint_overlay(self):
        """Outline the area the next magnification level covers."""
        if not self.stack_mode or not self.hint_enabled \
                or not self.info_visible or self.rendered_size is None \
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
        dialog.set_keep_above(True)  # stay over a fullscreen parent
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
        self.update_status()

    # -- events ------------------------------------------------------------

    def on_size_allocate(self, widget, allocation):
        if self.fit_mode:
            self.rescale(allocation)
        self.update_view_overlays()

    def on_key(self, widget, event):
        key = Gdk.keyval_name(event.keyval)
        if key in ("q", "Q"):
            Gtk.main_quit()
        elif key in ("i", "I"):  # info overlays: help, legend, level outline
            self.info_visible = not self.info_visible
            self.apply_help_visibility()
            self.apply_legend_visibility()
            self.update_hint_overlay()
        elif key == "Escape":  # leaves tool modes only; quitting is "q"
            if self.ruler_active:
                self.set_ruler_active(False)
            elif self.anno_tool is not None:
                self.set_anno_tool(None)
        elif key in ("r", "R"):
            self.set_ruler_active(not self.ruler_active)
        elif key in ("b", "B"):
            self.set_anno_tool(None if self.anno_tool == "box" else "box")
        elif key in ("e", "E"):
            self.set_anno_tool(None if self.anno_tool == "ellipse"
                               else "ellipse")
        elif key in ("t", "T"):
            self.set_anno_tool(None if self.anno_tool == "text" else "text")
        elif key in ("l", "L"):
            self.set_anno_tool(None if self.anno_tool == "line" else "line")
        elif key in ("BackSpace", "Delete"):
            self.remove_last_annotation()
        elif key in ("u", "U"):
            self.undo_annotation()
        elif key in ("c", "C"):
            if event.state & Gdk.ModifierType.CONTROL_MASK:
                self.copy_view_to_clipboard()  # Ctrl+C
            else:                              # plain c: cycle the color
                self.anno_color_index = (self.anno_color_index + 1) \
                    % len(self.ANNO_COLORS)
                self.show_toast(
                    '<span foreground="%s">■■</span> %s'
                    % (self.anno_color(),
                       self.ANNO_COLOR_NAMES[self.anno_color_index]),
                    markup=True)
                self.update_anno_overlay()
        elif key in ("p", "P"):
            if self.stack_mode:  # the manifest is authoritative for stacks
                self.show_toast("PPU from stack manifest: %.4g px/%s"
                                % (self.active_level()["ppu"], self.unit))
            else:
                self.ask_ppu()
        elif key in ("plus", "equal", "KP_Add"):
            self.set_view_scale(self.current_view_scale() * self.ZOOM_STEP)
        elif key in ("minus", "KP_Subtract"):
            self.set_view_scale(self.current_view_scale() / self.ZOOM_STEP)
        elif key in ("0", "KP_0"):
            self.set_view_scale(self.active_level()["ppu"])
        elif key in ("f", "F"):
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
        elif key in ("o", "O"):
            if self.stack_mode:
                self.hint_enabled = not self.hint_enabled
                self.update_hint_overlay()
        elif key == "Tab":  # drawing overlays: ruler, annotations, outline
            self.draw_visible = not self.draw_visible
            self.update_view_overlays()
        elif key in ("F11", "Return", "KP_Enter"):
            # Enter as well: remote/VNC clients often swallow F11.
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
        # Dragging pans in BOTH modes; the ruler places its point on the
        # release of a motionless click, so measuring and panning coexist.
        # Root coordinates stay stable while the adjustments move underneath.
        self.drag_origin = (event.x_root, event.y_root,
                            self.scroll.get_hadjustment().get_value(),
                            self.scroll.get_vadjustment().get_value())
        self.drag_panned = False
        if not self.ruler_active:
            self.set_viewport_cursor("grabbing")
        return True

    def on_motion(self, widget, event):
        if self.drag_origin is not None:
            x0, y0, h0, v0 = self.drag_origin
            if not self.drag_panned and \
                    abs(event.x_root - x0) + abs(event.y_root - y0) \
                    > self.DRAG_SLOP:
                self.drag_panned = True  # crossed the click/drag threshold
                self.set_viewport_cursor("grabbing")
            if self.drag_panned:
                self.scroll.get_hadjustment().set_value(
                    h0 - (event.x_root - x0))
                self.scroll.get_vadjustment().set_value(
                    v0 - (event.y_root - y0))
            return True
        if self.ruler_active:
            if self.ruler_start is not None and self.ruler_end is None:
                point = self.event_to_world(event)
                if point is not None:
                    self.ruler_cursor = self.snap_point(point, event.state)
                    self.update_ruler_overlay()
            return True
        if self.anno_tool is not None:
            if self.anno_tool != "text" and self.anno_start is not None:
                point = self.event_to_world(event)
                if point is not None:
                    self.anno_cursor = self.constrain_corner(point,
                                                             event.state)
                    self.update_anno_overlay()
            return True
        return False

    def on_button_release(self, widget, event):
        if event.button != 1 or self.drag_origin is None:
            return False
        self.drag_origin = None
        panned = self.drag_panned
        self.drag_panned = False
        if not self.ruler_active and self.anno_tool is None:
            self.set_viewport_cursor(None)
            return True
        self.set_viewport_cursor(self.tool_cursor())
        if panned:
            return True
        point = self.event_to_world(event)  # a click places a point
        if point is None:
            return True
        if self.ruler_active:
            if self.ruler_start is None or self.ruler_end is not None:
                self.ruler_start = point           # start a new measurement
                self.ruler_end = self.ruler_cursor = None
            else:
                self.ruler_end = self.snap_point(point, event.state)
            self.update_ruler_overlay()
        elif self.anno_tool == "text":
            self.ask_annotation_text(point)
        elif self.anno_start is None:
            self.anno_start = point                # first corner
            self.anno_cursor = None
        else:
            anno = {"kind": self.anno_tool, "a": self.anno_start,
                    "b": self.constrain_corner(point, event.state),
                    "color": self.anno_color()}
            self.annotations.append(anno)
            self.anno_undo.append(("add", anno, None))
            self.anno_rev += 1
            self.anno_start = self.anno_cursor = None
            self.update_anno_overlay()
            self.save_annotations()
        return True

    def tool_cursor(self):
        """Cursor for the active tool, or None for the default pointer."""
        if self.ruler_active:
            return "crosshair"
        return {"box": "cell", "ellipse": "cell", "line": "cell",
                "text": "text"}.get(self.anno_tool)

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
                            "crosshair": Gdk.CursorType.CROSSHAIR,
                            "cell": Gdk.CursorType.PLUS,
                            "text": Gdk.CursorType.XTERM}[name]
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
        "keys: +/- zoom, 0 actual size, f fit, Enter/F11 fullscreen,\n"
        "      Ctrl+wheel zoom, drag to pan, o next-level outline,\n"
        "      i info overlays (help/legend/outline) on/off,\n"
        "      Tab drawing overlays (ruler/annotations) on/off,\n"
        "      [/] stack level, p set PPU,\n"
        "      r ruler (Shift = free angle, Esc ends),\n"
        "      b/e box/ellipse (Shift = square/circle),\n"
        "      l line (Shift = horizontal/vertical/45), t text,\n"
        "      c cycle the annotation color,\n"
        "      BackSpace remove last annotation, u undo add/remove,\n"
        "      Ctrl+C copy the visible view to the clipboard, q quit\n"
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
