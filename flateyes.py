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
import re
import signal
import socket
import struct
import sys
import tempfile
import time
import zlib

APP = "flateyes"        # lowercase: socket names, cache dir, CLI messages
APP_TITLE = "FlatEyes"  # display name
VERSION = "1.2.0"

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
    path = os.path.join(base, key.replace("/", "_") + ".sock")
    if len(path.encode("utf-8")) > 96:
        # sun_path holds ~104 bytes on macOS/BSD, and launchd-style
        # DISPLAY values ("/var/run/.../org.xquartz:0") blow past it;
        # fall back to a digest of the key, still deterministic per
        # (uid, DISPLAY) so forwarders find the owner.
        digest = hashlib.sha1(key.encode("utf-8")).hexdigest()[:16]
        path = os.path.join(base, "%s-%d-%s.sock"
                            % (APP, os.getuid(), digest))
    return path


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
    # PyGObject already ran gtk_init_check() while importing; when it
    # failed (DISPLAY set but the X server unreachable: dead or restarted
    # session, xauth mismatch, ...) the first widget would raise a
    # RuntimeError traceback, so report it cleanly here instead.
    ok = Gtk.init_check(sys.argv)  # GTK3 returns (bool, argv)
    if isinstance(ok, tuple):
        ok = ok[0]
    if not ok:
        sys.stderr.write(
            "%s: cannot open display %s (X session not reachable)\n"
            % (APP, os.environ.get("DISPLAY", "")))
        sys.exit(3)


def workarea_size():
    try:
        display = Gdk.Display.get_default()
        monitor = display.get_primary_monitor() or display.get_monitor(0)
        area = monitor.get_workarea()
        return area.width, area.height
    except AttributeError:  # GTK < 3.22
        screen = Gdk.Screen.get_default()
        return screen.get_width(), screen.get_height()


_image_extensions = None


def image_extensions():
    """Lowercase filename extensions GdkPixbuf can decode."""
    global _image_extensions
    if _image_extensions is None:
        _image_extensions = set()
        for fmt in GdkPixbuf.Pixbuf.get_formats():
            _image_extensions.update(fmt.get_extensions())
    return _image_extensions


def natural_key(name):
    # "img2" sorts before "img10": with a capture group re.split alternates
    # text and digit parts, so items at the same position share a type.
    return [int(part) if part.isdigit() else part
            for part in re.split(r"(\d+)", name.lower())]


# ---------------------------------------------------------------------------
# png metadata embedding (Ctrl+S)
#
# For PNGs the .fe metadata lives inside the image itself, as an iTXt chunk
# (UTF-8, keyword "flateyes") before IEND, written only on an explicit
# Ctrl+S — no sidecar.  Decoders must skip unknown ancillary chunks, so the
# file stays a plain PNG everywhere else, but a copy carries its annotations
# along.  Other formats have no such slot; Ctrl+S writes their .fe sidecar
# instead (nothing autosaves either way).
# ---------------------------------------------------------------------------

PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"
PNG_META_KEYWORD = b"flateyes"


def is_png_file(path):
    try:
        with open(path, "rb") as handle:
            return handle.read(8) == PNG_SIGNATURE
    except OSError:
        return False


def parse_itxt(body):
    """Text of a flateyes iTXt chunk body; None when it is not ours."""
    if not body.startswith(PNG_META_KEYWORD + b"\x00") \
            or len(body) < len(PNG_META_KEYWORD) + 3:
        return None
    rest = body[len(PNG_META_KEYWORD) + 1:]
    compressed = rest[0] == 1   # rest[1] is the compression method
    rest = rest[2:]
    for _ in range(2):          # language tag, translated keyword
        _, sep, rest = rest.partition(b"\x00")
        if not sep:
            return None
    try:
        if compressed:
            rest = zlib.decompress(rest)
        return rest.decode("utf-8")
    except (zlib.error, UnicodeDecodeError):
        return None


def read_png_metadata(path):
    """Embedded flateyes metadata text from a PNG, or None.  Walks chunk
    headers with seeks, so large images only cost a few reads."""
    try:
        with open(path, "rb") as handle:
            if handle.read(8) != PNG_SIGNATURE:
                return None
            while True:
                head = handle.read(8)
                if len(head) < 8:
                    return None
                length, ctype = struct.unpack(">I4s", head)
                if ctype == b"IEND":
                    return None
                if ctype == b"iTXt":
                    body = handle.read(length)
                    if len(body) < length:
                        return None
                    text = parse_itxt(body)
                    if text is not None:
                        return text
                    handle.seek(4, 1)           # CRC
                else:
                    handle.seek(length + 4, 1)  # data + CRC
    except OSError:
        return None


def write_png_metadata(path, text):
    """Rewrite the PNG at path with our iTXt chunk inserted before IEND
    (a previous flateyes chunk is dropped; text=None just removes it).
    Pixel chunks are copied verbatim; the swap is atomic via os.replace,
    so an interrupted save never corrupts the original."""
    with open(path, "rb") as handle:
        blob = handle.read()
    if not blob.startswith(PNG_SIGNATURE):
        raise ValueError("not a PNG")
    out = [PNG_SIGNATURE]
    pos = len(PNG_SIGNATURE)
    done = False
    while pos + 8 <= len(blob):
        length, ctype = struct.unpack(">I4s", blob[pos:pos + 8])
        end = pos + 8 + length + 4
        if end > len(blob):
            raise ValueError("truncated PNG")
        if ctype == b"iTXt" \
                and parse_itxt(blob[pos + 8:end - 4]) is not None:
            pos = end   # drop the previous flateyes chunk
            continue
        if ctype == b"IEND":
            if text is not None:
                # keyword NUL, flag+method 0 (uncompressed), empty
                # language tag and translated keyword, then the text
                body = (PNG_META_KEYWORD + b"\x00\x00\x00\x00\x00"
                        + text.encode("utf-8"))
                out.append(struct.pack(">I", len(body)) + b"iTXt" + body
                           + struct.pack(">I", zlib.crc32(b"iTXt" + body)))
            out.append(blob[pos:])  # IEND and any trailing bytes verbatim
            done = True
            break
        out.append(blob[pos:end])
        pos = end
    if not done:
        raise ValueError("no IEND chunk")
    folder = os.path.dirname(os.path.abspath(path))
    fd, tmp = tempfile.mkstemp(prefix=".flateyes-", dir=folder)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(b"".join(out))
        os.chmod(tmp, os.stat(path).st_mode & 0o7777)
        os.replace(tmp, path)
    except OSError:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


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
    THUMB_SIZE = 120             # thumbnail browser: image cell size
    ANNO_CASING = 0x000000A0     # shape annotation outline
    # One palette for the line and background pickers ("c" dialog).
    # English labels only: X servers without Hangul fonts (e.g. XQuartz)
    # render Korean UI text as boxes.
    PALETTE = (("black", "#000000"), ("white", "#FFFFFF"),
               ("red", "#FF5040"), ("orange", "#FF9F1A"),
               ("green", "#3DDC55"), ("sky", "#35C5FF"),
               ("pink", "#FF4FD8"))
    DEFAULT_LINE = "#FF5040"     # red: visible on most captures
    DEFAULT_BG = "#000000"
    HELP_KEYS = (("+/-", "zoom"), ("0", "1:1"), ("f", "fit"),
                 ("Enter", "full"), (",/.", "file"), ("b", "browse"),
                 ("drag", "pan"), ("Ctrl+wheel", "zoom"),
                 ("r", "ruler"), ("d", "draw"), ("t", "text"),
                 ("s", "select"), ("u/y", "undo/redo"),
                 ("Ctrl+C", "copy"), ("Ctrl+S", "save"), ("p", "PPU"),
                 ("o", "outline"), ("[/]", "level"), ("i", "info"),
                 ("Tab", "overlays"), ("q", "quit"))

    def __init__(self, server_sock, first_path, first_legend=None,
                 ppu=None, unit=None, stack=False, levels=None,
                 annos=None):
        self.server_sock = server_sock
        self.path = None
        self.capture_pending = False  # a Ctrl+C grab is waiting to run
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
        self.window.connect("delete-event", self.on_delete_event)
        self.window.connect("key-press-event", self.on_key)
        self.window.connect("focus-in-event", self.on_focus_in)

        # Thumbnail browser ("b"): a second screen listing one folder's
        # subfolders and images.  Only a single level is read at a time,
        # so deep trees stay fast (the old Shift+,/. walked them all).
        self.browser_active = False
        self.browser_folder = None
        self.thumb_queue = []       # (row index, path) pending thumbnails
        self.thumb_source = None    # idle handler feeding them
        self.icon_cache = {}
        self.browser_store = Gtk.ListStore(GdkPixbuf.Pixbuf, str, str, bool)
        self.browser_view = Gtk.IconView(model=self.browser_store)
        self.browser_view.set_pixbuf_column(0)
        self.browser_view.set_text_column(1)
        self.browser_view.set_item_width(self.THUMB_SIZE + 16)
        self.browser_view.connect("item-activated", self.on_browser_activate)
        self.browser_scroll = Gtk.ScrolledWindow()
        self.browser_scroll.set_policy(Gtk.PolicyType.AUTOMATIC,
                                       Gtk.PolicyType.AUTOMATIC)
        self.browser_scroll.add(self.browser_view)
        self.browser_status = Gtk.Label()
        self.browser_status.set_halign(Gtk.Align.START)
        self.browser_status.set_margin_start(8)
        self.browser_status.set_margin_top(2)
        self.browser_status.set_margin_bottom(2)
        self.browser_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        self.browser_box.pack_start(self.browser_scroll, True, True, 0)
        self.browser_box.pack_start(self.browser_status, False, False, 0)
        self.browser_box.set_no_show_all(True)

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

        # The file's full path sits at the bottom-right (the legend moves
        # up to clear it), the scale/size/ppu readout at the bottom-left,
        # so the window title only needs to fit the file name.
        self.path_label = Gtk.Label()
        self.path_tooltip = None    # full path when the readout is shortened
        self.path_label.set_name("flateyes-status")
        self.path_label.set_halign(Gtk.Align.END)
        self.path_label.set_valign(Gtk.Align.END)
        self.path_label.set_margin_end(8)
        self.path_label.set_margin_bottom(8)
        self.path_label.set_no_show_all(True)
        self.status_label = Gtk.Label()
        self.status_label.set_name("flateyes-status")
        self.status_label.set_halign(Gtk.Align.START)
        self.status_label.set_valign(Gtk.Align.END)
        self.status_label.set_margin_start(8)
        self.status_label.set_margin_bottom(8)
        self.status_label.set_no_show_all(True)

        # Transient feedback message (e.g. after copying to the clipboard).
        # While a drawing mode is active, mode_toast holds a persistent
        # text that stays up and returns after transient toasts expire.
        self.toast_timeout = None
        self.mode_toast = None
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
                       self.status_label, self.path_label):
            widget.get_style_context().add_provider(
                css, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        self.chip_css = css  # for dynamically created readout labels
        # Annotations: boxes/ellipses stamped into one viewport-sized
        # overlay pixbuf, texts as Pango labels; all anchored in world
        # coordinates like the ruler.
        self.anno_tool = None       # "box" | "ellipse" | "text"
        self.anno_start = None      # first corner (world)
        self.anno_cursor = None     # preview corner (world)
        self.annotations = []       # committed shapes and texts
        self.is_png = False         # PNG: annotations embed on Ctrl+S,
        self.embedded_meta = False  # ... and this file carries a chunk
        self.anno_undo = []         # ("add"|"remove", anno, index) or
        self.anno_redo = []         # ... ("move", anno, (dx, dy) world);
                                    # redo is cleared by any new action
        self.anno_rev = 0           # bumped on any change for the key cache
        self.anno_drawn = None
        self.anno_selected = None   # annotation picked with "s" (keyboard)
        self.anno_edit_anchor = None  # "a"/"b": arrows resize that anchor
        self.anno_dirty = False     # metadata differs from the saved state
        self.saved_meta = []        # serialization at load/save time
        self.anno_font_size = 16    # last used text size (pt), sticky
        # Shape drawing ("d" dialog): kind, outline color, interior fill.
        self.anno_shape = "box"     # last drawn kind, preselected
        self.anno_line_width = 1    # stroke width px (lines and outlines)
        self.anno_line_dash = 0     # ... and 0 solid | 1 dashed | 2 dotted
        self.anno_casing = True     # dark halo around outlines and lines
        self.anno_line_color = self.DEFAULT_LINE
        self.anno_outline = True                # draw the box/ellipse border
        self.anno_fill = True                   # fill the box/ellipse
        self.anno_fill_color = self.DEFAULT_BG
        self.anno_fill_opaque = False           # off = translucent 0.35
        # Text style (text dialog), sticky but separate from the shapes.
        self.anno_text_color = self.DEFAULT_LINE
        self.anno_text_bg = True                # backdrop on/off
        self.anno_text_bg_color = self.DEFAULT_BG
        self.anno_text_bg_opaque = False
        self.anno_image = Gtk.Image()
        self.anno_image.set_halign(Gtk.Align.START)
        self.anno_image.set_valign(Gtk.Align.START)
        self.anno_image.set_no_show_all(True)

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
        self.legend_frame.set_margin_bottom(40)  # clear the path readout
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
        self.overlay.add_overlay(self.path_label)
        self.overlay.add_overlay(self.toast_label)
        for child in (self.legend_frame, self.hint_image, self.anno_image,
                      self.ruler_line, self.ruler_label, self.help_label,
                      self.status_label, self.path_label, self.toast_label):
            try:
                # Let clicks/wheel over the overlays fall through to the image.
                self.overlay.set_overlay_pass_through(child, True)
            except AttributeError:  # GTK < 3.18
                break
        # Pass-through children never see pointer events, so a tooltip set
        # on the path label itself would never trigger; answer for it here.
        self.overlay.set_has_tooltip(True)
        self.overlay.connect("query-tooltip", self.on_overlay_query_tooltip)
        self.overlay.connect("size-allocate", self.on_overlay_allocate)
        root_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        root_box.pack_start(self.overlay, True, True, 0)
        root_box.pack_start(self.browser_box, True, True, 0)
        self.window.add(root_box)

        start_folder = None
        if levels is None and not stack and os.path.isdir(first_path):
            start_folder = os.path.abspath(first_path)
        if start_folder is None:
            error = self.load(first_path, first_legend, stack=stack,
                              levels=levels)
            if error != "OK":
                sys.stderr.write("%s\n" % error)
                sys.exit(1)
            self.apply_request_annotations(annos or [])
            self.set_initial_size()
        else:  # folder request: start in the thumbnail browser
            work_w, work_h = workarea_size()
            self.window.set_default_size(int(work_w * 0.72),
                                         int(work_h * 0.85))
        self.window.show_all()
        self.apply_help_visibility()
        if start_folder is not None:
            self.enter_browser(start_folder)

        GLib.io_add_watch(server_sock.fileno(), GLib.IO_IN, self.on_incoming)
        for signum in (signal.SIGINT, signal.SIGTERM):
            try:
                GLib.unix_signal_add(GLib.PRIORITY_DEFAULT, signum,
                                     lambda *a: (Gtk.main_quit(), False)[1])
            except AttributeError:
                pass

    # -- image loading -----------------------------------------------------

    def open_request(self, path, legend=None, ppu=None, unit=None,
                     stack=False, levels=None, annos=None):
        """An incoming open: folders switch to the thumbnail browser,
        anything else loads as an image/stack."""
        if levels is None and not stack and os.path.isdir(path):
            if annos:
                return "ERR annotations need an image, not a folder: %s" \
                    % path
            self.enter_browser(os.path.abspath(path))
            return "OK"
        result = self.load(path, legend, ppu, unit, stack, levels)
        if result == "OK":
            self.apply_request_annotations(annos or [])
            if self.browser_active:
                self.leave_browser()
        return result

    def load(self, path, legend_path=None, ppu=None, unit=None, stack=False,
             levels=None):
        stack = stack or levels is not None
        if not stack and os.path.isdir(path):
            # folders open in the thumbnail browser, never here
            return "ERR is a folder: %s" % path
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
        self.set_ruler_active(False)
        self.clear_annotations()
        self.load_annotations()  # may restore this file's saved ppu/unit
        # PPU/unit precedence: an explicit request field beats the file's
        # saved value beats the stack manifest beats stickiness (the value
        # kept from the previous image).
        if stack_unit:
            self.unit = stack_unit
        if ppu is not None:
            self.ppu = ppu
        if unit is not None:
            self.unit = unit
        # The as-loaded state (request ppu included) is the clean baseline
        # for the title's unsaved marker.
        self.saved_meta = self.serialize_annotations()
        self.anno_dirty = False
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

    # -- folder browsing ----------------------------------------------------

    def folder_images(self, folder=None):
        """Decodable images in a folder (default: the current file's)."""
        if folder is None:
            folder = os.path.dirname(os.path.abspath(self.path or ""))
        try:
            names = os.listdir(folder)
        except OSError as exc:
            self.show_toast(str(exc))
            return []
        exts = image_extensions()
        names = [name for name in names if not name.startswith(".")
                 and os.path.splitext(name)[1].lstrip(".").lower() in exts]
        names.sort(key=natural_key)
        return [os.path.join(folder, name) for name in names]

    def browse_folder(self, step):
        if self.stack_mode:  # the folder holds the stack's own level images
            self.show_toast("folder browsing is off in stack mode")
            return
        files = self.folder_images()
        current = os.path.abspath(self.path or "")
        if current in files:
            start = files.index(current)
        else:  # hidden/renamed current file: enter the list at its sort slot
            key = natural_key(os.path.basename(current))
            below = sum(1 for path in files
                        if natural_key(os.path.basename(path)) < key)
            start = below - 1 if step > 0 else below
        candidates = [files[(start + step * n) % len(files)]
                      for n in range(1, len(files) + 1)] if files else []
        candidates = [path for path in candidates if path != current]
        if not candidates:
            self.show_toast("no other images in this folder")
            return
        if not self.confirm_unsaved():
            return  # keep the image and its unsaved changes
        error = None
        for target in candidates:  # skip over files that fail to decode
            result = self.load(target)
            if result == "OK":
                self.show_toast("(%d/%d) %s"
                                % (files.index(target) + 1, len(files),
                                   os.path.basename(target)))
                return
            error = result
        self.show_toast(error)

    # -- thumbnail browser ("b") -------------------------------------------

    def browser_icon(self, kind):
        """Fixed cells drawn with pixbuf fills (no cairo, and the icon
        theme may be missing on bare X servers): "folder", "up",
        "loading" and "broken"."""
        if kind in self.icon_cache:
            return self.icon_cache[kind]
        size = self.THUMB_SIZE
        icon = GdkPixbuf.Pixbuf.new(GdkPixbuf.Colorspace.RGB, True, 8,
                                    size, int(size * 0.75))
        icon.fill(0x00000000)
        w, h = icon.get_width(), icon.get_height()
        if kind in ("folder", "up"):
            tab_w, tab_h, top = int(w * 0.38), int(h * 0.16), int(h * 0.08)
            body_top = top + tab_h - 2
            edge, face = 0x8A6D1EFF, 0xE8C15AFF
            icon.new_subpixbuf(4, top, tab_w, tab_h).fill(edge)
            icon.new_subpixbuf(5, top + 1, tab_w - 2, tab_h - 2).fill(face)
            icon.new_subpixbuf(4, body_top, w - 8, h - body_top - 2) \
                .fill(edge)
            icon.new_subpixbuf(5, body_top + 1, w - 10,
                               h - body_top - 4).fill(face)
            if kind == "up":  # a darker chevron block pointing up
                icon.new_subpixbuf(w // 2 - 6, body_top + 8, 12,
                                   h - body_top - 18).fill(edge)
                icon.new_subpixbuf(w // 2 - 12, body_top + 14, 24,
                                   6).fill(edge)
        else:
            shade = 0x555555FF if kind == "broken" else 0x777777FF
            icon.new_subpixbuf(4, 2, w - 8, h - 4).fill(0x333333FF)
            icon.new_subpixbuf(5, 3, w - 10, h - 6).fill(shade)
        self.icon_cache[kind] = icon
        return icon

    def enter_browser(self, folder=None, select=None):
        """Switch to the thumbnail browser (one folder at a time)."""
        if folder is None:
            folder = os.path.dirname(os.path.abspath(self.path or "")) \
                or os.getcwd()
        self.browser_active = True
        self.overlay.hide()
        self.browser_box.set_no_show_all(False)
        self.browser_box.show_all()
        self.populate_browser(folder, select)
        self.browser_view.grab_focus()

    def leave_browser(self):
        """Back to the image screen (only reachable with an image)."""
        del self.thumb_queue[:]
        self.browser_active = False
        self.browser_box.hide()
        self.overlay.show()
        self.scroll.grab_focus()  # arrow keys pan again
        self.update_title()

    def populate_browser(self, folder, select=None):
        """One os.listdir deep: subfolders first, then this folder's
        images.  Thumbnails stream in from an idle handler."""
        folder = os.path.abspath(folder)
        self.browser_folder = folder
        self.browser_store.clear()
        del self.thumb_queue[:]
        try:
            names = [n for n in os.listdir(folder) if not n.startswith(".")]
        except OSError as exc:
            names = []
            self.browser_status.set_text("cannot read folder: %s" % exc)
        dirs = sorted((n for n in names
                       if os.path.isdir(os.path.join(folder, n))),
                      key=natural_key)
        images = self.folder_images(folder)
        parent = os.path.dirname(folder)
        if parent and parent != folder:
            self.browser_store.append(
                [self.browser_icon("up"), "..", parent, True])
        for name in dirs:
            self.browser_store.append(
                [self.browser_icon("folder"), name,
                 os.path.join(folder, name), True])
        cursor = None
        for path in images:
            row = len(self.browser_store)
            self.browser_store.append(
                [self.browser_icon("loading"), os.path.basename(path),
                 path, False])
            self.thumb_queue.append((row, path))
            if select and os.path.abspath(select) == os.path.abspath(path):
                cursor = row
        if self.thumb_queue and self.thumb_source is None:
            self.thumb_source = GLib.idle_add(self.on_thumb_idle)
        if cursor is not None:
            tree_path = Gtk.TreePath(cursor)
            self.browser_view.select_path(tree_path)
            self.browser_view.set_cursor(tree_path, None, False)
            GLib.idle_add(self.browser_view.scroll_to_path,
                          tree_path, True, 0.5, 0.5)
        self.window.set_title("%s - %s" % (folder, APP_TITLE))
        self.browser_status.set_text(
            "%s   %d folder%s, %d image%s   "
            "(Enter opens, BackSpace up, Esc back, q quits)"
            % (folder, len(dirs), "" if len(dirs) == 1 else "s",
               len(images), "" if len(images) == 1 else "s"))

    def on_thumb_idle(self):
        """Fill in one thumbnail per idle pass; the queue is replaced
        whenever the folder changes, so stale work just drains away."""
        if not self.thumb_queue or not self.browser_active:
            self.thumb_source = None
            return False
        row, path = self.thumb_queue.pop(0)
        try:
            thumb = GdkPixbuf.Pixbuf.new_from_file_at_scale(
                path, self.THUMB_SIZE, self.THUMB_SIZE, True)
            thumb = thumb.apply_embedded_orientation() or thumb
        except GLib.Error:
            thumb = self.browser_icon("broken")
        if row < len(self.browser_store):
            self.browser_store[row][0] = thumb
        return True

    def on_browser_activate(self, view, tree_path):
        row = self.browser_store[tree_path]
        target, is_dir = row[2], row[3]
        if is_dir:
            self.populate_browser(target)
            return
        current = os.path.abspath(self.path) if self.path else None
        if current == os.path.abspath(target) and self.pixbuf is not None:
            self.leave_browser()  # the image already on screen
            return
        if not self.confirm_unsaved():
            return
        result = self.load(target)
        if result == "OK":
            self.leave_browser()
        else:
            self.browser_status.set_text(result)

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
        if self.anno_dirty:
            name = "*" + name  # unsaved annotation changes
        self.window.set_title("%s - %s" % (name, APP_TITLE))
        full = self.path or ""
        shown = full
        if len(full) > 72:  # keep very long paths on one short line
            shown = full[:24] + "…" + full[-47:]
        self.path_tooltip = full if shown != full else None
        self.path_label.set_text(shown)
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

    def capture_view(self, callback):
        """Grab the visible viewport with the info overlays hidden and hand
        the pixbuf to callback.  Painting only happens on frame clock ticks
        back in the main loop, so the grab runs from a timeout after the
        hidden widgets have actually left the screen."""
        win = self.window.get_window()
        if win is None or self.capture_pending:
            return
        self.capture_pending = True
        self.toast_label.hide()
        hidden = []
        for widget in (self.help_label, self.status_label, self.path_label,
                       self.legend_frame, self.hint_image):
            if widget.get_visible():
                widget.hide()
                hidden.append(widget)

        def grab():
            alloc = self.overlay.get_allocation()
            pixbuf = Gdk.pixbuf_get_from_window(win, alloc.x, alloc.y,
                                                alloc.width, alloc.height)
            for widget in hidden:
                widget.show()
            self.capture_pending = False
            callback(pixbuf)
            return False

        GLib.timeout_add(150, grab)

    def copy_view_to_clipboard(self):
        """Ctrl+C: the visible viewport, info overlays excluded."""
        self.capture_view(self.finish_copy)

    def finish_copy(self, pixbuf):
        if pixbuf is None:
            self.show_toast("copy failed")
            return
        clipboard = Gtk.Clipboard.get(Gdk.SELECTION_CLIPBOARD)
        clipboard.set_image(pixbuf)
        # No clipboard.store(): handing the data to a clipboard manager
        # (e.g. the Exceed TurboX sync agent) can drop the image targets,
        # leaving "no image in clipboard" on paste.  Serving the selection
        # ourselves works everywhere while the viewer is running; the
        # clipboard just empties when it quits.
        self.show_toast("copied  %dx%d" % (pixbuf.get_width(),
                                           pixbuf.get_height()))

    def embed_annotations(self):
        """PNG branch of save_annotations: embed the metadata into the
        viewed PNG itself, so a copied file carries its annotations along.
        With nothing to embed, an existing chunk is removed."""
        lines = self.serialize_annotations()
        text = ("# flateyes annotations\n" + "\n".join(lines) + "\n") \
            if lines else None
        if text is None and not self.embedded_meta:
            self.show_toast("no annotations to embed")
            return
        try:
            write_png_metadata(self.path, text)
        except (OSError, ValueError):
            self.show_toast("embed failed (read-only?)")
            return
        self.embedded_meta = text is not None
        for stale in self.annotation_paths():
            try:
                os.unlink(stale)  # sidecar left behind by an older build
            except OSError:
                pass
        self.saved_meta = lines
        self.update_dirty()
        if text is None:
            self.show_toast("embedded annotations removed")
        else:
            self.show_toast("annotations embedded in %s"
                            % os.path.basename(self.path))

    def toasts_allowed(self):
        """Tab hides every overlay, the toast included."""
        return self.draw_visible or self.info_visible

    def show_toast(self, text, markup=False):
        if not self.toasts_allowed():
            return
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
        if self.mode_toast and self.toasts_allowed():
            self.toast_label.set_markup(self.mode_toast)  # fall back
        else:
            self.toast_label.hide()
        return False

    def update_mode_toast(self):
        """Keep the active mode visible as a persistent toast — drawing
        tools, the keyboard selection and its resize anchor alike.
        Transient toasts overlay it and it returns when they expire."""
        selected = self.valid_selection()
        if selected is not None:
            if self.anno_edit_anchor:
                part = "endpoint" if selected["kind"] in ("line", "ruler") \
                    else "corner"
                text = ("resize: %s %s  (arrows drag it, e next, Esc back)"
                        % (part, self.anno_edit_anchor.upper()))
            else:
                pos = next(i for i, a in enumerate(self.annotations)
                           if a is selected)
                text = ("selected %d/%d: %s  (arrows move, e edit,"
                        " Delete removes, Esc done)"
                        % (len(self.annotations) - pos,
                           len(self.annotations), selected["kind"]))
        elif self.ruler_active:
            text = "ruler: click two points  (Esc ends)"
        elif self.anno_tool == "text":
            text = "text: click to place  (Esc ends)"
        elif self.anno_tool in ("box", "ellipse", "line"):
            text = self.draw_mode_desc() + "  (Esc ends)"
        else:
            text = None
        self.mode_toast = text
        if not self.toasts_allowed():
            self.toast_label.hide()
            return
        if self.toast_timeout is not None:
            return  # a transient toast is up; its expiry restores this
        if text is None:
            self.toast_label.hide()
        else:
            self.toast_label.set_markup(text)
            self.toast_label.show()

    def draw_mode_desc(self):
        """Colored style summary of the active shape tool."""
        stroke = "%dpx %s" % (self.anno_line_width,
                              ("solid", "dashed",
                               "dotted")[self.anno_line_dash])
        if self.anno_tool == "line":
            desc = ('draw line <span foreground="%s">■■</span> %s'
                    % (self.anno_line_color, stroke))
            if not self.anno_casing:
                desc += "  no halo"
            return desc
        parts = ["draw %s:" % self.anno_tool]
        if self.anno_outline:
            parts.append('<span foreground="%s">■■</span> %s outline'
                         % (self.anno_line_color, stroke))
        if self.anno_fill:
            parts.append('<span foreground="%s">■■</span> %s fill'
                         % (self.anno_fill_color,
                            "opaque" if self.anno_fill_opaque
                            else "translucent"))
        if self.anno_outline and not self.anno_casing:
            parts.append("no halo")
        return "  ".join(parts)

    def apply_help_visibility(self):
        if self.info_visible:
            self.help_label.show()
            self.status_label.show()
            self.path_label.show()
        else:
            self.help_label.hide()
            self.status_label.hide()
            self.path_label.hide()

    def apply_legend_visibility(self):
        if self.legend_pixbuf is not None and self.info_visible:
            self.legend_image.show()
            self.legend_frame.show()
        else:
            self.legend_frame.hide()

    def on_overlay_allocate(self, widget, allocation):
        self.render_legend(allocation)

    def on_overlay_query_tooltip(self, widget, x, y, keyboard_mode, tooltip):
        if self.path_tooltip is None or not self.path_label.get_visible():
            return False
        coords = widget.translate_coordinates(self.path_label, int(x), int(y))
        if not coords:
            return False
        lx, ly = coords[-2], coords[-1]
        alloc = self.path_label.get_allocation()
        if 0 <= lx < alloc.width and 0 <= ly < alloc.height:
            tooltip.set_text(self.path_tooltip)
            return True
        return False

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
        if active:
            self.clear_selection()
        self.ruler_active = active
        self.ruler_start = self.ruler_end = self.ruler_cursor = None
        self.set_viewport_cursor(self.tool_cursor())
        self.update_view_overlays()
        self.update_mode_toast()

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

    def stamp_segment(self, buf, a, b, casing, core, width=1, dash=0):
        """Stamp a segment; width in px, dash 0=solid 1=dashed 2=dotted.
        casing/core may each be None to draw a single pass (multi-segment
        shapes stamp all casing first, then all core, to keep corners).
        The dash phase is anchored at a, so it holds still while panning."""
        ax, ay = a
        bx, by = b
        if dash == 0 and ay == by:    # horizontal, solid: two flat rects
            y0 = ay - width // 2
            if casing is not None:
                self.fill_rect(buf, min(ax, bx), y0 - 1,
                               abs(bx - ax) + 1, width + 2, casing)
            if core is not None:
                self.fill_rect(buf, min(ax, bx), y0,
                               abs(bx - ax) + 1, width, core)
        elif dash == 0 and ax == bx:  # vertical, solid
            x0 = ax - width // 2
            if casing is not None:
                self.fill_rect(buf, x0 - 1, min(ay, by),
                               width + 2, abs(by - ay) + 1, casing)
            if core is not None:
                self.fill_rect(buf, x0, min(ay, by),
                               width, abs(by - ay) + 1, core)
        else:           # free angle or dashed: 1px-spaced dabs
            seg = self.clip_segment(a, b, buf.get_width(),
                                    buf.get_height())
            if seg is None:
                return
            (sx, sy), (ex, ey) = seg
            steps = min(int(max(abs(ex - sx), abs(ey - sy))) + 1, 8000)
            spacing = math.hypot(ex - sx, ey - sy) / max(steps, 1)
            base = math.hypot(sx - ax, sy - ay)  # clipped-away length
            if dash == 1:
                on, period = 3 * width + 3, 5 * width + 6
            elif dash == 2:
                on, period = 1, 3 * width + 3
            else:
                on = period = 1
            points = [(sx + (ex - sx) * i / steps,
                       sy + (ey - sy) * i / steps)
                      for i in range(steps + 1)
                      if not dash or (base + i * spacing) % period < on]
            off = width // 2 + 1
            if casing is not None:
                for x, y in points:
                    self.fill_rect(buf, x - off, y - off,
                                   width + 2, width + 2, casing)
            if core is not None:
                for x, y in points:
                    self.fill_rect(buf, x - off, y - off,
                                   width + 1, width + 1, core)

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
            self.clear_selection()
        self.anno_tool = tool
        self.anno_start = self.anno_cursor = None
        self.set_viewport_cursor(self.tool_cursor())
        self.update_view_overlays()
        self.update_mode_toast()

    def anno_color(self):
        return self.anno_line_color

    @staticmethod
    def color_rgba(hex_color, alpha=0xFF):
        """"#RRGGBB" -> the 0xRRGGBBAA pixbuf fill value."""
        return (int(hex_color[1:], 16) << 8) | alpha

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
        selected = self.valid_selection()
        texts = [x for x in self.annotations if x["kind"] == "text"]
        rulers = [x for x in self.annotations if x["kind"] == "ruler"]
        shapes = [x for x in self.annotations if x["kind"] != "text"]
        preview = None
        if self.anno_tool in ("box", "ellipse", "line") \
                and self.anno_start is not None \
                and self.anno_cursor is not None:
            preview = {"kind": self.anno_tool, "a": self.anno_start,
                       "b": self.anno_cursor, "color": self.anno_color(),
                       "width": self.anno_line_width,
                       "dash": self.anno_line_dash}
            if self.anno_tool in ("box", "ellipse"):
                if self.anno_fill:
                    preview["fill"] = self.anno_fill_color
                    preview["fill_opaque"] = self.anno_fill_opaque
                if not self.anno_outline:
                    preview["outline"] = False
            if not self.anno_casing:
                preview["casing"] = False
        if not self.draw_visible or self.rendered_size is None \
                or not (shapes or preview or texts):
            self.anno_drawn = None
            self.anno_image.hide()
            for anno in self.annotations:
                if "label" in anno:
                    anno["label"].hide()
            return
        view = self.scroll.get_allocation()
        # The image allocation belongs in the key: right after a zoom/fit
        # change the overlays are drawn once against the STALE allocation,
        # and without it the corrected layout pass would hit the cache and
        # leave annotations displaced.
        img_alloc = self.image.get_allocation()
        key = (self.anno_rev, self.anno_line_color, self.anno_line_width,
               self.anno_line_dash, self.anno_casing, self.anno_outline,
               self.anno_fill, self.anno_fill_color, self.anno_fill_opaque,
               preview and (preview["a"], preview["b"]),
               self.scroll.get_hadjustment().get_value(),
               self.scroll.get_vadjustment().get_value(),
               self.scale_shown, self.level_index, self.rendered_size,
               self.ppu, self.unit,  # the ruler readouts convert with them
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
        if selected is not None and selected["kind"] != "text":
            a = self.image_px_to_view(self.px_from_world(selected["a"]))
            b = self.image_px_to_view(self.px_from_world(selected["b"]))
            if selected["kind"] in ("box", "ellipse"):
                x0, x1 = sorted((a[0], b[0]))
                y0, y1 = sorted((a[1], b[1]))
                corners = ((x0, y0), (x1, y0), (x0, y1), (x1, y1))
            else:
                corners = (a, b)   # line/ruler: the two endpoints
            active = {"a": a, "b": b}.get(self.anno_edit_anchor)
            self.stamp_selection(buf, corners, active)
        for anno in texts:
            x, y = self.image_px_to_view(self.px_from_world(anno["at"]))
            if -20 <= x <= view.width and -10 <= y <= view.height:
                anno["label"].set_margin_start(int(max(0, x)))
                anno["label"].set_margin_top(int(max(0, y)))
                anno["label"].show()
                if anno is selected:
                    alloc = anno["label"].get_allocation()
                    w, h = max(alloc.width, 10), max(alloc.height, 10)
                    self.stamp_selection(buf, ((x, y), (x + w, y),
                                               (x, y + h), (x + w, y + h)))
            else:
                anno["label"].hide()
        for anno in rulers:
            a = self.image_px_to_view(self.px_from_world(anno["a"]))
            b = self.image_px_to_view(self.px_from_world(anno["b"]))
            mid_x, mid_y = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
            if -40 <= mid_x <= view.width and -20 <= mid_y <= view.height:
                dist = math.hypot(anno["b"][0] - anno["a"][0],
                                  anno["b"][1] - anno["a"][1])
                anno["label"].set_text(self.format_distance(dist))
                anno["label"].set_margin_start(int(max(0, mid_x + 10)))
                anno["label"].set_margin_top(int(max(0, mid_y - 30)))
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
        if shape["kind"] == "ruler":
            self.stamp_segment(buf, a, b, self.RULER_CASING,
                               self.RULER_CORE)
            for x, y in (a, b):  # endpoint markers
                self.fill_rect(buf, x - 3, y - 3, 7, 7, self.RULER_CASING)
                self.fill_rect(buf, x - 2, y - 2, 5, 5, self.RULER_CORE)
            return
        core = self.color_rgba(shape["color"])
        casing = self.ANNO_CASING if shape.get("casing", True) else None
        if shape["kind"] == "line":
            self.stamp_segment(buf, a, b, casing, core,
                               shape.get("width", 1), shape.get("dash", 0))
            return
        x0, x1 = sorted((a[0], b[0]))
        y0, y1 = sorted((a[1], b[1]))
        # The interior paints first so the outline stays on top; fill()
        # replaces pixels (no blending), so the translucent alpha shows
        # the image through the overlay rather than stacking.
        fill_rgba = None
        if shape.get("fill"):
            fill_rgba = self.color_rgba(
                shape["fill"], 0xFF if shape.get("fill_opaque") else 0x59)
        outline = shape.get("outline", True)
        stroke_w = shape.get("width", 1)
        stroke_dash = shape.get("dash", 0)
        if shape["kind"] == "box":
            if fill_rgba is not None:
                self.fill_rect(buf, x0, y0, x1 - x0, y1 - y0, fill_rgba)
            if not outline:
                return
            if stroke_dash == 0:   # solid: flat rects with square corners
                for pass_w, rgba in ((stroke_w + 2, casing),
                                     (stroke_w, core)):
                    if rgba is None:
                        continue  # halo switched off
                    off = pass_w // 2
                    self.fill_rect(buf, x0 - off, y0 - off,
                                   x1 - x0 + pass_w, pass_w, rgba)  # top
                    self.fill_rect(buf, x0 - off, y1 - off,
                                   x1 - x0 + pass_w, pass_w, rgba)  # bottom
                    self.fill_rect(buf, x0 - off, y0 - off,
                                   pass_w, y1 - y0 + pass_w, rgba)  # left
                    self.fill_rect(buf, x1 - off, y0 - off,
                                   pass_w, y1 - y0 + pass_w, rgba)  # right
            else:  # dashed: four edge segments; all casing first so a
                   # later edge cannot cut into a finished corner's core
                corners = ((x0, y0), (x1, y0), (x1, y1), (x0, y1))
                edges = tuple(zip(corners, corners[1:] + corners[:1]))
                if casing is not None:
                    for ea, eb in edges:
                        self.stamp_segment(buf, ea, eb, casing, None,
                                           stroke_w, stroke_dash)
                for ea, eb in edges:
                    self.stamp_segment(buf, ea, eb, None, core,
                                       stroke_w, stroke_dash)
            return
        # ellipse: 1px-spaced dabs along the perimeter
        cx, cy = (x0 + x1) / 2.0, (y0 + y1) / 2.0
        rx, ry = (x1 - x0) / 2.0, (y1 - y0) / 2.0
        buf_w, buf_h = buf.get_width(), buf.get_height()
        if fill_rgba is not None and rx >= 1 and ry >= 1:
            # interior as one span per visible row
            for row in range(max(int(cy - ry) + 1, 0),
                             min(int(cy + ry) + 1, buf_h)):
                offset = (row - cy) / ry
                half = rx * math.sqrt(max(0.0, 1.0 - offset * offset))
                self.fill_rect(buf, cx - half, row, 2 * half, 1, fill_rgba)
        if not outline:
            return
        steps = min(max(int(6.4 * max(rx, ry)), 16), 8000)
        if stroke_dash == 1:
            on, period = 3 * stroke_w + 3, 5 * stroke_w + 6
        elif stroke_dash == 2:
            on, period = 1, 3 * stroke_w + 3
        else:
            on = period = 1
        margin = 3 + stroke_w
        points = []
        prev = None
        cum = 0.0   # dash pattern runs along the arc length
        for i in range(steps):
            x = cx + rx * math.cos(2 * math.pi * i / steps)
            y = cy + ry * math.sin(2 * math.pi * i / steps)
            if prev is not None:
                cum += math.hypot(x - prev[0], y - prev[1])
            prev = (x, y)
            if stroke_dash and cum % period >= on:
                continue
            if -margin <= x <= buf_w + margin \
                    and -margin <= y <= buf_h + margin:
                points.append((x, y))
        off = stroke_w // 2 + 1
        if casing is not None:
            for x, y in points:
                self.fill_rect(buf, x - off, y - off,
                               stroke_w + 2, stroke_w + 2, casing)
        for x, y in points:
            self.fill_rect(buf, x - off, y - off,
                           stroke_w + 1, stroke_w + 1, core)

    def stamp_selection(self, buf, points, active=None):
        """Corner handles marking the keyboard-selected annotation; the
        anchor the arrows drag ("e") grows a white core."""
        for x, y in points:
            self.fill_rect(buf, x - 5, y - 5, 11, 11, self.RULER_CASING)
            self.fill_rect(buf, x - 3, y - 3, 7, 7, self.RULER_CORE)
        if active is not None:
            x, y = active
            self.fill_rect(buf, x - 6, y - 6, 13, 13, self.RULER_CASING)
            self.fill_rect(buf, x - 4, y - 4, 9, 9, 0xFFFFFFFF)

    def ask_annotation_text(self, point, edit=None):
        """Text dialog: creates an annotation at point, or reworks the
        existing one passed as edit (selection + "e")."""
        dialog = Gtk.Dialog(title="Edit Text" if edit else "Text",
                            transient_for=self.window, modal=True)
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
        init = edit if edit is not None else {
            "size": self.anno_font_size, "color": self.anno_text_color,
            "bg": self.anno_text_bg, "bg_color": self.anno_text_bg_color,
            "bg_opaque": self.anno_text_bg_opaque}
        if edit is not None:
            editable.set_text(edit["text"])
            editable.set_position(len(edit["text"]))
        spin = Gtk.SpinButton.new_with_range(6, 96, 1)
        spin.set_value(init["size"])
        # Built-in hangul input for hosts without an input method.
        hangul = Gtk.CheckButton(label="Hangul (Shift+Space)")
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
        text_combo = self.color_combo(init["color"])
        bgcheck = Gtk.CheckButton(label="background")
        bgcheck.set_active(init["bg"])
        bg_combo = self.color_combo(init["bg_color"])
        opaque = Gtk.CheckButton(label="opaque")
        opaque.set_active(init["bg_opaque"])

        def sync_bg_widgets(*args):
            for widget in (bg_combo, opaque):
                widget.set_sensitive(bgcheck.get_active())

        bgcheck.connect("toggled", sync_bg_widgets)
        sync_bg_widgets()
        hexes = [hex_ for _, hex_ in self.PALETTE]
        # Live preview: the entered text tracks the chosen size, text
        # color and backdrop settings.  A buffer tag re-applied on every
        # change works on any GTK3, unlike the 3.20+ "textview" CSS node
        # or the deprecated override_font.
        preview_tag = view.get_buffer().create_tag(
            None, size_points=float(init["size"]),
            foreground=init["color"])

        def apply_preview(*args):
            buf = view.get_buffer()
            preview_tag.props.size_points = spin.get_value()
            preview_tag.props.foreground = \
                hexes[max(text_combo.get_active(), 0)]
            if bgcheck.get_active():
                rgba = Gdk.RGBA()
                rgba.parse(hexes[max(bg_combo.get_active(), 0)])
                rgba.alpha = 1.0 if opaque.get_active() else 0.35
                preview_tag.props.background_rgba = rgba
                preview_tag.props.background_set = True
            else:
                preview_tag.props.background_set = False
            buf.apply_tag(preview_tag, buf.get_start_iter(),
                          buf.get_end_iter())

        spin.connect("value-changed", apply_preview)
        text_combo.connect("changed", apply_preview)
        bg_combo.connect("changed", apply_preview)
        bgcheck.connect("toggled", apply_preview)
        opaque.connect("toggled", apply_preview)
        view.get_buffer().connect("changed", apply_preview)
        apply_preview()
        row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        row.pack_start(Gtk.Label(label="size (pt)"), False, False, 0)
        row.pack_start(spin, False, False, 0)
        row.pack_start(hangul, False, False, 12)
        bgrow = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        bgrow.pack_start(Gtk.Label(label="text"), False, False, 0)
        bgrow.pack_start(text_combo, False, False, 0)
        bgrow.pack_start(bgcheck, False, False, 6)
        bgrow.pack_start(bg_combo, False, False, 0)
        bgrow.pack_start(opaque, False, False, 6)
        hint = Gtk.Label()
        hint.set_markup("<small>Enter: new line · Ctrl+Enter: OK</small>")
        hint.set_halign(Gtk.Align.START)
        box = dialog.get_content_area()
        box.set_border_width(10)
        box.set_spacing(6)
        box.pack_start(scroll, True, True, 0)
        box.pack_start(row, False, False, 0)
        box.pack_start(bgrow, False, False, 0)
        box.pack_start(hint, False, False, 0)
        dialog.show_all()
        confirmed = dialog.run() == Gtk.ResponseType.OK
        text = editable.get_text().strip()
        size = int(spin.get_value())
        text_color = hexes[max(text_combo.get_active(), 0)]
        bg = bgcheck.get_active()
        bg_color = hexes[max(bg_combo.get_active(), 0)]
        bg_opaque = opaque.get_active()
        dialog.destroy()
        if not confirmed or not text:
            return  # emptied text is a cancel; deleting is the Delete key
        self.anno_font_size = size
        self.anno_text_color = text_color
        self.anno_text_bg = bg
        self.anno_text_bg_color = bg_color
        self.anno_text_bg_opaque = bg_opaque
        new = {"text": text, "size": size, "color": text_color, "bg": bg,
               "bg_color": bg_color, "bg_opaque": bg_opaque}
        if edit is not None:
            old = dict((k, edit[k]) for k in new)
            if new == old:
                return
            self.apply_text_fields(edit, new)
            self.anno_undo.append(("edit", edit, (old, new)))
        else:
            self.add_text_annotation(point, text, size, text_color, bg,
                                     bg_color, bg_opaque)
            self.anno_undo.append(("add", self.annotations[-1], None))
        del self.anno_redo[:]
        self.anno_rev += 1
        self.update_anno_overlay()
        self.update_dirty()

    def make_text_label(self, text, size, color, bg, bg_color, bg_opaque):
        """A styled overlay label for one text annotation."""
        label = Gtk.Label()
        label.set_halign(Gtk.Align.START)
        label.set_valign(Gtk.Align.START)
        label.set_no_show_all(True)
        label.set_markup('<span font="%d" foreground="%s">%s</span>'
                         % (size, color, GLib.markup_escape_text(text)))
        if bg:
            provider = Gtk.CssProvider()
            provider.load_from_data(
                ("label { background-color: %s; padding: 0px 3px;"
                 " border-radius: 2px; }"
                 % self.css_rgba(bg_color, 1.0 if bg_opaque else 0.35))
                .encode("utf-8"))
            label.get_style_context().add_provider(
                provider, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        self.overlay.add_overlay(label)
        try:
            self.overlay.set_overlay_pass_through(label, True)
        except AttributeError:  # GTK < 3.18
            pass
        return label

    def apply_text_fields(self, anno, fields):
        """Restyle a text annotation in place (edit, and its undo/redo):
        the label is rebuilt because the backdrop CSS cannot change."""
        anno.update(fields)
        self.overlay.remove(anno["label"])
        anno["label"] = self.make_text_label(
            anno["text"], anno["size"], anno["color"], anno["bg"],
            anno["bg_color"], anno["bg_opaque"])

    def add_text_annotation(self, point, text, size, color, bg=True,
                            bg_color="#000000", bg_opaque=False):
        label = self.make_text_label(text, size, color, bg, bg_color,
                                     bg_opaque)
        self.annotations.append({"kind": "text", "at": point,
                                 "text": text, "size": size,
                                 "color": color, "bg": bg,
                                 "bg_color": bg_color,
                                 "bg_opaque": bg_opaque, "label": label})
        self.anno_rev += 1

    @staticmethod
    def css_rgba(color, alpha):
        """'#RRGGBB' + alpha as a CSS rgba() literal."""
        return "rgba(%d,%d,%d,%.2f)" % (int(color[1:3], 16),
                                        int(color[3:5], 16),
                                        int(color[5:7], 16), alpha)

    @staticmethod
    def color_swatch(color, width=24, height=14):
        """Solid '#RRGGBB' sample pixbuf with a 1px gray frame (so white
        stays visible); fill/subpixbuf only — no cairo on the targets."""
        swatch = GdkPixbuf.Pixbuf.new(GdkPixbuf.Colorspace.RGB, True, 8,
                                      width, height)
        swatch.fill(0x808080FF)
        swatch.new_subpixbuf(1, 1, width - 2, height - 2).fill(
            Viewer.color_rgba(color))
        return swatch

    def color_combo(self, active):
        """Palette dropdown: a swatch pixbuf next to each color name."""
        store = Gtk.ListStore(GdkPixbuf.Pixbuf, str)
        for name, hex_ in self.PALETTE:
            store.append([self.color_swatch(hex_), name])
        combo = Gtk.ComboBox(model=store)
        swatch_cell = Gtk.CellRendererPixbuf()
        combo.pack_start(swatch_cell, False)
        combo.add_attribute(swatch_cell, "pixbuf", 0)
        name_cell = Gtk.CellRendererText()
        combo.pack_start(name_cell, True)
        combo.add_attribute(name_cell, "text", 1)
        hexes = [hex_ for _, hex_ in self.PALETTE]
        combo.set_active(hexes.index(active) if active in hexes else 0)
        return combo

    def ask_draw_shape(self):
        """"d": the one shape-drawing dialog — pick box/ellipse/line plus
        the style (outline color, box/ellipse interior fill), OK starts
        the drawing mode.  Texts pick their own colors in the "t" dialog;
        the ruler keeps its fixed color."""
        if self.pixbuf is None:
            return  # animations are shown unscaled and unannotated
        dialog = Gtk.Dialog(title="Draw", transient_for=self.window,
                            modal=True)
        dialog.set_keep_above(True)  # stay over a fullscreen parent
        dialog.add_button("Cancel", Gtk.ResponseType.CANCEL)
        dialog.add_button("OK", Gtk.ResponseType.OK)
        dialog.set_default_response(Gtk.ResponseType.OK)
        current = self.anno_tool \
            if self.anno_tool in ("box", "ellipse", "line") \
            else self.anno_shape
        shape_row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL,
                            spacing=10)
        radios = {}
        group = None
        for kind in ("box", "ellipse", "line"):
            radio = Gtk.RadioButton.new_with_label_from_widget(group, kind)
            group = group if group is not None else radio
            radio.set_active(kind == current)
            radios[kind] = radio
            shape_row.pack_start(radio, False, False, 0)
        line_combo = self.color_combo(self.anno_line_color)
        fill_combo = self.color_combo(self.anno_fill_color)
        use_outline = Gtk.CheckButton(label="use")
        use_outline.set_active(self.anno_outline)
        use_fill = Gtk.CheckButton(label="use")
        use_fill.set_active(self.anno_fill)
        fill_opaque = Gtk.CheckButton(label="opaque")
        fill_opaque.set_active(self.anno_fill_opaque)
        # The color row doubles up: the box/ellipse outline, or the line
        # color itself while the line shape is chosen — retitled live.
        outline_label = Gtk.Label(label="outline")
        # Stroke style for lines and box/ellipse outlines.
        width_label = Gtk.Label(label="width (px)")
        width_spin = Gtk.SpinButton.new_with_range(1, 8, 1)
        width_spin.set_value(self.anno_line_width)
        type_combo = Gtk.ComboBoxText()
        for name in ("solid", "dashed", "dotted"):
            type_combo.append_text(name)
        type_combo.set_active(self.anno_line_dash)
        halo_check = Gtk.CheckButton(label="black halo")
        halo_check.set_active(self.anno_casing)

        def sync_style_widgets(*args):
            # A line always draws with the line color: its fill and the
            # outline toggle rest while it is chosen.  The stroke style
            # (width/type/halo) follows the outline for box/ellipse.
            is_line = radios["line"].get_active()
            stroked = is_line or use_outline.get_active()
            outline_label.set_text("line" if is_line else "outline")
            line_combo.set_sensitive(stroked)
            for widget in (fill_combo, fill_opaque):
                widget.set_sensitive(not is_line and use_fill.get_active())
            for widget in (halo_check, width_label, width_spin,
                           type_combo):
                widget.set_sensitive(stroked)
            # an invisible shape helps nobody: whichever of outline/fill
            # is the last one on cannot be unchecked
            use_outline.set_sensitive(not is_line
                                      and use_fill.get_active())
            use_fill.set_sensitive(not is_line
                                   and use_outline.get_active())

        for radio in radios.values():
            radio.connect("toggled", sync_style_widgets)
        use_outline.connect("toggled", sync_style_widgets)
        use_fill.connect("toggled", sync_style_widgets)
        sync_style_widgets()
        grid = Gtk.Grid()
        grid.set_column_spacing(8)
        grid.set_row_spacing(6)
        for index, (label, combo) in enumerate(
                ((outline_label, line_combo),
                 (Gtk.Label(label="fill"), fill_combo))):
            label.set_halign(Gtk.Align.START)
            grid.attach(label, 0, index, 1, 1)
            grid.attach(combo, 1, index, 1, 1)
        grid.attach(use_outline, 2, 0, 1, 1)
        grid.attach(halo_check, 3, 0, 1, 1)
        grid.attach(use_fill, 2, 1, 1, 1)
        grid.attach(fill_opaque, 3, 1, 1, 1)
        width_label.set_halign(Gtk.Align.START)
        grid.attach(width_label, 0, 2, 1, 1)
        grid.attach(width_spin, 1, 2, 1, 1)
        grid.attach(type_combo, 2, 2, 2, 1)
        box = dialog.get_content_area()
        box.set_border_width(10)
        box.set_spacing(8)
        box.pack_start(shape_row, False, False, 0)
        box.pack_start(grid, False, False, 0)
        dialog.show_all()
        confirmed = dialog.run() == Gtk.ResponseType.OK
        hexes = [hex_ for _, hex_ in self.PALETTE]
        shape = next(kind for kind, radio in radios.items()
                     if radio.get_active())
        line_color = hexes[max(line_combo.get_active(), 0)]
        fill_color = hexes[max(fill_combo.get_active(), 0)]
        outline_on = use_outline.get_active()
        fill_on = use_fill.get_active()
        fill_op = fill_opaque.get_active()
        line_width = int(width_spin.get_value())
        line_dash = max(type_combo.get_active(), 0)
        halo_on = halo_check.get_active()
        dialog.destroy()
        if not confirmed:
            return
        self.anno_shape = shape
        self.anno_line_color = line_color
        self.anno_line_width = line_width
        self.anno_line_dash = line_dash
        self.anno_casing = halo_on
        self.anno_outline = outline_on
        self.anno_fill_color = fill_color
        self.anno_fill = fill_on
        self.anno_fill_opaque = fill_op
        # set_anno_tool shows the mode+style as a persistent toast
        self.set_anno_tool(shape)

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
        if not code:
            # Keys that carry no character (Shift/Ctrl themselves, arrows,
            # F-keys, ...) must not end the syllable: pressing Shift for a
            # double jamo broke composition, and event.is_modifier is not
            # readable through introspection.  Cursor movement is caught
            # by the position check on the next jamo instead.
            return False
        char = chr(code)
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

    def add_ruler_annotation(self, a, b):
        label = Gtk.Label()
        label.set_name("flateyes-ruler")  # same chip as the live readout
        label.set_halign(Gtk.Align.START)
        label.set_valign(Gtk.Align.START)
        label.set_no_show_all(True)
        label.get_style_context().add_provider(
            self.chip_css, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        self.overlay.add_overlay(label)
        try:
            self.overlay.set_overlay_pass_through(label, True)
        except AttributeError:  # GTK < 3.18
            pass
        self.annotations.append({"kind": "ruler", "a": a, "b": b,
                                 "label": label})
        self.anno_rev += 1

    def undo_annotation(self):
        """Reverts the last add or remove ("u")."""
        if not self.anno_undo:
            self.show_toast("nothing to undo")
            return
        op = self.anno_undo.pop()
        self.apply_annotation_op(op, invert=True)
        self.anno_redo.append(op)

    def redo_annotation(self):
        """Re-applies the last undone operation ("y")."""
        if not self.anno_redo:
            self.show_toast("nothing to redo")
            return
        op = self.anno_redo.pop()
        self.apply_annotation_op(op, invert=False)
        self.anno_undo.append(op)

    # -- keyboard selection ("s"): move or delete drawn annotations --------

    def valid_selection(self):
        """The selected annotation, or None once it left the list (undo,
        image switch, ...).  Identity, not ==: twins must stay apart."""
        if self.anno_selected is not None and \
                not any(a is self.anno_selected for a in self.annotations):
            self.anno_selected = None
            self.anno_edit_anchor = None
        return self.anno_selected

    def clear_selection(self):
        if self.anno_selected is None:
            return
        self.anno_selected = None
        self.anno_edit_anchor = None
        self.anno_rev += 1

    @staticmethod
    def anchor_points(anno):
        return (anno["at"],) if anno["kind"] == "text" \
            else (anno["a"], anno["b"])

    def cycle_selection(self, step):
        """"s": select annotations newest-first (Shift+s: the other way)."""
        if not self.annotations:
            self.show_toast("no annotations to select")
            return
        cur = self.valid_selection()
        if cur is None:
            pos = len(self.annotations) - 1 if step > 0 else 0
        else:
            pos = next(i for i, a in enumerate(self.annotations)
                       if a is cur)
            pos = (pos - step) % len(self.annotations)
        anno = self.annotations[pos]
        self.anno_selected = anno
        self.anno_edit_anchor = None
        if not self.draw_visible:   # the markers must be visible
            self.draw_visible = True
        self.anno_rev += 1
        self.scroll_to_selection(anno)
        self.update_view_overlays()
        self.update_mode_toast()  # "selected i/n" stays up while selected

    def scroll_to_selection(self, anno):
        """Center the viewport on a selection that is off-screen."""
        if self.rendered_size is None:
            return
        pts = self.anchor_points(anno)
        center = (sum(p[0] for p in pts) / len(pts),
                  sum(p[1] for p in pts) / len(pts))
        view = self.scroll.get_allocation()
        vx, vy = self.image_px_to_view(self.px_from_world(center))
        if 0 <= vx <= view.width and 0 <= vy <= view.height:
            return
        wx, wy = self.image_px_to_widget(self.px_from_world(center))
        for adj, target in ((self.scroll.get_hadjustment(), wx),
                            (self.scroll.get_vadjustment(), wy)):
            page = adj.get_page_size()
            adj.set_value(max(adj.get_lower(),
                              min(target - page / 2.0,
                                  adj.get_upper() - page)))

    def move_selection(self, dx, dy, fast):
        """Arrow keys: nudge the selection by one screen pixel (Shift: 10),
        so the felt step size is the same at every zoom level.  With an
        edit anchor ("e") only that corner/endpoint moves: a resize."""
        anno = self.valid_selection()
        if anno is None or self.rendered_size is None:
            return
        step = 10.0 if fast else 1.0
        scale = self.current_view_scale()  # screen px per world unit
        dx, dy = dx * step / scale, dy * step / scale
        # Keep every anchor on the image so the shape stays reachable
        # (the widest level bounds the world for stacks).
        base = self.levels[0]["pixbuf"]
        lo = self.world_from_px((0.0, 0.0), 0)
        hi = self.world_from_px((float(base.get_width()),
                                 float(base.get_height())), 0)
        target = self.anno_edit_anchor
        pts = (anno[target],) if target else self.anchor_points(anno)
        dx = max(lo[0] - min(p[0] for p in pts),
                 min(dx, hi[0] - max(p[0] for p in pts)))
        dy = max(lo[1] - min(p[1] for p in pts),
                 min(dy, hi[1] - max(p[1] for p in pts)))
        if not dx and not dy:
            return
        # a run of nudges coalesces into a single undo step
        top = self.anno_undo[-1] if self.anno_undo else None
        if target:
            anno[target] = (anno[target][0] + dx, anno[target][1] + dy)
            if top is not None and top[0] == "anchor" and top[1] is anno \
                    and top[2][0] == target:
                self.anno_undo[-1] = ("anchor", anno,
                                      (target, top[2][1] + dx,
                                       top[2][2] + dy))
            else:
                self.anno_undo.append(("anchor", anno, (target, dx, dy)))
        else:
            self.shift_annotation(anno, dx, dy)
            if top is not None and top[0] == "move" and top[1] is anno:
                self.anno_undo[-1] = ("move", anno,
                                      (top[2][0] + dx, top[2][1] + dy))
            else:
                self.anno_undo.append(("move", anno, (dx, dy)))
        del self.anno_redo[:]
        self.anno_rev += 1
        self.update_anno_overlay()
        self.update_dirty()

    def edit_selection(self):
        """"e" with a selection: texts reopen their input dialog, shapes
        cycle what the arrows drag: whole -> anchor b -> anchor a."""
        anno = self.valid_selection()
        if anno is None:
            return
        if anno["kind"] == "text":
            self.ask_annotation_text(anno["at"], edit=anno)
            return
        order = (None, "b", "a")
        which = order[(order.index(self.anno_edit_anchor) + 1) % len(order)]
        self.anno_edit_anchor = which
        self.anno_rev += 1
        self.update_anno_overlay()
        self.update_mode_toast()  # "resize: ..." / back to "selected i/n"

    @staticmethod
    def shift_annotation(anno, dx, dy):
        for key in ("a", "b", "at"):
            if key in anno:
                anno[key] = (anno[key][0] + dx, anno[key][1] + dy)

    def delete_selection(self):
        """Delete/BackSpace: remove the selection (undoable with "u")."""
        anno = self.valid_selection()
        if anno is None:
            return
        index = next(i for i, a in enumerate(self.annotations) if a is anno)
        del self.annotations[index]
        if "label" in anno:
            self.overlay.remove(anno["label"])
        self.anno_undo.append(("remove", anno, index))
        del self.anno_redo[:]
        self.anno_selected = None
        self.anno_edit_anchor = None
        self.anno_rev += 1
        self.update_anno_overlay()
        self.update_dirty()
        self.update_mode_toast()  # the fallback once the notice expires
        self.show_toast("annotation removed (u restores it)")

    def apply_annotation_op(self, op, invert):
        """Plays an op forward (redo) or backward (undo)."""
        action, anno, extra = op
        if action == "move":
            sign = -1 if invert else 1
            self.shift_annotation(anno, sign * extra[0], sign * extra[1])
        elif action == "anchor":            # one corner/endpoint dragged
            which, dx, dy = extra
            sign = -1 if invert else 1
            anno[which] = (anno[which][0] + sign * dx,
                           anno[which][1] + sign * dy)
        elif action == "edit":              # text reworded/restyled
            self.apply_text_fields(anno, extra[0] if invert else extra[1])
        elif (action == "add") == invert:   # take the annotation out
            if anno in self.annotations:
                self.annotations.remove(anno)
                if "label" in anno:
                    self.overlay.remove(anno["label"])
        else:                               # put it (back) in
            where = len(self.annotations) if extra is None \
                else min(extra, len(self.annotations))
            self.annotations.insert(where, anno)
            if "label" in anno:
                self.overlay.add_overlay(anno["label"])
                try:
                    self.overlay.set_overlay_pass_through(anno["label"],
                                                          True)
                except AttributeError:  # GTK < 3.18
                    pass
        self.anno_rev += 1
        self.update_anno_overlay()
        self.update_dirty()
        self.update_mode_toast()  # undo/redo can renumber the selection

    def clear_annotations(self):
        # runtime state only; the metadata on disk is left untouched
        for anno in self.annotations:
            if "label" in anno:
                self.overlay.remove(anno["label"])
        self.annotations = []
        self.anno_undo = []
        self.anno_redo = []
        self.anno_selected = None
        self.anno_edit_anchor = None
        self.anno_rev += 1
        self.anno_tool = None
        self.anno_start = self.anno_cursor = None
        self.update_anno_overlay()
        self.update_mode_toast()

    # -- annotation metadata (persistence) ---------------------------------

    def annotation_paths(self):
        """Sidecar and cache candidates for the current path's metadata."""
        digest = hashlib.sha1(self.path.encode("utf-8")).hexdigest()
        return (self.path + ".fe",
                os.path.join(GLib.get_user_cache_dir(), "flateyes",
                             digest + ".fe"))

    @staticmethod
    def serialize_anno(anno):
        """One annotation dict as its key=value metadata line — the same
        format in the sidecar file, the PNG chunk and forwarded open
        requests (--box and friends)."""
        if anno["kind"] == "ruler":
            return ("ruler=%.10g,%.10g,%.10g,%.10g"
                    % (anno["a"][0], anno["a"][1],
                       anno["b"][0], anno["b"][1]))
        color = anno.get("color", Viewer.DEFAULT_LINE)
        if anno["kind"] == "text":
            if anno.get("bg", True):
                # backdrop as #RRGGBBAA (0x59 = the translucent 0.35);
                # older builds read any non-"0" value as their default
                backdrop = "%s%02X" % (
                    anno.get("bg_color", "#000000"),
                    255 if anno.get("bg_opaque") else 89)
            else:
                backdrop = "0"
            return ("text=%.10g,%.10g,%d,%s,%s,%s"
                    % (anno["at"][0], anno["at"][1],
                       anno["size"], color, backdrop,
                       Viewer.escape_meta(anno["text"])))
        if anno.get("fill"):
            # same #RRGGBBAA form as the text backdrop field
            fill = "%s%02X" % (anno["fill"],
                               255 if anno.get("fill_opaque") else 89)
        else:
            fill = "0"
        if not anno.get("outline", True):
            color = "0"  # no border ("0" like an absent fill)
        # 7th/8th field: stroke width and dash type (outlines and
        # lines alike); older builds ignore trailing fields
        extra = ",%d,%d" % (anno.get("width", 1), anno.get("dash", 0))
        if not anno.get("casing", True):
            extra += ",0"  # 9th field: halo off (default on)
        return ("%s=%.10g,%.10g,%.10g,%.10g,%s,%s%s"
                % (anno["kind"], anno["a"][0], anno["a"][1],
                   anno["b"][0], anno["b"][1], color, fill, extra))

    def serialize_annotations(self):
        """Metadata lines shared by the sidecar file and the PNG chunk."""
        lines = []
        # The PPU used for this file is part of its metadata, so measurements
        # read the same on the next open.  Stacks take ppu from the manifest.
        if self.ppu and not self.stack_mode:
            lines.append("ppu=%.10g" % self.ppu)
            lines.append("unit=%s" % self.unit)
        lines.extend(self.serialize_anno(anno) for anno in self.annotations)
        return lines

    def update_dirty(self):
        """Retitle ("*name") when the metadata diverges from the saved
        state; undoing back to it clears the marker again."""
        dirty = self.serialize_annotations() != self.saved_meta
        if dirty != self.anno_dirty:
            self.anno_dirty = dirty
            self.update_title()

    def save_annotations(self):
        """Ctrl+S: persist the annotation metadata.  Nothing autosaves —
        drawings and PPU changes live in memory until this explicit save,
        and are lost when another image is opened without saving."""
        if self.path and self.is_png:
            self.embed_annotations()  # into the PNG itself; no sidecar
        else:
            self.save_sidecar()       # other formats: .fe next to the file

    def save_sidecar(self):
        """Sidecar first, cache as fallback; saving with no annotations
        and no PPU removes the metadata files instead."""
        lines = self.serialize_annotations()
        candidates = self.annotation_paths()
        if not lines:
            removed = False
            for path in candidates:
                try:
                    os.unlink(path)
                    removed = True
                except OSError:
                    pass
            self.saved_meta = lines
            self.update_dirty()
            self.show_toast("saved annotations removed" if removed
                            else "no annotations to save")
            return
        data = "# flateyes annotations\n" \
            + "".join(line + "\n" for line in lines)
        for path in candidates:
            try:
                if path != candidates[0]:
                    os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, "w", encoding="utf-8") as handle:
                    handle.write(data)
                self.saved_meta = lines
                self.update_dirty()
                # the cache fallback lives elsewhere: show the full path
                self.show_toast("annotations saved  %s"
                                % (os.path.basename(path)
                                   if path == candidates[0] else path))
                return
            except OSError:
                continue
        self.show_toast("annotations not saved (read-only?)")

    def load_annotations(self):
        self.is_png = bool(self.path) and is_png_file(self.path)
        self.embedded_meta = False
        if self.pixbuf is None:
            return  # animations cannot be annotated
        lines = None
        if self.is_png:
            embedded = read_png_metadata(self.path)
            self.embedded_meta = embedded is not None
            if embedded is not None:
                lines = embedded.splitlines()
        # For PNGs the embedded chunk is authoritative; the sidecar below
        # only catches files annotated by older builds (Ctrl+S migrates
        # them into the PNG).  Every other format saves there on Ctrl+S.
        if lines is None:
            for meta_path in self.annotation_paths():
                try:
                    with open(meta_path, "r", encoding="utf-8") as handle:
                        lines = handle.read().splitlines()
                    break  # first readable source wins
                except OSError:
                    continue
        ppu_restored = False
        for raw in lines or []:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            key, sep, value = line.partition("=")
            if not sep:
                continue
            try:
                if key == "ppu":
                    if not self.stack_mode and float(value) > 0:
                        self.ppu = float(value)
                        ppu_restored = True
                elif key == "unit":
                    if not self.stack_mode and value.strip():
                        self.unit = value.strip()
                elif key in ("box", "ellipse", "line", "ruler", "text"):
                    self.attach_annotation(self.parse_anno_line(key, value))
            except ValueError:
                continue  # skip malformed lines
        # Restored annotations enter the undo stack as adds, so "u"
        # deletes newest-first across restored and freshly drawn ones
        # alike (delete-last is folded into undo/redo).
        self.anno_undo.extend(("add", anno, None)
                              for anno in self.annotations)
        if self.annotations or ppu_restored:
            parts = []
            if self.annotations:
                parts.append("%d annotation%s"
                             % (len(self.annotations),
                                "" if len(self.annotations) == 1 else "s"))
            if ppu_restored:
                parts.append("PPU %.4g px/%s" % (self.ppu, self.unit))
            self.anno_rev += 1
            self.update_anno_overlay()
            self.show_toast(", ".join(parts) + " restored")

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
        return Viewer.DEFAULT_LINE

    @staticmethod
    def parse_anno_line(key, value):
        """One key=value annotation from saved metadata or a forwarded
        request as a plain data dict (no GTK — usable before import_gtk).
        Raises ValueError on malformed input."""
        if key == "ruler":
            ax, ay, bx, by = value.split(",")[:4]
            return {"kind": "ruler", "a": (float(ax), float(ay)),
                    "b": (float(bx), float(by))}
        if key == "text":
            x, y, size, color, bg, text = value.split(",", 5)
            text = Viewer.unescape_meta(text)
            if not text:
                raise ValueError("empty text")
            bg = bg.strip()
            bg_color, bg_opaque = "#000000", False
            if bg.startswith("#") and len(bg) == 9:
                try:  # "#RRGGBBAA"; "0"/"1" come from older builds
                    int(bg[1:9], 16)
                    bg_color = bg[:7]
                    bg_opaque = int(bg[7:9], 16) >= 0x80
                except ValueError:
                    pass
            return {"kind": "text", "at": (float(x), float(y)),
                    "text": text, "size": max(6, min(int(size), 96)),
                    "color": Viewer.parse_color(color), "bg": bg != "0",
                    "bg_color": bg_color, "bg_opaque": bg_opaque}
        parts = value.split(",")
        ax, ay, bx, by, color = parts[:5]
        anno = {"kind": key,
                "a": (float(ax), float(ay)),
                "b": (float(bx), float(by)),
                "color": Viewer.parse_color(color)}
        if color.strip() == "0" and key != "line":
            anno["outline"] = False  # border switched off
        # 6th field since the fill feature: #RRGGBBAA or "0"
        fill = parts[5].strip() if len(parts) > 5 else "0"
        if fill.startswith("#") and len(fill) == 9:
            try:
                int(fill[1:9], 16)
                anno["fill"] = fill[:7]
                anno["fill_opaque"] = int(fill[7:9], 16) >= 0x80
            except ValueError:
                pass
        if len(parts) > 6:
            try:  # 7th/8th field: stroke width and dash type
                anno["width"] = max(1, min(int(float(parts[6])), 8))
                if len(parts) > 7:
                    code = int(float(parts[7]))
                    anno["dash"] = code if code in (1, 2) else 0
            except ValueError:
                pass  # keep the shape, default 1px solid
        if len(parts) > 8 and parts[8].strip() == "0":
            anno["casing"] = False  # 9th field: halo off
        return anno

    @staticmethod
    def option_color(text):
        """A color from a command-line option: palette name or #RRGGBB."""
        for name, hex_ in Viewer.PALETTE:
            if text.lower() == name:
                return hex_
        if text.startswith("#") and len(text) == 7:
            try:
                int(text[1:], 16)
                return text
            except ValueError:
                pass
        raise ValueError("bad color: %s (use %s or #RRGGBB)"
                         % (text, "/".join(n for n, _ in Viewer.PALETTE)))

    @staticmethod
    def parse_anno_option(kind, value):
        """One --box/--ellipse/--line/--ruler/--text command-line value as
        a full annotation dict (same fields as parse_anno_line yields).
        Friendlier than the metadata format: the style fields are optional
        and colors also take palette names.  Raises ValueError."""
        if kind == "text":
            parts = value.split(",", 2)
            if len(parts) < 3 or not parts[2].strip():
                raise ValueError("expects X,Y,TEXT")
            try:
                at = (float(parts[0]), float(parts[1]))
            except ValueError:
                raise ValueError("bad position: %s,%s"
                                 % (parts[0], parts[1]))
            # literal \n starts a new line, like in the metadata format;
            # tabs would break the request protocol
            text = Viewer.unescape_meta(parts[2]).replace("\t", " ")
            return {"kind": "text", "at": at, "text": text, "size": 16,
                    "color": Viewer.DEFAULT_LINE, "bg": True,
                    "bg_color": Viewer.DEFAULT_BG, "bg_opaque": False}
        parts = [part.strip() for part in value.split(",")]
        if len(parts) < 4:
            raise ValueError("expects X1,Y1,X2,Y2")
        try:
            anno = {"kind": kind,
                    "a": (float(parts[0]), float(parts[1])),
                    "b": (float(parts[2]), float(parts[3]))}
        except ValueError:
            raise ValueError("bad coordinates: %s" % ",".join(parts[:4]))
        rest = parts[4:]
        if kind == "ruler":
            if rest:
                raise ValueError("expects exactly X1,Y1,X2,Y2")
            return anno
        anno["color"] = Viewer.DEFAULT_LINE
        if rest:  # 5th field: outline color, 0 = no outline (fill only)
            color = rest.pop(0)
            if color == "0":
                if kind == "line":
                    raise ValueError("a line needs a color")
                anno["outline"] = False
            elif color:
                anno["color"] = Viewer.option_color(color)
        if rest and kind != "line":  # 6th: fill, #RRGGBBAA makes it opaque
            fill = rest.pop(0)
            if fill.startswith("#") and len(fill) == 9:
                try:
                    int(fill[1:9], 16)
                except ValueError:
                    raise ValueError("bad fill: %s" % fill)
                anno["fill"] = fill[:7]
                anno["fill_opaque"] = int(fill[7:9], 16) >= 0x80
            elif fill not in ("", "0"):
                anno["fill"] = Viewer.option_color(fill)
                anno["fill_opaque"] = False
        if not anno.get("outline", True) and "fill" not in anno:
            raise ValueError("0 (no outline) needs a FILL")
        if rest:  # then WIDTH 1-8 and DASH solid/dashed/dotted
            width = rest.pop(0)
            try:
                anno["width"] = int(width)
            except ValueError:
                raise ValueError("bad width: %s" % width)
            if not 1 <= anno["width"] <= 8:
                raise ValueError("width must be 1-8, got: %s" % width)
        if rest:
            dashes = {"solid": 0, "dashed": 1, "dotted": 2,
                      "0": 0, "1": 1, "2": 2}
            dash = rest.pop(0)
            if dash.lower() not in dashes:
                raise ValueError("dash must be solid/dashed/dotted, "
                                 "got: %s" % dash)
            anno["dash"] = dashes[dash.lower()]
        if rest:
            raise ValueError("too many fields: %s" % ",".join(rest))
        return anno

    def attach_annotation(self, anno):
        """Append one parsed annotation dict; texts and rulers get the
        overlay label they carry at runtime."""
        if anno["kind"] == "text":
            self.add_text_annotation(anno["at"], anno["text"],
                                     anno["size"], anno["color"],
                                     anno["bg"], anno["bg_color"],
                                     anno["bg_opaque"])
        elif anno["kind"] == "ruler":
            self.add_ruler_annotation(anno["a"], anno["b"])
        else:
            self.annotations.append(anno)
            self.anno_rev += 1

    def apply_request_annotations(self, annos):
        """Annotations passed on the command line (--box and friends):
        added on top of the file's saved ones, undoable like drawn
        shapes, and unsaved until Ctrl+S."""
        if not annos:
            return
        if self.pixbuf is None:
            self.show_toast("animations cannot be annotated")
            return
        for anno in annos:
            self.attach_annotation(anno)
            self.anno_undo.append(("add", self.annotations[-1], None))
        del self.anno_redo[:]
        self.anno_rev += 1
        self.update_anno_overlay()
        self.update_dirty()

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

    def show_about(self, *args):
        """About dialog: F1 or the right-click menu."""
        dialog = Gtk.AboutDialog(transient_for=self.window, modal=True)
        dialog.set_keep_above(True)  # stay over a fullscreen parent
        dialog.set_program_name(APP_TITLE)
        dialog.set_version(VERSION)
        # Plain text on purpose: a website link cannot open anything on
        # the closed network, so the URL is only shown, not clickable.
        dialog.set_copyright("2026 FLATIDE LC.\nhttp://flatide.com")
        dialog.run()
        dialog.destroy()

    def show_context_menu(self, event):
        menu = Gtk.Menu()
        item = Gtk.MenuItem(label="About %s" % APP_TITLE)
        item.connect("activate", self.show_about)
        menu.append(item)
        menu.show_all()
        self.context_menu = menu  # keep it referenced while it is up
        try:
            menu.popup_at_pointer(event)
        except AttributeError:  # GTK < 3.22
            menu.popup(None, None, None, None, event.button, event.time)
        return True

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
        self.update_anno_overlay()  # ruler annotation labels show distances
        self.update_status()
        self.update_dirty()  # the PPU saves with the metadata

    # -- events ------------------------------------------------------------

    def on_size_allocate(self, widget, allocation):
        if self.fit_mode:
            self.rescale(allocation)
        self.update_view_overlays()

    def request_quit(self):
        if self.confirm_unsaved():
            Gtk.main_quit()

    def on_delete_event(self, widget, event):
        """Window close asks like "q"; True keeps the window open."""
        return not self.confirm_unsaved()

    def confirm_unsaved(self):
        """True when leaving the image (quit, close, browse) may proceed:
        clean, saved, or discarded."""
        if not self.anno_dirty:
            return True
        dialog = Gtk.Dialog(title="Unsaved annotations",
                            transient_for=self.window, modal=True)
        dialog.set_keep_above(True)  # stay over a fullscreen parent
        dialog.add_button("Cancel", Gtk.ResponseType.CANCEL)
        dialog.add_button("Discard", Gtk.ResponseType.REJECT)
        dialog.add_button("Save", Gtk.ResponseType.OK)
        dialog.set_default_response(Gtk.ResponseType.OK)
        label = Gtk.Label(label="Annotations are not saved (Ctrl+S).\n"
                                "Save them first?")
        label.set_justify(Gtk.Justification.LEFT)
        box = dialog.get_content_area()
        box.set_border_width(12)
        box.set_spacing(6)
        box.pack_start(label, True, True, 0)
        dialog.show_all()
        response = dialog.run()
        dialog.destroy()
        if response == Gtk.ResponseType.OK:
            self.save_annotations()
            return not self.anno_dirty  # a failed save keeps the window
        return response == Gtk.ResponseType.REJECT

    def on_key(self, widget, event):
        key = Gdk.keyval_name(event.keyval)
        if self.browser_active:  # the thumbnail browser has its own keys
            if key in ("q", "Q"):
                self.request_quit()
            elif key in ("Escape", "b", "B"):
                if self.pixbuf is not None or self.animation is not None:
                    self.leave_browser()
            elif key == "BackSpace":
                parent = os.path.dirname(self.browser_folder or "")
                if parent and parent != self.browser_folder:
                    self.populate_browser(parent)
            elif key == "F1":
                self.show_about()
            else:
                return False  # arrows/Enter/typeahead: the icon view's
            return True
        if key in ("q", "Q"):
            self.request_quit()
        elif key in ("i", "I"):  # info overlays: help, legend, level outline
            self.info_visible = not self.info_visible
            self.apply_help_visibility()
            self.apply_legend_visibility()
            self.update_hint_overlay()
            self.update_mode_toast()
        elif key == "Escape":  # leaves selection/tool modes; quitting is "q"
            if self.valid_selection() is not None:
                if self.anno_edit_anchor is not None:
                    self.anno_edit_anchor = None   # resize -> move mode
                    self.anno_rev += 1
                else:
                    self.clear_selection()
                self.update_anno_overlay()
                self.update_mode_toast()
            elif self.ruler_active:
                self.set_ruler_active(False)
            elif self.anno_tool is not None:
                self.set_anno_tool(None)
        elif key in ("r", "R"):
            self.set_ruler_active(not self.ruler_active)
        elif key in ("b", "B"):
            if self.stack_mode:  # the folder holds the stack's levels
                self.show_toast("folder browsing is off in stack mode")
            else:
                self.enter_browser(select=self.path)
        elif key in ("d", "D"):
            self.ask_draw_shape()   # shape + style dialog starts the mode
        elif key in ("e", "E") and self.valid_selection() is not None:
            self.edit_selection()   # resize anchors / the text dialog
        elif key in ("t", "T"):
            self.set_anno_tool(None if self.anno_tool == "text" else "text")
        elif key in ("u", "U"):
            self.undo_annotation()
        elif key in ("y", "Y"):
            self.redo_annotation()
        elif key in ("c", "C") \
                and event.state & Gdk.ModifierType.CONTROL_MASK:
            self.copy_view_to_clipboard()  # Ctrl+C
        elif key in ("s", "S") \
                and event.state & Gdk.ModifierType.CONTROL_MASK:
            self.save_annotations()  # Ctrl+S
        elif key in ("s", "S"):      # plain s: cycle-select annotations
            self.cycle_selection(
                -1 if event.state & Gdk.ModifierType.SHIFT_MASK else 1)
        elif key in ("Delete", "KP_Delete", "BackSpace") \
                and self.valid_selection() is not None:
            self.delete_selection()
        elif key in ("Left", "Right", "Up", "Down",
                     "KP_Left", "KP_Right", "KP_Up", "KP_Down") \
                and self.valid_selection() is not None:
            # with a selection the arrows move it instead of panning
            self.move_selection(
                key.endswith("Right") - key.endswith("Left"),
                key.endswith("Down") - key.endswith("Up"),
                bool(event.state & Gdk.ModifierType.SHIFT_MASK))
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
        elif key in ("comma", "less"):
            self.browse_folder(-1)
        elif key in ("period", "greater"):
            self.browse_folder(1)
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
        elif key == "Tab":  # every overlay: drawings, info and the toast
            visible = self.draw_visible or self.info_visible
            self.draw_visible = self.info_visible = not visible
            self.apply_help_visibility()
            self.apply_legend_visibility()
            self.update_view_overlays()
            self.update_mode_toast()
        elif key == "F1":
            self.show_about()
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
        if event.type != Gdk.EventType.BUTTON_PRESS:
            return False
        if event.button == 3:
            return self.show_context_menu(event)
        if event.button != 1:
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
            if self.ruler_start is None:
                self.ruler_start = point           # start a new measurement
                self.ruler_end = self.ruler_cursor = None
                self.update_ruler_overlay()
            else:
                # second click commits the measurement as an annotation:
                # it persists, undoes and saves like any drawn shape
                self.add_ruler_annotation(
                    self.ruler_start, self.snap_point(point, event.state))
                self.anno_undo.append(("add", self.annotations[-1], None))
                del self.anno_redo[:]
                self.ruler_start = self.ruler_end = self.ruler_cursor = None
                self.update_ruler_overlay()        # clear the live preview
                self.update_anno_overlay()
                self.update_dirty()
        elif self.anno_tool == "text":
            self.ask_annotation_text(point)
        elif self.anno_start is None:
            self.anno_start = point                # first corner
            self.anno_cursor = None
        else:
            anno = {"kind": self.anno_tool, "a": self.anno_start,
                    "b": self.constrain_corner(point, event.state),
                    "color": self.anno_color(),
                    "width": self.anno_line_width,
                    "dash": self.anno_line_dash}
            if self.anno_tool in ("box", "ellipse"):
                if self.anno_fill:
                    anno["fill"] = self.anno_fill_color
                    anno["fill_opaque"] = self.anno_fill_opaque
                if not self.anno_outline:
                    anno["outline"] = False
            if not self.anno_casing:
                anno["casing"] = False
            self.annotations.append(anno)
            self.anno_undo.append(("add", anno, None))
            del self.anno_redo[:]
            self.anno_rev += 1
            self.anno_start = self.anno_cursor = None
            self.update_anno_overlay()
            self.update_dirty()
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
            annos = []    # annotations to draw once the image is open
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
                elif key in ("box", "ellipse", "line", "ruler", "text"):
                    try:
                        annos.append(self.parse_anno_line(key, value))
                    except ValueError:
                        bad = "ERR bad %s: %s" % (key, value)
                # unknown keys are ignored for forward compatibility
            if bad:
                reply = bad
            elif inline:
                reply = self.open_request(inline[0]["path"], legend, None,
                                          unit, True, inline, annos)
            elif path:
                reply = self.open_request(path, legend, ppu, unit, stack,
                                          annos=annos)
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
        "usage: %s [-l LEGEND_FILE] [-p PPU] [-u UNIT] [DRAW...]\n"
        "                 [IMAGE_FILE|FOLDER]\n"
        "       %s [-l LEGEND_FILE] [-u UNIT] [DRAW...] -s STACK_FILE\n"
        "       %s [-l LEGEND_FILE] [-u UNIT] [DRAW...] --level IMG -p PPU\n"
        "                 [--center X,Y] [--level IMG -p PPU ...]\n"
        "\n"
        "Opens IMAGE_FILE in a viewer window on $DISPLAY.  If a viewer is\n"
        "already running on that display, the image replaces the one in the\n"
        "existing window and this process exits immediately.  With a FOLDER\n"
        "(default: the current directory) a thumbnail browser of its\n"
        "images and subfolders opens instead.\n"
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
        "DRAW options add annotations onto the opened image, on top of\n"
        "its saved ones; they behave like hand-drawn shapes (select,\n"
        "undo, ...) and stay unsaved until Ctrl+S.  Each may be repeated.\n"
        "Coordinates are image pixels (stacks: world units, like the\n"
        "ruler).  COLOR is a palette name (%s)\n"
        "or #RRGGBB; 0 = no outline (needs FILL).  FILL is a color, or\n"
        "#RRGGBBAA with AA >= 80 for an opaque fill (default none).\n"
        "WIDTH is the stroke width 1-8, DASH is solid, dashed or dotted.\n"
        "\n"
        "  --box X1,Y1,X2,Y2[,COLOR[,FILL[,WIDTH[,DASH]]]]\n"
        "  --ellipse X1,Y1,X2,Y2[,COLOR[,FILL[,WIDTH[,DASH]]]]\n"
        "  --line X1,Y1,X2,Y2[,COLOR[,WIDTH[,DASH]]]\n"
        "  --ruler X1,Y1,X2,Y2       finished ruler measurement (uses\n"
        "                            the PPU/unit in effect)\n"
        "  --text X,Y,TEXT           note at X,Y (16pt, default colors;\n"
        "                            a literal \\n breaks the line)\n"
        "\n"
        "keys: +/- zoom, 0 actual size, f fit, Enter/F11 fullscreen,\n"
        "      ,/. next/prev image in the folder,\n"
        "      b thumbnail browser: one folder's subfolders and images\n"
        "        (Enter opens, BackSpace goes up, Esc returns),\n"
        "      Ctrl+wheel zoom, drag to pan, o next-level outline,\n"
        "      i info overlays (help/legend/outline) on/off,\n"
        "      Tab all overlays (drawings and info) on/off,\n"
        "      [/] stack level, p set PPU,\n"
        "      r ruler (Shift = free angle, Esc ends),\n"
        "      d draw shapes: a dialog picks box/ellipse/line and the\n"
        "        style - outline (use, color), stroke width (1-8 px)\n"
        "        and type (solid/dashed/dotted) for lines and outlines\n"
        "        alike, the black halo around strokes (on/off) and the\n"
        "        box/ellipse fill (use, color, opaque/translucent); one\n"
        "        of outline/fill always stays on and texts style\n"
        "        themselves; Shift while clicking = square/circle/\n"
        "        45-degree line,\n"
        "      t text,\n"
        "      s select annotations, newest first (Shift+s backwards):\n"
        "        arrows move the selection (Shift = 10 px steps),\n"
        "        e edits it - shapes cycle a resize corner/endpoint\n"
        "          that the arrows then drag, texts reopen their\n"
        "          input dialog prefilled,\n"
        "        Delete/BackSpace removes it, Esc deselects,\n"
        "      u/y undo/redo annotations (u also deletes, newest first),\n"
        "      Ctrl+C copy the visible view (info hidden) to the clipboard,\n"
        "      Ctrl+S save the annotations and PPU (no autosave):\n"
        "             embedded into a PNG image itself, to a .fe\n"
        "             sidecar file for other formats; browsing to\n"
        "             another image with unsaved changes asks first,\n"
        "      F1/right-click About,\n"
        "      q quit - with unsaved annotations (the title shows\n"
        "        *name) a dialog asks to save/discard/cancel first\n"
        % (APP, APP, APP,
           "/".join(name for name, _ in Viewer.PALETTE)))


def parse_args(args):
    """Returns (path, legend, ppu, unit, is_stack, levels, annos) or an
    exit code.

    path is None when inline levels are given; is_stack marks a manifest.
    """
    legend = ppu = unit = stack_file = None
    levels = []
    annos = []
    paths = []
    i = 0
    while i < len(args):
        arg = args[i]
        took_value = None
        if arg in ("-h", "--help"):
            usage(sys.stdout)
            return 0
        elif arg in ("-l", "--legend", "-p", "--ppu", "-u", "--unit",
                     "-s", "--stack", "--level", "--center",
                     "--box", "--ellipse", "--line", "--ruler", "--text"):
            i += 1
            if i == len(args):
                sys.stderr.write("%s: %s requires an argument\n" % (APP, arg))
                return 2
            took_value = args[i]
        elif arg.startswith(("--legend=", "--ppu=", "--unit=", "--stack=",
                             "--level=", "--center=", "--box=",
                             "--ellipse=", "--line=", "--ruler=",
                             "--text=")):
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
            elif arg in ("--box", "--ellipse", "--line", "--ruler",
                         "--text"):
                try:
                    annos.append(Viewer.parse_anno_option(arg[2:],
                                                          took_value))
                except ValueError as exc:
                    sys.stderr.write("%s: %s: %s\n" % (APP, arg, exc))
                    return 2
            else:
                stack_file = took_value
        i += 1
    sources = (1 if paths else 0) + (1 if stack_file else 0) \
        + (1 if levels else 0)
    if sources > 1 or len(paths) > 1:
        usage(sys.stderr)
        return 2
    if sources == 0:  # no input: browse the current folder's images
        paths = ["."]
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
        return None, legend, None, unit, False, levels, annos
    if stack_file is not None:
        return stack_file, legend, ppu, unit, True, None, annos
    return paths[0], legend, ppu, unit, False, None, annos


def main(argv):
    parsed = parse_args(argv[1:])
    if isinstance(parsed, int):
        return parsed
    path, legend, ppu, unit, stack, levels, annos = parsed

    if levels is not None:
        for meta in levels:
            meta["path"] = os.path.abspath(meta["path"])
            if not os.path.isfile(meta["path"]):
                sys.stderr.write("%s: no such file: %s\n"
                                 % (APP, meta["path"]))
                return 1
    else:
        path = os.path.abspath(path)
        if stack:
            if not os.path.isfile(path):
                sys.stderr.write("%s: no such file: %s\n" % (APP, path))
                return 1
        elif not os.path.isfile(path) and not os.path.isdir(path):
            sys.stderr.write("%s: no such file or folder: %s\n"
                             % (APP, path))
            return 1
        if annos and os.path.isdir(path):
            sys.stderr.write("%s: annotations need an image, not a "
                             "folder: %s\n" % (APP, path))
            return 2
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
    # annotations travel as the same key=value lines Ctrl+S would write
    fields.extend(Viewer.serialize_anno(anno) for anno in annos)
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
           legend, ppu, unit, stack, levels, annos)
    Gtk.main()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
