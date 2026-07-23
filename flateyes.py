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
  * --multi opts out of the single-instance behaviour: the process always
    opens its own independent window and never touches the instance socket.

Usage:
  DISPLAY=:1 flateyes.py /path/to/image.jpg
"""

import bisect
import errno
import hashlib
import json
import math
import os
import re
import signal
import socket
import struct
import sys
import tempfile
import threading
import time
import zlib
from concurrent.futures import ThreadPoolExecutor

APP = "flateyes"        # lowercase: socket names, cache dir, CLI messages
APP_TITLE = "FlatEyes"  # display name
VERSION = "1.9.1"

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


LEGEND_BOX_STYLES = {"solid": "solid", "none": "none", "outline": "none",
                     "empty": "none", "hatch": "hatch", "cross": "cross",
                     "crosshatch": "cross", "dots": "dots", "dotted": "dots"}
LEGEND_LINE_STYLES = {"solid": "solid", "dash": "dashed", "dashed": "dashed",
                      "dot": "dotted", "dotted": "dotted"}


def parse_legend_entry(line):
    """One "kind COLOR [STYLE] LABEL..." legend definition line — the
    text legend file format and the legend= metadata value alike.
    Returns (entry, error); whitespace-splitting keeps labels free of
    tabs/newlines, which the request protocol and chunk format need.
    """
    parts = line.split()
    kind = parts[0].lower() if parts else ""
    if kind not in ("box", "line"):
        return None, "expected box or line, got: %s" % (parts[0] if parts
                                                        else "nothing")
    if len(parts) < 2:
        return None, "missing color"
    try:
        color = Viewer.option_color(parts[1])
    except ValueError as exc:
        return None, str(exc)
    styles = LEGEND_BOX_STYLES if kind == "box" else LEGEND_LINE_STYLES
    style = "solid"
    rest = parts[2:]
    if rest and rest[0].lower() in styles:
        style = styles[rest[0].lower()]
        rest = rest[1:]
    if not rest:
        return None, "missing label"
    return {"kind": kind, "color": color, "style": style,
            "label": " ".join(rest)}, None


def serialize_legend_entry(entry):
    """Canonical definition line: the style always explicit, so a label
    that starts with a style word survives the round trip."""
    return "%s %s %s %s" % (entry["kind"], entry["color"],
                            entry["style"], entry["label"])


def parse_legend_text(text, origin):
    """Parse a text legend definition: one entry per line, "#" comments.

      box COLOR [STYLE] LABEL...     STYLE: solid (default), none
                                     (outline only), hatch, cross, dots
      line COLOR [STYLE] LABEL...    STYLE: solid (default), dashed,
                                     dotted

    COLOR is a palette name or #RRGGBB.  The label runs to the end of
    the line (spaces allowed); a label starting with a style word needs
    an explicit STYLE before it.  Returns (entries, error); origin
    names the source in error messages.
    """
    entries = []
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        entry, error = parse_legend_entry(line)
        if error:
            return None, "ERR %s:%d: %s" % (origin, number, error)
        entries.append(entry)
    if not entries:
        return None, "ERR %s: empty legend" % origin
    return entries, None


def parse_legend_file(path):
    try:
        with open(path, "r", encoding="utf-8") as handle:
            return parse_legend_text(handle.read(), path)
    except (OSError, UnicodeDecodeError) as exc:
        return None, "ERR %s: %s" % (path, exc)


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
        self.view = view
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

    def replace_span(self, anchor, old_len, new):
        """Swap just the preedit span, keeping the cursor onscreen.
        Rewriting the whole buffer (set_text) empties it for a moment,
        which collapses the scroll position to the top on multi-line
        content — and a programmatic place_cursor never scrolls back."""
        self.buffer.delete(self.buffer.get_iter_at_offset(anchor),
                           self.buffer.get_iter_at_offset(anchor + old_len))
        self.buffer.insert(self.buffer.get_iter_at_offset(anchor), new)
        self.buffer.place_cursor(
            self.buffer.get_iter_at_offset(anchor + len(new)))
        self.view.scroll_mark_onscreen(self.buffer.get_insert())


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
    SNAP_RADIUS = 14             # ruler edge snap: search radius, screen px
    SNAP_MIN_GRAD = 40           # Sobel magnitude below this is "flat"
    SNAP_STICKY = 1.25           # a rival edge must beat the held snap 25%
    THUMB_SIZE = 120             # thumbnail browser: image cell size
    THUMB_CACHE = 128            # freedesktop "normal" thumbnail size
    THUMB_PARALLEL = 4           # async thumbnail decodes in flight
    ANNO_CASING = 0x000000A0     # shape annotation outline
    HIGHLIGHT_CASING = 0x39FF14FF  # "h" highlight: neon-green halo
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
                 ("n", "note"), ("s", "select"), ("u/y", "undo/redo"),
                 ("Ctrl+C", "copy"), ("Ctrl+Shift+C", "path"),
                 ("Ctrl+S", "save"), ("p", "PPU"),
                 ("o", "outline"), ("[/]", "level"), ("i", "info"),
                 ("Tab", "overlays"), ("q", "quit"))

    def __init__(self, server_sock, first_path, first_legend=None,
                 ppu=None, unit=None, stack=False, levels=None,
                 annos=None, note=None, legend_entries=None):
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
        self.anno_highlight = False  # "h": emphasize the drawn shapes

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
        self.from_browser = False   # image reached via the browser: Esc back
        self.thumb_queue = []       # (row index, path) pending thumbnails
        self.thumb_source = None    # idle handler feeding them
        self.thumb_pending = 0      # decode jobs in flight
        self.thumb_generation = 0   # bumped whenever the queue is replaced
        self.scan_generation = 0    # bumped whenever another scan starts
        self.browser_dir_keys = []  # natural_key of each shown subfolder
        self.thumb_pool = None      # worker threads, created on first browse
        # Cache warming: while an image is on screen its folder's
        # thumbnails are pre-generated in the background, so a later "b"
        # opens with every cell instant.
        self.warm_queue = []        # paths still to warm
        self.warm_source = None     # low-priority idle dispatcher
        self.warm_pending = 0       # warm jobs in flight
        self.warm_folder = None     # folder already warmed (or warming)
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
                               Gdk.EventMask.BUTTON1_MOTION_MASK |
                               Gdk.EventMask.LEAVE_NOTIFY_MASK)
        self.scroll.connect("scroll-event", self.on_scroll)
        self.scroll.connect("button-press-event", self.on_button_press)
        self.scroll.connect("motion-notify-event", self.on_motion)
        self.scroll.connect("button-release-event", self.on_button_release)
        self.scroll.connect("leave-notify-event", self.on_leave)
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
        self.ruler_axis = None      # snapped axis Ctrl holds on to ("h"/"v")
        self.ruler_dir = None       # free-angle unit vector Ctrl freezes
        self.ruler_drawn = None     # geometry of the rendered overlays
        self.ruler_line = Gtk.Image()
        self.ruler_label = Gtk.Label()
        # Edge snap ("m" toggles, off by default): ruler points attract
        # to the nearest luminance edge; the pointer itself never warps
        # (remote X lag), a crosshair previews where the first click
        # would land.  A plain key, not a modifier: window managers
        # grab Alt+click for window moves.
        self.snap_enabled = False
        self.snap_hover = None      # world point the next click snaps to
        self.snap_last = None       # (level, px point) hysteresis holds
        self.snap_cache = None      # (query key, result) of the last snap
        self.snap_marker = Gtk.Image()
        # Stack hint: outline of the area the next magnification covers.
        self.hint_drawn = None
        self.hint_image = Gtk.Image()
        for widget in (self.ruler_line, self.ruler_label, self.hint_image,
                       self.snap_marker):
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

        # Per-image note ("n"): free-form text without position or
        # style, pinned to the top-left as an info chip and saved into
        # the same metadata (note= line).  The left side keeps it clear
        # of the legend, and the top margin drops it below the key help
        # strip (like the legend clears the path readout).
        self.note = ""
        self.note_label = Gtk.Label()
        self.note_label.set_name("flateyes-status")
        self.note_label.set_halign(Gtk.Align.START)
        self.note_label.set_valign(Gtk.Align.START)
        self.note_label.set_margin_top(48)
        self.note_label.set_margin_start(8)
        self.note_label.set_line_wrap(True)
        self.note_label.set_max_width_chars(44)
        self.note_label.set_xalign(0)   # multi-line notes read flush left
        self.note_label.set_no_show_all(True)

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
            b" font-size: 11px; }"
            b"#flateyes-legend { background-color: rgba(0,0,0,0.78); }")
        for widget in (self.ruler_label, self.help_label, self.toast_label,
                       self.status_label, self.path_label, self.note_label):
            widget.get_style_context().add_provider(
                css, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        self.chip_css = css  # for dynamically created readout labels
        # Annotations: boxes/ellipses stamped into one viewport-sized
        # overlay pixbuf, texts as Pango labels; all anchored in world
        # coordinates like the ruler.
        self.anno_tool = None       # "box" | "ellipse" | "line" | "path"
                                    # | "text"
        self.anno_start = None      # first corner (world); for the path
                                    # tool: the last vertex placed
        self.anno_cursor = None     # preview corner (world)
        self.anno_path = []         # path tool: vertices placed so far
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
        self.anno_notable = False   # ...beyond rulers: prompts and titles
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

        # Legend: optional second image, or a text-defined swatch table,
        # overlaid at the bottom-right corner.
        self.legend_pixbuf = None
        self.legend_entries = None
        self.legend_rendered = None
        self.legend_image = Gtk.Image()
        # Text legend rows: pixbuf swatch + Gtk.Label (no cairo, so the
        # text cannot be stamped into a pixbuf; widgets do the type).
        self.legend_grid = Gtk.Grid()
        self.legend_grid.set_column_spacing(7)
        self.legend_grid.set_row_spacing(4)
        for setter in (self.legend_grid.set_margin_start,
                       self.legend_grid.set_margin_end,
                       self.legend_grid.set_margin_top,
                       self.legend_grid.set_margin_bottom):
            setter(7)
        legend_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        legend_box.add(self.legend_image)
        legend_box.add(self.legend_grid)
        legend_box.show()
        self.legend_frame = Gtk.Frame()
        self.legend_frame.set_name("flateyes-legend")
        self.legend_frame.get_style_context().add_provider(
            css, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        self.legend_frame.add(legend_box)
        self.legend_frame.set_halign(Gtk.Align.END)
        self.legend_frame.set_valign(Gtk.Align.END)
        self.legend_frame.set_margin_end(12)
        self.legend_frame.set_margin_bottom(40)  # clear the path readout
        self.legend_frame.set_no_show_all(True)

        self.overlay = Gtk.Overlay()
        self.overlay.add(self.scroll)
        self.overlay.add_overlay(self.hint_image)
        self.overlay.add_overlay(self.anno_image)
        # The legend is an info overlay: it sits above the drawn
        # annotations, but below the live ruler so a measurement into
        # its corner stays readable.
        self.overlay.add_overlay(self.legend_frame)
        self.overlay.add_overlay(self.ruler_line)
        self.overlay.add_overlay(self.ruler_label)
        self.overlay.add_overlay(self.snap_marker)
        self.overlay.add_overlay(self.help_label)
        self.overlay.add_overlay(self.status_label)
        self.overlay.add_overlay(self.path_label)
        self.overlay.add_overlay(self.note_label)
        self.overlay.add_overlay(self.toast_label)
        for child in (self.legend_frame, self.hint_image, self.anno_image,
                      self.ruler_line, self.ruler_label, self.snap_marker,
                      self.help_label, self.status_label, self.path_label,
                      self.note_label, self.toast_label):
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
                              levels=levels, legend_entries=legend_entries)
            if error != "OK":
                sys.stderr.write("%s\n" % error)
                sys.exit(1)
            self.apply_request_annotations(annos or [])
            self.apply_request_note(note)
            self.set_initial_size()
        else:  # folder request: start in the thumbnail browser
            work_w, work_h = workarea_size()
            self.window.set_default_size(int(work_w * 0.72),
                                         int(work_h * 0.85))
        self.window.show_all()
        self.apply_help_visibility()
        if start_folder is not None:
            self.enter_browser(start_folder)

        if server_sock is not None:  # None with --multi: no request socket
            GLib.io_add_watch(server_sock.fileno(), GLib.IO_IN,
                              self.on_incoming)
        # SIGINT/SIGTERM end Gtk.main cleanly.  GLib >= 2.80 moved the
        # unix API into its own GLibUnix namespace (the GLib shim then
        # warns on every start), but which names the typelib exports
        # varies by GLib version (signal_add vs signal_add_full only) -
        # probe the candidates in order, deprecated shim last.
        candidates = []
        try:
            import gi
            gi.require_version("GLibUnix", "2.0")
            from gi.repository import GLibUnix
        except (ImportError, ValueError):
            pass  # no GLibUnix typelib: older PyGObject
        else:
            for name in ("signal_add", "signal_add_full"):
                if hasattr(GLibUnix, name):
                    candidates.append(getattr(GLibUnix, name))
        if hasattr(GLib, "unix_signal_add"):
            candidates.append(GLib.unix_signal_add)
        quit_main = lambda *a: (Gtk.main_quit(), False)[1]  # noqa: E731
        for signum in (signal.SIGINT, signal.SIGTERM):
            for func in candidates:  # empty: terminal ^C only
                try:
                    func(GLib.PRIORITY_DEFAULT, signum, quit_main)
                    break
                except TypeError:   # unexpected introspected signature
                    continue

    # -- image loading -----------------------------------------------------

    def open_request(self, path, legend=None, ppu=None, unit=None,
                     stack=False, levels=None, annos=None, note=None,
                     legend_entries=None):
        """An incoming open: folders switch to the thumbnail browser,
        anything else loads as an image/stack."""
        if levels is None and not stack and os.path.isdir(path):
            if annos or note or legend_entries:
                return "ERR annotations need an image, not a folder: %s" \
                    % path
            self.enter_browser(os.path.abspath(path))
            return "OK"
        result = self.load(path, legend, ppu, unit, stack, levels,
                           legend_entries)
        if result == "OK":
            self.apply_request_annotations(annos or [])
            self.apply_request_note(note)
            if self.browser_active:
                self.leave_browser()
        return result

    def load(self, path, legend_path=None, ppu=None, unit=None, stack=False,
             levels=None, legend_entries=None):
        stack = stack or levels is not None
        if not stack and os.path.isdir(path):
            # folders open in the thumbnail browser, never here
            return "ERR is a folder: %s" % path
        if not os.path.isfile(path):
            return "ERR no such file: %s" % path
        # Decode the legend first so a bad legend leaves the window untouched.
        # An image file overlays as-is; anything else is a text definition.
        # legend_entries may also arrive pre-parsed (a --json legend); a
        # text -l file wins over it, matching the other json fields.
        legend_pixbuf = None
        if legend_path:
            if not os.path.isfile(legend_path):
                return "ERR no such file: %s" % legend_path
            info = GdkPixbuf.Pixbuf.get_file_info(legend_path)
            legend_fmt = info[0] if isinstance(info, tuple) else info
            if legend_fmt is None:
                legend_entries, error = parse_legend_file(legend_path)
                if error:
                    return error
            else:
                try:
                    legend_pixbuf = GdkPixbuf.Pixbuf.new_from_file(
                        legend_path)
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
        # A request text legend replaces the embedded one (Ctrl+S then
        # persists it); without one the embedded legend restored above
        # stays.  An image legend is a display-only overlay on top.
        if legend_entries is not None:
            self.legend_entries = legend_entries
        # The as-loaded state (request ppu/legend included) is the clean
        # baseline for the title's unsaved marker.
        self.saved_meta = self.serialize_annotations()
        self.anno_dirty = self.anno_notable = False
        self.legend_pixbuf = legend_pixbuf
        self.legend_rendered = None
        if legend_pixbuf is not None:
            self.render_legend()
        else:
            self.legend_image.clear()
        self.build_text_legend()
        self.apply_legend_visibility()
        if self.pixbuf is not None:
            self.rescale()
        else:
            self.image.set_from_animation(self.animation)
            self.scale_shown = 1.0
            self.update_title()
        self.start_thumb_warm()   # pre-cache this folder for a later "b"
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
        self.reset_thumb_work()
        self.browser_active = False
        self.from_browser = True    # so Esc on the image screen goes back
        self.browser_box.hide()
        self.overlay.show()
        self.scroll.grab_focus()  # arrow keys pan again
        self.update_title()
        self.pump_warm()   # resume any cache warming the browser paused

    def populate_browser(self, folder, select=None):
        """One os.scandir deep: subfolders first, then this folder's
        images.  The scan runs on a worker thread and the rows land via
        idle_add: enumerating a huge folder must not freeze the UI, and
        NFS dirents often carry no d_type, degrading is_dir() to one
        stat round trip per file.  The ".." row goes up at once and
        subfolders stream in as the walk finds them, so a slow folder
        can be left or descended while it still reads; the images land
        together at the end, and their thumbnails then stream in the
        same way."""
        folder = os.path.abspath(folder)
        self.browser_folder = folder
        self.browser_store.clear()
        self.browser_dir_keys = []  # natural_key of each shown subfolder
        self.reset_thumb_work()
        # The browser itself fills this folder's cache; pending warm work
        # is dropped so the workers belong to the visible screen.
        del self.warm_queue[:]
        self.warm_folder = folder
        self.scan_generation += 1
        self.window.set_title("%s - %s" % (folder, APP_TITLE))
        self.browser_status.set_text("%s   reading..." % folder)
        parent = os.path.dirname(folder)
        if parent and parent != folder:
            self.browser_store.append(
                [self.browser_icon("up"), "..", parent, True])
        threading.Thread(
            target=self.scan_folder_job, name="fe-scan", daemon=True,
            args=(self.scan_generation, folder, select,
                  image_extensions())).start()

    def scan_folder_job(self, gen, folder, select, exts):
        """Worker thread: enumerate and classify one folder, plus the
        cloud-placeholder flags for the decode order (one stat per
        image).  Touches only the filesystem; the store is left to the
        main loop.  Subfolders are handed over one by one as they turn
        up, everything else once the walk is done."""
        error = None
        image_names = []
        try:
            for entry in os.scandir(folder):
                if gen != self.scan_generation:
                    return          # superseded: drop the walk half-way
                name = entry.name
                if name.startswith("."):
                    continue
                try:
                    is_dir = entry.is_dir()
                except OSError:
                    is_dir = False
                if is_dir:
                    GLib.idle_add(self.deliver_folder_dir, gen, folder,
                                  name)
                elif os.path.splitext(name)[1].lstrip(".").lower() in exts:
                    image_names.append(name)
        except OSError as exc:
            error = "cannot read folder: %s" % exc
        image_names.sort(key=natural_key)
        dataless = set()
        for name in image_names:
            if gen != self.scan_generation:
                return
            if self.file_is_dataless(os.path.join(folder, name)):
                dataless.add(name)
        GLib.idle_add(self.deliver_folder_scan, gen, folder, select,
                      image_names, dataless, error)

    def deliver_folder_dir(self, gen, folder, name):
        """Main loop: one subfolder found mid-scan, inserted at its
        sorted slot right away.  The images only land after the last of
        these (idle callbacks fire in post order), so the row indices
        the thumbnail queue keeps stay stable."""
        if gen != self.scan_generation or not self.browser_active \
                or folder != self.browser_folder:
            return False
        key = natural_key(name)
        index = bisect.bisect_left(self.browser_dir_keys, key)
        self.browser_dir_keys.insert(index, key)
        offset = len(self.browser_store) - len(self.browser_dir_keys) + 1
        self.browser_store.insert(
            offset + index, [self.browser_icon("folder"), name,
                             os.path.join(folder, name), True])
        return False

    def deliver_folder_scan(self, gen, folder, select, image_names,
                            dataless, error):
        """Main loop: finish the browser rows from a completed scan; a
        stale scan (folder changed again, browser left) is dropped."""
        if gen != self.scan_generation or not self.browser_active \
                or folder != self.browser_folder:
            return False
        if error:
            self.browser_status.set_text(error)
        images = [os.path.join(folder, name) for name in image_names]
        cursor = None
        for path in images:
            row = len(self.browser_store)
            self.browser_store.append(
                [self.browser_icon("loading"), os.path.basename(path),
                 path, False])
            self.thumb_queue.append((row, path))
            if select and os.path.abspath(select) == os.path.abspath(path):
                cursor = row
        # Cloud placeholders decode last (each blocks a worker on an
        # on-demand download), so the locally-present thumbnails are not
        # stuck queued behind them.  Stable: natural order within groups.
        self.thumb_queue.sort(
            key=lambda rp: os.path.basename(rp[1]) in dataless)
        self.pump_thumbs()
        if cursor is not None:
            tree_path = Gtk.TreePath(cursor)
            self.browser_view.select_path(tree_path)
            self.browser_view.set_cursor(tree_path, None, False)
            GLib.idle_add(self.browser_view.scroll_to_path,
                          tree_path, True, 0.5, 0.5)
        if not error:
            ndirs = len(self.browser_dir_keys)
            self.browser_status.set_text(
                "%s   %d folder%s, %d image%s   "
                "(Enter opens, BackSpace up, Esc back, q quits)"
                % (folder, ndirs, "" if ndirs == 1 else "s",
                   len(images), "" if len(images) == 1 else "s"))
        return False

    def reset_thumb_work(self):
        """Drop queued thumbnails and orphan the in-flight decodes: the
        generation bump makes their results land stale and be discarded."""
        del self.thumb_queue[:]
        self.thumb_generation += 1

    def pump_thumbs(self):
        """(Re)arm the idle dispatcher unless it is already running."""
        if self.thumb_source is None and self.thumb_queue \
                and self.browser_active:
            self.thumb_source = GLib.idle_add(self.on_thumb_idle)

    def on_thumb_idle(self):
        """Hand one queue entry to a worker thread per idle pass, up to
        THUMB_PARALLEL in flight.  gdk-pixbuf's own async decoders turn
        out to run effectively serially, so a small pool of plain
        threads decoding synchronously (the C decode releases the GIL)
        is what actually parallelizes; deliver_thumb marshals the result
        back and pumps the next as slots free up."""
        if not self.browser_active or not self.thumb_queue \
                or self.thumb_pending >= self.THUMB_PARALLEL:
            self.thumb_source = None
            return False
        if self.thumb_pool is None:
            self.thumb_pool = ThreadPoolExecutor(
                max_workers=self.THUMB_PARALLEL, thread_name_prefix="fe-thumb")
        row, path = self.pop_thumb()
        self.thumb_pending += 1
        gen = self.thumb_generation
        self.thumb_pool.submit(self.decode_thumb_job, row, path, gen)
        return True

    def decode_thumb_job(self, row, path, gen):
        """Worker thread: cache lookup, else a synchronous decode, then
        cache-fill.  Touches only gdk-pixbuf and the filesystem (both
        thread-safe); the ListStore is left to the main loop.  Always
        delivers exactly once, so an unexpected error frees the slot
        instead of stalling the pipeline."""
        thumb = None
        try:
            thumb, mtime = self.load_thumb_cache(path)
            if thumb is None:
                decoded = GdkPixbuf.Pixbuf.new_from_file_at_scale(
                    path, self.THUMB_CACHE, self.THUMB_CACHE, True)
                decoded = decoded.apply_embedded_orientation() or decoded
                if mtime is not None and self.worth_caching(path):
                    self.save_thumb_cache(path, decoded, mtime)
                thumb = self.fit_thumb(decoded)
        except Exception:       # broken image, race, decode bug: show broken
            thumb = None
        GLib.idle_add(self.deliver_thumb, row, thumb, gen)

    def deliver_thumb(self, row, thumb, gen):
        """Main loop: fill the cell (or a broken icon) and free the slot.
        Stale results from a since-changed folder are dropped."""
        self.thumb_pending -= 1
        if gen == self.thumb_generation and self.browser_active:
            self.set_thumb(row, thumb if thumb is not None
                           else self.browser_icon("broken"))
        self.pump_thumbs()
        return False

    def pop_thumb(self):
        """Next queue entry, preferring rows scrolled into view so the
        user watches their own screen fill first."""
        try:
            rng = self.browser_view.get_visible_range()
        except (TypeError, ValueError):
            rng = None              # return shape varies across minors
        if rng and isinstance(rng[0], bool):
            rng = rng[1:] if rng[0] else None
        if rng:
            lo = rng[0].get_indices()[0]
            hi = rng[1].get_indices()[0]
            for i, (row, _) in enumerate(self.thumb_queue):
                if lo <= row <= hi:
                    return self.thumb_queue.pop(i)
        return self.thumb_queue.pop(0)

    def set_thumb(self, row, thumb):
        if row < len(self.browser_store):
            self.browser_store[row][0] = thumb

    def fit_thumb(self, thumb):
        """Scale a decoded or cached thumbnail into the browser cell."""
        w, h = thumb.get_width(), thumb.get_height()
        scale = min(float(self.THUMB_SIZE) / w, float(self.THUMB_SIZE) / h)
        if abs(scale - 1.0) < 1e-6:
            return thumb
        return thumb.scale_simple(max(1, int(w * scale)),
                                  max(1, int(h * scale)),
                                  GdkPixbuf.InterpType.BILINEAR)

    def thumb_cache_name(self, path):
        """freedesktop thumbnail location: md5 of the file URI under
        ~/.cache/thumbnails.  Sharing the spec cache means folders the
        user already browsed with eog/nautilus show instantly here, and
        our thumbnails help those tools in return."""
        uri = GLib.filename_to_uri(os.path.abspath(path), None)
        # FIPS-mode hosts refuse md5: the ValueError is caught by the
        # callers and thumbnails just stay session-local there.
        name = hashlib.md5(uri.encode("utf-8")).hexdigest() + ".png"
        root = os.environ.get("XDG_CACHE_HOME") \
            or os.path.join(os.path.expanduser("~"), ".cache")
        return os.path.join(root, "thumbnails"), name, uri

    def load_thumb_cache(self, path):
        """Return (thumbnail, mtime-string).  The thumbnail is None
        when missing or stale; mtime rides along so the decode path can
        fill the cache without a second stat."""
        try:
            mtime = str(int(os.stat(path).st_mtime))
        except OSError:
            return None, None
        try:
            root, name, _uri = self.thumb_cache_name(path)
        except (GLib.Error, ValueError):
            return None, mtime
        for level in ("normal", "large"):
            cached = os.path.join(root, level, name)
            if not os.path.exists(cached):
                continue
            try:
                thumb = GdkPixbuf.Pixbuf.new_from_file(cached)
            except GLib.Error:
                continue
            if thumb.get_option("tEXt::Thumb::MTime") == mtime:
                return self.fit_thumb(thumb), mtime
        return None, mtime

    def save_thumb_cache(self, path, thumb, mtime):
        """Write a spec-compliant "normal" thumbnail (Thumb:: keys,
        mode 0600, atomic rename).  Failure only costs persistence."""
        try:
            root, name, uri = self.thumb_cache_name(path)
            folder = os.path.join(root, "normal")
            os.makedirs(folder, 0o700, exist_ok=True)
            # Include the thread id: several workers cache in parallel.
            tmp = os.path.join(folder, "%s.%d.%d.tmp"
                               % (name, os.getpid(), threading.get_ident()))
            thumb.savev(tmp, "png",
                        ["tEXt::Thumb::URI", "tEXt::Thumb::MTime"],
                        [uri, mtime])
            os.chmod(tmp, 0o600)
            os.replace(tmp, os.path.join(folder, name))
        except (GLib.Error, OSError, ValueError):
            pass

    @staticmethod
    def file_is_dataless(path):
        """Cloud-placeholder heuristic: the on-disk blocks cover far less
        than the file size (iCloud optimized storage, and likewise thin
        network files).  Reading one stalls on an on-demand download, so
        background work steers around them.  Sparse or transparently
        compressed files can match too -- being deferred or left uncached
        is harmless there."""
        try:
            st = os.stat(path)
        except OSError:
            return False
        blocks = getattr(st, "st_blocks", None)
        if blocks is None or st.st_size < 65536:
            return False
        return blocks * 512 < st.st_size // 2

    def worth_caching(self, path):
        """Cache only images larger than the thumbnail itself: tiny
        files decode instantly, and an upscaled cache entry would look
        soft in other spec users (nautilus, eog)."""
        info = GdkPixbuf.Pixbuf.get_file_info(path)
        if not info or info[0] is None:
            return False
        return info[1] > self.THUMB_CACHE or info[2] > self.THUMB_CACHE

    # -- background cache warming (image mode) ---------------------------

    def start_thumb_warm(self):
        """Queue the viewed image's folder for thumbnail cache warming.
        Runs through the same worker pool as the browser but from a
        LOW-priority idle, so it never competes with an open browser or
        foreground work; a folder is warmed at most once per visit."""
        if self.stack_mode or not self.path:
            return
        folder = os.path.dirname(os.path.abspath(self.path))
        if folder == self.warm_folder:
            return   # already warmed or warming
        self.warm_folder = folder
        self.warm_queue = self.folder_images(folder)
        self.pump_warm()

    def pump_warm(self):
        if self.warm_source is None and self.warm_queue \
                and not self.browser_active:
            self.warm_source = GLib.idle_add(
                self.on_warm_idle, priority=GLib.PRIORITY_LOW)

    def on_warm_idle(self):
        if self.browser_active or not self.warm_queue \
                or self.warm_pending >= self.THUMB_PARALLEL:
            self.warm_source = None
            return False
        if self.thumb_pool is None:
            self.thumb_pool = ThreadPoolExecutor(
                max_workers=self.THUMB_PARALLEL, thread_name_prefix="fe-thumb")
        path = self.warm_queue.pop(0)
        self.warm_pending += 1
        self.thumb_pool.submit(self.warm_thumb_job, path)
        return True

    def warm_thumb_job(self, path):
        """Worker thread: make sure the spec cache holds a fresh thumbnail
        for path; the pixbuf itself is discarded.  Same decode/cache steps
        as the browser's decode_thumb_job, minus the delivery."""
        try:
            thumb, mtime = self.load_thumb_cache(path)
            if thumb is None and not self.file_is_dataless(path):
                # a cloud placeholder is left alone: speculative warming
                # must not force a bulk download of the whole folder
                decoded = GdkPixbuf.Pixbuf.new_from_file_at_scale(
                    path, self.THUMB_CACHE, self.THUMB_CACHE, True)
                decoded = decoded.apply_embedded_orientation() or decoded
                if mtime is not None and self.worth_caching(path):
                    self.save_thumb_cache(path, decoded, mtime)
        except Exception:   # broken image: the browser will mark it later
            pass
        GLib.idle_add(self.on_warm_done)

    def on_warm_done(self):
        self.warm_pending -= 1
        self.pump_warm()
        return False

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

    @staticmethod
    def shorten_path(path):
        """Very long paths on one short line: keep the head and tail."""
        if len(path) > 72:
            return path[:24] + "…" + path[-47:]
        return path

    def update_title(self):
        name = os.path.basename(self.path or "")
        if self.anno_notable:
            name = "*" + name  # unsaved changes beyond mere rulers
        self.window.set_title("%s - %s" % (name, APP_TITLE))
        full = self.path or ""
        shown = self.shorten_path(full)
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
                parts.append(value % self.trim_decimal(ppu, 4) + " px/"
                             + GLib.markup_escape_text(self.unit))
        self.status_label.set_markup(" · ".join(parts))

    # -- legend overlay ------------------------------------------------------

    LEGEND_SWATCH = (36, 14)  # swatch pixbuf size in the text legend

    def build_text_legend(self):
        """Rebuild the swatch/label rows from self.legend_entries."""
        for child in self.legend_grid.get_children():
            child.destroy()
        if not self.legend_entries:
            return
        for row, entry in enumerate(self.legend_entries):
            swatch = Gtk.Image.new_from_pixbuf(self.legend_swatch(entry))
            swatch.set_halign(Gtk.Align.START)
            swatch.set_valign(Gtk.Align.CENTER)
            label = Gtk.Label()
            label.set_markup(
                '<span foreground="#f0f0f0" size="small">%s</span>'
                % GLib.markup_escape_text(entry["label"]))
            label.set_halign(Gtk.Align.START)
            self.legend_grid.attach(swatch, 0, row, 1, 1)
            self.legend_grid.attach(label, 1, row, 1, 1)
        self.legend_grid.show_all()

    def legend_swatch(self, entry):
        """One swatch pixbuf; the interior stays transparent so the
        frame's dark backdrop reads as the pattern background."""
        w, h = self.LEGEND_SWATCH
        buf = GdkPixbuf.Pixbuf.new(GdkPixbuf.Colorspace.RGB, True, 8, w, h)
        buf.fill(0x00000000)
        rgba = self.color_rgba(entry["color"])
        style = entry["style"]
        if entry["kind"] == "line":
            y = h // 2 - 1
            if style == "solid":
                self.fill_rect(buf, 0, y, w, 2, rgba)
            else:
                on, period = (5, 9) if style == "dashed" else (2, 5)
                for x in range(0, w, period):
                    self.fill_rect(buf, x, y, min(on, w - x), 2, rgba)
            return buf
        if style == "solid":
            buf.fill(rgba)
            return buf
        if style in ("hatch", "cross"):
            for x in range(w):
                for y in range(h):
                    if (x + y) % 5 == 0 or \
                            (style == "cross" and (x - y) % 5 == 0):
                        self.fill_rect(buf, x, y, 1, 1, rgba)
        elif style == "dots":
            for x in range(3, w - 2, 5):
                for y in range(3, h - 2, 5):
                    self.fill_rect(buf, x, y, 2, 2, rgba)
        self.fill_rect(buf, 0, 0, w, 1, rgba)          # outline on top
        self.fill_rect(buf, 0, h - 1, w, 1, rgba)
        self.fill_rect(buf, 0, 0, 1, h, rgba)
        self.fill_rect(buf, w - 1, 0, 1, h, rgba)
        return buf

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
                       self.note_label, self.legend_frame, self.hint_image,
                       self.snap_marker):
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

    def copy_path_to_clipboard(self):
        """Ctrl+Shift+C: the viewed image's path as clipboard text
        (stacks: the level on screen)."""
        path = self.active_level()["path"] if self.stack_mode else self.path
        if not path:
            return
        clipboard = Gtk.Clipboard.get(Gdk.SELECTION_CLIPBOARD)
        clipboard.set_text(path, -1)
        # No clipboard.store(): see finish_copy — the selection is served
        # by the viewer itself, so the copy lives while it runs.
        self.show_toast("path copied  %s" % self.shorten_path(path))

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
            if self.anno_edit_anchor is not None:
                if selected["kind"] == "path":
                    label = ("point %d/%d"
                             % (self.anno_edit_anchor + 1,
                                len(selected["points"])))
                else:
                    part = "endpoint" \
                        if selected["kind"] in ("line", "ruler") \
                        else "corner"
                    label = "%s %s" % (part, self.anno_edit_anchor.upper())
                text = ("resize: %s  (arrows drag it, e next, Esc back)"
                        % label)
            else:
                pos = next(i for i, a in enumerate(self.annotations)
                           if a is selected)
                text = ("selected %d/%d: %s  (arrows move, e edit,"
                        " Delete removes, Esc done)"
                        % (len(self.annotations) - pos,
                           len(self.annotations), selected["kind"]))
        elif self.ruler_active:
            text = "ruler: click two points  (snap %s: m toggles; " \
                "Esc ends)" % ("on" if self.snap_enabled else "off")
        elif self.anno_tool == "text":
            text = "text: click to place  (Esc ends)"
        elif self.anno_tool == "path":
            text = self.draw_mode_desc() \
                + "  (click adds a point, double-click/Enter finishes, " \
                "Esc cancels)"
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
        if self.anno_tool in ("line", "path"):
            desc = ('draw %s <span foreground="%s">■■</span> %s'
                    % (self.anno_tool, self.anno_line_color, stroke))
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
        self.update_note_overlay()

    def update_note_overlay(self):
        """The note chip at the top-left: follows the info overlays,
        and only exists while the image has a note."""
        if self.note and self.info_visible:
            self.note_label.set_text(self.note)
            self.note_label.show()
        else:
            self.note_label.hide()

    def apply_legend_visibility(self):
        if self.info_visible and (self.legend_pixbuf is not None
                                  or self.legend_entries):
            # A request image legend covers the (still saved) entries.
            self.legend_image.set_visible(self.legend_pixbuf is not None)
            self.legend_grid.set_visible(self.legend_pixbuf is None
                                         and bool(self.legend_entries))
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
        self.ruler_axis = self.ruler_dir = None
        self.snap_hover = self.snap_last = self.snap_cache = None
        self.set_viewport_cursor(self.tool_cursor())
        self.update_view_overlays()
        self.update_mode_toast()

    def event_to_image_px(self, event):
        """Map a pointer event to image-pixel coordinates (clamped)."""
        win = self.image.get_window()
        if win is None or self.rendered_size is None:
            return None
        _, org_x, org_y = win.get_origin()
        return self.win_to_image_px(event.x_root - org_x,
                                    event.y_root - org_y)

    def win_to_image_px(self, x, y):
        """Image-window coordinates -> image pixels (clamped)."""
        alloc = self.image.get_allocation()
        x -= alloc.x
        y -= alloc.y
        # GtkImage centers the pixbuf inside its allocation.
        rend_w, rend_h = self.rendered_size
        x -= max(0, (alloc.width - rend_w) // 2)
        y -= max(0, (alloc.height - rend_h) // 2)
        img_w, img_h = self.image_size()
        return (min(max(x / self.scale_shown, 0.0), img_w),
                min(max(y / self.scale_shown, 0.0), img_h))

    def pointer_state(self):
        """Current pointer position (image px) and modifier mask, read
        directly off the device: pressing/releasing a key generates no
        motion event, so snapping needs the position without one."""
        win = self.image.get_window()
        if win is None or self.rendered_size is None:
            return None
        display = self.window.get_display()
        try:
            device = display.get_default_seat().get_pointer()
        except AttributeError:  # GTK < 3.20
            device = display.get_device_manager().get_client_pointer()
        _, x, y, state = win.get_device_position(device)
        return self.win_to_image_px(x, y), state

    def event_to_world(self, event):
        point = self.event_to_image_px(event)
        return None if point is None else self.world_from_px(point)

    @staticmethod
    def trim_decimal(value, decimals):
        """Fixed-point text, trailing zeros (and any bare dot) trimmed and
        always plain decimal, so large values never turn into 4.8e+04 the
        way %g does."""
        text = "%.*f" % (decimals, value)
        if "." in text:
            text = text.rstrip("0").rstrip(".")
        return text

    @staticmethod
    def um_decimals(ppu):
        """Decimal places a micron reading is worth: enough that a single
        pixel step (1/ppu um) stays visible, clamped to 2..6.  At a high
        ppu like 48000 that is 5 places, so 0.0065 um no longer rounds to
        0.01."""
        if ppu and ppu > 0:
            return min(6, max(2, int(math.ceil(math.log10(ppu)))))
        return 2

    def format_distance(self, dist_world):
        if self.stack_mode:
            # world units come straight from the manifest ppu values
            ppu = self.active_level()["ppu"]
            px = dist_world * ppu
            return "%s %s  (%d px)" % (
                self.trim_decimal(dist_world, self.um_decimals(ppu)),
                self.unit, round(px))
        if self.ppu:
            return "%s %s  (%d px)" % (
                self.trim_decimal(dist_world / self.ppu,
                                  self.um_decimals(self.ppu)),
                self.unit, round(dist_world))
        return "%d px" % round(dist_world)

    def snap_point(self, point, state):
        """Constrain to the dominant axis unless Shift asks for free angle.
        Holding Ctrl freezes the direction the measurement is already on:
        snapped mode keeps its horizontal/vertical axis instead of
        re-picking the dominant one at every motion, and free mode locks
        the current angle, sliding the end along it (only the length still
        follows the mouse)."""
        ax, ay = self.ruler_start
        if state & Gdk.ModifierType.SHIFT_MASK:
            self.ruler_axis = None
            dx, dy = point[0] - ax, point[1] - ay
            if state & Gdk.ModifierType.CONTROL_MASK \
                    and self.ruler_dir is not None:
                ux, uy = self.ruler_dir      # hold the angle, keep the length
                t = dx * ux + dy * uy
                return (ax + t * ux, ay + t * uy)
            length = math.hypot(dx, dy)
            if length:
                self.ruler_dir = (dx / length, dy / length)
            return point
        self.ruler_dir = None
        if not (state & Gdk.ModifierType.CONTROL_MASK) \
                or self.ruler_axis is None:
            self.ruler_axis = "h" \
                if abs(point[0] - ax) >= abs(point[1] - ay) else "v"
        if self.ruler_axis == "h":
            return (point[0], ay)
        return (ax, point[1])

    # -- ruler edge snap -----------------------------------------------------

    def edge_snap_allowed(self):
        return self.snap_enabled

    def edge_snap(self, point, direction=None):
        """Snap an image-px point onto the strongest luminance edge
        nearby: Sobel gradients over a small window, scored with a
        falloff by distance to the cursor.  With a unit direction only
        the gradient component along it counts, so edges running with
        the measurement never attract the point.  Returns a sub-pixel
        point, or None where the neighbourhood is flat (no snap)."""
        if self.pixbuf is None:
            return None
        radius = max(3, min(20, int(round(self.SNAP_RADIUS
                                          / self.scale_shown))))
        img_w, img_h = self.pixbuf.get_width(), self.pixbuf.get_height()
        cx = min(max(int(round(point[0])), 0), img_w - 1)
        cy = min(max(int(round(point[1])), 0), img_h - 1)
        dir_key = None if direction is None \
            else (round(direction[0], 2), round(direction[1], 2))
        key = (self.level_index, cx, cy, radius, dir_key)
        if self.snap_cache is not None and self.snap_cache[0] == key:
            return self.snap_cache[1]
        x0, y0 = max(0, cx - radius - 1), max(0, cy - radius - 1)
        x1, y1 = min(img_w, cx + radius + 2), min(img_h, cy + radius + 2)
        result = None
        if x1 - x0 >= 3 and y1 - y0 >= 3:
            result = self.edge_snap_window(point, direction, radius,
                                           x0, y0, x1 - x0, y1 - y0)
        self.snap_cache = (key, result)
        return result

    def edge_snap_window(self, point, direction, radius, x0, y0, w, h):
        # copy() first: get_pixels() on a bare subpixbuf would copy the
        # parent's full-width rows.
        sub = self.pixbuf.new_subpixbuf(x0, y0, w, h).copy()
        data = sub.get_pixels()
        stride = sub.get_rowstride()
        nch = sub.get_n_channels()
        lum = [0] * (w * h)   # luminance x256 (BT.601 integer weights)
        i = 0
        for row in range(h):
            base = row * stride
            for col in range(w):
                p = base + col * nch
                lum[i] = data[p] * 77 + data[p + 1] * 150 + data[p + 2] * 29
                i += 1
        fx, fy = point[0] - x0, point[1] - y0
        r2 = float(radius * radius)
        ux, uy = direction if direction is not None else (0.0, 0.0)
        directed = direction is not None
        score = [0] * (w * h)  # unweighted, kept for the sub-pixel fit
        best = None            # (weighted, col, row, gx, gy)
        for row in range(1, h - 1):
            up, mid, down = (row - 1) * w, row * w, (row + 1) * w
            dy2 = (row - fy) * (row - fy)
            for col in range(1, w - 1):
                nw, no, ne = lum[up + col - 1], lum[up + col], \
                    lum[up + col + 1]
                we, ea = lum[mid + col - 1], lum[mid + col + 1]
                sw, so, se = lum[down + col - 1], lum[down + col], \
                    lum[down + col + 1]
                gx = (ne + 2 * ea + se) - (nw + 2 * we + sw)
                gy = (sw + 2 * so + se) - (nw + 2 * no + ne)
                if directed:
                    s = gx * ux + gy * uy
                    s = s * s
                else:
                    s = gx * gx + gy * gy
                score[mid + col] = s
                d2 = (col - fx) * (col - fx) + dy2
                if d2 > r2:
                    continue
                weighted = s * (1.0 - d2 / (r2 + 1.0))
                if best is None or weighted > best[0]:
                    best = (weighted, col, row, gx, gy)
        floor = (self.SNAP_MIN_GRAD * 256) ** 2
        if best is None or score[best[2] * w + best[1]] < floor:
            return None
        # Hysteresis: hold the previous snap unless the rival clearly
        # wins, so the point does not hop between parallel edges.
        if self.snap_last is not None and self.snap_last[0] == \
                self.level_index:
            lx, ly = self.snap_last[1]
            pc, pr = int(round(lx)) - x0, int(round(ly)) - y0
            if 1 <= pc < w - 1 and 1 <= pr < h - 1:
                d2 = (pc - fx) * (pc - fx) + (pr - fy) * (pr - fy)
                if d2 <= r2:
                    held = score[pr * w + pc] * (1.0 - d2 / (r2 + 1.0))
                    if held >= floor and best[0] < held * self.SNAP_STICKY:
                        return self.snap_last[1]
        _, col, row, gx, gy = best
        # Sub-pixel: parabola through the scores along the dominant axis
        # of the refinement direction (the measurement direction, or the
        # gradient = the edge normal).
        vx, vy = (ux, uy) if directed else (gx, gy)
        mid = row * w
        if abs(vx) >= abs(vy):
            s_m, s_0, s_p = score[mid + col - 1], score[mid + col], \
                score[mid + col + 1]
        else:
            s_m, s_0, s_p = score[mid - w + col], score[mid + col], \
                score[mid + w + col]
        denom = s_m - 2 * s_0 + s_p
        delta = 0.0 if denom == 0 else \
            max(-0.5, min(0.5, 0.5 * (s_m - s_p) / denom))
        if abs(vx) >= abs(vy):
            result = (x0 + col + delta, y0 + row)
        else:
            result = (x0 + col, y0 + row + delta)
        self.snap_last = (self.level_index, result)
        return result

    def edge_snap_world(self, point, direction=None):
        """edge_snap in world coordinates (the direction passes through
        unchanged: world -> px is a uniform scale)."""
        snapped = self.edge_snap(self.px_from_world(point), direction)
        return None if snapped is None else self.world_from_px(snapped)

    def snap_ruler_end(self, point, state):
        """The ruler end: axis/angle constraint first, then edge snap
        along the measurement direction only -- edges crossing the ruler
        attract the point, edges running with it never do -- projected
        back so a constrained point stays on its line."""
        point = self.snap_point(point, state)
        if not self.edge_snap_allowed():
            return point
        ax, ay = self.ruler_start
        dx, dy = point[0] - ax, point[1] - ay
        length = math.hypot(dx, dy)
        if not length:
            return point
        direction = (dx / length, dy / length)
        snapped = self.edge_snap_world(point, direction)
        if snapped is None:
            return point
        if state & Gdk.ModifierType.SHIFT_MASK \
                and not state & Gdk.ModifierType.CONTROL_MASK:
            return snapped     # free angle: the point may leave the ray
        t = (snapped[0] - ax) * direction[0] \
            + (snapped[1] - ay) * direction[1]
        return (ax + t * direction[0], ay + t * direction[1])

    def update_snap_hover(self, event):
        """Before the first ruler point: preview where a click would
        snap, as a crosshair (the pointer itself never warps)."""
        hover = None
        if self.edge_snap_allowed():
            point = self.event_to_world(event)
            if point is not None:
                hover = self.edge_snap_world(point)
        self.snap_hover = hover
        self.update_snap_marker()

    def refresh_snap_preview(self):
        """Toggling "m" fires no motion event: bring the hover marker or
        the live end point up to date from the pointer position itself."""
        if not self.ruler_active:
            return
        pos = self.pointer_state()
        if pos is None:
            return
        point, state = pos
        if self.ruler_start is None:
            hover = None
            if self.edge_snap_allowed():
                snapped = self.edge_snap(point)
                hover = None if snapped is None \
                    else self.world_from_px(snapped)
            self.snap_hover = hover
            self.update_snap_marker()
        elif self.ruler_end is None and self.ruler_cursor is not None:
            self.ruler_cursor = self.snap_ruler_end(
                self.world_from_px(point), state)
            self.update_ruler_overlay()

    def update_snap_marker(self):
        point = self.snap_hover
        if point is None or not self.ruler_active or not self.draw_visible \
                or self.ruler_start is not None \
                or self.rendered_size is None:
            self.snap_marker.hide()
            return
        x, y = self.image_px_to_view(self.px_from_world(point))
        view = self.scroll.get_allocation()
        if not (0 <= x <= view.width and 0 <= y <= view.height):
            self.snap_marker.hide()
            return
        if self.snap_marker.get_pixbuf() is None:  # draw once, then move
            size, c = 17, 8
            buf = GdkPixbuf.Pixbuf.new(GdkPixbuf.Colorspace.RGB, True, 8,
                                       size, size)
            buf.fill(0x00000000)
            # Four arms with an open centre, so the snapped pixel itself
            # stays visible through the gap.
            for rect in ((0, c - 1, c - 2, 3), (c + 3, c - 1, c - 2, 3),
                         (c - 1, 0, 3, c - 2), (c - 1, c + 3, 3, c - 2)):
                self.fill_rect(buf, *rect, rgba=self.RULER_CASING)
            for rect in ((0, c, c - 2, 1), (c + 3, c, c - 2, 1),
                         (c, 0, 1, c - 2), (c, c + 3, 1, c - 2)):
                self.fill_rect(buf, *rect, rgba=self.RULER_CORE)
            self.snap_marker.set_from_pixbuf(buf)
        self.snap_marker.set_margin_start(max(0, int(round(x)) - 8))
        self.snap_marker.set_margin_top(max(0, int(round(y)) - 8))
        self.snap_marker.show()

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
        self.update_snap_marker()
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
                self.ruler_axis = self.ruler_dir = None
                self.update_ruler_overlay()
            if not self.draw_visible:
                self.draw_visible = True  # drawing needs its overlays back
            self.clear_selection()
        self.anno_tool = tool
        self.anno_start = self.anno_cursor = None
        del self.anno_path[:]
        self.set_viewport_cursor(self.tool_cursor())
        self.update_view_overlays()
        self.update_mode_toast()

    def anno_color(self):
        return self.anno_line_color

    @staticmethod
    def color_rgba(hex_color, alpha=0xFF):
        """"#RRGGBB" -> the 0xRRGGBBAA pixbuf fill value."""
        return (int(hex_color[1:], 16) << 8) | alpha

    def finish_path(self):
        """Commit the in-progress path (double-click or Enter); fewer
        than two vertices is just a cancel.  The tool stays active for
        the next path."""
        points = list(self.anno_path)
        del self.anno_path[:]
        self.anno_start = self.anno_cursor = None
        self.anno_rev += 1
        if len(points) >= 2:
            anno = {"kind": "path", "points": points,
                    "color": self.anno_color(),
                    "width": self.anno_line_width,
                    "dash": self.anno_line_dash}
            if not self.anno_casing:
                anno["casing"] = False
            self.annotations.append(anno)
            self.anno_undo.append(("add", anno, None))
            del self.anno_redo[:]
        self.update_anno_overlay()
        self.update_dirty()
        self.update_mode_toast()

    def constrain_corner(self, point, state):
        """Shift constrains: square/circle for shapes, 0/45/90 for lines."""
        if not state & Gdk.ModifierType.SHIFT_MASK:
            return point
        ax, ay = self.anno_start
        dx, dy = point[0] - ax, point[1] - ay
        if self.anno_tool in ("line", "path"):
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
        shapes = [x for x in self.annotations
                  if x["kind"] not in ("text", "ruler")]
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
        elif self.anno_tool == "path" and self.anno_path:
            pts = list(self.anno_path)
            if self.anno_cursor is not None:
                pts.append(self.anno_cursor)  # rubber band to the mouse
            if len(pts) >= 2:
                preview = {"kind": "path", "points": pts,
                           "color": self.anno_color(),
                           "width": self.anno_line_width,
                           "dash": self.anno_line_dash}
                if not self.anno_casing:
                    preview["casing"] = False
        if not self.draw_visible or self.rendered_size is None \
                or not (shapes or rulers or preview or texts):
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
               self.anno_highlight,
               preview and (preview.get("a"), preview.get("b"),
                            tuple(preview.get("points", ()))),
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
            self.stamp_annotation(buf, shape, self.anno_highlight)
        if preview is not None:
            self.stamp_annotation(buf, preview, self.anno_highlight)
        # Rulers stamp last: fills replace pixels (no blending), so a
        # box drawn later would erase an earlier measurement line.
        # Measurements stay readable above any shape, like the live
        # ruler widget does.
        for anno in rulers:
            self.stamp_annotation(buf, anno)
        if selected is not None and selected["kind"] != "text":
            if selected["kind"] == "path":
                corners = tuple(
                    self.image_px_to_view(self.px_from_world(p))
                    for p in selected["points"])
                active = corners[self.anno_edit_anchor] \
                    if isinstance(self.anno_edit_anchor, int) else None
            else:
                a = self.image_px_to_view(
                    self.px_from_world(selected["a"]))
                b = self.image_px_to_view(
                    self.px_from_world(selected["b"]))
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
                    # get_preferred_size reflects the text as it is NOW;
                    # the allocation lags a layout pass and reads 1x1
                    # right after an edit rebuilt the label, which shrank
                    # the handles to a dot.  Margins hold the position
                    # set above, so subtract them for the text itself.
                    _, nat = anno["label"].get_preferred_size()
                    w = max(nat.width
                            - anno["label"].get_margin_start(), 10)
                    h = max(nat.height
                            - anno["label"].get_margin_top(), 10)
                    self.stamp_selection(buf, ((x, y), (x + w, y),
                                               (x, y + h), (x + w, y + h)))
            else:
                anno["label"].hide()
        # Which rulers are on-screen this pass; a single one keeps its plain
        # up-right readout, several switch to spread-out placement + leaders.
        vis = []
        for anno in rulers:
            a = self.image_px_to_view(self.px_from_world(anno["a"]))
            b = self.image_px_to_view(self.px_from_world(anno["b"]))
            mid_x, mid_y = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
            if -40 <= mid_x <= view.width and -20 <= mid_y <= view.height:
                vis.append((anno, a, b, mid_x, mid_y))
            else:
                anno["label"].hide()
        multi = len(vis) > 1
        segs = [(a, b) for _, a, b, _, _ in vis]
        placed = []    # rects of ruler labels already positioned this pass
        leaders = []   # leader segments already claimed, kept clear of rects
        for idx, (anno, a, b, mid_x, mid_y) in enumerate(vis):
            label = anno["label"]
            dist = math.hypot(anno["b"][0] - anno["a"][0],
                              anno["b"][1] - anno["a"][1])
            label.set_text(self.format_distance(dist))
            label.show()   # a hidden label measures as zero
            # get_preferred_size folds in the margins, which still hold the
            # previous position; subtract them for the text's own size.
            _, nat = label.get_preferred_size()
            text_w = nat.width - label.get_margin_start()
            text_h = nat.height - label.get_margin_top()
            if multi:   # off the shared crossing, beside each own line
                others = segs[:idx] + segs[idx + 1:]
                x, y = self.pick_ruler_label_spot(a, b, text_w, text_h,
                                                  placed, leaders, others,
                                                  view)
            else:
                x, y = self.avoid_label_overlap(mid_x + 10,
                                                mid_y - text_h - 6,
                                                text_w, text_h, placed, view)
            label.set_margin_start(int(x))
            label.set_margin_top(int(y))
            rect = (x, y, x + text_w, y + text_h)
            placed.append(rect)
            if multi:
                seg = self.ruler_leader_seg(a, b, rect)
                if seg is not None:
                    leaders.append(seg)
        # With several rulers a bare readout no longer says which line it
        # measures (crossing rulers especially); tie each back to its own
        # line with a dotted leader, distinct from the solid ruler lines.
        # Labels are widgets stacked above this pixbuf, so a leader can
        # never paint over a chip -- the placement above keeps leaders and
        # foreign chips apart instead.
        for end, foot in leaders:
            self.stamp_segment(buf, end, foot, self.RULER_CASING,
                               self.RULER_CORE, 1, 2)
        self.anno_image.set_from_pixbuf(buf)
        self.anno_image.set_margin_start(0)
        self.anno_image.set_margin_top(0)
        self.anno_image.show()

    @staticmethod
    def rects_overlap(p, q):
        return (p[0] < q[2] and p[2] > q[0]
                and p[1] < q[3] and p[3] > q[1])

    def avoid_label_overlap(self, x, y, w, h, placed, view):
        """Nudge a w*h label from its desired (x, y) so it clears every
        ruler label already placed this pass: drop it just below the
        blocking label, wrap to a fresh column when one fills, and keep it
        inside the viewport.  Without this, rulers whose midpoints sit close
        together stack their readouts on the same spot and become unreadable.
        Best-effort and bounded: a viewport packed edge-to-edge with labels
        may still leave a residual overlap rather than loop forever."""
        gap = 3
        max_x = max(2, view.width - w - 2)
        max_y = max(2, view.height - h - 2)
        x = min(max(2, x), max_x)
        y = min(max(2, y), max_y)
        for _ in range(len(placed) * 2 + 2):
            rect = (x, y, x + w, y + h)
            hit = next((r for r in placed if self.rects_overlap(rect, r)),
                       None)
            if hit is None:
                break
            y = hit[3] + gap            # just below the blocking label
            if y > max_y:               # column full: start the next one
                x = min(x + w + gap, max_x)
                y = 2
        return x, y

    def ruler_label_spot(self, a, b, mid_x, mid_y, w, h):
        """Desired top-left for a ruler's readout when several rulers share
        the view.  Shift along the line (tangent) so crossing rulers don't
        pile their labels and leaders on the shared crossing, then lift off
        the line (normal) so each chip sits beside its own line.  The leader
        then lands on a distinct stretch of that line, away from the crossing."""
        dvx, dvy = b[0] - a[0], b[1] - a[1]
        length = math.hypot(dvx, dvy) or 1.0
        tx, ty = dvx / length, dvy / length         # unit tangent
        nx, ny = -ty, tx                             # unit normal
        if ny > 0 or (abs(ny) < 1e-9 and nx < 0):    # aim the normal upward
            nx, ny = -nx, -ny
        sdir = 1.0 if tx >= 0 else -1.0              # lean toward the right end
        shift = min(0.30 * length, 64.0)
        foot_x = mid_x + sdir * tx * shift
        foot_y = mid_y + sdir * ty * shift
        lift = (abs(nx) * w + abs(ny) * h) / 2.0 + 12
        return foot_x + nx * lift - w / 2.0, foot_y + ny * lift - h / 2.0

    @staticmethod
    def seg_hits_rect(p, q, rect):
        """Does segment p-q pass through rect?  (Liang-Barsky reject test.)"""
        x0, y0, x1, y1 = rect
        dx, dy = q[0] - p[0], q[1] - p[1]
        t0, t1 = 0.0, 1.0
        for num, den in ((p[0] - x0, -dx), (x1 - p[0], dx),
                         (p[1] - y0, -dy), (y1 - p[1], dy)):
            if den == 0:
                if num < 0:
                    return False
            else:
                r = num / den
                if den < 0:
                    t0 = max(t0, r)   # entering this boundary
                else:
                    t1 = min(t1, r)   # leaving it
                if t0 > t1:
                    return False
        return True

    @staticmethod
    def ruler_leader_seg(a, b, rect):
        """Leader for a readout at rect: from the label edge to the closest
        point of segment a-b.  The foot lands on that specific line (not a
        shared crossing), so crossing rulers stay identifiable.  None when
        the segment already passes under the label -- adjacency says it all."""
        lx0, ly0, lx1, ly1 = rect
        lcx, lcy = (lx0 + lx1) / 2.0, (ly0 + ly1) / 2.0
        dx, dy = b[0] - a[0], b[1] - a[1]
        denom = dx * dx + dy * dy
        t = 0.0 if denom == 0 else \
            ((lcx - a[0]) * dx + (lcy - a[1]) * dy) / denom
        t = max(0.0, min(1.0, t))
        px, py = a[0] + t * dx, a[1] + t * dy
        ex = min(max(px, lx0), lx1)   # stop at the label boundary
        ey = min(max(py, ly0), ly1)
        if abs(ex - px) < 1 and abs(ey - py) < 1:
            return None
        return ((ex, ey), (px, py))

    def pick_ruler_label_spot(self, a, b, w, h, placed, leaders, others,
                              view):
        """Place one ruler's readout so the whole arrangement stays legible:
        try anchor points along the ruler's own line and both sides of it,
        and take the first spot whose chip covers no other chip or leader
        and whose own leader does not run under an earlier chip (chips are
        widgets above the overlay, so anything under one is lost).  The
        strict first sweep also refuses to cover the other rulers' lines
        themselves, which walks chips away from a shared crossing; rulers
        packed too closely for that (near-parallel neighbours) retry without
        it, and the plain spread + shove remains the last resort."""
        dvx, dvy = b[0] - a[0], b[1] - a[1]
        length = math.hypot(dvx, dvy) or 1.0
        tx, ty = dvx / length, dvy / length
        # first side = the upward normal, matching the single-ruler habit
        first = -1.0 if tx > 0 else 1.0
        for strict in (True, False):
            for frac in (0.5, 0.34, 0.66, 0.2, 0.8):
                ax = a[0] + dvx * frac
                ay = a[1] + dvy * frac
                if not (0 <= ax <= view.width and 0 <= ay <= view.height):
                    continue   # anchor scrolled out: label points nowhere
                for side in (first, -first):
                    nx, ny = -ty * side, tx * side
                    lift = (abs(nx) * w + abs(ny) * h) / 2.0 + 12
                    x = ax + nx * lift - w / 2.0
                    y = ay + ny * lift - h / 2.0
                    x = min(max(2, x), max(2, view.width - w - 2))
                    y = min(max(2, y), max(2, view.height - h - 2))
                    rect = (x, y, x + w, y + h)
                    if any(self.rects_overlap(rect, r) for r in placed):
                        continue
                    if any(self.seg_hits_rect(s[0], s[1], rect)
                           for s in leaders):
                        continue   # chip would sit on an earlier leader
                    if strict and any(self.seg_hits_rect(oa, ob, rect)
                                      for oa, ob in others):
                        continue   # chip would cover someone else's line
                    seg = self.ruler_leader_seg(a, b, rect)
                    if seg is not None and any(
                            self.seg_hits_rect(seg[0], seg[1], r)
                            for r in placed):
                        continue   # leader would vanish under a chip
                    return x, y
        mid_x, mid_y = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
        x, y = self.ruler_label_spot(a, b, mid_x, mid_y, w, h)
        return self.avoid_label_overlap(x, y, w, h, placed, view)

    def stamp_annotation(self, buf, shape, highlight=False):
        """highlight ("h"): thicker stroke under a neon-green halo, so
        the drawn shapes pop on a busy image.  Rulers keep their own
        colors (the branch below returns first) and texts are labels."""
        if shape["kind"] == "path":
            pts = [self.image_px_to_view(self.px_from_world(p))
                   for p in shape["points"]]
            core = self.color_rgba(shape["color"])
            casing = self.ANNO_CASING if shape.get("casing", True) \
                else None
            width = shape.get("width", 1)
            dash = shape.get("dash", 0)
            if highlight:
                casing = self.HIGHLIGHT_CASING
                width = min(width + 2, 12)
            segments = list(zip(pts, pts[1:]))
            # all casing first, then all core, so a later segment cannot
            # cut into a finished corner's core
            if casing is not None:
                for sa, sb in segments:
                    self.stamp_segment(buf, sa, sb, casing, None,
                                       width, dash)
            for sa, sb in segments:
                self.stamp_segment(buf, sa, sb, None, core, width, dash)
            return
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
        stroke_w = shape.get("width", 1)
        if highlight:
            casing = self.HIGHLIGHT_CASING
            stroke_w = min(stroke_w + 2, 12)
        if shape["kind"] == "line":
            self.stamp_segment(buf, a, b, casing, core,
                               stroke_w, shape.get("dash", 0))
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

    def restore_focus(self):
        """Hand the keyboard back to the main window after a modal
        dialog: some backends (macOS quartz notably) fail to refocus the
        parent when a transient closes, leaving every key -- the Esc that
        the mode toast promises included -- dead until a click."""
        self.window.present()
        target = self.browser_view if self.browser_active else self.scroll
        target.grab_focus()

    @staticmethod
    def cancel_on_escape(dialog):
        """Esc cancels the dialog even when the focus sits in a text
        widget whose input method (macOS quartz) would swallow the key
        before the dialog's default Esc-close binding runs: a handler on
        the dialog itself sees the key before the focus-widget forward."""
        def on_dialog_key(widget, event):
            if Gdk.keyval_name(event.keyval) == "Escape":
                dialog.response(Gtk.ResponseType.CANCEL)
                return True
            return False
        dialog.connect("key-press-event", on_dialog_key)

    def ask_annotation_text(self, point, edit=None):
        """Text dialog: creates an annotation at point, or reworks the
        existing one passed as edit (selection + "e")."""
        dialog = Gtk.Dialog(title="Edit Text" if edit else "Text",
                            transient_for=self.window, modal=True)
        self.cancel_on_escape(dialog)
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
        self.restore_focus()
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

    def ask_note(self):
        """Note dialog ("n"): free-form text for the whole image — no
        position or style, shown at the top-left like the info chips
        and saved into the same metadata on Ctrl+S.  OK with the text
        emptied removes the note; notes bypass the undo stack."""
        if self.pixbuf is None:
            return  # animations carry no metadata (like annotations)
        dialog = Gtk.Dialog(title="Edit Note" if self.note else "Note",
                            transient_for=self.window, modal=True)
        self.cancel_on_escape(dialog)
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
        if self.note:
            editable.set_text(self.note)
            editable.set_position(len(self.note))
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
        hint = Gtk.Label()
        hint.set_markup("<small>Enter: new line · Ctrl+Enter: OK · "
                        "empty removes the note</small>")
        hint.set_halign(Gtk.Align.START)
        box = dialog.get_content_area()
        box.set_border_width(10)
        box.set_spacing(6)
        box.pack_start(scroll, True, True, 0)
        box.pack_start(hangul, False, False, 0)
        box.pack_start(hint, False, False, 0)
        dialog.show_all()
        confirmed = dialog.run() == Gtk.ResponseType.OK
        text = editable.get_text().strip()
        dialog.destroy()
        self.restore_focus()
        if not confirmed or text == self.note:
            return
        removed = bool(self.note) and not text
        self.note = text
        self.update_note_overlay()
        self.update_dirty()
        self.show_toast("note removed" if removed else "note set")

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
        self.cancel_on_escape(dialog)
        dialog.set_keep_above(True)  # stay over a fullscreen parent
        dialog.add_button("Cancel", Gtk.ResponseType.CANCEL)
        dialog.add_button("OK", Gtk.ResponseType.OK)
        dialog.set_default_response(Gtk.ResponseType.OK)
        current = self.anno_tool \
            if self.anno_tool in ("box", "ellipse", "line", "path") \
            else self.anno_shape
        shape_row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL,
                            spacing=10)
        radios = {}
        group = None
        for kind in ("box", "ellipse", "line", "path"):
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
            # A line/path always draws with the line color: its fill and
            # the outline toggle rest while one is chosen.  The stroke
            # style (width/type/halo) follows the outline for box/ellipse.
            is_line = radios["line"].get_active() \
                or radios["path"].get_active()
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
        self.restore_focus()
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
        replace_span = getattr(entry, "replace_span", None)
        if replace_span is not None:
            replace_span(anchor, old_len, new)  # keeps the scroll put
            return
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
        if anno["kind"] == "text":
            return (anno["at"],)
        if anno["kind"] == "path":
            return tuple(anno["points"])
        return (anno["a"], anno["b"])

    # An edit anchor is "a"/"b" for two-point shapes and a vertex index
    # for paths; 0 is a valid anchor, so tests are "is not None".
    @staticmethod
    def anchor_get(anno, which):
        return anno["points"][which] if isinstance(which, int) \
            else anno[which]

    @staticmethod
    def anchor_set(anno, which, point):
        if isinstance(which, int):
            anno["points"][which] = point
        else:
            anno[which] = point

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
        pts = (self.anchor_get(anno, target),) if target is not None \
            else self.anchor_points(anno)
        dx = max(lo[0] - min(p[0] for p in pts),
                 min(dx, hi[0] - max(p[0] for p in pts)))
        dy = max(lo[1] - min(p[1] for p in pts),
                 min(dy, hi[1] - max(p[1] for p in pts)))
        if not dx and not dy:
            return
        # a run of nudges coalesces into a single undo step
        top = self.anno_undo[-1] if self.anno_undo else None
        if target is not None:
            point = self.anchor_get(anno, target)
            self.anchor_set(anno, target, (point[0] + dx, point[1] + dy))
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
        if anno["kind"] == "path":   # newest vertex first, like "b"
            order = (None,) + tuple(range(len(anno["points"]) - 1, -1, -1))
        else:
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
        if "points" in anno:
            anno["points"] = [(x + dx, y + dy)
                              for x, y in anno["points"]]

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
            point = self.anchor_get(anno, which)
            self.anchor_set(anno, which, (point[0] + sign * dx,
                                          point[1] + sign * dy))
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
        self.note = ""
        self.legend_entries = None  # like the note: metadata, not request
        self.update_note_overlay()
        self.anno_undo = []
        self.anno_redo = []
        self.anno_selected = None
        self.anno_edit_anchor = None
        self.anno_rev += 1
        self.anno_tool = None
        self.anno_start = self.anno_cursor = None
        del self.anno_path[:]
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
        if anno["kind"] == "path":
            # variable-length coordinate list, then the same style tail
            # as the fixed shapes ("0" = the reserved fill slot)
            extra = ",%d,%d" % (anno.get("width", 1), anno.get("dash", 0))
            if not anno.get("casing", True):
                extra += ",0"
            return ("path=%s,%s,0%s"
                    % (",".join("%.10g,%.10g" % (p[0], p[1])
                                for p in anno["points"]), color, extra))
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
        if self.note:
            lines.append("note=%s" % self.escape_meta(self.note))
        lines.extend("legend=%s" % serialize_legend_entry(entry)
                     for entry in self.legend_entries or [])
        lines.extend(self.serialize_anno(anno) for anno in self.annotations)
        return lines

    @staticmethod
    def notable_lines(lines):
        """Metadata minus the ruler measurements: rulers are transient
        working aids, so a delta made of nothing but rulers is not worth
        a save question (Ctrl+S still stores them)."""
        return [l for l in lines if not l.startswith("ruler=")]

    def update_dirty(self):
        """Retitle ("*name") when the metadata diverges from the saved
        state in a way worth asking about; undoing back to it (or a
        rulers-only delta) clears the marker again."""
        lines = self.serialize_annotations()
        dirty = lines != self.saved_meta
        notable = dirty and \
            self.notable_lines(lines) != self.notable_lines(self.saved_meta)
        if dirty != self.anno_dirty or notable != self.anno_notable:
            self.anno_dirty = dirty
            self.anno_notable = notable
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
        legend_restored = []
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
                elif key == "note":
                    text = self.unescape_meta(value)
                    if text.strip():
                        self.note = text.strip()
                elif key == "legend":
                    entry, error = parse_legend_entry(value)
                    if entry is not None:
                        legend_restored.append(entry)
                elif key in ("box", "ellipse", "line", "path", "ruler",
                             "text"):
                    self.attach_annotation(self.parse_anno_line(key, value))
            except ValueError:
                continue  # skip malformed lines
        if legend_restored:
            self.legend_entries = legend_restored
        # Restored annotations enter the undo stack as adds, so "u"
        # deletes newest-first across restored and freshly drawn ones
        # alike (delete-last is folded into undo/redo).
        self.anno_undo.extend(("add", anno, None)
                              for anno in self.annotations)
        self.update_note_overlay()
        if self.annotations or ppu_restored or self.note or legend_restored:
            parts = []
            if self.annotations:
                parts.append("%d annotation%s"
                             % (len(self.annotations),
                                "" if len(self.annotations) == 1 else "s"))
            if ppu_restored:
                parts.append("PPU %s px/%s"
                             % (self.trim_decimal(self.ppu, 4), self.unit))
            if self.note:
                parts.append("note")
            if legend_restored:
                parts.append("legend")
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
        if key == "path":
            # the coordinate list runs until the first non-number (the
            # color); the style fields after it match the fixed shapes
            parts = value.split(",")
            coords = []
            index = 0
            while index < len(parts):
                try:
                    coords.append(float(parts[index]))
                except ValueError:
                    break
                index += 1
            if len(coords) < 4 or len(coords) % 2 or index >= len(parts):
                raise ValueError("bad path: %s" % value)
            anno = {"kind": "path",
                    "points": [(coords[i], coords[i + 1])
                               for i in range(0, len(coords), 2)],
                    "color": Viewer.parse_color(parts[index])}
            tail = parts[index + 1:]   # fill (reserved), width, dash, halo
            if len(tail) > 1:
                try:
                    anno["width"] = max(1, min(int(float(tail[1])), 8))
                    if len(tail) > 2:
                        code = int(float(tail[2]))
                        anno["dash"] = code if code in (1, 2) else 0
                except ValueError:
                    pass  # keep the path, default 1px solid
            if len(tail) > 3 and tail[3].strip() == "0":
                anno["casing"] = False
            return anno
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
                raise ValueError("expects X,Y[,STYLE...],TEXT")
            try:
                at = (float(parts[0]), float(parts[1]))
            except ValueError:
                raise ValueError("bad position: %s,%s"
                                 % (parts[0], parts[1]))
            anno = {"kind": "text", "at": at, "size": 16,
                    "color": Viewer.DEFAULT_LINE, "bg": True,
                    "bg_color": Viewer.DEFAULT_BG, "bg_opaque": False}
            # Optional size=/color=/bg= fields before the text proper;
            # the text starts at the first field that is none of them
            # (or right after an explicit text=, which lets a note
            # begin with "size=" literally).
            rest = parts[2]
            while True:
                head, sep, tail = rest.partition(",")
                key, eq, val = head.partition("=")
                key = key.strip().lower()
                if eq and key == "text":
                    rest = val + sep + tail
                    break
                if not (eq and key in ("size", "color", "bg")):
                    break
                if not sep or not tail.strip():
                    raise ValueError("TEXT missing after %s" % head)
                val = val.strip()
                if key == "size":
                    try:
                        anno["size"] = int(val)
                    except ValueError:
                        raise ValueError("bad size: %s" % val)
                    if not 6 <= anno["size"] <= 96:
                        raise ValueError("size must be 6-96, got: %s"
                                         % val)
                elif key == "color":
                    anno["color"] = Viewer.option_color(val)
                elif val == "0":    # bg=0: no backdrop
                    anno["bg"] = False
                elif val.startswith("#") and len(val) == 9:
                    try:  # bg=#RRGGBBAA, AA >= 80 = opaque (like FILL)
                        int(val[1:9], 16)
                    except ValueError:
                        raise ValueError("bad bg: %s" % val)
                    anno["bg"] = True
                    anno["bg_color"] = val[:7]
                    anno["bg_opaque"] = int(val[7:9], 16) >= 0x80
                else:
                    anno["bg"] = True
                    anno["bg_color"] = Viewer.option_color(val)
                    anno["bg_opaque"] = False
                rest = tail
            # literal \n starts a new line, like in the metadata format;
            # tabs would break the request protocol
            text = Viewer.unescape_meta(rest).replace("\t", " ")
            if not text.strip():
                raise ValueError("empty text")
            anno["text"] = text
            return anno
        if kind == "path":
            parts = [part.strip() for part in value.split(",")]
            coords = []
            while parts:
                try:
                    coords.append(float(parts[0]))
                except ValueError:
                    break
                parts.pop(0)
            if len(coords) < 4 or len(coords) % 2:
                raise ValueError("expects X1,Y1,X2,Y2[,X3,Y3...]")
            anno = {"kind": "path",
                    "points": [(coords[i], coords[i + 1])
                               for i in range(0, len(coords), 2)],
                    "color": Viewer.DEFAULT_LINE}
            if parts:
                anno["color"] = Viewer.option_color(parts.pop(0))
            if parts:
                width = parts.pop(0)
                try:
                    anno["width"] = int(width)
                except ValueError:
                    raise ValueError("bad width: %s" % width)
                if not 1 <= anno["width"] <= 8:
                    raise ValueError("width must be 1-8, got: %s" % width)
            if parts:
                dashes = {"solid": 0, "dashed": 1, "dotted": 2,
                          "0": 0, "1": 1, "2": 2}
                dash = parts.pop(0)
                if dash.lower() not in dashes:
                    raise ValueError("dash must be solid/dashed/dotted, "
                                     "got: %s" % dash)
                anno["dash"] = dashes[dash.lower()]
            if parts:
                raise ValueError("too many fields: %s" % ",".join(parts))
            return anno
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

    @staticmethod
    def parse_anno_json(obj):
        """One --json entry as a full annotation dict — the same JSON
        object format fe_embed.py takes: shapes give "a"/"b" pairs or
        x1/y1/x2/y2, texts "at" or x/y plus "text", with the optional
        style fields on top.  Raises ValueError on malformed input."""
        if not isinstance(obj, dict) or "kind" not in obj:
            raise ValueError("each entry needs a \"kind\"")
        obj = dict(obj)
        kind = obj.pop("kind")
        try:
            if kind == "text":
                at = obj.pop("at", None) or (obj.pop("x"), obj.pop("y"))
                anno = {"kind": "text", "at": (float(at[0]), float(at[1])),
                        "text": str(obj.pop("text"))}
                if not anno["text"].strip():
                    raise ValueError("empty text")
                anno["size"] = int(obj.pop("size", 16))
                if not 6 <= anno["size"] <= 96:
                    raise ValueError("size must be 6-96, got: %s"
                                     % anno["size"])
                anno["color"] = Viewer.option_color(
                    str(obj.pop("color", Viewer.DEFAULT_LINE)))
                anno["bg"] = bool(obj.pop("bg", True))
                anno["bg_color"] = Viewer.option_color(
                    str(obj.pop("bg_color", Viewer.DEFAULT_BG)))
                anno["bg_opaque"] = bool(obj.pop("bg_opaque", False))
            elif kind == "path":
                points = obj.pop("points")
                if not isinstance(points, list) or len(points) < 2:
                    raise ValueError("path needs a \"points\" array "
                                     "of 2+ [x, y] pairs")
                anno = {"kind": "path",
                        "points": [(float(p[0]), float(p[1]))
                                   for p in points],
                        "color": Viewer.option_color(
                            str(obj.pop("color", Viewer.DEFAULT_LINE)))}
                anno["width"] = int(obj.pop("width", 1))
                if not 1 <= anno["width"] <= 8:
                    raise ValueError("width must be 1-8, got: %s"
                                     % anno["width"])
                dash = obj.pop("dash", 0)
                dashes = {"solid": 0, "dashed": 1, "dotted": 2}
                if isinstance(dash, str) and dash.lower() in dashes:
                    anno["dash"] = dashes[dash.lower()]
                elif dash in (0, 1, 2):
                    anno["dash"] = int(dash)
                else:
                    raise ValueError("dash must be solid/dashed/"
                                     "dotted, got: %r" % (dash,))
                if not obj.pop("casing", True):
                    anno["casing"] = False
            elif kind in ("box", "ellipse", "line", "ruler"):
                a = obj.pop("a", None) or (obj.pop("x1"), obj.pop("y1"))
                b = obj.pop("b", None) or (obj.pop("x2"), obj.pop("y2"))
                anno = {"kind": kind, "a": (float(a[0]), float(a[1])),
                        "b": (float(b[0]), float(b[1]))}
                if kind != "ruler":
                    anno["color"] = Viewer.option_color(
                        str(obj.pop("color", Viewer.DEFAULT_LINE)))
                    anno["width"] = int(obj.pop("width", 1))
                    if not 1 <= anno["width"] <= 8:
                        raise ValueError("width must be 1-8, got: %s"
                                         % anno["width"])
                    dash = obj.pop("dash", 0)
                    dashes = {"solid": 0, "dashed": 1, "dotted": 2}
                    if isinstance(dash, str) and dash.lower() in dashes:
                        anno["dash"] = dashes[dash.lower()]
                    elif dash in (0, 1, 2):
                        anno["dash"] = int(dash)
                    else:
                        raise ValueError("dash must be solid/dashed/"
                                         "dotted, got: %r" % (dash,))
                    if not obj.pop("casing", True):
                        anno["casing"] = False
                if kind in ("box", "ellipse"):
                    fill = obj.pop("fill", None)
                    fill_opaque = bool(obj.pop("fill_opaque", False))
                    if fill is not None:
                        anno["fill"] = Viewer.option_color(str(fill))
                        anno["fill_opaque"] = fill_opaque
                    if not obj.pop("outline", True):
                        if fill is None:
                            raise ValueError("outline=false needs a fill")
                        anno["outline"] = False
            else:
                raise ValueError("unknown kind: %s" % kind)
        except KeyError as exc:
            raise ValueError("%s: missing field %s" % (kind, exc))
        except (TypeError, IndexError):
            raise ValueError("%s: bad coordinates" % kind)
        if obj:
            raise ValueError("%s: unknown fields: %s"
                             % (kind, ", ".join(sorted(obj))))
        return anno

    @staticmethod
    def parse_json_document(data):
        """A --json payload: either a plain array of annotation
        objects, or an object {"ppu": N, "unit": U, "note": TEXT,
        "legend": [LINE, ...], "annotations": [...]} (every key
        optional) so one file carries everything — the same document
        format fe_embed.py takes.  Each legend LINE is one text legend
        definition line ("box COLOR [STYLE] LABEL...").  Returns
        (annos, ppu, unit, note, legend_entries); raises ValueError."""
        if isinstance(data, list):
            return ([Viewer.parse_anno_json(obj) for obj in data],
                    None, None, None, None)
        if not isinstance(data, dict):
            raise ValueError("expected a JSON array or object")
        data = dict(data)
        ppu = data.pop("ppu", None)
        if ppu is not None:
            try:
                ppu = float(ppu)
            except (TypeError, ValueError):
                raise ValueError("bad ppu: %r" % (ppu,))
            if ppu <= 0:
                raise ValueError("ppu must be > 0")
        unit = data.pop("unit", None)
        if unit is not None:
            unit = str(unit).strip()
            if not unit:
                raise ValueError("empty unit")
        note = data.pop("note", None)
        if note is not None:
            note = str(note)
            if not note.strip():
                raise ValueError("empty note")
        legend = data.pop("legend", None)
        if legend is not None:
            if not isinstance(legend, list) or not legend:
                raise ValueError("\"legend\" must be a non-empty array "
                                 "of definition lines")
            parsed = []
            for index, line in enumerate(legend):
                entry, error = parse_legend_entry(str(line))
                if error:
                    raise ValueError("legend[%d]: %s" % (index, error))
                parsed.append(entry)
            legend = parsed
        annos = data.pop("annotations", [])
        if not isinstance(annos, list):
            raise ValueError("\"annotations\" must be an array")
        if data:
            raise ValueError("unknown fields: %s"
                             % ", ".join(sorted(data)))
        return ([Viewer.parse_anno_json(obj) for obj in annos],
                ppu, unit, note, legend)

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

    def apply_request_note(self, note):
        """A note passed on the command line (--note): replaces the
        file's saved note on screen, unsaved until Ctrl+S."""
        if not note or not note.strip() or self.pixbuf is None:
            return
        self.note = note.strip()
        self.update_note_overlay()
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
        self.restore_focus()

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
        self.cancel_on_escape(dialog)
        dialog.set_keep_above(True)  # stay over a fullscreen parent
        dialog.add_button("Cancel", Gtk.ResponseType.CANCEL)
        dialog.add_button("OK", Gtk.ResponseType.OK)
        dialog.set_default_response(Gtk.ResponseType.OK)
        entry = Gtk.Entry()
        if self.ppu:
            entry.set_text(self.trim_decimal(self.ppu, 6))
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
        self.restore_focus()
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
        if not self.anno_notable:
            return True   # clean, or only transient ruler measurements
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
        self.restore_focus()
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
            elif self.anno_tool == "path" and self.anno_path:
                # drop the unfinished path; the tool stays for a retry
                del self.anno_path[:]
                self.anno_start = self.anno_cursor = None
                self.anno_rev += 1
                self.update_anno_overlay()
            elif self.anno_tool is not None:
                self.set_anno_tool(None)
            elif self.from_browser and not self.stack_mode:
                # nothing left to cancel: go back to the browser we came from
                self.enter_browser(select=self.path)
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
        elif key in ("n", "N"):
            self.ask_note()
        elif key in ("u", "U"):
            self.undo_annotation()
        elif key in ("y", "Y"):
            self.redo_annotation()
        elif key in ("c", "C") \
                and event.state & Gdk.ModifierType.CONTROL_MASK \
                and event.state & Gdk.ModifierType.SHIFT_MASK:
            self.copy_path_to_clipboard()  # Ctrl+Shift+C
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
                self.show_toast("PPU from stack manifest: %s px/%s"
                                % (self.trim_decimal(
                                    self.active_level()["ppu"], 4), self.unit))
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
        elif key in ("h", "H"):  # emphasize the drawn shapes
            self.anno_highlight = not self.anno_highlight
            if self.anno_highlight and not self.draw_visible:
                self.draw_visible = True  # highlighting hidden shapes
            self.update_view_overlays()
            self.show_toast("shape highlight %s"
                            % ("on" if self.anno_highlight else "off"))
        elif key in ("m", "M"):  # ruler points snap to the nearest edge
            self.snap_enabled = not self.snap_enabled
            self.update_mode_toast()
            self.refresh_snap_preview()  # react without waiting for motion
            self.show_toast("ruler edge snap %s"
                            % ("on" if self.snap_enabled else "off"))
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
        elif key in ("Return", "KP_Enter") and self.anno_tool == "path" \
                and self.anno_path:
            self.finish_path()  # commit with the points placed so far
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

    def tool_click(self, event):
        """True when the press/release places tool points.  Quartz (the
        mac dev environment) turns Ctrl+left-click into a button-3
        event; while measuring/drawing Ctrl is a modifier (direction
        lock), so such an event is a click, not a context menu."""
        return event.button == 1 or (
            event.button == 3
            and bool(event.state & Gdk.ModifierType.CONTROL_MASK)
            and (self.ruler_active or self.anno_tool is not None))

    def on_button_press(self, widget, event):
        if event.type == Gdk.EventType.DOUBLE_BUTTON_PRESS \
                and self.anno_tool == "path" and self.anno_path \
                and self.tool_click(event):
            # the pair's first click already placed this vertex
            self.finish_path()
            self.drag_origin = None  # swallow the pair's second release
            return True
        if event.type != Gdk.EventType.BUTTON_PRESS:
            return False
        if not self.tool_click(event):
            if event.button == 3:
                return self.show_context_menu(event)
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
                    self.ruler_cursor = self.snap_ruler_end(point,
                                                            event.state)
                    self.update_ruler_overlay()
            elif self.ruler_start is None:
                self.update_snap_hover(event)
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

    def on_leave(self, widget, event):
        if self.snap_hover is not None:
            self.snap_hover = None
            self.update_snap_marker()
        return False

    def on_button_release(self, widget, event):
        if not self.tool_click(event) or self.drag_origin is None:
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
                if self.edge_snap_allowed():
                    point = self.edge_snap_world(point) or point
                self.ruler_start = point           # start a new measurement
                self.ruler_end = self.ruler_cursor = None
                self.ruler_axis = self.ruler_dir = None   # re-pick fresh
                self.snap_hover = None
                self.update_snap_marker()
                self.update_ruler_overlay()
            else:
                # second click commits the measurement as an annotation:
                # it persists, undoes and saves like any drawn shape
                self.add_ruler_annotation(
                    self.ruler_start, self.snap_ruler_end(point,
                                                          event.state))
                self.anno_undo.append(("add", self.annotations[-1], None))
                del self.anno_redo[:]
                self.ruler_start = self.ruler_end = self.ruler_cursor = None
                self.ruler_axis = self.ruler_dir = None
                self.update_ruler_overlay()        # clear the live preview
                self.update_anno_overlay()
                self.update_dirty()
        elif self.anno_tool == "text":
            self.ask_annotation_text(point)
        elif self.anno_tool == "path":
            if self.anno_path:  # Shift constrains against the last vertex
                point = self.constrain_corner(point, event.state)
            self.anno_path.append(point)
            self.anno_start = point    # constraint base and motion gate
            self.anno_cursor = None
            self.anno_rev += 1
            self.update_anno_overlay()
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
                "path": "cell", "text": "text"}.get(self.anno_tool)

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
        # show(), not show_all(): the image screen and the thumbnail
        # browser share the window and enter/leave_browser manage which
        # one is visible; show_all would un-hide the inactive screen too
        # (the window splits into image + browser halves).
        self.window.show()
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
            legend = ppu = unit = note = None
            legend_entries = None
            stack = False
            inline = []   # ppu=/center= after a level= bind to that level
            annos = []    # annotations to draw once the image is open
            bad = None
            for field in fields[1:]:
                key, _, value = field.partition("=")
                key, value = key.strip(), value.strip()
                if key == "legend":
                    legend = value or None
                elif key == "legendtext":
                    # a --json legend: the definition lines themselves,
                    # newline-escaped to fit one request field
                    legend_entries, error = parse_legend_text(
                        self.unescape_meta(value), "legend")
                    if error:
                        bad = error
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
                elif key == "note":
                    note = self.unescape_meta(value)
                elif key in ("box", "ellipse", "line", "path", "ruler",
                             "text"):
                    try:
                        annos.append(self.parse_anno_line(key, value))
                    except ValueError:
                        bad = "ERR bad %s: %s" % (key, value)
                # unknown keys are ignored for forward compatibility
            if bad:
                reply = bad
            elif inline:
                reply = self.open_request(inline[0]["path"], legend, None,
                                          unit, True, inline, annos, note,
                                          legend_entries)
            elif path:
                reply = self.open_request(path, legend, ppu, unit, stack,
                                          annos=annos, note=note,
                                          legend_entries=legend_entries)
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
        "usage: %s [-m] [-l LEGEND_FILE] [-p PPU] [-u UNIT] [DRAW...]\n"
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
        "  -m, --multi               always open a new, independent window\n"
        "                            (any form above accepts it): no\n"
        "                            forwarding to a running viewer, and\n"
        "                            later runs without it still go to the\n"
        "                            primary instance, never to this window\n"
        "  -l, --legend LEGEND_FILE  overlay LEGEND_FILE at the bottom-right\n"
        "                            corner.  An image file shows as-is\n"
        "                            for this request only; any other\n"
        "                            file is a text legend definition\n"
        "                            drawn as swatch + label rows, one\n"
        "                            entry per line (\"#\" comments):\n"
        "                              box COLOR [STYLE] LABEL...\n"
        "                              line COLOR [STYLE] LABEL...\n"
        "                            COLOR as in the DRAW options; box\n"
        "                            STYLE: solid (default), none (outline\n"
        "                            only), hatch, cross, dots; line STYLE:\n"
        "                            solid (default), dashed, dotted.\n"
        "                            A text legend joins the metadata like\n"
        "                            the drawn shapes: Ctrl+S embeds it\n"
        "                            (legend= lines), and a file opened\n"
        "                            without -l shows its embedded legend\n"
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
        "Coordinates are image pixels with the origin at the image\n"
        "CENTER, x right / y down (stacks: world units, like the\n"
        "ruler).  COLOR is a palette name (%s)\n"
        "or #RRGGBB; 0 = no outline (needs FILL).  FILL is a color, or\n"
        "#RRGGBBAA with AA >= 80 for an opaque fill (default none).\n"
        "WIDTH is the stroke width 1-8, DASH is solid, dashed or dotted.\n"
        "\n"
        "  --box X1,Y1,X2,Y2[,COLOR[,FILL[,WIDTH[,DASH]]]]\n"
        "  --ellipse X1,Y1,X2,Y2[,COLOR[,FILL[,WIDTH[,DASH]]]]\n"
        "  --line X1,Y1,X2,Y2[,COLOR[,WIDTH[,DASH]]]\n"
        "  --path X1,Y1,X2,Y2[,X3,Y3...][,COLOR[,WIDTH[,DASH]]]\n"
        "                            connected line segments through\n"
        "                            every X,Y in order (2+ points)\n"
        "  --ruler X1,Y1,X2,Y2       finished ruler measurement (uses\n"
        "                            the PPU/unit in effect)\n"
        "  --text X,Y[,STYLE...],TEXT\n"
        "                            note at X,Y; STYLE fields are\n"
        "                            size=6-96, color=COLOR and\n"
        "                            bg=0|COLOR|#RRGGBBAA (else 16pt,\n"
        "                            default colors).  TEXT runs to the\n"
        "                            end (commas allowed; text= starts\n"
        "                            it explicitly, a literal \\n breaks\n"
        "                            the line)\n"
        "  --note TEXT               one note for the whole image, no\n"
        "                            position or style (the \"n\" key):\n"
        "                            replaces the saved note on screen,\n"
        "                            unsaved until Ctrl+S; a literal \\n\n"
        "                            breaks the line\n"
        "  --json FILE               annotations from a JSON array of\n"
        "                            objects (\"-\" = stdin), the same\n"
        "                            format fe_embed.py takes; added in\n"
        "                            option order like the DRAW options.\n"
        "                            An object {ppu, unit, note, legend,\n"
        "                            annotations} also carries the\n"
        "                            metadata (explicit -p/-u/--note/-l\n"
        "                            win over the document's values);\n"
        "                            legend is an array of the definition\n"
        "                            lines -l takes\n"
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
        "      m edge snap for the ruler (off by default): the points\n"
        "        snap to the nearest image edge - a crosshair previews\n"
        "        the first point, the end snaps only along the\n"
        "        measuring direction,\n"
        "      d draw shapes: a dialog picks box/ellipse/line/path and\n"
        "        the style - outline (use, color), stroke width (1-8 px)\n"
        "        and type (solid/dashed/dotted) for lines and outlines\n"
        "        alike, the black halo around strokes (on/off) and the\n"
        "        box/ellipse fill (use, color, opaque/translucent); one\n"
        "        of outline/fill always stays on and texts style\n"
        "        themselves; Shift while clicking = square/circle/\n"
        "        45-degree line; a path adds a vertex per click and\n"
        "        double-click/Enter finishes it (Esc drops it),\n"
        "      t text,\n"
        "      n note: one free text per image, no position or style,\n"
        "        shown at the top-left with the info overlays and\n"
        "        saved with the annotations (empty text removes it),\n"
        "      h highlight the drawn shapes on/off: thicker strokes\n"
        "        under a neon-green halo, to spot them on a busy\n"
        "        image (texts and rulers stay as they are),\n"
        "      s select annotations, newest first (Shift+s backwards):\n"
        "        arrows move the selection (Shift = 10 px steps),\n"
        "        e edits it - shapes cycle a resize corner/endpoint\n"
        "          that the arrows then drag, texts reopen their\n"
        "          input dialog prefilled,\n"
        "        Delete/BackSpace removes it, Esc deselects,\n"
        "      u/y undo/redo annotations (u also deletes, newest first),\n"
        "      Ctrl+C copy the visible view (info hidden) to the clipboard,\n"
        "      Ctrl+Shift+C copy the image file path as text (stacks:\n"
        "             the level shown),\n"
        "      Ctrl+S save the annotations, PPU and legend (no autosave):\n"
        "             embedded into a PNG image itself, to a .fe\n"
        "             sidecar file for other formats; browsing to\n"
        "             another image with unsaved changes asks first,\n"
        "      F1/right-click About,\n"
        "      q quit - with unsaved annotations (the title shows\n"
        "        *name) a dialog asks to save/discard/cancel first\n"
        % (APP, APP, APP,
           "/".join(name for name, _ in Viewer.PALETTE)))


def parse_args(args):
    """Returns (path, legend, ppu, unit, is_stack, levels, annos, note,
    legend_entries, multi) or an exit code.

    path is None when inline levels are given; is_stack marks a manifest.
    """
    legend = ppu = unit = stack_file = note = None
    json_ppu = json_unit = json_note = json_legend = None
    multi = False
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
        elif arg in ("-m", "--multi"):
            multi = True
        elif arg in ("-l", "--legend", "-p", "--ppu", "-u", "--unit",
                     "-s", "--stack", "--level", "--center",
                     "--box", "--ellipse", "--line", "--path", "--ruler",
                     "--text", "--note", "--json"):
            i += 1
            if i == len(args):
                sys.stderr.write("%s: %s requires an argument\n" % (APP, arg))
                return 2
            took_value = args[i]
        elif arg.startswith(("--legend=", "--ppu=", "--unit=", "--stack=",
                             "--level=", "--center=", "--box=",
                             "--ellipse=", "--line=", "--path=",
                             "--ruler=", "--text=", "--note=",
                             "--json=")):
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
            elif arg in ("--box", "--ellipse", "--line", "--path",
                         "--ruler", "--text"):
                try:
                    annos.append(Viewer.parse_anno_option(arg[2:],
                                                          took_value))
                except ValueError as exc:
                    sys.stderr.write("%s: %s: %s\n" % (APP, arg, exc))
                    return 2
            elif arg == "--note":
                # literal \n breaks the line; tabs would break the
                # request protocol
                note = Viewer.unescape_meta(took_value).replace("\t", " ")
                if not note.strip():
                    sys.stderr.write("%s: --note expects a text\n" % APP)
                    return 2
            elif arg == "--json":
                try:
                    if took_value == "-":
                        data = json.load(sys.stdin)
                    else:
                        with open(took_value, "r",
                                  encoding="utf-8") as handle:
                            data = json.load(handle)
                    extra, doc_ppu, doc_unit, doc_note, doc_legend = \
                        Viewer.parse_json_document(data)
                    annos.extend(extra)
                    json_ppu = doc_ppu if doc_ppu is not None else json_ppu
                    json_unit = doc_unit or json_unit
                    json_note = doc_note or json_note
                    json_legend = doc_legend or json_legend
                except (OSError, ValueError) as exc:
                    sys.stderr.write("%s: --json %s: %s\n"
                                     % (APP, took_value, exc))
                    return 2
            else:
                stack_file = took_value
        i += 1
    # explicit command-line options win over the JSON document's values
    # (a json ppu never binds to --level lists: those are per-level)
    if ppu is None and json_ppu is not None and not levels:
        ppu = json_ppu
    if unit is None and json_unit is not None:
        unit = json_unit
    if note is None and json_note is not None:
        note = json_note.replace("\t", " ")  # request protocol safety
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
        return (None, legend, None, unit, False, levels, annos, note,
                json_legend, multi)
    if stack_file is not None:
        return (stack_file, legend, ppu, unit, True, None, annos, note,
                json_legend, multi)
    return (paths[0], legend, ppu, unit, False, None, annos, note,
            json_legend, multi)


def main(argv):
    parsed = parse_args(argv[1:])
    if isinstance(parsed, int):
        return parsed
    path, legend, ppu, unit, stack, levels, annos, note, legend_entries, \
        multi = parsed

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
        if (annos or note or legend_entries) and os.path.isdir(path):
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

    server = None
    if not multi:  # --multi: independent window, no instance socket at all
        addr = socket_address(display)
        fields = [path if levels is None else ""]
        if legend is not None:
            fields.append("legend=%s" % legend)
        if legend_entries:
            fields.append("legendtext=%s" % Viewer.escape_meta(
                "\n".join(serialize_legend_entry(entry)
                          for entry in legend_entries)))
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
        if note is not None:
            fields.append("note=%s" % Viewer.escape_meta(note))
        request = "\t".join(fields)
        for _ in range(5):
            code = try_forward(addr, request)
            if code is not None:
                return code
            server = try_bind(addr)
            if server is not None:
                break
            time.sleep(0.2)
        if server is None:
            sys.stderr.write("%s: could not create or reach the instance "
                             "socket\n" % APP)
            return 1

        if not addr.startswith("\0"):
            import atexit
            atexit.register(lambda: os.path.exists(addr) and os.unlink(addr))

    import_gtk()
    Viewer(server, path if levels is None else levels[0]["path"],
           legend, ppu, unit, stack, levels, annos, note, legend_entries)
    Gtk.main()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
