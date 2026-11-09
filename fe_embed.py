#!/usr/bin/env python3
"""Embed flateyes-compatible annotations into PNG files.

Standalone companion to flateyes.py for services that produce PNGs in
bulk (e.g. automated capture) and want each file to carry its markers
(boxes, ellipses, lines, paths, polygons, texts, rulers) the moment it
is written.
flateyes then shows them on open, and Ctrl+S keeps editing the same
chunk.  Python standard library only — deployment is copying this one
file, same as flateyes.py itself.

The annotation metadata lives inside the PNG as an iTXt chunk (UTF-8,
keyword "flateyes") inserted before IEND.  Decoders must skip unknown
ancillary chunks, so the file stays a plain PNG for every other tool;
pixels are never touched.  Coordinates are image pixels with the
origin at the image CENTER (x right, y down) — the same world frame
the viewer uses for multi-magnification stacks — so they are
independent of any viewer zoom.  A box over the top-left quadrant has
negative coordinates.

Library use:

    import fe_embed as fe
    fe.embed("shot_0001.png", [
        fe.box(120, 80, 420, 300, color="red", width=2),
        fe.box(-60, -50, 60, 50, fill="sky", fill_alpha=0x30),
        fe.text(120, 60, "DEFECT #17", size=20, color="white"),
    ], ppu=8.0, unit="um", note="capture rig #3")

    blob = fe.embed_bytes(png_bytes, annos)   # in-memory pipelines
    annos, ppu, unit, note, legend = fe.read("shot_0001.png")

    fe.embed("shot_0001.png", [], legend=[    # legend swatch table
        "box #3DDC55 hatch oxide",            # (definition lines; flateyes
        "line red dashed metal route",        #  shows it bottom-right)
    ])

    # export: the metadata drawn INTO a copy (flateyes at 100% zoom),
    # the legend in a panel the image grows to the right for
    fe.export("shot_0001.png", "shot_0001_view.png", scale=2)
    fe.export_legend("shot_0001.png", "shot_0001_legend.png")
    png = fe.export_bytes(png_bytes, hide=("note",))

CLI use (same option syntax as flateyes itself):

    python3 fe_embed.py --box 120,80,420,300,red,0,2 \
                        --text '120,60,size=20,color=white,DEFECT #17' \
                        shot_*.png
    python3 fe_embed.py --json annos.json shot_0001.png
    python3 fe_embed.py --dump shot_0001.png
    python3 fe_embed.py --export 'out/{stem}_view.png' \
                        --export-legend 'out/{stem}_legend.png' shot_*.png

The export is pure standard library as well: a PNG codec (every color
type, bit depth and interlace), the viewer's overlay painting ported
from flateyes.py (stamp_annotation and friends, the ruler readout
placement), and a TrueType/CFF rasterizer reading the system's font
files (the faces fontconfig hands Pango; a built-in 6x13 bitmap face
when there are none).

Format contract: the chunk layout and the key=value line format mirror
flateyes.py (serialize_anno / parse_anno_line / write_png_metadata).
After changing the format - or the viewer's annotation drawing - on
either side, run

    python3 fe_embed.py --selftest

next to flateyes.py — it round-trips every annotation kind through both
implementations and fails loudly on drift.
"""

import argparse
import array
import bisect
import itertools
import json
import math
import mmap
import os
import struct
import subprocess
import sys
import tempfile
import zlib

PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"
PNG_META_KEYWORD = b"flateyes"

# Mirrors the flateyes palette; colors also accept any #RRGGBB.
PALETTE = (("black", "#000000"), ("white", "#FFFFFF"),
           ("red", "#FF5040"), ("orange", "#FF9F1A"),
           ("green", "#3DDC55"), ("sky", "#35C5FF"),
           ("pink", "#FF4FD8"))
DEFAULT_LINE = "#FF5040"
DEFAULT_BG = "#000000"
TRANSLUCENT_ALPHA = 89   # flateyes' 0.35 backdrop/fill alpha
DASHES = {"solid": 0, "dashed": 1, "dotted": 2}

# Legend swatch styles (mirrors the flateyes tables, synonyms included).
LEGEND_BOX_STYLES = {"solid": "solid", "none": "none", "outline": "none",
                     "empty": "none", "clear": "none", "hatch": "hatch",
                     "cross": "cross", "crosshatch": "cross", "dots": "dots",
                     "dotted": "dots"}
LEGEND_LINE_STYLES = {"solid": "solid", "dash": "dashed", "dashed": "dashed",
                      "dot": "dotted", "dotted": "dotted"}

# floe fill patterns BY NAME (copy of floe's fillpatterns.def:
# 16 u16 rows as 64 hex chars, MSB = leftmost pixel). A box legend
# entry can name one of these instead of carrying a pat:HEX64
# bitmap; keep the table in sync with flateyes.py / floe when the
# .def re-bases. solid/clear resolve through LEGEND_BOX_STYLES.
FILL_PATTERNS = {
    "diagonal_right_wide":
        "0101020204040808101020204040808001010202040408081010202040408080",
    "diagonal_1":
        "1111222244448888111122224444888811112222444488881111222244448888",
    "diagonal_left_wide":
        "8080404020201010080804040202010180804040202010100808040402020101",
    "diagonal_2":
        "8888444422221111888844442222111188884444222211118888444422221111",
    "carets":
        "0000100028004400004400280010000000001000280044000044002800100000",
    "light_speckle":
        "8888000022220000888800002222000088880000222200008888000022220000",
    "speckle":
        "aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555",
    "alt_light_speckle":
        "2222555588885555222255558888555522225555888855552222555588885555",
    "alt_speckle":
        "5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa",
    "triangle_small":
        "00000000100038007c000000000000000000000000100038007c000000000000",
    "wave_small":
        "8888444422224444888844442222444488884444222244448888444422224444",
    "wave":
        "0808101020204040808040402020101008081010202040408080404020201010",
    "right_slope":
        "0003000c003000c003000c003000c0000003000c003000c003000c003000c000",
    "left_slope":
        "c00030000c00030000c00030000c0003c00030000c00030000c00030000c0003",
    "plus":
        "20002000f800200020000000000000000020002000f800200020000000000000",
    "brick":
        "ffff8000800080008000800080008000ffff0080008000800080008000800080",
    "circles":
        "10041004100408080808063001c00000000000000000000001c0063008080808",
    "carpet_1":
        "4444222211112282444488281111228244448828101128224444828811118888",
    "solid":
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "clear":
        "0000000000000000000000000000000000000000000000000000000000000000",
}


# ---------------------------------------------------------------------------
# annotation constructors — validated plain dicts, the same field layout
# flateyes uses internally
# ---------------------------------------------------------------------------

def _color(value, what="color"):
    """Palette name or #RRGGBB, normalized to #RRGGBB."""
    text = str(value).strip()
    for name, hex_ in PALETTE:
        if text.lower() == name:
            return hex_
    if text.startswith("#") and len(text) == 7:
        try:
            int(text[1:], 16)
            return text.upper()
        except ValueError:
            pass
    raise ValueError("bad %s: %s (use %s or #RRGGBB)"
                     % (what, value, "/".join(n for n, _ in PALETTE)))


def _fill_color(value):
    """A fill value: like _color, but "#RRGGBBAA" also works — the AA
    byte is the interior alpha.  Returns (color, alpha), alpha None
    when the value does not carry one."""
    text = str(value).strip()
    if text.startswith("#") and len(text) == 9:
        try:
            int(text[1:], 16)
            return text[:7], int(text[7:9], 16)
        except ValueError:
            pass
    return _color(text, "fill"), None


def _dash(value):
    if isinstance(value, str) and value.lower() in DASHES:
        return DASHES[value.lower()]
    if value in (0, 1, 2):
        return int(value)
    raise ValueError("dash must be solid/dashed/dotted (or 0/1/2), got: %r"
                     % (value,))


def _fill_pat(value):
    """A polygon-fill pattern token: a FILL_PATTERNS name (speckle,
    brick, ...) or a literal pat:HEX64 bitmap.  Returns the canonical
    lowercase token (mirror of flateyes.fill_pattern_token)."""
    tok = str(value).strip().lower()
    if tok in FILL_PATTERNS:
        return tok
    if tok.startswith("pat:"):
        hexs = tok[4:]
        if len(hexs) == 64 and all(c in "0123456789abcdef"
                                   for c in hexs):
            return tok
    raise ValueError("bad fill pattern: %s (use a floe fill name or "
                     "pat:HEX64)" % value)


def _shape(kind, x1, y1, x2, y2, color, fill, outline, width, dash,
           casing, fill_alpha=None):
    anno = {"kind": kind,
            "a": (float(x1), float(y1)), "b": (float(x2), float(y2)),
            "color": _color(color)}
    if not 1 <= int(width) <= 8:
        raise ValueError("width must be 1-8, got: %r" % (width,))
    anno["width"] = int(width)
    anno["dash"] = _dash(dash)
    if not casing:
        anno["casing"] = False
    if kind == "line":
        return anno
    if fill_alpha is not None:
        try:
            fill_alpha = int(fill_alpha)
        except (TypeError, ValueError):
            fill_alpha = -1
        if not 0 <= fill_alpha <= 255:
            raise ValueError("fill_alpha must be 0-255")
    if fill is not None:
        # "#RRGGBBAA" carries the alpha in the value; an explicit
        # fill_alpha wins over it
        anno["fill"], embedded = _fill_color(fill)
        anno["fill_alpha"] = fill_alpha if fill_alpha is not None \
            else (TRANSLUCENT_ALPHA if embedded is None else embedded)
    if not outline:
        if fill is None:
            raise ValueError("outline=False needs a fill")
        anno["outline"] = False
    return anno


def box(x1, y1, x2, y2, color=DEFAULT_LINE, fill=None, outline=True,
        width=1, dash="solid", casing=True, fill_alpha=None):
    """Rectangle from (x1,y1) to (x2,y2) in center-origin image px."""
    return _shape("box", x1, y1, x2, y2, color, fill, outline,
                  width, dash, casing, fill_alpha)


def ellipse(x1, y1, x2, y2, color=DEFAULT_LINE, fill=None, outline=True,
            width=1, dash="solid", casing=True, fill_alpha=None):
    """Ellipse inscribed in the (x1,y1)-(x2,y2) rectangle."""
    return _shape("ellipse", x1, y1, x2, y2, color, fill, outline,
                  width, dash, casing, fill_alpha)


def line(x1, y1, x2, y2, color=DEFAULT_LINE, width=1, dash="solid",
         casing=True):
    """Straight line segment."""
    return _shape("line", x1, y1, x2, y2, color, None, True,
                  width, dash, casing)


def path(points, color=DEFAULT_LINE, width=1, dash="solid", casing=True):
    """Connected line segments through 2+ (x, y) points, in order."""
    pts = [(float(p[0]), float(p[1])) for p in points]
    if len(pts) < 2:
        raise ValueError("path needs 2+ points")
    if not 1 <= int(width) <= 8:
        raise ValueError("width must be 1-8, got: %r" % (width,))
    anno = {"kind": "path", "points": pts, "color": _color(color),
            "width": int(width), "dash": _dash(dash)}
    if not casing:
        anno["casing"] = False
    return anno


def polygon(points, color=DEFAULT_LINE, fill=None, outline=True, width=1,
            dash="solid", casing=True, fill_alpha=None, fill_pat=None):
    """Closed shape through 3+ (x, y) points, filled like a box.
    fill_pat (or a ":PATTERN" suffix on the fill value) names a floe
    fill pattern (speckle, brick, ... or pat:HEX64): the interior
    paints as OPAQUE pattern pixels - fill_alpha defaults to 255 -
    instead of a translucent wash."""
    pts = [(float(p[0]), float(p[1])) for p in points]
    if len(pts) < 3:
        raise ValueError("polygon needs 3+ points")
    if not 1 <= int(width) <= 8:
        raise ValueError("width must be 1-8, got: %r" % (width,))
    anno = {"kind": "polygon", "points": pts, "color": _color(color),
            "width": int(width), "dash": _dash(dash)}
    if not casing:
        anno["casing"] = False
    if fill_alpha is not None:
        try:
            fill_alpha = int(fill_alpha)
        except (TypeError, ValueError):
            fill_alpha = -1
        if not 0 <= fill_alpha <= 255:
            raise ValueError("fill_alpha must be 0-255")
    if fill is not None and ":" in str(fill):
        fill, tok = str(fill).split(":", 1)
        if fill_pat is None:
            fill_pat = tok
    if fill_pat is not None:
        if fill is None:
            raise ValueError("fill_pat needs a fill color")
        fill_pat = _fill_pat(fill_pat)
    if fill is not None:
        anno["fill"], embedded = _fill_color(fill)
        anno["fill_alpha"] = fill_alpha if fill_alpha is not None \
            else (((255 if fill_pat is not None else TRANSLUCENT_ALPHA))
                  if embedded is None else embedded)
        if fill_pat is not None:
            anno["fill_pat"] = fill_pat
    if not outline:
        if fill is None:
            raise ValueError("outline=False needs a fill")
        anno["outline"] = False
    return anno


def text(x, y, content, size=16, color=DEFAULT_LINE, bg=True,
         bg_color=DEFAULT_BG, bg_opaque=False):
    """Text note anchored at (x,y); "\\n" in content starts a new line."""
    content = str(content)
    if not content.strip():
        raise ValueError("empty text")
    if not 6 <= int(size) <= 96:
        raise ValueError("size must be 6-96, got: %r" % (size,))
    return {"kind": "text", "at": (float(x), float(y)), "text": content,
            "size": int(size), "color": _color(color), "bg": bool(bg),
            "bg_color": _color(bg_color, "bg_color"),
            "bg_opaque": bool(bg_opaque)}


def ruler(x1, y1, x2, y2):
    """Finished ruler measurement (labeled using the embedded ppu)."""
    return {"kind": "ruler", "a": (float(x1), float(y1)),
            "b": (float(x2), float(y2))}


# ---------------------------------------------------------------------------
# key=value serialization — must stay byte-identical to flateyes.py's
# serialize_anno / parse_anno_line
# ---------------------------------------------------------------------------

def escape_meta(value):
    return value.replace("\\", "\\\\").replace("\n", "\\n")


def unescape_meta(value):
    out, i = [], 0
    while i < len(value):
        if value[i] == "\\" and i + 1 < len(value):
            if value[i + 1] == "n":
                out.append("\n")
                i += 2
                continue
            if value[i + 1] == "\\":
                out.append("\\")
                i += 2
                continue
        out.append(value[i])
        i += 1
    return "".join(out)


def parse_legend_line(value):
    """One "kind COLOR [STYLE] LABEL..." legend definition line into an
    entry dict (port of the flateyes parser, color case preserved).
    The legend= metadata value uses the same grammar."""
    parts = value.split()
    kind = parts[0].lower() if parts else ""
    if kind not in ("box", "line"):
        raise ValueError("expected box or line, got: %s"
                         % (parts[0] if parts else "nothing"))
    if len(parts) < 2:
        raise ValueError("missing color")
    color = None
    for name, hex_ in PALETTE:
        if parts[1].lower() == name:
            color = hex_
    if color is None:
        if parts[1].startswith("#") and len(parts[1]) == 7:
            try:
                int(parts[1][1:], 16)
                color = parts[1]
            except ValueError:
                pass
    if color is None:
        raise ValueError("bad color: %s (use %s or #RRGGBB)"
                         % (parts[1], "/".join(n for n, _ in PALETTE)))
    styles = LEGEND_BOX_STYLES if kind == "box" else LEGEND_LINE_STYLES
    style = "solid"
    rest = parts[2:]
    if kind == "box" and rest and rest[0].lower().startswith("pat:"):
        # floe fill-pattern swatch: 16x16 bitmap as 16 u16 rows,
        # 4 hex chars each, MSB = leftmost pixel (the
        # fillpatterns.def convention)
        hexs = rest[0][4:].lower()
        if len(hexs) != 64 or any(c not in "0123456789abcdef"
                                  for c in hexs):
            raise ValueError("bad pat: style (need 64 hex chars = "
                             "16x16 bitmap, MSB left)")
        style = "pat:" + hexs
        rest = rest[1:]
    elif rest and rest[0].lower() in styles:
        style = styles[rest[0].lower()]
        rest = rest[1:]
    elif kind == "box" and rest and rest[0].lower() in FILL_PATTERNS:
        # floe fill pattern BY NAME (speckle, brick, ...): the name
        # itself is the style; the bitmap comes from FILL_PATTERNS
        style = rest[0].lower()
        rest = rest[1:]
    if not rest:
        raise ValueError("missing label")
    return {"kind": kind, "color": color, "style": style,
            "label": " ".join(rest)}


def serialize_legend(entry):
    """Canonical definition line (explicit style), the legend= value."""
    return "%s %s %s %s" % (entry["kind"], entry["color"],
                            entry["style"], entry["label"])


def legend_lines(legend):
    """Validate an iterable of legend definition lines into their
    canonical form; raises ValueError naming the offending line."""
    lines = []
    for index, line in enumerate(legend):
        try:
            lines.append(serialize_legend(parse_legend_line(str(line))))
        except ValueError as exc:
            raise ValueError("legend[%d]: %s" % (index, exc))
    return lines


def serialize_anno(anno):
    """One annotation dict as its key=value metadata line."""
    if anno["kind"] == "ruler":
        return ("ruler=%.10g,%.10g,%.10g,%.10g"
                % (anno["a"][0], anno["a"][1], anno["b"][0], anno["b"][1]))
    color = anno.get("color", DEFAULT_LINE)
    if anno["kind"] in ("path", "polygon"):
        # variable-length coordinate list, then the same style tail as
        # the fixed shapes (a path's fill slot stays a reserved "0";
        # a polygon fills like a box)
        if anno["kind"] == "polygon" and anno.get("fill"):
            fill = "%s%02X" % (anno["fill"],
                               anno.get("fill_alpha", TRANSLUCENT_ALPHA))
            if anno.get("fill_pat"):
                # ":PATTERN" rides inside the comma-free fill slot
                fill += ":" + anno["fill_pat"]
        else:
            fill = "0"
        if not anno.get("outline", True):
            color = "0"
        extra = ",%d,%d" % (anno.get("width", 1), anno.get("dash", 0))
        if not anno.get("casing", True):
            extra += ",0"
        return ("%s=%s,%s,%s%s"
                % (anno["kind"],
                   ",".join("%.10g,%.10g" % (p[0], p[1])
                            for p in anno["points"]), color, fill, extra))
    if anno["kind"] == "text":
        if anno.get("bg", True):
            backdrop = "%s%02X" % (anno.get("bg_color", DEFAULT_BG),
                                   255 if anno.get("bg_opaque")
                                   else TRANSLUCENT_ALPHA)
        else:
            backdrop = "0"
        return ("text=%.10g,%.10g,%d,%s,%s,%s"
                % (anno["at"][0], anno["at"][1], anno["size"], color,
                   backdrop, escape_meta(anno["text"])))
    if anno.get("fill"):
        # AA is the interior alpha verbatim (older builds read >= 80
        # as their opaque, anything else as their translucent 0.35)
        fill = "%s%02X" % (anno["fill"],
                           anno.get("fill_alpha", TRANSLUCENT_ALPHA))
    else:
        fill = "0"
    if not anno.get("outline", True):
        color = "0"
    extra = ",%d,%d" % (anno.get("width", 1), anno.get("dash", 0))
    if not anno.get("casing", True):
        extra += ",0"
    return ("%s=%.10g,%.10g,%.10g,%.10g,%s,%s%s"
            % (anno["kind"], anno["a"][0], anno["a"][1],
               anno["b"][0], anno["b"][1], color, fill, extra))


def serialize(annos, ppu=None, unit="um", note=None, legend=None):
    """The full chunk text, or None when there is nothing to store.
    note is one free text for the whole image (no position or style);
    flateyes shows it at the top-left with the info overlays.  legend
    is an iterable of definition lines ("box COLOR [STYLE] LABEL...");
    flateyes draws them as a swatch table at the bottom-right."""
    lines = []
    if ppu:
        if float(ppu) <= 0:
            raise ValueError("ppu must be > 0")
        lines.append("ppu=%.10g" % float(ppu))
        lines.append("unit=%s" % unit)
    if note and str(note).strip():
        lines.append("note=%s" % escape_meta(str(note).strip()))
    lines.extend("legend=%s" % line for line in legend_lines(legend or []))
    lines.extend(serialize_anno(anno) for anno in annos)
    if not lines:
        return None
    return "# flateyes annotations\n" + "\n".join(lines) + "\n"


def _parse_color(value):
    value = value.strip()
    if len(value) == 7 and value.startswith("#"):
        try:
            int(value[1:], 16)
            return value
        except ValueError:
            pass
    return DEFAULT_LINE


def parse_anno_line(key, value):
    """One key=value line back into an annotation dict (port of the
    flateyes loader, including its legacy-field tolerance)."""
    if key == "ruler":
        ax, ay, bx, by = value.split(",")[:4]
        return {"kind": "ruler", "a": (float(ax), float(ay)),
                "b": (float(bx), float(by))}
    if key in ("path", "polygon"):
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
        if len(coords) % 2 and coords and parts[index - 1].strip() == "0":
            # the numeric "0" no-outline sentinel in the color slot was
            # scanned as a coordinate; give it back
            coords.pop()
            index -= 1
        if len(coords) < (6 if key == "polygon" else 4) \
                or len(coords) % 2 or index >= len(parts):
            raise ValueError("bad %s: %s" % (key, value))
        anno = {"kind": key,
                "points": [(coords[i], coords[i + 1])
                           for i in range(0, len(coords), 2)],
                "color": _parse_color(parts[index])}
        if key == "polygon" and parts[index].strip() == "0":
            anno["outline"] = False
        tail = parts[index + 1:]   # fill, width, dash, halo (the fill
        if tail and key == "polygon":  # slot is "0" for paths)
            fill = tail[0].strip()
            pat = None
            if ":" in fill:   # "#RRGGBBAA:PATTERN" fill mask
                fill, pat = fill.split(":", 1)
            if fill.startswith("#") and len(fill) == 9:
                try:
                    int(fill[1:9], 16)
                except ValueError:
                    pass
                else:
                    anno["fill"] = fill[:7]
                    anno["fill_alpha"] = int(fill[7:9], 16)
                    if pat:
                        anno["fill_pat"] = _fill_pat(pat)
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
        x, y, size, color, bg, content = value.split(",", 5)
        content = unescape_meta(content)
        if not content:
            raise ValueError("empty text")
        bg = bg.strip()
        bg_color, bg_opaque = "#000000", False
        if bg.startswith("#") and len(bg) == 9:
            try:
                int(bg[1:9], 16)
                bg_color = bg[:7]
                bg_opaque = int(bg[7:9], 16) >= 0x80
            except ValueError:
                pass
        return {"kind": "text", "at": (float(x), float(y)),
                "text": content, "size": max(6, min(int(size), 96)),
                "color": _parse_color(color), "bg": bg != "0",
                "bg_color": bg_color, "bg_opaque": bg_opaque}
    parts = value.split(",")
    ax, ay, bx, by, color = parts[:5]
    anno = {"kind": key, "a": (float(ax), float(ay)),
            "b": (float(bx), float(by)), "color": _parse_color(color)}
    if color.strip() == "0" and key != "line":
        anno["outline"] = False
    fill = parts[5].strip() if len(parts) > 5 else "0"
    if fill.startswith("#") and len(fill) == 9:
        try:
            int(fill[1:9], 16)
            anno["fill"] = fill[:7]
            anno["fill_alpha"] = int(fill[7:9], 16)
        except ValueError:
            pass
    if len(parts) > 6:
        try:
            anno["width"] = max(1, min(int(float(parts[6])), 8))
            if len(parts) > 7:
                code = int(float(parts[7]))
                anno["dash"] = code if code in (1, 2) else 0
        except ValueError:
            pass
    if len(parts) > 8 and parts[8].strip() == "0":
        anno["casing"] = False
    return anno


def parse_metadata(text):
    """Chunk text -> (annotations, ppu, unit, note, legend); malformed
    lines skipped like flateyes does.  legend is a list of canonical
    definition lines (None when the chunk has none)."""
    annos, ppu, unit, note, legend = [], None, None, None, None
    for raw in (text or "").splitlines():
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        key, sep, value = stripped.partition("=")
        if not sep:
            continue
        try:
            if key == "ppu":
                if float(value) > 0:
                    ppu = float(value)
            elif key == "unit":
                if value.strip():
                    unit = value.strip()
            elif key == "note":
                if unescape_meta(value).strip():
                    note = unescape_meta(value).strip()
            elif key == "legend":
                line = serialize_legend(parse_legend_line(value))
                legend = (legend or []) + [line]
            elif key in ("box", "ellipse", "line", "path", "polygon",
                         "ruler", "text"):
                annos.append(parse_anno_line(key, value))
        except ValueError:
            continue
    return annos, ppu, unit, note, legend


# ---------------------------------------------------------------------------
# png chunk layer — same iTXt handling as flateyes.py
# ---------------------------------------------------------------------------

def _parse_itxt(body):
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


def extract_text(blob):
    """Embedded flateyes metadata text from PNG bytes, or None."""
    if not blob.startswith(PNG_SIGNATURE):
        raise ValueError("not a PNG")
    pos = len(PNG_SIGNATURE)
    while pos + 8 <= len(blob):
        length, ctype = struct.unpack(">I4s", blob[pos:pos + 8])
        end = pos + 8 + length + 4
        if ctype == b"IEND" or end > len(blob):
            return None
        if ctype == b"iTXt":
            text = _parse_itxt(blob[pos + 8:end - 4])
            if text is not None:
                return text
        pos = end
    return None


def insert_text(blob, text):
    """PNG bytes with our iTXt chunk inserted before IEND (a previous
    flateyes chunk is dropped; text=None just removes it).  Pixel
    chunks are copied verbatim."""
    if not blob.startswith(PNG_SIGNATURE):
        raise ValueError("not a PNG")
    out = [PNG_SIGNATURE]
    pos = len(PNG_SIGNATURE)
    while pos + 8 <= len(blob):
        length, ctype = struct.unpack(">I4s", blob[pos:pos + 8])
        end = pos + 8 + length + 4
        if end > len(blob):
            raise ValueError("truncated PNG")
        if ctype == b"iTXt" \
                and _parse_itxt(blob[pos + 8:end - 4]) is not None:
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
            return b"".join(out)
        out.append(blob[pos:end])
        pos = end
    raise ValueError("no IEND chunk")


def _combine(existing, annos, ppu, unit, note, legend):
    """Chunk text for append mode: keep the lines already embedded, but
    a newly given ppu replaces the stored ppu/unit pair, and a newly
    given note/legend replaces the stored one."""
    kept = []
    for raw in (existing or "").splitlines():
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if ppu and (stripped.startswith("ppu=")
                    or stripped.startswith("unit=")):
            continue
        if note and stripped.startswith("note="):
            continue
        if legend and stripped.startswith("legend="):
            continue
        kept.append(stripped)
    fresh = (serialize(annos, ppu, unit, note, legend) or "").splitlines()[1:]
    head = (2 if ppu else 0) + (1 if note and str(note).strip() else 0) \
        + len(legend or [])
    lines = fresh[:head] + kept + fresh[head:]
    if not lines:
        return None
    return "# flateyes annotations\n" + "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# public entry points
# ---------------------------------------------------------------------------

def embed_bytes(blob, annos, ppu=None, unit="um", append=False, note=None,
                legend=None):
    """PNG bytes with the given annotations embedded.  With append=True
    they are added after any already-embedded ones; otherwise the chunk
    is replaced.  Empty input (and not appending) removes the chunk."""
    if append:
        text = _combine(extract_text(blob), annos, ppu, unit, note, legend)
    else:
        text = serialize(annos, ppu, unit, note, legend)
    return insert_text(blob, text)


def embed(path, annos, ppu=None, unit="um", append=False, note=None,
          legend=None):
    """Embed annotations into the PNG at path (atomic tmp + os.replace,
    so an interrupted write never corrupts the capture)."""
    with open(path, "rb") as handle:
        blob = handle.read()
    out = embed_bytes(blob, annos, ppu, unit, append, note, legend)
    folder = os.path.dirname(os.path.abspath(path))
    fd, tmp = tempfile.mkstemp(prefix=".fe-embed-", dir=folder)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(out)
        os.chmod(tmp, os.stat(path).st_mode & 0o7777)
        os.replace(tmp, path)
    except OSError:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def read_bytes(blob):
    """(annotations, ppu, unit, note, legend) embedded in PNG bytes."""
    return parse_metadata(extract_text(blob))


def read(path):
    """(annotations, ppu, unit, note, legend) embedded in the PNG at
    path."""
    with open(path, "rb") as handle:
        return read_bytes(handle.read())


def strip(path):
    """Remove the embedded metadata chunk, if any."""
    embed(path, [])


# ---------------------------------------------------------------------------
# export, part 1: png pixels - any PNG decoded to 8-bit RGBA and written
# back, pure python (zlib + struct)
# ---------------------------------------------------------------------------

_PNG_CHANNELS = {0: 1, 2: 3, 3: 1, 4: 2, 6: 4}
_PNG_DEPTHS = {0: (1, 2, 4, 8, 16), 2: (8, 16), 3: (1, 2, 4, 8),
               4: (8, 16), 6: (8, 16)}
_ADAM7 = ((0, 0, 8, 8), (4, 0, 8, 8), (0, 4, 4, 8), (2, 0, 4, 4),
          (0, 2, 2, 4), (1, 0, 2, 2), (0, 1, 1, 2))
# Ancillary chunks that stay true when the pixels change (color space,
# physical pixel size); copied into the export.
_PNG_KEEP = (b"gAMA", b"cHRM", b"sRGB", b"iCCP", b"pHYs")
_SUM_CODE = "I" if array.array("I").itemsize == 4 else "L"
_SUM_SIZE = array.array(_SUM_CODE).itemsize
_SUM_LOW = 0 if sys.byteorder == "little" else _SUM_SIZE - 1
_SWAR_MASKS = {}
# filter-choice heuristic: residuals within +-2 count as "small"
_SMALL_RESIDUAL = bytes(1 if v <= 2 or v >= 254 else 0 for v in range(256))


def _swar_masks(n):
    masks = _SWAR_MASKS.get(n)
    if masks is None:
        if len(_SWAR_MASKS) > 64:
            _SWAR_MASKS.clear()
        masks = _SWAR_MASKS[n] = (int.from_bytes(b"\x80" * n, "big"),
                                  int.from_bytes(b"\x7f" * n, "big"))
    return masks


def _bytes_add(a, b):
    """(a + b) mod 256 per byte in a few big-int operations instead of
    a Python loop: the low 7 bits add without crossing a byte, the top
    bits are XORed back in."""
    n = len(a)
    hi, lo = _swar_masks(n)
    x = int.from_bytes(a, "big")
    y = int.from_bytes(b, "big")
    return (((x & lo) + (y & lo)) ^ ((x ^ y) & hi)).to_bytes(n, "big")


def _bytes_sub(a, b):
    """(a - b) mod 256 per byte, same trick: the borrows stop at each
    byte's forced top bit."""
    n = len(a)
    hi, lo = _swar_masks(n)
    x = int.from_bytes(a, "big")
    y = int.from_bytes(b, "big")
    return (((x | hi) - (y & lo)) ^ ((x ^ ~y) & hi)).to_bytes(n, "big")


def _unsub(line, bpp):
    """Undo the Sub filter: each channel lane is a running sum, taken
    mod 256 by keeping the low byte of every 32-bit total (all C-level
    loops: accumulate, array, slicing)."""
    out = bytearray(len(line))
    for lane in range(bpp):
        sums = array.array(_SUM_CODE, itertools.accumulate(line[lane::bpp]))
        out[lane::bpp] = sums.tobytes()[_SUM_LOW::_SUM_SIZE]
    return out


def _unavg(line, prev, bpp):
    cur = bytearray(line)
    for i in range(min(bpp, len(cur))):
        cur[i] = (cur[i] + (prev[i] >> 1)) & 0xFF
    for i in range(bpp, len(cur)):
        cur[i] = (cur[i] + ((cur[i - bpp] + prev[i]) >> 1)) & 0xFF
    return cur


def _unpaeth(line, prev, bpp):
    if not prev.strip(b"\x00"):
        return _unsub(line, bpp)  # above the first row Paeth is Sub
    cur = bytearray(line)
    for i in range(min(bpp, len(cur))):
        cur[i] = (cur[i] + prev[i]) & 0xFF
    for i in range(bpp, len(cur)):
        a = cur[i - bpp]
        b = prev[i]
        c = prev[i - bpp]
        pa = b - c
        pb = a - c
        pc = pa + pb
        if pa < 0:
            pa = -pa
        if pb < 0:
            pb = -pb
        if pc < 0:
            pc = -pc
        if pa <= pb and pa <= pc:
            cur[i] = (cur[i] + a) & 0xFF
        elif pb <= pc:
            cur[i] = (cur[i] + b) & 0xFF
        else:
            cur[i] = (cur[i] + c) & 0xFF
    return cur


def _unfilter(raw, pos, rowbytes, height, bpp):
    """Reconstruct height filtered scanlines starting at raw[pos];
    returns (the rows back to back, position after them)."""
    out = bytearray(rowbytes * height)
    prev = bytes(rowbytes)
    for y in range(height):
        if pos + 1 + rowbytes > len(raw):
            raise ValueError("truncated image data")
        kind = raw[pos]
        line = raw[pos + 1:pos + 1 + rowbytes]
        pos += 1 + rowbytes
        if kind == 0:
            cur = line
        elif kind == 1:
            cur = _unsub(line, bpp)
        elif kind == 2:
            cur = _bytes_add(line, prev)
        elif kind == 3:
            cur = _unavg(line, prev, bpp)
        elif kind == 4:
            cur = _unpaeth(line, prev, bpp)
        else:
            raise ValueError("bad PNG filter type %d" % kind)
        out[y * rowbytes:(y + 1) * rowbytes] = cur
        prev = cur
    return out, pos


def _unpack_bits(rows, width, height, depth):
    """1/2/4-bit samples, one per byte (rows are byte-padded)."""
    per = 8 // depth
    mask = (1 << depth) - 1
    spread = bytearray(len(rows) * per)
    for k in range(per):
        shift = 8 - depth * (k + 1)
        spread[k::per] = rows.translate(
            bytes((v >> shift) & mask for v in range(256)))
    stride = (width * depth + 7) // 8 * per
    if stride == width:
        return spread
    return bytearray().join(spread[y * stride:y * stride + width]
                            for y in range(height))


def _key_alpha(planes, n):
    """tRNS color key: alpha 0 where every (plane, key byte) matches,
    255 elsewhere - per-byte tests as translate tables, ANDed as big
    ints."""
    mask = None
    for plane, key in planes:
        if not 0 <= key <= 255:
            return b"\xff" * n
        hit = int.from_bytes(plane.translate(
            bytes(1 if v == key else 0 for v in range(256))), "big")
        mask = hit if mask is None else mask & hit
    return mask.to_bytes(n, "big").translate(
        b"\xff" + b"\x00" + b"\xff" * 254)


def _png_rgba(rows, width, height, color, depth, plte, trns):
    """Unfiltered rows of one (sub)image -> 8-bit RGBA."""
    n = width * height
    out = bytearray(n * 4)
    if depth < 8:
        samples = _unpack_bits(rows, width, height, depth)
    elif depth == 16:
        samples = rows[0::2]   # high bytes, every sample in order
    else:
        samples = rows
    if color == 3:
        pal = bytes(plte[:768]) + bytes(768 - min(len(plte), 768))
        for k in range(3):
            out[k::4] = samples.translate(pal[k::3])
        alphas = bytes(trns[:256]) if trns else b""
        out[3::4] = samples.translate(alphas + b"\xff" * (256 - len(alphas)))
        return out
    ch = _PNG_CHANNELS[color]
    if color in (0, 4):
        gray = samples[0::ch] if ch > 1 else samples
        if depth < 8:
            gray = gray.translate(bytes(
                min(255, v * 255 // ((1 << depth) - 1)) for v in range(256)))
        for k in range(3):
            out[k::4] = gray
    else:
        for k in range(3):
            out[k::4] = samples[k::ch]
    if color in (4, 6):
        out[3::4] = samples[ch - 1::ch]
    elif trns is not None and len(trns) >= (2 if color == 0 else 6):
        keys = struct.unpack(">%dH" % (1 if color == 0 else 3),
                             trns[:2 if color == 0 else 6])
        if depth == 16:
            planes = []
            for k, key in enumerate(keys):
                planes.append((rows[2 * k::2 * len(keys)], key >> 8))
                planes.append((rows[2 * k + 1::2 * len(keys)], key & 0xFF))
        elif depth < 8:
            planes = [(samples, keys[0])]
        else:
            planes = [(samples[k::len(keys)], key)
                      for k, key in enumerate(keys)]
        out[3::4] = _key_alpha(planes, n)
    else:
        out[3::4] = b"\xff" * n
    return out


def _png_chunks(blob):
    if not blob.startswith(PNG_SIGNATURE):
        raise ValueError("not a PNG")
    pos = len(PNG_SIGNATURE)
    while pos + 8 <= len(blob):
        length, ctype = struct.unpack(">I4s", blob[pos:pos + 8])
        end = pos + 12 + length
        if end > len(blob):
            raise ValueError("truncated PNG")
        yield ctype, blob[pos + 8:end - 4]
        if ctype == b"IEND":
            return
        pos = end
    raise ValueError("no IEND chunk")


def _png_decode(blob):
    """PNG bytes -> (width, height, RGBA bytearray, has alpha, chunks
    worth keeping).  Every color type, bit depth and Adam7 interlace;
    16-bit samples keep their high byte."""
    ihdr = plte = trns = None
    idat = []
    keep = []
    for ctype, body in _png_chunks(blob):
        if ctype == b"IHDR":
            ihdr = body
        elif ctype == b"PLTE":
            plte = body
        elif ctype == b"tRNS":
            trns = body
        elif ctype == b"IDAT":
            idat.append(body)
        elif ctype in _PNG_KEEP:
            keep.append((ctype, body))
    if ihdr is None or len(ihdr) != 13 or not idat:
        raise ValueError("no image data")
    width, height, depth, color, method, filt, interlace = \
        struct.unpack(">IIBBBBB", ihdr)
    if depth not in _PNG_DEPTHS.get(color, ()) or method or filt \
            or interlace > 1 or not width or not height \
            or (color == 3 and not plte):
        raise ValueError("unsupported PNG (color type %d, %d bit)"
                         % (color, depth))
    try:
        raw = zlib.decompress(b"".join(idat))
    except zlib.error as exc:
        raise ValueError("corrupt image data (%s)" % exc)
    bits = _PNG_CHANNELS[color] * depth
    bpp = max(1, bits // 8)
    if not interlace:
        rows, _ = _unfilter(raw, 0, (width * bits + 7) // 8, height, bpp)
        rgba = _png_rgba(rows, width, height, color, depth, plte, trns)
    else:
        rgba = bytearray(width * height * 4)
        pos = 0
        for x0, y0, dx, dy in _ADAM7:
            pw = (width - x0 + dx - 1) // dx
            ph = (height - y0 + dy - 1) // dy
            if pw <= 0 or ph <= 0:
                continue
            rows, pos = _unfilter(raw, pos, (pw * bits + 7) // 8, ph, bpp)
            sub = _png_rgba(rows, pw, ph, color, depth, plte, trns)
            for j in range(ph):
                start = ((y0 + j * dy) * width + x0) * 4
                line = sub[j * pw * 4:(j + 1) * pw * 4]
                for k in range(4):
                    rgba[start + k:start + k + (pw - 1) * dx * 4 + 1:
                         dx * 4] = line[k::4]
    if color in (0, 4):   # a gray ICC profile cannot describe RGB output
        keep = [(t, b) for t, b in keep if t != b"iCCP"]
    alpha = color in (4, 6) or trns is not None
    return width, height, rgba, alpha, keep


def _png_chunk(ctype, body):
    return (struct.pack(">I", len(body)) + ctype + body
            + struct.pack(">I", zlib.crc32(ctype + body) & 0xFFFFFFFF))


def _png_encode(width, height, rgba, alpha, chunks=(), level=6):
    """8-bit RGBA -> PNG bytes (RGB when alpha is False).  Each row
    takes whichever of None/Sub/Up leaves the most near-zero bytes -
    a cheap stand-in for libpng's heuristic (Avg/Paeth would need a
    Python loop per byte)."""
    if alpha:
        data, bpp, color = rgba, 4, 6
    else:
        data = bytearray(width * height * 3)
        for k in range(3):
            data[k::3] = rgba[k::4]
        bpp, color = 3, 2
    stride = width * bpp
    lead = bytes(bpp)
    prev = bytes(stride)
    parts = []
    for y in range(height):
        line = bytes(data[y * stride:(y + 1) * stride])
        options = (line, _bytes_sub(line, lead + line[:-bpp]),
                   _bytes_sub(line, prev))
        scores = [o.translate(_SMALL_RESIDUAL).count(1) for o in options]
        kind = scores.index(max(scores))
        parts.append(b"\x00\x01\x02"[kind:kind + 1])
        parts.append(options[kind])
        prev = line
    out = [PNG_SIGNATURE,
           _png_chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8,
                                           color, 0, 0, 0))]
    for ctype, body in chunks:
        out.append(_png_chunk(ctype, body))
    out.append(_png_chunk(b"IDAT", zlib.compress(b"".join(parts), level)))
    out.append(_png_chunk(b"IEND", b""))
    return b"".join(out)


# ---------------------------------------------------------------------------
# export, part 2: painting - the flateyes overlay look, in image pixels
# ---------------------------------------------------------------------------

DPI_SCALE = 96 / 72.0       # Pango points -> pixels (96 dpi screens)
UI_PT = 11                  # GTK's default UI font size (Cantarell 11)
ANNO_CASING = b"\x00\x00\x00\xa0"    # Viewer.ANNO_CASING
RULER_CORE = b"\xff\xff\xff\xff"     # Viewer.RULER_CORE: plain white
CHIP_TEXT = (0xF0, 0xF0, 0xF0)       # #flateyes-status / legend labels
EXPORT_HIDE = ("shapes", "texts", "rulers", "note", "legend")


def _rgba(hex_color, alpha=255):
    """"#RRGGBB" + alpha -> the 4-byte pixel."""
    return bytes((int(hex_color[1:3], 16), int(hex_color[3:5], 16),
                  int(hex_color[5:7], 16), alpha))


class _Canvas(object):
    """8-bit RGBA pixels being painted.  opaque: every alpha is 255,
    which lets blends run as C-level translate() over whole spans."""

    def __init__(self, width, height, rgba, opaque):
        self.width, self.height = width, height
        self.rgba = rgba
        self.opaque = opaque


_BLEND_TABLES = {}


def _blend_table(c, a):
    """translate() table: color channel value c at alpha a over every
    possible destination value."""
    key = (c << 8) | a
    table = _BLEND_TABLES.get(key)
    if table is None:
        if len(_BLEND_TABLES) > 4096:
            _BLEND_TABLES.clear()
        ia = 255 - a
        table = _BLEND_TABLES[key] = bytes((c * a + d * ia + 127) // 255
                                           for d in range(256))
    return table


def _blend_pixel(buf, p, r, g, b, a):
    """Source-over of one non-premultiplied pixel, destination alpha
    honored (transparent sources/panels)."""
    da = buf[p + 3]
    if da == 255 or a == 255:
        ia = 255 - a
        buf[p] = (r * a + buf[p] * ia + 127) // 255
        buf[p + 1] = (g * a + buf[p + 1] * ia + 127) // 255
        buf[p + 2] = (b * a + buf[p + 2] * ia + 127) // 255
        if a == 255:
            buf[p + 3] = 255
        return
    sa = a / 255.0
    rest = da / 255.0 * (1.0 - sa)
    oa = sa + rest
    if oa <= 0:
        return
    buf[p] = int((r * sa + buf[p] * rest) / oa + 0.5)
    buf[p + 1] = int((g * sa + buf[p + 1] * rest) / oa + 0.5)
    buf[p + 2] = int((b * sa + buf[p + 2] * rest) / oa + 0.5)
    buf[p + 3] = int(oa * 255 + 0.5)


def _blend_span(cv, y, x0, x1, rgba):
    """Paint rgba over row y, columns x0..x1 (already clipped)."""
    a = rgba[3]
    if not a or x1 <= x0:
        return
    buf = cv.rgba
    p0 = (y * cv.width + x0) * 4
    p1 = p0 + (x1 - x0) * 4
    if a == 255:
        buf[p0:p1] = rgba * (x1 - x0)
    elif cv.opaque:
        for k in range(3):
            buf[p0 + k:p1:4] = buf[p0 + k:p1:4].translate(
                _blend_table(rgba[k], a))
    else:
        r, g, b = rgba[0], rgba[1], rgba[2]
        for p in range(p0, p1, 4):
            _blend_pixel(buf, p, r, g, b, a)


def _blend_rect(cv, x, y, w, h, rgba, clip):
    x0, y0 = max(x, clip[0]), max(y, clip[1])
    x1, y1 = min(x + w, clip[2]), min(y + h, clip[3])
    for row in range(y0, y1):
        _blend_span(cv, row, x0, x1, rgba)


def _blend_round_rect(cv, x, y, w, h, radius, rgba, clip):
    """A CSS border-radius backdrop: straight spans plus anti-aliased
    corner pixels (4x4 supersampled quarter circles)."""
    r = max(0, min(radius, w // 2, h // 2))
    x0, x1 = max(x, clip[0]), min(x + w, clip[2])
    if x0 >= x1:
        return
    edge = []   # per corner column: coverage 0-255 for each corner row
    for row in range(r):
        covs = []
        for col in range(r):
            hits = 0
            for sy in (0.125, 0.375, 0.625, 0.875):
                for sx in (0.125, 0.375, 0.625, 0.875):
                    dx, dy = r - (col + sx), r - (row + sy)
                    if dx * dx + dy * dy <= r * r:
                        hits += 1
            covs.append(hits * 255 // 16)
        edge.append(covs)
    a = rgba[3]
    for row in range(max(y, clip[1]), min(y + h, clip[3])):
        k = row - y
        corner = k if k < r else (h - 1 - k if k >= h - r else None)
        if corner is None:
            _blend_span(cv, row, x0, x1, rgba)
            continue
        covs = edge[corner]
        _blend_span(cv, row, max(x0, x + r), min(x1, x + w - r), rgba)
        for col in range(r):
            alpha = a * covs[col] // 255
            if not alpha:
                continue
            tint = rgba[:3] + bytes((alpha,))
            for px in (x + col, x + w - 1 - col):
                if x0 <= px < x1:
                    _blend_span(cv, row, px, px + 1, tint)


def _blend_mask(cv, x, y, w, h, cov, rgb, alpha, clip):
    """A glyph's coverage bitmap in color rgb at alpha, over the canvas."""
    x0, y0 = max(x, clip[0]), max(y, clip[1])
    x1, y1 = min(x + w, clip[2]), min(y + h, clip[3])
    if x0 >= x1 or y0 >= y1:
        return
    r, g, b = rgb
    buf, stride, opaque = cv.rgba, cv.width, cv.opaque
    for row in range(y0, y1):
        src = (row - y) * w - x
        p = (row * stride + x0) * 4
        for col in range(x0, x1):
            c = cov[src + col]
            if c:
                a = c if alpha == 255 else c * alpha // 255
                if not opaque:
                    _blend_pixel(buf, p, r, g, b, a)
                elif a == 255:
                    buf[p] = r
                    buf[p + 1] = g
                    buf[p + 2] = b
                else:
                    ia = 255 - a
                    buf[p] = (r * a + buf[p] * ia + 127) // 255
                    buf[p + 1] = (g * a + buf[p + 1] * ia + 127) // 255
                    buf[p + 2] = (b * a + buf[p + 2] * ia + 127) // 255
            p += 4


class _Layer(object):
    """The viewer's overlay pixbuf: a transparent RGBA plane over the
    image whose fills REPLACE pixels (GdkPixbuf.fill() on a
    subpixbuf), so translucent shapes never stack among themselves;
    composited over the image once, the way GTK lays the overlay
    widget over the picture.  Rows are allocated when first painted."""

    def __init__(self, width, height):
        self.width, self.height = width, height
        self.rows = [None] * height
        self.spans = [None] * height   # [x0, x1) painted per row

    def _row(self, y, x0, x1):
        row = self.rows[y]
        if row is None:
            row = self.rows[y] = bytearray(self.width * 4)
            self.spans[y] = [x0, x1]
        else:
            span = self.spans[y]
            if x0 < span[0]:
                span[0] = x0
            if x1 > span[1]:
                span[1] = x1
        return row

    def fill_rect(self, x, y, w, h, rgba):
        """Viewer.fill_rect: round, clip, replace."""
        x, y = int(round(x)), int(round(y))
        w, h = int(round(w)), int(round(h))
        if x < 0:
            w += x
            x = 0
        if y < 0:
            h += y
            y = 0
        w = min(w, self.width - x)
        h = min(h, self.height - y)
        if w <= 0 or h <= 0:
            return
        run = rgba * w
        for row in range(y, y + h):
            self._row(row, x, x + w)[x * 4:(x + w) * 4] = run

    def blend(self, x, y, rgba):
        """GdkPixbuf.composite of one pixel (the fill-pattern strips)."""
        if rgba[3] == 255:
            self._row(y, x, x + 1)[x * 4:x * 4 + 4] = rgba
        elif rgba[3]:
            _blend_pixel(self._row(y, x, x + 1), x * 4,
                         rgba[0], rgba[1], rgba[2], rgba[3])

    def composite(self, cv):
        """Lay the plane over the canvas, run by run of equal pixels."""
        for y in range(self.height):
            row = self.rows[y]
            if row is None:
                continue
            x0, x1 = self.spans[y]
            p, end = x0 * 4, x1 * 4
            while p < end:
                pixel = row[p:p + 4]
                q = p + 4
                step = 1
                while q < end:   # gallop over the run of this pixel
                    n = min(step, (end - q) // 4)
                    if row[q:q + 4 * n] == pixel * n:
                        q += 4 * n
                        step *= 2
                    elif step > 1:
                        step = 1
                    else:
                        break
                if pixel[3]:
                    _blend_span(cv, y, p // 4, q // 4, bytes(pixel))
                p = q


def _clip_segment(a, b, width, height, pad=4):
    """Viewer.clip_segment (Liang-Barsky); None when outside."""
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


def _pattern_rows(token):
    hexs = token[4:] if token.startswith("pat:") else FILL_PATTERNS[token]
    return [int(hexs[i * 4:i * 4 + 4], 16) for i in range(16)]


def _ellipse_dabs(cx, cy, rx, ry, buf_w, buf_h, margin, dash, on, period):
    """Viewer.ellipse_dabs: dab centers ~1px apart along an ellipse
    outline near the buffer, dashed by arc length; past 8000 samples
    the perimeter goes in 64-sample blocks, each starting its dash count
    at the sum of the block chords before it."""
    steps = max(int(6.4 * max(rx, ry)), 16)
    block = steps if steps <= 8000 else 64
    points = []
    base = 0.0
    for lo in range(0, steps, block):
        hi = min(lo + block, steps)
        t0, t1 = 2 * math.pi * lo / steps, 2 * math.pi * hi / steps
        ax, ay = cx + rx * math.cos(t0), cy + ry * math.sin(t0)
        bx, by = cx + rx * math.cos(t1), cy + ry * math.sin(t1)
        chord = math.hypot(bx - ax, by - ay)
        pad = chord + margin
        if block < steps and (
                max(ax, bx) < -pad or min(ax, bx) > buf_w + pad
                or max(ay, by) < -pad or min(ay, by) > buf_h + pad):
            base += chord
            continue
        cum = base
        prev = None
        for i in range(lo, hi):
            x = cx + rx * math.cos(2 * math.pi * i / steps)
            y = cy + ry * math.sin(2 * math.pi * i / steps)
            if prev is not None:
                cum += math.hypot(x - prev[0], y - prev[1])
            prev = (x, y)
            if dash and cum % period >= on:
                continue
            if -margin <= x <= buf_w + margin \
                    and -margin <= y <= buf_h + margin:
                points.append((x, y))
        base += chord
    return points


class _Painter(object):
    """flateyes' stamp_annotation and helpers, ported onto a _Layer in
    image pixels.  s=1 reproduces the viewer at 100% zoom; s=2 draws
    every stroke, dash, arrowhead and pattern twice as big (what the
    viewer shows at 50%, at full image resolution)."""

    def __init__(self, layer, s=1.0):
        self.layer = layer
        self.s = s
        self.one = max(1, int(round(s)))   # the viewer's 1px

    def stroke(self, width):
        return max(1, int(round(width * self.s)))

    def segment(self, a, b, casing, core, width=1, dash=0):
        """Viewer.stamp_segment: width in viewer px, dash 0 solid /
        1 dashed / 2 dotted, casing or core None skips that pass; the
        dash phase is anchored at a."""
        layer, one = self.layer, self.one
        w = self.stroke(width)
        ax, ay = a
        bx, by = b
        if dash == 0 and ay == by:     # horizontal, solid: flat rects
            y0 = ay - w // 2
            if casing is not None:
                layer.fill_rect(min(ax, bx), y0 - one, abs(bx - ax) + 1,
                                w + 2 * one, casing)
            if core is not None:
                layer.fill_rect(min(ax, bx), y0, abs(bx - ax) + 1, w, core)
            return
        if dash == 0 and ax == bx:     # vertical, solid
            x0 = ax - w // 2
            if casing is not None:
                layer.fill_rect(x0 - one, min(ay, by), w + 2 * one,
                                abs(by - ay) + 1, casing)
            if core is not None:
                layer.fill_rect(x0, min(ay, by), w, abs(by - ay) + 1, core)
            return
        seg = _clip_segment(a, b, layer.width, layer.height, w + 4 * one)
        if seg is None:
            return
        (sx, sy), (ex, ey) = seg
        steps = int(max(abs(ex - sx), abs(ey - sy))) + 1
        spacing = math.hypot(ex - sx, ey - sy) / steps
        base = math.hypot(sx - ax, sy - ay)   # clipped-away length
        if dash == 1:
            on, period = (3 * width + 3) * self.s, (5 * width + 6) * self.s
        elif dash == 2:
            on, period = self.s, (3 * width + 3) * self.s
        else:
            on = period = 1
        points = [(sx + (ex - sx) * i / steps, sy + (ey - sy) * i / steps)
                  for i in range(steps + 1)
                  if not dash or (base + i * spacing) % period < on]
        off = w // 2 + one
        if casing is not None:
            for x, y in points:
                layer.fill_rect(x - off, y - off, w + 2 * one, w + 2 * one,
                                casing)
        if core is not None:
            for x, y in points:
                layer.fill_rect(x - off, y - off, w + one, w + one, core)

    def arrow(self, tip, ang, rgba):
        """Viewer.stamp_arrow: solid triangle, tip first."""
        size, half = 11 * self.s, 4 * self.s
        ux, uy = math.cos(ang), math.sin(ang)
        bx, by = tip[0] - size * ux, tip[1] - size * uy
        self.polygon([tip, (bx - half * uy, by + half * ux),
                      (bx + half * uy, by - half * ux)], rgba)

    def _spans(self, pts):
        """Even-odd scanline crossings per row (Viewer.fill_polygon)."""
        top = max(int(min(p[1] for p in pts)), 0)
        bottom = min(int(max(p[1] for p in pts)) + 1, self.layer.height)
        edges = list(zip(pts, pts[1:] + pts[:1]))
        for row in range(top, bottom):
            yc = row + 0.5   # half-open rule: vertices count once
            xs = []
            for (x1, y1), (x2, y2) in edges:
                if (y1 <= yc < y2) or (y2 <= yc < y1):
                    xs.append(x1 + (yc - y1) * (x2 - x1) / (y2 - y1))
            xs.sort()
            for i in range(0, len(xs) - 1, 2):
                yield row, xs[i], xs[i + 1]

    def polygon(self, pts, rgba):
        for row, xa, xb in self._spans(pts):
            self.layer.fill_rect(xa, row, xb - xa, 1, rgba)

    def polygon_pat(self, pts, rgba, pat):
        """Viewer.fill_polygon_pat: on-bits of the 16x16 floe pattern
        paint rgba, off-bits leave the image; anchored at the image's
        top-left, one bit per s pixels."""
        rows = _pattern_rows(pat)
        layer, s = self.layer, self.s
        for row, xa, xb in self._spans(pts):
            bits = rows[int(row / s) % 16]
            for x in range(max(int(round(xa)), 0),
                           min(int(round(xb)), layer.width)):
                if (bits >> (15 - int(x / s) % 16)) & 1:
                    layer.blend(x, row, rgba)

    def shape(self, shape, cx, cy):
        """Viewer.stamp_annotation (no highlight) for one annotation in
        world coordinates; (cx, cy) is the image center."""
        kind = shape["kind"]
        layer = self.layer
        if kind in ("path", "polygon"):
            pts = [(p[0] + cx, p[1] + cy) for p in shape["points"]]
            core = _rgba(shape["color"])
            casing = ANNO_CASING if shape.get("casing", True) else None
            width = shape.get("width", 1)
            dash = shape.get("dash", 0)
            if kind == "polygon":
                if shape.get("fill") and len(pts) >= 3:
                    fill = _rgba(shape["fill"], shape.get("fill_alpha", 0x59))
                    if shape.get("fill_pat"):
                        self.polygon_pat(pts, fill, shape["fill_pat"])
                    else:
                        self.polygon(pts, fill)
                if not shape.get("outline", True):
                    return
                segments = list(zip(pts, pts[1:] + pts[:1]))
            else:
                segments = list(zip(pts, pts[1:]))
            if casing is not None:
                for sa, sb in segments:
                    self.segment(sa, sb, casing, None, width, dash)
            for sa, sb in segments:
                self.segment(sa, sb, None, core, width, dash)
            return
        a = (shape["a"][0] + cx, shape["a"][1] + cy)
        b = (shape["b"][0] + cx, shape["b"][1] + cy)
        if kind == "ruler":
            self.segment(a, b, None, RULER_CORE)
            if a != b:   # outward arrowheads at both ends (floe's look)
                ang = math.atan2(b[1] - a[1], b[0] - a[0])
                self.arrow(b, ang, RULER_CORE)
                self.arrow(a, ang + math.pi, RULER_CORE)
            else:
                layer.fill_rect(a[0] - 2 * self.s, a[1] - 2 * self.s,
                                5 * self.s, 5 * self.s, RULER_CORE)
            return
        core = _rgba(shape["color"])
        casing = ANNO_CASING if shape.get("casing", True) else None
        width = shape.get("width", 1)
        stroke_w = self.stroke(width)
        dash = shape.get("dash", 0)
        if kind == "line":
            self.segment(a, b, casing, core, width, dash)
            return
        x0, x1 = sorted((a[0], b[0]))
        y0, y1 = sorted((a[1], b[1]))
        fill = None
        if shape.get("fill"):
            fill = _rgba(shape["fill"], shape.get("fill_alpha", 0x59))
        outline = shape.get("outline", True)
        one = self.one
        if kind == "box":
            if fill is not None:
                layer.fill_rect(x0, y0, x1 - x0, y1 - y0, fill)
            if not outline:
                return
            if dash == 0:   # solid: flat rects with square corners
                for pass_w, rgba in ((stroke_w + 2 * one, casing),
                                     (stroke_w, core)):
                    if rgba is None:
                        continue
                    off = pass_w // 2
                    layer.fill_rect(x0 - off, y0 - off, x1 - x0 + pass_w,
                                    pass_w, rgba)
                    layer.fill_rect(x0 - off, y1 - off, x1 - x0 + pass_w,
                                    pass_w, rgba)
                    layer.fill_rect(x0 - off, y0 - off, pass_w,
                                    y1 - y0 + pass_w, rgba)
                    layer.fill_rect(x1 - off, y0 - off, pass_w,
                                    y1 - y0 + pass_w, rgba)
            else:
                corners = ((x0, y0), (x1, y0), (x1, y1), (x0, y1))
                edges = tuple(zip(corners, corners[1:] + corners[:1]))
                if casing is not None:
                    for ea, eb in edges:
                        self.segment(ea, eb, casing, None, width, dash)
                for ea, eb in edges:
                    self.segment(ea, eb, None, core, width, dash)
            return
        # ellipse: 1px-spaced dabs along the perimeter
        ecx, ecy = (x0 + x1) / 2.0, (y0 + y1) / 2.0
        rx, ry = (x1 - x0) / 2.0, (y1 - y0) / 2.0
        if fill is not None and rx >= 1 and ry >= 1:
            for row in range(max(int(ecy - ry) + 1, 0),
                             min(int(ecy + ry) + 1, layer.height)):
                offset = (row - ecy) / ry
                half = rx * math.sqrt(max(0.0, 1.0 - offset * offset))
                layer.fill_rect(ecx - half, row, 2 * half, 1, fill)
        if not outline:
            return
        if dash == 1:
            on, period = (3 * width + 3) * self.s, (5 * width + 6) * self.s
        elif dash == 2:
            on, period = self.s, (3 * width + 3) * self.s
        else:
            on = period = 1
        points = _ellipse_dabs(ecx, ecy, rx, ry, layer.width, layer.height,
                               3 * one + stroke_w, dash, on, period)
        off = stroke_w // 2 + one
        if casing is not None:
            for x, y in points:
                layer.fill_rect(x - off, y - off, stroke_w + 2 * one,
                                stroke_w + 2 * one, casing)
        for x, y in points:
            layer.fill_rect(x - off, y - off, stroke_w + one,
                            stroke_w + one, core)


# -- ruler readouts: Viewer.update_anno_overlay's label placement -------

def _trim_decimal(value, decimals):
    text = "%.*f" % (decimals, value)
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    return text


def _um_decimals(ppu):
    if ppu and ppu > 0:
        return min(6, max(2, int(math.ceil(math.log10(ppu)))))
    return 2


def format_distance(dist, ppu=None, unit="um"):
    """A ruler readout exactly as flateyes words it."""
    if ppu:
        return "%s %s  (%d px)" % (_trim_decimal(dist / ppu,
                                                 _um_decimals(ppu)),
                                   unit, round(dist))
    return "%d px" % round(dist)


def _rects_overlap(p, q):
    return p[0] < q[2] and p[2] > q[0] and p[1] < q[3] and p[3] > q[1]


def _avoid_label_overlap(x, y, w, h, placed, view, s):
    gap, edge = 3 * s, 2 * s
    max_x = max(edge, view[0] - w - edge)
    max_y = max(edge, view[1] - h - edge)
    x = min(max(edge, x), max_x)
    y = min(max(edge, y), max_y)
    for _ in range(len(placed) * 2 + 2):
        rect = (x, y, x + w, y + h)
        hit = next((r for r in placed if _rects_overlap(rect, r)), None)
        if hit is None:
            break
        y = hit[3] + gap
        if y > max_y:
            x = min(x + w + gap, max_x)
            y = edge
    return x, y


def _ruler_label_spot(a, b, mid_x, mid_y, w, h, s):
    dvx, dvy = b[0] - a[0], b[1] - a[1]
    length = math.hypot(dvx, dvy) or 1.0
    tx, ty = dvx / length, dvy / length
    nx, ny = -ty, tx
    if ny > 0 or (abs(ny) < 1e-9 and nx < 0):
        nx, ny = -nx, -ny
    sdir = 1.0 if tx >= 0 else -1.0
    shift = min(0.30 * length, 64.0 * s)
    foot_x = mid_x + sdir * tx * shift
    foot_y = mid_y + sdir * ty * shift
    lift = (abs(nx) * w + abs(ny) * h) / 2.0 + 12 * s
    return foot_x + nx * lift - w / 2.0, foot_y + ny * lift - h / 2.0


def _seg_hits_rect(p, q, rect):
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
                t0 = max(t0, r)
            else:
                t1 = min(t1, r)
            if t0 > t1:
                return False
    return True


def _ruler_leader_seg(a, b, rect):
    lx0, ly0, lx1, ly1 = rect
    lcx, lcy = (lx0 + lx1) / 2.0, (ly0 + ly1) / 2.0
    dx, dy = b[0] - a[0], b[1] - a[1]
    denom = dx * dx + dy * dy
    t = 0.0 if denom == 0 else ((lcx - a[0]) * dx + (lcy - a[1]) * dy) / denom
    t = max(0.0, min(1.0, t))
    px, py = a[0] + t * dx, a[1] + t * dy
    ex = min(max(px, lx0), lx1)
    ey = min(max(py, ly0), ly1)
    if abs(ex - px) < 1 and abs(ey - py) < 1:
        return None
    return ((ex, ey), (px, py))


def _pick_ruler_label_spot(a, b, w, h, placed, leaders, others, view, s):
    dvx, dvy = b[0] - a[0], b[1] - a[1]
    length = math.hypot(dvx, dvy) or 1.0
    tx, ty = dvx / length, dvy / length
    first = -1.0 if tx > 0 else 1.0
    edge = 2 * s
    for strict in (True, False):
        for frac in (0.5, 0.34, 0.66, 0.2, 0.8):
            ax = a[0] + dvx * frac
            ay = a[1] + dvy * frac
            if not (0 <= ax <= view[0] and 0 <= ay <= view[1]):
                continue
            for side in (first, -first):
                nx, ny = -ty * side, tx * side
                lift = (abs(nx) * w + abs(ny) * h) / 2.0 + 12 * s
                x = ax + nx * lift - w / 2.0
                y = ay + ny * lift - h / 2.0
                x = min(max(edge, x), max(edge, view[0] - w - edge))
                y = min(max(edge, y), max(edge, view[1] - h - edge))
                rect = (x, y, x + w, y + h)
                if any(_rects_overlap(rect, r) for r in placed):
                    continue
                if any(_seg_hits_rect(sg[0], sg[1], rect) for sg in leaders):
                    continue
                if strict and any(_seg_hits_rect(oa, ob, rect)
                                  for oa, ob in others):
                    continue
                seg = _ruler_leader_seg(a, b, rect)
                if seg is not None and any(
                        _seg_hits_rect(seg[0], seg[1], r) for r in placed):
                    continue
                return x, y
    mid_x, mid_y = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
    x, y = _ruler_label_spot(a, b, mid_x, mid_y, w, h, s)
    return _avoid_label_overlap(x, y, w, h, placed, view, s)


# ---------------------------------------------------------------------------
# export, part 3: text - TrueType/OpenType faces read straight from the
# system font files (the ones fontconfig hands Pango), rasterized here
# with anti-aliasing; a built-in bitmap face when no font file exists
# ---------------------------------------------------------------------------


def _cff_bias(count):
    return 107 if count < 1240 else (1131 if count < 33900 else 32768)


class _CffIndex(object):
    """A CFF INDEX, offsets read on demand (CJK fonts carry 60k+
    charstrings; only the glyphs drawn get looked up)."""

    def __init__(self, data, pos):
        self.data = data
        self.count = struct.unpack_from(">H", data, pos)[0]
        if not self.count:
            self.end = pos + 2
            return
        self.size = data[pos + 2]
        self.offs = pos + 3
        self.base = pos + 2 + (self.count + 1) * self.size
        self.end = self.base + self._off(self.count)

    def _off(self, i):
        p = self.offs + i * self.size
        return int.from_bytes(self.data[p:p + self.size], "big")

    def __len__(self):
        return self.count

    def __getitem__(self, i):
        if not 0 <= i < self.count:
            raise IndexError(i)
        start, end = self._off(i), self._off(i + 1)
        return self.data[self.base + start:self.base + end]


def _cff_dict(blob):
    """CFF DICT -> {operator: [operands]} (escaped operators as
    1200 + second byte)."""
    out = {}
    operands = []
    i = 0
    while i < len(blob):
        b0 = blob[i]
        if b0 <= 21:
            if b0 == 12:
                key = 1200 + (blob[i + 1] if i + 1 < len(blob) else 0)
                i += 2
            else:
                key = b0
                i += 1
            out[key] = operands
            operands = []
        elif b0 == 28:
            operands.append(struct.unpack_from(">h", blob, i + 1)[0])
            i += 3
        elif b0 == 29:
            operands.append(struct.unpack_from(">i", blob, i + 1)[0])
            i += 5
        elif b0 == 30:   # real number, nibble coded - only skipped
            i += 1
            while i < len(blob):
                byte = blob[i]
                i += 1
                if byte & 0x0F == 0x0F or byte >> 4 == 0x0F:
                    break
            operands.append(0)
        elif 32 <= b0 <= 246:
            operands.append(b0 - 139)
            i += 1
        elif 247 <= b0 <= 250:
            operands.append((b0 - 247) * 256 + blob[i + 1] + 108)
            i += 2
        elif 251 <= b0 <= 254:
            operands.append(-(b0 - 251) * 256 - blob[i + 1] - 108)
            i += 2
        else:
            i += 1
    return out


class _Cff(object):
    """CFF outlines (OpenType "CFF " table), CID-keyed fonts included."""

    def __init__(self, data, off):
        self.data = data
        pos = off + data[off + 2]
        names = _CffIndex(data, pos)
        tops = _CffIndex(data, names.end)
        strings = _CffIndex(data, tops.end)
        self.gsubrs = _CffIndex(data, strings.end)
        top = _cff_dict(tops[0])
        self.charstrings = _CffIndex(data, off + top[17][0])
        self.fdselect = None
        if 1236 in top:   # FDArray: each font dict its own Private
            fds = _CffIndex(data, off + top[1236][0])
            self.subrs = [self._private_subrs(off, _cff_dict(fds[i]))
                          for i in range(len(fds))]
            if 1237 in top:
                self.fdselect = off + top[1237][0]
        else:
            self.subrs = [self._private_subrs(off, top)]

    def _private_subrs(self, off, top):
        if 18 not in top or len(top[18]) < 2:
            return None
        size, where = int(top[18][0]), int(top[18][1])
        private = _cff_dict(self.data[off + where:off + where + size])
        if 19 in private:
            return _CffIndex(self.data, off + where + int(private[19][0]))
        return None

    def _fd(self, gid):
        if self.fdselect is None:
            return 0
        data, p = self.data, self.fdselect
        if data[p] == 0:
            return data[p + 1 + gid]
        if data[p] == 3:
            count = struct.unpack_from(">H", data, p + 1)[0]
            for k in range(count):
                first, fd, nxt = struct.unpack_from(">HBH", data,
                                                    p + 3 + 3 * k)
                if first <= gid < nxt:
                    return fd
        return 0

    def outline(self, gid):
        if not 0 <= gid < len(self.charstrings):
            return []
        fd = self._fd(gid)
        subrs = self.subrs[fd] if fd < len(self.subrs) else None
        return _T2(self.gsubrs, subrs).run(self.charstrings[gid])


class _T2(object):
    """Type 2 charstring interpreter: outlines only (hints counted to
    skip the hintmask bytes, the advance width taken from hmtx)."""

    def __init__(self, gsubrs, lsubrs):
        self.gsubrs, self.lsubrs = gsubrs, lsubrs
        self.gbias = _cff_bias(len(gsubrs))
        self.lbias = _cff_bias(len(lsubrs)) if lsubrs is not None else 0
        self.contours = []
        self.cur = None
        self.x = self.y = 0.0
        self.stack = []
        self.stems = 0
        self.seen = False   # first stack-clearing operator passed
        self.done = False
        self.store = {}

    def run(self, code):
        self._exec(code, 0)
        self._close()
        return self.contours

    def _close(self):
        if self.cur is not None and len(self.cur) > 1:
            self.contours.append(self.cur)
        self.cur = None

    def _move(self, dx, dy):
        self._close()
        self.x += dx
        self.y += dy
        self.cur = [("M", self.x, self.y)]

    def _line(self, dx, dy):
        if self.cur is None:
            self.cur = [("M", self.x, self.y)]
        self.x += dx
        self.y += dy
        self.cur.append(("L", self.x, self.y))

    def _curve(self, dx1, dy1, dx2, dy2, dx3, dy3):
        if self.cur is None:
            self.cur = [("M", self.x, self.y)]
        x1, y1 = self.x + dx1, self.y + dy1
        x2, y2 = x1 + dx2, y1 + dy2
        self.x, self.y = x2 + dx3, y2 + dy3
        self.cur.append(("C", x1, y1, x2, y2, self.x, self.y))

    def _width(self, extra):
        """Drop the optional leading advance-width operand."""
        if not self.seen and extra:
            del self.stack[0]
        self.seen = True

    def _exec(self, code, depth):
        if depth > 10:
            raise ValueError("charstring subroutines nest too deep")
        st = self.stack
        i, n = 0, len(code)
        while i < n:
            b0 = code[i]
            if b0 >= 32 or b0 == 28:
                if 32 <= b0 <= 246:
                    st.append(b0 - 139)
                    i += 1
                elif b0 == 28:
                    st.append(struct.unpack_from(">h", code, i + 1)[0])
                    i += 3
                elif b0 <= 250:
                    st.append((b0 - 247) * 256 + code[i + 1] + 108)
                    i += 2
                elif b0 <= 254:
                    st.append(-(b0 - 251) * 256 - code[i + 1] - 108)
                    i += 2
                else:
                    st.append(struct.unpack_from(">i", code, i + 1)[0]
                              / 65536.0)
                    i += 5
                continue
            i += 1
            if b0 in (1, 3, 18, 23):          # [hv]stem[hm]
                self._width(len(st) % 2)
                self.stems += len(st) // 2
                del st[:]
            elif b0 in (19, 20):              # hintmask, cntrmask
                if st:                        # implied vstem
                    self._width(len(st) % 2)
                    self.stems += len(st) // 2
                    del st[:]
                self.seen = True
                i += (self.stems + 7) // 8
            elif b0 == 21:                    # rmoveto
                self._width(len(st) > 2)
                self._move(st[-2], st[-1])
                del st[:]
            elif b0 == 22:                    # hmoveto
                self._width(len(st) > 1)
                self._move(st[-1], 0)
                del st[:]
            elif b0 == 4:                     # vmoveto
                self._width(len(st) > 1)
                self._move(0, st[-1])
                del st[:]
            elif b0 == 5:                     # rlineto
                for j in range(0, len(st) - 1, 2):
                    self._line(st[j], st[j + 1])
                del st[:]
            elif b0 in (6, 7):                # hlineto, vlineto
                horizontal = b0 == 6
                for v in st:
                    if horizontal:
                        self._line(v, 0)
                    else:
                        self._line(0, v)
                    horizontal = not horizontal
                del st[:]
            elif b0 == 8:                     # rrcurveto
                for j in range(0, len(st) - 5, 6):
                    self._curve(*st[j:j + 6])
                del st[:]
            elif b0 == 24:                    # rcurveline
                j = 0
                while j + 6 <= len(st) - 2:
                    self._curve(*st[j:j + 6])
                    j += 6
                if j + 2 <= len(st):
                    self._line(st[j], st[j + 1])
                del st[:]
            elif b0 == 25:                    # rlinecurve
                j = 0
                while j + 2 <= len(st) - 6:
                    self._line(st[j], st[j + 1])
                    j += 2
                if j + 6 <= len(st):
                    self._curve(*st[j:j + 6])
                del st[:]
            elif b0 == 26:                    # vvcurveto
                j, d1 = (1, st[0]) if len(st) % 2 else (0, 0)
                while j + 4 <= len(st):
                    self._curve(d1, st[j], st[j + 1], st[j + 2], 0, st[j + 3])
                    d1 = 0
                    j += 4
                del st[:]
            elif b0 == 27:                    # hhcurveto
                j, d1 = (1, st[0]) if len(st) % 2 else (0, 0)
                while j + 4 <= len(st):
                    self._curve(st[j], d1, st[j + 1], st[j + 2], st[j + 3], 0)
                    d1 = 0
                    j += 4
                del st[:]
            elif b0 in (30, 31):              # vhcurveto, hvcurveto
                horizontal = b0 == 31
                j, m = 0, len(st)
                while j + 4 <= m:
                    last = st[j + 4] if m - j == 5 else 0
                    if horizontal:
                        self._curve(st[j], 0, st[j + 1], st[j + 2],
                                    last, st[j + 3])
                    else:
                        self._curve(0, st[j], st[j + 1], st[j + 2],
                                    st[j + 3], last)
                    j += 5 if m - j == 5 else 4
                    horizontal = not horizontal
                del st[:]
            elif b0 == 10 or b0 == 29:        # callsubr, callgsubr
                if not st:
                    raise ValueError("charstring stack underflow")
                if b0 == 10:
                    subrs, bias = self.lsubrs, self.lbias
                else:
                    subrs, bias = self.gsubrs, self.gbias
                if subrs is None:
                    raise ValueError("charstring calls missing subrs")
                self._exec(subrs[int(st.pop()) + bias], depth + 1)
                if self.done:
                    return
            elif b0 == 11:                    # return
                return
            elif b0 == 14:                    # endchar
                self._width(len(st) in (1, 5))
                self.done = True
                return
            elif b0 == 12:
                b1 = code[i]
                i += 1
                self._escape(b1)
            else:
                del st[:]

    def _escape(self, op):
        st = self.stack
        if op == 35 and len(st) >= 12:        # flex
            self._curve(*st[0:6])
            self._curve(*st[6:12])
        elif op == 34 and len(st) >= 7:       # hflex
            dx1, dx2, dy2, dx3, dx4, dx5, dx6 = st[:7]
            self._curve(dx1, 0, dx2, dy2, dx3, 0)
            self._curve(dx4, 0, dx5, -dy2, dx6, 0)
        elif op == 36 and len(st) >= 9:       # hflex1
            dx1, dy1, dx2, dy2, dx3, dx4, dx5, dy5, dx6 = st[:9]
            self._curve(dx1, dy1, dx2, dy2, dx3, 0)
            self._curve(dx4, 0, dx5, dy5, dx6, -(dy1 + dy2 + dy5))
        elif op == 37 and len(st) >= 11:      # flex1
            d = st[:11]
            dx = sum(d[0:10:2])
            dy = sum(d[1:10:2])
            self._curve(*d[0:6])
            if abs(dx) > abs(dy):
                self._curve(d[6], d[7], d[8], d[9], d[10], -dy)
            else:
                self._curve(d[6], d[7], d[8], d[9], -dx, d[10])
        else:
            self._arith(op)
            return
        del st[:]

    def _arith(self, op):
        """The rarely used arithmetic/storage operators."""
        st = self.stack
        try:
            if op == 9:
                st.append(abs(st.pop()))
            elif op == 10:
                b, a = st.pop(), st.pop()
                st.append(a + b)
            elif op == 11:
                b, a = st.pop(), st.pop()
                st.append(a - b)
            elif op == 12:
                b, a = st.pop(), st.pop()
                st.append(a / b if b else 0)
            elif op == 14:
                st.append(-st.pop())
            elif op == 24:
                b, a = st.pop(), st.pop()
                st.append(a * b)
            elif op == 26:
                st.append(math.sqrt(max(0, st.pop())))
            elif op == 18:
                st.pop()
            elif op == 27:
                st.append(st[-1])
            elif op == 28:
                st[-1], st[-2] = st[-2], st[-1]
            elif op == 3:
                b, a = st.pop(), st.pop()
                st.append(1 if a and b else 0)
            elif op == 4:
                b, a = st.pop(), st.pop()
                st.append(1 if a or b else 0)
            elif op == 5:
                st.append(0 if st.pop() else 1)
            elif op == 15:
                b, a = st.pop(), st.pop()
                st.append(1 if a == b else 0)
            elif op == 22:
                v2, v1, s2, s1 = st.pop(), st.pop(), st.pop(), st.pop()
                st.append(s1 if v1 <= v2 else s2)
            elif op == 23:
                st.append(0.5)
            elif op == 20:
                index, value = st.pop(), st.pop()
                self.store[int(index)] = value
            elif op == 21:
                st.append(self.store.get(int(st.pop()), 0))
            elif op == 29:
                index = int(st.pop())
                st.append(st[-1 - index] if index >= 0 else st[-1])
            elif op == 30:
                shift, count = int(st.pop()), int(st.pop())
                if count > 0:
                    part = st[-count:]
                    shift %= count
                    st[-count:] = part[-shift:] + part[:-shift]
            else:
                del st[:]
        except IndexError:
            del st[:]


def _tt_contour(points):
    """TrueType (x, y, on-curve) points -> path ops, implied on-curve
    midpoints between consecutive off-curve points."""
    full = []
    count = len(points)
    for k in range(count):
        x, y, on = points[k]
        full.append((x, y, on))
        nx, ny, non = points[(k + 1) % count]
        if not on and not non:
            full.append(((x + nx) / 2.0, (y + ny) / 2.0, 1))
    start = next((k for k, p in enumerate(full) if p[2]), None)
    if start is None:
        return None
    full = full[start:] + full[:start]
    ops = [("M", full[0][0], full[0][1])]
    k, m = 1, len(full)
    while k <= m:
        x, y, on = full[k % m]
        if on:
            ops.append(("L", x, y))
            k += 1
        else:
            nx, ny, _ = full[(k + 1) % m]
            ops.append(("Q", x, y, nx, ny))
            k += 2
    return ops


class _SfntFont(object):
    """One TrueType/OpenType face (glyf or CFF outlines), read from the
    font file on demand - just the tables needed to draw text."""

    def __init__(self, path, index=0):
        self.path = path
        with open(path, "rb") as handle:
            try:
                self.data = mmap.mmap(handle.fileno(), 0,
                                      access=mmap.ACCESS_READ)
            except (ValueError, OSError):
                self.data = handle.read()
        data = self.data
        base = 0
        if data[:4] == b"ttcf":
            if index >= struct.unpack_from(">I", data, 8)[0]:
                raise ValueError("no face %d in %s" % (index, path))
            base = struct.unpack_from(">I", data, 12 + 4 * index)[0]
        if data[base:base + 4] not in (b"\x00\x01\x00\x00", b"OTTO",
                                       b"true"):
            raise ValueError("not a TrueType/OpenType font: %s" % path)
        self.tables = {}
        for k in range(struct.unpack_from(">H", data, base + 4)[0]):
            tag, _, where, size = struct.unpack_from(">4sIII", data,
                                                     base + 12 + 16 * k)
            self.tables[tag] = (where, size)
        head = self.tables[b"head"][0]
        self.upem = struct.unpack_from(">H", data, head + 18)[0] or 1000
        self.long_loca = struct.unpack_from(">h", data, head + 50)[0] == 1
        hhea = self.tables[b"hhea"][0]
        self.ascender, self.descender = struct.unpack_from(">hh", data,
                                                           hhea + 4)
        if self.ascender <= 0 or self.ascender - self.descender <= 0:
            self.ascender, self.descender = (int(self.upem * 0.8),
                                             -int(self.upem * 0.2))
        self.hmetrics = struct.unpack_from(">H", data, hhea + 34)[0]
        self.hmtx = self.tables[b"hmtx"][0]
        self.glyph_count = struct.unpack_from(
            ">H", data, self.tables[b"maxp"][0] + 4)[0]
        self._cmap()
        if b"glyf" in self.tables and b"loca" in self.tables:
            self.glyf = self.tables[b"glyf"][0]
            self.loca = self.tables[b"loca"][0]
            self.cff = None
        elif b"CFF " in self.tables:
            self.cff = _Cff(data, self.tables[b"CFF "][0])
        else:
            raise ValueError("no glyf/CFF outlines: %s" % path)

    def _cmap(self):
        data = self.data
        cmap = self.tables[b"cmap"][0]
        best = None
        for k in range(struct.unpack_from(">H", data, cmap + 2)[0]):
            pid, eid, where = struct.unpack_from(">HHI", data,
                                                 cmap + 4 + 8 * k)
            fmt = struct.unpack_from(">H", data, cmap + where)[0]
            rank = {(3, 10, 12): 0, (0, 4, 12): 1, (0, 6, 12): 1,
                    (3, 1, 4): 2, (0, 3, 4): 3}.get((pid, eid, fmt))
            if rank is None and pid == 0 and fmt in (4, 12):
                rank = 4
            if rank is not None and (best is None or rank < best[0]):
                best = (rank, cmap + where, fmt)
        if best is None:
            raise ValueError("no Unicode cmap")
        _, off, fmt = best
        self.cmap_fmt = fmt
        if fmt == 4:
            segs = struct.unpack_from(">H", data, off + 6)[0] // 2
            self.c_ends = struct.unpack_from(">%dH" % segs, data, off + 14)
            self.c_starts = struct.unpack_from(">%dH" % segs, data,
                                               off + 16 + 2 * segs)
            self.c_deltas = struct.unpack_from(">%dh" % segs, data,
                                               off + 16 + 4 * segs)
            self.c_ro_pos = off + 16 + 6 * segs
            self.c_ranges = struct.unpack_from(">%dH" % segs, data,
                                               self.c_ro_pos)
        else:
            count = struct.unpack_from(">I", data, off + 12)[0]
            groups = struct.unpack_from(">%dI" % (3 * count), data, off + 16)
            self.c_starts = groups[0::3]
            self.c_ends = groups[1::3]
            self.c_gids = groups[2::3]

    def glyph(self, cp):
        """Glyph index for a code point, 0 when the face lacks it."""
        if self.cmap_fmt == 4:
            if cp > 0xFFFF:
                return 0
            k = bisect.bisect_left(self.c_ends, cp)
            if k >= len(self.c_ends) or self.c_starts[k] > cp:
                return 0
            if not self.c_ranges[k]:
                gid = (cp + self.c_deltas[k]) & 0xFFFF
            else:
                at = (self.c_ro_pos + 2 * k + self.c_ranges[k]
                      + 2 * (cp - self.c_starts[k]))
                gid = struct.unpack_from(">H", self.data, at)[0]
                if gid:
                    gid = (gid + self.c_deltas[k]) & 0xFFFF
        else:
            k = bisect.bisect_right(self.c_starts, cp) - 1
            if k < 0 or cp > self.c_ends[k]:
                return 0
            gid = self.c_gids[k] + cp - self.c_starts[k]
        return gid if gid < self.glyph_count else 0

    def advance(self, gid):
        k = min(gid, self.hmetrics - 1)
        return struct.unpack_from(">H", self.data, self.hmtx + 4 * k)[0]

    def outline(self, gid):
        """Contours in font units (y up): lists of ("M", x, y) then
        ("L", x, y) / ("Q", cx, cy, x, y) / ("C", ...) ops."""
        if self.cff is not None:
            return self.cff.outline(gid)
        contours = []
        for points in self._glyf_points(gid, 0):
            ops = _tt_contour(points)
            if ops is not None:
                contours.append(ops)
        return contours

    def _loca(self, gid):
        if self.long_loca:
            return struct.unpack_from(">I", self.data, self.loca + 4 * gid)[0]
        return struct.unpack_from(">H", self.data, self.loca + 2 * gid)[0] * 2

    def _glyf_points(self, gid, depth):
        if not 0 <= gid < self.glyph_count or depth > 8:
            return []
        start, end = self._loca(gid), self._loca(gid + 1)
        if end <= start:
            return []
        data = self.data
        p = self.glyf + start
        count = struct.unpack_from(">h", data, p)[0]
        if count >= 0:
            if not count:
                return []
            ends = struct.unpack_from(">%dH" % count, data, p + 10)
            total = ends[-1] + 1
            q = p + 10 + 2 * count
            q += 2 + struct.unpack_from(">H", data, q)[0]
            flags = []
            while len(flags) < total:
                flag = data[q]
                q += 1
                flags.append(flag)
                if flag & 8:
                    flags.extend([flag] * data[q])
                    q += 1
            del flags[total:]
            coords = []
            for short, same in ((2, 16), (4, 32)):
                values = []
                v = 0
                for flag in flags:
                    if flag & short:
                        d = data[q]
                        q += 1
                        v += d if flag & same else -d
                    elif not flag & same:
                        v += struct.unpack_from(">h", data, q)[0]
                        q += 2
                    values.append(v)
                coords.append(values)
            xs, ys = coords
            contours = []
            first = 0
            for last in ends:
                contours.append([(xs[k], ys[k], flags[k] & 1)
                                 for k in range(first, last + 1)])
                first = last + 1
            return contours
        contours = []
        q = p + 10
        while True:
            flags, sub = struct.unpack_from(">HH", data, q)
            q += 4
            if flags & 1:
                a1, a2 = struct.unpack_from(">hh" if flags & 2 else ">HH",
                                            data, q)
                q += 4
            else:
                a1, a2 = struct.unpack_from(">bb" if flags & 2 else ">BB",
                                            data, q)
                q += 2
            xx, xy, yx, yy = 1.0, 0.0, 0.0, 1.0
            if flags & 8:
                xx = yy = struct.unpack_from(">h", data, q)[0] / 16384.0
                q += 2
            elif flags & 0x40:
                xx, yy = [v / 16384.0 for v in
                          struct.unpack_from(">hh", data, q)]
                q += 4
            elif flags & 0x80:
                xx, xy, yx, yy = [v / 16384.0 for v in
                                  struct.unpack_from(">hhhh", data, q)]
                q += 8
            part = [[(xx * x + yx * y, xy * x + yy * y, on)
                     for x, y, on in c]
                    for c in self._glyf_points(sub, depth + 1)]
            if flags & 2:
                dx, dy = a1, a2
            else:   # anchor points: parent point a1 meets child point a2
                mine = [pt for c in contours for pt in c]
                theirs = [pt for c in part for pt in c]
                dx = dy = 0
                if a1 < len(mine) and a2 < len(theirs):
                    dx = mine[a1][0] - theirs[a2][0]
                    dy = mine[a1][1] - theirs[a2][1]
            contours.extend([[(x + dx, y + dy, on) for x, y, on in c]
                             for c in part])
            if not flags & 0x20:
                return contours


# X11 misc-fixed 6x13 ("Public domain font.  Share and enjoy."): ASCII
# 0x20-0x7E, 13 rows per glyph as 2 hex digits, bit 5 = leftmost pixel.
_FIXED_6X13 = (
    "0000000000000000000000000000000808080808080800080000000014141400"
    "0000000000000000000014143e143e14140000000000081e28281c0a0a3c0800"
    "000000122a14040810142a240000000000102828102826241a00000000080808"
    "0000000000000000000408081010101010080804000010080804040404040808"
    "10000000082a1c2a080000000000000000000008083e08080000000000000000"
    "00000000000c0810000000000000003e00000000000000000000000000000008"
    "1c08000000020204040810102020000000000814222222222214080000000008"
    "182808080808083e000000001c222202040810203e000000003e0204081c0202"
    "221c0000000004040c1414243e0404000000003e20202c320202221c00000000"
    "1c2220203c2222221c000000003e0204040808101010000000001c2222221c22"
    "22221c000000001c2222221e0202221c000000000000081c080000081c080000"
    "000000081c0800000c0810000000020408102010080402000000000000003e00"
    "003e000000000000201008040204081020000000001c22220204080800080000"
    "00001c2222262a2a2c201e0000000008142222223e222222000000003c121212"
    "1c1212123c000000001c222020202020221c000000003c121212121212123c00"
    "0000003e2020203c2020203e000000003e2020203c20202020000000001c2220"
    "20202622221c00000000222222223e22222222000000001c080808080808081c"
    "000000000e040404040404241800000000222224283028242222000000002020"
    "2020202020203e000000002222362a2a22222222000000002232322a2a262622"
    "22000000001c222222222222221c000000003c2222223c20202020000000001c"
    "2222222222222a1c020000003c2222223c28242222000000001c2220201c0202"
    "221c000000003e08080808080808080000000022222222222222221c00000000"
    "22222222141414080800000000222222222a2a2a2a1400000000222214140814"
    "14222200000000222214140808080808000000003e020404081010203e000000"
    "1c1010101010101010101c0000002020101008040402020000001c0404040404"
    "040404041c000000081422000000000000000000000000000000000000003e00"
    "0008040000000000000000000000000000001c021e22261a000000002020203c"
    "222222223c000000000000001c222020221c000000000202021e222222221e00"
    "0000000000001c223e20221c000000000c1210103c1010101000000000000000"
    "1c2222221e02221c00002020202c32222222220000000000080018080808081c"
    "000000000004000c040404042424180000202020242830282422000000001808"
    "0808080808081c00000000000000342a2a2a2a22000000000000002c32222222"
    "22000000000000001c222222221c000000000000003c2222223c202020000000"
    "00001e2222221e02020200000000002c3220202020000000000000001c221804"
    "221c000000000010103c101010120c0000000000000022222222261a00000000"
    "0000002222221414080000000000000022222a2a2a1400000000000000221408"
    "08142200000000000000222222261a02221c00000000003e040810203e000000"
    "0608080808300808080806000000080808080808080808000000300808080806"
    "0808080830000000122a240000000000000000")


class _BitmapFont(object):
    """The built-in 6x13 face as outlines (every lit pixel run a
    rectangle), so it scales through the same rasterizer."""

    upem, ascender, descender = 13, 11, -2

    def __init__(self):
        self.rows = bytes.fromhex(_FIXED_6X13)

    def glyph(self, cp):
        return cp - 0x1F if 0x20 <= cp <= 0x7E else 0

    def advance(self, gid):
        return 6

    def outline(self, gid):
        contours = []
        base = (gid - 1) * 13
        for r in range(13):
            bits = self.rows[base + r]
            top, bottom = 11 - r, 10 - r
            x = 0
            while x < 6:
                if bits >> (5 - x) & 1:
                    start = x
                    while x < 6 and bits >> (5 - x) & 1:
                        x += 1
                    contours.append([("M", start, top), ("L", x, top),
                                     ("L", x, bottom),
                                     ("L", start, bottom)])
                else:
                    x += 1
        return contours


def _flatten(contours, scale, ox, oy):
    """Font-unit contours -> closed pixel polylines (y flipped so the
    baseline sits at oy); curves split finely enough to stay within
    ~0.2 px of the true outline."""
    polys = []
    for ops in contours:
        pts = []
        cx = cy = 0.0
        for op in ops:
            kind = op[0]
            if kind == "M" or kind == "L":
                cx, cy = ox + op[1] * scale, oy - op[2] * scale
                pts.append((cx, cy))
            elif kind == "Q":
                x1, y1 = ox + op[1] * scale, oy - op[2] * scale
                x2, y2 = ox + op[3] * scale, oy - op[4] * scale
                dd = abs(cx - 2 * x1 + x2) + abs(cy - 2 * y1 + y2)
                steps = max(1, min(24, int(math.ceil(math.sqrt(dd * 1.25)))))
                for k in range(1, steps + 1):
                    t = k / float(steps)
                    mt = 1.0 - t
                    pts.append((mt * mt * cx + 2 * mt * t * x1 + t * t * x2,
                                mt * mt * cy + 2 * mt * t * y1 + t * t * y2))
                cx, cy = x2, y2
            else:
                x1, y1 = ox + op[1] * scale, oy - op[2] * scale
                x2, y2 = ox + op[3] * scale, oy - op[4] * scale
                x3, y3 = ox + op[5] * scale, oy - op[6] * scale
                dd = max(abs(cx - 2 * x1 + x2) + abs(cy - 2 * y1 + y2),
                         abs(x1 - 2 * x2 + x3) + abs(y1 - 2 * y2 + y3))
                steps = max(1, min(32, int(math.ceil(math.sqrt(dd * 3.75)))))
                for k in range(1, steps + 1):
                    t = k / float(steps)
                    mt = 1.0 - t
                    a, b, c, d = mt * mt * mt, 3 * mt * mt * t, \
                        3 * mt * t * t, t * t * t
                    pts.append((a * cx + b * x1 + c * x2 + d * x3,
                                a * cy + b * y1 + c * y2 + d * y3))
                cx, cy = x3, y3
        if len(pts) > 2:
            polys.append(pts)
    return polys


def _accumulate_line(acc, w, h, x0, y0, x1, y1):
    """Signed-area accumulation of one edge (the font-rs scheme): each
    covered cell gets the exact area the edge sweeps, a running sum
    along the row turns it into coverage."""
    if y0 == y1:
        return
    if y0 < y1:
        sign = 1.0
    else:
        sign = -1.0
        x0, y0, x1, y1 = x1, y1, x0, y0
    dxdy = (x1 - x0) / (y1 - y0)
    x = x0
    if y0 < 0:
        x -= y0 * dxdy
    for y in range(max(0, int(y0)), min(h, int(math.ceil(y1)))):
        line = y * w
        dy = min(y + 1.0, y1) - max(float(y), y0)
        xnext = x + dxdy * dy
        d = dy * sign
        lo, hi = (x, xnext) if x < xnext else (xnext, x)
        lo_f = math.floor(lo)
        lo_i = int(lo_f)
        hi_c = math.ceil(hi)
        hi_i = int(hi_c)
        if hi_i <= lo_i + 1:
            mid = 0.5 * (x + xnext) - lo_f
            acc[line + lo_i] += d - d * mid
            acc[line + lo_i + 1] += d * mid
        else:
            inv = 1.0 / (hi - lo)
            f0 = lo - lo_f
            a0 = 0.5 * inv * (1.0 - f0) * (1.0 - f0)
            f1 = hi - hi_c + 1.0
            am = 0.5 * inv * f1 * f1
            acc[line + lo_i] += d * a0
            if hi_i == lo_i + 2:
                acc[line + lo_i + 1] += d * (1.0 - a0 - am)
            else:
                a1 = inv * (1.5 - f0)
                acc[line + lo_i + 1] += d * (a1 - a0)
                for xi in range(lo_i + 2, hi_i - 1):
                    acc[line + xi] += d * inv
                a2 = a1 + (hi_i - lo_i - 3) * inv
                acc[line + hi_i - 1] += d * (1.0 - a2 - am)
            acc[line + hi_i] += d * am
        x = xnext


def _rasterize(polys, bold=0):
    """Pixel polylines -> (left, top, w, h, coverage bytes 0-255), the
    nonzero fill anti-aliased; bold widens it rightwards by smearing
    the coverage over that many extra pixels."""
    xs = [p[0] for pts in polys for p in pts]
    ys = [p[1] for pts in polys for p in pts]
    if not xs:
        return None
    left, top = int(math.floor(min(xs))), int(math.floor(min(ys)))
    w = int(math.ceil(max(xs))) - left + 2
    h = int(math.ceil(max(ys))) - top
    if h <= 0:
        return None
    acc = [0.0] * (w * h + 2)
    for pts in polys:
        prev = pts[-1]
        for pt in pts:
            _accumulate_line(acc, w, h, prev[0] - left, prev[1] - top,
                             pt[0] - left, pt[1] - top)
            prev = pt
    cov = bytearray(w * h)
    for row in range(0, w * h, w):
        total = 0.0
        for k in range(row, row + w):
            total += acc[k]
            v = total if total >= 0 else -total
            cov[k] = 255 if v >= 1.0 else int(v * 255.0 + 0.5)
    if bold:
        wide = w + bold
        out = bytearray(wide * h)
        for row in range(h):
            src = cov[row * w:(row + 1) * w]
            dst = row * wide
            for k in range(bold + 1):
                for x in range(w):
                    v = src[x]
                    if v > out[dst + x + k]:
                        out[dst + x + k] = v
        cov, w = out, wide
    return left, top, w, h, cov


# -- font discovery, fallback chain, text layout -------------------------

_FONT_DIRS = ("/usr/share/fonts", "/usr/local/share/fonts",
              "~/.local/share/fonts", "~/.fonts",
              "/System/Library/Fonts", "/Library/Fonts")
# Without fontconfig: well-known faces, Latin first, then Hangul ones.
_FONT_FILES = ("DejaVuSans.ttf", "LiberationSans-Regular.ttf",
               "NotoSans-Regular.ttf", "Arial.ttf", "NanumGothic.ttf",
               "NotoSansCJK-Regular.ttc", "NotoSansCJKkr-Regular.otf",
               "NotoSansKR-Regular.otf", "UnDotum.ttf", "gulim.ttf",
               "AppleSDGothicNeo.ttc", "AppleGothic.ttf",
               "Arial Unicode.ttf")
_FONT_EXTS = (".ttf", ".otf", ".ttc", ".otc")


def _system_fonts():
    """(path, face index) candidates in fallback order: fontconfig's
    sorted list for sans-serif - the faces Pango would fall back
    through - else well-known files in the usual font directories."""
    found = []
    try:
        proc = subprocess.Popen(
            ["fc-match", "-s", "-f", "%{file}\t%{index}\n", "sans-serif"],
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        try:
            out = proc.communicate(timeout=20)[0]
        except subprocess.TimeoutExpired:
            proc.kill()
            out = proc.communicate()[0]
    except OSError:
        out = b""
    for line in out.decode("utf-8", "replace").splitlines():
        path, _, index = line.partition("\t")
        if path.lower().endswith(_FONT_EXTS) \
                and "lastresort" not in path.lower():
            try:
                found.append((path, int(index or 0)))
            except ValueError:
                pass
    if found:
        return found
    names = {}
    for root in _FONT_DIRS:
        for folder, _, files in os.walk(os.path.expanduser(root)):
            for name in files:
                if name.lower().endswith(_FONT_EXTS):
                    names.setdefault(name, os.path.join(folder, name))
    known = [names.pop(name) for name in _FONT_FILES if name in names]
    return [(path, 0) for path in known + sorted(names.values())]


def _font_spec(text):
    """--font value: FILE or FILE:N (face N of a collection)."""
    path, sep, index = text.rpartition(":")
    if sep and index.isdigit() and not os.path.exists(text):
        return path, int(index)
    return text, 0


class _Fonts(object):
    """The export's font fallback chain: --font faces first, then the
    system faces in fontconfig order (each loaded only once a character
    is still missing), the built-in 6x13 face last - and only for
    ASCII.  Characters nobody has draw as a hollow box."""

    def __init__(self, specs=(), system=True):
        self.specs = [_font_spec(s) for s in specs]
        self.explicit = len(self.specs)
        self.system = system
        self.faces = []
        self.next = 0
        self.bitmap = _BitmapFont()
        self.chars = {}
        self.missing = set()
        self.reported = set()
        self.warned = False
        self.glyphs = {}

    def warnings(self):
        """Text problems not reported yet, as messages: no font file
        at all, characters no face has."""
        out = []
        if not self.faces and self.chars and not self.warned:
            self.warned = True
            out.append("no TrueType/OpenType font found: text uses the "
                       "built-in 6x13 face (ASCII only); add --font FILE")
        fresh = sorted(self.missing - self.reported)
        if fresh:
            self.reported.update(fresh)
            more = len(fresh) - 12
            out.append("no font has %s%s (drawn as boxes); add --font FILE"
                       % (", ".join("%s (U+%04X)" % (ch, ord(ch))
                                    for ch in fresh[:12]),
                          " and %d more" % more if more > 0 else ""))
        return out

    def load_explicit(self):
        """Open every --font face now, raising ValueError on a bad one."""
        while self.next < self.explicit:
            self._load_next()

    def _load_next(self):
        if self.next >= len(self.specs) and self.system:
            self.system = False
            self.specs.extend(c for c in _system_fonts()
                              if c not in self.specs)
        while self.next < len(self.specs):
            path, index = self.specs[self.next]
            self.next += 1
            try:
                self.faces.append(_SfntFont(path, index))
                return True
            except (OSError, ValueError, KeyError, IndexError,
                    struct.error) as exc:
                if self.next <= self.explicit:
                    raise ValueError("font %s: %s" % (path, exc))
        return False

    @property
    def primary(self):
        if not self.faces:
            self._load_next()
        return self.faces[0] if self.faces else self.bitmap

    def lookup(self, ch):
        """(face, glyph id) for one character; face None = no glyph."""
        hit = self.chars.get(ch)
        if hit is None:
            cp = ord(ch)
            k = 0
            while hit is None:
                while k < len(self.faces) and hit is None:
                    gid = self.faces[k].glyph(cp)
                    if gid:
                        hit = (self.faces[k], gid)
                    k += 1
                if hit is None and not self._load_next():
                    break
            if hit is None:
                gid = self.bitmap.glyph(cp)
                if gid:
                    hit = (self.bitmap, gid)
                else:
                    self.missing.add(ch)
                    hit = (None, 0)
            self.chars[ch] = hit
        return hit

    def coverage(self, face, gid, px, frac, bold):
        """Cached glyph coverage: (left, top, w, h, coverage) around
        the pen at (frac, baseline 0), or None for blank glyphs."""
        key = (id(face), gid, px, frac, bold)
        hit = self.glyphs.get(key, False)
        if hit is not False:
            return hit
        if len(self.glyphs) > 4096:
            self.glyphs.clear()
        if face is None:   # hollow box for a character no face has
            t = max(1.0, px / 14.0)
            x0, x1 = frac + px * 0.08, frac + px * 0.52
            y0, y1 = -px * 0.72, 0.0
            polys = [[(x0, y0), (x1, y0), (x1, y1), (x0, y1)],
                     [(x0 + t, y0 + t), (x0 + t, y1 - t), (x1 - t, y1 - t),
                      (x1 - t, y0 + t)]]
        else:
            try:
                contours = face.outline(gid)
            except (ValueError, IndexError, KeyError, struct.error):
                contours = []
            polys = _flatten(contours, px / float(face.upem), frac, 0.0)
        hit = self.glyphs[key] = _rasterize(polys, bold) if polys else None
        return hit


class _TextBlock(object):
    """Lines of text laid out at px size the way a GtkLabel does it:
    each line ascent + descent tall, glyphs on the face's advances."""

    def __init__(self, fonts, text, px, bold=0):
        self.fonts, self.px, self.bold = fonts, px, bold
        primary = fonts.primary
        unit = px / float(primary.upem)
        asc, desc = primary.ascender * unit, -primary.descender * unit
        self.lines = []
        width = 0.0
        for line in text.split("\n"):
            glyphs = []
            x = 0.0
            for ch in line:
                if ch == "\t":
                    ch = " "
                if ord(ch) < 32:
                    continue
                face, gid = fonts.lookup(ch)
                glyphs.append((face, gid, x))
                if face is None:
                    x += px * 0.6 + bold
                    continue
                unit = px / float(face.upem)
                x += face.advance(gid) * unit + bold
                if face is not primary:
                    asc = max(asc, face.ascender * unit)
                    desc = max(desc, -face.descender * unit)
            self.lines.append(glyphs)
            width = max(width, x)
        self.ascent, self.line_h = asc, asc + desc
        self.width = int(math.ceil(width))
        self.height = int(math.ceil(self.line_h * len(self.lines)))

    def draw(self, cv, x, y, rgb, clip, alpha=255):
        """Paint with the block's top-left at (x, y)."""
        fonts = self.fonts
        for k, glyphs in enumerate(self.lines):
            base = int(math.floor(y + self.ascent + k * self.line_h + 0.5))
            for face, gid, gx in glyphs:
                pen = x + gx
                ix = int(math.floor(pen))
                frac = int((pen - ix) * 4 + 0.5)   # quarter-pixel steps
                if frac == 4:
                    ix, frac = ix + 1, 0
                hit = fonts.coverage(face, gid, self.px, frac / 4.0,
                                      self.bold)
                if hit is not None:
                    left, top, w, h, cov = hit
                    _blend_mask(cv, ix + left, base + top, w, h, cov, rgb,
                                alpha, clip)


def _text_width(fonts, text, px):
    width = 0.0
    for ch in text:
        face, gid = fonts.lookup(ch)
        width += px * 0.6 if face is None \
            else face.advance(gid) * px / float(face.upem)
    return width


def _wrap(fonts, text, px, max_w):
    """Greedy word wrap of every paragraph to max_w pixels; a word too
    long for a line of its own breaks between characters."""
    lines = []
    for para in text.split("\n"):
        line = ""
        for word in para.split(" "):
            joined = word if not line else line + " " + word
            if _text_width(fonts, joined, px) <= max_w:
                line = joined
                continue
            if line:
                lines.append(line)
            line = ""
            for ch in word:
                if line and _text_width(fonts, line + ch, px) > max_w:
                    lines.append(line)
                    line = ""
                line += ch
        lines.append(line)
    return lines


def _hex_rgb(hex_color):
    return (int(hex_color[1:3], 16), int(hex_color[3:5], 16),
            int(hex_color[5:7], 16))


def _chip(cv, x, y, block, fg, bg, pad_x, pad_y, radius, clip):
    """A styled label: backdrop with rounded corners, text inside."""
    if bg is not None:
        _blend_round_rect(cv, x, y, block.width + 2 * pad_x,
                          block.height + 2 * pad_y, radius, bg, clip)
    block.draw(cv, x + pad_x, y + pad_y, fg, clip)


# ---------------------------------------------------------------------------
# export, part 4: the legend table and the exported image
# ---------------------------------------------------------------------------

def _swatch_grid(entry):
    """Viewer.legend_swatch as a 36x14 grid of lit (entry color)
    pixels, painted with the same fill_rect calls; unlit pixels show
    the frame's backdrop."""
    w, h = 36, 14
    grid = [[False] * w for _ in range(h)]

    def fill(x, y, fw, fh):
        for yy in range(max(y, 0), min(y + fh, h)):
            for xx in range(max(x, 0), min(x + fw, w)):
                grid[yy][xx] = True

    style = entry["style"]
    if entry["kind"] == "line":
        y = h // 2 - 1
        if style == "solid":
            fill(0, y, w, 2)
        else:
            on, period = (5, 9) if style == "dashed" else (2, 5)
            for x in range(0, w, period):
                fill(x, y, min(on, w - x), 2)
        return grid
    if style == "solid":
        fill(0, 0, w, h)
        return grid
    hexs = (style[4:] if style.startswith("pat:")
            else FILL_PATTERNS.get(style))
    if hexs is not None:   # floe fill pattern, MSB = leftmost
        rows = [int(hexs[i * 4:i * 4 + 4], 16) for i in range(16)]
        for y in range(h):
            for x in range(w):
                if (rows[y % 16] >> (15 - (x % 16))) & 1:
                    fill(x, y, 1, 1)
    elif style in ("hatch", "cross"):
        for x in range(w):
            for y in range(h):
                if (x + y) % 5 == 0 or \
                        (style == "cross" and (x - y) % 5 == 0):
                    fill(x, y, 1, 1)
    elif style == "dots":
        for x in range(3, w - 2, 5):
            for y in range(3, h - 2, 5):
                fill(x, y, 2, 2)
    fill(0, 0, w, 1)          # outline on top
    fill(0, h - 1, w, 1)
    fill(0, 0, 1, h)
    fill(w - 1, 0, 1, h)
    return grid


def _draw_swatch(cv, x, y, w, h, entry, s, clip):
    grid = _swatch_grid(entry)
    rgba = _rgba(entry["color"])
    for dy in range(h):
        yy = y + dy
        if not clip[1] <= yy < clip[3]:
            continue
        row = grid[min(13, int(dy / s))]
        dx = 0
        while dx < w:
            if not row[min(35, int(dx / s))]:
                dx += 1
                continue
            start = dx
            while dx < w and row[min(35, int(dx / s))]:
                dx += 1
            _blend_span(cv, yy, max(x + start, clip[0]),
                        min(x + dx, clip[2]), rgba)


class _LegendFrame(object):
    """The viewer's text legend - swatch + label rows on the dark
    rgba(0,0,0,0.78) frame - at scale s.  Labels are never ellipsized
    (no hover tooltip in a picture); with max_h the rows wrap into
    columns to stay within that height, but a column keeps at least 8
    rows (a short image grows down instead of the legend sideways)."""

    BACKDROP = b"\x00\x00\x00\xc7"

    def __init__(self, fonts, entries, s, max_h=None):
        px = UI_PT * DPI_SCALE / 1.2 * s   # Pango "small"
        self.s = s
        self.pad = int(round(7 * s))
        self.gap = int(round(7 * s))
        self.row_gap = int(round(4 * s))
        self.col_gap = int(round(14 * s))
        self.sw, self.sh = int(round(36 * s)), int(round(14 * s))
        self.items = [(e, _TextBlock(fonts, e["label"], px)) for e in entries]
        self.row_h = max([self.sh] + [b.height for _, b in self.items])
        rows = len(self.items)
        if max_h is not None:
            fit = (max_h - 2 * self.pad + self.row_gap) \
                // (self.row_h + self.row_gap)
            rows = min(rows, max(fit, 8))
        self.columns = [self.items[k:k + rows]
                        for k in range(0, len(self.items), rows)]
        self.col_w = [self.sw + self.gap + max(b.width for _, b in col)
                      for col in self.columns]
        self.width = 2 * self.pad + sum(self.col_w) \
            + self.col_gap * (len(self.columns) - 1)
        self.height = 2 * self.pad + rows * self.row_h \
            + (rows - 1) * self.row_gap

    def draw(self, cv, x, y, clip):
        _blend_rect(cv, x, y, self.width, self.height, self.BACKDROP, clip)
        cx = x + self.pad
        for column, col_w in zip(self.columns, self.col_w):
            ry = y + self.pad
            for entry, block in column:
                _draw_swatch(cv, cx, ry + (self.row_h - self.sh) // 2,
                             self.sw, self.sh, entry, self.s, clip)
                block.draw(cv, cx + self.sw + self.gap,
                           ry + (self.row_h - block.height) // 2,
                           CHIP_TEXT, clip)
                ry += self.row_h + self.row_gap
            cx += col_w + self.col_gap


def _bg_rgba(value):
    """--legend-bg: palette name, #RRGGBB, or none/transparent."""
    if str(value).strip().lower() in ("none", "transparent"):
        return b"\x00\x00\x00\x00"
    try:
        return _rgba(_color(value, "legend background"))
    except ValueError:
        raise ValueError("bad legend background: %s (use %s, #RRGGBB or "
                         "none)" % (value, "/".join(n for n, _ in PALETTE)))


def _render(blob, annos, ppu, unit, note, legend, s, bg, hide, fonts):
    """The export canvas plus the source chunks worth keeping."""
    width, height, rgba, alpha, keep = _png_decode(blob)
    opaque = not alpha or rgba[3::4].count(255) == width * height
    cv = _Canvas(width, height, rgba, opaque)
    cx, cy = width / 2.0, height / 2.0
    view = (width, height)
    clip = (0, 0, width, height)
    unit = unit or "um"
    shown = [a for a in annos
             if {"text": "texts", "ruler": "rulers"}.get(a["kind"], "shapes")
             not in hide]
    layer = _Layer(width, height)
    painter = _Painter(layer, s)
    for anno in shown:
        if anno["kind"] not in ("text", "ruler"):
            painter.shape(anno, cx, cy)
    # Rulers stamp last: fills replace pixels, so a later box would
    # erase an earlier measurement line (the viewer's order).
    rulers = [a for a in shown if a["kind"] == "ruler"]
    for anno in rulers:
        painter.shape(anno, cx, cy)
    ruler_px = UI_PT * DPI_SCALE * s
    ruler_bold = max(1, int(round(ruler_px / 15.0)))
    pad_x, pad_y = int(round(7 * s)), int(round(2 * s))
    vis = []
    for anno in rulers:
        a = (anno["a"][0] + cx, anno["a"][1] + cy)
        b = (anno["b"][0] + cx, anno["b"][1] + cy)
        mid_x, mid_y = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
        if -40 <= mid_x <= width and -20 <= mid_y <= height:
            vis.append((anno, a, b, mid_x, mid_y))
    multi = len(vis) > 1
    segs = [(a, b) for _, a, b, _, _ in vis]
    placed, leaders, chips = [], [], {}
    for idx, (anno, a, b, mid_x, mid_y) in enumerate(vis):
        dist = math.hypot(anno["b"][0] - anno["a"][0],
                          anno["b"][1] - anno["a"][1])
        block = _TextBlock(fonts, format_distance(dist, ppu, unit),
                           ruler_px, ruler_bold)
        w, h = block.width + 2 * pad_x, block.height + 2 * pad_y
        if multi:   # off the shared crossing, beside each own line
            x, y = _pick_ruler_label_spot(a, b, w, h, placed, leaders,
                                          segs[:idx] + segs[idx + 1:],
                                          view, s)
        else:
            x, y = _avoid_label_overlap(mid_x + 10 * s, mid_y - h - 6 * s,
                                        w, h, placed, view, s)
        chips[id(anno)] = (block, int(x), int(y))
        rect = (x, y, x + w, y + h)
        placed.append(rect)
        if multi:
            seg = _ruler_leader_seg(a, b, rect)
            if seg is not None:
                leaders.append(seg)
    for end, foot in leaders:   # dotted ties back to each own line
        painter.segment(end, foot, None, RULER_CORE, 1, 2)
    layer.composite(cv)
    if note and "note" not in hide:
        px = 11 * s
        sample = "The quick brown fox jumps over the lazy dog."
        char_w = _text_width(fonts, sample, px) / len(sample)
        margin, npad_x, npad_y = (int(round(8 * s)), int(round(9 * s)),
                                  int(round(2 * s)))
        wrap_w = max(char_w, min(44 * char_w,
                                 width - 2 * margin - 2 * npad_x))
        block = _TextBlock(fonts, "\n".join(_wrap(fonts, note, px, wrap_w)),
                           px)
        _chip(cv, margin, margin, block, CHIP_TEXT, b"\x00\x00\x00\x99",
              npad_x, npad_y, int(round(4 * s)), clip)
    # Labels stack in annotation order above the note chip, like the
    # overlay widgets the viewer adds per annotation.
    for anno in shown:
        if anno["kind"] == "ruler" and id(anno) in chips:
            block, x, y = chips[id(anno)]
            _chip(cv, x, y, block, (255, 255, 255), b"\x00\x00\x00\xc7",
                  pad_x, pad_y, int(round(3 * s)), clip)
        elif anno["kind"] == "text":
            x, y = anno["at"][0] + cx, anno["at"][1] + cy
            if not (-20 <= x <= width and -10 <= y <= height):
                continue
            block = _TextBlock(fonts, anno["text"],
                               anno["size"] * DPI_SCALE * s)
            backdrop = None
            if anno.get("bg", True):
                backdrop = _rgba(anno.get("bg_color", DEFAULT_BG),
                                 255 if anno.get("bg_opaque") else 89)
            _chip(cv, int(max(0, x)), int(max(0, y)), block,
                  _hex_rgb(anno["color"]), backdrop,
                  int(round(3 * s)) if backdrop else 0, 0,
                  int(round(2 * s)), clip)
    if legend and "legend" not in hide:
        entries = [parse_legend_line(line) for line in legend]
        margin = int(round(12 * s))
        frame = _LegendFrame(fonts, entries, s, height - 2 * margin)
        cv = _extend(cv, frame.width + 2 * margin,
                     max(height, frame.height + 2 * margin), bg)
        frame.draw(cv, width + margin, cv.height - margin - frame.height,
                   (width, 0, cv.width, cv.height))
    return cv, keep


def _extend(cv, extra_w, new_h, bg):
    """The canvas grown to the right (and down, if needed) with bg."""
    new_w = cv.width + extra_w
    out = bytearray(bg) * (new_w * new_h)
    row = cv.width * 4
    for y in range(cv.height):
        start = y * new_w * 4
        out[start:start + row] = cv.rgba[y * row:(y + 1) * row]
    return _Canvas(new_w, new_h, out, cv.opaque and bg[3] == 255)


_FONT_SETS = {}


def _font_set(fonts):
    """The fallback chain for a --font list, cached so a batch export
    reuses the opened faces and rasterized glyphs.  A _Fonts instance
    passes through (the selftest pins the built-in face that way)."""
    if isinstance(fonts, _Fonts):
        return fonts
    key = tuple(fonts or ())
    chain = _FONT_SETS.get(key)
    if chain is None:
        chain = _Fonts(key)
        chain.load_explicit()
        _FONT_SETS[key] = chain
    return chain


def _export_options(scale, legend_bg, hide):
    """Validated (scale, panel background pixel, hide set)."""
    try:
        s = float(scale)
    except (TypeError, ValueError):
        raise ValueError("bad scale: %r" % (scale,))
    if not 0.25 <= s <= 16:
        raise ValueError("scale must be 0.25-16, got: %g" % s)
    hide = set(hide or ())
    unknown = hide - set(EXPORT_HIDE)
    if unknown:
        raise ValueError("cannot hide %s (choose from %s)"
                         % (", ".join(sorted(unknown)),
                            ", ".join(EXPORT_HIDE)))
    return s, _bg_rgba(legend_bg), hide


def _write_new(path, blob):
    """Write an export: temp file beside it + os.replace, so a reader
    never sees half a PNG; missing parent folders are created."""
    folder = os.path.dirname(os.path.abspath(path))
    if not os.path.isdir(folder):
        os.makedirs(folder)
    fd, tmp = tempfile.mkstemp(prefix=".fe-export-", dir=folder)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(blob)
        mask = os.umask(0)
        os.umask(mask)
        os.chmod(tmp, 0o666 & ~mask)
        os.replace(tmp, path)
    except OSError:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def export_bytes(blob, annos=(), ppu=None, unit=None, note=None,
                 legend=None, scale=1.0, legend_bg="black", hide=(),
                 fonts=None):
    """PNG bytes of the image as flateyes shows it at 100% zoom: the
    embedded shapes, rulers, texts and note drawn into the pixels, and
    the legend table in a panel the image grows to the right for, so
    it covers nothing.  annos/ppu/unit/note/legend work like flateyes'
    own command-line options: annotations go on top of the embedded
    ones, the others replace what is stored.

    scale enlarges every stroke, label and the legend (2 = what the
    viewer shows at 50% zoom, at full resolution); legend_bg colors the
    panel (palette name, #RRGGBB or "none" for transparent); hide
    leaves out any of EXPORT_HIDE; fonts lists font files tried before
    the system fonts.  The result keeps only the ppu/unit metadata, so
    a ruler measured on it still converts."""
    s, bg, hide = _export_options(scale, legend_bg, hide)
    text = _combine(extract_text(blob), list(annos), ppu, unit or "um",
                    note, legend)
    annos, ppu, stored_unit, note, legend = parse_metadata(text)
    unit = unit or stored_unit or "um"
    cv, keep = _render(blob, annos, ppu, unit, note, legend, s, bg, hide,
                       _font_set(fonts))
    out = _png_encode(cv.width, cv.height, cv.rgba, not cv.opaque, keep)
    return insert_text(out, serialize([], ppu, unit)) if ppu else out


def export(path, out_path, **options):
    """export_bytes for the PNG at path, written to out_path; the
    source file is never modified."""
    with open(path, "rb") as handle:
        blob = handle.read()
    _write_new(out_path, export_bytes(blob, **options))


def legend_bytes(legend, scale=1.0, legend_bg="black", fonts=None):
    """The legend table alone as PNG bytes: definition lines in, the
    same frame export_bytes puts beside the image out."""
    s, bg, _ = _export_options(scale, legend_bg, ())
    entries = [parse_legend_line(line) for line in legend_lines(legend)]
    if not entries:
        raise ValueError("empty legend")
    frame = _LegendFrame(_font_set(fonts), entries, s)
    cv = _Canvas(frame.width, frame.height,
                 bytearray(bg) * (frame.width * frame.height), bg[3] == 255)
    frame.draw(cv, 0, 0, (0, 0, cv.width, cv.height))
    return _png_encode(cv.width, cv.height, cv.rgba, not cv.opaque)


def export_legend(path, out_path, legend=None, **options):
    """The legend embedded in the PNG at path (or the given definition
    lines instead) alone, as a PNG at out_path."""
    if legend is None:
        legend = read(path)[4]
        if not legend:
            raise ValueError("no legend embedded")
    _write_new(out_path, legend_bytes(legend, **options))


# ---------------------------------------------------------------------------
# command line
# ---------------------------------------------------------------------------

def parse_anno_option(kind, value):
    """One --box/--ellipse/--line/--ruler/--text value, using the same
    friendly syntax as the flateyes command line (optional style fields,
    palette color names)."""
    if kind == "text":
        parts = value.split(",", 2)
        if len(parts) < 3 or not parts[2].strip():
            raise ValueError("expects X,Y[,STYLE...],TEXT")
        kwargs = {}
        # Optional size=/color=/bg= fields before the text proper; the
        # text starts at the first field that is none of them (or right
        # after an explicit text=, which lets a note begin with
        # "size=" literally).  Same syntax as the flateyes CLI.
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
                    kwargs["size"] = int(val)
                except ValueError:
                    raise ValueError("bad size: %s" % val)
            elif key == "color":
                kwargs["color"] = val
            elif val == "0":    # bg=0: no backdrop
                kwargs["bg"] = False
            elif val.startswith("#") and len(val) == 9:
                try:  # bg=#RRGGBBAA, AA >= 80 = opaque (like FILL)
                    int(val[1:9], 16)
                except ValueError:
                    raise ValueError("bad bg: %s" % val)
                kwargs["bg"] = True
                kwargs["bg_color"] = val[:7]
                kwargs["bg_opaque"] = int(val[7:9], 16) >= 0x80
            else:
                kwargs["bg"] = True
                kwargs["bg_color"] = val
                kwargs["bg_opaque"] = False
            rest = tail
        return text(parts[0], parts[1], unescape_meta(rest), **kwargs)
    if kind in ("path", "polygon"):
        parts = [part.strip() for part in value.split(",")]
        coords = []
        while parts:
            try:
                coords.append(float(parts[0]))
            except ValueError:
                break
            parts.pop(0)
        if len(coords) % 2 and coords and coords[-1] == 0:
            # the "0" no-outline sentinel scanned as a coordinate
            coords.pop()
            parts.insert(0, "0")
        if len(coords) < (6 if kind == "polygon" else 4) \
                or len(coords) % 2:
            raise ValueError("expects X1,Y1,X2,Y2,X3,Y3[,X4,Y4...]"
                             if kind == "polygon" else
                             "expects X1,Y1,X2,Y2[,X3,Y3...]")
        kwargs = {}
        if parts:
            color = parts.pop(0)
            if kind == "polygon" and color == "0":
                kwargs["outline"] = False
            elif color:
                kwargs["color"] = color
        if kind == "polygon" and parts:  # FILL, like a box
            fill = parts.pop(0)
            if fill not in ("", "0"):
                kwargs["fill"] = fill  # the constructor splits #RRGGBBAA
        if parts:
            kwargs["width"] = int(parts.pop(0))
        if parts:
            kwargs["dash"] = parts.pop(0)
        if parts:
            raise ValueError("too many fields: %s" % ",".join(parts))
        maker = polygon if kind == "polygon" else path
        return maker(list(zip(coords[0::2], coords[1::2])), **kwargs)
    parts = [part.strip() for part in value.split(",")]
    if len(parts) < 4:
        raise ValueError("expects X1,Y1,X2,Y2")
    coords = parts[:4]
    rest = parts[4:]
    if kind == "ruler":
        if rest:
            raise ValueError("expects exactly X1,Y1,X2,Y2")
        return ruler(*coords)
    kwargs = {}
    if rest:  # 5th field: outline color, 0 = no outline (fill only)
        color = rest.pop(0)
        if color == "0":
            if kind == "line":
                raise ValueError("a line needs a color")
            kwargs["outline"] = False
        elif color:
            kwargs["color"] = color
    if rest and kind != "line":  # 6th: fill, AA of #RRGGBBAA = alpha
        fill = rest.pop(0)
        if fill not in ("", "0"):
            kwargs["fill"] = fill  # the constructor splits #RRGGBBAA
    if rest:  # then WIDTH 1-8 and DASH solid/dashed/dotted
        kwargs["width"] = int(rest.pop(0))
    if rest:
        kwargs["dash"] = rest.pop(0)
    if rest:
        raise ValueError("too many fields: %s" % ",".join(rest))
    maker = {"box": box, "ellipse": ellipse, "line": line}[kind]
    return maker(*coords, **kwargs)


def from_json(obj):
    """One JSON object into an annotation dict via the constructors, so
    a service config gets the same validation as library calls."""
    if not isinstance(obj, dict) or "kind" not in obj:
        raise ValueError("each entry needs a \"kind\"")
    obj = dict(obj)
    kind = obj.pop("kind")
    try:
        if kind == "text":
            at = obj.pop("at", None) or (obj.pop("x"), obj.pop("y"))
            return text(at[0], at[1], obj.pop("text"), **obj)
        if kind in ("path", "polygon"):
            points = obj.pop("points")
            if not isinstance(points, list):
                raise ValueError("%s needs a \"points\" array" % kind)
            return (polygon if kind == "polygon" else path)(points, **obj)
        a = obj.pop("a", None) or (obj.pop("x1"), obj.pop("y1"))
        b = obj.pop("b", None) or (obj.pop("x2"), obj.pop("y2"))
        if kind == "ruler":
            if obj:
                raise ValueError("unknown fields: %s" % ", ".join(obj))
            return ruler(a[0], a[1], b[0], b[1])
        maker = {"box": box, "ellipse": ellipse, "line": line}[kind]
        return maker(a[0], a[1], b[0], b[1], **obj)
    except KeyError as exc:
        raise ValueError("%s: missing/unknown field %s" % (kind, exc))
    except TypeError as exc:
        raise ValueError("%s: %s" % (kind, exc))


def parse_json_document(data):
    """A --json payload: either a plain array of annotation objects, or
    an object {"ppu": N, "unit": U, "note": TEXT, "legend": [LINE, ...],
    "annotations": [...]} (every key optional) so one file carries
    everything.  Each legend LINE is one definition line ("box COLOR
    [STYLE] LABEL...").  Returns (annos, ppu, unit, note, legend);
    raises ValueError on malformed input."""
    if isinstance(data, list):
        return [from_json(obj) for obj in data], None, None, None, None
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
            raise ValueError("\"legend\" must be a non-empty array of "
                             "definition lines")
        legend = legend_lines(legend)
    annos = data.pop("annotations", [])
    if not isinstance(annos, list):
        raise ValueError("\"annotations\" must be an array")
    if data:
        raise ValueError("unknown fields: %s" % ", ".join(sorted(data)))
    return [from_json(obj) for obj in annos], ppu, unit, note, legend


class _AnnoOption(argparse.Action):
    """Collect every --box/--ellipse/... into one list, preserving the
    command-line order (draw order in the viewer)."""

    def __call__(self, parser, namespace, value, option_string=None):
        try:
            namespace.annos.append(parse_anno_option(self.const, value))
        except ValueError as exc:
            parser.error("%s %s: %s" % (option_string, value, exc))


def build_parser():
    parser = argparse.ArgumentParser(
        description="Embed flateyes-compatible annotations into PNGs "
                    "(pixels untouched; flateyes shows them on open), "
                    "or --export them drawn into a copy.")
    parser.add_argument("png", nargs="*", metavar="PNG",
                        help="target PNG files (each gets the same "
                             "annotations)")
    for kind, metavar in (
            ("box", "X1,Y1,X2,Y2[,COLOR[,FILL[,WIDTH[,DASH]]]]"),
            ("ellipse", "X1,Y1,X2,Y2[,COLOR[,FILL[,WIDTH[,DASH]]]]"),
            ("line", "X1,Y1,X2,Y2[,COLOR[,WIDTH[,DASH]]]"),
            ("path", "X1,Y1,X2,Y2[,X3,Y3...][,COLOR[,WIDTH[,DASH]]]"),
            ("polygon", "X1,Y1,X2,Y2,X3,Y3[,X4,Y4...]"
                        "[,COLOR[,FILL[,WIDTH[,DASH]]]]"),
            ("ruler", "X1,Y1,X2,Y2"),
            ("text", "X,Y[,STYLE...],TEXT")):
        parser.add_argument("--" + kind, action=_AnnoOption, const=kind,
                            metavar=metavar, dest="annos",
                            help="add a %s annotation (repeatable; COLOR"
                                 " is a palette name or #RRGGBB)" % kind)
    parser.add_argument("--json", metavar="FILE",
                        help="annotations from a JSON array (\"-\" = "
                             "stdin), appended after the option ones; "
                             "an object {ppu, unit, note, legend, "
                             "annotations} also carries the metadata "
                             "(explicit --ppu/--unit/--note/--legend "
                             "win)")
    parser.add_argument("--legend", metavar="FILE",
                        help="legend definition text file, one entry "
                             "per line (\"#\" comments): \"box COLOR "
                             "[solid|none|hatch|cross|dots|<floe fill "
                             "name>|pat:HEX64] LABEL\" or "
                             "\"line COLOR [solid|dashed|dotted] "
                             "LABEL\"; flateyes draws it as a swatch "
                             "table at the bottom-right (with --append "
                             "it replaces a stored legend)")
    parser.add_argument("--note", metavar="TEXT",
                        help="one free text for the whole image, no "
                             "position or style (flateyes shows it at "
                             "the top-left; a literal \\n breaks the "
                             "line; with --append it replaces a stored "
                             "note)")
    parser.add_argument("--ppu", type=float, metavar="N",
                        help="pixels per unit stored with the "
                             "annotations (ruler scale)")
    parser.add_argument("--unit", metavar="U",
                        help="unit label for --ppu (default: um)")
    parser.add_argument("--append", action="store_true",
                        help="keep annotations already embedded instead "
                             "of replacing them")
    parser.add_argument("--dump", action="store_true",
                        help="print each file's embedded metadata and "
                             "exit")
    parser.add_argument("--strip", action="store_true",
                        help="remove the embedded metadata chunk")
    parser.add_argument("--export", metavar="OUT",
                        help="draw the annotations, rulers, texts and "
                             "note into a new PNG at OUT, the way flateyes "
                             "shows them at 100%% zoom, the legend in a "
                             "panel the image grows to the right for (the "
                             "source is not modified; annotation options "
                             "given here go on top of the embedded ones); "
                             "several PNGs need {stem} or {name} in OUT, "
                             "\"-\" = stdout")
    parser.add_argument("--export-legend", metavar="OUT",
                        help="the legend table alone as a PNG at OUT "
                             "(same OUT rules)")
    parser.add_argument("--scale", type=float, metavar="S",
                        help="export decoration size: 1 = flateyes at "
                             "100%% zoom (default), 2 = strokes, labels "
                             "and legend twice as big (large images)")
    parser.add_argument("--legend-bg", metavar="COLOR",
                        help="export legend panel/image background: "
                             "palette name, #RRGGBB or none (transparent);"
                             " default black")
    parser.add_argument("--hide", action="append", metavar="KIND[,KIND]",
                        help="leave out of --export: shapes, texts, "
                             "rulers, note, legend")
    parser.add_argument("--font", action="append", metavar="FILE[:N]",
                        help="TTF/OTF/TTC font for exported text, tried "
                             "before the system fonts (fontconfig); :N "
                             "picks a collection face; repeatable")
    parser.add_argument("--selftest", action="store_true",
                        help="round-trip check (cross-checks against "
                             "flateyes.py when it is importable)")
    parser.set_defaults(annos=[])
    return parser


def _export_target(template, source):
    """--export/--export-legend OUT for one source PNG, {stem}/{name}/
    {dir} filled in; "-" stays stdout."""
    if template == "-":
        return template
    name = os.path.basename(source)
    try:
        target = template.format(stem=os.path.splitext(name)[0], name=name,
                                 dir=os.path.dirname(source) or ".")
    except (KeyError, IndexError, ValueError):
        raise ValueError("bad output path %s (placeholders: {stem}, "
                         "{name}, {dir})" % template)
    if os.path.abspath(target) == os.path.abspath(source) \
            or (os.path.exists(target) and os.path.samefile(target, source)):
        raise ValueError("refusing to overwrite the source with its "
                         "export (%s)" % template)
    return target


def export_main(parser, args, annos, ppu, unit, note, legend):
    """--export/--export-legend for every PNG; a file that fails is
    reported and the rest still run (exit status 1)."""
    outputs = [t for t in (args.export, args.export_legend) if t is not None]
    if outputs.count("-") > 1:
        parser.error("only one export can go to stdout (-)")
    if len(args.png) > 1:
        for template in outputs:
            if template == "-" or not ("{stem}" in template
                                       or "{name}" in template):
                parser.error("%s: several PNGs need {stem} or {name} in "
                             "the output path" % template)
    hide = set()
    for value in args.hide or ():
        hide.update(v.strip().lower() for v in value.split(",") if v.strip())
    options = {"scale": 1.0 if args.scale is None else args.scale,
               "legend_bg": args.legend_bg or "black", "fonts": args.font}
    try:
        _export_options(options["scale"], options["legend_bg"], hide)
        fonts = _font_set(args.font)
    except ValueError as exc:
        parser.error(str(exc))
    log = sys.stderr if "-" in outputs else sys.stdout

    def image(blob):
        return export_bytes(blob, annos, ppu, unit, note, legend, hide=hide,
                            **options)

    def legend_only(blob):
        lines = legend or read_bytes(blob)[4]
        if not lines:
            raise ValueError("no legend to export")
        return legend_bytes(lines, **options)

    jobs = [(t, what, make) for t, what, make in
            ((args.export, "", image),
             (args.export_legend, "legend ", legend_only)) if t is not None]
    status = 0
    for path in args.png:
        try:
            with open(path, "rb") as handle:
                blob = handle.read()
        except OSError as exc:
            sys.stderr.write("%s: %s\n" % (path, exc))
            status = 1
            continue
        for template, what, make in jobs:   # each output on its own
            try:
                target = _export_target(template, path)
                png = make(blob)
                if target == "-":
                    sys.stdout.buffer.write(png)
                    sys.stdout.flush()
                else:
                    _write_new(target, png)
                log.write("%s -> %s (%s%dx%d)\n"
                          % ((path, target, what)
                             + struct.unpack(">II", png[16:24])))
            except (OSError, ValueError) as exc:
                sys.stderr.write("%s: %s\n" % (path, exc))
                status = 1
        for warning in fonts.warnings():
            sys.stderr.write("warning: %s\n" % warning)
    return status


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.selftest:
        return selftest()
    if not args.png:
        parser.error("no PNG files given")
    exporting = args.export is not None or args.export_legend is not None
    if exporting and (args.dump or args.strip):
        parser.error("--export/--export-legend cannot be combined with "
                     "--dump/--strip")
    if not exporting and (args.scale is not None or args.hide or args.font
                          or args.legend_bg is not None):
        parser.error("--scale/--legend-bg/--hide/--font need --export or "
                     "--export-legend")
    if args.dump:
        for path in args.png:
            try:
                with open(path, "rb") as handle:
                    text = extract_text(handle.read())
            except (OSError, ValueError) as exc:
                sys.stderr.write("%s: %s\n" % (path, exc))
                return 1
            if len(args.png) > 1:
                sys.stdout.write("==> %s <==\n" % path)
            sys.stdout.write(text if text is not None
                             else "(no embedded metadata)\n")
        return 0
    if args.strip:
        if args.annos or args.json or args.ppu or args.note or args.legend:
            parser.error("--strip takes no annotations")
        for path in args.png:
            try:
                strip(path)
                sys.stdout.write("%s: metadata removed\n" % path)
            except (OSError, ValueError) as exc:
                sys.stderr.write("%s: %s\n" % (path, exc))
                return 1
        return 0
    annos = list(args.annos)
    json_ppu = json_unit = json_note = json_legend = None
    if args.json:
        try:
            if args.json == "-":
                data = json.load(sys.stdin)
            else:
                with open(args.json, "r", encoding="utf-8") as handle:
                    data = json.load(handle)
            extra, json_ppu, json_unit, json_note, json_legend = \
                parse_json_document(data)
            annos.extend(extra)
        except (OSError, ValueError) as exc:
            sys.stderr.write("--json %s: %s\n" % (args.json, exc))
            return 1
    file_legend = None
    if args.legend:
        try:
            with open(args.legend, "r", encoding="utf-8") as handle:
                raw = [l.strip() for l in handle.read().splitlines()]
            file_legend = legend_lines(l for l in raw
                                       if l and not l.startswith("#"))
            if not file_legend:
                raise ValueError("empty legend")
        except (OSError, UnicodeDecodeError, ValueError) as exc:
            sys.stderr.write("--legend %s: %s\n" % (args.legend, exc))
            return 1
    # explicit command-line values win over the JSON document's
    ppu = args.ppu if args.ppu is not None else json_ppu
    unit = args.unit or json_unit
    note = unescape_meta(args.note) if args.note else json_note
    legend = file_legend or json_legend
    if exporting:
        return export_main(parser, args, annos, ppu, unit, note, legend)
    unit = unit or "um"
    if not annos and not ppu and not note and not legend \
            and not args.append:
        parser.error("no annotations given (use --strip to remove)")
    for path in args.png:
        try:
            embed(path, annos, ppu, unit, args.append, note, legend)
        except (OSError, ValueError) as exc:
            sys.stderr.write("%s: %s\n" % (path, exc))
            return 1
        sys.stdout.write("%s: %d annotation%s embedded%s\n"
                         % (path, len(annos),
                            "" if len(annos) == 1 else "s",
                            " (appended)" if args.append else ""))
    return 0


# ---------------------------------------------------------------------------
# selftest — drift alarm between this file and flateyes.py
# ---------------------------------------------------------------------------

def _sample_png(width=4, height=4):
    def chunk(ctype, data):
        return (struct.pack(">I", len(data)) + ctype + data
                + struct.pack(">I", zlib.crc32(ctype + data)))
    raw = b"".join(b"\x00" + b"\x30\x60\x90\xff" * width
                   for _ in range(height))
    return (PNG_SIGNATURE
            + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height,
                                         8, 6, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw))
            + chunk(b"IEND", b""))


def _sample_annos():
    return [
        box(10, 20, 200, 120, color="red", width=2),
        box(30, 40, 90, 80, fill="orange", fill_alpha=255,
            outline=False),
        box(-60, -50, -10, -5, fill="sky", fill_alpha=0x30),
        box(-60, 0, -10, 45, fill="#80808080"),   # AA inside the value
        box(-60, 50, -10, 95, fill="#80808040", fill_alpha=200),
        ellipse(50.5, 60.25, 150, 160, color="#123ABC", fill="sky",
                dash="dashed", casing=False),
        line(0, 0, 199, 99, color="green", width=8, dash="dotted"),
        path([(5, 5), (60, 40.5), (60, 90), (110.25, 90)],
             color="pink", width=3, dash="dashed"),
        path([(0, 0), (10, 10)], casing=False),
        polygon([(100, 10), (150, 60), (125.5, 90), (75, 60)],
                color="sky", fill="sky", fill_alpha=0x30, width=2),
        polygon([(10, 100), (40, 100), (25, 130)], fill="orange",
                outline=False),
        polygon([(60, 100), (90, 100), (90, 130), (60, 130)],
                color="red", fill="#FF5252", fill_pat="speckle",
                width=2, casing=False),   # opaque pattern fill
        polygon([(100, 100), (130, 100), (115, 130)],
                fill="#00E67680:brick"),  # pattern via fill suffix
        ruler(5, 5, 105, 5),
        text(12, 14, "DEFECT #17\n불량 위치\\메모", size=20,
             color="white", bg_color="black", bg_opaque=True),
        text(40, 90, "plain", bg=False),
    ]


def _ref_png(width, height, color, depth, pixels, plte=None, trns=None,
             interlace=0):
    """An independent, deliberately plain PNG writer for the decoder
    check: samples packed MSB first, filter types 0-4 in rotation,
    optional Adam7 passes.  pixels[y][x] is a tuple of samples."""
    bpp = max(1, _PNG_CHANNELS[color] * depth // 8)

    def pack(samples):
        if depth == 16:
            return b"".join(struct.pack(">H", v) for v in samples)
        out, acc, bits = bytearray(), 0, 0
        for v in samples:
            acc, bits = (acc << depth) | v, bits + depth
            if bits == 8:
                out.append(acc)
                acc, bits = 0, 0
        if bits:
            out.append(acc << (8 - bits))
        return bytes(out)

    def paeth(a, b, c):
        p = a + b - c
        pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
        return a if pa <= pb and pa <= pc else (b if pb <= pc else c)

    raw = bytearray()
    kind = 0
    for x0, y0, dx, dy in (_ADAM7 if interlace else ((0, 0, 1, 1),)):
        xs, ys = range(x0, width, dx), range(y0, height, dy)
        if not xs or not ys:
            continue
        prev = None
        for y in ys:
            line = pack([v for x in xs for v in pixels[y][x]])
            prev = prev or bytes(len(line))
            raw.append(kind)
            for i, v in enumerate(line):
                a = line[i - bpp] if i >= bpp else 0
                c = prev[i - bpp] if i >= bpp else 0
                guess = (0, a, prev[i], (a + prev[i]) >> 1,
                         paeth(a, prev[i], c))[kind]
                raw.append((v - guess) & 0xFF)
            prev = line
            kind = (kind + 1) % 5
    chunks = [(b"IHDR", struct.pack(">IIBBBBB", width, height, depth, color,
                                    0, 0, interlace))]
    if plte:
        chunks.append((b"PLTE", plte))
    if trns:
        chunks.append((b"tRNS", trns))
    chunks += [(b"IDAT", zlib.compress(bytes(raw))), (b"IEND", b"")]
    return PNG_SIGNATURE + b"".join(_png_chunk(t, b) for t, b in chunks)


def _selftest_export(check):
    """The export machinery: decoder against _ref_png in every color
    type/depth/filter/interlace shape, encoder round trip, then the
    rendering itself (built-in face, so the pixels are deterministic)."""
    plte = b"\x10\x20\x30\x40\x50\x60\x70\x80\x90\xa0\xb0\xc0"
    cases = [
        ("RGB 8", 13, 7, 2, 8, None, None, 0,
         lambda x, y: (x * 19 & 255, y * 37 & 255, x * y * 7 & 255),
         lambda s: s + (255,)),
        ("RGBA 16 interlaced", 9, 9, 6, 16, None, None, 1,
         lambda x, y: (x * 7000, y * 7000, (x + y) * 3000, 65535 - x * 5000),
         lambda s: tuple(v >> 8 for v in s)),
        ("gray 1", 10, 3, 0, 1, None, None, 0,
         lambda x, y: ((x + y) % 2,), lambda s: (s[0] * 255,) * 3 + (255,)),
        ("gray 4 + tRNS key", 7, 5, 0, 4, None, b"\x00\x05", 1,
         lambda x, y: ((x * 3 + y) % 16,),
         lambda s: (s[0] * 17,) * 3 + (0 if s[0] == 5 else 255,)),
        ("palette 2 + tRNS", 11, 4, 3, 2, plte, b"\x00\x80", 0,
         lambda x, y: ((x + 2 * y) % 4,),
         lambda s: tuple(plte[3 * s[0]:3 * s[0] + 3])
         + ((0, 0x80)[s[0]] if s[0] < 2 else 255,)),
        ("gray+alpha 8 interlaced", 11, 6, 4, 8, None, None, 1,
         lambda x, y: (x * 20, y * 40), lambda s: (s[0],) * 3 + (s[1],)),
        ("RGB 16 + tRNS key", 6, 6, 2, 16, None,
         struct.pack(">3H", 1000, 2000, 3000), 0,
         lambda x, y: (1000, 2000, 3000) if (x + y) % 3 == 0
         else (1000, 2000, 3001),
         lambda s: (3, 7, 11, 0 if s[2] == 3000 else 255)),
    ]
    for label, w, h, color, depth, pal, trns, inter, make, expect in cases:
        pixels = [[make(x, y) for x in range(w)] for y in range(h)]
        try:
            got = _png_decode(_ref_png(w, h, color, depth, pixels, pal, trns,
                                       inter))
        except ValueError as exc:
            got = (None, None, str(exc))
        want = bytearray()
        for row in pixels:
            for sample in row:
                want.extend(expect(sample))
        check("png decode: %s" % label, got[:3] == (w, h, want))
    rgba = bytearray((x * 7 + y * 3 + (x * y) % 11) & 255
                     for y in range(17) for x in range(4 * 23))
    back = _png_decode(_png_encode(23, 17, rgba, True))
    opaque = bytearray(rgba)
    opaque[3::4] = b"\xff" * (23 * 17)
    back_rgb = _png_decode(_png_encode(23, 17, opaque, False))
    check("png encode round trip (RGBA, RGB)",
          back[:4] == (23, 17, rgba, True)
          and back_rgb[:4] == (23, 17, opaque, False))

    builtin = _Fonts(system=False)
    w, h = 160, 120
    base = _png_encode(w, h, bytearray(b"\x30\x60\x90\xff") * (w * h), False)
    src = embed_bytes(base, [box(-50, -40, -10, -10, color="red", width=2),
                             ruler(-60, 30, 60, 30),
                             text(0, -50, "Ag", size=10, color="white")],
                      ppu=2.0, note="note",
                      legend=["box red solid metal", "line sky dashed route"])
    out = export_bytes(src, fonts=builtin)
    ow, oh, px, alpha, _ = _png_decode(out)

    def pixel(x, y):
        return tuple(px[(y * ow + x) * 4:(y * ow + x) * 4 + 4])

    check("export: legend panel grows the image right",
          ow > w and oh == h and not alpha
          and pixel(ow - 1, 0) == (0, 0, 0, 255)
          and any(pixel(x, y) == (0xFF, 0x50, 0x40, 255)
                  for x in range(w, ow) for y in range(oh)))
    check("export: shapes and rulers drawn, the rest untouched",
          pixel(29, 35) == (0xFF, 0x50, 0x40, 255)
          and pixel(80, 90) == (255, 255, 255, 255)
          and pixel(150, 110) == (0x30, 0x60, 0x90, 255))
    check("export: text drawn",
          any(pixel(x, y) == (255, 255, 255, 255)
              for x in range(80, 110) for y in range(10, 30)))
    check("export keeps only ppu/unit metadata",
          extract_text(out) == "# flateyes annotations\nppu=2\nunit=um\n")
    hidden = _png_decode(export_bytes(src, hide=("legend", "note", "texts"),
                                      fonts=builtin))
    check("export --hide legend keeps the size", hidden[:2] == (w, h))
    check("export of an unannotated PNG keeps the pixels",
          _png_decode(export_bytes(base, fonts=builtin))[2]
          == _png_decode(base)[2])
    lone = _png_decode(legend_bytes(["box red solid metal"], scale=2,
                                    legend_bg="none", fonts=builtin))
    check("legend alone (scale 2, transparent backdrop)",
          lone[3] and lone[0] > 70 and lone[1] > 28
          and b"\xff\x50\x40\xff" in bytes(lone[2]))
    system = _Fonts()
    face, gid = system.lookup(u"가")
    if face is None:
        sys.stdout.write("  --  no system font with Hangul; "
                         "TrueType/CFF render check skipped\n")
    else:
        hit = system.coverage(face, gid, 24.0, 0.0, 0)
        check("system font renders Hangul (%s)" % os.path.basename(face.path),
              hit is not None and max(hit[4]) == 255)


def selftest():
    failures = []

    def check(label, ok):
        if not ok:
            failures.append(label)
        sys.stdout.write("  %s %s\n" % ("ok " if ok else "FAIL", label))

    annos = _sample_annos()
    sample_note = "capture rig #3\n확인 요망"
    sample_legend = ["box #3DDC55 none pwell",
                     "box green hatch 산화막 layer",
                     "box #FFFF66 dots via",
                     "box sky solid dots",   # label = a style word
                     "box #D6FF3F pat:%s M4 fill" % ("aaaa5555" * 8),
                     "box #FF3F3F speckle BOUNDARY 0/0",
                     "box pink clear NW 3/0",   # floe clear -> none
                     "line red dashed metal route",
                     "line #35C5FF boundary"]
    blob = _sample_png()
    stamped = embed_bytes(blob, annos, ppu=8.5, unit="um",
                          note=sample_note, legend=sample_legend)
    got, ppu, unit, note, legend = read_bytes(stamped)
    check("round-trip count", len(got) == len(annos))
    check("round-trip ppu/unit/note",
          ppu == 8.5 and unit == "um" and note == sample_note)
    check("round-trip lines",
          [serialize_anno(a) for a in got]
          == [serialize_anno(a) for a in annos])
    check("round-trip legend (canonical form)",
          legend == legend_lines(sample_legend)
          and legend == legend_lines(legend))
    appended = embed_bytes(stamped, [text(1, 1, "late")], append=True,
                           note="replaced",
                           legend=["box red solid rework"])
    got2, ppu2, _, note2, legend2 = read_bytes(appended)
    check("append keeps old + ppu, replaces note + legend",
          len(got2) == len(annos) + 1 and ppu2 == 8.5
          and got2[-1]["text"] == "late" and note2 == "replaced"
          and legend2 == ["box #FF5040 solid rework"])
    check("strip restores original bytes",
          insert_text(stamped, None) == blob)
    _selftest_export(check)

    tried_flateyes = False
    try:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import flateyes
        tried_flateyes = True
    except Exception as exc:  # ImportError and any import-time surprise
        sys.stdout.write("  --  flateyes.py not importable (%s); "
                         "cross-check skipped\n" % exc)
    if tried_flateyes:
        tmpdir = tempfile.mkdtemp(prefix="fe-embed-test-")
        target = os.path.join(tmpdir, "sample.png")
        try:
            with open(target, "wb") as handle:
                handle.write(stamped)
            theirs = flateyes.read_png_metadata(target)
            check("flateyes reads our chunk",
                  theirs == extract_text(stamped))
            stub = object.__new__(flateyes.Viewer)
            stub.ppu, stub.unit, stub.stack_mode = 8.5, "um", False
            stub.note = sample_note
            stub.annotations = annos
            stub.legend_entries = [flateyes.parse_legend_entry(l)[0]
                                   for l in legend]
            check("flateyes serializes the same chunk",
                  "# flateyes annotations\n"
                  + "\n".join(stub.serialize_annotations()) + "\n"
                  == extract_text(stamped))
            check("legend lines parse identically in flateyes",
                  [flateyes.serialize_legend_entry(
                      flateyes.parse_legend_entry(l)[0]) for l in legend]
                  == legend
                  and [flateyes.parse_legend_entry(l)[0] for l in legend]
                  == [parse_legend_line(l) for l in legend])
            lines = [l for l in (theirs or "").splitlines()
                     if l and not l.startswith("#")
                     and not l.startswith(("ppu=", "unit=", "note=",
                                           "legend="))]
            mirrored = []
            for entry in lines:
                key, _, value = entry.partition("=")
                parsed = flateyes.Viewer.parse_anno_line(key, value)
                mirrored.append(flateyes.Viewer.serialize_anno(parsed))
            check("flateyes re-serializes identically", mirrored == lines)
            check("our parse matches flateyes parse",
                  [parse_anno_line(l.partition("=")[0],
                                   l.partition("=")[2]) for l in lines]
                  == [flateyes.Viewer.parse_anno_line(
                      l.partition("=")[0], l.partition("=")[2])
                      for l in lines])
            options = [
                ("box", "10,20,200,120,red,0,2"),
                ("box", "30,40,90,80,0,orange"),
                ("box", "-60,-50,-10,-5,sky,#35C5FF30"),
                ("box", "-60,0,-10,45,red,#80808080"),
                ("ellipse", "50.5,60.25,150,160,#123ABC,sky,1,dashed"),
                ("line", "0,0,199,99,green,8,dotted"),
                ("path", "5,5,60,40.5,60,90,110.25,90,pink,3,dashed"),
                ("path", "0,0,10,10,20,0"),
                ("polygon", "100,10,150,60,125.5,90,75,60,sky,"
                            "#35C5FF30,2"),
                ("polygon", "10,100,40,100,25,130,0,orange"),
                ("polygon", "60,100,90,100,90,130,60,130,red,"
                            "red:speckle,2"),
                ("polygon", "100,100,130,100,115,130,0,"
                            "#00E67680:brick"),
                ("ruler", "5,5,105,5"),
                ("text", "12,14,DEFECT #17"),
                ("text", "12,14,size=20,color=white,bg=#000000FF,A"),
                ("text", "12,14,bg=sky,반투명 배경"),
                ("text", "12,14,bg=0,label only"),
                ("text", "12,14,text=size=6 is tiny, right"),
            ]
            check("CLI options parse identically",
                  [serialize_anno(parse_anno_option(k, v))
                   for k, v in options]
                  == [flateyes.Viewer.serialize_anno(
                      flateyes.Viewer.parse_anno_option(k, v))
                      for k, v in options])
            jsons = [
                {"kind": "box", "x1": 5, "y1": 5, "x2": 40, "y2": 30,
                 "color": "sky", "fill": "sky", "width": 2},
                {"kind": "ellipse", "a": [1, 2], "b": [30, 40],
                 "fill": "#FF9F1A", "fill_alpha": 255,
                 "outline": False},
                {"kind": "box", "x1": -60, "y1": -50, "x2": -10,
                 "y2": -5, "fill": "sky", "fill_alpha": 48},
                {"kind": "box", "x1": -60, "y1": 0, "x2": -10,
                 "y2": 45, "fill": "#80808080"},
                {"kind": "polygon",
                 "points": [[0, 0], [40, 0], [20, 30]],
                 "fill": "#80808040", "fill_alpha": 200},
                {"kind": "line", "x1": 0, "y1": 0, "x2": 9, "y2": 9,
                 "dash": "dotted", "casing": False},
                {"kind": "path", "points": [[1, 2], [30, 2], [30, 44]],
                 "color": "orange", "width": 2, "dash": "dashed"},
                {"kind": "polygon",
                 "points": [[100, 10], [150, 60], [125.5, 90], [75, 60]],
                 "color": "sky", "fill": "sky", "fill_alpha": 48,
                 "width": 2},
                {"kind": "polygon",
                 "points": [[10, 100], [40, 100], [25, 130]],
                 "fill": "orange", "outline": False},
                {"kind": "polygon",
                 "points": [[60, 100], [90, 100], [90, 130], [60, 130]],
                 "color": "red", "fill": "#FF5252",
                 "fill_pat": "speckle", "width": 2, "casing": False},
                {"kind": "polygon",
                 "points": [[100, 100], [130, 100], [115, 130]],
                 "fill": "#00E67680:brick"},
                {"kind": "ruler", "x1": 1, "y1": 1, "x2": 8, "y2": 1},
                {"kind": "text", "x": 5, "y": 32, "text": "불량 A",
                 "size": 12, "color": "white", "bg_opaque": True},
                {"kind": "text", "at": [7, 8], "text": "no bg",
                 "bg": False},
            ]
            check("JSON entries parse identically",
                  [serialize_anno(from_json(dict(o))) for o in jsons]
                  == [flateyes.Viewer.serialize_anno(
                      flateyes.Viewer.parse_anno_json(dict(o)))
                      for o in jsons])
            doc = {"ppu": 8.5, "unit": "um", "note": "문서 노트",
                   "legend": sample_legend, "annotations": jsons}
            ours = parse_json_document(dict(doc))
            theirs = flateyes.Viewer.parse_json_document(dict(doc))
            check("JSON document parses identically",
                  ours[1:4] == theirs[1:4] == (8.5, "um", "문서 노트")
                  and [serialize_anno(a) for a in ours[0]]
                  == [flateyes.Viewer.serialize_anno(a)
                      for a in theirs[0]]
                  and ours[4]
                  == [flateyes.serialize_legend_entry(e)
                      for e in theirs[4]])
            flateyes.write_png_metadata(target, "# flateyes annotations\n"
                                        + "\n".join(lines) + "\n")
            with open(target, "rb") as handle:
                ours = extract_text(handle.read())
            check("we read flateyes' chunk",
                  ours is not None
                  and [l for l in ours.splitlines()
                       if l and not l.startswith("#")] == lines)
            # the export's ports of the viewer's ruler readout: wording
            # and label placement must match at scale 1
            readouts = []
            for ppu_, dist in ((None, 299.6), (8.5, 300.0), (48000, 3.0),
                               (0.8, 12345.0)):
                stub.ppu, stub.unit = ppu_, "um"
                readouts.append(stub.format_distance(dist)
                                == format_distance(dist, ppu_, "um"))
            check("ruler readout worded like flateyes", all(readouts))
            view = type("View", (), {"width": 640, "height": 480})()
            rulers = [((100.0, 120.0), (420.0, 120.0)),
                      ((260.0, 40.0), (260.0, 300.0)),
                      ((120.0, 300.0), (400.0, 60.0)),
                      ((600.0, 470.0), (630.0, 400.0))]
            spots, theirs_spots = [], []
            for mine in (True, False):
                placed, leaders = [], []
                for idx, (a, b) in enumerate(rulers):
                    others = rulers[:idx] + rulers[idx + 1:]
                    if mine:
                        spot = _pick_ruler_label_spot(
                            a, b, 120, 22, placed, leaders, others,
                            (640, 480), 1.0)
                    else:
                        spot = stub.pick_ruler_label_spot(
                            a, b, 120, 22, placed, leaders, others, view)
                    rect = (spot[0], spot[1], spot[0] + 120, spot[1] + 22)
                    placed.append(rect)
                    seg = _ruler_leader_seg(a, b, rect)
                    if seg is not None:
                        leaders.append(seg)
                    (spots if mine else theirs_spots).append(spot)
            single = _avoid_label_overlap(500, -10, 120, 22, [], (640, 480),
                                          1.0)
            check("ruler labels placed like flateyes",
                  spots == theirs_spots and single
                  == stub.avoid_label_overlap(500, -10, 120, 22, [], view))
            # ellipse outlines: small, and zoomed far past the view
            ellipses = ((320.0, 240.0, 150.0, 90.0, 0, 1, 1),
                        (300.0, 200.0, 40.0, 25.0, 1, 6, 11),
                        (5000.0, 240.0, 4800.0, 3000.0, 0, 1, 1),
                        (-900.0, 9000.0, 9500.0, 8800.0, 2, 1, 6))
            check("ellipse outlines sampled like flateyes",
                  all(_ellipse_dabs(ex, ey, erx, ery, 640, 480, 4, d, on, p)
                      == flateyes.Viewer.ellipse_dabs(ex, ey, erx, ery,
                                                      640, 480, 4, d, on, p)
                      for ex, ey, erx, ery, d, on, p in ellipses))
        finally:
            try:
                os.unlink(target)
            except OSError:
                pass
            try:
                os.rmdir(tmpdir)
            except OSError:
                pass
    if failures:
        sys.stdout.write("selftest FAILED: %s\n" % ", ".join(failures))
        return 1
    sys.stdout.write("selftest OK (flateyes cross-check: %s)\n"
                     % ("yes" if tried_flateyes else "skipped"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
