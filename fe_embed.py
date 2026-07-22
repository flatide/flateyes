#!/usr/bin/env python3
"""Embed flateyes-compatible annotations into PNG files.

Standalone companion to flateyes.py for services that produce PNGs in
bulk (e.g. automated capture) and want each file to carry its markers
(boxes, ellipses, lines, texts, rulers) the moment it is written.
flateyes then shows them on open, and Ctrl+S keeps editing the same
chunk.  Python standard library only — deployment is copying this one
file, same as flateyes.py itself.

The annotation metadata lives inside the PNG as an iTXt chunk (UTF-8,
keyword "flateyes") inserted before IEND.  Decoders must skip unknown
ancillary chunks, so the file stays a plain PNG for every other tool;
pixels are never touched.  Coordinates are image pixels (origin top
left), so they are independent of any viewer zoom.

Library use:

    import fe_embed as fe
    fe.embed("shot_0001.png", [
        fe.box(120, 80, 420, 300, color="red", width=2),
        fe.text(120, 60, "DEFECT #17", size=20, color="white"),
    ], ppu=8.0, unit="um")

    blob = fe.embed_bytes(png_bytes, annos)   # in-memory pipelines
    annos, ppu, unit = fe.read("shot_0001.png")

CLI use (same option syntax as flateyes itself):

    python3 fe_embed.py --box 120,80,420,300,red,0,2 \
                        --text '120,60,size=20,color=white,DEFECT #17' \
                        shot_*.png
    python3 fe_embed.py --json annos.json shot_0001.png
    python3 fe_embed.py --dump shot_0001.png

Format contract: the chunk layout and the key=value line format mirror
flateyes.py (serialize_anno / parse_anno_line / write_png_metadata).
After changing the format on either side, run

    python3 fe_embed.py --selftest

next to flateyes.py — it round-trips every annotation kind through both
implementations and fails loudly on drift.
"""

import argparse
import json
import os
import struct
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


def _dash(value):
    if isinstance(value, str) and value.lower() in DASHES:
        return DASHES[value.lower()]
    if value in (0, 1, 2):
        return int(value)
    raise ValueError("dash must be solid/dashed/dotted (or 0/1/2), got: %r"
                     % (value,))


def _shape(kind, x1, y1, x2, y2, color, fill, fill_opaque, outline,
           width, dash, casing):
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
    if fill is not None:
        anno["fill"] = _color(fill, "fill")
        anno["fill_opaque"] = bool(fill_opaque)
    if not outline:
        if fill is None:
            raise ValueError("outline=False needs a fill")
        anno["outline"] = False
    return anno


def box(x1, y1, x2, y2, color=DEFAULT_LINE, fill=None, fill_opaque=False,
        outline=True, width=1, dash="solid", casing=True):
    """Rectangle from (x1,y1) to (x2,y2) in image pixels."""
    return _shape("box", x1, y1, x2, y2, color, fill, fill_opaque,
                  outline, width, dash, casing)


def ellipse(x1, y1, x2, y2, color=DEFAULT_LINE, fill=None,
            fill_opaque=False, outline=True, width=1, dash="solid",
            casing=True):
    """Ellipse inscribed in the (x1,y1)-(x2,y2) rectangle."""
    return _shape("ellipse", x1, y1, x2, y2, color, fill, fill_opaque,
                  outline, width, dash, casing)


def line(x1, y1, x2, y2, color=DEFAULT_LINE, width=1, dash="solid",
         casing=True):
    """Straight line segment."""
    return _shape("line", x1, y1, x2, y2, color, None, False, True,
                  width, dash, casing)


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


def serialize_anno(anno):
    """One annotation dict as its key=value metadata line."""
    if anno["kind"] == "ruler":
        return ("ruler=%.10g,%.10g,%.10g,%.10g"
                % (anno["a"][0], anno["a"][1], anno["b"][0], anno["b"][1]))
    color = anno.get("color", DEFAULT_LINE)
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
        fill = "%s%02X" % (anno["fill"], 255 if anno.get("fill_opaque")
                           else TRANSLUCENT_ALPHA)
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


def serialize(annos, ppu=None, unit="um"):
    """The full chunk text, or None when there is nothing to store."""
    lines = []
    if ppu:
        if float(ppu) <= 0:
            raise ValueError("ppu must be > 0")
        lines.append("ppu=%.10g" % float(ppu))
        lines.append("unit=%s" % unit)
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
            anno["fill_opaque"] = int(fill[7:9], 16) >= 0x80
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
    """Chunk text -> (annotations, ppu, unit); malformed lines skipped
    like flateyes does."""
    annos, ppu, unit = [], None, None
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
            elif key in ("box", "ellipse", "line", "ruler", "text"):
                annos.append(parse_anno_line(key, value))
        except ValueError:
            continue
    return annos, ppu, unit


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


def _combine(existing, annos, ppu, unit):
    """Chunk text for append mode: keep the lines already embedded, but
    a newly given ppu replaces the stored ppu/unit pair."""
    kept = []
    for raw in (existing or "").splitlines():
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if ppu and (stripped.startswith("ppu=")
                    or stripped.startswith("unit=")):
            continue
        kept.append(stripped)
    fresh = (serialize(annos, ppu, unit) or "").splitlines()[1:]
    lines = (fresh[:2] if ppu else []) + kept + (fresh[2:] if ppu else fresh)
    if not lines:
        return None
    return "# flateyes annotations\n" + "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# public entry points
# ---------------------------------------------------------------------------

def embed_bytes(blob, annos, ppu=None, unit="um", append=False):
    """PNG bytes with the given annotations embedded.  With append=True
    they are added after any already-embedded ones; otherwise the chunk
    is replaced.  Empty input (and not appending) removes the chunk."""
    if append:
        text = _combine(extract_text(blob), annos, ppu, unit)
    else:
        text = serialize(annos, ppu, unit)
    return insert_text(blob, text)


def embed(path, annos, ppu=None, unit="um", append=False):
    """Embed annotations into the PNG at path (atomic tmp + os.replace,
    so an interrupted write never corrupts the capture)."""
    with open(path, "rb") as handle:
        blob = handle.read()
    out = embed_bytes(blob, annos, ppu, unit, append)
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
    """(annotations, ppu, unit) embedded in PNG bytes."""
    return parse_metadata(extract_text(blob))


def read(path):
    """(annotations, ppu, unit) embedded in the PNG at path."""
    with open(path, "rb") as handle:
        return read_bytes(handle.read())


def strip(path):
    """Remove the embedded metadata chunk, if any."""
    embed(path, [])


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
    if rest and kind != "line":  # 6th: fill, #RRGGBBAA makes it opaque
        fill = rest.pop(0)
        if fill.startswith("#") and len(fill) == 9:
            try:
                int(fill[1:9], 16)
            except ValueError:
                raise ValueError("bad fill: %s" % fill)
            kwargs["fill"] = fill[:7]
            kwargs["fill_opaque"] = int(fill[7:9], 16) >= 0x80
        elif fill not in ("", "0"):
            kwargs["fill"] = fill
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
                    "(pixels untouched; flateyes shows them on open).")
    parser.add_argument("png", nargs="*", metavar="PNG",
                        help="target PNG files (each gets the same "
                             "annotations)")
    for kind, metavar in (
            ("box", "X1,Y1,X2,Y2[,COLOR[,FILL[,WIDTH[,DASH]]]]"),
            ("ellipse", "X1,Y1,X2,Y2[,COLOR[,FILL[,WIDTH[,DASH]]]]"),
            ("line", "X1,Y1,X2,Y2[,COLOR[,WIDTH[,DASH]]]"),
            ("ruler", "X1,Y1,X2,Y2"),
            ("text", "X,Y[,STYLE...],TEXT")):
        parser.add_argument("--" + kind, action=_AnnoOption, const=kind,
                            metavar=metavar, dest="annos",
                            help="add a %s annotation (repeatable; COLOR"
                                 " is a palette name or #RRGGBB)" % kind)
    parser.add_argument("--json", metavar="FILE",
                        help="annotations from a JSON array (\"-\" = "
                             "stdin); appended after the option ones")
    parser.add_argument("--ppu", type=float, metavar="N",
                        help="pixels per unit stored with the "
                             "annotations (ruler scale)")
    parser.add_argument("--unit", default="um", metavar="U",
                        help="unit label for --ppu (default: um)")
    parser.add_argument("--append", action="store_true",
                        help="keep annotations already embedded instead "
                             "of replacing them")
    parser.add_argument("--dump", action="store_true",
                        help="print each file's embedded metadata and "
                             "exit")
    parser.add_argument("--strip", action="store_true",
                        help="remove the embedded metadata chunk")
    parser.add_argument("--selftest", action="store_true",
                        help="round-trip check (cross-checks against "
                             "flateyes.py when it is importable)")
    parser.set_defaults(annos=[])
    return parser


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.selftest:
        return selftest()
    if not args.png:
        parser.error("no PNG files given")
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
        if args.annos or args.json or args.ppu:
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
    if args.json:
        try:
            if args.json == "-":
                data = json.load(sys.stdin)
            else:
                with open(args.json, "r", encoding="utf-8") as handle:
                    data = json.load(handle)
            if not isinstance(data, list):
                raise ValueError("expected a JSON array")
            annos.extend(from_json(obj) for obj in data)
        except (OSError, ValueError) as exc:
            sys.stderr.write("--json %s: %s\n" % (args.json, exc))
            return 1
    if not annos and not args.ppu and not args.append:
        parser.error("no annotations given (use --strip to remove)")
    for path in args.png:
        try:
            embed(path, annos, args.ppu, args.unit, args.append)
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
        box(30, 40, 90, 80, fill="orange", fill_opaque=True,
            outline=False),
        ellipse(50.5, 60.25, 150, 160, color="#123ABC", fill="sky",
                dash="dashed", casing=False),
        line(0, 0, 199, 99, color="green", width=8, dash="dotted"),
        ruler(5, 5, 105, 5),
        text(12, 14, "DEFECT #17\n불량 위치\\메모", size=20,
             color="white", bg_color="black", bg_opaque=True),
        text(40, 90, "plain", bg=False),
    ]


def selftest():
    failures = []

    def check(label, ok):
        if not ok:
            failures.append(label)
        sys.stdout.write("  %s %s\n" % ("ok " if ok else "FAIL", label))

    annos = _sample_annos()
    blob = _sample_png()
    stamped = embed_bytes(blob, annos, ppu=8.5, unit="um")
    got, ppu, unit = read_bytes(stamped)
    check("round-trip count", len(got) == len(annos))
    check("round-trip ppu/unit", ppu == 8.5 and unit == "um")
    check("round-trip lines",
          [serialize_anno(a) for a in got]
          == [serialize_anno(a) for a in annos])
    appended = embed_bytes(stamped, [text(1, 1, "late")], append=True)
    got2, ppu2, _ = read_bytes(appended)
    check("append keeps old + ppu",
          len(got2) == len(annos) + 1 and ppu2 == 8.5
          and got2[-1]["text"] == "late")
    check("strip restores original bytes",
          insert_text(stamped, None) == blob)

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
            lines = [l for l in (theirs or "").splitlines()
                     if l and not l.startswith("#")
                     and not l.startswith(("ppu=", "unit="))]
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
                ("ellipse", "50.5,60.25,150,160,#123ABC,sky,1,dashed"),
                ("line", "0,0,199,99,green,8,dotted"),
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
            flateyes.write_png_metadata(target, "# flateyes annotations\n"
                                        + "\n".join(lines) + "\n")
            with open(target, "rb") as handle:
                ours = extract_text(handle.read())
            check("we read flateyes' chunk",
                  ours is not None
                  and [l for l in ours.splitlines()
                       if l and not l.startswith("#")] == lines)
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
