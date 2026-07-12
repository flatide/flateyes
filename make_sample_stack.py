#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Generate a sample mip-map stack for testing tdviewer --stack.

Standard library only (no PIL), so it runs on the closed-network targets.
Creates sample/level{1,2,3}.png (2000x2000, ppu 0.8/3.2/8.0) plus
sample/sample.tds, all levels drawn from one shared world (um):

  * grid: 100um lines everywhere, 20um and 5um lines appear as the
    magnification supports them (shows the precision gain per level)
  * red crosshair at the world center (checks level alignment)
  * blue bar exactly 100um long at y=+40um (checks the ruler)
  * per level: tinted background, colored border, big level digit

Usage: python3 make_sample_stack.py [output_dir]   (default: ./sample)
"""

import os
import struct
import sys
import zlib

SIZE = 2000
LEVELS = [  # (filename, ppu, background, border)
    ("level1_5x.png", 0.8, (242, 246, 255), (64, 112, 208)),
    ("level2_20x.png", 3.2, (240, 255, 242), (48, 160, 80)),
    ("level3_50x.png", 8.0, (255, 246, 240), (224, 128, 48)),
]
GRID_PITCHES = [(100, (140, 150, 170)), (20, (190, 198, 214)),
                (5, (216, 222, 234))]
MIN_GRID_PX = 8          # draw a grid only when its pitch spans >= this
CROSS = (208, 32, 32)
BAR = (32, 64, 192)
DIGIT = (60, 64, 72)

SEGMENTS = {  # 7-segment layouts per digit
    1: "bc", 2: "abged", 3: "abgcd",
}


def write_png(path, rows):
    def chunk(tag, data):
        return (struct.pack(">I", len(data)) + tag + data
                + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF))
    raw = b"".join(b"\x00" + bytes(row) for row in rows)
    with open(path, "wb") as out:
        out.write(b"\x89PNG\r\n\x1a\n")
        out.write(chunk(b"IHDR", struct.pack(">IIBBBBB", SIZE, SIZE,
                                             8, 2, 0, 0, 0)))
        out.write(chunk(b"IDAT", zlib.compress(raw, 6)))
        out.write(chunk(b"IEND", b""))


def fill_px(rows, x0, y0, x1, y1, color):
    x0, y0 = max(0, int(x0)), max(0, int(y0))
    x1, y1 = min(SIZE, int(x1)), min(SIZE, int(y1))
    if x0 >= x1 or y0 >= y1:
        return
    span = bytes(color) * (x1 - x0)
    for y in range(y0, y1):
        rows[y][x0 * 3:x1 * 3] = span


def fill_world(rows, ppu, wx0, wy0, wx1, wy1, color):
    half = SIZE / 2.0
    fill_px(rows, half + wx0 * ppu, half + wy0 * ppu,
            half + wx1 * ppu, half + wy1 * ppu, color)


def draw_digit(rows, digit, x, y, color):
    width, height, t = 100, 180, 16
    boxes = {"a": (0, 0, width, t),
             "b": (width - t, 0, t, height // 2),
             "c": (width - t, height // 2, t, height // 2),
             "d": (0, height - t, width, t),
             "e": (0, height // 2, t, height // 2),
             "f": (0, 0, t, height // 2),
             "g": (0, (height - t) // 2, width, t)}
    for name in SEGMENTS[digit]:
        bx, by, bw, bh = boxes[name]
        fill_px(rows, x + bx, y + by, x + bx + bw, y + by + bh, color)


def make_level(number, ppu, background, border):
    rows = [bytearray(bytes(background) * SIZE) for _ in range(SIZE)]
    half_world = SIZE / 2.0 / ppu

    # grid, fine pitches first so major lines paint over them
    for pitch, color in reversed(GRID_PITCHES):
        if pitch * ppu < MIN_GRID_PX:
            continue
        count = int(half_world // pitch)
        for k in range(-count, count + 1):
            w = k * pitch
            fill_world(rows, ppu, w, -half_world, w + 1.0 / ppu,
                       half_world, color)
            fill_world(rows, ppu, -half_world, w, half_world,
                       w + 1.0 / ppu, color)

    # center crosshair: 50um wide, 2um thick
    fill_world(rows, ppu, -25, -1, 25, 1, CROSS)
    fill_world(rows, ppu, -1, -25, 1, 25, CROSS)

    # measurable bar: exactly 100um from x=-50 to x=+50 at y=+40, with caps
    fill_world(rows, ppu, -50, 38, 50, 42, BAR)
    fill_world(rows, ppu, -50, 32, -48, 48, BAR)
    fill_world(rows, ppu, 48, 32, 50, 48, BAR)

    # fine detail row: 2um dots every 6um at y=+60 (crisp only at high mag)
    for k in range(-8, 9):
        fill_world(rows, ppu, k * 6 - 1, 59, k * 6 + 1, 61, DIGIT)

    # border and big level digit for instant identification
    for x0, y0, x1, y1 in ((0, 0, SIZE, 8), (0, SIZE - 8, SIZE, SIZE),
                           (0, 0, 8, SIZE), (SIZE - 8, 0, SIZE, SIZE)):
        fill_px(rows, x0, y0, x1, y1, border)
    draw_digit(rows, number, 50, 50, DIGIT)
    return rows


def main(argv):
    out_dir = argv[1] if len(argv) > 1 else "sample"
    os.makedirs(out_dir, exist_ok=True)
    manifest = ["unit=um"]
    for number, (name, ppu, background, border) in enumerate(LEVELS, 1):
        path = os.path.join(out_dir, name)
        write_png(path, make_level(number, ppu, background, border))
        manifest += ["level=%s" % name, "ppu=%g" % ppu]
        print("wrote %s (ppu=%g, %gx%g um)"
              % (path, ppu, SIZE / ppu, SIZE / ppu))
    tds = os.path.join(out_dir, "sample.tds")
    with open(tds, "w") as out:
        out.write("\n".join(manifest) + "\n")
    print("wrote %s" % tds)
    print("try: tdviewer --stack %s" % tds)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
