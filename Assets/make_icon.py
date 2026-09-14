#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Code-driven icon builder. Turns one of the Assets/*.png files into a
polished, multi-resolution .ico (16-256 px) + a preview PNG.

Usage:
    python make_icon.py                 # uses Assets/ball2.png
    python make_icon.py --source Assets/balance_icon.png

The builder auto-trims letterboxing, squares the canvas, rounds the corners
and fattens transparency so the result looks clean as a Windows taskbar icon.
"""
import argparse
import os
import sys

try:
    from PIL import Image, ImageDraw
except ImportError:
    Image = None
    ImageDraw = None

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_SOURCE = os.path.join(HERE, "ball2.png")
OUT_ICO = os.path.join(HERE, "icon.ico")
OUT_PNG = os.path.join(HERE, "icon_preview.png")
SIZES = (16, 24, 32, 48, 64, 128, 256)


def _bg_color(im, pad=6):
    """Guess the dominant background color from the image border pixels."""
    w, h = im.size
    pts = []
    for x in range(0, w, max(1, w // 40)):
        pts.append(im.getpixel((x, pad)))
        pts.append(im.getpixel((x, h - 1 - pad)))
    for y in range(0, h, max(1, h // 40)):
        pts.append(im.getpixel((pad, y)))
        pts.append(im.getpixel((w - 1 - pad, y)))
    from collections import Counter
    return Counter(pts).most_common(1)[0][0]


def build_icon(source=DEFAULT_SOURCE, out_ico=OUT_ICO, out_png=OUT_PNG):
    if Image is None:
        raise RuntimeError("Pillow is required. Install with: pip install Pillow")
    if not os.path.exists(source):
        raise RuntimeError("Source image not found: %s" % source)

    im = Image.open(source).convert("RGBA")
    bg = _bg_color(im)

    # Trim letterbox: drop rows/cols that are (near) transparent or (near) the
    # border background colour.
    px = im.load()
    w, h = im.size
    def is_border(x, y):
        r, g, b, a = px[x, y]
        if a < 25:
            return True
        br, bg_gr, bb, _ = bg
        return abs(r - br) <= 22 and abs(g - bg_gr) <= 22 and abs(b - bb) <= 22
    min_x, min_y, max_x, max_y = w, h, -1, -1
    step = 2
    for y in range(0, h, step):
        for x in range(0, w, step):
            if not is_border(x, y):
                if x < min_x: min_x = x
                if x > max_x: max_x = x
                if y < min_y: min_y = y
                if y > max_y: max_y = y
    if max_x < 0:
        return False
    pad = 2
    min_x = max(0, min_x - pad); min_y = max(0, min_y - pad)
    max_x = min(w - 1, max_x + pad); max_y = min(h - 1, max_y + pad)
    im = im.crop((min_x, min_y, max_x + 1, max_y + 1))

    # Square canvas, centered.
    side = max(im.size)
    canvas = Image.new("RGBA", (side, side), (0, 0, 0, 0))
    canvas.paste(im, ((side - im.size[0]) // 2, (side - im.size[1]) // 2), im)
    canvas.thumbnail((256, 256), Image.LANCZOS)

    # Rounded corners mask with soft edge.
    mask = Image.new("L", canvas.size, 0)
    d = ImageDraw.Draw(mask)
    rad = int(canvas.size[0] * 0.20)
    d.rounded_rectangle([0, 0, canvas.size[0] - 1, canvas.size[1] - 1],
                        radius=rad, fill=255)
    canvas.putalpha(mask)

    # Subtle 1px inner highlight outline for depth on dark taskbars.
    outline = Image.new("RGBA", canvas.size, (255, 255, 255, 0))
    od = ImageDraw.Draw(outline)
    od.rounded_rectangle([1, 1, canvas.size[0] - 2, canvas.size[1] - 2],
                         radius=rad - 1, outline=(255, 255, 255, 46), width=1)
    canvas = Image.alpha_composite(canvas, outline)

    canvas.save(out_ico, format="ICO", sizes=[(s, s) for s in SIZES])
    canvas.save(out_png)
    return True


def _main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source", default=DEFAULT_SOURCE)
    ap.add_argument("--out", default=OUT_ICO)
    ap.add_argument("--preview", default=OUT_PNG)
    args = ap.parse_args()
    ok = build_icon(args.source, args.out, args.preview)
    print("built %s -> %s (%s)" % (os.path.relpath(args.source), os.path.relpath(args.out),
                                   "OK" if ok else "FAILED"))


if __name__ == "__main__":
    sys.exit(_main())