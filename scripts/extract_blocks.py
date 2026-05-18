"""
Extract bit-sequence rows from Cook's block PNG images.

Source blocks from: github.com/inexxt/rule_110 (images originally from Cook 2009, arXiv:0906.3248).
Primary reference: Matthew Cook, "A Concrete View of Rule 110 Computation",
                   EPTCS 1, 2009, pp. 31-55, arXiv:0906.3248.

Block key (Cook 2008, §1.4):
  A, B    — ossifier blocks (period 3 lines)
  C       — central anchor (non-periodic; t=0 row marked with ORIG_ZERO=179)
  D, E, F, G  — central region blocks (period 30 lines)
  H, I, J, K, L  — right-hand side appendant blocks (period 30 lines)

Block → CTS encoding:
  CTS tape bit 0 → blocks E, D  (stationary: C2 glider absent at slot)
  CTS tape bit 1 → blocks F, D  (stationary: C2 glider present at slot)
  Last D in central region → G
  Each CTS appendant Y (1) → I, I
  Each CTS appendant N (0) → I, J
  First I in each non-empty appendant → K, H
  Empty appendant → L
  First K of the sequence is moved to the very end.

Phase constants (from symbols_to_bits.py):
  CONST_LEFT_PHASE = 7
  true_right_phases = {D:21, E:29, F:23, G:4, H:0, I:16, J:22, K:8, L:7}
  change_of_phase(incoming, right_phase) = ((7+1) - right_phase + incoming) % 30
"""

import numpy as np
from PIL import Image
from pathlib import Path
import json

ORIG_BACKGROUND = 128
ORIG_WHITE = 255
ORIG_BLACK = 0
ORIG_ZERO = 179  # marks t=0 row in block C
NEW_BACKGROUND = 0
NEW_WHITE = 255
NEW_BLACK = 128
NEW_ZERO = 0

BLOCKS_DIR = Path(__file__).parent.parent / "blocks"

def load_block(name):
    img = np.array(Image.open(BLOCKS_DIR / f"{name}.png"))
    if img.ndim == 3:
        img = img[:, :, 0]
    m = {ORIG_BACKGROUND: NEW_BACKGROUND, ORIG_WHITE: NEW_WHITE,
         ORIG_BLACK: NEW_BLACK, ORIG_ZERO: NEW_ZERO}
    return np.vectorize(lambda x: m.get(int(x), int(x)))(img)

def get_row_bits(block_img, y):
    """Return the non-background cells of row y as a list of 0/1."""
    nrows = block_img.shape[0]
    row = block_img[y % nrows, :]
    non_bg = row[row != NEW_BACKGROUND]
    return [1 if v == NEW_WHITE else 0 for v in non_bg]

def extract_all_blocks():
    blocks = {}
    for name in list("ABCDEFGHIJKL"):
        img = load_block(name)
        period = 3 if name in ("A", "B") else 30
        rows = [get_row_bits(img, y) for y in range(period)]
        blocks[name] = {"period": period, "rows": rows, "shape": list(img.shape)}

    # Find t=0 row in block C
    C_raw = np.array(Image.open(BLOCKS_DIR / "C.png"))
    if C_raw.ndim == 3: C_raw = C_raw[:, :, 0]
    zero_rows = [i for i in range(C_raw.shape[0]) if 179 in C_raw[i, :]]
    zero_loc = zero_rows[0] % 30
    blocks["C"]["zero_loc"] = zero_loc
    blocks["C"]["t0_row"] = blocks["C"]["rows"][zero_loc]

    return blocks

def print_summary(blocks):
    print("Cook Rule 110 block summary")
    print("=" * 60)
    print(f"Block C t=0 row (zero_loc={blocks['C']['zero_loc']}):")
    print(f"  {''.join(map(str, blocks['C']['t0_row']))} ({len(blocks['C']['t0_row'])} bits)")
    print()
    for name in list("ABCDEFGHIJKL"):
        b = blocks[name]
        print(f"Block {name}: period={b['period']}, shape={b['shape']}")
        for i, row in enumerate(b['rows'][:5]):
            marker = f" ← t=0" if name=="C" and i==b.get("zero_loc", -1) else ""
            print(f"  row {i:2d}: {''.join(map(str,row[:60]))}{'...' if len(row)>60 else ''} ({len(row)} bits){marker}")
        if len(b['rows']) > 5:
            print(f"  ... ({b['period']-5} more rows)")

if __name__ == "__main__":
    blocks = extract_all_blocks()
    print_summary(blocks)

    # Save extracted blocks as JSON for use without PIL
    out = {}
    for name, b in blocks.items():
        out[name] = {"period": b["period"], "rows": b["rows"]}
        if "zero_loc" in b:
            out[name]["zero_loc"] = b["zero_loc"]

    out_path = Path(__file__).parent / "cook_blocks.json"
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2)
    print(f"\nSaved block data to {out_path}")
