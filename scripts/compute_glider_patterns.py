#!/usr/bin/env python3
"""
Compute Rule 110 glider bit patterns from first principles.

Cook ether: period-14 pattern, one step = shift right by 4 cells.
Ether bits (from Lean Ether.lean, i=0..13):
  1 0 0 1 1 0 1 1 1 1 1 0 0 0
  i.e. bit[i] = ether[i % 14]

Strategy: to find the C2 glider (width=3, period=7, velocity=0):
  Build a tape where the left ether phase and right ether phase differ by 3.
  The transition region is the C2 glider. Simulate 7 steps: should return to same pattern.

For each glider type (C1: w=9, C2: w=3, C3: w=11), we offset the right ether by w cells.
"""

ETHER = [1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0]  # period 14

def ether_cell(i: int) -> int:
    return ETHER[i % 14]

def rule110(left: int, center: int, right: int) -> int:
    """Rule 110: output bit from 3-cell neighborhood."""
    idx = (left << 2) | (center << 1) | right
    return (110 >> idx) & 1

def step_tape(tape: list[int], left_phase: int = 0, right_phase: int = 0) -> list[int]:
    """
    Apply one Rule 110 step.
    Boundaries use ether at given phases (indices -1 and len(tape) use ether).
    left_phase: ether phase at position 0 (so position -1 = ether[(0-1+left_phase) % 14])
    right_phase: ether phase offset on the right side
    """
    n = len(tape)
    new = []
    for i in range(n):
        # Left neighbour
        if i > 0:
            left = tape[i - 1]
        else:
            # Position -1 on the left side: ether_cell(-1 + left_phase) = ether_cell(left_phase - 1)
            left = ether_cell(left_phase - 1)
        center = tape[i]
        # Right neighbour
        if i < n - 1:
            right = tape[i + 1]
        else:
            # Position n on the right side: ether at (n + right_phase) % 14
            right = ether_cell(n + right_phase)
        new.append(rule110(left, center, right))
    return new

def make_glider_tape(width_offset: int, tape_size: int = 400, center: int = 200) -> list[int]:
    """
    Build a tape: left half = ether at phase 0, right half = ether at phase width_offset.
    """
    tape = []
    for i in range(tape_size):
        if i < center:
            tape.append(ether_cell(i))  # left ether: phase 0
        else:
            tape.append(ether_cell(i + width_offset))  # right ether: shifted by width
    return tape

def find_period_pattern(tape: list[int], period: int, steps: int, center: int,
                        window: int = 40) -> None:
    """Run `steps` Rule 110 steps and check if tape returns to itself at the center window."""
    original = tape[center - window // 2 : center + window // 2]
    current = tape[:]
    for t in range(steps):
        current = step_tape(current, len(current))
    final = current[center - window // 2 : center + window // 2]
    match = (original == final)
    print(f"  Period-{period} check: {'✓ MATCH' if match else '✗ no match'}")
    return match

def extract_glider_row(tape: list[int], center: int, left_window: int = 20, right_window: int = 20) -> dict:
    """
    Extract the 'defect' bits around center: cells that differ from pure ether.
    Returns the region plus the ether-subtracted defect.
    """
    region = tape[center - left_window : center + right_window]
    defect = []
    for j, bit in enumerate(region):
        i = center - left_window + j
        expected = ether_cell(i)
        defect.append(bit ^ expected)  # XOR: 1 where it differs from ether
    return {"region": region, "defect": defect, "offset": center - left_window}

def find_glider(name: str, width: int, period: int, velocity: int = 0,
                tape_size: int = 500, warmup: int = 200):
    """
    Find the glider with given Cook width (ether phase offset), period, velocity.
    `warmup` steps let boundary transients die out before we read the pattern.
    """
    print(f"\n{'='*60}")
    print(f"Glider {name}: width={width}, period={period}, velocity={velocity}")
    print(f"{'='*60}")

    center = tape_size // 2
    tape = make_glider_tape(width, tape_size, center)

    # The right ether has phase offset = width, so its boundary conditions are different.
    # We'll use ether-extended boundaries.
    left_phase = 0         # ether on the left starts at index 0
    right_phase = width    # ether on the right is shifted by `width`

    cur = tape[:]
    # Warmup: let the glider settle
    for _ in range(warmup):
        cur = step_tape(cur, left_phase, right_phase)

    # Now read the settled state
    snapshot0 = cur[:]

    # Simulate period more steps
    for _ in range(period):
        cur = step_tape(cur, left_phase, right_phase)

    snapshot1 = cur[:]

    # Compare center window (velocity=0: same position; velocity≠0: shifted by velocity*period)
    w = 40
    s0 = snapshot0[center - w : center + w]
    s1_shifted = snapshot1[center - w + velocity * period : center + w + velocity * period]

    if s0 == s1_shifted:
        print(f"  ✓ Period-{period} verified (velocity={velocity})")
    else:
        # Try to find actual shift
        found = False
        for sh in range(-28, 29):
            s1_try = snapshot1[center - w + sh : center + w + sh]
            if s1_try == s0:
                print(f"  ✓ Period-{period} verified with shift={sh} (expected {velocity*period})")
                found = True
                break
        if not found:
            print(f"  ✗ Period-{period} check failed")

    # Print the glider pattern: cells that differ from ether
    row0 = snapshot0[center - 20 : center + 20]
    ether_row0 = [ether_cell((center - 20 + j)) for j in range(40)]
    # Left ether and right ether at different phases
    ether_ref = []
    for j in range(40):
        i = center - 20 + j
        if i < center:
            ether_ref.append(ether_cell(i))
        else:
            ether_ref.append(ether_cell(i + width))
    defect = [row0[j] ^ ether_ref[j] for j in range(40)]

    print(f"\n  Pattern at seam (40 cells, after warmup):")
    print(f"  Raw:    {''.join(map(str,row0))}")
    print(f"  EthRef: {''.join(map(str,ether_ref))}")
    print(f"  Defect: {''.join('^' if d else '.' for d in defect)}")

    # Find the minimal bounding box of the defect
    nonzero_j = [j for j in range(40) if defect[j]]
    if nonzero_j:
        lo, hi = nonzero_j[0], nonzero_j[-1]
        glider_bits = row0[lo:hi+1]
        print(f"\n  Glider cell pattern (positions {center-20+lo}..{center-20+hi}):")
        print(f"  bits = {glider_bits}")
        print(f"  len  = {len(glider_bits)}")

    # Print full period evolution
    print(f"\n  Evolution over period (20 cells around seam):")
    cur2 = snapshot0[:]
    for t in range(period):
        row = cur2[center - 10 : center + 10]
        ether_l = [ether_cell(center - 10 + j) for j in range(10)]
        ether_r = [ether_cell(center + j + width) for j in range(10)]
        eth = ether_l + ether_r
        dft = [row[j] ^ eth[j] for j in range(20)]
        diff_str = "".join("^" if dft[j] else "." for j in range(20))
        print(f"    t={t}: {''.join(map(str,row))}  defect: {diff_str}")
        cur2 = step_tape(cur2, left_phase, right_phase)

    return snapshot0


def main():
    print("Rule 110 Glider Pattern Computation")
    print(f"Ether pattern (period 14): {ETHER}")
    print(f"Rule 110 truth table: ", end="")
    for idx in range(8):
        print(f"F({(idx>>2)&1},{(idx>>1)&1},{idx&1})={rule110((idx>>2)&1,(idx>>1)&1,idx&1)}", end=" ")
    print()

    # Cook C-family gliders: stationary (velocity 0), period 7
    # C1: width=9, period=7
    # C2: width=3, period=7
    # C3: width=11, period=7

    find_glider("C1", width=9, period=7)
    find_glider("C2", width=3, period=7)
    find_glider("C3", width=11, period=7)

    # A glider: width=6, period=(3,2) — moves right 2 in 3 steps
    # (velocity = +2 cells per 3 steps)
    find_glider("A",  width=6, period=3, velocity=2)

    # B glider: width=8, period=(4,-2) — moves left 2 in 4 steps
    find_glider("B",  width=8, period=4, velocity=-2)


if __name__ == "__main__":
    main()
