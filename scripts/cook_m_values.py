"""
Cook (2008) "A Concrete View of Rule 110 Computation" — step-count calculator.

Source: Matthew Cook, "A Concrete View of Rule 110 Computation",
        EPTCS 1, 2009, pp. 31-55
        arXiv:0906.3248  https://doi.org/10.48550/arXiv.0906.3248
        Related DOI: https://doi.org/10.4204/EPTCS.1.4

For Lean's `cook_cts_step_sim_ax`: given a cyclic tag system appendant list,
returns the exact number of Rule 110 steps to simulate each CTS computation step.

---

Block structure (Cook 2008, Figures 1 and 2):
  - Block C (central) is non-periodic; placed once.
  - Blocks A and B (left-side ossifier): period 3 lines.
  - Blocks D, E, F, G, H, I, J, K, L, M (central + right-side): period 30 lines.
  - 30 = period of the Ē glider, which Cook's construction is built around.

Per-appendant block decomposition (right-side periodic sequence):
  Each Y symbol in an appendant -> "II"  (two I-blocks, both 30 lines each)
  Each N symbol in an appendant -> "IJ"  (one I, one J, both 30 lines each)
  The very first I in each non-empty appendant is replaced with "KM"
  (K = raw leader, M = modified first component).  This swaps one I (30)
  for two blocks K + M (60), adding 30 lines per non-empty appendant.
  An empty appendant gets a single L-block (raw short leader, 30 lines).

  -> non-empty appendant of length L symbols  ->  (2L + 1) blocks  ->  30(2L+1) lines
  -> empty appendant                          ->  1 block          ->  30 lines

One full CTS computation step uses one appendant, so the Rule 110 time
elapsed equals the block-stack height for that appendant.

Required: every non-empty appendant length must be a multiple of 6
(Cook 2008, §1.5; ensures rejector alignment mod 3 and invisibles pass ossifiers).

---

Glider periods (time, horizontal displacement), Cook (2008) / Cook (2004) Figure 5:
  A:  (3,  2)     B:  (4, -2)
  C₁/C₂/C₃: (7,  0)   D₁/D₂: (10, 2)
  Ē:  (30, -8)    Eⁿ: (15, -4)   F:  (36, -4)
  Gⁿ: (42,-14)    H:  (92,-18)

Left-side ossifier spacing v (Cook 2008, §1.4):
  v = 76·Y + 80·N + 60·(nonempty appendants) + 43·(empty appendants)
  Pattern: [A]^v B [A]^(v+5) B [A]^(v+1) B [A]^(v+8) B

Modular alignment conditions Cook proves:
  - ↗-distance after rejection: 4+1+(2c-1)·5+2+5+5 ≡ 0 (mod 6), c = chars rejected, mult 6
  - ⌒-distance for Ē crossing C₂: must be 3 (mod 4)
  - ↗-distance for Ē crossing A⁴: 1 (mod 6); ossification requires 5 (mod 6)
"""

from typing import List


def cook_M(appendant: str) -> int:
    """Rule 110 step count to simulate one CTS step using this appendant.

    appendant: string over {'Y', 'N'}, possibly empty (empty string = empty appendant).
    """
    if not appendant:
        return 30          # L block: short-leader for empty appendant
    L = len(appendant)
    if L % 6 != 0:
        raise ValueError(
            f"Non-empty appendant length must be a multiple of 6 (Cook §1.5); "
            f"got len={L}: {appendant!r}"
        )
    return 30 * (2 * L + 1)


def cook_M_sequence(appendants: List[str], n_steps: int) -> List[int]:
    """Step counts M_0, M_1, ..., M_{n_steps-1} for cyclic CTS execution.

    appendants: cyclic list of appendants over {'Y','N'}.
    n_steps:    number of CTS computation steps to plan for.
    """
    p = len(appendants)
    per_M = [cook_M(a) for a in appendants]
    return [per_M[i % p] for i in range(n_steps)]


def cook_v(appendants: List[str]) -> int:
    """Vertical ossifier spacing v from Cook (2008), §1.4.

    v = 76·Y + 80·N + 60·nonempty + 43·empty
    where Y, N are totals across ALL appendants.
    """
    total_Y = sum(a.count("Y") for a in appendants)
    total_N = sum(a.count("N") for a in appendants)
    nonempty = sum(1 for a in appendants if a)
    empty    = sum(1 for a in appendants if not a)
    return 76 * total_Y + 80 * total_N + 60 * nonempty + 43 * empty


def cook_cycle_length(appendants: List[str]) -> int:
    """Rule 110 steps to complete one full cycle through the appendant list."""
    return sum(cook_M(a) for a in appendants)


if __name__ == "__main__":
    print("Cook (2008) Rule 110 step counts — CTS simulation\n" + "=" * 53)

    # Reference table: appendant length L -> M
    print("\nReference table (appendant length -> M = Rule 110 steps per CTS step):")
    print(f"  {'L (symbols)':<14}{'2L+1 blocks':<14}{'M (steps)'}")
    for L in [0, 6, 12, 18, 24, 30, 60]:
        blocks = 1 if L == 0 else 2 * L + 1
        M      = 30 if L == 0 else 30 * (2 * L + 1)
        note   = "  <- empty appendant" if L == 0 else ""
        print(f"  {L:<14}{blocks:<14}{M}{note}")

    # Example: appendants {YYYYYY, empty, NNNNNN, empty}
    example = ["YYYYYY", "", "NNNNNN", ""]
    print(f"\nExample: appendants = {example}")
    print(f"  v (ossifier spacing) = {cook_v(example)}")
    print(f"  Full cycle length    = {cook_cycle_length(example)} Rule 110 steps")
    print(f"  Per-appendant M:     {[cook_M(a) for a in example]}")
    print(f"  First 12 CTS steps:  {cook_M_sequence(example, 12)}")

    # Verify the Lean formula: cook_cts_step_M cts = 30 * (2 * len(appendant) + 1)
    # for non-empty, or 30 for empty
    print("\nVerification (Lean formula check):")
    for a in ["", "YYYYYY", "YYNNYY", "NNNNNN", "YYYYYYNNNNNN"]:
        if a and len(a) % 6 != 0:
            continue
        expected = cook_M(a)
        lean_formula = 30 if not a else 30 * (2 * len(a) + 1)
        ok = "✓" if expected == lean_formula else "✗"
        print(f"  {ok} len={len(a):<4}  M={expected:<8}  formula={lean_formula}")
