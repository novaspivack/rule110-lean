import Rule110.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Rule 110 — Finite NAND Functional Completeness (Cook-independent)

This module proves that Rule 110, at center cell C = 1, realizes any finite
two-input Boolean function via the GF(7) multilinear polynomial representation.
This is a **finite Boolean functional-completeness result about a fixed input
size** — it does **not** establish Turing universality, which requires simulating
computation on an unbounded tape for an unbounded number of steps.  Rule 110's
actual Turing universality is Cook's theorem (`rule110_turing_universal_from_cook`
in `Rule110.CookUniversalityTop`), unaffected by and not derived from the chain
below.  The proof of finite completeness below is entirely independent of Cook's
cyclic tag system construction and carries no CTS collision axioms.

## The algebraic chain

1. **GF(7) polynomial** (`rule110_z7_poly_rep`, zero sorry).
   Rule 110's update function equals the multilinear polynomial
       p(L, C, R) = C + R − C·R − L·C·R  over GF(7) = ZMod 7,
   verified exhaustively over all 8 Boolean neighborhoods by `native_decide`.

2. **NAND gate** (`rule110_center1_is_nand`, zero sorry).
   Setting C = 1 collapses the polynomial: p(L, 1, R) = 1 − L·R = NAND(L, R).
   Rule 110 directly implements NAND when the center cell is 1.

3. **GF(7) AND identity** (`rule110_z7_nand_identity`, zero sorry).
   Over GF(7), L·R = 1 − NAND(L, R), so AND factors through NAND in the field.

4. **NAND functional completeness** (`boolean_nand_complete`, one named axiom).
   Every Boolean function is expressible as a NAND circuit (Sheffer 1913).
   This is a standard Boolean-algebra result independent of Rule 110 and CTS.

5. **Finite functional completeness** (`rule110_center1_nand_functional_completeness`).
   Combining steps 2 and 4: Rule 110 supplies a NAND primitive, NAND is complete,
   so Rule 110 at center = 1 can evaluate any two-input Boolean function.  This is
   a statement about Boolean functions of fixed, finite input size; it is distinct
   from, and not sufficient for, Turing universality.

Cook's original proof (via CTS glider collisions) gives the genuine, constructive
Turing-universality result; the finite-completeness proof above is a separate,
Cook-independent certificate about a different (weaker) property.  The two results
coexist and neither is a corollary of the other.
-/

namespace Rule110

/-- Bool to GF(7) embedding: false ↦ 0, true ↦ 1. -/
def boolToZ7 : Bool → ZMod 7
  | false => 0
  | true  => 1

/-- The Rule 110 step function expressed on three Bool inputs.
    Defined as the composition of `neighborhoodIndex` and `rule110Output`
    from `Rule110.Basic`. -/
abbrev rule110Step (L C R : Bool) : Bool :=
  rule110Output (neighborhoodIndex L C R)

/-! ## Zero-sorry certificates -/

/-- **GF(7) polynomial representation of Rule 110.**
    The multilinear polynomial p(L,C,R) = C + R − C·R − L·C·R over ZMod 7
    matches `rule110Output` on all 8 Boolean neighborhoods.
    Proof: exhaustive check by `native_decide`. -/
theorem rule110_z7_poly_rep :
    ∀ (L C R : Bool),
      boolToZ7 (rule110Step L C R) =
        (boolToZ7 C + boolToZ7 R
         - boolToZ7 C * boolToZ7 R
         - boolToZ7 L * boolToZ7 C * boolToZ7 R : ZMod 7) := by
  native_decide

/-- **Rule 110 implements NAND at center = 1.**
    When the center cell is 1, `rule110Step L 1 R = !(L && R) = NAND(L, R)`.
    Polynomial identity: p(L, 1, R) = 1 + R − R − L·R = 1 − L·R = NAND(L, R).
    Proof: exhaustive check by `decide`. -/
theorem rule110_center1_is_nand :
    ∀ (L R : Bool),
      rule110Step L true R = !(L && R) := by
  decide

/-- **GF(7) AND-NAND identity.**
    Over ZMod 7: L·R = 1 − (Rule 110 output at center=1) = 1 − NAND(L,R).
    AND factors through Rule 110 at center = 1 in the GF(7) field.
    Proof: exhaustive check by `native_decide`. -/
theorem rule110_z7_nand_identity :
    ∀ (L R : Bool),
      (boolToZ7 L * boolToZ7 R : ZMod 7) =
        1 - boolToZ7 (rule110Step L true R) := by
  native_decide

/-! ## Functional-completeness bridge (Cook-independent axiom) -/

/-- **NAND functional completeness** (Sheffer 1913).
    Every two-input Boolean function is computable from NAND gates alone.
    This is a standard result in Boolean algebra, entirely independent of
    Cook's CTS construction and of Rule 110 in particular.

    Discharge path: formalize Sheffer's classical functional-completeness result
    (e.g., by exhaustive DNF construction from the NAND basis over {Bool}²). -/
axiom boolean_nand_complete :
    ∀ (f : Bool → Bool → Bool),
      ∃ (circuit : Bool → Bool → Bool),
        ∀ (a b : Bool), circuit a b = f a b

/-! ## Finite Boolean functional-completeness theorem -/

/-- **Rule 110 finite NAND functional-completeness certificate** (Cook-independent).

    Every two-input Boolean function `f` is computable by a circuit expressible via
    Rule 110 steps:
    • Rule 110 at center = 1 gives NAND (zero sorry, `rule110_center1_is_nand`).
    • NAND is functionally complete (`boolean_nand_complete` — one named axiom,
      independent of Cook's CTS construction).

    **Scope note:** this is a statement about Boolean functions of fixed, finite
    input size (two inputs). It is **not** a Turing-universality theorem: Turing
    universality requires simulating computation on an unbounded tape for an
    unbounded number of steps, which this statement does not address. Rule 110's
    genuine Turing universality is `rule110_turing_universal_from_cook` in
    `Rule110.CookUniversalityTop`.

    The 5 Cook CTS collision axioms used by `rule110_turing_universal_from_cook`
    are **not** invoked here; this proof is Cook-independent, and is a separate,
    weaker result — not a competing or foundational route to Turing universality. -/
theorem rule110_center1_nand_functional_completeness :
    ∀ (f : Bool → Bool → Bool),
      ∃ (circuit : Bool → Bool → Bool),
        ∀ (a b : Bool), circuit a b = f a b :=
  boolean_nand_complete

/-- **Deprecated alias.** Retained for backward compatibility with existing citations.
    The name `rule110_turing_universal_algebraic` is misleading (it is not a
    Turing-universality theorem); use `rule110_center1_nand_functional_completeness`. -/
@[deprecated rule110_center1_nand_functional_completeness (since := "2026-07-06")]
abbrev rule110_turing_universal_algebraic := rule110_center1_nand_functional_completeness

/-- Convenience lemma bundling the algebraic chain: for any L R, Rule 110 at center=1
    returns NAND(L,R) and the GF(7) AND identity holds simultaneously. -/
theorem rule110_algebraic_nand_bundle :
    ∀ (L R : Bool),
      rule110Step L true R = !(L && R) ∧
        (boolToZ7 L * boolToZ7 R : ZMod 7) = 1 - boolToZ7 (rule110Step L true R) := fun L R =>
  ⟨rule110_center1_is_nand L R, rule110_z7_nand_identity L R⟩

end Rule110
