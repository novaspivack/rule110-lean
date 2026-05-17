import Mathlib.Data.List.Basic

import Rule110.CookGliderCatalog
import Rule110.Ether
import Rule110.InfTape

/-!
# Glider references and finite tape overlays (Milestone 2 scaffolding)

Cook’s real glider grammar is **phase-parameterized** (`CookCollisionTaxonomy`): collisions depend on
`CookUpPhase` / `CookOverPhase`, not merely on species labels.

This module introduces:

* `CookGliderRef`, combining catalogued named gliders and indexed families from Figure 5.
* `overrideCells`, a simple utility writing finitely many cellular assignments on top of any base tape.

Placing canonical Cook bit-patterns for each species — and proving collision lemmas against
`infTapeStep` — is Milestone 2–3 work.

## Locality

`overrideCells_eq_base_on_Icc` records that patches disjoint from a finite spatial interval do not
change the tape inside that interval — combined with `infRule110Steps_agree_Icc` this yields “payload
far from cone ⇒ evolution matches ether” (`CTStoRule110.ctsTapeWithOverrides_infRule110Steps_eq_shift_of_disjoint`).
-/

namespace Rule110

/-- A Cook Figure 5 species reference (named row or indexed family instantiation). -/
inductive CookGliderRef where
  | named (g : CookNamedGlider) : CookGliderRef
  | indexed (g : CookIndexedGlider) (n : ℕ) : CookGliderRef

def CookGliderRef.widthNat : CookGliderRef → ℕ
  | .named g => g.widthNat
  | .indexed g n => g.widthNat n

/-- Apply finitely many labelled overrides to `base`, last wins on duplicate indices. -/
def overrideCells (base : InfTape) : List (ℕ × Bool) → InfTape
  | [] => base
  | (i, b) :: rest =>
      overrideCells (fun j => if j = i then b else base j) rest

@[simp] theorem overrideCells_nil (base : InfTape) : overrideCells base [] = base :=
  rfl

theorem overrideCells_cons (base : InfTape) (i : ℕ) (b : Bool) (rest : List (ℕ × Bool)) :
    overrideCells base ((i, b) :: rest) =
      overrideCells (fun j => if j = i then b else base j) rest :=
  rfl

/-- If every write lies strictly outside `[lo, hi]`, the overlay agrees with `base` on that interval. -/
theorem overrideCells_eq_base_on_Icc (base : InfTape) (cells : List (ℕ × Bool)) (lo hi : ℕ)
    (hdisj : ∀ p ∈ cells, p.1 < lo ∨ hi < p.1) :
    ∀ j, lo ≤ j → j ≤ hi → overrideCells base cells j = base j := by
  revert base hdisj
  induction cells with
  | nil =>
    intro base _disj j _hj_lo _hj_hi
    rfl
  | cons q qs ih =>
    intro base hdisj j hj_lo hj_hi
    rcases q with ⟨i0, b0⟩
    simp only [List.mem_cons, forall_eq_or_imp] at hdisj
    rcases hdisj with ⟨hdq, htail⟩
    let base' := fun k => if k = i0 then b0 else base k
    have hn_ij : j ≠ i0 := by
      rcases hdq with hlt | hgt
      · exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt hj_lo)).symm
      · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hj_hi hgt)
    have hqs := ih base' htail j hj_lo hj_hi
    simp only [overrideCells_cons]
    rw [hqs]
    simp [base', hn_ij]

/-- Cook ether as an `InfTape`, convenient for glider-overlay experiments. -/
abbrev etherTape : InfTape := cookEther

end Rule110
