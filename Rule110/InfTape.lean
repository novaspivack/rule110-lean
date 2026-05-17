import Mathlib.Tactic.Linarith

import Rule110.Basic

/-!
# Infinite one-sided tapes and Rule 110 stepping

Semantics align with `UgpLean.Universality.HypothesisB`: site `0` uses a `false` left boundary.
-/

namespace Rule110

abbrev InfTape := ℕ → Bool

/-- One Rule 110 step on an infinite one-sided tape. -/
def infTapeStep (tape : InfTape) : InfTape :=
  fun i =>
    let left   := if i = 0 then false else tape (i - 1)
    let center := tape i
    let right  := tape (i + 1)
    rule110Output (neighborhoodIndex left center right)

/-- Iterate `infTapeStep` `n` times. -/
def infRule110Steps : ℕ → InfTape → InfTape
  | 0,     tape => tape
  | n + 1, tape => infRule110Steps n (infTapeStep tape)

theorem infRule110Steps_zero (tape : InfTape) : infRule110Steps 0 tape = tape :=
  rfl

theorem infRule110Steps_succ (n : ℕ) (tape : InfTape) :
    infRule110Steps (n + 1) tape = infRule110Steps n (infTapeStep tape) :=
  rfl

/-- Shift an infinite tape right by `k` cells: `(shiftInfTape t k) j = t (j + k)`. -/
def shiftInfTape (tape : InfTape) (k : ℕ) : InfTape :=
  fun j => tape (j + k)

@[simp] theorem shiftInfTape_apply (tape : InfTape) (k j : ℕ) :
    shiftInfTape tape k j = tape (j + k) :=
  rfl

/-- Pointwise-equal tapes agree after one synchronous step. -/
theorem infTapeStep_congr_pointwise {t1 t2 : InfTape} (h : ∀ j, t1 j = t2 j) :
    ∀ j, infTapeStep t1 j = infTapeStep t2 j := by
  intro j
  simp only [infTapeStep]
  rcases eq_or_ne j 0 with hj | hj
  · subst hj
    simp only [↓reduceIte, h]
  · simp only [hj, ↓reduceIte, h]

/-- Pointwise-equal tapes evolve identically at every coordinate and depth. -/
theorem infRule110Steps_congr_pointwise {t1 t2 : InfTape} (h : ∀ j, t1 j = t2 j) :
    ∀ n i : ℕ, infRule110Steps n t1 i = infRule110Steps n t2 i
  | 0, i => by simpa using h i
  | Nat.succ n, i => by
      simp only [infRule110Steps_succ]
      simpa using infRule110Steps_congr_pointwise (infTapeStep_congr_pointwise h) n i

/-- One spatial shift by `4` commutes with `infTapeStep` on interior indices `j ≥ 1`. -/
theorem infTapeStep_shiftInfTape_four {t : InfTape} {j : ℕ} (hj : 0 < j) :
    infTapeStep (shiftInfTape t 4) j = infTapeStep t (j + 4) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj) with ⟨j', rfl⟩
  simp [shiftInfTape_apply, infTapeStep]

/-- Matching initial data on the spatial cone `[i - n, i + n]` implies equality after `n` synchronous
steps at `i`, provided `n ≤ i` (the backwards cone stays away from the synthetic left neighbour at site `0`).
-/
theorem infRule110Steps_agree_Icc {t1 t2 : InfTape} {n i : ℕ}
    (hn : n ≤ i)
    (h : ∀ j, i - n ≤ j → j ≤ i + n → t1 j = t2 j) :
    infRule110Steps n t1 i = infRule110Steps n t2 i := by
  induction n generalizing t1 t2 i with
  | zero =>
    simp only [infRule110Steps]
    exact h i le_rfl le_rfl
  | succ n ih =>
    simp only [infRule110Steps_succ]
    have hn_i : n ≤ i := Nat.le_trans (Nat.le_succ n) hn
    exact @ih (infTapeStep t1) (infTapeStep t2) i hn_i fun j hj_lo hj_hi => by
      have hj_pos : 0 < j := by omega
      simp only [infTapeStep]
      simp only [Nat.ne_of_gt hj_pos, ↓reduceIte,
        h (j - 1) (by omega) (by omega),
        h j (by omega) (by omega),
        h (j + 1) (by omega) (by omega)]

/-- Shift-by-`4` intertwines `n` global Rule‑110 updates with reading the unshifted evolution `4` sites to
the right, provided `n + 1 ≤ i` (boundary isolation).
-/
theorem infRule110Steps_shiftInfTape_four {t : InfTape} {n i : ℕ} (hi : n + 1 ≤ i) :
    infRule110Steps n (shiftInfTape t 4) i = infRule110Steps n t (i + 4) := by
  revert t i hi
  induction n with
  | zero =>
    intro t i hi
    simp only [infRule110Steps, shiftInfTape_apply]
  | succ n ih =>
    intro t i hi_succ
    simp only [infRule110Steps_succ]
    let u := infTapeStep (shiftInfTape t 4)
    let v := shiftInfTape (infTapeStep t) 4
    have hn_i : n ≤ i := by omega
    have agree :
        ∀ j, i - n ≤ j → j ≤ i + n → u j = v j := by
      intro j hj_lo hj_hi
      dsimp [u, v, shiftInfTape_apply]
      exact infTapeStep_shiftInfTape_four (by omega)
    rw [infRule110Steps_agree_Icc hn_i agree]
    dsimp [v, shiftInfTape_apply]
    exact ih (t := infTapeStep t) (i := i) (by omega)

end Rule110
