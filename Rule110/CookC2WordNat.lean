import Mathlib.Tactic.IntervalCases

import Rule110.CookC2BoundedSim

/-!
# `natToWord` / `word_toNatLE` bijection (bounded length)

Little-endian binary packing for C2 exhaustive encodings. Decidable roundtrip certificates
for `L ≤ 7` on the `natToWord` image; `natToWord_inj` is analytical.
-/

namespace Rule110

/-- Little-endian value of a bool word (inverse of `natToWord` on fixed length). -/
def word_toNatLE (w : List Bool) : ℕ :=
  (List.range w.length).foldl (fun n i => n + (if w[i]! then 2 ^ i else 0)) 0

@[simp] theorem word_toNatLE_nil : word_toNatLE [] = 0 := by
  simp [word_toNatLE]

/-- Roundtrip `word_toNatLE ∘ natToWord` at fixed length (decidable cert). -/
def wordNatRoundtripOk (L : ℕ) : Bool :=
  if _ : L ≤ 7 then
    (List.range (2 ^ L)).all fun n => decide (word_toNatLE (natToWord L n) = n)
  else
    true

/-- Roundtrip `natToWord ∘ word_toNatLE` on the `natToWord` image at fixed length. -/
def natWordRoundtripOk (L : ℕ) : Bool :=
  if _ : L ≤ 7 then
    (List.range (2 ^ L)).all fun n =>
      decide (natToWord L (word_toNatLE (natToWord L n)) = natToWord L n)
  else
    true

theorem word_nat_roundtrip_ok_upto7 : ∀ L, L ≤ 7 → wordNatRoundtripOk L = true := by
  intro L hL
  interval_cases L <;> native_decide

theorem nat_word_roundtrip_ok_upto7 : ∀ L, L ≤ 7 → natWordRoundtripOk L = true := by
  intro L hL
  interval_cases L <;> native_decide

theorem word_toNatLE_natToWord (L n : ℕ) (hL : L ≤ 7) (hn : n < 2 ^ L) :
    word_toNatLE (natToWord L n) = n := by
  have hall : ((List.range (2 ^ L)).all fun n => decide (word_toNatLE (natToWord L n) = n)) = true := by
    simpa [wordNatRoundtripOk, hL, reduceIte] using word_nat_roundtrip_ok_upto7 L hL
  have hmem := List.mem_range.mpr hn
  have h1 := (List.all_eq_true.mp hall) n hmem
  exact (decide_eq_true_iff).1 (by simpa [wordNatRoundtripOk, hL, reduceIte] using h1)

theorem natToWord_word_toNatLE_natToWord (L n : ℕ) (hL : L ≤ 7) (hn : n < 2 ^ L) :
    natToWord L (word_toNatLE (natToWord L n)) = natToWord L n := by
  have hall :
      ((List.range (2 ^ L)).all fun n =>
          decide (natToWord L (word_toNatLE (natToWord L n)) = natToWord L n)) = true := by
    simpa [natWordRoundtripOk, hL, reduceIte] using nat_word_roundtrip_ok_upto7 L hL
  have hmem := List.mem_range.mpr hn
  have h1 := (List.all_eq_true.mp hall) n hmem
  exact (decide_eq_true_iff).1 (by simpa [natWordRoundtripOk, hL, reduceIte] using h1)

theorem natToWord_inj (L n₁ n₂ : ℕ) (hL : L ≤ 7) (hn₁ : n₁ < 2 ^ L) (hn₂ : n₂ < 2 ^ L)
    (heq : natToWord L n₁ = natToWord L n₂) : n₁ = n₂ := by
  rw [← word_toNatLE_natToWord L n₁ hL hn₁, ← word_toNatLE_natToWord L n₂ hL hn₂, heq]

end Rule110
