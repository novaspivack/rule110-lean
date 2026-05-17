import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

import Rule110.Basic
import Rule110.InfTape

/-!
# Cook ether (spatial period 14, temporal shift by 4 cells per synchronous step)
-/

namespace Rule110

def cookEtherBits (i : Fin 14) : Bool :=
  match i with
  | ⟨0, _⟩  => true
  | ⟨1, _⟩  => false
  | ⟨2, _⟩  => false
  | ⟨3, _⟩  => true
  | ⟨4, _⟩  => true
  | ⟨5, _⟩  => false
  | ⟨6, _⟩  => true
  | ⟨7, _⟩  => true
  | ⟨8, _⟩  => true
  | ⟨9, _⟩  => true
  | ⟨10, _⟩ => true
  | ⟨11, _⟩ => false
  | ⟨12, _⟩ => false
  | ⟨13, _⟩ => false

def cookEther : InfTape :=
  fun i => cookEtherBits ⟨i % 14, Nat.mod_lt _ (by decide : 0 < 14)⟩

@[simp] theorem cookEther_eq_mod (i : ℕ) :
    cookEther i = cookEtherBits ⟨i % 14, Nat.mod_lt _ (by decide : 0 < 14)⟩ :=
  rfl

def etherPeriod : ℕ := 14

theorem etherPeriod_pos : 0 < etherPeriod := by decide

theorem ether_is_periodic (i : ℕ) : cookEther i = cookEther (i + 14) := by
  simp only [cookEther_eq_mod]
  congr 1
  apply Fin.ext
  dsimp
  rw [← Nat.add_mod_right i 14]

private theorem cookEther_eq_of_mod {i j : ℕ} (h : i % 14 = j % 14) : cookEther i = cookEther j := by
  simp only [cookEther_eq_mod]
  congr 1
  apply Fin.ext
  simpa using h

theorem cookEther_shift_mod (i j : ℕ) :
    cookEther (i + j) = cookEther (i % 14 + j) :=
  cookEther_eq_of_mod (by rw [← Nat.mod_add_mod])

theorem cookEther_left_as_shift (i : ℕ) :
    (if i = 0 then false else cookEther (i - 1)) =
      cookEtherBits ⟨(i + 13) % 14, Nat.mod_lt _ etherPeriod_pos⟩ := by
  rcases i with _ | j
  · simp [cookEtherBits]
  · simp only [Nat.succ_ne_zero, ↓reduceIte, cookEther_eq_mod]
    congr 1
    apply Fin.ext
    dsimp
    rw [← Nat.add_mod_right j 14]

theorem infTapeStep_cookEther_eq (i : ℕ) :
    infTapeStep cookEther i =
      rule110Output
        (neighborhoodIndex
          (cookEtherBits ⟨(i + 13) % 14, Nat.mod_lt _ etherPeriod_pos⟩)
          (cookEtherBits ⟨i % 14, Nat.mod_lt _ etherPeriod_pos⟩)
          (cookEtherBits ⟨(i + 1) % 14, Nat.mod_lt _ etherPeriod_pos⟩)) := by
  simp only [infTapeStep]
  rw [cookEther_left_as_shift i]
  simp [cookEther_eq_mod]
private theorem mod_add_eq_of_mod_eq {i k a : ℕ} (hk : i % 14 = k % 14) :
    (i + a) % 14 = (k + a) % 14 := by
  calc
    (i + a) % 14 = (i % 14 + a % 14) % 14 := Nat.add_mod i a 14
    _ = (k % 14 + a % 14) % 14 := by rw [hk]
    _ = (k + a) % 14 := (Nat.add_mod k a 14).symm

private theorem mod_triple {i k : ℕ} (hk : i % 14 = k % 14) :
    (i + 13) % 14 = (k + 13) % 14 ∧
    i % 14 = k % 14 ∧
    (i + 1) % 14 = (k + 1) % 14 :=
  ⟨mod_add_eq_of_mod_eq hk (a := 13), hk, mod_add_eq_of_mod_eq hk (a := 1)⟩

theorem infTapeStep_cookEther_mod_eq (i k : ℕ) (hk : i % 14 = k % 14) :
    infTapeStep cookEther i = infTapeStep cookEther k := by
  simp only [infTapeStep_cookEther_eq]
  rcases mod_triple hk with ⟨h1, h2, h3⟩
  simp only [h1, h2, h3]

private theorem ether_shift_aux (k : Fin 14) :
    infTapeStep cookEther k.val =
      cookEther (k.val + 4) := by
  simp only [infTapeStep_cookEther_eq, cookEther_eq_mod]
  fin_cases k <;> decide

theorem ether_stable_phase (i : ℕ) : infTapeStep cookEther i = cookEther (i + 4) := by
  have hk := Nat.mod_lt i etherPeriod_pos
  calc
    infTapeStep cookEther i
        = infTapeStep cookEther (i % 14) :=
          infTapeStep_cookEther_mod_eq i (i % 14) (Nat.mod_mod _ _).symm
    _ = cookEther (i % 14 + 4) := ether_shift_aux ⟨i % 14, hk⟩
    _ = cookEther (i + 4) :=
          cookEther_eq_of_mod (Nat.add_mod i 4 14).symm

theorem ether_stable_under_rule110 :
    ∃ phase : ℕ,
      (∀ i : ℕ, infTapeStep cookEther i = cookEther (i + phase)) ∧
      phase = 4 :=
  ⟨4, ⟨ether_stable_phase, rfl⟩⟩

/-! ### Neighbourhood equality helper

Reasoning about collisions ultimately compares two tapes cell-wise on `{i-1,i,i+1}` relative to the odd
left boundary at `i = 0`.
-/

theorem infTapeStep_eq_of_agree (t1 t2 : InfTape) (i : ℕ)
    (hl :
      (if i = 0 then false else t1 (i - 1)) =
        if i = 0 then false else t2 (i - 1))
    (hc : t1 i = t2 i)
    (hr : t1 (i + 1) = t2 (i + 1)) :
    infTapeStep t1 i = infTapeStep t2 i := by
  simp [infTapeStep, hl, hc, hr]

/-! ### Iterated stepping vs spatial shift (computational witness)

**Semantics reminder:** `infRule110Steps (Nat.succ n) tape = infRule110Steps n (infTapeStep tape)` — we
apply one synchronous Rule‑110 update to the **whole** infinite tape, then recurse. This is **not** the
same as indexing `infTapeStep^[n]` unless stated carefully.

Empirically (and matching Cook’s phase‑4 narrative away from the hard boundary), when `n ≤ i` the tape at
coordinate `i` after `n` global updates agrees with `cookEther (i + 4 * n)`. This is now proved as
`infRule110Steps_cookEther_shift` (spot checks below remain as cheap regression anchors).
-/

theorem infRule110Steps_cookEther_shift {i n : ℕ} (hn : n ≤ i) :
    infRule110Steps n cookEther i = cookEther (i + 4 * n) := by
  revert hn i
  induction n with
  | zero =>
    intro i hn
    simp only [infRule110Steps, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    intro i hn_succ
    simp only [infRule110Steps_succ]
    have pt : ∀ j, infTapeStep cookEther j = shiftInfTape cookEther 4 j := fun j => ether_stable_phase j
    rw [infRule110Steps_congr_pointwise pt n i]
    rw [infRule110Steps_shiftInfTape_four hn_succ]
    rw [ih (show n ≤ i + 4 by omega)]
    congr 1; omega

theorem infRule110Steps_cookEther_shift_spotcheck₁ :
    infRule110Steps 1 cookEther 5 = cookEther 9 := by native_decide

theorem infRule110Steps_cookEther_shift_spotcheck₂ :
    infRule110Steps 2 cookEther 6 = cookEther 14 := by native_decide

theorem infRule110Steps_cookEther_shift_spotcheck₃ :
    infRule110Steps 3 cookEther 10 = cookEther 22 := by native_decide

end Rule110
