import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases

import Rule110.CookC2BoundedSim
import Rule110.CTStoRule110
import Rule110.InfTape

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-!
# List simulator ↔ InfTape bridge (Stage 1b)

The bounded C2 witness in `CookC2BoundedSim` runs Rule 110 on a finite `List Bool`
with ether padding beyond the list length. This module connects that semantics to
`InfTape` stepping so we can relate `c2SimRead` to `tape_has_glider_at` on
`infRule110Steps` outputs.

Stage 1b target: discharge `cook_c2_tape_bit_ax` for slots `≤ 20` (then extend).
-/

namespace Rule110

/-- Embed a finite prefix as an `InfTape`, using `cookEther` beyond `l.length`. -/
def listToInfTape (l : List Bool) : InfTape :=
  fun i => if h : i < l.length then l.get ⟨i, h⟩ else cookEther i

theorem listToInfTape_lt (l : List Bool) {i : ℕ} (hi : i < l.length) :
    listToInfTape l i = l.get ⟨i, hi⟩ := by
  simp [listToInfTape, hi]

theorem listToInfTape_ge (l : List Bool) {i : ℕ} (hi : l.length ≤ i) :
    listToInfTape l i = cookEther i := by
  simp [listToInfTape, Nat.not_lt.mpr hi]

/-- Read bit `i` from a list the same way `c2SimRead` does at the glider origin. -/
def listReadDiff (l : List Bool) (origin : ℕ) : Bool :=
  l.getD origin false ≠ cookEther origin

theorem listReadDiff_eq_tape_has_glider_at (l : List Bool) (slot : ℕ)
    (hlen : c2SimOrigin slot < l.length) :
    listReadDiff l (c2SimOrigin slot) =
      tape_has_glider_at (listToInfTape l) slot 0 := by
  have hlen' : 1000 + slot * 42 < l.length := by
    simpa [c2SimOrigin, cts_tape_origin, cts_glider_spacing] using hlen
  unfold listReadDiff tape_has_glider_at listToInfTape
  simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing, cookEther, dif_pos hlen', Nat.add_zero]
  have hget : l.getD (1000 + slot * 42) false = l[1000 + slot * 42] :=
    @List.getD_eq_getElem Bool l false (1000 + slot * 42) hlen'
  simp [hget, List.getElem?_eq_getElem hlen']

/-- `tape_has_glider_at` depends only on the tape value at the slot origin. -/
theorem tape_has_glider_at_eq_of_origin (tape1 tape2 : InfTape) (slot accum : ℕ)
    (h : tape1 (cts_tape_origin + slot * cts_glider_spacing) =
         tape2 (cts_tape_origin + slot * cts_glider_spacing)) :
    tape_has_glider_at tape1 slot accum = tape_has_glider_at tape2 slot accum := by
  simp [tape_has_glider_at, h]

/-! ## List step agrees with `infTapeStep` on the finite prefix -/

private theorem c2SimLeft_eq_listToInfTape (l : List Bool) {i : ℕ} (hi : i < l.length) :
    c2SimLeft l i = if i = 0 then false else listToInfTape l (i - 1) := by
  unfold c2SimLeft listToInfTape
  rcases eq_or_ne i 0 with h0 | h0
  · simp [h0]
  · have hi_pred : i - 1 < l.length := by omega
    rw [@List.getD_eq_getElem Bool l false (i - 1) hi_pred]
    simp [h0, hi_pred, listToInfTape_lt l hi_pred]

private theorem c2SimRight_eq_listToInfTape (l : List Bool) {i : ℕ} (hi : i < l.length) :
    c2SimRight l i = listToInfTape l (i + 1) := by
  unfold c2SimRight listToInfTape
  by_cases h : i + 1 < l.length
  · rw [@List.getD_eq_getElem Bool l false (i + 1) h]
    simp [h, listToInfTape_lt l h]
  · have hi1 : l.length ≤ i + 1 := Nat.le_of_not_gt h
    have hi1' : i + 1 = l.length := by omega
    simp [h, hi1', listToInfTape_ge l hi1]

@[simp] theorem c2SimStep_length (l : List Bool) :
    (c2SimStep l).length = l.length := by
  simp [c2SimStep, List.length_map, List.length_range]

@[simp] theorem c2SimRun_length (n : ℕ) (l : List Bool) :
    (c2SimRun n l).length = l.length := by
  induction n generalizing l with
  | zero => simp [c2SimRun]
  | succ n ih =>
    simp only [c2SimRun]
    rw [ih, c2SimStep_length]

theorem c2SimStep_listToInfTape (l : List Bool) {i : ℕ} (hi : i < l.length) :
    listToInfTape (c2SimStep l) i = infTapeStep (listToInfTape l) i := by
  have hi' : i < (c2SimStep l).length := by simpa [c2SimStep_length] using hi
  have hi_range : i < (List.range l.length).length := by simpa [List.length_range] using hi
  rw [listToInfTape_lt (c2SimStep l) hi']
  simp [c2SimStep, infTapeStep, List.getElem_map, List.getElem_range hi_range,
    c2SimLeft_eq_listToInfTape l hi, c2SimRight_eq_listToInfTape l hi,
    listToInfTape_lt l hi, @List.getD_eq_getElem Bool l false i hi]
  rcases eq_or_ne i 0 with rfl | hi0
  · simp [@List.getElem?_eq_getElem Bool l 0 hi, @List.getD_eq_getElem Bool l false 0 hi]
  · simp [hi0, @List.getElem?_eq_getElem Bool l i hi, @List.getD_eq_getElem Bool l false i hi]

/-- After `n` bounded list steps, site `j` matches `infRule110Steps` on the embedded tape,
    provided the dependency cone stays inside the list prefix (`j + n < l.length`). -/
theorem c2SimRun_eq_infRule110Steps_at (l : List Bool) (n j : ℕ)
    (hn_j : n ≤ j) (hj : j + n < l.length) :
    listToInfTape (c2SimRun n l) j = infRule110Steps n (listToInfTape l) j := by
  induction n generalizing l j with
  | zero =>
    have hj' : j < l.length := by omega
    simp [c2SimRun, infRule110Steps, listToInfTape_lt (l := l) hj']
  | succ n ih =>
    simp only [c2SimRun, infRule110Steps_succ]
    have hn : n ≤ j := Nat.le_of_succ_le hn_j
    have hj' : j + n < l.length := by omega
    have ih' := ih (c2SimStep l) j hn (by simpa [c2SimStep_length] using hj')
    rw [ih']
    apply infRule110Steps_agree_Icc hn
    intro k hk_lo hk_hi
    exact c2SimStep_listToInfTape l (by omega)

private theorem c2SimOrigin_le_1840 (slot : ℕ) (hslot : slot ≤ 20) :
    c2SimOrigin slot ≤ 1840 := by
  simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]
  nlinarith

/-! ## Minimal CTS word for isolated slot tests -/

/-- Word of length `slot + 1` with the bit at index `slot`. -/
def cts_min_word (slot : ℕ) (bit : Bool) : List Bool :=
  List.replicate slot false ++ [bit]

theorem cts_min_word_length (slot : ℕ) (bit : Bool) :
    (cts_min_word slot bit).length = slot + 1 := by
  simp [cts_min_word, List.length_append, List.length_replicate, List.length_singleton]

theorem cts_min_word_slot_lt (slot : ℕ) (bit : Bool) :
    slot < (cts_min_word slot bit).length := by
  rw [cts_min_word_length]; omega

theorem cts_min_word_getD (slot : ℕ) (bit : Bool) :
    (cts_min_word slot bit).getD slot false = bit := by
  have hlen := cts_min_word_slot_lt slot bit
  rw [@List.getD_eq_getElem Bool _ false slot hlen]
  simp [cts_min_word, List.getElem_append, List.length_replicate, List.getElem_replicate,
    List.getElem_singleton, Nat.not_lt.mpr le_rfl]

/-! ## `c2SimInit` matches `cts_to_rule110_tape` on the 30-step cone (slots ≤ 20) -/

theorem cts_tape_idx_irrelevant (idx idx' : ℕ) (w : List Bool) (i : ℕ) :
    cts_to_rule110_tape (CyclicTagSystem.mk []) idx w i =
      cts_to_rule110_tape (CyclicTagSystem.mk []) idx' w i := by
  simp [cts_to_rule110_tape, cts_word_to_gliders, cts_word_to_cells,
    ctsTapeWithOverrides, ctsBaselineTape_eq_cookEther, gliders_to_tape_eq_reverse_flatMap]

theorem c2SimInit_eq_cts_tape_cone (slot : ℕ) (bit : Bool) (hslot : slot ≤ 20) :
    ∀ k, c2SimOrigin slot - 30 ≤ k → k ≤ c2SimOrigin slot + 30 →
      cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (cts_min_word slot bit) k =
        listToInfTape (c2SimInit slot bit) k := by
  intro k hk_lo hk_hi
  cases bit
  all_goals
    interval_cases slot <;>
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing] at hk_lo hk_hi ⊢ <;>
    interval_cases k <;> native_decide

/-! ## Bounded C2 read ↔ InfTape decode (slots ≤ 20) -/

theorem c2SimReadAt_eq_listReadDiff (slot : ℕ) (w : List Bool) :
    c2SimReadAt slot w =
      listReadDiff (c2SimRun 30 (c2SimInitWord w)) (c2SimOrigin slot) := by
  simp [c2SimReadAt, listReadDiff, c2SimOrigin, cts_tape_origin, cts_glider_spacing]

theorem c2SimRead_eq_listReadDiff (slot : ℕ) (bit : Bool) :
    c2SimRead slot bit =
      listReadDiff (c2SimRun 30 (c2SimInit slot bit)) (c2SimOrigin slot) := by
  simp [c2SimRead, c2SimInit, c2SimReadAt_eq_listReadDiff]

theorem c2SimRead_eq_tape_has_glider_at_list (slot : ℕ) (bit : Bool)
    (hslot : slot ≤ 20) :
    tape_has_glider_at (listToInfTape (c2SimRun 30 (c2SimInit slot bit))) slot 0 = bit := by
  have hlen : c2SimOrigin slot < (c2SimRun 30 (c2SimInit slot bit)).length := by
    simpa [c2SimRun_length, c2SimInit_length] using
      show c2SimOrigin slot < c2SimBound from by
        have := c2SimOrigin_le_1840 slot hslot
        simp [c2SimBound, c2SimOrigin, cts_tape_origin, cts_glider_spacing]
        omega
  rw [← listReadDiff_eq_tape_has_glider_at (c2SimRun 30 (c2SimInit slot bit)) slot hlen]
  rw [← c2SimRead_eq_listReadDiff]
  exact cts_min_word_sim_read slot bit hslot

theorem c2SimRead_eq_tape_has_glider_at_inf (slot : ℕ) (bit : Bool)
    (hslot : slot ≤ 20) :
    tape_has_glider_at
      (infRule110Steps 30 (listToInfTape (c2SimInit slot bit))) slot 0 = bit := by
  have hj : 30 ≤ c2SimOrigin slot := by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  have hj' : c2SimOrigin slot + 30 < (c2SimInit slot bit).length := by
    simpa [c2SimInit_length] using
      show c2SimOrigin slot + 30 < c2SimBound from by
        have := c2SimOrigin_le_1840 slot hslot
        simp [c2SimBound, c2SimOrigin, cts_tape_origin, cts_glider_spacing]
        omega
  have hagree := c2SimRun_eq_infRule110Steps_at (c2SimInit slot bit) 30 (c2SimOrigin slot) hj hj'
  have hlist := c2SimRead_eq_tape_has_glider_at_list slot bit hslot
  rw [← tape_has_glider_at_eq_of_origin
    (listToInfTape (c2SimRun 30 (c2SimInit slot bit)))
    (infRule110Steps 30 (listToInfTape (c2SimInit slot bit))) slot 0 hagree]
  exact hlist

/-- **Stage 1b (general words, bounded, list sim):** after 30 steps, `c2SimReadAt` decodes
    `natToWord L n` at `slot` when `L ≤ c2VerifyMaxLen`. InfTape lift pending. -/
theorem cook_c2_tape_read_list (L slot n : ℕ) (hL : L ≤ c2VerifyMaxLen) (hslot : slot < L)
    (_hn : n < 2^L) :
    c2SimReadAt slot (natToWord L n) = (natToWord L n).getD slot false := by
  have h4 : L ≤ 4 := by simpa [c2VerifyMaxLen] using hL
  interval_cases L
  all_goals
    interval_cases slot <;> try omega
    all_goals
      interval_cases n <;> native_decide

/-- **Cook Collision C1 (bounded general words, list sim).** InfTape version: see
    `cook_c2_tape_bit_min_word` (min-word, slots ≤ 20). Full InfTape read for arbitrary
    multi-glider words remains open. -/
theorem cook_c2_tape_bit_list (L slot n : ℕ) (hL : L ≤ c2VerifyMaxLen) (hslot : slot < L)
    (hn : n < 2^L) :
    c2SimReadAt slot (natToWord L n) = (natToWord L n).getD slot false :=
  cook_c2_tape_read_list L slot n hL hslot hn

theorem cook_c2_tape_bit_min_word (slot : ℕ) (bit : Bool) (hslot : slot ≤ 20) (idx : ℕ) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (cts_min_word slot bit)))
      slot 0 = bit := by
  -- Decode via bounded list sim, then transport along init cone agreement.
  have hlist := c2SimRead_eq_tape_has_glider_at_inf slot bit hslot
  have h30 : 30 ≤ c2SimOrigin slot := by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  have hcone := c2SimInit_eq_cts_tape_cone slot bit hslot
  have hagree :
      infRule110Steps 30 (listToInfTape (c2SimInit slot bit)) (c2SimOrigin slot) =
        infRule110Steps 30
          (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (cts_min_word slot bit))
          (c2SimOrigin slot) := by
    apply Eq.symm
    exact infRule110Steps_agree_Icc h30 fun k hk_lo hk_hi => by
      rw [cts_tape_idx_irrelevant idx 0 (cts_min_word slot bit) k]
      exact hcone k hk_lo hk_hi
  exact (tape_has_glider_at_eq_of_origin _ _ _ _ hagree).symm.trans hlist

/-- Decoder witness for the min-word case (Stage 1b partial discharge). -/
def cook_c2_decode_at (slot : ℕ) (tape : InfTape) : Bool :=
  tape_has_glider_at tape slot 0

end Rule110
