import Init.Data.List.Lemmas

import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases

import Rule110.CookC2BoundedSim
import Rule110.CookC2VerifyLen6
import Rule110.CookC2VerifyLen7
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

/-- Init agreement on the 30-step read cone for bounded `natToWord` encodings. -/
def c2InitReadConeOk (L readSlot n : ℕ) : Bool :=
  if _ : L ≤ c2VerifyMaxLen then
    if _ : readSlot < L then
      if _ : n < 2^L then
        (List.range 61).all fun d =>
          let k := c2SimOrigin readSlot - 30 + d
          decide (listToInfTape (c2SimInitWord (natToWord L n)) k =
            cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord L n) k)
      else true
    else true
  else true

def c2AllInitReadConesOk : Bool :=
  (List.range (c2VerifyMaxLen + 1)).all fun L =>
    (List.range L).all fun readSlot =>
      (List.range (2^L)).all fun n => c2InitReadConeOk L readSlot n

theorem c2_all_init_read_cones_ok : c2AllInitReadConesOk = true := by native_decide

theorem c2_init_read_cone_ok (L readSlot n : ℕ) (hL : L ≤ c2VerifyMaxLen)
    (hslot : readSlot < L) (hn : n < 2^L) :
    c2InitReadConeOk L readSlot n = true := by
  have _h5 : L ≤ 5 := by simpa [c2VerifyMaxLen] using hL
  interval_cases L
  all_goals
    interval_cases readSlot <;> try omega
    all_goals
      interval_cases n <;> native_decide

private theorem c2InitReadConeOk_get (L readSlot n d : ℕ)
    (hL : L ≤ c2VerifyMaxLen) (hslot : readSlot < L) (hn : n < 2^L) (hd : d < 61) :
    listToInfTape (c2SimInitWord (natToWord L n)) (c2SimOrigin readSlot - 30 + d) =
      cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord L n)
        (c2SimOrigin readSlot - 30 + d) := by
  have hbool := c2_init_read_cone_ok L readSlot n hL hslot hn
  have hall : ((List.range 61).all fun d =>
      decide (listToInfTape (c2SimInitWord (natToWord L n)) (c2SimOrigin readSlot - 30 + d) =
        cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord L n)
          (c2SimOrigin readSlot - 30 + d))) = true := by
    simpa [c2InitReadConeOk, hL, hslot, hn, reduceIte] using hbool
  have hdec := (List.all_eq_true.mp hall) d (List.mem_range.mpr hd)
  exact (decide_eq_true_iff).1 hdec

theorem c2SimInitWord_eq_cts_tape_cone_read (L readSlot n : ℕ) (hL : L ≤ c2VerifyMaxLen)
    (hslot : readSlot < L) (hn : n < 2^L) (k : ℕ)
    (hk_lo : c2SimOrigin readSlot - 30 ≤ k) (hk_hi : k ≤ c2SimOrigin readSlot + 30) :
    listToInfTape (c2SimInitWord (natToWord L n)) k =
      cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord L n) k := by
  have origin_eq : c2SimOrigin readSlot = cts_tape_origin + readSlot * cts_glider_spacing := rfl
  have hd : ∃ d, d < 61 ∧ k = c2SimOrigin readSlot - 30 + d := by
    refine ⟨k + 30 - c2SimOrigin readSlot, ?_, ?_⟩
    · simp [origin_eq, cts_tape_origin, cts_glider_spacing] at hk_hi ⊢; omega
    · simp [origin_eq, cts_tape_origin, cts_glider_spacing] at hk_lo hk_hi ⊢; omega
  obtain ⟨d, hd_lt, hk_eq⟩ := hd
  rw [hk_eq]
  exact c2InitReadConeOk_get L readSlot n d hL hslot hn hd_lt

private theorem c2SimOrigin_lt_bound (slot : ℕ) (hslot : slot ≤ 4) :
    c2SimOrigin slot < c2SimBound := by
  simp [c2SimOrigin, c2SimBound, cts_tape_origin, cts_glider_spacing]
  have : slot * 42 ≤ 4 * 42 := Nat.mul_le_mul_right _ hslot
  omega

private theorem c2SimOrigin_add30_lt_bound (slot : ℕ) (hslot : slot ≤ 4) :
    c2SimOrigin slot + 30 < c2SimBound := by
  simp [c2SimOrigin, c2SimBound, cts_tape_origin, cts_glider_spacing]
  have : slot * 42 ≤ 4 * 42 := Nat.mul_le_mul_right _ hslot
  omega

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
    `natToWord L n` at `slot` when `L ≤ c2VerifyMaxLen`. -/
theorem cook_c2_tape_read_list (L slot n : ℕ) (hL : L ≤ c2VerifyMaxLen) (hslot : slot < L)
    (_hn : n < 2^L) :
    c2SimReadAt slot (natToWord L n) = (natToWord L n).getD slot false := by
  have h5 : L ≤ 5 := by simpa [c2VerifyMaxLen] using hL
  interval_cases L
  all_goals
    interval_cases slot <;> try omega
    all_goals
      interval_cases n <;> native_decide

/-- **Cook Collision C1 (bounded general words, list sim).** InfTape:
    `cook_c2_tape_bit_inf_nat` (multi-glider, L ≤ 5); min-word: `cook_c2_tape_bit_min_word`;
    L = 6: `cook_c2_tape_bit_inf_nat_len6`. -/
theorem cook_c2_tape_bit_list (L slot n : ℕ) (hL : L ≤ c2VerifyMaxLen) (hslot : slot < L)
    (hn : n < 2^L) :
    c2SimReadAt slot (natToWord L n) = (natToWord L n).getD slot false :=
  cook_c2_tape_read_list L slot n hL hslot hn

/-- **Stage 1b (InfTape, bounded multi-glider words):** after 30 steps, decode `natToWord L n`
    at `slot` via `tape_has_glider_at` when `L ≤ c2VerifyMaxLen`. -/
theorem cook_c2_tape_bit_inf_nat (L slot n : ℕ) (hL : L ≤ c2VerifyMaxLen) (hslot : slot < L)
    (hn : n < 2^L) (idx : ℕ) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n)))
      slot 0 =
      (natToWord L n).getD slot false := by
  let w := natToWord L n
  have hslot4 : slot ≤ 4 := by
    have hL5 : L ≤ 5 := by simpa [c2VerifyMaxLen] using hL
    omega
  have hlist := cook_c2_tape_bit_list L slot n hL hslot hn
  have hlen : c2SimOrigin slot < (c2SimRun 30 (c2SimInitWord w)).length := by
    simpa [c2SimRun_length, c2SimInitWord_length] using c2SimOrigin_lt_bound slot hslot4
  have h30 : 30 ≤ c2SimOrigin slot := by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  have hj' : c2SimOrigin slot + 30 < c2SimBound :=
    c2SimOrigin_add30_lt_bound slot hslot4
  have hlist_inf :
      tape_has_glider_at (listToInfTape (c2SimRun 30 (c2SimInitWord w))) slot 0 =
        w.getD slot false := by
    rw [← listReadDiff_eq_tape_has_glider_at (c2SimRun 30 (c2SimInitWord w)) slot hlen,
      ← c2SimReadAt_eq_listReadDiff, hlist]
  have hinit := c2SimInitWord_eq_cts_tape_cone_read L slot n hL hslot hn
  have hagree :
      infRule110Steps 30 (listToInfTape (c2SimInitWord w)) (c2SimOrigin slot) =
        infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w) (c2SimOrigin slot) := by
    apply Eq.symm
    refine infRule110Steps_agree_Icc h30 fun k hk_lo hk_hi => ?_
    rw [cts_tape_idx_irrelevant idx 0 w k]
    exact (hinit k hk_lo hk_hi).symm
  have hrun := c2SimRun_eq_infRule110Steps_at (c2SimInitWord w) 30 (c2SimOrigin slot) h30
    (by simpa [c2SimInitWord_length] using hj')
  have hrun' :
      tape_has_glider_at (infRule110Steps 30 (listToInfTape (c2SimInitWord w))) slot 0 =
        w.getD slot false := by
    rw [← tape_has_glider_at_eq_of_origin
      (listToInfTape (c2SimRun 30 (c2SimInitWord w)))
      (infRule110Steps 30 (listToInfTape (c2SimInitWord w))) slot 0 hrun]
    exact hlist_inf
  rw [← tape_has_glider_at_eq_of_origin
    (infRule110Steps 30 (listToInfTape (c2SimInitWord w)))
    (infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w)) slot 0 hagree]
  exact hrun'

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

/-- **Bounded C1 discharge (natToWord, L ≤ 5):** decoder `cook_c2_decode_at` at slot. -/
theorem cook_c2_tape_bit_bounded (L slot n : ℕ) (hL : L ≤ c2VerifyMaxLen) (hslot : slot < L)
    (hn : n < 2^L) (idx : ℕ) (bit : Bool)
    (hbit : (natToWord L n).getD slot false = bit) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n)))
      slot 0 = bit := by
  rw [← hbit]
  exact cook_c2_tape_bit_inf_nat L slot n hL hslot hn idx

/-- Decoder witness for the min-word case (Stage 1b partial discharge). -/
def cook_c2_decode_at (slot : ℕ) (tape : InfTape) : Bool :=
  tape_has_glider_at tape slot 0

/-- **Partial C1 discharge:** bounded `natToWord` family (L ≤ 5) admits a slot decoder. -/
theorem cook_c2_tape_bit_ax_partial (L slot n : ℕ) (hL : L ≤ c2VerifyMaxLen) (hslot : slot < L)
    (hn : n < 2^L) (idx : ℕ) :
    cook_c2_decode_at slot
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n))) =
      (natToWord L n).getD slot false :=
  cook_c2_tape_bit_inf_nat L slot n hL hslot hn idx

/-- **Stage 1b (list sim, L ≤ 6):** isolated L=6 cert extends the L ≤ 5 family. -/
theorem cook_c2_tape_bit_list_upto6 (L slot n : ℕ) (hL : L ≤ 6) (hslot : slot < L) (hn : n < 2^L) :
    c2SimReadAt slot (natToWord L n) = (natToWord L n).getD slot false := by
  by_cases h5 : L ≤ c2VerifyMaxLen
  · exact cook_c2_tape_read_list L slot n h5 hslot hn
  · have hL6 : L = 6 := by
      simp [c2VerifyMaxLen] at h5 hL ⊢; omega
    subst hL6
    exact c2_len6_word_read_ok slot n hslot hn

/-! ### L=6 isolated init-cone cert (Stage 1b InfTape extension) -/

def c2Len6InitReadConeOk (readSlot n : ℕ) : Bool :=
  if _ : readSlot < 6 then
    if _ : n < 2^6 then
      (List.range 61).all fun d =>
        let k := c2SimOrigin readSlot - 30 + d
        decide (listToInfTape (c2SimInitWord (natToWord 6 n)) k =
          cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord 6 n) k)
    else true
  else true

def c2Len6AllInitReadConesOk : Bool :=
  (List.range 6).all fun readSlot =>
    (List.range (2^6)).all fun n => c2Len6InitReadConeOk readSlot n

theorem c2_len6_all_init_read_cones_ok : c2Len6AllInitReadConesOk = true := by
  native_decide

theorem c2_len6_init_read_cone_ok (readSlot n : ℕ) (hslot : readSlot < 6) (hn : n < 2^6) :
    c2Len6InitReadConeOk readSlot n = true := by
  have hn64 : n < 64 := by
    have hpow : 2^6 = 64 := by decide
    simpa [hpow] using hn
  have hall : ((List.range 6).all fun readSlot =>
      ((List.range (2^6)).all fun n => c2Len6InitReadConeOk readSlot n)) = true := by
    simpa [c2Len6AllInitReadConesOk] using c2_len6_all_init_read_cones_ok
  have h1 := (List.all_eq_true.mp hall) readSlot (List.mem_range.mpr hslot)
  have h2 := (List.all_eq_true.mp h1) n (List.mem_range.mpr hn64)
  exact (decide_eq_true_iff).1 (by simpa [c2Len6InitReadConeOk, hslot, hn, hn64, reduceIte] using h2)

private theorem c2Len6InitReadConeOk_get (readSlot n d : ℕ) (hslot : readSlot < 6) (hn : n < 2^6)
    (hd : d < 61) :
    listToInfTape (c2SimInitWord (natToWord 6 n)) (c2SimOrigin readSlot - 30 + d) =
      cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord 6 n)
        (c2SimOrigin readSlot - 30 + d) := by
  have hn64 : n < 64 := by
    have hpow : 2^6 = 64 := by decide
    simpa [hpow] using hn
  have hbool := c2_len6_init_read_cone_ok readSlot n hslot hn
  have hall : ((List.range 61).all fun d =>
      decide (listToInfTape (c2SimInitWord (natToWord 6 n)) (c2SimOrigin readSlot - 30 + d) =
        cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord 6 n)
          (c2SimOrigin readSlot - 30 + d))) = true := by
    simpa [c2Len6InitReadConeOk, hslot, hn, hn64, reduceIte] using hbool
  have hdec := (List.all_eq_true.mp hall) d (List.mem_range.mpr hd)
  exact (decide_eq_true_iff).1 hdec

theorem c2Len6SimInitWord_eq_cts_tape_cone_read (readSlot n : ℕ) (hslot : readSlot < 6)
    (hn : n < 2^6) (k : ℕ)
    (hk_lo : c2SimOrigin readSlot - 30 ≤ k) (hk_hi : k ≤ c2SimOrigin readSlot + 30) :
    listToInfTape (c2SimInitWord (natToWord 6 n)) k =
      cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord 6 n) k := by
  have origin_eq : c2SimOrigin readSlot = cts_tape_origin + readSlot * cts_glider_spacing := rfl
  have hd : ∃ d, d < 61 ∧ k = c2SimOrigin readSlot - 30 + d := by
    refine ⟨k + 30 - c2SimOrigin readSlot, ?_, ?_⟩
    · simp [origin_eq, cts_tape_origin, cts_glider_spacing] at hk_hi ⊢; omega
    · simp [origin_eq, cts_tape_origin, cts_glider_spacing] at hk_lo hk_hi ⊢; omega
  obtain ⟨d, hd_lt, hk_eq⟩ := hd
  rw [hk_eq]
  exact c2Len6InitReadConeOk_get readSlot n d hslot hn hd_lt

private theorem c2SimOrigin_lt_bound_len6 (slot : ℕ) (hslot : slot ≤ 5) :
    c2SimOrigin slot < c2SimBound := by
  simp [c2SimOrigin, c2SimBound, cts_tape_origin, cts_glider_spacing]
  have : slot * 42 ≤ 5 * 42 := Nat.mul_le_mul_right _ hslot
  omega

private theorem c2SimOrigin_add30_lt_bound_len6 (slot : ℕ) (hslot : slot ≤ 5) :
    c2SimOrigin slot + 30 < c2SimBound := by
  simp [c2SimOrigin, c2SimBound, cts_tape_origin, cts_glider_spacing]
  have : slot * 42 ≤ 5 * 42 := Nat.mul_le_mul_right _ hslot
  omega

/-- **Stage 1b (InfTape, L = 6):** decode `natToWord 6 n` at slot after 30 steps. -/
theorem cook_c2_tape_bit_inf_nat_len6 (slot n : ℕ) (hslot : slot < 6) (hn : n < 2^6) (idx : ℕ) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord 6 n)))
      slot 0 =
      (natToWord 6 n).getD slot false := by
  let w := natToWord 6 n
  have hslot5 : slot ≤ 5 := by omega
  have hlist := c2_len6_word_read_ok slot n hslot hn
  have hlen : c2SimOrigin slot < (c2SimRun 30 (c2SimInitWord w)).length := by
    simpa [c2SimRun_length, c2SimInitWord_length] using c2SimOrigin_lt_bound_len6 slot hslot5
  have h30 : 30 ≤ c2SimOrigin slot := by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  have hj' : c2SimOrigin slot + 30 < c2SimBound :=
    c2SimOrigin_add30_lt_bound_len6 slot hslot5
  have hlist_inf :
      tape_has_glider_at (listToInfTape (c2SimRun 30 (c2SimInitWord w))) slot 0 =
        w.getD slot false := by
    rw [← listReadDiff_eq_tape_has_glider_at (c2SimRun 30 (c2SimInitWord w)) slot hlen,
      ← c2SimReadAt_eq_listReadDiff, hlist]
  have hinit := c2Len6SimInitWord_eq_cts_tape_cone_read slot n hslot hn
  have hagree :
      infRule110Steps 30 (listToInfTape (c2SimInitWord w)) (c2SimOrigin slot) =
        infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w) (c2SimOrigin slot) := by
    apply Eq.symm
    refine infRule110Steps_agree_Icc h30 fun k hk_lo hk_hi => ?_
    rw [cts_tape_idx_irrelevant idx 0 w k]
    exact (hinit k hk_lo hk_hi).symm
  have hrun := c2SimRun_eq_infRule110Steps_at (c2SimInitWord w) 30 (c2SimOrigin slot) h30
    (by simpa [c2SimInitWord_length] using hj')
  have hrun' :
      tape_has_glider_at (infRule110Steps 30 (listToInfTape (c2SimInitWord w))) slot 0 =
        w.getD slot false := by
    rw [← tape_has_glider_at_eq_of_origin
      (listToInfTape (c2SimRun 30 (c2SimInitWord w)))
      (infRule110Steps 30 (listToInfTape (c2SimInitWord w))) slot 0 hrun]
    exact hlist_inf
  rw [← tape_has_glider_at_eq_of_origin
    (infRule110Steps 30 (listToInfTape (c2SimInitWord w)))
    (infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w)) slot 0 hagree]
  exact hrun'

/-- **Stage 1b (InfTape, L ≤ 6):** extends `cook_c2_tape_bit_inf_nat` with isolated L=6 cert. -/
theorem cook_c2_tape_bit_inf_nat_upto6 (L slot n : ℕ) (hL : L ≤ 6) (hslot : slot < L) (hn : n < 2^L)
    (idx : ℕ) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n)))
      slot 0 =
      (natToWord L n).getD slot false := by
  by_cases h5 : L ≤ c2VerifyMaxLen
  · exact cook_c2_tape_bit_inf_nat L slot n h5 hslot hn idx
  · have hL6 : L = 6 := by
      simp [c2VerifyMaxLen] at h5 hL ⊢; omega
    subst hL6
    exact cook_c2_tape_bit_inf_nat_len6 slot n hslot hn idx

/-- **Partial C1 discharge (L ≤ 6):** bounded `natToWord` family on InfTape. -/
theorem cook_c2_tape_bit_ax_partial_upto6 (L slot n : ℕ) (hL : L ≤ 6) (hslot : slot < L)
    (hn : n < 2^L) (idx : ℕ) :
    cook_c2_decode_at slot
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n))) =
      (natToWord L n).getD slot false :=
  cook_c2_tape_bit_inf_nat_upto6 L slot n hL hslot hn idx

/-! ### L=7 isolated init-cone cert (Stage 1b InfTape extension) -/

def c2Len7InitReadConeOk (readSlot n : ℕ) : Bool :=
  if _ : readSlot < 7 then
    if _ : n < 2^7 then
      (List.range 61).all fun d =>
        let k := c2SimOrigin readSlot - 30 + d
        decide (listToInfTape (c2SimInitWord (natToWord 7 n)) k =
          cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord 7 n) k)
    else true
  else true

def c2Len7AllInitReadConesOk : Bool :=
  (List.range 7).all fun readSlot =>
    (List.range (2^7)).all fun n => c2Len7InitReadConeOk readSlot n

theorem c2_len7_all_init_read_cones_ok : c2Len7AllInitReadConesOk = true := by
  native_decide

theorem c2_len7_init_read_cone_ok (readSlot n : ℕ) (hslot : readSlot < 7) (hn : n < 2^7) :
    c2Len7InitReadConeOk readSlot n = true := by
  have hn128 : n < 128 := by
    have hpow : 2^7 = 128 := by decide
    simpa [hpow] using hn
  have hall : ((List.range 7).all fun readSlot =>
      ((List.range (2^7)).all fun n => c2Len7InitReadConeOk readSlot n)) = true := by
    simpa [c2Len7AllInitReadConesOk] using c2_len7_all_init_read_cones_ok
  have h1 := (List.all_eq_true.mp hall) readSlot (List.mem_range.mpr hslot)
  have h2 := (List.all_eq_true.mp h1) n (List.mem_range.mpr hn128)
  exact (decide_eq_true_iff).1 (by simpa [c2Len7InitReadConeOk, hslot, hn, hn128, reduceIte] using h2)

private theorem c2Len7InitReadConeOk_get (readSlot n d : ℕ) (hslot : readSlot < 7) (hn : n < 2^7)
    (hd : d < 61) :
    listToInfTape (c2SimInitWord (natToWord 7 n)) (c2SimOrigin readSlot - 30 + d) =
      cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord 7 n)
        (c2SimOrigin readSlot - 30 + d) := by
  have hn128 : n < 128 := by
    have hpow : 2^7 = 128 := by decide
    simpa [hpow] using hn
  have hbool := c2_len7_init_read_cone_ok readSlot n hslot hn
  have hall : ((List.range 61).all fun d =>
      decide (listToInfTape (c2SimInitWord (natToWord 7 n)) (c2SimOrigin readSlot - 30 + d) =
        cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord 7 n)
          (c2SimOrigin readSlot - 30 + d))) = true := by
    simpa [c2Len7InitReadConeOk, hslot, hn, hn128, reduceIte] using hbool
  have hdec := (List.all_eq_true.mp hall) d (List.mem_range.mpr hd)
  exact (decide_eq_true_iff).1 hdec

theorem c2Len7SimInitWord_eq_cts_tape_cone_read (readSlot n : ℕ) (hslot : readSlot < 7)
    (hn : n < 2^7) (k : ℕ)
    (hk_lo : c2SimOrigin readSlot - 30 ≤ k) (hk_hi : k ≤ c2SimOrigin readSlot + 30) :
    listToInfTape (c2SimInitWord (natToWord 7 n)) k =
      cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (natToWord 7 n) k := by
  have origin_eq : c2SimOrigin readSlot = cts_tape_origin + readSlot * cts_glider_spacing := rfl
  have hd : ∃ d, d < 61 ∧ k = c2SimOrigin readSlot - 30 + d := by
    refine ⟨k + 30 - c2SimOrigin readSlot, ?_, ?_⟩
    · simp [origin_eq, cts_tape_origin, cts_glider_spacing] at hk_hi ⊢; omega
    · simp [origin_eq, cts_tape_origin, cts_glider_spacing] at hk_lo hk_hi ⊢; omega
  obtain ⟨d, hd_lt, hk_eq⟩ := hd
  rw [hk_eq]
  exact c2Len7InitReadConeOk_get readSlot n d hslot hn hd_lt

private theorem c2SimOrigin_lt_bound_len7 (slot : ℕ) (hslot : slot ≤ 6) :
    c2SimOrigin slot < c2SimBound := by
  simp [c2SimOrigin, c2SimBound, cts_tape_origin, cts_glider_spacing]
  have : slot * 42 ≤ 6 * 42 := Nat.mul_le_mul_right _ hslot
  omega

private theorem c2SimOrigin_add30_lt_bound_len7 (slot : ℕ) (hslot : slot ≤ 6) :
    c2SimOrigin slot + 30 < c2SimBound := by
  simp [c2SimOrigin, c2SimBound, cts_tape_origin, cts_glider_spacing]
  have : slot * 42 ≤ 6 * 42 := Nat.mul_le_mul_right _ hslot
  omega

/-- **Stage 1b (InfTape, L = 7):** decode `natToWord 7 n` at slot after 30 steps. -/
theorem cook_c2_tape_bit_inf_nat_len7 (slot n : ℕ) (hslot : slot < 7) (hn : n < 2^7) (idx : ℕ) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord 7 n)))
      slot 0 =
      (natToWord 7 n).getD slot false := by
  let w := natToWord 7 n
  have hslot6 : slot ≤ 6 := by omega
  have hlist := c2_len7_word_read_ok slot n hslot hn
  have hlen : c2SimOrigin slot < (c2SimRun 30 (c2SimInitWord w)).length := by
    simpa [c2SimRun_length, c2SimInitWord_length] using c2SimOrigin_lt_bound_len7 slot hslot6
  have h30 : 30 ≤ c2SimOrigin slot := by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  have hj' : c2SimOrigin slot + 30 < c2SimBound :=
    c2SimOrigin_add30_lt_bound_len7 slot hslot6
  have hlist_inf :
      tape_has_glider_at (listToInfTape (c2SimRun 30 (c2SimInitWord w))) slot 0 =
        w.getD slot false := by
    rw [← listReadDiff_eq_tape_has_glider_at (c2SimRun 30 (c2SimInitWord w)) slot hlen,
      ← c2SimReadAt_eq_listReadDiff, hlist]
  have hinit := c2Len7SimInitWord_eq_cts_tape_cone_read slot n hslot hn
  have hagree :
      infRule110Steps 30 (listToInfTape (c2SimInitWord w)) (c2SimOrigin slot) =
        infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w) (c2SimOrigin slot) := by
    apply Eq.symm
    refine infRule110Steps_agree_Icc h30 fun k hk_lo hk_hi => ?_
    rw [cts_tape_idx_irrelevant idx 0 w k]
    exact (hinit k hk_lo hk_hi).symm
  have hrun := c2SimRun_eq_infRule110Steps_at (c2SimInitWord w) 30 (c2SimOrigin slot) h30
    (by simpa [c2SimInitWord_length] using hj')
  have hrun' :
      tape_has_glider_at (infRule110Steps 30 (listToInfTape (c2SimInitWord w))) slot 0 =
        w.getD slot false := by
    rw [← tape_has_glider_at_eq_of_origin
      (listToInfTape (c2SimRun 30 (c2SimInitWord w)))
      (infRule110Steps 30 (listToInfTape (c2SimInitWord w))) slot 0 hrun]
    exact hlist_inf
  rw [← tape_has_glider_at_eq_of_origin
    (infRule110Steps 30 (listToInfTape (c2SimInitWord w)))
    (infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w)) slot 0 hagree]
  exact hrun'

/-- **Stage 1b (InfTape, L ≤ 7):** extends partial C1 with isolated L=7 cert. -/
theorem cook_c2_tape_bit_inf_nat_upto7 (L slot n : ℕ) (hL : L ≤ 7) (hslot : slot < L) (hn : n < 2^L)
    (idx : ℕ) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n)))
      slot 0 =
      (natToWord L n).getD slot false := by
  by_cases h5 : L ≤ c2VerifyMaxLen
  · exact cook_c2_tape_bit_inf_nat L slot n h5 hslot hn idx
  · by_cases h6 : L ≤ 6
    · have hL6 : L = 6 := by
        simp [c2VerifyMaxLen] at h5 h6 hL ⊢; omega
      subst hL6
      exact cook_c2_tape_bit_inf_nat_len6 slot n hslot hn idx
    · have hL7 : L = 7 := by
        simp [c2VerifyMaxLen] at h5 h6 hL ⊢; omega
      subst hL7
      exact cook_c2_tape_bit_inf_nat_len7 slot n hslot hn idx

/-- **Partial C1 discharge (L ≤ 7):** bounded `natToWord` family on InfTape. -/
theorem cook_c2_tape_bit_ax_partial_upto7 (L slot n : ℕ) (hL : L ≤ 7) (hslot : slot < L)
    (hn : n < 2^L) (idx : ℕ) :
    cook_c2_decode_at slot
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n))) =
      (natToWord L n).getD slot false :=
  cook_c2_tape_bit_inf_nat_upto7 L slot n hL hslot hn idx

end Rule110
