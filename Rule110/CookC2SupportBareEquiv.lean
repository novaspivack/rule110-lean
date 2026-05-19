import Mathlib.Data.List.GetD

import Rule110.CookC2SupportConeDisjoint
import Rule110.CookC2InfTapeBridge

set_option maxRecDepth 200000 in

/-!
# Ossifier overlay does not affect C2 list-sim readback (slots ≤ 20)

Init-cone cell equality + `infRule110Steps_agree_Icc` (ossifier patch is spatially separated).
-/

namespace Rule110

private theorem map_range_getD (f : ℕ → Bool) (i n : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i false = f i := by
  have hi' : i < ((List.range n).map f).length := by
    simpa [List.length_map, List.length_range] using hi
  rw [List.getD_eq_getElem (n := i) (hn := hi')]
  simp [List.getElem_map, List.getElem_range (by simpa [List.length_range] using hi)]

private theorem listToInfTape_getD_eq (l : List Bool) {i : ℕ} (hi : i < l.length) :
    listToInfTape l i = l.getD i false := by
  simp [listToInfTape, hi]

private theorem c2SimOrigin_le_1840 (slot : ℕ) (hslot : slot ≤ 20) :
    c2SimOrigin slot ≤ 1840 := by
  simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]
  nlinarith

private theorem c2SimOrigin_add30_lt_bound (slot : ℕ) (hslot : slot ≤ 20) :
    c2SimOrigin slot + 30 < c2SimBound := by
  have := c2SimOrigin_le_1840 slot hslot
  simp [c2SimBound, c2SimOrigin, cts_tape_origin, cts_glider_spacing]
  omega

private theorem c2SimOrigin_ge_30 (slot : ℕ) : 30 ≤ c2SimOrigin slot := by
  simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]
  omega

private theorem c2SimInitWordWithOssifier_getD_eq_bare (w : List Bool) (slot : ℕ) (hslot : slot ≤ 20)
    (k : ℕ) (hk_lo : c2SimOrigin slot - 30 ≤ k) (hk_hi : k ≤ c2SimOrigin slot + 30) :
    (c2SimInitWordWithOssifier w).getD k false = (c2SimInitWord w).getD k false := by
  have hk : k < c2SimBound := by
    have := c2SimOrigin_add30_lt_bound slot hslot
    omega
  have hnot : ¬ (cts_ossifier_origin ≤ k ∧ k < cts_ossifier_origin + cookOssifierPatchBits.length) :=
    c2_ossifier_patch_outside_read_cone slot hslot k hk_lo hk_hi
  show ((List.range c2SimBound).map (c2SimCellForWordWithOssifier w)).getD k false =
      ((List.range c2SimBound).map (c2SimCellForWord w)).getD k false
  rw [map_range_getD (f := c2SimCellForWordWithOssifier w) k c2SimBound hk,
    map_range_getD (f := c2SimCellForWord w) k c2SimBound hk]
  simp [c2SimCellForWordWithOssifier, hnot]

theorem c2SimInitWordWithOssifier_listToInfTape_eq_bare (w : List Bool) (slot : ℕ)
    (hslot : slot ≤ 20) (k : ℕ) (hk_lo : c2SimOrigin slot - 30 ≤ k)
    (hk_hi : k ≤ c2SimOrigin slot + 30) :
    listToInfTape (c2SimInitWordWithOssifier w) k =
      listToInfTape (c2SimInitWord w) k := by
  have hk : k < c2SimBound := by
    have := c2SimOrigin_add30_lt_bound slot hslot
    omega
  have hk_oss : k < (c2SimInitWordWithOssifier w).length := by
    rw [c2SimInitWordWithOssifier_length]; exact hk
  have hk_bare : k < (c2SimInitWord w).length := by
    rw [c2SimInitWord_length]; exact hk
  rw [listToInfTape_getD_eq (c2SimInitWordWithOssifier w) hk_oss,
    listToInfTape_getD_eq (c2SimInitWord w) hk_bare]
  exact c2SimInitWordWithOssifier_getD_eq_bare w slot hslot k hk_lo hk_hi

theorem c2SimRun_withOssifier_eq_bare_at_origin (w : List Bool) (slot : ℕ) (hslot : slot ≤ 20) :
    (c2SimRun 30 (c2SimInitWordWithOssifier w)).getD (c2SimOrigin slot) false =
      (c2SimRun 30 (c2SimInitWord w)).getD (c2SimOrigin slot) false := by
  let origin := c2SimOrigin slot
  have h30 : 30 ≤ origin := c2SimOrigin_ge_30 slot
  have hj : origin + 30 < c2SimBound := c2SimOrigin_add30_lt_bound slot hslot
  have horigin : origin < c2SimBound := by omega
  have hr_oss := c2SimRun_eq_infRule110Steps_at (c2SimInitWordWithOssifier w) 30 origin h30
    (by rw [c2SimInitWordWithOssifier_length]; exact hj)
  have hr_bare := c2SimRun_eq_infRule110Steps_at (c2SimInitWord w) 30 origin h30
    (by rw [c2SimInitWord_length]; exact hj)
  have hagree : ∀ k, origin - 30 ≤ k → k ≤ origin + 30 →
      listToInfTape (c2SimInitWordWithOssifier w) k =
        listToInfTape (c2SimInitWord w) k :=
    fun k hk_lo hk_hi =>
      c2SimInitWordWithOssifier_listToInfTape_eq_bare w slot hslot k hk_lo hk_hi
  have heq : infRule110Steps 30 (listToInfTape (c2SimInitWordWithOssifier w)) origin =
      infRule110Steps 30 (listToInfTape (c2SimInitWord w)) origin :=
    infRule110Steps_agree_Icc h30 hagree
  have hrun_len : origin < (c2SimRun 30 (c2SimInitWordWithOssifier w)).length := by
    rw [c2SimRun_length, c2SimInitWordWithOssifier_length]; exact horigin
  have hrun_len' : origin < (c2SimRun 30 (c2SimInitWord w)).length := by
    rw [c2SimRun_length, c2SimInitWord_length]; exact horigin
  rw [← listToInfTape_getD_eq (c2SimRun 30 (c2SimInitWordWithOssifier w)) hrun_len,
    hr_oss, heq, ← hr_bare,
    listToInfTape_getD_eq (c2SimRun 30 (c2SimInitWord w)) hrun_len']

theorem c2SimReadAtWithOssifier_eq_bare (slot : ℕ) (w : List Bool) (hslot : slot ≤ 20) :
    c2SimReadAtWithOssifier slot w = c2SimReadAt slot w := by
  dsimp [c2SimReadAtWithOssifier, c2SimReadAt]
  rw [c2SimRun_withOssifier_eq_bare_at_origin w slot hslot]

/-- Analytical L ≤ 7 support readback: ossifier overlay + bare list sim + cone disjointness. -/
theorem c2_support_word_read_from_bare (L slot n : ℕ) (hL : L ≤ 7) (hslot : slot < L) (hn : n < 2 ^ L) :
    c2SimReadAtWithOssifier slot (natToWord L n) = (natToWord L n).getD slot false := by
  rw [c2SimReadAtWithOssifier_eq_bare slot (natToWord L n) (by omega)]
  exact cook_c2_tape_bit_list_upto7 L slot n hL hslot hn

theorem c2_support_len7_word_read_from_bare (slot n : ℕ) (hslot : slot < 7) (hn : n < 2 ^ 7) :
    c2SimReadAtWithOssifier slot (natToWord 7 n) = (natToWord 7 n).getD slot false :=
  c2_support_word_read_from_bare 7 slot n (by decide) hslot hn

end Rule110
