import Rule110.CookC2VerifySupportLen5

/-!
# Ossifier patch disjoint from C2 list-sim read cones

The left ossifier overlay in `c2SimInitWordWithOssifier` sits at indices 500–505;
data-slot read cones (30-step backward light cone) begin at index 970 for slot 0
and only move right with slot index.
-/

namespace Rule110

private theorem c2SimOrigin_cone_lo_ge_506 (slot : ℕ) :
    cts_ossifier_origin + cookOssifierPatchBits.length ≤ c2SimOrigin slot - 30 := by
  simp [c2SimOrigin, cts_ossifier_origin, cts_tape_origin, cts_glider_spacing,
    cookOssifierPatchBits_length]
  omega

/-- Ossifier patch lies outside the 30-step read cone for all data slots. -/
theorem c2_ossifier_patch_outside_read_cone (slot : ℕ) (_hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : c2SimOrigin slot - 30 ≤ k) (_hk_hi : k ≤ c2SimOrigin slot + 30) :
    ¬ (cts_ossifier_origin ≤ k ∧ k < cts_ossifier_origin + cookOssifierPatchBits.length) := by
  intro h
  have h506 := c2SimOrigin_cone_lo_ge_506 slot
  rcases h with ⟨hk_le, hk_lt⟩
  have hk_end : k < cts_ossifier_origin + cookOssifierPatchBits.length := by
    simpa [cookOssifierPatchBits_length] using hk_lt
  linarith [hk_lo, h506, hk_le, hk_end]

theorem c2SimCellForWordWithOssifier_eq_bare_off_ossifier (w : List Bool) (k : ℕ)
    (hnot : ¬ (cts_ossifier_origin ≤ k ∧ k < cts_ossifier_origin + cookOssifierPatchBits.length)) :
    c2SimCellForWordWithOssifier w k = c2SimCellForWord w k := by
  simp [c2SimCellForWordWithOssifier, hnot]

end Rule110
