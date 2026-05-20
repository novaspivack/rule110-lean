import Rule110.CookStage3OriginSucc
import Rule110.CookCollisionWitnesses

/-!
# Final-word tail geometry (Cook C3′′ extended slots)

Far-boundary lemmas and final-word tail **evolution** predicate (Icc agreement on evolved vs
mid). Discharge of `CookCtsTailOriginHypFinal` for growing words reduces to
`CookCtsTailEvolutionHypFinal`.
-/

namespace Rule110

/-! ## Far-boundary geometry -/

/-- Slot indices at least one past the word end lie at or beyond the far boundary. -/
theorem cts_word_far_boundary_le_slot_origin (n slot : ℕ) (h : n + 1 ≤ slot) :
    cts_word_far_boundary n ≤ cts_slot_origin slot := by
  simp [cts_word_far_boundary, cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  omega

theorem cts_slot_origin_outside_word (w : List Bool) (slot : ℕ) (h : w.length + 1 ≤ slot) :
    cts_word_outside_all w (cts_slot_origin slot) := by
  simp [cts_word_outside_all]
  exact cts_word_far_boundary_le_slot_origin w.length slot h

/-! ## Final-word tail evolution -/

/-- After `M₁` steps, evolved vs mid agree on every Icc needed for `M₂`-step tails at
    **final-word** slot origins (covers appendant-grown slots). Requires `M₂ ≤ origin slot`
    for each slot (same regime as `cook_cts_tail_origin_of_evolution`). -/
def CookCtsTailEvolutionHypFinal (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w_mid w_final : List Bool)
    (idx_mid M₁ M₂ : ℕ) : Prop :=
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let mid := cts_to_rule110_tape_phased_with_support_idx cts idx_mid w_mid
  let evolved := infRule110Steps M₁ init
  ∀ slot, slot < w_final.length →
    M₂ ≤ cts_slot_origin slot →
      ∀ j, cts_slot_origin slot - M₂ ≤ j → j ≤ cts_slot_origin slot + M₂ →
        evolved j = mid j

/-- Icc agreement on the final word implies final-word tail origin when `M₂ ≤ origin`. -/
theorem cook_cts_tail_origin_final_of_evolution (cts : CyclicTagSystem) (idx₀ : ℕ)
    (w₀ w_mid w_final : List Bool) (idx_mid M₁ M₂ : ℕ) (slot : ℕ) (hslot : slot < w_final.length)
    (hbound : M₂ ≤ cts_slot_origin slot)
    (htail : CookCtsTailEvolutionHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂) :
    let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
    let mid := cts_to_rule110_tape_phased_with_support_idx cts idx_mid w_mid
    let evolved := infRule110Steps M₁ init
    infRule110Steps M₂ evolved (cts_slot_origin slot) =
      infRule110Steps M₂ mid (cts_slot_origin slot) := by
  apply infRule110Steps_agree_Icc hbound
  intro j hj_lo hj_hi
  exact htail slot hslot hbound j hj_lo hj_hi

theorem cook_cts_tail_origin_final_of_evolution_all (cts : CyclicTagSystem) (idx₀ : ℕ)
    (w₀ w_mid w_final : List Bool) (idx_mid M₁ M₂ : ℕ)
    (hbound : ∀ slot, slot < w_final.length → M₂ ≤ cts_slot_origin slot)
    (htail : CookCtsTailEvolutionHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂) :
    CookCtsTailOriginHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ := by
  intro slot hslot
  by_cases hM₂ : M₂ = 0
  · rw [hM₂]
    have hbound' := hbound slot hslot
    have heq := htail slot hslot hbound' (cts_slot_origin slot) (by omega) (by omega)
    rw [infRule110Steps_zero, infRule110Steps_zero]
    exact heq
  · exact cook_cts_tail_origin_final_of_evolution cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ slot hslot
      (hbound slot hslot) htail

end Rule110
