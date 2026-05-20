import Rule110.CookStage3CollisionModel
import Rule110.CookCollisionWitnesses
import Rule110.CyclicTagSystem
import Rule110.InfTape

/-!
# Stage 3 C3′′ induction step (composition)

Cone helpers and the `n + 1` composition schema for origin-cell readback via
`infRule110Steps_add` and `cook_total_M_from_microstep_split`.
-/

namespace Rule110

/-! ## Cone helpers -/

theorem cook_cts_slot_cone_cell_eq_origin (slot : ℕ) :
    cook_cts_slot_cone_cell slot 30 = cts_slot_origin slot := by
  simp [cook_cts_slot_cone_cell, cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  omega

/-- Every cell in the `M₂`-step Icc around a slot origin lies in the 61-cell read cone. -/
theorem cook_cts_tail_icc_cell_in_read_cone (slot M₂ j : ℕ)
    (hM : M₂ ≤ 30) (hj_lo : cts_slot_origin slot - M₂ ≤ j) (hj_hi : j ≤ cts_slot_origin slot + M₂) :
    ∃ d, d < 61 ∧ j = cook_cts_slot_cone_cell slot d := by
  refine ⟨j + 30 - cts_slot_origin slot, ?_, ?_⟩
  · have horig : 30 ≤ cts_slot_origin slot := by
      simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing]
      omega
    have hj_ge : cts_slot_origin slot - 30 ≤ j := by
      have hsub : cts_slot_origin slot - 30 ≤ cts_slot_origin slot - M₂ := by
        simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing] at *
        omega
      exact Nat.le_trans hsub hj_lo
    omega
  · have hj_ge : cts_slot_origin slot - 30 ≤ j := by
      have hsub : cts_slot_origin slot - 30 ≤ cts_slot_origin slot - M₂ := by
        simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing] at *
        omega
      exact Nat.le_trans hsub hj_lo
    calc j
        = cts_slot_origin slot - 30 + (j + 30 - cts_slot_origin slot) := by
          have horig : 30 ≤ cts_slot_origin slot := by
            simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing]
            omega
          omega
        _ = cts_slot_origin slot - 30 + (j + 30 - cts_slot_origin slot) := rfl
        _ = cook_cts_slot_cone_cell slot (j + 30 - cts_slot_origin slot) := by
          simp [cook_cts_slot_cone_cell, cts_slot_origin, cts_tape_origin, cts_glider_spacing]

/-! ## Tail origin hypotheses -/

/-- After `M₁` steps, `M₂`-step tail evolution from the actual tape matches tail evolution
    from the ideal mid-encode at each slot origin. Required for multi-step C3′′ via
    `infRule110Steps_add`. -/
def CookCtsTailOriginHyp (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ) : Prop :=
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let mid := cts_to_rule110_tape_phased_with_support_idx cts idx₁ w₁
  let evolved := infRule110Steps M₁ init
  ∀ slot, slot < w₁.length →
    infRule110Steps M₂ evolved (cts_slot_origin slot) =
      infRule110Steps M₂ mid (cts_slot_origin slot)

/-- After `M₁` steps, `M₂`-step tail from the actual tape matches mid-encode at every slot
    origin in the **final** `(n+1)`-step CTS word (not merely the one-step post-word). -/
def CookCtsTailOriginHypFinal (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w_mid w_final : List Bool)
    (idx_mid M₁ M₂ : ℕ) : Prop :=
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let mid := cts_to_rule110_tape_phased_with_support_idx cts idx_mid w_mid
  let evolved := infRule110Steps M₁ init
  ∀ slot, slot < w_final.length →
    infRule110Steps M₂ evolved (cts_slot_origin slot) =
      infRule110Steps M₂ mid (cts_slot_origin slot)

/-! ## Induction step schema -/

/-- **Induction step (C3′′):** one microstep + tail readback on the final word + `infRule110Steps_add`. -/
theorem cook_cts_eval_sim_at_data_cones_origin_succ_schema
    (cts : CyclicTagSystem) (n : ℕ) (w₀ w_mid w_final : List Bool) (idx₀ idx_mid idx_final M₁ : ℕ)
    (h_eval : cts.cts_eval_with_idx (n + 1) w₀ idx₀ = (w_final, idx_final))
    (h_mid : cts.cts_step idx₀ w₀ = (w_mid, idx_mid))
    (ih : CookCtsEvalSimAtDataConesOrigin cts n w_mid idx_mid)
    (htail : CookCtsTailOriginHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁
      (cook_total_M_from cts n idx_mid))
    (hMsplit : cook_total_M_from cts (n + 1) idx₀ = M₁ + cook_total_M_from cts n idx_mid) :
    CookCtsEvalSimAtDataConesOrigin cts (n + 1) w₀ idx₀ := by
  intro slot hslot
  have hlen :
      (cts.cts_eval_with_idx (n + 1) w₀ idx₀).1 = w_final := by
    simpa using congrArg Prod.fst h_eval
  have hidx :
      (cts.cts_eval_with_idx (n + 1) w₀ idx₀).2 = idx_final := by
    simpa using congrArg Prod.snd h_eval
  have hslotW : slot < w_final.length := hlen ▸ hslot
  have h_inner :
      cts.cts_eval_with_idx n w_mid idx_mid = (w_final, idx_final) := by
    rw [← h_eval, CyclicTagSystem.cts_eval_with_idx_succ, h_mid]
  have hw_eq : (cts.cts_eval_with_idx n w_mid idx_mid).1 = w_final :=
    congrArg Prod.fst h_inner
  have hidx_eq : (cts.cts_eval_with_idx n w_mid idx_mid).2 = idx_final :=
    congrArg Prod.snd h_inner
  have hslot' : slot < (cts.cts_eval_with_idx n w_mid idx_mid).1.length :=
    hw_eq ▸ hslotW
  dsimp [CookCtsEvalSimAtDataConesOrigin] at ih
  dsimp [CookCtsEvalSimAtDataConesOrigin]
  rw [hMsplit, infRule110Steps_add]
  have hdone := (htail slot hslotW).trans (ih slot hslot')
  have hfst :
      (cts.cts_eval_with_idx (n + 1) w₀ idx₀).1 =
        (cts.cts_eval_with_idx n w_mid idx_mid).1 :=
    hlen.trans hw_eq.symm
  have hsnd :
      (cts.cts_eval_with_idx (n + 1) w₀ idx₀).2 =
        (cts.cts_eval_with_idx n w_mid idx_mid).2 :=
    hidx.trans hidx_eq.symm
  have htarget :
      cts_to_rule110_tape_phased_with_support_idx cts (cts.cts_eval_with_idx (n + 1) w₀ idx₀).2
          (cts.cts_eval_with_idx (n + 1) w₀ idx₀).1 (cts_slot_origin slot) =
        cts_to_rule110_tape_phased_with_support_idx cts (cts.cts_eval_with_idx n w_mid idx_mid).2
          (cts.cts_eval_with_idx n w_mid idx_mid).1 (cts_slot_origin slot) := by
    rw [hsnd, hfst]
  exact hdone.trans htarget.symm

end Rule110
