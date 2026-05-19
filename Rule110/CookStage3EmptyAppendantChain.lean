import Rule110.CookStage3CollisionModel
import Rule110.CookConstructionCollisionCerts
import Rule110.CookPhasedSupportInfTapeBridge
import Rule110.CookEmptyAppendantSim
import Rule110.CookCollisionWitnesses
import Rule110.CTStoRule110
import Rule110.InfTape

set_option maxRecDepth 4096 in

/-!
# Empty-appendant Stage 3 status chain (SPEC_070_08)

Records what is discharged vs. what remains for the standard empty CTS (`w₀ = []`).

**Discharged (no legacy C3 axiom):** C3′ and C3′′ at all `n`; phased post-decode vacuous;
list↔InfTape init and step semantics on the slot-0 read cone.

**Open (legacy `CookCtsEvalSim`):** one-step support-sector fixed point at `M = 30`.
Bounded simulation refutes slot-0 cone stability (`empty_phased_support_cone_not_fixed_30`);
Cook §4 kind-2 collision certificate matches the same encoding.

Induction from n=1 to all `n` is in `CookStage3Verification` (`cook_cts_eval_sim_empty_from_one_step`).
-/

namespace Rule110

/-- Support placements return the same phased tape after `M` Rule 110 steps. -/
def CookCtsSupportPlacementsFixed (M : ℕ) (ps : List GliderPlacement) : Prop :=
  gliders_to_tape_phased ps = infRule110Steps M (gliders_to_tape_phased ps)

/-- Legacy empty-appendant n=1 ↔ 30-step support-sector fixed point. -/
theorem cook_cts_eval_sim_empty_one_step_iff_support_fixed (cts : CyclicTagSystem)
    (hzero : ∀ k, k < cts.cycleLen → (cts.appendants.getD k []).length = 0) :
    CookCtsEvalSim cts 1 (w₀ := []) ↔
      CookCtsSupportPlacementsFixed 30 cts_support_placements := by
  constructor
  · intro h
    rw [CookCtsEvalSim] at h
    rw [cts_eval_one_empty cts, cts_word_to_placements_phased_with_support_nil] at h
    rw [cts_to_rule110_tape_phased_with_support, cts_word_to_placements_phased_with_support_nil] at h
    have hM : cook_total_M cts 1 = 30 := by
      rw [cook_total_M_succ_empty_appendant cts 0 hzero]
      simp [cook_total_M, cook_total_M_from]
    rw [hM] at h
    exact h
  · intro h
    rw [CookCtsEvalSim, cts_eval_one_empty cts, cts_word_to_placements_phased_with_support_nil,
        cts_to_rule110_tape_phased_with_support, cts_word_to_placements_phased_with_support_nil]
    have hM : cook_total_M cts 1 = 30 := by
      rw [cook_total_M_succ_empty_appendant cts 0 hzero]
      simp [cook_total_M, cook_total_M_from]
    rw [hM]
    exact h

/-- Slot-0 read cone is not preserved after 30 bounded list steps. -/
theorem cook_cts_support_slot0_cone_not_fixed_30 :
    emptyPhasedSupportConeFixed30 = false :=
  empty_phased_support_cone_not_fixed_30

/-- Cook §4 kind-2 certificate on the same empty phased-with-support encoding. -/
theorem cook_empty_appendant_kind2_collision_negative :
    collisionSimConeFixed kind2EmptySupportInit 30 0 = false :=
  kind2_empty_support_slot0_cone_not_fixed_30

/-- C3′ + C3′′ + phased decode for all `n` at empty input (no bridge axioms). -/
structure CookEmptyAppendantC3PrimeDischarged where
  data_cones : ∀ (cts : CyclicTagSystem) (n : ℕ),
      CookCtsEvalSimAtDataCones cts n [] 0
  data_cones_origin : ∀ (cts : CyclicTagSystem) (n : ℕ),
      CookCtsEvalSimAtDataConesOrigin cts n [] 0
  phased_decode : ∀ (cts : CyclicTagSystem) (n : ℕ),
      CookCtsPhasedPostDecodeAt cts n [] 0
  standard_empty : ∀ n, CookCtsEvalSimAtDataCones cook_standard_empty_cts n [] 0

theorem cook_empty_appendant_c3prime_discharged : CookEmptyAppendantC3PrimeDischarged where
  data_cones := fun cts n => cook_cts_eval_sim_at_data_cones_empty_input cts n 0
  data_cones_origin := fun cts n => cook_cts_eval_sim_at_data_cones_origin_empty_input cts n 0
  phased_decode := fun cts n => cook_cts_phased_post_decode_empty_input cts n 0
  standard_empty := cook_standard_empty_cts_data_cones

theorem cook_empty_appendant_origin_list_inf_30 :
    listToInfTape (c2SimRun 30 emptyPhasedSupportInit) (cts_slot_origin 0) =
      infRule110Steps 30 (cts_to_rule110_tape_phased_with_support (CyclicTagSystem.mk []) [])
        (cts_slot_origin 0) := by
  rw [emptyPhasedSupport_origin_run_eq_inf_30, emptyPhasedSupport_origin_inf_steps_agree]

theorem kind2_empty_support_init_eq :
    kind2EmptySupportInit = emptyPhasedSupportInit := by
  simp [kind2EmptySupportInit, emptyPhasedSupportInit, collisionSimInit,
    cts_word_to_placements_phased_with_support_nil]

private theorem emptyPhasedSupportInit_origin_lt_length :
    cts_slot_origin 0 < emptyPhasedSupportInit.length := by
  simp [emptyPhasedSupportInit, c2SimBound, cts_slot_origin, cts_tape_origin, cts_glider_spacing]

/-- **Negative theorem:** support-sector 30-step fixed point refuted at slot origin. -/
theorem cook_cts_support_placements_not_fixed_30 :
    ¬ CookCtsSupportPlacementsFixed 30 cts_support_placements := by
  intro h
  dsimp [CookCtsSupportPlacementsFixed] at h
  apply empty_phased_support_origin_list_not_fixed_30
  have hinit := emptyPhasedSupportInitReadConeOk_get 30 (by decide)
  have hd : emptySlot0ConeLo + 30 = cts_slot_origin 0 := by
    simp [emptySlot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  have hinit_at :
      listToInfTape emptyPhasedSupportInit (cts_slot_origin 0) =
        gliders_to_tape_phased cts_support_placements (cts_slot_origin 0) := by
    rw [← hd, hinit]
    simp [cts_to_rule110_tape_phased_with_support, cts_word_to_placements_phased_with_support_nil]
  calc
    listToInfTape (c2SimRun 30 emptyPhasedSupportInit) (cts_slot_origin 0)
        = infRule110Steps 30 (listToInfTape emptyPhasedSupportInit) (cts_slot_origin 0) :=
      emptyPhasedSupport_origin_run_eq_inf_30
    _ = infRule110Steps 30 (gliders_to_tape_phased cts_support_placements) (cts_slot_origin 0) :=
      emptyPhasedSupport_origin_inf_steps_agree.symm
    _ = gliders_to_tape_phased cts_support_placements (cts_slot_origin 0) :=
      (congrArg (fun t => t (cts_slot_origin 0)) h).symm
    _ = listToInfTape emptyPhasedSupportInit (cts_slot_origin 0) := hinit_at.symm

/-- Legacy `CookCtsEvalSim` at n=1 for the standard empty CTS is refuted. -/
theorem cook_standard_empty_cts_legacy_c3_n1_blocked :
    ¬ CookCtsEvalSim cook_standard_empty_cts 1 [] := by
  intro h
  have hiff := (cook_cts_eval_sim_empty_one_step_iff_support_fixed cook_standard_empty_cts
    (fun k hk => by
      have hk0 : k = 0 := by
        simp [cook_standard_empty_cts, CyclicTagSystem.cycleLen] at hk
        omega
      subst hk0
      rfl)).1 h
  exact cook_cts_support_placements_not_fixed_30 hiff

structure CookLegacyC3EmptyN1Blocked where
  support_not_fixed : ¬ CookCtsSupportPlacementsFixed 30 cts_support_placements
  legacy_sim_blocked : ¬ CookCtsEvalSim cook_standard_empty_cts 1 []
  c3prime_discharged : CookEmptyAppendantC3PrimeDischarged
  kind2_collision : collisionSimConeFixed kind2EmptySupportInit 30 0 = false

theorem cook_legacy_c3_empty_n1_blocked : CookLegacyC3EmptyN1Blocked where
  support_not_fixed := cook_cts_support_placements_not_fixed_30
  legacy_sim_blocked := cook_standard_empty_cts_legacy_c3_n1_blocked
  c3prime_discharged := cook_empty_appendant_c3prime_discharged
  kind2_collision := cook_empty_appendant_kind2_collision_negative

end Rule110
