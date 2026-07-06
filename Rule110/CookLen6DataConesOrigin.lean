import Rule110.CookC3PrimeDecodeSim
import Rule110.CookLen6InfTapeBridge
import Rule110.CookStage3CollisionModel
import Rule110.InfTape

set_option maxRecDepth 100000 in

/-!
# L=6 n=1 origin-cell C3′′ discharge (Stage 3)

After 390 bounded list steps, slot-origin cells match the
post-appendant phased encode. This module lifts that list witness to `InfTape`
`CookCtsEvalSimAtDataConesOrigin` without the C3′′ axiom for this case.
-/

namespace Rule110

theorem len6OneStepOriginCellOk_get (slot : ℕ) (hslot : slot < 6) :
    (c2SimRun 390 len6TruePhasedSupportInit).getD (c2SimOrigin slot) false =
      len6PostAppendantPhasedSupportInit.getD (c2SimOrigin slot) false := by
  have hall : ((List.range 6).all fun slot =>
      decide ((c2SimRun 390 len6TruePhasedSupportInit).getD (c2SimOrigin slot) false =
        len6PostAppendantPhasedSupportInit.getD (c2SimOrigin slot) false)) = true := by
    simpa [len6OneStepOriginCellOk] using len6_one_step_origin_cell_ok
  have hdec := (List.all_eq_true.mp hall) slot (List.mem_range.mpr hslot)
  exact (decide_eq_true_iff).1 hdec

theorem len6_slot_origin_lt_bound (slot : ℕ) (hslot : slot < 6) :
    c2SimOrigin slot < 2500 := by
  simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing]
  omega

private theorem len6_origin_list_sim_eq_post_list (slot : ℕ) (hslot : slot < 6) :
    listToInfTape (c2SimRun 390 len6TruePhasedSupportInit) (c2SimOrigin slot) =
      listToInfTape len6PostAppendantPhasedSupportInit (c2SimOrigin slot) := by
  have hb := len6_slot_origin_lt_bound slot hslot
  have hget := len6OneStepOriginCellOk_get slot hslot
  have hlen : c2SimOrigin slot < (c2SimRun 390 len6TruePhasedSupportInit).length := by
    rw [c2SimRun_length, len6TruePhasedSupportInit_length]; exact hb
  have hlen' : c2SimOrigin slot < len6PostAppendantPhasedSupportInit.length := by
    rw [len6PostAppendantPhasedSupportInit_length]; exact hb
  rw [listToInfTape_lt _ hlen, listToInfTape_lt _ hlen']
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rw [← List.getD_eq_getElem (l := c2SimRun 390 len6TruePhasedSupportInit) (d := false)
      (n := c2SimOrigin slot) hlen,
    ← List.getD_eq_getElem (l := len6PostAppendantPhasedSupportInit) (d := false)
      (n := c2SimOrigin slot) hlen']
  exact hget

private theorem len6_origin_inf_eq_phased_post (slot : ℕ) (hslot : slot < 6) :
    infRule110Steps 390
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word)
        (c2SimOrigin slot) =
      cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant
        (c2SimOrigin slot) := by
  have hb : c2SimOrigin slot < c2SimBound := by
    simpa [c2SimBound] using len6_slot_origin_lt_bound slot hslot
  have h1 := len6_origin_inf_steps_agree_init slot hslot
  have h2 := len6True_run_eq_inf_390_at_slot slot hslot
  have h3 := len6_origin_list_sim_eq_post_list slot hslot
  have h4 := len6Post_phased_target_eq_list_embed (c2SimOrigin slot) hb
  rw [h4, ← h3]
  exact h1.trans h2.symm

/-- **C3′′ discharge (L=6, n=1, `[true]` input):** origin cells match post-appendant encode. -/
theorem cook_cts_eval_sim_at_data_cones_origin_len6_one :
    CookCtsEvalSimAtDataConesOrigin cook_min_len6_cts 1 cook_min_len6_true_word 0 := by
  intro slot hslot
  have hslot6 : slot < 6 := by
    simp [CookCtsEvalSimAtDataConesOrigin, cts_eval_with_idx_one_true_len6,
      cook_min_len6_appendant_len, cook_min_len6_cts, cook_min_len6_appendant] at hslot
    exact hslot
  simp [CookCtsEvalSimAtDataConesOrigin, cts_eval_with_idx_one_true_len6,
    cook_total_M_from_one_len6, cook_min_len6_cts, cook_min_len6_appendant,
    cook_min_len6_appendant_len, c2SimOrigin, cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  exact len6_origin_inf_eq_phased_post slot hslot6

end Rule110
