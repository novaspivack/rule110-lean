import Rule110.CookC3PrimeDecodeSim
import Rule110.CookLen6DataConesOrigin
import Rule110.CookLen6InfTapeBridge

set_option maxRecDepth 100000 in

/-!
# Approach #15: phased post-decode on InfTape (L=6 n=1)

List witness `len6_one_step_phased_post_decode_ok` lifts to `tape_has_glider_at` on
`infRule110Steps` output using the list↔InfTape glider bridge and origin stepping agreement.
-/

namespace Rule110

private theorem len6PhasedPostDecodeOk_get (slot : ℕ) (hslot : slot < 6) :
    listPhasedGliderAt
        (cts_word_to_placements_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant)
        (c2SimRun 390 len6TruePhasedSupportInit) slot =
      cook_min_len6_appendant.getD slot false := by
  have hall : ((List.range 6).all fun slot =>
      decide (listPhasedGliderAt
          (cts_word_to_placements_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant)
          (c2SimRun 390 len6TruePhasedSupportInit) slot =
        cook_min_len6_appendant.getD slot false)) = true := by
    simpa [len6OneStepPhasedPostDecodeOk] using len6_one_step_phased_post_decode_ok
  have hdec := (List.all_eq_true.mp hall) slot (List.mem_range.mpr hslot)
  exact (decide_eq_true_iff).1 hdec

/-- **Approach #15 (InfTape):** phased post-decode matches appendant word after 390 steps. -/
theorem len6_phased_post_decode_inf_one (slot : ℕ) (hslot : slot < 6) :
    let ps := cts_word_to_placements_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant
    tape_has_glider_at
        (infRule110Steps 390
          (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word))
        slot (accumPhaseAt ps (c2SimOrigin slot)) =
      cook_min_len6_appendant.getD slot false := by
  intro ps
  set fin := c2SimRun 390 len6TruePhasedSupportInit
  have hb : c2SimOrigin slot < c2SimBound := by
    simpa [c2SimBound] using len6_slot_origin_lt_bound slot hslot
  have hlen : c2SimOrigin slot < fin.length := by
    rw [c2SimRun_length, len6TruePhasedSupportInit_length]; exact hb
  set accum := accumPhaseAt ps (c2SimOrigin slot)
  have hlist := len6PhasedPostDecodeOk_get slot hslot
  have hbridge := listPhasedGliderAt_eq_tape_has_glider_at ps fin slot hlen
  have horig := len6_origin_inf_eq_list_fin slot hslot
  have hinf := tape_has_glider_at_eq_of_origin
      (infRule110Steps 390
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word))
      (listToInfTape fin) slot accum horig
  exact hinf.trans (hbridge.symm.trans hlist)

/-- **Phased post-decode discharge (L=6, n=1):** all six slots without axiom. -/
theorem cook_cts_phased_post_decode_len6_one :
    CookCtsPhasedPostDecodeAt cook_min_len6_cts 1 cook_min_len6_true_word 0 := by
  intro slot hslot
  have hslot6 : slot < 6 := by
    simp [CookCtsPhasedPostDecodeAt, cts_eval_with_idx_one_true_len6,
      cook_min_len6_appendant_len, cook_min_len6_cts, cook_min_len6_appendant] at hslot
    exact hslot
  simp [CookCtsPhasedPostDecodeAt, cts_eval_with_idx_one_true_len6,
    cook_total_M_from_one_len6, cook_min_len6_cts, cook_min_len6_appendant,
    cook_min_len6_appendant_len, c2SimOrigin, cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  exact len6_phased_post_decode_inf_one slot hslot6

end Rule110
