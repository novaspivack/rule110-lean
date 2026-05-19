import Rule110.CookStage3CollisionModel
import Rule110.CookLen6DataConesOrigin
import Rule110.CookLen6PhasedPostDecode
import Rule110.CookLen6FirstBlock30
import Rule110.CTStoRule110
import Rule110.TMtoCTS

/-!
# Cook universality scaffold (SPEC_070_08 top-level target)

`rule110_turing_universal_from_cook` (zero sorry, zero bridge axioms) remains open.
This module records proved partial results on the Cook → CTS → Rule 110 chain.
-/

namespace Rule110

/-- L=6 minimal appendant: phased post-decode at n=1 without axiom. -/
theorem cook_len6_phased_post_decode_one :
    CookCtsPhasedPostDecodeAt cook_min_len6_cts 1 cook_min_len6_true_word 0 :=
  cook_cts_phased_post_decode_len6_one

/-- L=6 first block (30 steps): slot-0 origin matches post-appendant encode. -/
theorem cook_len6_first_block_30_origin :
    infRule110Steps 30
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word)
        (c2SimOrigin 0) =
      cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant
        (c2SimOrigin 0) :=
  len6_first_block_30_origin_inf

/-- Standard empty-appendant CTS: C3′ holds at all step counts (vacuous readback). -/
theorem cook_standard_empty_data_cones_all (n : ℕ) :
    CookCtsEvalSimAtDataCones cook_standard_empty_cts n [] 0 :=
  cook_standard_empty_cts_data_cones n

/-- L=6 minimal appendant: C3′′ origin readback at n=1 without axiom. -/
theorem cook_len6_data_cones_origin_one :
    CookCtsEvalSimAtDataConesOrigin cook_min_len6_cts 1 cook_min_len6_true_word 0 :=
  cook_cts_eval_sim_at_data_cones_origin_len6_one

/-- Standard empty-appendant CTS: C3′′ holds at all step counts (vacuous). -/
theorem cook_standard_empty_data_cones_origin_all (n : ℕ) :
    CookCtsEvalSimAtDataConesOrigin cook_standard_empty_cts n [] 0 :=
  cook_standard_empty_cts_data_cones_origin n

/-- Stage 1 far-field ether drift is discharged (`cook_cts_step_sim_ax`). -/
theorem cook_stage1_step_sim (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool) (i : ℕ)
    (L : ℕ) (M : ℕ) (hi : cts_word_far_boundary w.length + M ≤ i) :
    infRule110Steps M (cts_to_rule110_tape cts idx w) i = cookEther (i + 4 * M) :=
  cook_cts_step_sim_ax cts idx w i L M hi

end Rule110
