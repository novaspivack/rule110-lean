import Rule110.CookC3PrimeDecodeSim
import Rule110.CookLen6InfTapeBridge

set_option maxRecDepth 100000 in

/-!
# Approach #16: L=6 first-block (30-step) slot-0 origin (Stage 3)
-/

namespace Rule110

private theorem len6FirstBlock30OriginOk_get :
    (c2SimRun 30 len6TruePhasedSupportInit).getD (c2SimOrigin 0) false =
      len6PostAppendantPhasedSupportInit.getD (c2SimOrigin 0) false := by
  simpa [len6FirstBlock30OriginOk] using len6_first_block_30_origin_ok

theorem len6_first_block_30_origin_inf :
    infRule110Steps 30
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word)
        (c2SimOrigin 0) =
      cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant
        (c2SimOrigin 0) := by
  have hb : c2SimOrigin 0 < c2SimBound := by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing, c2SimBound]
  have hfin :
      listToInfTape (c2SimRun 30 len6TruePhasedSupportInit) (c2SimOrigin 0) =
        listToInfTape len6PostAppendantPhasedSupportInit (c2SimOrigin 0) := by
    have hlen : c2SimOrigin 0 < (c2SimRun 30 len6TruePhasedSupportInit).length := by
      rw [c2SimRun_length, len6TruePhasedSupportInit_length]; exact hb
    have hlen' : c2SimOrigin 0 < len6PostAppendantPhasedSupportInit.length := by
      rw [len6PostAppendantPhasedSupportInit_length]; exact hb
    rw [listToInfTape_lt _ hlen, listToInfTape_lt _ hlen']
    rw [List.get_eq_getElem, List.get_eq_getElem]
    rw [← List.getD_eq_getElem (l := c2SimRun 30 len6TruePhasedSupportInit) (d := false)
        (n := c2SimOrigin 0) hlen,
      ← List.getD_eq_getElem (l := len6PostAppendantPhasedSupportInit) (d := false)
        (n := c2SimOrigin 0) hlen']
    exact len6FirstBlock30OriginOk_get
  have hpost := len6Post_phased_target_eq_list_embed (c2SimOrigin 0) hb
  rw [hpost, ← hfin]
  exact len6_slot0_origin_inf_steps_agree_init_30.trans len6True_origin_run_eq_inf_30.symm

end Rule110
