import Rule110.CookLen6DataConesOrigin
import Rule110.CookLen6InfTapeBridge
import Rule110.CookLen6TailEvolution
import Rule110.CookStage3OriginSucc

/-!
# L=6 tail-origin discharge (`M₁ = 390`, `M₂ = 30`)

List certificates in `CookLen6TailEvolution` plus InfTape bridges discharge
`CookCtsTailOriginHyp` for the minimal L=6 input. The evolved-side InfTape bridge is one
open micro-lemma (`len6_evolved_inf30_eq_list420_at_slot`); mid-side and list composition
are proved here.
-/

namespace Rule110

private theorem len6Tail420OriginOk_get (slot : ℕ) (hslot : slot < 6) :
    (c2SimRun 420 len6TruePhasedSupportInit).getD (c2SimOrigin slot) false =
      (c2SimRun 30 len6PostAppendantPhasedSupportInit).getD (c2SimOrigin slot) false := by
  have hall : ((List.range 6).all fun slot =>
      decide ((c2SimRun 420 len6TruePhasedSupportInit).getD (c2SimOrigin slot) false =
        (c2SimRun 30 len6TailMidList).getD (c2SimOrigin slot) false)) = true := by
    simpa [len6Tail420OriginOk, len6TailMidList] using len6_tail420_origin_ok
  have hdec := (List.all_eq_true.mp hall) slot (List.mem_range.mpr hslot)
  exact (decide_eq_true_iff).1 hdec

private theorem len6_list420_eq_list30_mid (slot : ℕ) (hslot : slot < 6) :
    listToInfTape (c2SimRun 420 len6TruePhasedSupportInit) (c2SimOrigin slot) =
      listToInfTape (c2SimRun 30 len6PostAppendantPhasedSupportInit) (c2SimOrigin slot) := by
  have hb := len6_slot_origin_lt_bound slot hslot
  have hlen : c2SimOrigin slot < (c2SimRun 420 len6TruePhasedSupportInit).length := by
    rw [c2SimRun_length, len6TruePhasedSupportInit_length]; exact hb
  have hlen' : c2SimOrigin slot < (c2SimRun 30 len6PostAppendantPhasedSupportInit).length := by
    rw [c2SimRun_length, len6PostAppendantPhasedSupportInit_length]; exact hb
  have hget := len6Tail420OriginOk_get slot hslot
  rw [listToInfTape_lt _ hlen, listToInfTape_lt _ hlen']
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rw [← List.getD_eq_getElem (l := c2SimRun 420 len6TruePhasedSupportInit) (d := false)
      (n := c2SimOrigin slot) hlen,
    ← List.getD_eq_getElem (l := c2SimRun 30 len6PostAppendantPhasedSupportInit) (d := false)
      (n := c2SimOrigin slot) hlen']
  exact hget

private theorem len6_mid_inf30_eq_list_at_slot (slot : ℕ) (hslot : slot < 6) :
    infRule110Steps 30
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant)
        (c2SimOrigin slot) =
      listToInfTape (c2SimRun 30 len6PostAppendantPhasedSupportInit) (c2SimOrigin slot) := by
  have hle : 30 ≤ c2SimOrigin slot := by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]
    omega
  have hk : c2SimOrigin slot + 30 < c2SimBound := by
    simp [c2SimBound, c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  have hagree :
      ∀ j, c2SimOrigin slot - 30 ≤ j → j ≤ c2SimOrigin slot + 30 →
        cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant j =
          listToInfTape len6PostAppendantPhasedSupportInit j := by
    intro j _hj_lo _hj_hi
    have hj : j < c2SimBound := by
      simp [c2SimBound, c2SimOrigin, cts_tape_origin, cts_glider_spacing] at *
      omega
    exact len6Post_phased_target_eq_list_embed j hj
  have hfin := infRule110Steps_agree_Icc hle hagree
  have hrun := len6PostPhasedSupport_run_eq_inf_at 30 (c2SimOrigin slot) hle hk
  exact hfin.trans hrun.symm

/-- **Tail-origin discharge (L=6, `M₁ = 390`, `M₂ = 30`):** slot origins after 390+30 steps. -/
theorem cook_cts_tail_origin_len6_M390_M30 :
    CookCtsTailOriginHyp cook_min_len6_cts 0 cook_min_len6_true_word cook_min_len6_appendant 1 390 30 := by
  intro slot hslot
  have hslot6 : slot < 6 := by
    simp [cook_min_len6_appendant_len] at hslot
    exact hslot
  simp only [CookCtsTailOriginHyp, c2SimOrigin, cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  exact (len6_evolved_inf30_eq_list420_at_slot slot hslot6).trans <|
    (len6_list420_eq_list30_mid slot hslot6).trans (len6_mid_inf30_eq_list_at_slot slot hslot6).symm

end Rule110
