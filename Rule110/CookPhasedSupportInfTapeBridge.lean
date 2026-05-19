import Rule110.CookC2InfTapeBridge
import Rule110.CookEmptyAppendantSim

set_option maxRecDepth 100000 in

/-!
# Phased-with-support list simulator ↔ InfTape bridge (Stage 3)

Connects bounded `c2SimRun` on `emptyPhasedSupportInit` to `infRule110Steps` on the
embedded `InfTape`. Init-cone agreement with `cts_to_rule110_tape_phased_with_support`
is certified in `CookEmptyAppendantSim`; this module proves **step semantics** agree
on the slot-0 read cone (even though the cone is not a fixed point after 30 steps).
-/

namespace Rule110

@[simp] theorem emptyPhasedSupportInit_length :
    emptyPhasedSupportInit.length = c2SimBound := by
  simp [emptyPhasedSupportInit, List.length_map, List.length_range]

theorem emptyPhasedSupport_run_eq_inf_at (n k : ℕ)
    (hn_k : n ≤ k) (hk : k + n < c2SimBound) :
    listToInfTape (c2SimRun n emptyPhasedSupportInit) k =
      infRule110Steps n (listToInfTape emptyPhasedSupportInit) k := by
  rw [← emptyPhasedSupportInit_length] at hk
  exact c2SimRun_eq_infRule110Steps_at emptyPhasedSupportInit n k hn_k hk

theorem emptyPhasedSupportInitReadConeOk_get (d : ℕ) (hd : d < 61) :
    listToInfTape emptyPhasedSupportInit (emptySlot0ConeLo + d) =
      cts_to_rule110_tape_phased_with_support (CyclicTagSystem.mk []) []
        (emptySlot0ConeLo + d) := by
  have hall : ((List.range 61).all fun d =>
      decide (listToInfTape emptyPhasedSupportInit (emptySlot0ConeLo + d) =
        cts_to_rule110_tape_phased_with_support (CyclicTagSystem.mk []) []
          (emptySlot0ConeLo + d))) = true := by
    simpa [emptyPhasedSupportInitReadConeOk] using empty_phased_support_init_read_cone_ok
  have hdec := (List.all_eq_true.mp hall) d (List.mem_range.mpr hd)
  exact (decide_eq_true_iff).1 hdec

theorem emptyPhasedSupport_init_cone_eq_phased (k : ℕ)
    (hk_lo : emptySlot0ConeLo ≤ k) (hk_hi : k ≤ emptySlot0ConeHi) :
    listToInfTape emptyPhasedSupportInit k =
      cts_to_rule110_tape_phased_with_support (CyclicTagSystem.mk []) [] k := by
  have hd : ∃ d, d < 61 ∧ k = emptySlot0ConeLo + d := by
    refine ⟨k - emptySlot0ConeLo, ?_, ?_⟩
    · simp [emptySlot0ConeLo, emptySlot0ConeHi, cts_slot_origin, cts_tape_origin,
        cts_glider_spacing] at hk_hi ⊢; omega
    · simp [emptySlot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hk_lo ⊢; omega
  obtain ⟨d, hd_lt, hk_eq⟩ := hd
  rw [hk_eq]
  exact emptyPhasedSupportInitReadConeOk_get d hd_lt

theorem emptyPhasedSupport_phased_init_eq_list_on_slot0_cone (k : ℕ)
    (hk_lo : emptySlot0ConeLo ≤ k) (hk_hi : k ≤ emptySlot0ConeHi) :
    cts_to_rule110_tape_phased_with_support (CyclicTagSystem.mk []) [] k =
      listToInfTape emptyPhasedSupportInit k :=
  (emptyPhasedSupport_init_cone_eq_phased k hk_lo hk_hi).symm

theorem emptyPhasedSupport_slot0_cone_run_eq_inf_30 (k : ℕ)
    (hk_lo : emptySlot0ConeLo ≤ k) (hk_hi : k ≤ emptySlot0ConeHi) :
    listToInfTape (c2SimRun 30 emptyPhasedSupportInit) k =
      infRule110Steps 30 (listToInfTape emptyPhasedSupportInit) k := by
  apply emptyPhasedSupport_run_eq_inf_at 30 k
  · simp [emptySlot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hk_lo ⊢; omega
  · simp [c2SimBound, emptySlot0ConeHi, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hk_hi ⊢
    omega

/-- At slot origin, phased init agrees with list embed on the full 30-step dependency window. -/
theorem emptyPhasedSupport_origin_inf_steps_agree :
    infRule110Steps 30 (cts_to_rule110_tape_phased_with_support (CyclicTagSystem.mk []) [])
        (cts_slot_origin 0) =
      infRule110Steps 30 (listToInfTape emptyPhasedSupportInit) (cts_slot_origin 0) := by
  have hk_le : 30 ≤ cts_slot_origin 0 := by
    simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  have hagree :
      ∀ j, cts_slot_origin 0 - 30 ≤ j → j ≤ cts_slot_origin 0 + 30 →
        cts_to_rule110_tape_phased_with_support (CyclicTagSystem.mk []) [] j =
          listToInfTape emptyPhasedSupportInit j := by
    intro j hj_lo hj_hi
    exact emptyPhasedSupport_phased_init_eq_list_on_slot0_cone j
      (by simp [emptySlot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hj_lo ⊢; omega)
      (by simp [emptySlot0ConeHi, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hj_hi ⊢; omega)
  exact infRule110Steps_agree_Icc hk_le hagree

theorem emptyPhasedSupport_origin_run_eq_inf_30 :
    listToInfTape (c2SimRun 30 emptyPhasedSupportInit) (cts_slot_origin 0) =
      infRule110Steps 30 (listToInfTape emptyPhasedSupportInit) (cts_slot_origin 0) :=
  emptyPhasedSupport_slot0_cone_run_eq_inf_30 (cts_slot_origin 0)
    (by simp [emptySlot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing])
    (by simp [emptySlot0ConeHi, cts_slot_origin, cts_tape_origin, cts_glider_spacing])

end Rule110
