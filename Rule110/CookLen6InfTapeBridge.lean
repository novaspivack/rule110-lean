import Rule110.CookC2InfTapeBridge
import Rule110.CookLen6AppendantSim

set_option maxRecDepth 100000 in

/-!
# L=6 appendant list simulator ↔ InfTape bridge (Stage 3)

List `c2SimRun` semantics agree with `infRule110Steps` on the embedded tape at slot origin
after 390 steps (M for L=6 appendant). Init-cone phased agreement is in
`CookLen6AppendantSim`; full 390-step phased dependency match is **not** expected.
-/

namespace Rule110

@[simp] theorem len6TruePhasedSupportInit_length :
    len6TruePhasedSupportInit.length = c2SimBound := by
  simp [len6TruePhasedSupportInit, List.length_map, List.length_range]

theorem len6TruePhasedSupport_run_eq_inf_at (n k : ℕ)
    (hn_k : n ≤ k) (hk : k + n < c2SimBound) :
    listToInfTape (c2SimRun n len6TruePhasedSupportInit) k =
      infRule110Steps n (listToInfTape len6TruePhasedSupportInit) k := by
  rw [← len6TruePhasedSupportInit_length] at hk
  exact c2SimRun_eq_infRule110Steps_at len6TruePhasedSupportInit n k hn_k hk

private theorem len6TrueInitReadConeOk_get (d : ℕ) (hd : d < 61) :
    listToInfTape len6TruePhasedSupportInit (len6Slot0ConeLo + d) =
      cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word
        (len6Slot0ConeLo + d) := by
  have hall : ((List.range 61).all fun d =>
      decide (listToInfTape len6TruePhasedSupportInit (len6Slot0ConeLo + d) =
        cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word
          (len6Slot0ConeLo + d))) = true := by
    simpa [len6TrueInitReadConeOk] using len6_true_init_read_cone_ok
  have hdec := (List.all_eq_true.mp hall) d (List.mem_range.mpr hd)
  exact (decide_eq_true_iff).1 hdec

theorem len6True_init_cone_eq_phased_idx (k : ℕ)
    (hk_lo : len6Slot0ConeLo ≤ k) (hk_hi : k ≤ cts_slot_origin 0 + 30) :
    listToInfTape len6TruePhasedSupportInit k =
      cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word k := by
  have hd : ∃ d, d < 61 ∧ k = len6Slot0ConeLo + d := by
    refine ⟨k - len6Slot0ConeLo, ?_, ?_⟩
    · simp [len6Slot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hk_hi ⊢; omega
    · simp [len6Slot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hk_lo ⊢; omega
  obtain ⟨d, hd_lt, hk_eq⟩ := hd
  rw [hk_eq]
  exact len6TrueInitReadConeOk_get d hd_lt

theorem len6True_origin_run_eq_inf_390 :
    listToInfTape (c2SimRun 390 len6TruePhasedSupportInit) (cts_slot_origin 0) =
      infRule110Steps 390 (listToInfTape len6TruePhasedSupportInit) (cts_slot_origin 0) := by
  apply len6TruePhasedSupport_run_eq_inf_at 390 (cts_slot_origin 0)
  · simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  · simp [c2SimBound, cts_slot_origin, cts_tape_origin, cts_glider_spacing]

end Rule110
