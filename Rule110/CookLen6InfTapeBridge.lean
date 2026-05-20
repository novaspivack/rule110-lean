import Rule110.CookC2InfTapeBridge
import Rule110.CookLen6AppendantSim
import Rule110.CookLen6Evolved390Literal

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

theorem len6TrueInitReadConeOk_get (d : ℕ) (hd : d < 61) :
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

theorem len6True_phased_init_eq_list_on_slot0_cone (k : ℕ)
    (hk_lo : len6Slot0ConeLo ≤ k) (hk_hi : k ≤ cts_slot_origin 0 + 30) :
    cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word k =
      listToInfTape len6TruePhasedSupportInit k :=
  (len6True_init_cone_eq_phased_idx k hk_lo hk_hi).symm

theorem len6True_slot0_cone_run_eq_inf_30 (k : ℕ)
    (hk_lo : len6Slot0ConeLo ≤ k) (hk_hi : k ≤ cts_slot_origin 0 + 30) :
    listToInfTape (c2SimRun 30 len6TruePhasedSupportInit) k =
      infRule110Steps 30 (listToInfTape len6TruePhasedSupportInit) k := by
  apply len6TruePhasedSupport_run_eq_inf_at 30 k
  · simp [len6Slot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hk_lo ⊢; omega
  · simp [c2SimBound, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hk_hi ⊢; omega

theorem len6_slot0_origin_inf_steps_agree_init_30 :
    infRule110Steps 30
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word)
        (cts_slot_origin 0) =
      infRule110Steps 30 (listToInfTape len6TruePhasedSupportInit) (cts_slot_origin 0) := by
  have hk_le : 30 ≤ cts_slot_origin 0 := by
    simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  have hagree :
      ∀ j, cts_slot_origin 0 - 30 ≤ j → j ≤ cts_slot_origin 0 + 30 →
        cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word j =
          listToInfTape len6TruePhasedSupportInit j := by
    intro j hj_lo hj_hi
    exact len6True_phased_init_eq_list_on_slot0_cone j
      (by simp [len6Slot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hj_lo ⊢; omega)
      (by simp [len6Slot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hj_hi ⊢; omega)
  exact infRule110Steps_agree_Icc hk_le hagree

theorem len6True_origin_run_eq_inf_30 :
    listToInfTape (c2SimRun 30 len6TruePhasedSupportInit) (cts_slot_origin 0) =
      infRule110Steps 30 (listToInfTape len6TruePhasedSupportInit) (cts_slot_origin 0) :=
  len6True_slot0_cone_run_eq_inf_30 (cts_slot_origin 0)
    (by simp [len6Slot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing])
    (by simp [len6Slot0ConeLo, cts_slot_origin, cts_tape_origin, cts_glider_spacing])

theorem len6True_origin_run_eq_inf_390 :
    listToInfTape (c2SimRun 390 len6TruePhasedSupportInit) (cts_slot_origin 0) =
      infRule110Steps 390 (listToInfTape len6TruePhasedSupportInit) (cts_slot_origin 0) := by
  apply len6TruePhasedSupport_run_eq_inf_at 390 (cts_slot_origin 0)
  · simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  · simp [c2SimBound, cts_slot_origin, cts_tape_origin, cts_glider_spacing]

theorem len6True_phased_init_eq_list_embed (k : ℕ) (hk : k < c2SimBound) :
    cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word k =
      listToInfTape len6TruePhasedSupportInit k := by
  rw [listToInfTape_lt len6TruePhasedSupportInit (by rw [len6TruePhasedSupportInit_length]; exact hk)]
  unfold len6TruePhasedSupportInit cts_to_rule110_tape_phased_with_support_idx
  simp [List.getElem_map, List.getElem_range]

@[simp] theorem len6PostAppendantPhasedSupportInit_length :
    len6PostAppendantPhasedSupportInit.length = c2SimBound := by
  simp [len6PostAppendantPhasedSupportInit, List.length_map, List.length_range]

theorem len6PostPhasedSupport_run_eq_inf_at (n k : ℕ)
    (hn_k : n ≤ k) (hk : k + n < c2SimBound) :
    listToInfTape (c2SimRun n len6PostAppendantPhasedSupportInit) k =
      infRule110Steps n (listToInfTape len6PostAppendantPhasedSupportInit) k := by
  rw [← len6PostAppendantPhasedSupportInit_length] at hk
  exact c2SimRun_eq_infRule110Steps_at len6PostAppendantPhasedSupportInit n k hn_k hk

theorem len6Post_phased_target_eq_list_embed (k : ℕ) (hk : k < c2SimBound) :
    cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant k =
      listToInfTape len6PostAppendantPhasedSupportInit k := by
  rw [listToInfTape_lt len6PostAppendantPhasedSupportInit
    (by rw [len6PostAppendantPhasedSupportInit_length]; exact hk)]
  unfold len6PostAppendantPhasedSupportInit cts_to_rule110_tape_phased_with_support_idx
  simp [List.getElem_map, List.getElem_range]

theorem len6True_phased_init_eq_list_on_origin_window (slot : ℕ) (hslot : slot < 6) (j : ℕ)
    (hj_lo : c2SimOrigin slot - 390 ≤ j) (hj_hi : j ≤ c2SimOrigin slot + 390) :
    cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word j =
      listToInfTape len6TruePhasedSupportInit j :=
  len6True_phased_init_eq_list_embed j (by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing, c2SimBound] at hj_lo hj_hi ⊢; omega)

theorem len6True_run_eq_inf_390_at_slot (slot : ℕ) (_hslot : slot < 6) :
    listToInfTape (c2SimRun 390 len6TruePhasedSupportInit) (c2SimOrigin slot) =
      infRule110Steps 390 (listToInfTape len6TruePhasedSupportInit) (c2SimOrigin slot) := by
  apply len6TruePhasedSupport_run_eq_inf_at 390 (c2SimOrigin slot)
  · simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  · simp [c2SimBound, c2SimOrigin, cts_tape_origin, cts_glider_spacing, len6TruePhasedSupportInit_length]
    omega

theorem len6_origin_inf_steps_agree_init (slot : ℕ) (hslot : slot < 6) :
    infRule110Steps 390
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word)
        (c2SimOrigin slot) =
      infRule110Steps 390 (listToInfTape len6TruePhasedSupportInit) (c2SimOrigin slot) := by
  apply infRule110Steps_agree_Icc
  · simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  · intro j hj_lo hj_hi
    exact len6True_phased_init_eq_list_on_origin_window slot hslot j hj_lo hj_hi

theorem len6_origin_inf_eq_list_fin (slot : ℕ) (hslot : slot < 6) :
    infRule110Steps 390
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word)
        (c2SimOrigin slot) =
      listToInfTape (c2SimRun 390 len6TruePhasedSupportInit) (c2SimOrigin slot) :=
  (len6_origin_inf_steps_agree_init slot hslot).trans (len6True_run_eq_inf_390_at_slot slot hslot).symm

private theorem len6Evolved390_inf_eq_at (k : ℕ) (hk390 : 390 ≤ k) (hk : k + 390 < c2SimBound) :
    infRule110Steps 390 (listToInfTape len6TruePhasedSupportInit) k =
      listToInfTape len6Evolved390 k := by
  have h := len6TruePhasedSupport_run_eq_inf_at 390 k hk390 hk
  have heq : c2SimRun 390 len6TruePhasedSupportInit = len6Evolved390 := len6Evolved390_correct.symm
  calc infRule110Steps 390 (listToInfTape len6TruePhasedSupportInit) k
      = listToInfTape (c2SimRun 390 len6TruePhasedSupportInit) k := h.symm
    _ = listToInfTape len6Evolved390 k := by rw [heq]

private theorem len6_inf390_phased_eq_evolved_at (slot : ℕ) (hslot : slot < 6) (j : ℕ)
    (hj_lo : c2SimOrigin slot - 30 ≤ j) (hj_hi : j ≤ c2SimOrigin slot + 30) :
    infRule110Steps 390
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word) j =
      listToInfTape len6Evolved390 j := by
  have hj390 : 390 ≤ j := by simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing] at hj_lo ⊢; omega
  have hj_hi' : j + 390 < c2SimBound := by
    simp [c2SimBound, c2SimOrigin, cts_tape_origin, cts_glider_spacing] at hj_hi ⊢; omega
  have hagree : ∀ k, j - 390 ≤ k → k ≤ j + 390 →
      cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word k =
        listToInfTape len6TruePhasedSupportInit k := by
    intro k hk_lo hk_hi
    exact len6True_phased_init_eq_list_embed k (by
      simp [c2SimBound, c2SimOrigin, cts_tape_origin, cts_glider_spacing] at hj_hi ⊢; omega)
  exact (infRule110Steps_agree_Icc hj390 (fun k hk_lo hk_hi => (hagree k hk_lo hk_hi).symm)).symm.trans
    (len6Evolved390_inf_eq_at j hj390 hj_hi')

/-- Chunked `390 + 30` InfTape steps at slot origins agree with `420` list simulation.

List compose `c2SimRun 420 = c2SimRun 30 ∘ c2SimRun 390` at slot origins is discharged by
`native_decide` in `CookLen6TailEvolution`. The `n = 390` InfTape transport is proved via
`len6Evolved390` (the hard-coded literal `c2SimRun 390 len6TruePhasedSupportInit`), whose
equality to the run is proved by `native_decide` in `CookLen6Evolved390Literal`. -/
theorem len6_evolved_inf30_eq_list420_at_slot (slot : ℕ) (hslot : slot < 6) :
    infRule110Steps 30
        (infRule110Steps 390
          (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word))
        (c2SimOrigin slot) =
      listToInfTape (c2SimRun 420 len6TruePhasedSupportInit) (c2SimOrigin slot) := by
  have hb : c2SimOrigin slot < c2SimBound := by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing, c2SimBound]; omega
  have hle30 : 30 ≤ c2SimOrigin slot := by simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  have hk30 : c2SimOrigin slot + 30 < len6Evolved390.length := by
    simp [len6Evolved390_length, c2SimBound, c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  have h390_window : ∀ j, c2SimOrigin slot - 30 ≤ j → j ≤ c2SimOrigin slot + 30 →
      infRule110Steps 390
          (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word) j =
        listToInfTape len6Evolved390 j := by
    intro j hj_lo hj_hi
    exact len6_inf390_phased_eq_evolved_at slot hslot j hj_lo hj_hi
  have hinfl30 := infRule110Steps_agree_Icc hle30 h390_window
  have hrun30 := c2SimRun_eq_infRule110Steps_at len6Evolved390 30 (c2SimOrigin slot) hle30 hk30
  have hlen420 : c2SimOrigin slot < (c2SimRun 420 len6TruePhasedSupportInit).length := by
    simpa [c2SimRun_length, len6TruePhasedSupportInit_length] using hb
  have hlen30e : c2SimOrigin slot < (c2SimRun 30 len6Evolved390).length := by
    simpa [c2SimRun_length, len6Evolved390_length, c2SimBound, c2SimOrigin,
      cts_tape_origin, cts_glider_spacing] using hb
  have hcompose420 : listToInfTape (c2SimRun 30 len6Evolved390) (c2SimOrigin slot) =
      listToInfTape (c2SimRun 420 len6TruePhasedSupportInit) (c2SimOrigin slot) := by
    rw [listToInfTape_lt _ hlen30e, listToInfTape_lt _ hlen420]
    rw [List.get_eq_getElem, List.get_eq_getElem]
    rw [← List.getD_eq_getElem (l := c2SimRun 30 len6Evolved390) (d := false)
          (n := c2SimOrigin slot) hlen30e,
        ← List.getD_eq_getElem (l := c2SimRun 420 len6TruePhasedSupportInit) (d := false)
          (n := c2SimOrigin slot) hlen420]
    have hall : ((List.range 6).all fun s =>
        decide ((c2SimRun 420 len6TruePhasedSupportInit).getD (c2SimOrigin s) false =
          (c2SimRun 30 len6Evolved390).getD (c2SimOrigin s) false)) = true := by
      native_decide
    have hdec := (List.all_eq_true.mp hall) slot (List.mem_range.mpr hslot)
    exact ((decide_eq_true_iff).1 hdec).symm
  calc
    infRule110Steps 30 (infRule110Steps 390
        (cts_to_rule110_tape_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_true_word))
        (c2SimOrigin slot)
        = infRule110Steps 30 (listToInfTape len6Evolved390) (c2SimOrigin slot) := hinfl30
    _ = listToInfTape (c2SimRun 30 len6Evolved390) (c2SimOrigin slot) := hrun30.symm
    _ = listToInfTape (c2SimRun 420 len6TruePhasedSupportInit) (c2SimOrigin slot) := hcompose420

end Rule110
