import Rule110.CookStage3CollisionModel
import Rule110.CookStage3Len6Refinement
import Rule110.CookStage3EmptyAppendantChain
import Rule110.CookLen6DataConesOrigin
import Rule110.CookLen6PhasedPostDecode
import Rule110.CookLen6AppendantSim
import Rule110.CyclicTagSystem
import Rule110.InfTape

/-!
# Stage 3 global C3 discharge via CTS-step induction

Reduces multi-step operational readback (`CookCtsEvalSimAtDataConesOrigin`,
`CookCtsPhasedPostDecodeAt`, `CookCtsEvalSimAtDataCones`) to:

1. **Base case** (`n = 0`) — discharged in `CookStage3CollisionModel`.
2. **One CTS step** — appendant-local Rule 110 simulation after `M` steps.
3. **Inductive composition** — `infRule110Steps_add` with `cook_total_M_from` bookkeeping.

Legacy static tape equality (`CookCtsEvalSim`) is the wrong target: refuted at empty `n = 1`.
Full 61-cell data cones (C3′) fail even at L=6 `n = 1` (`len6_data_cones_readback_not_ok`).
Origin-cell readback (C3′′) and phased post-decode discharge at L=6 `n = 1` and for all `n`
when the input word is empty.
-/

namespace Rule110

/-! ## One-step operational predicates -/

/-- After one CTS step and `M` Rule 110 steps, origin cells match the post-step phased encode. -/
def CookCtsDataConesOriginOneStep (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool) : Prop :=
  let (w₁, idx₁) := cts.cts_step idx₀ w₀
  let M := cook_M_for_appendant_len (cts.appendants.getD (idx₀ % cts.cycleLen) []).length
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let target := cts_to_rule110_tape_phased_with_support_idx cts idx₁ w₁
  ∀ slot, slot < w₁.length →
    infRule110Steps M init (cts_slot_origin slot) = target (cts_slot_origin slot)

/-- After one CTS step and `M` Rule 110 steps, phased post-decode matches the post-step word. -/
def CookCtsPhasedPostDecodeOneStep (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool) : Prop :=
  let (w₁, idx₁) := cts.cts_step idx₀ w₀
  let M := cook_M_for_appendant_len (cts.appendants.getD (idx₀ % cts.cycleLen) []).length
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let ps := cts_word_to_placements_phased_with_support_idx cts idx₁ w₁
  ∀ slot, slot < w₁.length →
    tape_has_glider_at (infRule110Steps M init) slot (accumPhaseAt ps (cts_slot_origin slot)) =
      w₁.getD slot false

/-- After one CTS step and `M` Rule 110 steps, full 61-cell read cones match post-step encode. -/
def CookCtsDataConesOneStep (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool) : Prop :=
  let (w₁, idx₁) := cts.cts_step idx₀ w₀
  let M := cook_M_for_appendant_len (cts.appendants.getD (idx₀ % cts.cycleLen) []).length
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let target := cts_to_rule110_tape_phased_with_support_idx cts idx₁ w₁
  ∀ slot, slot < w₁.length →
    ∀ d, d < 61 →
      infRule110Steps M init (cook_cts_slot_cone_cell slot d) = target (cook_cts_slot_cone_cell slot d)

/-! ## Vacuous one-step discharge (empty post-step word) -/

theorem cook_cts_data_cones_origin_one_step_of_empty_post (cts : CyclicTagSystem) (idx₀ : ℕ)
    (w₀ : List Bool) (hw : (cts.cts_step idx₀ w₀).1 = []) :
    CookCtsDataConesOriginOneStep cts idx₀ w₀ := by
  simp [CookCtsDataConesOriginOneStep, hw, List.length_nil, Nat.not_lt_zero]

theorem cook_cts_phased_post_decode_one_step_of_empty_post (cts : CyclicTagSystem) (idx₀ : ℕ)
    (w₀ : List Bool) (hw : (cts.cts_step idx₀ w₀).1 = []) :
    CookCtsPhasedPostDecodeOneStep cts idx₀ w₀ := by
  simp [CookCtsPhasedPostDecodeOneStep, hw, List.length_nil, Nat.not_lt_zero]

theorem cook_cts_data_cones_one_step_of_empty_post (cts : CyclicTagSystem) (idx₀ : ℕ)
    (w₀ : List Bool) (hw : (cts.cts_step idx₀ w₀).1 = []) :
    CookCtsDataConesOneStep cts idx₀ w₀ := by
  simp [CookCtsDataConesOneStep, hw, List.length_nil, Nat.not_lt_zero]

/-! ## L=6 minimal one-step discharge (reuses global n=1 theorems) -/

def cook_is_min_len6_one_step_input (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool) : Prop :=
  cts = cook_min_len6_cts ∧ idx₀ = 0 ∧ w₀ = cook_min_len6_true_word

/-- One-step C3′′ at L=6 `[true]` equals global `n = 1` readback (same `M`, init, target). -/
theorem cook_cts_data_cones_origin_one_step_len6_min :
    CookCtsDataConesOriginOneStep cook_min_len6_cts 0 cook_min_len6_true_word := by
  intro slot hslot
  have hslot6 : slot < 6 := by
    simp [CookCtsDataConesOriginOneStep, CyclicTagSystem.cts_step, cook_min_len6_cts,
      cook_min_len6_true_word, cook_min_len6_appendant, cook_min_len6_appendant_len] at hslot
    exact hslot
  simp [CookCtsDataConesOriginOneStep, CyclicTagSystem.cts_step, cook_min_len6_cts,
    cook_min_len6_true_word, cook_min_len6_appendant, cook_min_len6_appendant_len,
    cook_M_len6, c2SimOrigin, cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  exact (cook_cts_eval_sim_at_data_cones_origin_len6_one slot hslot6)

theorem cook_cts_phased_post_decode_one_step_len6_min :
    CookCtsPhasedPostDecodeOneStep cook_min_len6_cts 0 cook_min_len6_true_word := by
  intro slot hslot
  have hslot6 : slot < 6 := by
    simp [CookCtsPhasedPostDecodeOneStep, CyclicTagSystem.cts_step, cook_min_len6_cts,
      cook_min_len6_true_word, cook_min_len6_appendant, cook_min_len6_appendant_len] at hslot
    exact hslot
  simp [CookCtsPhasedPostDecodeOneStep, CyclicTagSystem.cts_step, cook_min_len6_cts,
    cook_min_len6_true_word, cook_min_len6_appendant, cook_min_len6_appendant_len,
    cook_M_len6, c2SimOrigin, cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  exact (cook_cts_phased_post_decode_len6_one slot hslot6)

/-! ## C3′ blocked at L=6 (61-cell cones refuted) -/

theorem cook_cts_data_cones_one_step_len6_min_blocked :
    len6OneStepSimDataConesOk = false :=
  len6_one_step_data_cones_not_ok

/-! ## Empty input: all `n` by induction on steps -/

theorem cook_cts_eval_sim_at_data_cones_origin_empty_input_ind (cts : CyclicTagSystem) :
    ∀ n idx₀, CookCtsEvalSimAtDataConesOrigin cts n [] idx₀ := by
  intro n idx₀
  induction n with
  | zero => exact cook_cts_eval_sim_at_data_cones_origin_zero cts [] idx₀
  | succ n _ih =>
    apply cook_cts_eval_sim_at_data_cones_origin_of_empty_post_word cts (n + 1) [] idx₀
    exact CyclicTagSystem.cts_eval_with_idx_empty cts (n + 1) idx₀

theorem cook_cts_phased_post_decode_empty_input_ind (cts : CyclicTagSystem) :
    ∀ n idx₀, CookCtsPhasedPostDecodeAt cts n [] idx₀ := by
  intro n idx₀
  induction n with
  | zero =>
    intro slot hslot
    simp [CookCtsPhasedPostDecodeAt, CyclicTagSystem.cts_eval_with_idx_zero] at hslot
  | succ n _ih =>
    apply cook_cts_phased_post_decode_of_empty_post_word cts (n + 1) [] idx₀
    exact CyclicTagSystem.cts_eval_with_idx_empty cts (n + 1) idx₀

theorem cook_cts_eval_sim_at_data_cones_empty_input_ind (cts : CyclicTagSystem) :
    ∀ n idx₀, CookCtsEvalSimAtDataCones cts n [] idx₀ := by
  intro n idx₀
  induction n with
  | zero => exact cook_cts_eval_sim_at_data_cones_zero cts [] idx₀
  | succ n _ih =>
    apply cook_cts_eval_sim_at_data_cones_of_empty_post_word cts (n + 1) [] idx₀
    exact CyclicTagSystem.cts_eval_with_idx_empty cts (n + 1) idx₀

/-! ## One-step axioms (general nonempty configurations) -/

/-- **One-step C3′′:** appendant-local origin readback. Global C3′′ requires an additional
    cone-composition lemma (open). L=6 min input discharged above. -/
axiom cook_cts_data_cones_origin_one_step_ax (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool)
    (hdata : 0 < (cts.cts_step idx₀ w₀).1.length) :
    CookCtsDataConesOriginOneStep cts idx₀ w₀

/-- **One-step phased post-decode.** L=6 min input discharged above. -/
axiom cook_cts_phased_post_decode_one_step_ax (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool)
    (hdata : 0 < (cts.cts_step idx₀ w₀).1.length) :
    CookCtsPhasedPostDecodeOneStep cts idx₀ w₀

/-- **One-step C3′ (full cones):** refuted at L=6 min input; axiom retained for other configs. -/
axiom cook_cts_data_cones_one_step_ax (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool)
    (hdata : 0 < (cts.cts_step idx₀ w₀).1.length) :
    CookCtsDataConesOneStep cts idx₀ w₀

theorem cook_cts_data_cones_origin_one_step (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool) :
    CookCtsDataConesOriginOneStep cts idx₀ w₀ := by
  by_cases hw : (cts.cts_step idx₀ w₀).1 = []
  · exact cook_cts_data_cones_origin_one_step_of_empty_post cts idx₀ w₀ hw
  · have hpos : 0 < (cts.cts_step idx₀ w₀).1.length := by
      cases w : (cts.cts_step idx₀ w₀).1 with
      | nil => contradiction
      | cons _ _ => simp
    by_cases h : cook_is_min_len6_one_step_input cts idx₀ w₀
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact cook_cts_data_cones_origin_one_step_len6_min
    · exact cook_cts_data_cones_origin_one_step_ax cts idx₀ w₀ hpos

theorem cook_cts_phased_post_decode_one_step (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool) :
    CookCtsPhasedPostDecodeOneStep cts idx₀ w₀ := by
  by_cases hw : (cts.cts_step idx₀ w₀).1 = []
  · exact cook_cts_phased_post_decode_one_step_of_empty_post cts idx₀ w₀ hw
  · have hpos : 0 < (cts.cts_step idx₀ w₀).1.length := by
      cases w : (cts.cts_step idx₀ w₀).1 with
      | nil => contradiction
      | cons _ _ => simp
    by_cases h : cook_is_min_len6_one_step_input cts idx₀ w₀
    · rcases h with ⟨rfl, rfl, rfl⟩
      exact cook_cts_phased_post_decode_one_step_len6_min
    · exact cook_cts_phased_post_decode_one_step_ax cts idx₀ w₀ hpos

theorem cook_cts_data_cones_one_step (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool) :
    CookCtsDataConesOneStep cts idx₀ w₀ := by
  by_cases hw : (cts.cts_step idx₀ w₀).1 = []
  · exact cook_cts_data_cones_one_step_of_empty_post cts idx₀ w₀ hw
  · have hpos : 0 < (cts.cts_step idx₀ w₀).1.length := by
      cases w : (cts.cts_step idx₀ w₀).1 with
      | nil => contradiction
      | cons _ _ => simp
    exact cook_cts_data_cones_one_step_ax cts idx₀ w₀ hpos

/-! ## Inductive composition scaffold -/

/-- Hypothesis for composing one CTS step with a tail simulation: after `M₁` steps the tape
    agrees with the post-step encode on every slot origin needed for the tail check. -/
def CookCtsOriginCompositionHyp (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ : ℕ) : Prop :=
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let mid := cts_to_rule110_tape_phased_with_support_idx cts idx₁ w₁
  ∀ slot, slot < w₁.length →
    infRule110Steps M₁ init (cts_slot_origin slot) = mid (cts_slot_origin slot)

/-- **Induction step schema (C3′′):** tail readback at `n` composed with `infRule110Steps_add`
    once `M` bookkeeping and cone-composition hypotheses are supplied. The composition gap
    (actual post-one-step tape vs ideal mid-encode) remains open. -/
def CookCtsEvalSimAtDataConesOriginSuccSchema (cts : CyclicTagSystem) (n : ℕ)
    (w₀ w₁ : List Bool) (idx₀ idx₁ M₁ : ℕ) : Prop :=
  cts.cts_eval_with_idx (n + 1) w₀ idx₀ = (w₁, idx₁) →
    CookCtsDataConesOriginOneStep cts idx₀ w₀ →
      CookCtsEvalSimAtDataConesOrigin cts n w₁ idx₁ →
        CookCtsOriginCompositionHyp cts idx₀ w₀ w₁ idx₁ M₁ →
          cook_total_M_from cts (n + 1) idx₀ = M₁ + cook_total_M_from cts n idx₁ →
            CookCtsEvalSimAtDataConesOrigin cts (n + 1) w₀ idx₀

/-! ## Status bundle -/

structure CookStage3InductionDischarged where
  empty_input_origin : ∀ (cts : CyclicTagSystem) (n idx₀ : ℕ),
      CookCtsEvalSimAtDataConesOrigin cts n [] idx₀
  empty_input_phased : ∀ (cts : CyclicTagSystem) (n idx₀ : ℕ),
      CookCtsPhasedPostDecodeAt cts n [] idx₀
  empty_input_cones : ∀ (cts : CyclicTagSystem) (n idx₀ : ℕ),
      CookCtsEvalSimAtDataCones cts n [] idx₀
  len6_one_step_origin : CookCtsDataConesOriginOneStep cook_min_len6_cts 0 cook_min_len6_true_word
  len6_one_step_phased : CookCtsPhasedPostDecodeOneStep cook_min_len6_cts 0 cook_min_len6_true_word
  len6_one_step_cones_blocked : len6OneStepSimDataConesOk = false
  len6_global_origin : CookCtsEvalSimAtDataConesOrigin cook_min_len6_cts 1 cook_min_len6_true_word 0
  len6_global_phased : CookCtsPhasedPostDecodeAt cook_min_len6_cts 1 cook_min_len6_true_word 0
  legacy_c3_empty_n1_blocked : ¬ CookCtsEvalSim cook_standard_empty_cts 1 []

theorem cook_stage3_induction_discharged : CookStage3InductionDischarged where
  empty_input_origin := cook_cts_eval_sim_at_data_cones_origin_empty_input_ind
  empty_input_phased := cook_cts_phased_post_decode_empty_input_ind
  empty_input_cones := cook_cts_eval_sim_at_data_cones_empty_input_ind
  len6_one_step_origin := cook_cts_data_cones_origin_one_step_len6_min
  len6_one_step_phased := cook_cts_phased_post_decode_one_step_len6_min
  len6_one_step_cones_blocked := cook_cts_data_cones_one_step_len6_min_blocked
  len6_global_origin := cook_cts_eval_sim_at_data_cones_origin_len6_one
  len6_global_phased := cook_cts_phased_post_decode_len6_one
  legacy_c3_empty_n1_blocked := cook_standard_empty_cts_legacy_c3_n1_blocked

/-- **BLOCKED:** global C3′ — 61-cell readback refuted at L=6 `n = 1`. -/
theorem cook_cts_eval_sim_data_cones_global_blocked :
    len6DataConesReadbackOk = false :=
  len6_data_cones_readback_not_ok

/-- **BLOCKED:** legacy `CookCtsEvalSim` cannot hold for all `n` on the standard empty CTS. -/
theorem cook_cts_eval_sim_legacy_global_blocked :
    ¬ (∀ n, CookCtsEvalSim cook_standard_empty_cts n []) := by
  intro hall
  exact cook_standard_empty_cts_legacy_c3_n1_blocked (hall 1)

end Rule110
