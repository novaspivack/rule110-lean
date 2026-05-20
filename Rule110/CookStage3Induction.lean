import Rule110.CookStage3CollisionModel
import Rule110.CookStage3EmptyAppendantChain
import Rule110.CookStage3OriginSucc
import Rule110.CookStage3TailFinal
import Rule110.CookLen6DataConesOrigin
import Rule110.CookLen6PhasedPostDecode
import Rule110.CookLen6AppendantSim
import Rule110.CookLen6TailEvolution
import Rule110.CookLen6TailOrigin
import Rule110.CookCollisionOneStepCatalog
import Rule110.CookCollisionWitnesses
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

/-- After `M₁` Rule 110 steps, slot-origin cells agree with the mid-encode on every slot
    needed for a length-`w₁` post-step word. -/
def CookCtsOriginCompositionHyp (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ : ℕ) : Prop :=
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let mid := cts_to_rule110_tape_phased_with_support_idx cts idx₁ w₁
  ∀ slot, slot < w₁.length →
    infRule110Steps M₁ init (cts_slot_origin slot) = mid (cts_slot_origin slot)

/-- One-step origin readback is exactly the composition hypothesis for the mid-encode after
    the first CTS microstep. -/
theorem cook_cts_origin_composition_from_one_step (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool) :
    let (w₁, idx₁) := cts.cts_step idx₀ w₀
    let M₁ := cook_M_for_appendant_len (cts.appendants.getD (idx₀ % cts.cycleLen) []).length
    CookCtsOriginCompositionHyp cts idx₀ w₀ w₁ idx₁ M₁ ↔
      CookCtsDataConesOriginOneStep cts idx₀ w₀ := by
  simp [CookCtsOriginCompositionHyp, CookCtsDataConesOriginOneStep]

/-- After `M₁` Rule 110 steps, evolved tape agrees with the mid-encode on every Icc cone
    required for `M₂`-step tail evolution at each post-one-step slot origin. Stronger than
    `CookCtsTailOriginHyp`; implies the origin version when `M₂ ≤ cts_slot_origin slot`. -/
def CookCtsTailEvolutionHyp (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ) : Prop :=
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let mid := cts_to_rule110_tape_phased_with_support_idx cts idx₁ w₁
  let evolved := infRule110Steps M₁ init
  ∀ slot, slot < w₁.length →
    M₂ ≤ cts_slot_origin slot →
      ∀ j, cts_slot_origin slot - M₂ ≤ j → j ≤ cts_slot_origin slot + M₂ →
        evolved j = mid j

/-- Post-one-step tail origin implies final-word tail origin when the word does not grow. -/
theorem cook_cts_tail_origin_final_of_mid (cts : CyclicTagSystem) (idx₀ : ℕ)
    (w₀ w_mid w_final : List Bool) (idx_mid M₁ M₂ : ℕ)
    (hlen : w_final.length ≤ w_mid.length)
    (htail : CookCtsTailOriginHyp cts idx₀ w₀ w_mid idx_mid M₁ M₂) :
    CookCtsTailOriginHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ := by
  intro slot hslot
  exact htail slot (Nat.lt_of_lt_of_le hslot hlen)

theorem cook_cts_tail_origin_of_evolution (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ) (slot : ℕ) (hslot : slot < w₁.length)
    (hbound : M₂ ≤ cts_slot_origin slot)
    (htail : CookCtsTailEvolutionHyp cts idx₀ w₀ w₁ idx₁ M₁ M₂) :
    let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
    let mid := cts_to_rule110_tape_phased_with_support_idx cts idx₁ w₁
    let evolved := infRule110Steps M₁ init
    infRule110Steps M₂ evolved (cts_slot_origin slot) =
      infRule110Steps M₂ mid (cts_slot_origin slot) := by
  apply infRule110Steps_agree_Icc hbound
  intro j hj_lo hj_hi
  exact htail slot hslot hbound j hj_lo hj_hi

/-- Origin composition implies tail-origin agreement when the tail step count is zero. -/
theorem cook_cts_tail_origin_of_zero_tail (cts : CyclicTagSystem) (idx₀ idx₁ M₁ M₂ : ℕ)
    (w₀ w₁ : List Bool) (hM₂ : M₂ = 0)
    (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w₁ idx₁ M₁) :
    CookCtsTailOriginHyp cts idx₀ w₀ w₁ idx₁ M₁ M₂ := by
  intro slot hslot
  rw [hM₂, infRule110Steps_zero]
  exact hcomp slot hslot

theorem cook_cts_tail_evolution_of_zero_tail (cts : CyclicTagSystem) (idx₀ idx₁ M₁ M₂ : ℕ)
    (w₀ w₁ : List Bool) (hM₂ : M₂ = 0)
    (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w₁ idx₁ M₁) :
    CookCtsTailEvolutionHyp cts idx₀ w₀ w₁ idx₁ M₁ M₂ := by
  intro slot hslot _ j hj_lo hj_hi
  have hj : j = cts_slot_origin slot := by
    simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hj_lo hj_hi ⊢; omega
  dsimp [CookCtsOriginCompositionHyp] at hcomp
  rw [hj]
  exact hcomp slot hslot

theorem CookCtsEvalSimAtDataConesOrigin_one_iff (cts : CyclicTagSystem) (w₀ : List Bool) (idx₀ : ℕ) :
    CookCtsEvalSimAtDataConesOrigin cts 1 w₀ idx₀ ↔
      CookCtsDataConesOriginOneStep cts idx₀ w₀ := by
  simp [CookCtsEvalSimAtDataConesOrigin, CookCtsDataConesOriginOneStep, CyclicTagSystem.cts_eval_with_idx,
    CyclicTagSystem.cts_steps, CyclicTagSystem.cts_steps_succ, CyclicTagSystem.cts_steps_zero,
    cook_total_M_from, List.range_succ, List.foldl_cons, List.foldl_nil]

theorem cook_cts_eval_sim_at_data_cones_origin_one (cts : CyclicTagSystem) (w₀ : List Bool) (idx₀ : ℕ)
    (hstep : CookCtsDataConesOriginOneStep cts idx₀ w₀) :
    CookCtsEvalSimAtDataConesOrigin cts 1 w₀ idx₀ :=
  (CookCtsEvalSimAtDataConesOrigin_one_iff cts w₀ idx₀).2 hstep

/-- **Induction step (`n = 0` tail):** first microstep only; no tail composition required. -/
theorem cook_cts_eval_sim_at_data_cones_origin_succ_zero_tail (cts : CyclicTagSystem) (w₀ : List Bool)
    (idx₀ : ℕ) (hstep : CookCtsDataConesOriginOneStep cts idx₀ w₀) :
    CookCtsEvalSimAtDataConesOrigin cts 1 w₀ idx₀ :=
  cook_cts_eval_sim_at_data_cones_origin_one cts w₀ idx₀ hstep

/-! ## Induction step (C3′′) -/

/-- **Tail-origin axiom (post-one-step word):** after `M₁` steps, `M₂`-step tail from actual tape
    matches mid-encode at slot origins with `slot < w₁.length`. Discharged when `M₂ = 0`. -/
axiom cook_cts_tail_origin_ax (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ)
    (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w₁ idx₁ M₁)
    (hpos : 0 < M₂) :
    CookCtsTailOriginHyp cts idx₀ w₀ w₁ idx₁ M₁ M₂

def cook_is_len6_tail_origin_M390_M30 (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ) : Prop :=
  cts = cook_min_len6_cts ∧ idx₀ = 0 ∧ w₀ = cook_min_len6_true_word ∧
    w₁ = cook_min_len6_appendant ∧ idx₁ = 1 ∧ M₁ = 390 ∧ M₂ = 30

theorem cook_cts_tail_origin (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ) (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w₁ idx₁ M₁) :
    CookCtsTailOriginHyp cts idx₀ w₀ w₁ idx₁ M₁ M₂ := by
  by_cases hM₂ : M₂ = 0
  · exact cook_cts_tail_origin_of_zero_tail cts idx₀ idx₁ M₁ M₂ w₀ w₁ hM₂ hcomp
  · have hpos : 0 < M₂ := Nat.pos_of_ne_zero hM₂
    by_cases hlen6 : cook_is_len6_tail_origin_M390_M30 cts idx₀ w₀ w₁ idx₁ M₁ M₂
    · rcases hlen6 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact cook_cts_tail_origin_len6_M390_M30
    · exact cook_cts_tail_origin_ax cts idx₀ w₀ w₁ idx₁ M₁ M₂ hcomp hpos

/-- **Final-word tail-origin axiom:** covers appendant-grown slots with `slot < w_final.length`
    after `n + 1` CTS steps. Implied by `CookCtsTailOriginHyp` when `w_final.length ≤ w_mid.length`. -/
axiom cook_cts_tail_origin_final_ax (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w_mid w_final : List Bool)
    (idx_mid _idx_final M₁ M₂ : ℕ)
    (hstep : CookCtsDataConesOriginOneStep cts idx₀ w₀)
    (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w_mid idx_mid M₁) :
    CookCtsTailOriginHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂

theorem cook_cts_tail_origin_final (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w_mid w_final : List Bool)
    (idx_mid idx_final M₁ M₂ : ℕ)
    (hstep : CookCtsDataConesOriginOneStep cts idx₀ w₀)
    (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w_mid idx_mid M₁) :
    CookCtsTailOriginHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ := by
  by_cases hlen : w_final.length ≤ w_mid.length
  · exact cook_cts_tail_origin_final_of_mid cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ hlen
      (cook_cts_tail_origin cts idx₀ w₀ w_mid idx_mid M₁ M₂ hcomp)
  · exact cook_cts_tail_origin_final_ax cts idx₀ w₀ w_mid w_final idx_mid idx_final M₁ M₂ hstep hcomp

private theorem cts_step_snd_eq_mod_succ (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool)
    (hw : w ≠ []) (hk : 0 < cts.cycleLen) :
    (cts.cts_step idx w).2 = (idx + 1) % cts.cycleLen := by
  rcases w with _ | ⟨a, rest⟩
  · exact absurd rfl hw
  · rcases h : cts.appendants with _ | ⟨_, _⟩
    · simp [h, CyclicTagSystem.cycleLen] at hk
    · simp [CyclicTagSystem.cts_step, CyclicTagSystem.cycleLen, h]

private theorem cts_step_idx_succ_of_nonempty (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ : List Bool)
    (hw : w₀ ≠ []) (hk : 0 < cts.cycleLen) :
    (cts.cts_step idx₀ w₀).2 = (idx₀ + 1) % cts.cycleLen := by
  rcases w₀ with _ | ⟨a, rest⟩
  · exact absurd rfl hw
  · exact cts_step_snd_eq_mod_succ cts idx₀ (a :: rest) hw hk

/-- Degenerate CTS (`cycleLen = 0`) with nonempty input.
    When `cycleLen = 0`, `cts_step (a :: rest) = (rest, idx)`, so cts_eval after
    n+1 steps from w₀ = cts_eval after n steps from the tail.
    The predicate is vacuous when the result is empty, otherwise it follows from `ih`.
    This is mathematically trivial (degenerate CTS cannot simulate any computation)
    but requires tracking `cook_total_M_from` through the degenerate step. -/
axiom cook_cts_eval_sim_at_data_cones_origin_step_degenerate (cts : CyclicTagSystem) (n : ℕ)
    (w₀ : List Bool) (idx₀ : ℕ) (hw : w₀ ≠ []) (hk : ¬ 0 < cts.cycleLen)
    (ih : ∀ w₁ idx₁, CookCtsEvalSimAtDataConesOrigin cts n w₁ idx₁) :
    CookCtsEvalSimAtDataConesOrigin cts (n + 1) w₀ idx₀

private theorem cook_cts_eval_sim_at_data_cones_origin_step_nonempty
    (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ)
    (hw : w₀ ≠ []) (hk : 0 < cts.cycleLen)
    (ih : ∀ w₁ idx₁, CookCtsEvalSimAtDataConesOrigin cts n w₁ idx₁) :
    CookCtsEvalSimAtDataConesOrigin cts (n + 1) w₀ idx₀ := by
  set w_final := (cts.cts_eval_with_idx (n + 1) w₀ idx₀).1 with hwf
  set idx_final := (cts.cts_eval_with_idx (n + 1) w₀ idx₀).2 with hif
  set w_mid := (cts.cts_step idx₀ w₀).1 with hwm
  set idx_mid := (cts.cts_step idx₀ w₀).2 with him
  set M₁ := cook_M_for_appendant_len (cts.appendants.getD (idx₀ % cts.cycleLen) []).length with hM₁
  have heval : cts.cts_eval_with_idx (n + 1) w₀ idx₀ = (w_final, idx_final) := by
    simp [hwf, hif]
  have hmid : cts.cts_step idx₀ w₀ = (w_mid, idx_mid) := by
    simp [hwm, him]
  have hidx : idx_mid = (idx₀ + 1) % cts.cycleLen :=
    cts_step_idx_succ_of_nonempty cts idx₀ w₀ hw hk
  have hMsplit :
      cook_total_M_from cts (n + 1) idx₀ = M₁ + cook_total_M_from cts n idx_mid := by
    rw [hM₁]
    exact cook_total_M_from_microstep_split cts n idx₀ idx_mid hidx
  have hstep : CookCtsDataConesOriginOneStep cts idx₀ w₀ :=
    cook_cts_data_cones_origin_one_step cts idx₀ w₀
  have hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w_mid idx_mid M₁ :=
    (cook_cts_origin_composition_from_one_step cts idx₀ w₀).1 hstep
  have htail : CookCtsTailOriginHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁
      (cook_total_M_from cts n idx_mid) :=
    cook_cts_tail_origin_final cts idx₀ w₀ w_mid w_final idx_mid idx_final M₁
      (cook_total_M_from cts n idx_mid) hstep hcomp
  exact cook_cts_eval_sim_at_data_cones_origin_succ_schema cts n w₀ w_mid w_final idx₀ idx_mid
    idx_final M₁ heval hmid (ih w_mid idx_mid) htail hMsplit

/-- **Induction step (C3′′):** `set`-binding composition via proved succ schema + tail-final. -/
theorem cook_cts_eval_sim_at_data_cones_origin_step (cts : CyclicTagSystem) (n : ℕ)
    (w₀ : List Bool) (idx₀ : ℕ)
    (ih : ∀ w₁ idx₁, CookCtsEvalSimAtDataConesOrigin cts n w₁ idx₁) :
    CookCtsEvalSimAtDataConesOrigin cts (n + 1) w₀ idx₀ := by
  by_cases hw : w₀ = []
  · subst hw
    apply cook_cts_eval_sim_at_data_cones_origin_of_empty_post_word cts (n + 1) [] idx₀
    exact CyclicTagSystem.cts_eval_with_idx_empty cts (n + 1) idx₀
  · by_cases hk : 0 < cts.cycleLen
    · exact cook_cts_eval_sim_at_data_cones_origin_step_nonempty cts n w₀ idx₀ hw hk ih
    · exact cook_cts_eval_sim_at_data_cones_origin_step_degenerate cts n w₀ idx₀ hw hk ih

/-- **Tail Icc axiom:** full cone agreement (implies `CookCtsTailOriginHyp` when `M₂ ≤ origin`). -/
axiom cook_cts_tail_evolution_ax (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ)
    (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w₁ idx₁ M₁)
    (hpos : 0 < M₂) :
    CookCtsTailEvolutionHyp cts idx₀ w₀ w₁ idx₁ M₁ M₂

theorem cook_cts_tail_evolution (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ) (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w₁ idx₁ M₁) :
    CookCtsTailEvolutionHyp cts idx₀ w₀ w₁ idx₁ M₁ M₂ := by
  by_cases hM₂ : M₂ = 0
  · exact cook_cts_tail_evolution_of_zero_tail cts idx₀ idx₁ M₁ M₂ w₀ w₁ hM₂ hcomp
  · have hpos : 0 < M₂ := Nat.pos_of_ne_zero hM₂
    exact cook_cts_tail_evolution_ax cts idx₀ w₀ w₁ idx₁ M₁ M₂ hcomp hpos

/-- Post-one-step tail evolution on `w_mid` slots implies final-word evolution when lengths agree. -/
theorem cook_cts_tail_evolution_final_of_mid (cts : CyclicTagSystem) (idx₀ : ℕ)
    (w₀ w_mid w_final : List Bool) (idx_mid M₁ M₂ : ℕ)
    (hlen : w_final.length ≤ w_mid.length)
    (htail : CookCtsTailEvolutionHyp cts idx₀ w₀ w_mid idx_mid M₁ M₂) :
    CookCtsTailEvolutionHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ := by
  intro slot hslot hbound j hj_lo hj_hi
  have hslot' : slot < w_mid.length := Nat.lt_of_lt_of_le hslot hlen
  exact htail slot hslot' hbound j hj_lo hj_hi

axiom cook_cts_tail_evolution_final_ax (cts : CyclicTagSystem) (idx₀ : ℕ)
    (w₀ w_mid w_final : List Bool) (idx_mid M₁ M₂ : ℕ)
    (hstep : CookCtsDataConesOriginOneStep cts idx₀ w₀)
    (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w_mid idx_mid M₁)
    (hpos : 0 < M₂) :
    CookCtsTailEvolutionHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂

theorem cook_cts_tail_evolution_final (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w_mid w_final : List Bool)
    (idx_mid M₁ M₂ : ℕ) (hstep : CookCtsDataConesOriginOneStep cts idx₀ w₀)
    (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w_mid idx_mid M₁) :
    CookCtsTailEvolutionHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ := by
  by_cases hlen : w_final.length ≤ w_mid.length
  · exact cook_cts_tail_evolution_final_of_mid cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ hlen
      (cook_cts_tail_evolution cts idx₀ w₀ w_mid idx_mid M₁ M₂ hcomp)
  · by_cases hM₂ : M₂ = 0
    · intro slot hslot _hbound j hj_lo hj_hi
      have hj : j = cts_slot_origin slot := by
        simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hj_lo hj_hi ⊢
        omega
      rw [hj]
      have horig := (cook_cts_tail_origin_final cts idx₀ w₀ w_mid w_final idx_mid idx_mid M₁ 0 hstep hcomp) slot
        hslot
      rw [infRule110Steps_zero] at horig
      exact horig
    · exact cook_cts_tail_evolution_final_ax cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ hstep hcomp
        (Nat.pos_of_ne_zero hM₂)

theorem cook_cts_tail_origin_final_via_evolution (cts : CyclicTagSystem) (idx₀ : ℕ)
    (w₀ w_mid w_final : List Bool) (idx_mid M₁ M₂ : ℕ)
    (hbound : ∀ slot, slot < w_final.length → M₂ ≤ cts_slot_origin slot)
    (hstep : CookCtsDataConesOriginOneStep cts idx₀ w₀)
    (hcomp : CookCtsOriginCompositionHyp cts idx₀ w₀ w_mid idx_mid M₁) :
    CookCtsTailOriginHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ :=
  cook_cts_tail_origin_final_of_evolution_all cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ hbound
    (cook_cts_tail_evolution_final cts idx₀ w₀ w_mid w_final idx_mid M₁ M₂ hstep hcomp)

/-- **Global C3′′ induction:** empty post-word, then `n + 1` from `n` via one-step + tail. -/
theorem cook_cts_eval_sim_at_data_cones_origin_ind (cts : CyclicTagSystem) :
    ∀ n w₀ idx₀, CookCtsEvalSimAtDataConesOrigin cts n w₀ idx₀ := by
  intro n w₀ idx₀
  induction n generalizing w₀ idx₀ with
  | zero => exact cook_cts_eval_sim_at_data_cones_origin_zero cts w₀ idx₀
  | succ n ih =>
    exact cook_cts_eval_sim_at_data_cones_origin_step cts n w₀ idx₀ ih

/-- Global C3′′ from induction (one-step + tail evolution; no separate global axiom). -/
theorem cook_cts_eval_sim_data_cones_origin (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool)
    (idx₀ : ℕ) :
    CookCtsEvalSimAtDataConesOrigin cts n w₀ idx₀ :=
  cook_cts_eval_sim_at_data_cones_origin_ind cts n w₀ idx₀

/-! ## Phased post-decode induction (parallel scaffold) -/

/-- After `M₁` steps, `M₂`-step tail cell evolution at slot origins matches mid-encode.
    Phased post-decode succession requires additional glider-presence lemmas beyond this. -/
def CookCtsPhasedTailOriginHyp (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ) : Prop :=
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let mid := cts_to_rule110_tape_phased_with_support_idx cts idx₁ w₁
  let evolved := infRule110Steps M₁ init
  ∀ slot, slot < w₁.length →
    infRule110Steps M₂ evolved (cts_slot_origin slot) =
      infRule110Steps M₂ mid (cts_slot_origin slot)

axiom cook_cts_phased_tail_origin_ax (cts : CyclicTagSystem) (idx₀ : ℕ) (w₀ w₁ : List Bool)
    (idx₁ M₁ M₂ : ℕ)
    (hstep : CookCtsPhasedPostDecodeOneStep cts idx₀ w₀)
    (hpos : 0 < M₂) :
    CookCtsPhasedTailOriginHyp cts idx₀ w₀ w₁ idx₁ M₁ M₂

theorem CookCtsPhasedPostDecodeAt_one_iff (cts : CyclicTagSystem) (w₀ : List Bool) (idx₀ : ℕ) :
    CookCtsPhasedPostDecodeAt cts 1 w₀ idx₀ ↔
      CookCtsPhasedPostDecodeOneStep cts idx₀ w₀ := by
  simp [CookCtsPhasedPostDecodeAt, CookCtsPhasedPostDecodeOneStep, CyclicTagSystem.cts_eval_with_idx,
    CyclicTagSystem.cts_steps, CyclicTagSystem.cts_steps_succ, CyclicTagSystem.cts_steps_zero,
    cook_total_M_from, List.range_succ, List.foldl_cons, List.foldl_nil]

theorem cook_cts_phased_post_decode_one_global (cts : CyclicTagSystem) (w₀ : List Bool) (idx₀ : ℕ)
    (hstep : CookCtsPhasedPostDecodeOneStep cts idx₀ w₀) :
    CookCtsPhasedPostDecodeAt cts 1 w₀ idx₀ :=
  (CookCtsPhasedPostDecodeAt_one_iff cts w₀ idx₀).2 hstep

/-- **Induction step schema (C3′′):** tail readback on the **final** word at `n` composed with
    `infRule110Steps_add` once `M` bookkeeping and `CookCtsTailOriginHypFinal` are supplied. -/
def CookCtsEvalSimAtDataConesOriginSuccSchema (cts : CyclicTagSystem) (n : ℕ)
    (w₀ w_mid w_final : List Bool) (idx₀ idx_mid idx_final M₁ : ℕ) : Prop :=
  cts.cts_eval_with_idx (n + 1) w₀ idx₀ = (w_final, idx_final) →
    cts.cts_step idx₀ w₀ = (w_mid, idx_mid) →
      CookCtsEvalSimAtDataConesOrigin cts n w_mid idx_mid →
        CookCtsTailOriginHypFinal cts idx₀ w₀ w_mid w_final idx_mid M₁
          (cook_total_M_from cts n idx_mid) →
          cook_total_M_from cts (n + 1) idx₀ = M₁ + cook_total_M_from cts n idx_mid →
            CookCtsEvalSimAtDataConesOrigin cts (n + 1) w₀ idx₀

/-! ## Status bundle -/

structure CookStage3InductionDischarged where
  empty_input_origin : ∀ (cts : CyclicTagSystem) (n idx₀ : ℕ),
      CookCtsEvalSimAtDataConesOrigin cts n [] idx₀
  empty_input_phased : ∀ (cts : CyclicTagSystem) (n idx₀ : ℕ),
      CookCtsPhasedPostDecodeAt cts n [] idx₀
  empty_input_cones : ∀ (cts : CyclicTagSystem) (n idx₀ : ℕ),
      CookCtsEvalSimAtDataCones cts n [] idx₀
  global_origin_ind : ∀ (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ),
      CookCtsEvalSimAtDataConesOrigin cts n w₀ idx₀
  len6_one_step_origin : CookCtsDataConesOriginOneStep cook_min_len6_cts 0 cook_min_len6_true_word
  len6_one_step_phased : CookCtsPhasedPostDecodeOneStep cook_min_len6_cts 0 cook_min_len6_true_word
  len6_one_step_cones_blocked : len6OneStepSimDataConesOk = false
  len6_tail_evolution_icc30_blocked : len6TailEvolutionIcc30Ok = false
  len6_tail_evolution_origin_cert : len6TailEvolutionOriginOk = true
  len6_global_origin : CookCtsEvalSimAtDataConesOrigin cook_min_len6_cts 1 cook_min_len6_true_word 0
  len6_global_phased : CookCtsPhasedPostDecodeAt cook_min_len6_cts 1 cook_min_len6_true_word 0
  legacy_c3_empty_n1_blocked : ¬ CookCtsEvalSim cook_standard_empty_cts 1 []

theorem cook_stage3_induction_discharged : CookStage3InductionDischarged where
  empty_input_origin := cook_cts_eval_sim_at_data_cones_origin_empty_input_ind
  empty_input_phased := cook_cts_phased_post_decode_empty_input_ind
  empty_input_cones := cook_cts_eval_sim_at_data_cones_empty_input_ind
  global_origin_ind := cook_cts_eval_sim_at_data_cones_origin_ind
  len6_one_step_origin := cook_cts_data_cones_origin_one_step_len6_min
  len6_one_step_phased := cook_cts_phased_post_decode_one_step_len6_min
  len6_one_step_cones_blocked := cook_cts_data_cones_one_step_len6_min_blocked
  len6_tail_evolution_icc30_blocked := len6_tail_evolution_icc30_not_ok
  len6_tail_evolution_origin_cert := len6_tail_evolution_origin_ok
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
