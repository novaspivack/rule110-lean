import Rule110.CookStage3CollisionModel
import Rule110.CookLen6DataConesOrigin
import Rule110.CookLen6PhasedPostDecode

/-!
# Stage 3 L=6 refined splits (SPEC_070_08)

Nonempty post-word discharge for the minimal L=6 appendant at `n = 1` is a **theorem**, not
`cook_cts_eval_sim_data_cones_origin_ax` / `cook_cts_phased_post_decode_ax`.
This module re-exports split theorems that route those cases to the discharged proofs.
-/

namespace Rule110

/-- The minimal L=6 one-step configuration discharged in Round 02 (#14–#15). -/
def cook_is_min_len6_one_step (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ) : Prop :=
  cts = cook_min_len6_cts ∧ n = 1 ∧ w₀ = cook_min_len6_true_word ∧ idx₀ = 0

theorem cook_is_min_len6_one_step_iff (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ) :
    cook_is_min_len6_one_step cts n w₀ idx₀ ↔
      cts = cook_min_len6_cts ∧ n = 1 ∧ w₀ = cook_min_len6_true_word ∧ idx₀ = 0 :=
  Iff.rfl

/-- Nonempty C3′′: L=6 n=1 uses theorem; all other nonempty cases use the axiom. -/
theorem cook_cts_eval_sim_data_cones_origin_nonempty (cts : CyclicTagSystem) (n : ℕ)
    (w₀ : List Bool) (idx₀ : ℕ) (hdata : 0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length) :
    CookCtsEvalSimAtDataConesOrigin cts n w₀ idx₀ := by
  by_cases h : cook_is_min_len6_one_step cts n w₀ idx₀
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact cook_cts_eval_sim_at_data_cones_origin_len6_one
  · exact cook_cts_eval_sim_data_cones_origin_ax cts n w₀ idx₀ hdata

/-- Nonempty phased post-decode: L=6 n=1 uses theorem; all other nonempty cases use the axiom. -/
theorem cook_cts_phased_post_decode_nonempty (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool)
    (idx₀ : ℕ) (hdata : 0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length) :
    CookCtsPhasedPostDecodeAt cts n w₀ idx₀ := by
  by_cases h : cook_is_min_len6_one_step cts n w₀ idx₀
  · rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact cook_cts_phased_post_decode_len6_one
  · exact cook_cts_phased_post_decode_ax cts n w₀ idx₀ hdata

/-- **Refined C3′′ split:** empty post-word theorem; L=6 n=1 theorem; other nonempty → axiom. -/
theorem cook_cts_eval_sim_at_data_cones_origin_refined (cts : CyclicTagSystem) (n : ℕ)
    (w₀ : List Bool) (idx₀ : ℕ) :
    CookCtsEvalSimAtDataConesOrigin cts n w₀ idx₀ := by
  by_cases hw : (cts.cts_eval_with_idx n w₀ idx₀).1 = []
  · exact cook_cts_eval_sim_at_data_cones_origin_of_empty_post_word cts n w₀ idx₀ hw
  · have hpos : 0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length := by
      cases w : (cts.cts_eval_with_idx n w₀ idx₀).1 with
      | nil => contradiction
      | cons _ _ => simp
    exact cook_cts_eval_sim_data_cones_origin_nonempty cts n w₀ idx₀ hpos

/-- **Refined phased-decode split:** empty post-word theorem; L=6 n=1 theorem; other nonempty → axiom. -/
theorem cook_cts_phased_post_decode_refined (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool)
    (idx₀ : ℕ) :
    CookCtsPhasedPostDecodeAt cts n w₀ idx₀ := by
  by_cases hw : (cts.cts_eval_with_idx n w₀ idx₀).1 = []
  · exact cook_cts_phased_post_decode_of_empty_post_word cts n w₀ idx₀ hw
  · have hpos : 0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length := by
      cases w : (cts.cts_eval_with_idx n w₀ idx₀).1 with
      | nil => contradiction
      | cons _ _ => simp
    exact cook_cts_phased_post_decode_nonempty cts n w₀ idx₀ hpos

end Rule110
