import Rule110.CookLen6AppendantSim
import Rule110.CTStoRule110

/-!
# Stage 3 collision-invariant formulation (Cook §4)

After 10 failed attempts on **static re-encoding** (`CookCtsEvalSimAt`: full `InfTape`
equality against post-step placements), this module records the weaker **data-cone readback**
target aligned with Cook §4 collision dynamics.

Full tape equality implies data-cone agreement; the converse fails (Round 02 negative
witnesses). Future discharge of Stage 3 should target `CookCtsEvalSimAtDataCones` plus
finite collision certificates (`CookConstructionCollisionKind`), not placement equality alone.
-/

namespace Rule110

/-- Read cone `[slot·spacing − 30, slot·spacing + 30]` (61 cells). -/
def cook_cts_slot_cone_cell (slot d : ℕ) : ℕ :=
  cts_slot_origin slot - 30 + d

/-- After `M` Rule 110 steps, every data-slot read cone matches the post-`n`-step CTS encode. -/
def CookCtsEvalSimAtDataCones (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ) :
    Prop :=
  let (w, idx) := cts.cts_eval_with_idx n w₀ idx₀
  let M := cook_total_M_from cts n idx₀
  let init := cts_to_rule110_tape_phased_with_support_idx cts idx₀ w₀
  let target := cts_to_rule110_tape_phased_with_support_idx cts idx w
  ∀ slot, slot < w.length →
    ∀ d, d < 61 →
      infRule110Steps M init (cook_cts_slot_cone_cell slot d) =
        target (cook_cts_slot_cone_cell slot d)

/-- **Stage 3 base case (data cones):** zero steps, zero Rule 110 steps. -/
theorem cook_cts_eval_sim_at_data_cones_zero (cts : CyclicTagSystem) (w₀ : List Bool) (idx₀ : ℕ) :
    CookCtsEvalSimAtDataCones cts 0 w₀ idx₀ := by
  intro slot hslot d _hd
  simp [CookCtsEvalSimAtDataCones, CyclicTagSystem.cts_eval_with_idx_zero,
    cook_total_M_from_zero, infRule110Steps_zero]

/-- Static full-tape simulation implies data-cone readback (strict implication). -/
theorem CookCtsEvalSimAt_implies_data_cones (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool)
    (idx₀ : ℕ) (h : CookCtsEvalSimAt cts n w₀ idx₀) :
    CookCtsEvalSimAtDataCones cts n w₀ idx₀ := by
  intro slot hslot d _hd
  dsimp [CookCtsEvalSimAt] at h
  dsimp [CookCtsEvalSimAtDataCones, cts_to_rule110_tape_phased_with_support_idx]
  exact (congrFun h (cook_cts_slot_cone_cell slot d)).symm

/-- L=6: bounded list sim refutes data-cone readback on slots 0–5 (same predicate as before). -/
def len6DataConesReadbackOk : Bool :=
  len6OneStepSimDataConesOk

theorem len6_data_cones_readback_not_ok : len6DataConesReadbackOk = false :=
  len6_one_step_data_cones_not_ok

/-- **Vacuous discharge:** when the post-`n` CTS word is empty, no data slots require readback. -/
theorem cook_cts_eval_sim_at_data_cones_of_empty_post_word (cts : CyclicTagSystem) (n : ℕ)
    (w₀ : List Bool) (idx₀ : ℕ)
    (hw : (cts.cts_eval_with_idx n w₀ idx₀).1 = []) :
    CookCtsEvalSimAtDataCones cts n w₀ idx₀ := by
  intro slot hslot d _hd
  have hlen : (cts.cts_steps n w₀ idx₀).1.length = 0 := by
    rw [← CyclicTagSystem.cts_eval_with_idx, hw, List.length_nil]
  have hpos : slot < 0 := by
    rw [hlen] at hslot
    exact hslot
  exact (Nat.not_lt_zero slot hpos).elim

/-- **C3′ discharge (empty input word):** no axiom required — post-step word stays empty. -/
theorem cook_cts_eval_sim_at_data_cones_empty_input (cts : CyclicTagSystem) (n : ℕ) (idx₀ : ℕ) :
    CookCtsEvalSimAtDataCones cts n [] idx₀ :=
  cook_cts_eval_sim_at_data_cones_of_empty_post_word cts n [] idx₀
    (CyclicTagSystem.cts_eval_with_idx_empty cts n idx₀)

/-- **Cook Collision Axiom C3′ (data-cone readback):** required only when post-step word
    has data slots (`w.length > 0`). Empty-word cases are discharged above. -/
axiom cook_cts_eval_sim_data_cones_ax (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ)
    (hdata : 0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length) :
    CookCtsEvalSimAtDataCones cts n w₀ idx₀

/-- Split C3′: empty post-word is a theorem; nonempty post-word uses the axiom. -/
theorem cook_cts_eval_sim_at_data_cones (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ) :
    CookCtsEvalSimAtDataCones cts n w₀ idx₀ := by
  by_cases hw : (cts.cts_eval_with_idx n w₀ idx₀).1 = []
  · exact cook_cts_eval_sim_at_data_cones_of_empty_post_word cts n w₀ idx₀ hw
  · have hpos : 0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length := by
      cases w : (cts.cts_eval_with_idx n w₀ idx₀).1 with
      | nil => contradiction
      | cons _ _ => simp
    exact cook_cts_eval_sim_data_cones_ax cts n w₀ idx₀ hpos

/-- **Stage 3 (data cones, empty appendant):** all `n` at `w₀ = []` without legacy C3. -/
theorem cook_cts_eval_sim_at_data_cones_empty_all (cts : CyclicTagSystem) (n : ℕ) :
    CookCtsEvalSimAtDataCones cts n [] 0 :=
  cook_cts_eval_sim_at_data_cones_empty_input cts n 0

theorem cook_standard_empty_cts_data_cones (n : ℕ) :
    CookCtsEvalSimAtDataCones cook_standard_empty_cts n [] 0 :=
  cook_cts_eval_sim_at_data_cones_empty_input cook_standard_empty_cts n 0

end Rule110
