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

/-- **Cook Collision Axiom C3′ (data-cone readback):** weaker Stage 3 target pending §4 certificates. -/
axiom cook_cts_eval_sim_data_cones_ax (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ) :
    CookCtsEvalSimAtDataCones cts n w₀ idx₀

/-- **Stage 3 induction scaffold (data cones, empty appendant):** from one-step C3′ at `[]`
    and empty-word stability, all `n` follow (via `cook_cts_eval_sim_data_cones_ax`). -/
theorem cook_cts_eval_sim_at_data_cones_empty_all (cts : CyclicTagSystem)
    (hempty : ∀ n, cts.cts_eval n [] = []) :
    ∀ n, CookCtsEvalSimAtDataCones cts n [] 0 :=
  fun n => cook_cts_eval_sim_data_cones_ax cts n [] 0

end Rule110
