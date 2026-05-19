import Rule110.CyclicTagSystem
import Rule110.CTStoRule110
import Rule110.CookCollisionWitnesses
import Rule110.Ether
import Rule110.InfTape

/-!
# Stage 3 Cook bridge verification (partial)

Base cases for `cook_cts_eval_sim_ax` (multi-step CTS ↔ Rule 110 simulation).
-/

namespace Rule110

@[simp] theorem cook_total_M_zero (cts : CyclicTagSystem) :
    cook_total_M cts 0 = 0 := by
  simp [cook_total_M]

/-- **Stage 3 base case (n = 0):** zero CTS steps = zero Rule 110 steps; phased tape unchanged. -/
theorem cook_cts_eval_sim_zero (cts : CyclicTagSystem) (w₀ : List Bool) :
    CookCtsEvalSim cts 0 w₀ := by
  simp [CookCtsEvalSim, CyclicTagSystem.cts_eval_zero, cook_total_M_zero, infRule110Steps_zero,
    cts_to_rule110_tape_phased]

theorem cook_total_M_succ_witness (cts : CyclicTagSystem) (n : ℕ) :
    cook_total_M cts (n + 1) =
      cook_total_M cts n +
        cook_M_for_appendant_len (cts.appendants.getD (n % cts.cycleLen) []).length :=
  cook_total_M_succ cts n

theorem cook_total_M_succ_empty_appendant (cts : CyclicTagSystem) (n : ℕ)
    (h : ∀ k, k < cts.cycleLen → (cts.appendants.getD k []).length = 0) :
    cook_total_M cts (n + 1) = cook_total_M cts n + 30 := by
  rw [cook_total_M_succ]
  have hlen : (cts.appendants.getD (n % cts.cycleLen) []).length = 0 := by
    by_cases hk : cts.cycleLen = 0
    · cases cts with | mk appendants
      cases appendants with
      | nil => simp
      | cons _ _ => simp [CyclicTagSystem.cycleLen] at hk
    · exact h _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hk))
  have hM : cook_M_for_appendant_len (cts.appendants.getD (n % cts.cycleLen) []).length = 30 := by
    simp only [cook_M_for_appendant_len, hlen]
    split <;> decide
  rw [hM]

theorem cook_cts_eval_one_empty (cts : CyclicTagSystem) :
    cts.cts_eval 1 [] = [] :=
  cts_eval_one_empty cts

theorem cook_total_M_one_empty_appendant (cts : CyclicTagSystem)
    (hzero : ∀ k, k < cts.cycleLen → (cts.appendants.getD k []).length = 0) :
    cook_total_M cts 1 = 30 := by
  rw [cook_total_M_succ_empty_appendant cts 0 hzero, cook_total_M_zero]

theorem cook_cts_eval_empty_step30 (cts : CyclicTagSystem)
    (hzero : ∀ k, k < cts.cycleLen → (cts.appendants.getD k []).length = 0)
    (hstep : CookCtsEvalSim cts 1 (w₀ := [])) :
    gliders_to_tape_phased [] = infRule110Steps 30 (gliders_to_tape_phased []) := by
  rw [CookCtsEvalSim] at hstep
  rw [cook_cts_eval_one_empty cts, cts_word_to_placements_phased_nil,
      cts_to_rule110_tape_phased, cts_word_to_placements_phased_nil,
      cook_total_M_one_empty_appendant cts hzero] at hstep
  exact hstep

/-- **Stage 3 induction scaffold (empty appendant only):**
    If the one-step axiom holds at `w₀ = []` and every appendant is empty, then the axiom
    holds for all `n`. Requires the one-step case to be a 30-step fixed point on the empty
    phased encoding (`cook_cts_eval_sim_ax cts 1 []` implies
    `gliders_to_tape_phased [] = infRule110Steps 30 (gliders_to_tape_phased [])`). -/
theorem cook_cts_eval_sim_empty_from_one_step (cts : CyclicTagSystem)
    (hempty : ∀ n, cts.cts_eval n [] = [])
    (hzero : ∀ k, k < cts.cycleLen → (cts.appendants.getD k []).length = 0)
    (hstep : CookCtsEvalSim cts 1 (w₀ := [])) :
    ∀ n, CookCtsEvalSim cts n (w₀ := []) := by
  intro n
  induction n with
  | zero => exact cook_cts_eval_sim_zero cts []
  | succ n ih =>
    unfold CookCtsEvalSim at ih hstep ⊢
    have ih' := ih
    rw [hempty n, cts_word_to_placements_phased_nil,
        cts_to_rule110_tape_phased, cts_word_to_placements_phased_nil] at ih'
    have hRight :
        infRule110Steps (cook_total_M cts (n + 1)) (gliders_to_tape_phased []) =
          gliders_to_tape_phased [] := by
      calc infRule110Steps (cook_total_M cts (n + 1)) (gliders_to_tape_phased [])
          _ = infRule110Steps 30 (infRule110Steps (cook_total_M cts n) (gliders_to_tape_phased [])) := by
                rw [cook_total_M_succ_empty_appendant cts n hzero,
                    infRule110Steps_add (cook_total_M cts n) 30 (gliders_to_tape_phased [])]
          _ = infRule110Steps 30 (gliders_to_tape_phased []) :=
            (congrArg (infRule110Steps 30) ih').symm
          _ = gliders_to_tape_phased [] := by
            exact Eq.symm (cook_cts_eval_empty_step30 cts hzero hstep)
    rw [hempty (n + 1), cts_word_to_placements_phased_nil,
        cts_to_rule110_tape_phased, cts_word_to_placements_phased_nil]
    exact hRight.symm

theorem cook_cts_eval_sim_standard_empty_from_one_step
    (hstep : CookCtsEvalSim cook_standard_empty_cts 1 (w₀ := [])) :
    ∀ n, CookCtsEvalSim cook_standard_empty_cts n (w₀ := []) :=
  cook_cts_eval_sim_empty_from_one_step cook_standard_empty_cts
    (fun n => cook_standard_empty_cts_eval n)
    (fun k hk => by
      have hk0 : k = 0 := by
        simp [cook_standard_empty_cts, CyclicTagSystem.cycleLen] at hk
        omega
      subst hk0
      rfl)
    hstep

/-- Bare ether drifts under one Rule 110 step (existing spotcheck); empty phased encoding cannot
    satisfy `CookCtsEvalSim` at n=1 without Cook collision simulation restoring the tape. -/
theorem cookEther_not_pointwise_fixed_one_step :
    ∃ i, infRule110Steps 1 cookEther i ≠ cookEther i := by
  refine ⟨5, ?_⟩
  rw [infRule110Steps_cookEther_shift_spotcheck₁]
  native_decide

end Rule110
