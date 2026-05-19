import Rule110.CyclicTagSystem
import Rule110.CTStoRule110
import Rule110.CookCollisionWitnesses
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
    gliders_to_tape_phased (cts_word_to_placements_phased (cts.cts_eval 0 w₀)) =
      infRule110Steps (cook_total_M cts 0) (cts_to_rule110_tape_phased cts w₀) := by
  simp [CyclicTagSystem.cts_eval_zero, cook_total_M_zero, infRule110Steps_zero,
    cts_to_rule110_tape_phased]

theorem cook_total_M_succ_witness (cts : CyclicTagSystem) (n : ℕ) :
    cook_total_M cts (n + 1) =
      cook_total_M cts n +
        cook_M_for_appendant_len (cts.appendants.getD (n % cts.cycleLen) []).length :=
  cook_total_M_succ cts n

end Rule110
