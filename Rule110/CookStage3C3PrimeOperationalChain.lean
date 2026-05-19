import Rule110.CookStage3CollisionModel
import Rule110.CookStage3EmptyAppendantChain

/-!
# Stage 3 operational certification chain (C3′ path)

Documents that the **operational** Stage 3 target is data-cone readback (`CookCtsEvalSimAtDataCones`
and refinements), not legacy global tape equality (`CookCtsEvalSim`).

For empty input words, all three operational predicates are discharged for all `n` without bridge
axioms. Legacy `CookCtsEvalSim` at n=1 on the standard empty CTS is refuted.
-/

namespace Rule110

/-- Empty input word: C3′ + C3′′ + phased post-decode at every step count. -/
theorem cook_stage3_empty_word_operational (cts : CyclicTagSystem) (n : ℕ) (idx₀ : ℕ) :
    CookCtsEvalSimAtDataCones cts n [] idx₀ ∧
      CookCtsEvalSimAtDataConesOrigin cts n [] idx₀ ∧
        CookCtsPhasedPostDecodeAt cts n [] idx₀ :=
  ⟨cook_cts_eval_sim_at_data_cones_empty_input cts n idx₀,
    cook_cts_eval_sim_at_data_cones_origin_empty_input cts n idx₀,
    cook_cts_phased_post_decode_empty_input cts n idx₀⟩

/-- Standard empty CTS: operational Stage 3 holds at all `n` (no legacy C3 axiom). -/
theorem cook_standard_empty_stage3_operational (n : ℕ) :
    CookCtsEvalSimAtDataCones cook_standard_empty_cts n [] 0 ∧
      CookCtsEvalSimAtDataConesOrigin cook_standard_empty_cts n [] 0 ∧
        CookCtsPhasedPostDecodeAt cook_standard_empty_cts n [] 0 :=
  cook_stage3_empty_word_operational cook_standard_empty_cts n 0

/-- Operational bundle: empty-appendant C3′ discharge + legacy n=1 refutation. -/
structure CookStage3OperationalDischarged where
  empty_word : ∀ (cts : CyclicTagSystem) (n : ℕ) (idx₀ : ℕ),
      CookCtsEvalSimAtDataCones cts n [] idx₀ ∧
        CookCtsEvalSimAtDataConesOrigin cts n [] idx₀ ∧
          CookCtsPhasedPostDecodeAt cts n [] idx₀
  empty_appendant : CookEmptyAppendantC3PrimeDischarged
  legacy_n1_refuted : ¬ CookCtsEvalSim cook_standard_empty_cts 1 []

theorem cook_stage3_operational_discharged : CookStage3OperationalDischarged where
  empty_word := cook_stage3_empty_word_operational
  empty_appendant := cook_empty_appendant_c3prime_discharged
  legacy_n1_refuted := cook_standard_empty_cts_legacy_c3_n1_blocked

end Rule110
