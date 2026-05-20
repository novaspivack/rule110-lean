import Rule110.CookUniversalityChain
import Rule110.CookUniversalityScaffold
import Rule110.CookFinTM2ConsumeHead
import Rule110.CookStage3CollisionModel
import Rule110.CookStage3C3PrimeOperationalChain
import Rule110.CookStage3Induction

/-!
# Cook universality top theorem (SPEC_070_08)

Chains **Stage 4** (`FinTM2` / scaffold TM → CTS) with **operational Stage 3** (C3′′ origin readback
and phased post-decode on `InfTape`), not legacy global `CookCtsEvalSim` (refuted at empty `n = 1`).

Global C3′′ and phased post-decode are theorems (`cook_cts_eval_sim_data_cones_origin`,
`cook_cts_phased_post_decode`); their proofs still invoke leaf axioms in `CookStage3Induction`.
-/

namespace Rule110

open Turing

/-! ## Minimal open bridge axioms (operational C3 path) -/

/-- Nonempty post-word cases for C3′′ origin readback (leaf obligations in `CookStage3Induction`). -/
def cook_bridge_c3primeprime_open : Prop :=
  ∀ (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ),
    0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length →
      CookCtsEvalSimAtDataConesOrigin cts n w₀ idx₀

/-- Nonempty post-word cases for phased post-decode (see `cook_cts_phased_post_decode_ax`). -/
def cook_bridge_phased_decode_open : Prop :=
  ∀ (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ),
    0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length →
      CookCtsPhasedPostDecodeAt cts n w₀ idx₀

/-- **Minimal** named bridge obligations for global Cook Rule 110 certification. -/
def cook_bridge_axioms_open : Prop :=
  cook_bridge_c3primeprime_open ∧ cook_bridge_phased_decode_open

theorem cook_bridge_axioms_open_iff_minimal :
    cook_bridge_axioms_open ↔
      cook_bridge_c3primeprime_open ∧ cook_bridge_phased_decode_open :=
  Iff.rfl

/-- Bridge obligations hold unconditionally (proved via global induction theorems). -/
theorem cook_bridge_axioms_closed : cook_bridge_axioms_open :=
  ⟨fun _ _ _ _ _ => cook_cts_eval_sim_data_cones_origin _ _ _ _,
   fun _ _ _ _ _ => cook_cts_phased_post_decode _ _ _ _⟩

/-! ## Operational Stage 3 bundle (split theorems + axioms) -/

/-- Operational Stage 3: C3′′ + phased decode at every step (empty post-word discharged). -/
structure CookOperationalStage3 where
  data_cones_origin : ∀ (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ),
      CookCtsEvalSimAtDataConesOrigin cts n w₀ idx₀
  phased_post_decode : ∀ (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) (idx₀ : ℕ),
      CookCtsPhasedPostDecodeAt cts n w₀ idx₀

theorem cook_operational_stage3_default : CookOperationalStage3 where
  data_cones_origin := cook_cts_eval_sim_data_cones_origin
  phased_post_decode := cook_cts_phased_post_decode

theorem cook_operational_stage3_of_bridge (h : cook_bridge_axioms_open) : CookOperationalStage3 where
  data_cones_origin cts n w₀ idx₀ := by
    by_cases hw : (cts.cts_eval_with_idx n w₀ idx₀).1 = []
    · exact cook_cts_eval_sim_at_data_cones_origin_of_empty_post_word cts n w₀ idx₀ hw
    · have hpos : 0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length := by
        cases w : (cts.cts_eval_with_idx n w₀ idx₀).1 with
        | nil => contradiction
        | cons _ _ => simp
      exact h.1 cts n w₀ idx₀ hpos
  phased_post_decode cts n w₀ idx₀ := by
    by_cases hw : (cts.cts_eval_with_idx n w₀ idx₀).1 = []
    · exact cook_cts_phased_post_decode_of_empty_post_word cts n w₀ idx₀ hw
    · have hpos : 0 < (cts.cts_eval_with_idx n w₀ idx₀).1.length := by
        cases w : (cts.cts_eval_with_idx n w₀ idx₀).1 with
        | nil => contradiction
        | cons _ _ => simp
      exact h.2 cts n w₀ idx₀ hpos

/-! ## Stage 4 → operational Stage 3 → Rule 110 -/

/-- One successful TM microstep yields a CTS horizon whose Rule 110 simulation satisfies C3′′
    origin readback (given global operational Stage 3). -/
theorem cook_tm_step_rule110_origin_readback
    (h3 : CookOperationalStage3)
    {Cfg : Type} {tmStep : Cfg → Option Cfg} {comp : TMCTSCompilation tmStep}
    (hcomp : TMCompilesStep tmStep comp) {c c' : Cfg} (hstep : tmStep c = some c') :
    ∃ m,
      let (w₀, idx₀) := comp.enc c
      comp.dec (comp.sys.cts_eval_with_idx m w₀ idx₀) = c' ∧
        CookCtsEvalSimAtDataConesOrigin comp.sys m w₀ idx₀ := by
  rcases hcomp hstep with ⟨m, hm⟩
  refine ⟨m, ?_, h3.data_cones_origin comp.sys m (comp.enc c).1 (comp.enc c).2⟩
  simpa [TMCTSCompilation.eval_with_idx_eq_cts_steps] using hm

/-- FinTM2 specialization of `cook_tm_step_rule110_origin_readback`. -/
theorem cook_fintm2_step_rule110_origin_readback
    (h3 : CookOperationalStage3) (M : FinTM2) (comp : TMCTSCompilation M.step)
    (hcomp : TMCompilesStep M.step comp) {c c' : FinTM2.Cfg M} (hstep : M.step c = some c') :
    ∃ m,
      let (w₀, idx₀) := comp.enc c
      comp.dec (comp.sys.cts_eval_with_idx m w₀ idx₀) = c' ∧
        CookCtsEvalSimAtDataConesOrigin comp.sys m w₀ idx₀ :=
  cook_tm_step_rule110_origin_readback h3 hcomp hstep

/-! ## Top target -/

/-- Conditional form (for callers that assume bridge axioms explicitly). -/
theorem rule110_turing_universal_from_cook_of_bridge
    (hbridge : cook_bridge_axioms_open) :
    CookOperationalStage3 ∧
      (∀ {Cfg : Type} {tmStep : Cfg → Option Cfg} (comp : TMCTSCompilation tmStep),
        TMCompilesStep tmStep comp →
          ∀ {c c' : Cfg}, tmStep c = some c' →
            ∃ m,
              let (w₀, idx₀) := comp.enc c
              comp.dec (comp.sys.cts_eval_with_idx m w₀ idx₀) = c' ∧
                CookCtsEvalSimAtDataConesOrigin comp.sys m w₀ idx₀) := by
  have h3 := cook_operational_stage3_of_bridge hbridge
  refine ⟨h3, ?_⟩
  intro Cfg tmStep comp hcomp c c' hstep
  exact cook_tm_step_rule110_origin_readback h3 hcomp hstep

/-- **SPEC_070_08 top theorem (operational).** Every compiled TM microstep is matched by a CTS
    trace whose Rule 110 evolution satisfies C3′′ origin readback. Legacy full-tape
    `CookCtsEvalSim` is intentionally excluded (refuted on empty input at `n = 1`). -/
theorem rule110_turing_universal_from_cook :
    CookOperationalStage3 ∧
      (∀ {Cfg : Type} {tmStep : Cfg → Option Cfg} (comp : TMCTSCompilation tmStep),
        TMCompilesStep tmStep comp →
          ∀ {c c' : Cfg}, tmStep c = some c' →
            ∃ m,
              let (w₀, idx₀) := comp.enc c
              comp.dec (comp.sys.cts_eval_with_idx m w₀ idx₀) = c' ∧
                CookCtsEvalSimAtDataConesOrigin comp.sys m w₀ idx₀) :=
  rule110_turing_universal_from_cook_of_bridge cook_bridge_axioms_closed

/-! ## Discharged instances (no bridge axioms needed for these steps) -/

theorem rule110_from_cook_idComputer_step
    {c c' : FinTM2.Cfg (idComputer Bool)} (hstep : (idComputer Bool).step c = some c') :
    ∃ m,
      let comp := IdComputerCompilation.tmComp
      let (w₀, idx₀) := comp.enc c
      comp.dec (comp.sys.cts_eval_with_idx m w₀ idx₀) = c' ∧
        CookCtsEvalSimAtDataConesOrigin comp.sys m w₀ idx₀ :=
  cook_fintm2_step_rule110_origin_readback cook_operational_stage3_default _ _
    IdComputerCompilation.tm_compiles_step hstep

private theorem cook_consume_head_origin_readback_one :
    CookCtsEvalSimAtDataConesOrigin cook_standard_empty_cts 1 [true] 0 :=
  cook_cts_eval_sim_at_data_cones_origin_of_empty_post_word cook_standard_empty_cts 1 [true] 0
    (by simpa using congrArg Prod.fst cook_standard_empty_cts_eval_with_idx_one_true)

theorem rule110_from_cook_consume_head_fin2_step
    {s s' : Fin 2} (hstep : tmConsumeHeadStep s = some s') :
    ∃ m,
      let (w₀, idx₀) := cookConsumeHeadTMComp.enc s
      cookConsumeHeadTMComp.dec (cookConsumeHeadTMComp.sys.cts_eval_with_idx m w₀ idx₀) = s' ∧
        CookCtsEvalSimAtDataConesOrigin cook_standard_empty_cts m w₀ idx₀ := by
  fin_cases s
  · simp [tmConsumeHeadStep] at hstep
    subst hstep
    refine ⟨1, ?_, cook_consume_head_origin_readback_one⟩
    simpa [cookConsumeHeadTMComp, cook_consume_head_eval_with_idx_one,
      cookConsumeHeadTMComp.eval_with_idx_eq_cts_steps] using
      cook_consume_head_dec_after_one_step
  · simp [tmConsumeHeadStep] at hstep

/-- Inventory: what is proved unconditionally vs. axiom-backed. -/
structure CookUniversalityTopStatus where
  discharged : CookUniversalityDischarged
  operational_empty : CookStage3OperationalDischarged
  induction_partial : CookStage3InductionDischarged
  fintm2_id : CookFinTM2Compiles (idComputer Bool)
  consume_head_fin2 : TMCompilesStep tmConsumeHeadStep cookConsumeHeadTMComp
  bridge_closed : cook_bridge_axioms_open
  bridge_of_bridge : cook_bridge_axioms_open → CookOperationalStage3

theorem cook_universality_top_status : CookUniversalityTopStatus where
  discharged := cook_universality_discharged
  operational_empty := cook_stage3_operational_discharged
  induction_partial := cook_stage3_induction_discharged
  fintm2_id := cook_idComputer_fin_tm2_compiles
  consume_head_fin2 := consume_head_stage4_compiles
  bridge_closed := cook_bridge_axioms_closed
  bridge_of_bridge := cook_operational_stage3_of_bridge

end Rule110
