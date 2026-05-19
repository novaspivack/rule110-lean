import Mathlib.Computability.TuringMachine.Computable

import Rule110.CookFinTM2Compilation
import Rule110.CookTMCompilation
import Rule110.TMtoCTS

/-!
# Mathlib TM2 ↔ Cook CTS compilation bridge (Stage 4)

Cook's full FinTM2 → CTS encoding remains open. This module anchors the pipeline to
Mathlib's `FinTM2` identity machine and records a Bool-step scaffold alongside our
existing `Unit` identity compilation.
-/

namespace Rule110

open Turing CyclicTagSystem

/-- Cook §2 target: a bundled `FinTM2` admits a step-correct `TMCTSCompilation`. Still open
    for nontrivial machines; see `cook_stage4_tm_compiles_step_bundle` for scaffold instances. -/
def CookFinTM2Compiles (M : FinTM2) : Prop :=
  ∃ (comp : TMCTSCompilation M.step), TMCompilesStep M.step comp

/-- Mathlib provides a halting identity `FinTM2` (input stack = output stack). -/
theorem cook_fin_tm2_id_machine : Nonempty FinTM2 :=
  ⟨idComputer Bool⟩

/-- Identity step on `Bool` (placeholder until Cook FinTM2 encoding is wired). -/
def tmBoolIdentityStep (b : Bool) : Option Bool :=
  some b

/-- Bool configurations encode as empty or singleton CTS words on the standard empty CTS. -/
def cookBoolIdentityTMComp : TMCTSCompilation tmBoolIdentityStep where
  sys := cook_standard_empty_cts
  enc := fun b => (if b then [true] else [], 0)
  dec := fun (w, _) => w != []
  decode_roundtrip := fun b => by
    cases b <;> simp
  simulates_step := fun {c c'} h => by
    rcases Option.some.inj h with rfl
    refine ⟨0, ?_⟩
    cases c <;> simp [cts_eval_with_idx_zero, cts_steps]

theorem cook_bool_identity_simulates_step (b b' : Bool) (h : tmBoolIdentityStep b = some b') :
    ∃ m,
      let (w, idx) := cookBoolIdentityTMComp.enc b
      let (w', idx') := cookBoolIdentityTMComp.sys.cts_steps m w idx
      cookBoolIdentityTMComp.dec (w', idx') = b' :=
  cookBoolIdentityTMComp.simulates_step h

theorem cook_bool_identity_eval_with_idx_add (b : Bool) (m n : ℕ) :
    cookBoolIdentityTMComp.eval_with_idx b (m + n) =
      let (w', idx') := cookBoolIdentityTMComp.eval_with_idx b m
      cookBoolIdentityTMComp.sys.cts_eval_with_idx n w' idx' :=
  cookBoolIdentityTMComp.eval_with_idx_add b m n

theorem cook_bool_identity_tm_compiles_step :
    TMCompilesStep tmBoolIdentityStep cookBoolIdentityTMComp :=
  cookBoolIdentityTMComp.tm_compiles_step

/-- All four Stage 4 scaffolds satisfy `TMCompilesStep`. -/
theorem cook_stage4_tm_compiles_step_bundle :
    TMCompilesStep tmIdentityStep trivialIdentityTMComp ∧
      TMCompilesStep tmBoolIdentityStep cookBoolIdentityTMComp ∧
        TMCompilesStep tmConsumeHeadStep cookConsumeHeadTMComp ∧
          TMCompilesStep tmCountDownStep cookCountDownTMComp :=
  ⟨trivial_identity_tm_compiles_step, cook_bool_identity_tm_compiles_step,
    cook_consume_head_tm_compiles_step, cook_count_down_tm_compiles_step⟩

/-- Stage 4: Mathlib TM2 identity anchor **and** Cook CTS scaffolds (identity + consume-head + countdown). -/
theorem cook_stage4_quad_scaffold :
    Nonempty FinTM2 ∧
      Nonempty (TMCTSCompilation tmIdentityStep) ∧
        Nonempty (TMCTSCompilation tmBoolIdentityStep) ∧
          Nonempty (TMCTSCompilation tmConsumeHeadStep) ∧
            Nonempty (TMCTSCompilation tmCountDownStep) :=
  ⟨⟨idComputer Bool⟩, ⟨trivialIdentityTMComp⟩, ⟨cookBoolIdentityTMComp⟩, ⟨cookConsumeHeadTMComp⟩,
    ⟨cookCountDownTMComp⟩⟩

/-- Stage 4: Mathlib TM2 identity anchor **and** Cook CTS identity scaffolds coexist. -/
theorem cook_stage4_dual_identity_scaffold :
    Nonempty FinTM2 ∧
      Nonempty (TMCTSCompilation tmIdentityStep) ∧
        Nonempty (TMCTSCompilation tmBoolIdentityStep) :=
  ⟨⟨idComputer Bool⟩, ⟨trivialIdentityTMComp⟩, ⟨cookBoolIdentityTMComp⟩⟩

/-- Mathlib's halting identity `FinTM2` compiles to CTS (index-tagged empty-appendant encoding). -/
theorem cook_idComputer_fin_tm2_compiles : CookFinTM2Compiles (idComputer Bool) := by
  obtain ⟨comp, h⟩ := idComputer_fin_tm2_compiles_witness
  exact ⟨comp, h⟩

/-- Consume-head `Fin 2` scaffold and Mathlib `FinTM2` anchor (see `CookFinTM2ConsumeHead`). -/
theorem cook_stage4_consume_head_bundle :
    TMCompilesStep tmConsumeHeadStep cookConsumeHeadTMComp ∧
      CookFinTM2Compiles (idComputer Bool) :=
  ⟨cook_consume_head_tm_compiles_step, cook_idComputer_fin_tm2_compiles⟩

end Rule110
