import Mathlib.Computability.TuringMachine.Computable

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

/-- Stage 4: Mathlib TM2 identity anchor **and** Cook CTS scaffolds (identity + consume-head). -/
theorem cook_stage4_triple_scaffold :
    Nonempty FinTM2 ∧
      Nonempty (TMCTSCompilation tmIdentityStep) ∧
        Nonempty (TMCTSCompilation tmBoolIdentityStep) ∧
          Nonempty (TMCTSCompilation tmConsumeHeadStep) :=
  ⟨⟨idComputer Bool⟩, ⟨trivialIdentityTMComp⟩, ⟨cookBoolIdentityTMComp⟩, ⟨cookConsumeHeadTMComp⟩⟩

/-- Stage 4: Mathlib TM2 identity anchor **and** Cook CTS identity scaffolds coexist. -/
theorem cook_stage4_dual_identity_scaffold :
    Nonempty FinTM2 ∧
      Nonempty (TMCTSCompilation tmIdentityStep) ∧
        Nonempty (TMCTSCompilation tmBoolIdentityStep) :=
  ⟨⟨idComputer Bool⟩, ⟨trivialIdentityTMComp⟩, ⟨cookBoolIdentityTMComp⟩⟩

end Rule110
