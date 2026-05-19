import Mathlib.Computability.TuringMachine.Computable

import Rule110.CookFinTM2Compilation
import Rule110.CookTM2Bridge
import Rule110.CookTMCompilation

/-!
# Consume-head CTS encoding on Mathlib `idComputer Bool`

`cookConsumeHeadTMComp` simulates the two-state `tmConsumeHeadStep` on `cook_standard_empty_cts`.
Mathlib's `idComputer Bool` preserves its input stack across the halt transition, so it cannot
share the same `(enc, dec)` pair (halt would require CTS word `[]` while the stack may be
nonempty). The authoritative consume-head Stage-4 witness remains `cook_consume_head_tm_compiles_step`.

This file records the **proved** `FinTM2` anchor (`CookFinTM2Compilation`) and alignment lemmas
between the Fin 2 scaffold and the identity machine's halting step shape.
-/

namespace Rule110

open CyclicTagSystem
open Turing Turing.TM2

/-- Mathlib halting machine (proved in `CookFinTM2Compilation`). -/
abbrev consumeHeadFinTMAnchor : FinTM2 := idComputer Bool

namespace ConsumeHeadIdComputerCompilation

/-- Alternate empty-CTS marker encoding (active `[true]`, halt `[]`). -/
def enc (c : FinTM2.Cfg consumeHeadFinTMAnchor) : List Bool × ℕ :=
  match c.l with
  | some () => ([true], 0)
  | none => ([], 0)

def dec (p : List Bool × ℕ) : FinTM2.Cfg consumeHeadFinTMAnchor :=
  match p.1 with
  | [] => ⟨none, (), fun _ => []⟩
  | _ => ⟨some (), (), fun _ => []⟩

end ConsumeHeadIdComputerCompilation

/-- Active label uses the consume-head CTS marker `[true]`. -/
theorem consume_head_active_enc_marker (c : FinTM2.Cfg consumeHeadFinTMAnchor) (hl : c.l = some ()) :
    (ConsumeHeadIdComputerCompilation.enc c).1 = [true] := by
  simp [ConsumeHeadIdComputerCompilation.enc, hl]

/-- After one `idComputer` step the label is halting (`none`), matching consume-head state `1`. -/
theorem consume_head_idComputer_step_halts (c : FinTM2.Cfg consumeHeadFinTMAnchor) (hl : c.l = some ()) :
    consumeHeadFinTMAnchor.step c = some { c with l := none } :=
  IdComputerCompilation.step_active c hl

/-- Consume-head Fin 2 scaffold: one microstep reaches the halting encoding. -/
theorem consume_head_fin2_reaches_halt :
    cookConsumeHeadTMComp.eval_with_idx 0 1 = cookConsumeHeadTMComp.enc 1 :=
  cook_consume_head_eval_reaches_halt

/-- Stage 4: consume-head `Fin 2` machine compiles to CTS (empty appendant). -/
theorem consume_head_stage4_compiles : TMCompilesStep tmConsumeHeadStep cookConsumeHeadTMComp :=
  cook_consume_head_tm_compiles_step

/-- Stage 4: Mathlib `FinTM2` identity machine compiles (two-appendant encoding). -/
theorem consume_head_fintm2_anchor_compiles : CookFinTM2Compiles consumeHeadFinTMAnchor :=
  cook_idComputer_fin_tm2_compiles

end Rule110
