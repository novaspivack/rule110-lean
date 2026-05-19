import Mathlib.Computability.TuringMachine.Computable

import Rule110.TMtoCTS

/-!
# Mathlib `FinTM2` → CTS compilation (`idComputer`)

Cook's full multi-stack encoding remains future work. For Mathlib's halting identity machine
`idComputer Bool`, configurations are encoded as a word plus appendant index: a leading `true`
marks the active (non-halting) phase at index `0`, and one empty-appendant CTS microstep
consumes that marker and advances the index to `1`, matching `FinTM2.step` on `Stmt.halt`.
-/

namespace Rule110

open CyclicTagSystem
open Turing Turing.TM2

abbrev idComputerTM : FinTM2 := idComputer Bool

namespace IdComputerCompilation

abbrev IdCfg := FinTM2.Cfg idComputerTM

/-- Stack at the single input/output location. -/
def stack (c : IdCfg) : List Bool :=
  c.stk (k := idComputerTM.k₀)

/-- Active (`l = some ()`) configurations carry a leading `true` and index `0`. -/
def enc (c : IdCfg) : List Bool × ℕ :=
  match c.l with
  | some () => (true :: stack c, 0)
  | none => (stack c, 1)

/-- Index `0` reads as active; index `1` as halted with word equal to the stack. -/
def dec (p : List Bool × ℕ) : IdCfg :=
  match p with
  | (w, 0) =>
      match w with
      | true :: s => ⟨some (), (), fun _ => s⟩
      | _ => ⟨some (), (), fun _ => w⟩
  | (w, _) => ⟨none, (), fun _ => w⟩

private theorem cfg_ext {c c' : IdCfg}
    (hl : c.l = c'.l) (hv : c.var = c'.var) (hs : c.stk = c'.stk) : c = c' := by
  rcases c with ⟨l, v, S⟩
  rcases c' with ⟨l', v', S'⟩
  subst hl hv hs
  rfl

theorem decode_roundtrip (c : IdCfg) : dec (enc c) = c := by
  rcases c with ⟨l, v, S⟩
  rcases v
  cases l with
  | none =>
    apply cfg_ext <;> simp [enc, dec, stack, idComputer]
    funext k
    cases k
    rfl
  | some a =>
    cases a
    apply cfg_ext <;> simp [enc, dec, stack, idComputer]
    funext k
    cases k
    rfl

/-- `idComputer` executes `halt` in one machine step: active configs become halting. -/
theorem step_active (c : IdCfg) (hl : c.l = some ()) :
    idComputerTM.step c = some { c with l := none } := by
  rcases c with ⟨l, v, stk⟩
  rcases v
  subst hl
  simp [FinTM2.step, TM2.step, idComputer, TM2.stepAux]
  rfl

theorem step_halted (c : IdCfg) (hl : c.l = none) : idComputerTM.step c = none := by
  rcases c with ⟨l, v, stk⟩
  rcases v
  subst hl
  simp [FinTM2.step, TM2.step, idComputer]
  rfl

/-- Two empty appendants: each microstep deletes the head bit and toggles the appendant index. -/
def cts : CyclicTagSystem :=
  { appendants := [[], []] }

@[simp] theorem cts_cycleLen : cts.cycleLen = 2 := rfl

theorem cts_step_running (s : List Bool) :
    cts.cts_step 0 (true :: s) = (s, 1) := by
  simp [cts, CyclicTagSystem.cts_step]

theorem cts_steps_one_running (s : List Bool) :
    cts.cts_steps 1 (true :: s) 0 = (s, 1) :=
  cts_step_running s

/-- Bundled CTS compiler for `idComputer Bool`. -/
def tmComp : TMCTSCompilation idComputerTM.step where
  sys := cts
  enc := enc
  dec := dec
  decode_roundtrip := decode_roundtrip
  simulates_step := by
    intro c c' h
    rcases c with ⟨l, v, S⟩
    rcases v
    cases l with
    | none => simp [FinTM2.step, TM2.step, idComputer, TM2.stepAux] at h
    | some _ =>
      have hc' : c' = ⟨none, (), S⟩ := (Option.some_inj.mp h).symm
      subst hc'
      refine ⟨1, ?_⟩
      change dec (cts.cts_steps 1 (true :: S PUnit.unit) 0) = ⟨none, (), S⟩
      simp only [cts_steps_one_running, dec]
      apply cfg_ext <;> rfl

theorem tm_compiles_step : TMCompilesStep idComputerTM.step tmComp :=
  tmComp.tm_compiles_step

end IdComputerCompilation

theorem idComputer_fin_tm2_compiles_witness :
    ∃ (comp : TMCTSCompilation (idComputer Bool).step),
      TMCompilesStep (idComputer Bool).step comp :=
  ⟨IdComputerCompilation.tmComp, IdComputerCompilation.tm_compiles_step⟩

end Rule110
