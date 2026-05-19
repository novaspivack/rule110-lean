import Rule110.CyclicTagSystem

/-!
# Turing machines → cyclic tag systems (Cook §2 — Milestone 4)

The classical Cook reduction expands any TM configuration into a CTS word plus cycling appendant index,
then proves that **micro-steps** of the CTS mirror TM transitions.

Mathlib’s formal TM toolbox (`Mathlib.Computability.TuringMachine`, especially `Turing.TM2`) is the natural
source model once we pin alphabet encodings.

This milestone file records the **target correctness shape** without fixing Cook’s encoding witnesses yet.
-/

namespace Rule110

open CyclicTagSystem

variable {Cfg : Type}

/-- Data specifying that `sys` simulates `tmStep` under `(enc, dec)`. -/
structure TMCTSCompilation (tmStep : Cfg → Option Cfg) where
  sys : CyclicTagSystem
  enc : Cfg → List Bool × ℕ
  dec : List Bool × ℕ → Cfg
  decode_roundtrip : ∀ c : Cfg, dec (enc c) = c
  /-- For every successful TM transition there exists a finite CTS trace whose decoded snapshot matches
      the successor configuration. -/
  simulates_step :
    ∀ {c c' : Cfg},
      tmStep c = some c' →
        ∃ m : ℕ,
          let (w, idx) := enc c
          let (w', idx') := cts_steps sys m w idx
          dec (w', idx') = c'

/-- Encoded configuration after `m` CTS microsteps (word + appendant index). -/
def TMCTSCompilation.eval_with_idx {Cfg : Type} {tmStep : Cfg → Option Cfg}
    (comp : TMCTSCompilation tmStep) (c : Cfg) (m : ℕ) : List Bool × ℕ :=
  let (w, idx) := comp.enc c
  comp.sys.cts_eval_with_idx m w idx

/-- Extracted word component of `eval_with_idx`. -/
def TMCTSCompilation.eval_word {Cfg : Type} {tmStep : Cfg → Option Cfg}
    (comp : TMCTSCompilation tmStep) (c : Cfg) (m : ℕ) : List Bool :=
  (comp.eval_with_idx c m).1

/-- Zero CTS microsteps leave the encoded configuration unchanged. -/
theorem TMCTSCompilation.eval_with_idx_zero {Cfg : Type} {tmStep : Cfg → Option Cfg}
    (comp : TMCTSCompilation tmStep) (c : Cfg) :
    comp.eval_with_idx c 0 = comp.enc c := by
  simp [TMCTSCompilation.eval_with_idx, cts_eval_with_idx_zero]

theorem TMCTSCompilation.eval_word_zero {Cfg : Type} {tmStep : Cfg → Option Cfg}
    (comp : TMCTSCompilation tmStep) (c : Cfg) :
    comp.eval_word c 0 = (comp.enc c).1 := by
  simp [TMCTSCompilation.eval_word, TMCTSCompilation.eval_with_idx_zero]

end Rule110
