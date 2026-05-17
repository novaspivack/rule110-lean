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

end Rule110
