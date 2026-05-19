import Rule110.TMtoCTS
import Rule110.CTStoRule110

/-!
# TM → CTS compilation witnesses (Stage 4 scaffold)

Cook's full TM encoding remains open. This module records a **zero-cost identity**
compilation showing the `TMCTSCompilation.simulates_step` target is satisfiable and
compatible with `eval_with_idx` lemmas already in `TMtoCTS.lean`.
-/

namespace Rule110

open CyclicTagSystem

/-- Identity step on `Unit`: always succeeds with the same configuration. -/
def tmIdentityStep (_c : Unit) : Option Unit :=
  some ()

/-- Standard empty appendant CTS; encoded configuration is always `([], 0)`. -/
def trivialIdentityTMComp : TMCTSCompilation tmIdentityStep where
  sys := cook_standard_empty_cts
  enc := fun _ => ([], 0)
  dec := fun _ => ()
  decode_roundtrip := fun _ => rfl
  simulates_step := fun h => by
    rcases Option.some.inj h with rfl
    exact ⟨0, rfl⟩

theorem trivial_identity_tm_simulates_step (c c' : Unit) (h : tmIdentityStep c = some c') :
    ∃ m,
      let (w, idx) := trivialIdentityTMComp.enc c
      let (w', idx') := trivialIdentityTMComp.sys.cts_steps m w idx
      trivialIdentityTMComp.dec (w', idx') = c' :=
  trivialIdentityTMComp.simulates_step h

/-- One CTS microstep on the trivial encoding matches `eval_with_idx` at `m = 1`. -/
theorem trivial_identity_eval_with_idx_one (c : Unit) :
    trivialIdentityTMComp.eval_with_idx c 1 =
      trivialIdentityTMComp.sys.cts_eval_with_idx 1 [] 0 := by
  simp [TMCTSCompilation.eval_with_idx_one, trivialIdentityTMComp]

end Rule110
