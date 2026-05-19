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

/-! ### Consume-head two-state TM (non-identity Stage 4 witness) -/

/-- Two-state machine: state `0` consumes the encoded head bit and halts in state `1`. -/
def tmConsumeHeadStep (s : Fin 2) : Option (Fin 2) :=
  match s with
  | 0 => some 1
  | 1 => none

/-- Encode state `0` as `[true]` on the standard empty CTS; halting state `1` as `[]`. -/
def cookConsumeHeadTMComp : TMCTSCompilation tmConsumeHeadStep where
  sys := cook_standard_empty_cts
  enc s := if s = 0 then ([true], 0) else ([], 0)
  dec := fun (w, _) => if w = [] then (1 : Fin 2) else 0
  decode_roundtrip := by
    intro s
    fin_cases s <;> simp
  simulates_step := by
    intro s s' h
    fin_cases s
    · simp [tmConsumeHeadStep] at h
      subst h
      refine ⟨1, ?_⟩
      simp [cook_standard_empty_cts_steps_one_true]
    · simp [tmConsumeHeadStep] at h

theorem cook_consume_head_simulates_step (s s' : Fin 2) (h : tmConsumeHeadStep s = some s') :
    ∃ m,
      let (w, idx) := cookConsumeHeadTMComp.enc s
      let (w', idx') := cookConsumeHeadTMComp.sys.cts_steps m w idx
      cookConsumeHeadTMComp.dec (w', idx') = s' :=
  cookConsumeHeadTMComp.simulates_step h

theorem cook_consume_head_eval_with_idx_one :
    cookConsumeHeadTMComp.eval_with_idx 0 1 = ([], 0) := by
  unfold TMCTSCompilation.eval_with_idx
  simp [cookConsumeHeadTMComp, TMCTSCompilation.eval_with_idx_one,
    cook_standard_empty_cts_eval_with_idx_one_true]

end Rule110
