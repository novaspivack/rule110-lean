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

theorem cook_consume_head_eval_with_idx_add (m n : ℕ) :
    cookConsumeHeadTMComp.eval_with_idx 0 (m + n) =
      let (w', idx') := cookConsumeHeadTMComp.eval_with_idx 0 m
      cookConsumeHeadTMComp.sys.cts_eval_with_idx n w' idx' :=
  cookConsumeHeadTMComp.eval_with_idx_add 0 m n

/-- One TM microstep from state `0` reaches the halting encoding for state `1`. -/
theorem cook_consume_head_eval_reaches_halt :
    cookConsumeHeadTMComp.eval_with_idx 0 1 = cookConsumeHeadTMComp.enc 1 := by
  rw [cook_consume_head_eval_with_idx_one]
  simp [cookConsumeHeadTMComp]

theorem cook_consume_head_dec_after_one_step :
    cookConsumeHeadTMComp.dec (cookConsumeHeadTMComp.eval_with_idx 0 1) = 1 := by
  rw [cook_consume_head_eval_with_idx_one]
  simp [cookConsumeHeadTMComp]

theorem cook_consume_head_tm_compiles_step :
    TMCompilesStep tmConsumeHeadStep cookConsumeHeadTMComp :=
  cookConsumeHeadTMComp.tm_compiles_step

/-! ### Three-state countdown TM (multi-step consume on standard empty CTS) -/

/-- Three-state machine: `0 → 1 → 2 → halt`. -/
def tmCountDownStep (s : Fin 3) : Option (Fin 3) :=
  match s with
  | 0 => some 1
  | 1 => some 2
  | 2 => none

private def countDownEnc (s : Fin 3) : List Bool × ℕ :=
  match s with
  | 0 => ([true, true], 0)
  | 1 => ([true], 0)
  | 2 => ([], 0)

private def countDownDec (w : List Bool) (_ : ℕ) : Fin 3 :=
  match w with
  | [] => 2
  | [_] => 1
  | _ => 0

/-- Unary-length encoding: state `k` carries `2 - k` head `true` bits before halting. -/
def cookCountDownTMComp : TMCTSCompilation tmCountDownStep where
  sys := cook_standard_empty_cts
  enc := countDownEnc
  dec := fun p => countDownDec p.1 p.2
  decode_roundtrip := by
    intro s
    fin_cases s <;> simp [countDownEnc, countDownDec]
  simulates_step := by
    intro s s' h
    fin_cases s
    · simp [tmCountDownStep] at h
      subst h
      refine ⟨1, ?_⟩
      simp [countDownEnc, countDownDec, cook_standard_empty_cts_steps_one_true_pair]
    · simp [tmCountDownStep] at h
      subst h
      refine ⟨1, ?_⟩
      simp [countDownEnc, countDownDec, cook_standard_empty_cts_steps_one_true]
    · simp [tmCountDownStep] at h

theorem cook_count_down_simulates_step (s s' : Fin 3) (h : tmCountDownStep s = some s') :
    ∃ m,
      let (w, idx) := cookCountDownTMComp.enc s
      let (w', idx') := cookCountDownTMComp.sys.cts_steps m w idx
      cookCountDownTMComp.dec (w', idx') = s' :=
  cookCountDownTMComp.simulates_step h

theorem cook_count_down_tm_compiles_step :
    TMCompilesStep tmCountDownStep cookCountDownTMComp :=
  cookCountDownTMComp.tm_compiles_step

theorem trivial_identity_tm_compiles_step :
    TMCompilesStep tmIdentityStep trivialIdentityTMComp :=
  trivialIdentityTMComp.tm_compiles_step

theorem trivial_identity_eval_with_idx_add (c : Unit) (m n : ℕ) :
    trivialIdentityTMComp.eval_with_idx c (m + n) =
      let (w', idx') := trivialIdentityTMComp.eval_with_idx c m
      trivialIdentityTMComp.sys.cts_eval_with_idx n w' idx' :=
  trivialIdentityTMComp.eval_with_idx_add c m n

end Rule110
