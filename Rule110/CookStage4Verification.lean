import Rule110.CookTMCompilation
import Rule110.CookTM2Bridge
import Rule110.TMtoCTS

/-!
# Stage 4 TM → CTS verification witnesses
-/

namespace Rule110

open Turing

theorem tm_identity_step_witness (c : Unit) :
    tmIdentityStep c = some c :=
  rfl

theorem trivial_identity_tm_comp_witness :
    trivialIdentityTMComp.sys = cook_standard_empty_cts := rfl

theorem trivial_identity_simulates_step_witness (c c' : Unit)
    (h : tmIdentityStep c = some c') :
    ∃ m,
      let (w, idx) := trivialIdentityTMComp.enc c
      let (w', idx') := trivialIdentityTMComp.sys.cts_steps m w idx
      trivialIdentityTMComp.dec (w', idx') = c' :=
  trivialIdentityTMComp.simulates_step h

theorem trivial_identity_eval_with_idx_zero_witness (c : Unit) :
    trivialIdentityTMComp.eval_with_idx c 0 = trivialIdentityTMComp.enc c :=
  trivialIdentityTMComp.eval_with_idx_zero c

theorem trivial_identity_eval_with_idx_add_witness (c : Unit) (m n : ℕ) :
    trivialIdentityTMComp.eval_with_idx c (m + n) =
      let (w', idx') := trivialIdentityTMComp.eval_with_idx c m
      trivialIdentityTMComp.sys.cts_eval_with_idx n w' idx' :=
  trivialIdentityTMComp.eval_with_idx_add c m n

theorem cook_fin_tm2_id_machine_witness : Nonempty Turing.FinTM2 :=
  cook_fin_tm2_id_machine

theorem cook_bool_identity_simulates_step_witness (b b' : Bool)
    (h : tmBoolIdentityStep b = some b') :
    ∃ m,
      let (w, idx) := cookBoolIdentityTMComp.enc b
      let (w', idx') := cookBoolIdentityTMComp.sys.cts_steps m w idx
      cookBoolIdentityTMComp.dec (w', idx') = b' :=
  cook_bool_identity_simulates_step b b' h

theorem cook_bool_identity_eval_with_idx_add_witness (b : Bool) (m n : ℕ) :
    cookBoolIdentityTMComp.eval_with_idx b (m + n) =
      let (w', idx') := cookBoolIdentityTMComp.eval_with_idx b m
      cookBoolIdentityTMComp.sys.cts_eval_with_idx n w' idx' :=
  cook_bool_identity_eval_with_idx_add b m n

theorem cook_consume_head_simulates_step_witness (s s' : Fin 2)
    (h : tmConsumeHeadStep s = some s') :
    ∃ m,
      let (w, idx) := cookConsumeHeadTMComp.enc s
      let (w', idx') := cookConsumeHeadTMComp.sys.cts_steps m w idx
      cookConsumeHeadTMComp.dec (w', idx') = s' :=
  cook_consume_head_simulates_step s s' h

theorem cook_consume_head_eval_with_idx_one_witness :
    cookConsumeHeadTMComp.eval_with_idx 0 1 = ([], 0) :=
  cook_consume_head_eval_with_idx_one

theorem cook_consume_head_eval_with_idx_add_witness (m n : ℕ) :
    cookConsumeHeadTMComp.eval_with_idx 0 (m + n) =
      let (w', idx') := cookConsumeHeadTMComp.eval_with_idx 0 m
      cookConsumeHeadTMComp.sys.cts_eval_with_idx n w' idx' :=
  cook_consume_head_eval_with_idx_add m n

theorem cook_consume_head_eval_reaches_halt_witness :
    cookConsumeHeadTMComp.eval_with_idx 0 1 = cookConsumeHeadTMComp.enc 1 :=
  cook_consume_head_eval_reaches_halt

theorem cook_consume_head_dec_after_one_step_witness :
    cookConsumeHeadTMComp.dec (cookConsumeHeadTMComp.eval_with_idx 0 1) = 1 :=
  cook_consume_head_dec_after_one_step

end Rule110
