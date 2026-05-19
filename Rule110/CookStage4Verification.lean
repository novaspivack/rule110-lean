import Rule110.CookTMCompilation
import Rule110.TMtoCTS

/-!
# Stage 4 TM → CTS verification witnesses
-/

namespace Rule110

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

end Rule110
