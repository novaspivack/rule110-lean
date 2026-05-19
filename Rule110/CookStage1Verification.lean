import Rule110.CookC2BoundedSim
import Rule110.CookC2InfTapeBridge
import Rule110.CTStoRule110

/-!
# Stage 1 Cook bridge verification

* **`cook_cts_step_sim_ax`** — discharged in `CTStoRule110` (far-field ether drift).
* **`cook_c2_tape_bit_sim_witness`** — bounded list simulator (slots 0–20).
* **`cook_c2_tape_bit_min_word`** — InfTape decode for isolated min-word encoding (Stage 1b).
* **`cook_c2_tape_bit_ax`** — full general-word axiom remains open.
-/

namespace Rule110

theorem cook_c2_tape_bit_sim_witness (slot : ℕ) (bit : Bool) (hslot : slot ≤ 20) :
    c2SimRead slot bit = bit :=
  cts_min_word_sim_read slot bit hslot

theorem cook_c2_tape_bit_min_word_witness (slot : ℕ) (bit : Bool) (hslot : slot ≤ 20) (idx : ℕ) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (cts_min_word slot bit)))
      slot 0 = bit :=
  cook_c2_tape_bit_min_word slot bit hslot idx

end Rule110
