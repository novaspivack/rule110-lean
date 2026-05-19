import Rule110.CookC2BoundedSim
import Rule110.CTStoRule110

/-!
# Stage 1 Cook bridge verification

* **`cook_cts_step_sim_ax`** — discharged in `CTStoRule110` (far-field ether drift).
* **`cook_c2_tape_bit_sim_witness`** — bounded simulator check in `CookC2BoundedSim` (slots 0–20).
* **`cook_c2_tape_bit_ax`** — InfTape-level decode remains an explicit axiom (Stage 1b link).
-/

namespace Rule110

theorem cook_c2_tape_bit_sim_witness (slot : ℕ) (bit : Bool) (hslot : slot ≤ 20) :
    c2SimRead slot bit = bit :=
  cts_min_word_sim_read slot bit hslot

end Rule110
