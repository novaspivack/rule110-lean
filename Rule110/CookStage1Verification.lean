import Rule110.CookC2BoundedSim
import Rule110.CookC2InfTapeBridge
import Rule110.CookC2VerifySupportLen5
import Rule110.CookC2VerifySupportLen6
import Rule110.CookC2VerifySupportLen7
import Rule110.CookC2SupportBareEquiv
import Rule110.CTStoRule110

/-!
# Stage 1 Cook bridge verification

* **`cook_cts_step_sim_ax`** — discharged in `CTStoRule110` (far-field ether drift).
* **`cook_c2_tape_bit_sim_witness`** — bounded list simulator (slots 0–20).
* **`cook_c2_tape_bit_min_word`** — InfTape decode for isolated min-word encoding (Stage 1b).
* **`cook_c2_tape_bit_list`** — multi-glider list sim read (word length ≤ 4).
* **`cook_c2_tape_bit_inf_nat`** — InfTape decode for bounded multi-glider words (Stage 1b).
* **`c2_init_read_cone_ok`** — init cone agreement checker (bundled, L ≤ 4).
* **`cook_c2_tape_bit_ax`** — full InfTape general-word axiom remains open.
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

theorem cook_c2_tape_bit_list_witness (L slot n : ℕ)
    (hL : L ≤ c2VerifyMaxLen) (hslot : slot < L) (hn : n < 2^L) :
    c2SimReadAt slot (natToWord L n) = (natToWord L n).getD slot false :=
  cook_c2_tape_bit_list L slot n hL hslot hn

theorem cook_c2_tape_bit_list_upto6_witness (L slot n : ℕ) (hL : L ≤ 6) (hslot : slot < L)
    (hn : n < 2^L) :
    c2SimReadAt slot (natToWord L n) = (natToWord L n).getD slot false :=
  cook_c2_tape_bit_list_upto6 L slot n hL hslot hn

theorem cook_c2_tape_bit_list_upto7_witness (L slot n : ℕ) (hL : L ≤ 7) (hslot : slot < L)
    (hn : n < 2^L) :
    c2SimReadAt slot (natToWord L n) = (natToWord L n).getD slot false :=
  cook_c2_tape_bit_list_upto7 L slot n hL hslot hn

theorem c2_init_read_cone_ok_witness (L readSlot n : ℕ)
    (hL : L ≤ c2VerifyMaxLen) (hslot : readSlot < L) (hn : n < 2^L) :
    c2InitReadConeOk L readSlot n = true :=
  c2_init_read_cone_ok L readSlot n hL hslot hn

theorem cook_c2_tape_bit_inf_nat_witness (L slot n : ℕ) (idx : ℕ)
    (hL : L ≤ c2VerifyMaxLen) (hslot : slot < L) (hn : n < 2^L) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n)))
      slot 0 =
      (natToWord L n).getD slot false :=
  cook_c2_tape_bit_inf_nat L slot n hL hslot hn idx

theorem cook_c2_tape_bit_inf_nat_upto6_witness (L slot n : ℕ) (idx : ℕ) (hL : L ≤ 6)
    (hslot : slot < L) (hn : n < 2^L) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n)))
      slot 0 =
      (natToWord L n).getD slot false :=
  cook_c2_tape_bit_inf_nat_upto6 L slot n hL hslot hn idx

theorem cook_c2_tape_bit_inf_nat_upto7_witness (L slot n : ℕ) (idx : ℕ) (hL : L ≤ 7)
    (hslot : slot < L) (hn : n < 2^L) :
    tape_has_glider_at
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n)))
      slot 0 =
      (natToWord L n).getD slot false :=
  cook_c2_tape_bit_inf_nat_upto7 L slot n hL hslot hn idx

theorem cook_c2_tape_bit_ax_partial_upto7_witness (L slot n : ℕ) (idx : ℕ) (hL : L ≤ 7)
    (hslot : slot < L) (hn : n < 2^L) :
    cook_c2_decode_at slot
      (infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n))) =
      (natToWord L n).getD slot false :=
  cook_c2_tape_bit_ax_partial_upto7 L slot n hL hslot hn idx

theorem c2_support_len5_word_read_witness (slot n : ℕ) (hslot : slot < 5) (hn : n < 2 ^ 5) :
    c2SimReadAtWithOssifier slot (natToWord 5 n) = (natToWord 5 n).getD slot false :=
  c2_support_len5_word_read slot n hslot hn

theorem c2_support_len6_word_read_witness (slot n : ℕ) (hslot : slot < 6) (hn : n < 2 ^ 6) :
    c2SimReadAtWithOssifier slot (natToWord 6 n) = (natToWord 6 n).getD slot false :=
  c2_support_len6_word_read slot n hslot hn

theorem c2_support_len7_word_read_witness (slot n : ℕ) (hslot : slot < 7) (hn : n < 2 ^ 7) :
    c2SimReadAtWithOssifier slot (natToWord 7 n) = (natToWord 7 n).getD slot false :=
  c2_support_len7_word_read slot n hslot hn

theorem c2_support_word_read_from_bare_witness (L slot n : ℕ) (hL : L ≤ 7) (hslot : slot < L)
    (hn : n < 2 ^ L) :
    c2SimReadAtWithOssifier slot (natToWord L n) = (natToWord L n).getD slot false :=
  c2_support_word_read_from_bare L slot n hL hslot hn

theorem c2_support_len7_word_read_from_bare_witness (slot n : ℕ) (hslot : slot < 7) (hn : n < 2 ^ 7) :
    c2SimReadAtWithOssifier slot (natToWord 7 n) = (natToWord 7 n).getD slot false :=
  c2_support_len7_word_read_from_bare slot n hslot hn

theorem c2_len6_all_init_read_cones_ok_witness :
    c2Len6AllInitReadConesOk = true :=
  c2_len6_all_init_read_cones_ok

theorem c2_len7_all_words_ok_witness : c2Len7AllWordsOk = true :=
  c2_len7_all_words_ok

theorem c2_len7_all_init_read_cones_ok_witness :
    c2Len7AllInitReadConesOk = true :=
  c2_len7_all_init_read_cones_ok

end Rule110
