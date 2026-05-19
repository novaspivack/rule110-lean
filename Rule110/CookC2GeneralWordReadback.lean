import Rule110.CookC2WordNat
import Rule110.CookC2VerifySupportLen5
import Rule110.CookC2VerifySupportLen6
import Rule110.CookC2VerifySupportLen7

/-!
# C2 ossifier readback for `natToWord` encodings at each length `L ≤ 7`

Arbitrary `List Bool` readback reduces to this family once
`natToWord L (word_toNatLE w) = w` is available (analytical surjection; blocked at `L = 7`
for a universal `native_decide` sweep).
-/

namespace Rule110

/-- Ossifier list-sim readback for `natToWord L n` at `L = 5`. -/
theorem c2_support_nat_word_read_len5 (slot n : ℕ) (hslot : slot < 5) (hn : n < 2 ^ 5) :
    c2SimReadAtWithOssifier slot (natToWord 5 n) = (natToWord 5 n).getD slot false :=
  c2_support_len5_word_read slot n hslot hn

theorem c2_support_nat_word_read_len6 (slot n : ℕ) (hslot : slot < 6) (hn : n < 2 ^ 6) :
    c2SimReadAtWithOssifier slot (natToWord 6 n) = (natToWord 6 n).getD slot false :=
  c2_support_len6_word_read slot n hslot hn

theorem c2_support_nat_word_read_len7 (slot n : ℕ) (hslot : slot < 7) (hn : n < 2 ^ 7) :
    c2SimReadAtWithOssifier slot (natToWord 7 n) = (natToWord 7 n).getD slot false :=
  c2_support_len7_word_read slot n hslot hn

/-- Dispatch ossifier readback on `natToWord L n` by word length (`L ∈ {5,6,7}`). -/
theorem c2_support_nat_word_read_upto7 (L slot n : ℕ) (hL : 5 ≤ L ∧ L ≤ 7) (hslot : slot < L)
    (hn : n < 2 ^ L) :
    c2SimReadAtWithOssifier slot (natToWord L n) = (natToWord L n).getD slot false := by
  rcases hL with ⟨hL5, hL7⟩
  interval_cases L
  · exact c2_support_nat_word_read_len5 slot n hslot hn
  · exact c2_support_nat_word_read_len6 slot n hslot hn
  · exact c2_support_nat_word_read_len7 slot n hslot hn

end Rule110
