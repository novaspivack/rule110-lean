import Rule110.CookC2VerifySupportLen5

set_option maxRecDepth 100000 in

/-!
# C2 readback with ossifier support overlay (L ≤ 6 list sim)

Extends `CookC2VerifySupportLen5` to L = 6 before global `c2VerifyMaxLen` bump.
Leader glider remains outside `c2SimBound`.
-/

namespace Rule110

def c2SupportLen6WordReadOk (slot n : ℕ) : Bool :=
  if _ : slot < 6 then
    if _ : n < 2 ^ 6 then
      decide (c2SimReadAtWithOssifier slot (natToWord 6 n) = (natToWord 6 n).getD slot false)
    else true
  else true

def c2SupportLen6AllWordsOk : Bool :=
  (List.range 6).all fun slot =>
    (List.range (2 ^ 6)).all fun n => c2SupportLen6WordReadOk slot n

theorem c2_support_len6_all_words_ok : c2SupportLen6AllWordsOk = true := by
  native_decide

theorem c2_support_len6_word_read (slot n : ℕ) (hslot : slot < 6) (hn : n < 2 ^ 6) :
    c2SimReadAtWithOssifier slot (natToWord 6 n) = (natToWord 6 n).getD slot false := by
  have hn64 : n < 64 := by
    have : 2 ^ 6 = 64 := by decide
    simpa [this] using hn
  have hall : ((List.range 6).all fun slot =>
      ((List.range (2 ^ 6)).all fun n => c2SupportLen6WordReadOk slot n)) = true := by
    simpa [c2SupportLen6AllWordsOk] using c2_support_len6_all_words_ok
  have h1 := (List.all_eq_true.mp hall) slot (List.mem_range.mpr hslot)
  have h2 := (List.all_eq_true.mp h1) n (List.mem_range.mpr hn64)
  exact (decide_eq_true_iff).1 (by simpa [c2SupportLen6WordReadOk, hslot, hn, hn64, reduceIte] using h2)

end Rule110
