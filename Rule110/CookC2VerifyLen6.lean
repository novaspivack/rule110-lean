import Rule110.CookC2BoundedSim

set_option maxRecDepth 100000 in

/-!
# C2 readback verification at word length L = 6 (Stage 1b extension probe)

Isolated check before bumping global `c2VerifyMaxLen` from 5 to 6.
-/

namespace Rule110

def c2Len6WordReadOk (slot n : ℕ) : Bool :=
  if _ : slot < 6 then
    if _ : n < 2^6 then
      decide (c2SimReadAt slot (natToWord 6 n) = (natToWord 6 n).getD slot false)
    else true
  else true

def c2Len6AllWordsOk : Bool :=
  (List.range 6).all fun slot =>
    (List.range (2^6)).all fun n => c2Len6WordReadOk slot n

theorem c2_len6_all_words_ok : c2Len6AllWordsOk = true := by
  native_decide

theorem c2_len6_word_read_ok (slot n : ℕ) (hslot : slot < 6) (hn : n < 2^6) :
    c2SimReadAt slot (natToWord 6 n) = (natToWord 6 n).getD slot false := by
  have hn64 : n < 64 := by
    have hpow : 2^6 = 64 := by decide
    simpa [hpow] using hn
  have hslot_all : ((List.range 6).all fun slot =>
      ((List.range (2^6)).all fun n => c2Len6WordReadOk slot n)) = true := by
    simpa [c2Len6AllWordsOk] using c2_len6_all_words_ok
  have h1 := (List.all_eq_true.mp hslot_all) slot (List.mem_range.mpr hslot)
  have h2 := (List.all_eq_true.mp h1) n (List.mem_range.mpr hn64)
  exact (decide_eq_true_iff).1 (by simpa [c2Len6WordReadOk, hslot, hn, hn64, reduceIte] using h2)

end Rule110
