import Rule110.CookC2BoundedSim

set_option maxRecDepth 100000 in

/-!
# C2 readback verification at word length L = 7 (Stage 1b extension probe)

Isolated check before extending partial InfTape C1 discharge beyond L = 6.
-/

namespace Rule110

def c2Len7WordReadOk (slot n : ℕ) : Bool :=
  if _ : slot < 7 then
    if _ : n < 2^7 then
      decide (c2SimReadAt slot (natToWord 7 n) = (natToWord 7 n).getD slot false)
    else true
  else true

def c2Len7AllWordsOk : Bool :=
  (List.range 7).all fun slot =>
    (List.range (2^7)).all fun n => c2Len7WordReadOk slot n

theorem c2_len7_all_words_ok : c2Len7AllWordsOk = true := by
  native_decide

theorem c2_len7_word_read_ok (slot n : ℕ) (hslot : slot < 7) (hn : n < 2^7) :
    c2SimReadAt slot (natToWord 7 n) = (natToWord 7 n).getD slot false := by
  have hn128 : n < 128 := by
    have hpow : 2^7 = 128 := by decide
    simpa [hpow] using hn
  have hslot_all : ((List.range 7).all fun slot =>
      ((List.range (2^7)).all fun n => c2Len7WordReadOk slot n)) = true := by
    simpa [c2Len7AllWordsOk] using c2_len7_all_words_ok
  have h1 := (List.all_eq_true.mp hslot_all) slot (List.mem_range.mpr hslot)
  have h2 := (List.all_eq_true.mp h1) n (List.mem_range.mpr hn128)
  exact (decide_eq_true_iff).1 (by simpa [c2Len7WordReadOk, hslot, hn, hn128, reduceIte] using h2)

end Rule110
