import Rule110.CookC2BoundedSim

set_option maxRecDepth 100000 in

/-!
# C2 readback verification at word length L = 5 (Stage 1b extension probe)

Isolated check before bumping global `c2VerifyMaxLen` from 4 to 5.
-/

namespace Rule110

def c2Len5WordReadOk (slot n : ℕ) : Bool :=
  if _ : slot < 5 then
    if _ : n < 2^5 then
      decide (c2SimReadAt slot (natToWord 5 n) = (natToWord 5 n).getD slot false)
    else true
  else true

def c2Len5AllWordsOk : Bool :=
  (List.range 5).all fun slot =>
    (List.range (2^5)).all fun n => c2Len5WordReadOk slot n

theorem c2_len5_all_words_ok : c2Len5AllWordsOk = true := by
  native_decide

end Rule110
