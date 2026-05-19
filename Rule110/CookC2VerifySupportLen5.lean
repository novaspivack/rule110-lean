import Rule110.CookC2BoundedSim
import Rule110.OssifierGlider

set_option maxRecDepth 100000 in

/-!
# C2 readback with ossifier support overlay (L ≤ 5 list sim)

Leader glider (origin 8000) lies outside `c2SimBound = 2500`; only the left ossifier
patch is overlaid in the bounded list simulator. Exhaustive `native_decide` check for
L = 5 `natToWord` family.
-/

namespace Rule110

def c2SimCellForWordWithOssifier (w : List Bool) (i : ℕ) : Bool :=
  if cts_ossifier_origin ≤ i ∧ i < cts_ossifier_origin + cookOssifierPatchBits.length then
    cookOssifierPatchBits.getD (i - cts_ossifier_origin) false
  else
    c2SimCellForWord w i

def c2SimInitWordWithOssifier (w : List Bool) : List Bool :=
  (List.range c2SimBound).map (c2SimCellForWordWithOssifier w)

def c2SimReadAtWithOssifier (slot : ℕ) (w : List Bool) : Bool :=
  let origin := c2SimOrigin slot
  let tape := c2SimRun 30 (c2SimInitWordWithOssifier w)
  tape.getD origin false ≠ cookEther origin

def c2SupportLen5WordReadOk (slot n : ℕ) : Bool :=
  if _ : slot < 5 then
    if _ : n < 2 ^ 5 then
      decide (c2SimReadAtWithOssifier slot (natToWord 5 n) = (natToWord 5 n).getD slot false)
    else true
  else true

def c2SupportLen5AllWordsOk : Bool :=
  (List.range 5).all fun slot =>
    (List.range (2 ^ 5)).all fun n => c2SupportLen5WordReadOk slot n

theorem c2_support_len5_all_words_ok : c2SupportLen5AllWordsOk = true := by
  native_decide

theorem c2_support_len5_word_read (slot n : ℕ) (hslot : slot < 5) (hn : n < 2 ^ 5) :
    c2SimReadAtWithOssifier slot (natToWord 5 n) = (natToWord 5 n).getD slot false := by
  have hn32 : n < 32 := by
    have : 2 ^ 5 = 32 := by decide
    simpa [this] using hn
  have hall : ((List.range 5).all fun slot =>
      ((List.range (2 ^ 5)).all fun n => c2SupportLen5WordReadOk slot n)) = true := by
    simpa [c2SupportLen5AllWordsOk] using c2_support_len5_all_words_ok
  have h1 := (List.all_eq_true.mp hall) slot (List.mem_range.mpr hslot)
  have h2 := (List.all_eq_true.mp h1) n (List.mem_range.mpr hn32)
  exact (decide_eq_true_iff).1 (by simpa [c2SupportLen5WordReadOk, hslot, hn, hn32, reduceIte] using h2)

end Rule110
