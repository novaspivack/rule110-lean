import Mathlib.Tactic.IntervalCases

import Rule110.CookGliderVerification
import Rule110.CTStoRule110

namespace Rule110

set_option maxRecDepth 100000

def c2SimBound : ℕ := 2500

def c2SimOrigin (slot : ℕ) : ℕ :=
  cts_tape_origin + slot * cts_glider_spacing

/-- Cell value for general word `w`: C2 patch at each `1`-bit slot, else ether. -/
def c2SimCellForWord (w : List Bool) (i : ℕ) : Bool :=
  match (List.range w.length).find? fun slot =>
      w.getD slot false &&
        c2SimOrigin slot ≤ i && i - c2SimOrigin slot < 6 with
  | none => cookEther i
  | some slot => cookC2Bits.getD (i - c2SimOrigin slot) false

def c2SimInitWord (w : List Bool) : List Bool :=
  (List.range c2SimBound).map (c2SimCellForWord w)

def c2SimInit (slot : ℕ) (bit : Bool) : List Bool :=
  c2SimInitWord (List.replicate slot false ++ [bit])

def c2SimLeft (tape : List Bool) (i : ℕ) : Bool :=
  if i = 0 then false else tape.getD (i - 1) false

def c2SimRight (tape : List Bool) (i : ℕ) : Bool :=
  if i + 1 < tape.length then tape.getD (i + 1) false else cookEther (i + 1)

def c2SimStep (tape : List Bool) : List Bool :=
  (List.range tape.length).map fun i =>
    rule110Output (neighborhoodIndex (c2SimLeft tape i) (tape.getD i false) (c2SimRight tape i))

def c2SimRun : ℕ → List Bool → List Bool
  | 0, tape => tape
  | n + 1, tape => c2SimRun n (c2SimStep tape)

def c2SimReadAt (slot : ℕ) (w : List Bool) : Bool :=
  let origin := c2SimOrigin slot
  let tape := c2SimRun 30 (c2SimInitWord w)
  tape.getD origin false ≠ cookEther origin

def c2SimRead (slot : ℕ) (bit : Bool) : Bool :=
  c2SimReadAt slot (List.replicate slot false ++ [bit])

@[simp] theorem c2SimInitWord_length (w : List Bool) :
    (c2SimInitWord w).length = c2SimBound := by
  simp [c2SimInitWord, List.length_map, List.length_range]

@[simp] theorem c2SimInit_length (slot : ℕ) (bit : Bool) :
    (c2SimInit slot bit).length = c2SimBound := by
  simp [c2SimInit, c2SimInitWord_length]

/-! ### Exhaustive readback checker (words of length `≤ c2VerifyMaxLen`) -/

def c2VerifyMaxLen : ℕ := 5

def natToWord (L n : ℕ) : List Bool :=
  (List.range L).map fun i => decide (((n / 2^i) % 2) = 1)

def c2WordReadOk (L slot n : ℕ) : Bool :=
  if _ : slot < L then
    decide (c2SimReadAt slot (natToWord L n) = (natToWord L n).getD slot false)
  else
    true

def c2AllWordsOkAtLen (L slot : ℕ) : Bool :=
  if _ : L ≤ c2VerifyMaxLen then
    (List.range (2^L)).all fun n => c2WordReadOk L slot n
  else
    true

def c2AllWordsOkAtSlot (slot : ℕ) : Bool :=
  if _ : slot ≤ c2VerifyMaxLen then
    (List.range (c2VerifyMaxLen + 1)).all fun L => c2AllWordsOkAtLen L slot
  else
    true

def c2AllWordsOk : Bool :=
  (List.range (c2VerifyMaxLen + 1)).all c2AllWordsOkAtSlot

theorem c2_all_words_read_ok : c2AllWordsOk = true := by native_decide

/-- Initial tape agrees with `cts_to_rule110_tape` on the 30-step cone at `slot`. -/
def c2ConeCellOk (L n slot k : ℕ) : Bool :=
  if _ : L ≤ c2VerifyMaxLen then
    if _ : slot ≤ c2VerifyMaxLen then
      if _ : n < 2^L then
        let w := natToWord L n
        let lo := c2SimOrigin slot - 30
        let hi := c2SimOrigin slot + 30
        if _ : lo ≤ k ∧ k ≤ hi then
          decide ((c2SimInitWord w).getD k false =
            cts_to_rule110_tape (CyclicTagSystem.mk []) 0 w k)
        else
          true
      else
        true
    else
      true
  else
    true

def c2ConeAllOk : Bool :=
  (List.range (c2VerifyMaxLen + 1)).all fun L =>
    (List.range (2^L)).all fun n =>
      (List.range (c2VerifyMaxLen + 1)).all fun slot =>
        (List.range 61).all fun d =>
          c2ConeCellOk L n slot (c2SimOrigin slot - 30 + d)

theorem c2_cone_all_ok : c2ConeAllOk = true := by native_decide

/-! Fast witnesses (slot 0–20). -/

theorem c2_min_word_read_0 (bit : Bool) : c2SimRead 0 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_1 (bit : Bool) : c2SimRead 1 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_2 (bit : Bool) : c2SimRead 2 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_3 (bit : Bool) : c2SimRead 3 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_4 (bit : Bool) : c2SimRead 4 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_5 (bit : Bool) : c2SimRead 5 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_6 (bit : Bool) : c2SimRead 6 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_7 (bit : Bool) : c2SimRead 7 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_8 (bit : Bool) : c2SimRead 8 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_9 (bit : Bool) : c2SimRead 9 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_10 (bit : Bool) : c2SimRead 10 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_11 (bit : Bool) : c2SimRead 11 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_12 (bit : Bool) : c2SimRead 12 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_13 (bit : Bool) : c2SimRead 13 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_14 (bit : Bool) : c2SimRead 14 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_15 (bit : Bool) : c2SimRead 15 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_16 (bit : Bool) : c2SimRead 16 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_17 (bit : Bool) : c2SimRead 17 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_18 (bit : Bool) : c2SimRead 18 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_19 (bit : Bool) : c2SimRead 19 bit = bit := by cases bit <;> native_decide
theorem c2_min_word_read_20 (bit : Bool) : c2SimRead 20 bit = bit := by cases bit <;> native_decide

theorem cts_min_word_sim_read (slot : ℕ) (bit : Bool) (h : slot ≤ 20) :
    c2SimRead slot bit = bit := by
  interval_cases slot
  · exact c2_min_word_read_0 bit
  · exact c2_min_word_read_1 bit
  · exact c2_min_word_read_2 bit
  · exact c2_min_word_read_3 bit
  · exact c2_min_word_read_4 bit
  · exact c2_min_word_read_5 bit
  · exact c2_min_word_read_6 bit
  · exact c2_min_word_read_7 bit
  · exact c2_min_word_read_8 bit
  · exact c2_min_word_read_9 bit
  · exact c2_min_word_read_10 bit
  · exact c2_min_word_read_11 bit
  · exact c2_min_word_read_12 bit
  · exact c2_min_word_read_13 bit
  · exact c2_min_word_read_14 bit
  · exact c2_min_word_read_15 bit
  · exact c2_min_word_read_16 bit
  · exact c2_min_word_read_17 bit
  · exact c2_min_word_read_18 bit
  · exact c2_min_word_read_19 bit
  · exact c2_min_word_read_20 bit

end Rule110
