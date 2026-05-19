import Mathlib.Tactic.IntervalCases

import Rule110.CookGliderVerification
import Rule110.CTStoRule110

namespace Rule110

def c2SimBound : ℕ := 2500

def c2SimOrigin (slot : ℕ) : ℕ :=
  cts_tape_origin + slot * cts_glider_spacing

def c2SimInit (slot : ℕ) (bit : Bool) : List Bool :=
  let origin := c2SimOrigin slot
  (List.range c2SimBound).map fun i =>
    if bit ∧ origin ≤ i ∧ i - origin < 6 then
      cookC2Bits.getD (i - origin) false
    else
      cookEther i

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

def c2SimRead (slot : ℕ) (bit : Bool) : Bool :=
  let origin := c2SimOrigin slot
  let tape := c2SimRun 30 (c2SimInit slot bit)
  let expected := cookEther origin
  tape.getD origin false ≠ expected

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
