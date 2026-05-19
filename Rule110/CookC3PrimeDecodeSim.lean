import Rule110.CookC2InfTapeBridge
import Rule110.CookLen6AppendantSim
import Rule110.CTStoRule110

set_option maxRecDepth 100000 in

/-!
# C3′ glider-decode formulation (approach #13)

Cook reads CTS bits via **glider presence** at slot origins (`tape_has_glider_at`), not
full 61-cell cone equality against a static post-step re-encode.

Tests whether 390-step simulation from `[true]` + support decodes to the post-step
appendant word at each slot origin.
-/

namespace Rule110

def listTapeHasGliderAt (tape : List Bool) (slot : ℕ) : Bool :=
  listReadDiff tape (c2SimOrigin slot)

def len6OneStepGliderDecodeOk : Bool :=
  let init := len6TruePhasedSupportInit
  let fin := c2SimRun 390 init
  let w := cook_min_len6_appendant
  (List.range w.length).all fun slot =>
    decide (listTapeHasGliderAt fin slot = w.getD slot false)

/-- Slot-0 only: does 390-step decode match appendant bit 0? -/
def len6OneStepGliderDecodeSlot0Ok : Bool :=
  let fin := c2SimRun 390 len6TruePhasedSupportInit
  decide (listTapeHasGliderAt fin 0 = false)

/-- **Approach #13:** glider-decode readback at all six slots after 390 steps. -/
theorem len6_one_step_glider_decode_not_ok :
    len6OneStepGliderDecodeOk = false := by
  native_decide

theorem len6_one_step_glider_decode_slot0_not_ok :
    len6OneStepGliderDecodeSlot0Ok = false := by
  native_decide

end Rule110
