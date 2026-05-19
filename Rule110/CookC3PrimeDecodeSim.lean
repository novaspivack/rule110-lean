import Rule110.CookAppendantBlockStack
import Rule110.CookC2InfTapeBridge
import Rule110.CookLen6AppendantSim
import Rule110.CTStoRule110

set_option maxRecDepth 100000 in

/-!
# C3′ readback formulations (approaches #13–#16)

Tests alternate Stage 3 targets weaker than full static cone re-encode.
-/

namespace Rule110

def listTapeHasGliderAt (tape : List Bool) (slot : ℕ) : Bool :=
  listReadDiff tape (c2SimOrigin slot)

/-- Phased-correct glider presence using `accumPhaseAt` from a placement list. -/
def listPhasedGliderAt (ps : List GliderPlacement) (tape : List Bool) (slot : ℕ) : Bool :=
  let origin := c2SimOrigin slot
  tape.getD origin false ≠ phaseEther origin (accumPhaseAt ps origin)

def len6OneStepGliderDecodeOk : Bool :=
  let init := len6TruePhasedSupportInit
  let fin := c2SimRun 390 init
  let w := cook_min_len6_appendant
  (List.range w.length).all fun slot =>
    decide (listTapeHasGliderAt fin slot = w.getD slot false)

/-- **Approach #14:** slot-origin cell equality only (not full 61-cell cones). -/
def len6OneStepOriginCellOk : Bool :=
  let fin := c2SimRun 390 len6TruePhasedSupportInit
  let target := len6PostAppendantPhasedSupportInit
  (List.range 6).all fun slot =>
    decide (fin.getD (c2SimOrigin slot) false = target.getD (c2SimOrigin slot) false)

/-- **Approach #15:** phased decode using post-step placement phase background. -/
def len6OneStepPhasedPostDecodeOk : Bool :=
  let fin := c2SimRun 390 len6TruePhasedSupportInit
  let ps := cts_word_to_placements_phased_with_support_idx cook_min_len6_cts 0 cook_min_len6_appendant
  (List.range 6).all fun slot =>
    decide (listPhasedGliderAt ps fin slot = cook_min_len6_appendant.getD slot false)

/-- **Approach #16:** first appendant block only (30 steps, K-block in L=6 stack). -/
def len6FirstBlock30OriginOk : Bool :=
  let fin := c2SimRun 30 len6TruePhasedSupportInit
  let target := len6PostAppendantPhasedSupportInit
  decide (fin.getD (c2SimOrigin 0) false = target.getD (c2SimOrigin 0) false)

theorem len6_one_step_glider_decode_not_ok :
    len6OneStepGliderDecodeOk = false := by native_decide

/-- **Approach #14 (positive):** slot-origin cells match post-step encode after 390 steps. -/
theorem len6_one_step_origin_cell_ok :
    len6OneStepOriginCellOk = true := by native_decide

/-- **Approach #15 (positive):** phased post-placement decode matches appendant word. -/
theorem len6_one_step_phased_post_decode_ok :
    len6OneStepPhasedPostDecodeOk = true := by native_decide

/-- **Approach #16:** after first 30 steps, slot-0 origin matches post-step target at origin. -/
theorem len6_first_block_30_origin_ok :
    len6FirstBlock30OriginOk = true := by native_decide

end Rule110
