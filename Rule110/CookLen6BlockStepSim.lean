import Rule110.CookAppendantBlockStack
import Rule110.CookC2BoundedSim
import Rule110.CookLen6AppendantSim
import Rule110.CookConstructionCollisionCerts
import Rule110.CTStoRule110

set_option maxRecDepth 100000 in

/-!
# L=6 sequential block-step simulation (Cook §4 dynamic scaffold)

Cook processes appendant blocks in order: **30 Rule 110 steps per block** (period 30).
This module overlays appendant-field blocks one at a time on the running list tape,
running 30 Rule 110 steps after each overlay (13 × 30 = 390 total).
-/

namespace Rule110

def cook_appendant_field_origin_local : ℕ := 2000

def collisionOverlayBlock (tape : List Bool) (origin : ℕ) (bits : List Bool) : List Bool :=
  (List.range tape.length).map fun i =>
    if origin ≤ i ∧ i - origin < bits.length then
      bits.getD (i - origin) false
    else
      tape.getD i false

def cook_len6_partial_block_placements (nBlocks : ℕ) : List GliderPlacement :=
  let stack := cook_appendant_block_stack (List.replicate 6 false)
  let (_, ps) :=
    (stack.take nBlocks).foldl (fun (origin, acc) b =>
      let bits := cookAppendantBlockRow0 b
      let p : GliderPlacement := { origin := origin, cook_width := 30, bits := bits }
      (origin + bits.length, acc ++ [p])) (cook_appendant_field_origin_local, [])
  ps

def cts_len6_dynamic_placements (nBlocks : ℕ) (w : List Bool) : List GliderPlacement :=
  cts_support_placements_for_idx cook_min_len6_cts 0 ++
    cook_len6_partial_block_placements nBlocks ++
    cts_word_to_placements_phased w

def len6DynamicInit (nBlocks : ℕ) (w : List Bool) : List Bool :=
  collisionSimInit (cts_len6_dynamic_placements nBlocks w)

/-- Overlay each L=6 stack block in order; 30 list-sim steps after each overlay. -/
def len6DynamicBlockStepRun (w : List Bool) : List Bool :=
  let stack := cook_appendant_block_stack (List.replicate 6 false)
  let (fin, _) :=
    stack.foldl (fun (tape, origin) b =>
      let bits := cookAppendantBlockRow0 b
      let tape' := collisionOverlayBlock tape origin bits
      (c2SimRun 30 tape', origin + bits.length))
      (len6DynamicInit 0 w, cook_appendant_field_origin_local)
  fin

def len6DynamicBlockStepDataConesOk (w : List Bool) : Bool :=
  let fin := len6DynamicBlockStepRun w
  let target := len6DynamicInit 13 w
  (List.range 6).all fun slot =>
    collisionSimConeEq target fin slot

/-- **Dynamic block-step witness:** sequential overlay + 30-step windows do not match
    the full static 13-block target on all six data cones. -/
theorem len6_dynamic_block_step_data_cones_not_ok :
    len6DynamicBlockStepDataConesOk cook_min_len6_true_word = false := by
  native_decide

end Rule110
