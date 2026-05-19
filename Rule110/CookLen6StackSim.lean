import Rule110.CookAppendantBlockStack
import Rule110.CookC2BoundedSim
import Rule110.CookLen6AppendantSim
import Rule110.CTStoRule110

set_option maxRecDepth 100000 in

/-!
# L=6 appendant with spatial I/J block stack (Stage 3 approach #10)

Extends phased-with-support idx encoding with contiguous appendant-field blocks
(`cook_appendant_block_placements`). Tests whether spatial block stack closes
390-step data-cone agreement.
-/

namespace Rule110

/-- Origin for contiguous appendant-field row-0 blocks (left of leader at 8000). -/
def cook_appendant_field_origin : ℕ := 2000

def cook_appendant_block_placements (app : List Bool) : List GliderPlacement :=
  let (_, ps) :=
    (cook_appendant_block_stack app).foldl (fun (origin, acc) b =>
      let bits := cookAppendantBlockRow0 b
      let p : GliderPlacement := { origin := origin, cook_width := 30, bits := bits }
      (origin + bits.length, acc ++ [p])) (cook_appendant_field_origin, [])
  ps

def cts_word_to_placements_phased_with_stack_idx (cts : CyclicTagSystem) (idx : ℕ)
    (w : List Bool) : List GliderPlacement :=
  let app := cts.appendants.getD (idx % cts.cycleLen) []
  cts_support_placements_for_idx cts idx ++
    cook_appendant_block_placements app ++
    cts_word_to_placements_phased w

def cts_to_rule110_tape_phased_with_stack_idx (cts : CyclicTagSystem) (idx : ℕ)
    (w : List Bool) : InfTape :=
  gliders_to_tape_phased (cts_word_to_placements_phased_with_stack_idx cts idx w)

def len6TrueStackPhasedInit : List Bool :=
  (List.range c2SimBound).map fun i =>
    gliders_to_tape_phased
      (cts_word_to_placements_phased_with_stack_idx cook_min_len6_cts 0 cook_min_len6_true_word) i

def len6PostAppendantStackPhasedInit : List Bool :=
  (List.range c2SimBound).map fun i =>
    gliders_to_tape_phased
      (cts_word_to_placements_phased_with_stack_idx cook_min_len6_cts 0 cook_min_len6_appendant) i

def len6StackOneStepSimDataConesOk : Bool :=
  let init := len6TrueStackPhasedInit
  let fin := c2SimRun 390 init
  let target := len6PostAppendantStackPhasedInit
  (List.range 6).all fun slot =>
    (List.range 61).all fun d =>
      let k := cts_slot_origin slot - 30 + d
      decide (fin.getD k false = target.getD k false)

/-- **Approach #10 witness:** spatial I/J block stack does not close data cones either. -/
theorem len6_stack_one_step_data_cones_not_ok :
    len6StackOneStepSimDataConesOk = false := by
  native_decide

end Rule110
