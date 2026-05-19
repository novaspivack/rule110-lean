import Rule110.CookC2BoundedSim
import Rule110.CookC2InfTapeBridge
import Rule110.CTStoRule110

set_option maxRecDepth 100000 in

/-!
# Bounded L=6 appendant simulation (Stage 3 mitigation)

Minimal nonempty appendant (`List.replicate 6 false`, M = 390) for Cook §4 collision
certificates. Init-cone bridge + optional 390-step data-cone readback check.
-/

namespace Rule110

def len6Slot0ConeLo : ℕ := cts_slot_origin 0 - 30

def len6TruePhasedSupportInit : List Bool :=
  (List.range c2SimBound).map fun i =>
    gliders_to_tape_phased (cts_word_to_placements_phased_with_support cook_min_len6_true_word) i

def len6PostAppendantPhasedSupportInit : List Bool :=
  (List.range c2SimBound).map fun i =>
    gliders_to_tape_phased (cts_word_to_placements_phased_with_support cook_min_len6_appendant) i

def len6TrueInitReadConeOk : Bool :=
  (List.range 61).all fun d =>
    let k := len6Slot0ConeLo + d
    decide (listToInfTape len6TruePhasedSupportInit k =
      cts_to_rule110_tape_phased_with_support cook_min_len6_cts cook_min_len6_true_word k)

/-- Init agreement for `[true]` with phased ossifier+leader support (slot-0 cone). -/
theorem len6_true_init_read_cone_ok : len6TrueInitReadConeOk = true := by
  native_decide

def len6OneStepSimDataConesOk : Bool :=
  let init := len6TruePhasedSupportInit
  let fin := c2SimRun 390 init
  let target := len6PostAppendantPhasedSupportInit
  (List.range 6).all fun slot =>
    (List.range 61).all fun d =>
      let k := cts_slot_origin slot - 30 + d
      decide (fin.getD k false = target.getD k false)

/-- **Negative witness (Stage 3 L=6):** 390 bounded list steps from `[true]` encoding do
    **not** match the post-step 6-slot appendant encoding on all data read cones. -/
theorem len6_one_step_data_cones_not_ok :
    len6OneStepSimDataConesOk = false := by
  native_decide

end Rule110
