import Rule110.CookC2BoundedSim
import Rule110.CTStoRule110

set_option maxRecDepth 100000 in

/-!
# Bounded empty-appendant simulation (Stage 3)

Finite-window Rule 110 simulation for the **empty CTS word** with phased ossifier+leader
support (`cts_support_placements`). Attempted `native_decide` certification of 30-step
slot-0 read-cone stability — **negative result** (cone cells change).
-/

namespace Rule110

def emptySlot0ConeLo : ℕ := cts_slot_origin 0 - 30

def emptySlot0ConeHi : ℕ := cts_slot_origin 0 + 30

def emptyPhasedSupportInit : List Bool :=
  (List.range c2SimBound).map (gliders_to_tape_phased cts_support_placements)

def emptyPhasedSupportConeEqInit (n : ℕ) : Bool :=
  let init := emptyPhasedSupportInit
  let fin := c2SimRun n init
  (List.range 61).all fun d =>
    decide (fin.getD (emptySlot0ConeLo + d) false = init.getD (emptySlot0ConeLo + d) false)

def emptyPhasedSupportConeFixed30 : Bool :=
  emptyPhasedSupportConeEqInit 30

/-- **Negative witness:** 30 bounded list steps do **not** preserve the slot-0 read cone
    for phased-with-support empty encoding (`c2SimBound = 2500` window). -/
theorem empty_phased_support_cone_not_fixed_30 :
    emptyPhasedSupportConeFixed30 = false := by
  native_decide

end Rule110
