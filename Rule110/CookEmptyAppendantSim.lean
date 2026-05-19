import Rule110.CookC2BoundedSim
import Rule110.CookC2InfTapeBridge
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

/-- Init agreement: bounded list embed matches InfTape phased-with-support empty encoding
    on the slot-0 read cone. -/
def emptyPhasedSupportInitReadConeOk : Bool :=
  (List.range 61).all fun d =>
    let k := emptySlot0ConeLo + d
    decide (listToInfTape emptyPhasedSupportInit k =
      cts_to_rule110_tape_phased_with_support (CyclicTagSystem.mk []) [] k)

theorem empty_phased_support_init_read_cone_ok :
    emptyPhasedSupportInitReadConeOk = true := by
  native_decide

/-- **Negative witness:** 30 bounded list steps do **not** preserve the slot-0 read cone
    for phased-with-support empty encoding (`c2SimBound = 2500` window). -/
theorem empty_phased_support_cone_not_fixed_30 :
    emptyPhasedSupportConeFixed30 = false := by
  native_decide

/-- Slot-origin cell (not the full 61-cell cone) drifts after 30 steps. -/
def emptyPhasedSupportOriginCellNotFixed30 : Bool :=
  let init := emptyPhasedSupportInit
  let fin := c2SimRun 30 init
  decide (fin.getD (cts_slot_origin 0) false ≠ init.getD (cts_slot_origin 0) false)

theorem empty_phased_support_origin_cell_not_fixed_30 :
    emptyPhasedSupportOriginCellNotFixed30 = true := by
  native_decide

theorem emptyPhasedSupportInit_getD_origin :
    (c2SimRun 30 emptyPhasedSupportInit).getD (cts_slot_origin 0) false ≠
      emptyPhasedSupportInit.getD (cts_slot_origin 0) false := by
  have h := empty_phased_support_origin_cell_not_fixed_30
  simpa [emptyPhasedSupportOriginCellNotFixed30, decide_eq_true_iff] using h

def emptyPhasedSupportOriginListNotFixed30 : Bool :=
  decide (listToInfTape (c2SimRun 30 emptyPhasedSupportInit) (cts_slot_origin 0) ≠
    listToInfTape emptyPhasedSupportInit (cts_slot_origin 0))

theorem emptyPhasedSupportOriginListNotFixed30_true :
    emptyPhasedSupportOriginListNotFixed30 = true := by
  native_decide

theorem empty_phased_support_origin_list_not_fixed_30 :
    listToInfTape (c2SimRun 30 emptyPhasedSupportInit) (cts_slot_origin 0) ≠
      listToInfTape emptyPhasedSupportInit (cts_slot_origin 0) := by
  have h := emptyPhasedSupportOriginListNotFixed30_true
  exact (decide_eq_true_iff.mp (by simpa [emptyPhasedSupportOriginListNotFixed30] using h))

end Rule110
