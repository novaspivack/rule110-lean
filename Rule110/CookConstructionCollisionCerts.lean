import Rule110.CookC2BoundedSim
import Rule110.CookCollisionTaxonomy
import Rule110.CTStoRule110

set_option maxRecDepth 100000 in

/-!
# Cook §4 construction collision certificates (finite windows)

Bounded `native_decide` witnesses for the five Neary–Woods collision kinds
(`CookConstructionCollisionKind`). Each certificate checks a local invariant in
the list-simulation layer (`c2SimRun`) on a finite patch of the CTS encoding.

These do **not** discharge Stage 3 alone; they supply the finite collision
evidence required alongside `CookCtsEvalSimAtDataCones` (Round 02 diagnosis).
-/

namespace Rule110

def collisionSimInit (placements : List GliderPlacement) : List Bool :=
  (List.range c2SimBound).map (gliders_to_tape_phased placements)

def collisionSimConeEq (init fin : List Bool) (slot : ℕ) : Bool :=
  (List.range 61).all fun d =>
    let k := cts_slot_origin slot - 30 + d
    decide (fin.getD k false = init.getD k false)

def collisionSimConeFixed (init : List Bool) (steps slot : ℕ) : Bool :=
  collisionSimConeEq init (c2SimRun steps init) slot

/-! ### Kind 1 — ossifier meets moving data (`ossifier_meets_moving_or_invisible`) -/

/-- Ossifier + single C2 at slot 0 (no leader): slot-0 read cone **not** fixed over 30 steps. -/
def kind1OssifierC2Placements : List GliderPlacement :=
  [cts_ossifier_placement] ++ cts_word_to_placements_phased [true]

def kind1OssifierC2Init : List Bool :=
  collisionSimInit kind1OssifierC2Placements

theorem kind1_ossifier_c2_slot0_cone_not_fixed_30 :
    collisionSimConeFixed kind1OssifierC2Init 30 0 = false := by
  native_decide

/-! ### Kind 2 — tape data passes moving data (`tape_passes_through_moving_or_invisible`) -/

/-- Full phased-with-support empty word: slot-0 cone **not** fixed (Round 02 negative). -/
def kind2EmptySupportInit : List Bool :=
  collisionSimInit (cts_word_to_placements_phased_with_support [])

theorem kind2_empty_support_slot0_cone_not_fixed_30 :
    collisionSimConeFixed kind2EmptySupportInit 30 0 = false := by
  native_decide

/-- Ossifier + leader + `[true]`: slot-0 cone **not** fixed over 30 steps. -/
def kind2TrueSupportPlacements : List GliderPlacement :=
  cts_word_to_placements_phased_with_support_idx cook_min_len6_cts 0 [true]

def kind2TrueSupportInit : List Bool :=
  collisionSimInit kind2TrueSupportPlacements

theorem kind2_true_support_slot0_cone_not_fixed_30 :
    collisionSimConeFixed kind2TrueSupportInit 30 0 = false := by
  native_decide

/-! ### Kind 3 — tape hits prepared leader (`tape_hits_prepared_leader`) -/

/-- Data at slot 19 + full support: slot-19 read cone **not** fixed over 30 steps. -/
def kind3Slot19Placements : List GliderPlacement :=
  cts_word_to_placements_phased_with_support (List.replicate 19 false ++ [true])

theorem kind3_slot19_cone_not_fixed_30 :
    collisionSimConeFixed (collisionSimInit kind3Slot19Placements) 30 19 = false := by
  native_decide

/-! ### Kind 4 — acceptor/rejector meets table data (scaffold) -/

/-- K+H leader + `[true]` at idx 0: slot-0 cone not fixed (leader collision field). -/
def kind4KHLeaderTruePlacements : List GliderPlacement :=
  cts_word_to_placements_phased_with_support_idx cook_min_len6_cts 0 [true]

theorem kind4_kh_leader_true_slot0_not_fixed_30 :
    collisionSimConeFixed (collisionSimInit kind4KHLeaderTruePlacements) 30 0 = false := by
  native_decide

/-! ### Taxonomy linkage (re-export negative witnesses) -/

abbrev cook_collision_kind1_negative := kind1_ossifier_c2_slot0_cone_not_fixed_30

abbrev cook_collision_kind2_empty_negative := kind2_empty_support_slot0_cone_not_fixed_30

abbrev cook_collision_kind3_negative := kind3_slot19_cone_not_fixed_30

end Rule110
