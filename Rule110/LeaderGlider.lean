import Rule110.CookBlockData
import Rule110.CookGliderCatalog
import Rule110.Ether
import Rule110.Gliders

set_option maxRecDepth 100000 in

/-!
# Cook Ē-type leader glider and L-block template (Stage 2)

Cook's construction is built around the **Ē** glider (Figure 5: period `(30, -8)`,
Cook width 7). An **empty appendant** uses block **L** — the raw short leader
(30 lines × 235 cells per row in the PNG extraction).

This module embeds block L row 0 and links it to catalog species `Ebar`. Full
period-30 recurrence of the 235-cell row on bare ether is **not** verified in
isolation (same contextual caveat as C2 phases 1–3 and ossifier block rows).

## Verified here

* Catalog linkage for species `Ebar` (period `(30, -8)`, width 7).
* L-block row length 235; block period 30.
* Placement on ether differs from pure ether inside the patch (`native_decide`).
* `GliderConfig` scaffold for downstream CTS encoding.
-/

namespace Rule110

/-! ## Catalog linkage -/

theorem leader_catalog_period :
    CookNamedGlider.periodTX CookNamedGlider.Ebar = ⟨30, -8⟩ := rfl

theorem leader_catalog_width :
    CookNamedGlider.widthNat CookNamedGlider.Ebar = 7 := rfl

theorem leader_catalog_dt :
    (CookNamedGlider.periodTX CookNamedGlider.Ebar).dt = 30 := rfl

theorem leader_block_period_matches_catalog :
    cookLBlockPeriod = (CookNamedGlider.periodTX CookNamedGlider.Ebar).dt.toNat := by
  native_decide

/-! ## Bounded list simulation -/

def leaderSimBound : ℕ := 700

/-- Origin for leader block experiments (right-hand appendant region). -/
def leaderSimOrigin : ℕ := 300

def leaderSimLeft (tape : List Bool) (i : ℕ) : Bool :=
  if i = 0 then false else tape.getD (i - 1) false

def leaderSimRight (tape : List Bool) (i : ℕ) : Bool :=
  if i + 1 < tape.length then tape.getD (i + 1) false else cookEther (i + 1)

def leaderSimStep (tape : List Bool) : List Bool :=
  (List.range tape.length).map fun i =>
    rule110Output (neighborhoodIndex (leaderSimLeft tape i) (tape.getD i false)
      (leaderSimRight tape i))

def leaderSimRun : ℕ → List Bool → List Bool
  | 0, tape => tape
  | n + 1, tape => leaderSimRun n (leaderSimStep tape)

def leaderSimInit : List Bool :=
  let origin := leaderSimOrigin
  (List.range leaderSimBound).map fun i =>
    if origin ≤ i ∧ i - origin < cookLBlockRow0.length then
      cookLBlockRow0.getD (i - origin) false
    else
      cookEther i

theorem leaderSimInit_length : leaderSimInit.length = leaderSimBound := by
  simp [leaderSimInit, List.length_map, List.length_range]

/-- Block L row 0 overrides pure ether at cell index 1 within the patch. -/
theorem leader_block_row0_differs :
    cookLBlockRow0.getD 1 false ≠ cookEther (leaderSimOrigin + 1) := by native_decide

/-- Block L row 0 overrides pure ether at cell index 2 within the patch. -/
theorem leader_block_row0_cell2_differs :
    cookLBlockRow0.getD 2 false ≠ cookEther (leaderSimOrigin + 2) := by native_decide

/-! ## CTS encoding scaffold -/

/-- Right phase for block L in Cook's compiler (`true_right_phases[L] = 7`). -/
def leaderBlockPhase : ℕ := 7

/-- Spatial origin for the raw leader (empty-appendant case). -/
def cts_leader_origin : ℕ := 8000

/-- Ē-type leader glider config using the full L-block row 0 template. -/
def cts_leader_glider : GliderConfig :=
  { species := CookGliderRef.named CookNamedGlider.Ebar
    origin  := cts_leader_origin
    phase   := ⟨leaderBlockPhase, by decide⟩
    bits    := cookLBlockRow0 }

theorem cts_leader_glider_bits_length :
    cts_leader_glider.bits.length = cookLBlockRow0.length := rfl

theorem cts_leader_glider_block_length :
    cts_leader_glider.bits.length = 235 := cookLBlockRow0_length

end Rule110
