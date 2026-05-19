import Rule110.CookBlockData
import Rule110.CookGliderCatalog
import Rule110.Ether
import Rule110.Gliders

set_option maxRecDepth 100000 in

/-!
# Cook A-type ossifier glider (Stage 2)

Cook's left-side **ossifier** uses period-3 blocks **A** and **B** (Cook 2008 §1.4).
Figure 5 classifies the underlying glider as **A** with period `(Δt, Δx) = (3, 2)` and
Cook width 6.

This module embeds the extracted **block A** bit rows (`CookBlockData`) and provides
bounded list simulation witnesses. Full isolated period-3 recurrence on bare ether is
**not** claimed: Cook's block rows are spatial snapshots from the full construction,
analogous to the C2 phases that require surrounding context (`CookGliderVerification`).

## Verified here

* Catalog linkage for species `A` (period and width).
* Block row lengths (28 cells each).
* Placement on ether differs from pure ether at the patch origin (`native_decide`).
* `GliderConfig` scaffold for downstream CTS encoding.
-/

namespace Rule110

/-! ## Catalog linkage -/

theorem ossifier_catalog_period :
    CookNamedGlider.periodTX CookNamedGlider.A = ⟨3, 2⟩ := rfl

theorem ossifier_catalog_width :
    CookNamedGlider.widthNat CookNamedGlider.A = 6 := rfl

theorem ossifier_block_period :
    (cookABlockRow ⟨0, by decide⟩).length = 28 :=
  cookABlockRow_length ⟨0, by decide⟩

/-! ## Representative 6-cell A patch (Figure 5 width) -/

/-- First six cells of block A row 0 — the Figure-5 width representative. -/
def cookOssifierPatchBits : List Bool :=
  (cookABlockRow ⟨0, by decide⟩).take 6

theorem cookOssifierPatchBits_length : cookOssifierPatchBits.length = 6 := by native_decide

/-! ## Bounded list simulation -/

def ossifierSimBound : ℕ := 500

/-- Origin for ossifier block experiments (left of the CTS data region). -/
def ossifierSimOrigin : ℕ := 200

def ossifierSimLeft (tape : List Bool) (i : ℕ) : Bool :=
  if i = 0 then false else tape.getD (i - 1) false

def ossifierSimRight (tape : List Bool) (i : ℕ) : Bool :=
  if i + 1 < tape.length then tape.getD (i + 1) false else cookEther (i + 1)

def ossifierSimStep (tape : List Bool) : List Bool :=
  (List.range tape.length).map fun i =>
    rule110Output (neighborhoodIndex (ossifierSimLeft tape i) (tape.getD i false)
      (ossifierSimRight tape i))

def ossifierSimRun : ℕ → List Bool → List Bool
  | 0, tape => tape
  | n + 1, tape => ossifierSimRun n (ossifierSimStep tape)

def ossifierSimInit (row : Fin 3) : List Bool :=
  let origin := ossifierSimOrigin
  let rowBits := cookABlockRow row
  (List.range ossifierSimBound).map fun i =>
    if origin ≤ i ∧ i - origin < rowBits.length then
      rowBits.getD (i - origin) false
    else
      cookEther i

theorem ossifierSimInit_length (row : Fin 3) :
    (ossifierSimInit row).length = ossifierSimBound := by
  simp [ossifierSimInit, List.length_map, List.length_range]

/-- Block A row 0 overrides pure ether at the patch origin. -/
theorem ossifier_block_row0_differs :
    (cookABlockRow ⟨0, by decide⟩).getD 0 false ≠ cookEther ossifierSimOrigin := by
  native_decide

/-- Block A row 0 overrides pure ether at cell index 1 within the patch. -/
theorem ossifier_block_row0_cell1_differs :
    (cookABlockRow ⟨0, by decide⟩).getD 1 false ≠ cookEther (ossifierSimOrigin + 1) := by
  native_decide

/-! ## CTS encoding scaffold -/

/-- Left ether phase constant from Cook's block compiler (`CONST_LEFT_PHASE = 7`). -/
def ossifierLeftPhase : ℕ := 7

/-- Spatial origin for the left-side ossifier train in CTS encodings. -/
def cts_ossifier_origin : ℕ := 500

/-- A-type ossifier glider config (6-cell patch, catalog species A). -/
def cts_ossifier_glider : GliderConfig :=
  { species := CookGliderRef.named CookNamedGlider.A
    origin  := cts_ossifier_origin
    phase   := ⟨ossifierLeftPhase, by decide⟩
    bits    := cookOssifierPatchBits }

theorem cts_ossifier_glider_bits_length :
    cts_ossifier_glider.bits.length = CookNamedGlider.widthNat CookNamedGlider.A := by
  rw [cts_ossifier_glider, cookOssifierPatchBits_length, ossifier_catalog_width]

end Rule110
