import Mathlib.Data.List.GetD

import Rule110.CookC2BoundedSim
import Rule110.CTStoRule110
import Rule110.InfTape

/-!
# List simulator ↔ InfTape bridge (Stage 1b)

The bounded C2 witness in `CookC2BoundedSim` runs Rule 110 on a finite `List Bool`
with ether padding beyond the list length. This module connects that semantics to
`InfTape` stepping so we can relate `c2SimRead` to `tape_has_glider_at` on
`infRule110Steps` outputs.

Stage 1b target: discharge `cook_c2_tape_bit_ax` for slots `≤ 20` (then extend).
-/

namespace Rule110

/-- Embed a finite prefix as an `InfTape`, using `cookEther` beyond `l.length`. -/
def listToInfTape (l : List Bool) : InfTape :=
  fun i => if h : i < l.length then l.get ⟨i, h⟩ else cookEther i

theorem listToInfTape_lt (l : List Bool) {i : ℕ} (hi : i < l.length) :
    listToInfTape l i = l.get ⟨i, hi⟩ := by
  simp [listToInfTape, hi]

theorem listToInfTape_ge (l : List Bool) {i : ℕ} (hi : l.length ≤ i) :
    listToInfTape l i = cookEther i := by
  simp [listToInfTape, Nat.not_lt.mpr hi]

/-- Read bit `i` from a list the same way `c2SimRead` does at the glider origin. -/
def listReadDiff (l : List Bool) (origin : ℕ) : Bool :=
  l.getD origin false ≠ cookEther origin

theorem listReadDiff_eq_tape_has_glider_at (l : List Bool) (slot : ℕ)
    (hlen : c2SimOrigin slot < l.length) :
    listReadDiff l (c2SimOrigin slot) =
      tape_has_glider_at (listToInfTape l) slot 0 := by
  have hlen' : 1000 + slot * 42 < l.length := by
    simpa [c2SimOrigin, cts_tape_origin, cts_glider_spacing] using hlen
  unfold listReadDiff tape_has_glider_at listToInfTape
  simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing, cookEther, dif_pos hlen', Nat.add_zero]
  have hget : l.getD (1000 + slot * 42) false = l[1000 + slot * 42] :=
    @List.getD_eq_getElem Bool l false (1000 + slot * 42) hlen'
  simp [hget, List.getElem?_eq_getElem hlen']

end Rule110
