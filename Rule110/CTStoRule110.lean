import Rule110.CyclicTagSystem
import Rule110.Ether
import Rule110.Gliders
import Rule110.InfTape

/-!
# Cyclic tag systems → Rule 110 tapes (Cook §4 — Milestone 3)

Full Cook encoding writes CTS symbols as trains of separated gliders riding on the ether background,
then proves that **construction collisions** (Neary–Woods §2 checklist) realize `cts_step`.

For now we expose only the canonical ether baseline and functorial combinators built from
`overrideCells`; Milestone 3 replaces `ctsBaselineTape` with spatially-placed glider data.

Proved locality tools (still **not** Cook step simulation):

* `Gliders.overrideCells_eq_base_on_Icc`
* `ctsTapeWithOverrides_infRule110Steps_eq_shift_of_disjoint`
-/

namespace Rule110

/-- Baseline tape carrying no CTS payload yet — plain Cook ether. -/
def ctsBaselineTape (_cts : CyclicTagSystem) (_idx : ℕ) (_w : List Bool) : InfTape :=
  cookEther

@[simp] theorem ctsBaselineTape_eq_cookEther (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool) :
    ctsBaselineTape cts idx w = cookEther :=
  rfl

/-- Convenient spelling: overlay explicit finite writes atop the ether baseline. -/
def ctsTapeWithOverrides (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool)
    (cells : List (ℕ × Bool)) : InfTape :=
  overrideCells (ctsBaselineTape cts idx w) cells

theorem ctsTapeWithOverrides_nil (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool) :
    ctsTapeWithOverrides cts idx w [] = cookEther := by
  simp [ctsTapeWithOverrides]

/-- On the baseline CTS encoding (pure ether), global Rule‑110 evolution matches Cook’s spatial shift
by `4` per step at coordinates away from the hard boundary (`n ≤ i`). -/
theorem ctsBaselineTape_infRule110Steps_eq_shift {cts : CyclicTagSystem} {idx : ℕ} {w : List Bool}
    {i n : ℕ} (hn : n ≤ i) :
    infRule110Steps n (ctsBaselineTape cts idx w) i = cookEther (i + 4 * n) := by
  simpa [ctsBaselineTape_eq_cookEther] using infRule110Steps_cookEther_shift hn

/-- Payload writes disjoint from the backwards dependency cone `[i - n, i + n]` are invisible to the
value at site `i` after `n` synchronous Rule‑110 updates (still assuming `n ≤ i` for the ether drift).
Cook’s CTS simulation will place gliders inside bounded windows; this lemma isolates “far-away junk”.
-/
theorem ctsTapeWithOverrides_infRule110Steps_eq_shift_of_disjoint {cts : CyclicTagSystem} {idx : ℕ}
    {w : List Bool} {cells : List (ℕ × Bool)} {i n : ℕ} (hn : n ≤ i)
    (hdisj : ∀ p ∈ cells, p.1 < i - n ∨ i + n < p.1) :
    infRule110Steps n (ctsTapeWithOverrides cts idx w cells) i = cookEther (i + 4 * n) := by
  have hag :
      ∀ j, i - n ≤ j → j ≤ i + n → ctsTapeWithOverrides cts idx w cells j = cookEther j := by
    intro j hj_lo hj_hi
    simp only [ctsTapeWithOverrides, ctsBaselineTape_eq_cookEther]
    refine overrideCells_eq_base_on_Icc cookEther cells (i - n) (i + n) ?_ j hj_lo hj_hi
    intro p hp
    rcases hdisj p hp with hlt | hgt
    · exact Or.inl hlt
    · exact Or.inr hgt
  calc
    infRule110Steps n (ctsTapeWithOverrides cts idx w cells) i
        = infRule110Steps n cookEther i :=
          infRule110Steps_agree_Icc hn hag
    _ = cookEther (i + 4 * n) := infRule110Steps_cookEther_shift hn

end Rule110
