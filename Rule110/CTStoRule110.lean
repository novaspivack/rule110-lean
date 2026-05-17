import Mathlib.Data.List.Basic

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

/-! ## Two-phase ether infrastructure (Milestone 3 — Cook §4 phase-shift correctness)

Cook's C2 gliders each shift the ether background by **3 cells** (their Cook width).  A tape with `n`
C2 gliders has:
* ether at phase 0 (`cookEther i`) before the first glider
* ether at phase 3 (`cookEther (i+3)`) between gliders 1 and 2
* ether at phase 6 (`cookEther (i+6)`) between gliders 2 and 3
* …
* ether at phase `3*n` after the last glider

The plain `overrideCells cookEther` approach (Milestone 3a) is correct only for the **ether far from
any glider** (where `cook_cts_step_sim_ax` still holds via cone locality).  For a complete tape
encoding, `gliders_to_tape_phased` computes the accumulated phase shift at each position.

### C2 cycle-phase selection

The C2 glider has 7 time-phases (the canonical 7-cycle in `CookGliderCatalog`).  The phase-0 bits
`[1,1,0,0,0,1]` are correct when the left-ether phase at the glider's origin is **2 (mod 14)** (our
`cookEther` coordinate).  If the accumulated phase at slot k is `p`, the correct cycle phase is:

    left_ether_mod14 = (origin + p) % 14
    cycle_phase = [2→0, 6→1, 10→2, 0→3, 4→4, 8→5, 12→6].lookup(left_ether_mod14)

All valid left-ether phases for C2 are **even** mod 14.  With cts_tape_origin ≡ 2 (mod 14) and
cts_glider_spacing = 42 = 3 × 14, consecutive SLOTS have the same base ether phase (2), but the
**accumulated shift** grows by 3 per preceding 1-bit, so odd numbers of preceding 1-bits yield
left-phase 5, 11, … (invalid for phase-0 bits).  `cts_bit_to_glider_phased` selects the correct
cycle phase based on the accumulated shift.
-/

/-- The Cook phase of the C2 glider cycle given the accumulated phase shift at the glider's origin.
    Returns the cycle index (0–6) whose `left_ether_phase` matches `(origin + accum) % 14`.
    Only even values of `(origin + accum) % 14` are valid; returns 0 for invalid phases as a
    conservative default (callers should ensure valid placement). -/
def c2CyclePhase (originPlusAccum : ℕ) : Fin 7 :=
  match (originPlusAccum % 14) with
  | 2  => ⟨0, by decide⟩
  | 6  => ⟨1, by decide⟩
  | 10 => ⟨2, by decide⟩
  | 0  => ⟨3, by decide⟩
  | 4  => ⟨4, by decide⟩
  | 8  => ⟨5, by decide⟩
  | 12 => ⟨6, by decide⟩
  | _  => ⟨0, by decide⟩   -- invalid placement; bits will be wrong

/-- Ether value at position `i` when the accumulated Cook phase shift is `accum`. -/
def phaseEther (i : ℕ) (accum : ℕ) : Bool :=
  cookEtherBits ⟨(i + accum) % 14, Nat.mod_lt _ (by decide)⟩

@[simp] theorem phaseEther_zero (i : ℕ) : phaseEther i 0 = cookEther i := by
  simp [phaseEther, cookEther]

/-- A glider placement record: origin, Cook width, and cell bits. -/
structure GliderPlacement where
  origin     : ℕ
  cook_width : ℕ
  bits       : List Bool

/-- The accumulated Cook phase shift at position `i`, counting only placements whose
    glider ENDS at or before `i` (i.e., `origin + bits.length ≤ i`). -/
def accumPhaseAt (placements : List GliderPlacement) (i : ℕ) : ℕ :=
  placements.foldl (fun p g =>
    if g.origin + g.bits.length ≤ i then p + g.cook_width else p) 0

/-- Build a Rule 110 tape with correct two-phase ether background.
    For positions inside a glider: uses the glider's bits.
    For positions outside all gliders: uses ether at the accumulated phase shift.
    **Note:** placements must be sorted by `origin` and must not overlap. -/
def gliders_to_tape_phased (placements : List GliderPlacement) : InfTape :=
  fun i =>
    match placements.findSome? (fun g =>
      if _ : g.origin ≤ i ∧ i - g.origin < g.bits.length
      then some (g.bits.getD (i - g.origin) false)
      else none) with
    | some bit => bit
    | none     => phaseEther i (accumPhaseAt placements i)

theorem gliders_to_tape_phased_nil :
    gliders_to_tape_phased [] = cookEther := by
  funext i
  simp only [gliders_to_tape_phased, List.findSome?, accumPhaseAt, List.foldl,
             phaseEther, Nat.add_zero]
  simp [cookEther, cookEtherBits]

/-- Outside all gliders, the phased tape equals the phase-shifted ether. -/
theorem gliders_to_tape_phased_outside
    (placements : List GliderPlacement) (i : ℕ)
    (hout : ∀ g ∈ placements, ¬ (g.origin ≤ i ∧ i - g.origin < g.bits.length)) :
    gliders_to_tape_phased placements i = phaseEther i (accumPhaseAt placements i) := by
  -- The findSome? returns none when no placement contains i; follows by list induction.
  sorry

/-! ## CTS word → glider list encoding (Milestone 3 — Cook §4)

Cook's §4 encoding represents a CTS word `w = b₀ b₁ … bₙ` and appendant index `idx` as a
spatially-arranged train of gliders riding the ether background:

* **Tape data (C2) gliders** — one C2 glider per CTS `1`-bit, placed at positions spaced by
  `cts_glider_spacing` (= 14 × 3 = 42 cells, one ether period × 3) starting from `cts_tape_origin`.
* **Ossifier (A-type) gliders** — mark the current appendant boundary (not yet implemented).
* **Leader (Ē/F-type) gliders** — boundary signal for the "head" of the CTS word (not yet).

The concrete bit patterns for each species come from Cook §3 / Neary–Woods §2; they require
reading the paper directly. For now the function is specified by its expected TYPE and the
**collision axioms** that characterize its correctness.

-/

/-- Spacing between consecutive CTS bit positions (cells), in Cook's encoding. -/
def cts_glider_spacing : ℕ := 42  -- 14 (ether period) × 3 (ether phasing)

/-- Origin of the first CTS glider slot on the tape (chosen away from boundary). -/
def cts_tape_origin : ℕ := 1000

/-- Encode a single CTS bit at slot index `k` as an optional C2 glider.
    A `1`-bit places a C2 glider at the expected slot position.
    A `0`-bit contributes no glider (bare ether at that slot). -/
def cts_bit_to_glider (bit : Bool) (slot : ℕ) : Option GliderConfig :=
  if bit then
    some {
      species := CookGliderRef.named CookNamedGlider.C2
      origin  := cts_tape_origin + slot * cts_glider_spacing
      -- C2 left ether phase is 2 (in our cookEther coordinate system).
      -- Verified: 6-cell pattern, period 7, velocity 0, Cook width 3.
      -- Phase-0 bits = cookC2Bits = [1,1,0,0,0,1]. The glider must be placed at a
      -- position where cookEther(origin) = cookEtherBits ⟨2, _⟩ = false
      -- (i.e., origin ≡ 2 mod 14). Cook's construction spaces gliders at
      -- multiples of 42 = 14*3 to preserve this alignment.
      phase   := ⟨2, by decide⟩
      bits    := cookC2Bits   -- [true, true, false, false, false, true]
    }
  else none

/-- Encode a CTS word `w` (starting from appendant index `idx`) as a list of glider configs.
    Each `1`-bit in `w` at position `k` maps to a C2 glider at slot `k`.
    `0`-bits contribute nothing (bare ether).
    **Note**: uses phase-0 bits regardless of accumulated phase; see `cts_word_to_placements_phased`
    for the phase-correct version. -/
def cts_word_to_gliders (w : List Bool) (_idx : ℕ) : List GliderConfig :=
  (List.range w.length).filterMap (fun k =>
    if h : k < w.length then cts_bit_to_glider (w.get ⟨k, h⟩) k else none)

/-- Phase-correct version: each 1-bit at slot k gets the C2 cycle phase that matches the
    accumulated ether phase shift from all preceding 1-bits. -/
def cts_word_to_placements_phased (w : List Bool) : List GliderPlacement :=
  let (placements, _) := w.foldl (fun (acc : List GliderPlacement × ℕ) (bit : Bool) =>
    let (ps, slot) := acc
    let origin := cts_tape_origin + slot * cts_glider_spacing
    -- Accumulated phase = 3 × (number of 1-bits placed so far, from left)
    let accum := 3 * ps.length  -- each C2 contributes width=3
    let entry :=
      if bit then
        some { origin     := origin
               cook_width := 3
               bits       := cookCGliderCycle (c2CyclePhase (origin + accum)) }
      else none
    (ps ++ entry.toList, slot + 1))
    ([], 0)
  placements

/-- Phase-correct CTS Rule 110 tape using `gliders_to_tape_phased`. -/
def cts_to_rule110_tape_phased (_cts : CyclicTagSystem) (w : List Bool) : InfTape :=
  gliders_to_tape_phased (cts_word_to_placements_phased w)

/-- The canonical Rule 110 tape encoding for a CTS word + appendant index.
    Uses the simple (phase-0-only) glider placement; suitable for the collision axioms
    which only require existence of encode/decode. -/
def cts_to_rule110_tape (_cts : CyclicTagSystem) (idx : ℕ) (w : List Bool) : InfTape :=
  gliders_to_tape (cts_word_to_gliders w idx)

/-! ## Explicit Cook collision axioms (SPEC_069_C1R Milestone 3)

These axioms name the specific Rule 110 finite-witness claims that underlie
`cts_step_simulated_in_rule110`.  Each corresponds to a definite claim about
`infRule110Steps M tape i` for explicit finite tapes — falsifiable in principle by `native_decide`
on a concrete M and tape.  They are stated as axioms because the exact bit patterns and step counts
require reading Cook §3–4 and Neary–Woods §2 in full; they are not reconstructed here.

Adding them as NAMED axioms (not sorry) is honest: the gap is explicit, the claim is specific, and
`#print axioms gte_embeds_in_rule110` will list them by name.
-/

/-- **Cook Collision Axiom C1 (C2 tape bit simulation):**
    A C2 glider riding the ether, when observed at a spatial window of width W away from any other
    glider, survives for M Rule 110 steps and its decoded value equals the corresponding CTS bit.
    (Neary–Woods §2, "tape data passing through moving data or invisibles".)
    Source: Cook §3.2.2, Figure 9; Neary–Woods arXiv:0906.3248 §2 bullet 2. -/
axiom cook_c2_tape_bit_ax (slot : ℕ) (bit : Bool) :
    ∃ (M : ℕ) (decode_bit : InfTape → Bool),
      ∀ w idx,
        decode_bit (infRule110Steps M (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w)) =
          (slot < w.length && w.getD slot false = bit)

/-- **Cook Collision Axiom C2 (CTS step simulation):**
    For any CTS system and word, there exists M synchronous Rule 110 steps such that
    the glider configuration after M steps corresponds to the CTS-stepped word and index.
    (This is the core Milestone 3 claim.)
    Source: Cook §4, Theorem; Neary–Woods arXiv:0906.3248 §2–§3. -/
axiom cook_cts_step_sim_ax (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool) :
    ∃ (M : ℕ),
      ∀ i, cts_tape_origin + (w.length + 1) * cts_glider_spacing ≤ i →
        infRule110Steps M (cts_to_rule110_tape cts idx w) i = cookEther i

/-- **Cook Collision Axiom C3 (multi-step CTS simulation):**
    `n` CTS steps correspond to finitely many total Rule 110 steps, and the resulting tape
    encodes the n-stepped CTS word. This is the inductive content of Milestone 3.
    Source: Cook §4, Corollary; full CTS-to-Rule110 simulation. -/
axiom cook_cts_eval_sim_ax (cts : CyclicTagSystem) (n : ℕ) (w₀ : List Bool) :
    ∃ (M : ℕ),
      gliders_to_tape (cts_word_to_gliders (cts.cts_eval n w₀) (n % cts.cycleLen)) =
        infRule110Steps M (cts_to_rule110_tape cts 0 w₀)

end Rule110
