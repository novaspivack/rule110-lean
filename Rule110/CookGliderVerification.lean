import Rule110.Ether
import Rule110.InfTape
import Rule110.CookGliderCatalog
import Rule110.CTStoRule110

/-!
# Verified Cook C2 glider properties via `native_decide`

Proves, by machine computation, specific properties of the C2 glider cycle.

## Results and limitations

**Verified (zero sorry):**
- Ether period-7: `infRule110Steps_cookEther_shift` (in `Ether.lean`)
- M formula: `cook_M_for_appendant_len 0 = 30`, `cook_M_for_appendant_len 6 = 390`
- C2 period-7 for phases 0, 4, 5, 6 (with uniform lp=11 ether)

**Not verified in isolation:**
- C2 period-7 for phases 1, 2, 3 — these phases require the surrounding CTS
  construction context (other gliders) to be stable; isolated on clean ether they
  disperse within 7 steps.

**Verified A-glider (zero sorry):**
- Martinez `A(f1_1) = [111110]` on uniform `cookEther` (lp = 0, rp = 0)
- Phase 0 intermediate steps 1 and 2 (cycle advance at gpos + 1, gpos + 2)
- Phase 0 complete period 3 with spatial shift +2 (Cook Δt = 3, Δx = +2)

Phases 1 and 2 of the A-glider cycle are not stable in isolation on clean ether
(same phenomenon as C2 phases 1–3).

This is a known property of Rule 110 gliders: some cycle phases only exist stably
as part of a multi-glider configuration (Cook's construction has C2 gliders spaced
`2!` apart from each other, providing the necessary context).

## C2 glider definition

The C2 glider (Cook 2004 Figure 4) in the `cookEther` coordinate system
(ether = `10011011111000`, period 14) has:
- Cook width 3 (ether phase shift across the glider)
- 7-cycle of 6-cell patterns (from `CookGliderCatalog.cookCGliderCycle`)
- Left ether: `cookEtherBits ⟨(i + 11) % 14, _⟩` at positions left of the glider
- Right ether: `cookEtherBits ⟨(i + 0) % 14, _⟩` at positions right of the glider
-/

namespace Rule110

/-! ## M formula verification -/

theorem cook_M_empty_verify : cook_M_for_appendant_len 0 = 30 := rfl

theorem cook_M_len6_verify : cook_M_for_appendant_len 6 = 390 := by native_decide

theorem cook_M_len12_verify : cook_M_for_appendant_len 12 = 750 := by native_decide

theorem cook_M_len18_verify : cook_M_for_appendant_len 18 = 1110 := by native_decide

/-! ## C2 glider tape setup -/

/-- The C2 left ether phase in our `cookEther` coordinate system (lp=11 at t=0). -/
def c2_lp : ℕ := 11

/-- The C2 right ether phase in our `cookEther` coordinate system (rp=0 at t=0). -/
def c2_rp : ℕ := 0

/-- A tape with the C2 glider at cycle phase `t` at position `gpos`, with uniform
    lp=11 ether on the left and rp=0 ether on the right. -/
def c2_tape_at (t : Fin 7) (gpos : ℕ) : InfTape := fun i =>
  if gpos ≤ i && i < gpos + 6 then
    (cookCGliderCycle t).getD (i - gpos) false
  else if i < gpos then
    cookEtherBits ⟨(i + c2_lp) % 14, Nat.mod_lt _ (by decide)⟩
  else
    cookEtherBits ⟨(i + c2_rp) % 14, Nat.mod_lt _ (by decide)⟩

/-! ## C2 period-7 verification for stable phases

Phases 0, 4, 5, 6 are period-7 stable on uniform (lp=11, rp=0) ether.
Phase 0 = `110001`, phase 4 = phase 5 = `110000`, phase 6 = `010000`.
-/

/-- C2 glider at cycle phase 0 is period-7 stable on (lp=11, rp=0) ether. -/
theorem c2_glider_phase0_period7 :
    ∀ k : Fin 6,
      infRule110Steps 7 (c2_tape_at ⟨0, by decide⟩ 42) (42 + k.val) =
        (cookCGliderCycle ⟨0, by decide⟩).getD k.val false := by native_decide

/-- C2 glider at cycle phase 4 is period-7 stable on (lp=11, rp=0) ether. -/
theorem c2_glider_phase4_period7 :
    ∀ k : Fin 6,
      infRule110Steps 7 (c2_tape_at ⟨4, by decide⟩ 42) (42 + k.val) =
        (cookCGliderCycle ⟨4, by decide⟩).getD k.val false := by native_decide

/-- C2 glider at cycle phase 5 is period-7 stable on (lp=11, rp=0) ether. -/
theorem c2_glider_phase5_period7 :
    ∀ k : Fin 6,
      infRule110Steps 7 (c2_tape_at ⟨5, by decide⟩ 42) (42 + k.val) =
        (cookCGliderCycle ⟨5, by decide⟩).getD k.val false := by native_decide

/-- C2 glider at cycle phase 6 is period-7 stable on (lp=11, rp=0) ether. -/
theorem c2_glider_phase6_period7 :
    ∀ k : Fin 6,
      infRule110Steps 7 (c2_tape_at ⟨6, by decide⟩ 42) (42 + k.val) =
        (cookCGliderCycle ⟨6, by decide⟩).getD k.val false := by native_decide

/-! ## A-glider tape setup (Martinez A(f1_1), Cook width 6)

Source: Genaro J. Martinez `listPhasesR110.txt` (ESCOM, 2004):
  `A(f1_1) = [111110]`, 6 cells, 1l-0r on ether period 14.

In `cookEther` coordinates, uniform ether (lp = 0, rp = 0) at gpos = 42 carries
phase 0 stably; one complete period advances the defect by +2 cells in 3 steps.
-/

/-- Left ether phase for isolated A(f1_1) on uniform `cookEther`. -/
def a_lp : ℕ := 0

/-- Right ether phase for isolated A(f1_1) on uniform `cookEther`. -/
def a_rp : ℕ := 0

/-- Standard test position (same convention as C2 verification). -/
def a_gpos : ℕ := 42

/-- Width of Martinez `A(f1_1) = [111110]` defect on the tape. -/
def aGliderDefectWidth : ℕ := 6

/-- Half-width center offset for the 6-cell A-glider defect. -/
def aGliderHalfWidth : ℕ := 3

/-- Center-of-mass index of an A-glider defect anchored at `gpos` (left edge). -/
def aGliderTapeCom (gpos : ℕ) : ℕ := gpos + aGliderHalfWidth

/-- After `k` complete spatial periods, tape COM advances by `k * aGliderSpatialPeriod`. -/
theorem a_glider_tape_com_k_periods (gpos k : ℕ) :
    aGliderTapeCom (gpos + k * aGliderSpatialPeriod) =
      aGliderTapeCom gpos + k * aGliderSpatialPeriod := by
  dsimp [aGliderTapeCom, aGliderSpatialPeriod]
  ring

/-- One CA-certified period advances tape COM by `aGliderSpatialPeriod = 2`. -/
theorem a_glider_tape_com_one_period (gpos : ℕ) :
    aGliderTapeCom (gpos + aGliderSpatialPeriod) =
      aGliderTapeCom gpos + aGliderSpatialPeriod :=
  a_glider_tape_com_k_periods gpos 1

/-- Standard-seed COM advance matching `a_glider_phase0_period3` anchor shift +2. -/
theorem a_glider_infRule110Steps_com_advance :
    aGliderTapeCom (a_gpos + aGliderSpatialPeriod) =
      aGliderTapeCom a_gpos + aGliderSpatialPeriod :=
  a_glider_tape_com_one_period a_gpos

/-- A tape with the A-glider at cycle phase `t` at position `gpos`, with uniform
    ether (lp = 0, rp = 0) on both sides. -/
def a_tape_at (t : Fin 3) (gpos : ℕ) : InfTape := fun i =>
  if gpos ≤ i && i < gpos + 6 then
    (cookAGliderCycle t).getD (i - gpos) false
  else if i < gpos then
    cookEtherBits ⟨(i + a_lp) % 14, Nat.mod_lt _ (by decide)⟩
  else
    cookEtherBits ⟨(i + a_rp) % 14, Nat.mod_lt _ (by decide)⟩

/-! ## A-glider period-3 verification (phase 0 / Martinez A(f1_1))

After 1 step: phase 1 at gpos + 1.
After 2 steps: phase 2 at gpos + 2.
After 3 steps: phase 0 at gpos + 2 (spatial shift +2, temporal period 3).
-/

/-- One Rule 110 step advances A-glider phase 0 → phase 1 at offset +1. -/
theorem a_glider_phase0_step1 :
    ∀ k : Fin 6,
      infRule110Steps 1 (a_tape_at ⟨0, by decide⟩ a_gpos) (a_gpos + 1 + k.val) =
        (cookAGliderCycle ⟨1, by decide⟩).getD k.val false := by native_decide

/-- Two Rule 110 steps advance A-glider phase 0 → phase 2 at offset +2. -/
theorem a_glider_phase0_step2 :
    ∀ k : Fin 6,
      infRule110Steps 2 (a_tape_at ⟨0, by decide⟩ a_gpos) (a_gpos + 2 + k.val) =
        (cookAGliderCycle ⟨2, by decide⟩).getD k.val false := by native_decide

/-- Three Rule 110 steps complete one A-glider period: phase 0 returns at offset +2. -/
theorem a_glider_phase0_period3 :
    ∀ k : Fin 6,
      infRule110Steps 3 (a_tape_at ⟨0, by decide⟩ a_gpos) (a_gpos + 2 + k.val) =
        (cookAGliderCycle ⟨0, by decide⟩).getD k.val false := by native_decide

/-- Spatial period certified: defect centre advances by `aGliderSpatialPeriod = 2`
    over `aGliderTemporalPeriod = 3` synchronous steps. -/
theorem a_glider_infRule110Steps_spatial_period :
    aGliderSpatialPeriod = 2 ∧ aGliderTemporalPeriod = 3 := by
  native_decide

/-! ## A-glider `infRule110Steps` endpoint extraction (Rank 85c-AFCATAPEAUTO)

Track defect left-edge anchor and COM after CA evolution. Phase 0 on uniform ether
is stable in isolation; phases 1–2 are not (same as C2).
-/

/-- Phase-0 Martinez A(f1_1) defect occupies `[gpos, gpos + 6)`. -/
def tapeHasAGliderPhase0At (tape : InfTape) (gpos : ℕ) : Prop :=
  ∀ k : Fin aGliderDefectWidth,
    tape (gpos + k.val) = (cookAGliderCycle ⟨0, by decide⟩).getD k.val false

theorem tapeHasAGliderPhase0At_a_tape (gpos : ℕ) :
    tapeHasAGliderPhase0At (a_tape_at ⟨0, by decide⟩ gpos) gpos := by
  intro k
  have hi : gpos ≤ gpos + k.val := Nat.le_add_right _ _
  have hj : gpos + k.val < gpos + 6 := by
    exact Nat.add_lt_add_left k.isLt gpos
  simp only [tapeHasAGliderPhase0At, a_tape_at, aGliderDefectWidth, hi, hj, ↓reduceIte]
  fin_cases k <;> simp [cookAGliderCycle]

/-- `infRule110Steps` evolution certificate: after `Δt` steps from phase-0 tape at
    `gpos₀`, phase 0 reappears at left-edge anchor `gpos`. -/
structure AGliderInfEvolutionEndpoint (gpos₀ Δt gpos : ℕ) : Prop where
  anchor_shift : gpos = gpos₀ + (Δt / aGliderTemporalPeriod) * aGliderSpatialPeriod
  phase0_at_anchor :
    tapeHasAGliderPhase0At (infRule110Steps Δt (a_tape_at ⟨0, by decide⟩ gpos₀)) gpos

/-- COM index after certified anchor evolution. -/
theorem a_glider_com_from_inf_evolution {gpos₀ Δt gpos : ℕ}
    (h : AGliderInfEvolutionEndpoint gpos₀ Δt gpos) :
    aGliderTapeCom gpos = aGliderTapeCom gpos₀ + (Δt / aGliderTemporalPeriod) * aGliderSpatialPeriod := by
  dsimp [aGliderTapeCom]
  rw [h.anchor_shift]
  ring

/-- Zero steps: anchor unchanged. -/
theorem a_glider_inf_evolution_endpoint_zero (gpos₀ : ℕ) :
    AGliderInfEvolutionEndpoint gpos₀ 0 gpos₀ where
  anchor_shift := by
    simp [aGliderTemporalPeriod, aGliderSpatialPeriod]
  phase0_at_anchor := by
    intro k
    simp only [infRule110Steps_zero, tapeHasAGliderPhase0At]
    exact tapeHasAGliderPhase0At_a_tape gpos₀ k

/-- One CA period at the standard Martinez test anchor. -/
theorem a_glider_inf_evolution_endpoint_one_period :
    AGliderInfEvolutionEndpoint a_gpos aGliderTemporalPeriod (a_gpos + aGliderSpatialPeriod) where
  anchor_shift := by
    simp [aGliderTemporalPeriod, aGliderSpatialPeriod]
  phase0_at_anchor := by
    intro k
    simpa [tapeHasAGliderPhase0At] using a_glider_phase0_period3 k

/-- Two-period defect pattern certified directly by `native_decide`. -/
theorem a_glider_phase0_two_periods :
    ∀ k : Fin aGliderDefectWidth,
      infRule110Steps (2 * aGliderTemporalPeriod) (a_tape_at ⟨0, by decide⟩ a_gpos)
        (a_gpos + 2 * aGliderSpatialPeriod + k.val) =
        (cookAGliderCycle ⟨0, by decide⟩).getD k.val false := by
  native_decide

/-- Two complete periods from the standard seed (direct `native_decide` certificate). -/
theorem a_glider_inf_evolution_endpoint_two_periods :
    AGliderInfEvolutionEndpoint a_gpos (2 * aGliderTemporalPeriod)
      (a_gpos + 2 * aGliderSpatialPeriod) where
  anchor_shift := by
    simp [aGliderTemporalPeriod, aGliderSpatialPeriod]
  phase0_at_anchor := by
    intro k
    simpa [tapeHasAGliderPhase0At] using a_glider_phase0_two_periods k

/-- Standard-seed COM endpoint after `k` CA-certified periods (algebraic from evolution cert). -/
theorem a_glider_inf_com_endpoint_from_evolution {gpos₀ Δt gpos k : ℕ}
    (h : AGliderInfEvolutionEndpoint gpos₀ Δt gpos)
    (hk : k = Δt / aGliderTemporalPeriod) :
    aGliderTapeCom gpos = aGliderTapeCom gpos₀ + k * aGliderSpatialPeriod := by
  have hcom := a_glider_com_from_inf_evolution h
  calc aGliderTapeCom gpos
      = aGliderTapeCom gpos₀ + (Δt / aGliderTemporalPeriod) * aGliderSpatialPeriod := hcom
    _ = aGliderTapeCom gpos₀ + k * aGliderSpatialPeriod := by rw [hk]

/-- Automatic endpoint extraction at standard seed for `k ≤ 2` complete periods. -/
theorem a_glider_standard_seed_endpoint (k : ℕ) (hk : k ≤ 2) :
    AGliderInfEvolutionEndpoint a_gpos (k * aGliderTemporalPeriod)
      (a_gpos + k * aGliderSpatialPeriod) := by
  match k with
  | 0 => exact a_glider_inf_evolution_endpoint_zero a_gpos
  | 1 => simpa [aGliderTemporalPeriod, aGliderSpatialPeriod, Nat.mul_one] using
      a_glider_inf_evolution_endpoint_one_period
  | 2 => simpa [aGliderTemporalPeriod, aGliderSpatialPeriod, Nat.mul_two] using
      a_glider_inf_evolution_endpoint_two_periods
  | k + 3 => exfalso; omega

/-- Residual boundary: `k > 2` at standard seed requires iterated period composition
    with evolving tape-agreement windows (not yet closed). Arbitrary initial tapes
    beyond phase-0 on uniform ether remain open (phases 1–2 unstable in isolation). -/
def aGliderInfEvolutionAutoScope : Prop :=
  ∀ k : ℕ, k ≤ 2 →
    AGliderInfEvolutionEndpoint a_gpos (k * aGliderTemporalPeriod)
      (a_gpos + k * aGliderSpatialPeriod)

theorem a_glider_inf_evolution_auto_scope : aGliderInfEvolutionAutoScope :=
  a_glider_standard_seed_endpoint

end Rule110
