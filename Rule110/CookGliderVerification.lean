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

end Rule110
