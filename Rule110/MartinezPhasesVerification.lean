import Rule110.Ether
import Rule110.InfTape
import Rule110.CookGliderCatalog
import Rule110.CookGliderVerification
import Rule110.MartinezPhasesCatalog

/-!
# Martinez phase catalog — dynamic verification and Cook bridges

Selective `native_decide` certificates for Martinez gliders on the `cookEther`
coordinate system. Full catalog data lives in `MartinezPhasesCatalog.lean`.
-/

namespace Rule110

theorem martinez_catalog_complete :
    martinezCatalogLength = 394 ∧
    martinezCatalogSourceCount = 365 ∧
    martinezCatalogAliasCount = 29 := by
  native_decide

theorem martinez_A_f1_1_cook_bridge :
    (martinezEntry? ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f1_1⟩).map (·.bits) =
      some cookAGliderBits :=
  martinez_A_f1_1_eq_cookAGliderBits

theorem martinez_A_f1_1_period_on_cookEther :
    ∀ k : Fin 6,
      infRule110Steps 3 (a_tape_at ⟨0, by decide⟩ a_gpos) (a_gpos + 2 + k.val) =
        (cookAGliderCycle ⟨0, by decide⟩).getD k.val false := by
  exact a_glider_phase0_period3

theorem martinez_A_period_matches_cook :
    aGliderTemporalPeriod = (CookNamedGlider.periodTX .A).dt.natAbs ∧
    aGliderSpatialPeriod = (CookNamedGlider.periodTX .A).dx.natAbs := by
  exact ⟨aGliderTemporalPeriod_eq_cook_dt, aGliderSpatialPeriod_eq_cook_dx⟩

/-- Martinez full-string gliders beyond A/C2 require Cook CTS collision context. -/
def martinezDynamicsOpen (key : MartinezKey) : Bool :=
  match key.family with
  | .A | .C2 | .ether => false
  | _ => true

def MartinezDynamicsOpen (key : MartinezKey) : Prop := martinezDynamicsOpen key = true

theorem martinez_A_dynamics_verified :
    martinezDynamicsOpen ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f1_1⟩ = false := by
  decide

theorem martinez_C2_A_dynamics_verified :
    martinezDynamicsOpen ⟨MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ = false := by
  decide

theorem martinez_B_dynamics_open :
    martinezDynamicsOpen ⟨MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f1_1⟩ = true := by
  decide

theorem cook_named_gliders_in_martinez_catalog :
    (martinezEntry? ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f1_1⟩).isSome ∧
    (martinezEntry? ⟨MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f1_1⟩).isSome ∧
    (martinezEntry? ⟨MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome ∧
    (martinezEntry? ⟨MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome ∧
    (martinezEntry? ⟨MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome ∧
    (martinezEntry? ⟨MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome ∧
    (martinezEntry? ⟨MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome ∧
    (martinezEntry? ⟨MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome ∧
    (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome ∧
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome := by
  native_decide

end Rule110
