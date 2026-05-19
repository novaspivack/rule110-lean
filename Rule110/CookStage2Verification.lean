import Rule110.OssifierGlider
import Rule110.LeaderGlider
import Rule110.CTStoRule110

/-!
# Stage 2 Cook glider verification (Ossifier / Leader)

Re-exports key Stage 2 witnesses for the SPEC_070_08 pipeline.
-/

namespace Rule110

theorem cook_ossifier_catalog_witness :
    CookNamedGlider.periodTX CookNamedGlider.A = ⟨3, 2⟩ ∧
    CookNamedGlider.widthNat CookNamedGlider.A = 6 :=
  ⟨ossifier_catalog_period, ossifier_catalog_width⟩

theorem cook_leader_catalog_witness :
    CookNamedGlider.periodTX CookNamedGlider.Ebar = ⟨30, -8⟩ ∧
    CookNamedGlider.widthNat CookNamedGlider.Ebar = 7 :=
  ⟨leader_catalog_period, leader_catalog_width⟩

theorem cook_ossifier_block_present :
    (cookABlockRow ⟨0, by decide⟩).getD 0 false ≠ cookEther ossifierSimOrigin :=
  ossifier_block_row0_differs

theorem cook_leader_block_present :
    cookLBlockRow0.getD 1 false ≠ cookEther (leaderSimOrigin + 1) :=
  leader_block_row0_differs

theorem cook_cts_support_gliders_witness :
    cts_support_gliders.length = 2 ∧
    cts_ossifier_glider.species = CookGliderRef.named CookNamedGlider.A ∧
    cts_leader_glider.species = CookGliderRef.named CookNamedGlider.Ebar :=
  ⟨cts_support_gliders_length, rfl, rfl⟩

end Rule110
