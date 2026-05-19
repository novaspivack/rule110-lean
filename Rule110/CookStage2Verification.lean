import Rule110.OssifierGlider
import Rule110.LeaderGlider
import Rule110.CookCollisionWitnesses
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

theorem cook_support_agrees_on_data_cone_witness (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool)
    (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    cts_to_rule110_tape_with_support cts idx w k = cts_to_rule110_tape cts idx w k :=
  cts_support_agrees_on_data_cone_gen cts idx w slot hslot k hk_lo hk_hi

theorem cook_support_agrees_on_data_cone_empty (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    cts_to_rule110_tape_with_support (CyclicTagSystem.mk []) 0 [] k =
      cts_to_rule110_tape (CyclicTagSystem.mk []) 0 [] k :=
  cts_support_agrees_on_data_cone_gen (CyclicTagSystem.mk []) 0 [] slot hslot k hk_lo hk_hi

theorem cook_phased_support_placements_witness :
    cts_support_placements.length = 2 ∧
    cts_ossifier_placement.cook_width = 6 ∧
    cts_leader_placement.cook_width = cts_leader_cook_width ∧
    cts_leader_k_glider.bits.length = 338 :=
  ⟨cts_support_placements_length, rfl, rfl, cts_leader_k_glider_block_length⟩

theorem cook_leader_k_block_row0_witness :
    cookKBlockRow0.getD 1 false ≠ cookEther (300 + 1) :=
  leader_k_block_row0_differs

theorem cook_leader_k_cell_outside_slot_cone_witness (slot : ℕ) (hslot : slot ≤ 20) {i : ℕ} {b : Bool}
    (h : (i, b) ∈ cts_leader_k_glider.toCells) :
    i < cts_slot_origin slot - 30 ∨ cts_slot_origin slot + 30 < i :=
  cts_leader_k_cell_outside_slot_cone slot hslot h

theorem cook_phased_support_outside_slot_cone_for_idx_witness (cts : CyclicTagSystem) (idx : ℕ)
    (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    ∀ g ∈ cts_support_placements_for_idx cts idx,
      ¬ (g.origin ≤ k ∧ k - g.origin < g.bits.length) :=
  cts_phased_support_outside_slot_cone_for_idx cts idx slot hslot k hk_lo hk_hi

theorem cook_leader_placement_before_origin (i : ℕ) (hi : i < cts_leader_origin) :
    ¬ (cts_leader_placement.origin + cts_leader_placement.bits.length ≤ i) :=
  cts_leader_placement_ends_after i hi

theorem cook_phased_support_outside_slot_cone_witness (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    ∀ g ∈ cts_support_placements,
      ¬ (g.origin ≤ k ∧ k - g.origin < g.bits.length) :=
  cts_phased_support_outside_slot_cone slot hslot k hk_lo hk_hi

theorem cook_accumPhaseAt_phased_support_ossifier_offset (w : List Bool) (i : ℕ)
    (hdata : cts_tape_origin ≤ i) (hleader : i < cts_leader_origin) :
    accumPhaseAt (cts_word_to_placements_phased_with_support w) i =
      6 + accumPhaseAt (cts_word_to_placements_phased w) i :=
  accumPhaseAt_phased_with_support_ossifier_offset w i hdata hleader

end Rule110
