import Rule110.CTStoRule110
import Rule110.Gliders
import Rule110.LeaderGlider
import Rule110.OssifierGlider
import Mathlib.Tactic.Linarith

/-!
# Cook collision spacing witnesses (Stage 2 → 3 scaffolding)

Structural lemmas showing ossifier (origin 500) and leader (origin 8000) support patches
are disjoint from the 30-step read cone around CTS data slots `slot ≤ 20` (origins from 1000).
This lets `cts_to_rule110_tape_with_support` agree with `cts_to_rule110_tape` on all data reads.
-/

namespace Rule110

/-! ## Support patch cell bounds -/

theorem cts_ossifier_cell_le_end {i : ℕ} {b : Bool}
    (h : (i, b) ∈ cts_ossifier_glider.toCells) :
    i ≤ cts_ossifier_origin + 5 := by
  simp only [GliderConfig.toCells, List.mem_map, List.mem_range,
    cts_ossifier_glider, cookOssifierPatchBits_length] at h
  obtain ⟨j, hj, heq⟩ := h
  have hi : i = cts_ossifier_origin + j := by cases heq; rfl
  rw [hi, cts_ossifier_origin]
  omega

theorem cts_ossifier_cell_lt_tape_origin {i : ℕ} {b : Bool}
    (h : (i, b) ∈ cts_ossifier_glider.toCells) :
    i < cts_tape_origin := by
  have hi := cts_ossifier_cell_le_end h
  have hbound : cts_ossifier_origin + 5 < cts_tape_origin := by
    simp [cts_ossifier_origin, cts_tape_origin]
  exact Nat.lt_of_le_of_lt hi hbound

theorem cts_leader_cell_ge_leader_origin {i : ℕ} {b : Bool}
    (h : (i, b) ∈ cts_leader_glider.toCells) :
    cts_leader_origin ≤ i := by
  simp only [GliderConfig.toCells, List.mem_map, List.mem_range] at h
  obtain ⟨j, _, heq⟩ := h
  cases heq
  simp [cts_leader_glider, cts_leader_origin]

/-! ## Data cone vs support separation (slots ≤ 20) -/

theorem cts_slot_cone_lo_ge (slot : ℕ) (_hslot : slot ≤ 20) :
    970 ≤ cts_slot_origin slot - 30 := by
  simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  omega

theorem cts_slot_cone_hi_le (slot : ℕ) (hslot : slot ≤ 20) :
    cts_slot_origin slot + 30 ≤ 1870 := by
  simp [cts_slot_origin, cts_tape_origin, cts_glider_spacing]
  omega

theorem cts_ossifier_cell_outside_slot_cone (slot : ℕ) (hslot : slot ≤ 20) {i : ℕ} {b : Bool}
    (h : (i, b) ∈ cts_ossifier_glider.toCells) :
    i < cts_slot_origin slot - 30 ∨ cts_slot_origin slot + 30 < i := by
  left
  have := cts_ossifier_cell_le_end h
  have hlo := cts_slot_cone_lo_ge slot hslot
  simp [cts_ossifier_origin] at this ⊢
  omega

theorem cts_leader_cell_outside_slot_cone (slot : ℕ) (hslot : slot ≤ 20) {i : ℕ} {b : Bool}
    (h : (i, b) ∈ cts_leader_glider.toCells) :
    i < cts_slot_origin slot - 30 ∨ cts_slot_origin slot + 30 < i := by
  right
  have hge := cts_leader_cell_ge_leader_origin h
  have hhi := cts_slot_cone_hi_le slot hslot
  simp [cts_leader_origin] at hge ⊢
  omega

theorem cts_leader_k_cell_ge_leader_origin {i : ℕ} {b : Bool}
    (h : (i, b) ∈ cts_leader_k_glider.toCells) :
    cts_leader_origin ≤ i := by
  simp only [GliderConfig.toCells, List.mem_map, List.mem_range] at h
  obtain ⟨j, _, heq⟩ := h
  cases heq
  simp [cts_leader_k_glider, cts_leader_origin]

theorem cts_leader_k_cell_outside_slot_cone (slot : ℕ) (hslot : slot ≤ 20) {i : ℕ} {b : Bool}
    (h : (i, b) ∈ cts_leader_k_glider.toCells) :
    i < cts_slot_origin slot - 30 ∨ cts_slot_origin slot + 30 < i := by
  right
  have hge := cts_leader_k_cell_ge_leader_origin h
  have hhi := cts_slot_cone_hi_le slot hslot
  simp [cts_leader_origin] at hge ⊢
  omega

private theorem cts_support_flatMap_eq :
    (cts_support_gliders).reverse.flatMap GliderConfig.toCells =
      cts_leader_glider.toCells ++ cts_ossifier_glider.toCells := by
  simp [cts_support_gliders, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]

private theorem ne_of_mem_outside_cone (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30)
    {i : ℕ} {b : Bool}
    (hmem : (i, b) ∈ cts_ossifier_glider.toCells ∨ (i, b) ∈ cts_leader_glider.toCells) :
    i ≠ k := by
  intro heq
  rcases hmem with hmem | hmem
  · have hout := cts_ossifier_cell_outside_slot_cone slot hslot hmem
    rw [heq] at hout
    rcases hout with hlt | hgt <;> omega
  · have hout := cts_leader_cell_outside_slot_cone slot hslot hmem
    rw [heq] at hout
    rcases hout with hlt | hgt <;> omega

private theorem cts_support_cells_outside_slot_cone (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    ∀ p ∈ (cts_support_gliders).reverse.flatMap GliderConfig.toCells, p.1 ≠ k := by
  intro p hp
  rw [cts_support_flatMap_eq] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ne_of_mem_outside_cone slot hslot k hk_lo hk_hi (Or.inr hp)
  · exact ne_of_mem_outside_cone slot hslot k hk_lo hk_hi (Or.inl hp)

/-! ## Support vs data on the read cone (all words, slots ≤ 20) -/

private theorem cts_word_support_flatMap (w : List Bool) (idx : ℕ) :
    (cts_word_to_gliders w idx ++ cts_support_gliders).reverse.flatMap GliderConfig.toCells =
      (cts_support_gliders).reverse.flatMap GliderConfig.toCells ++ cts_word_to_cells w idx := by
  simp only [cts_word_to_cells, List.reverse_append, List.flatMap_append]

private theorem ne_of_mem_outside_cone_k (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30)
    {i : ℕ} {b : Bool}
    (hmem : (i, b) ∈ cts_ossifier_glider.toCells ∨ (i, b) ∈ cts_leader_k_glider.toCells) :
    i ≠ k := by
  intro heq
  rcases hmem with hmem | hmem
  · have hout := cts_ossifier_cell_outside_slot_cone slot hslot hmem
    rw [heq] at hout
    rcases hout with hlt | hgt <;> omega
  · have hout := cts_leader_k_cell_outside_slot_cone slot hslot hmem
    rw [heq] at hout
    rcases hout with hlt | hgt <;> omega

private theorem cts_support_k_flatMap_eq :
    ([cts_ossifier_glider, cts_leader_k_glider]).reverse.flatMap GliderConfig.toCells =
      cts_leader_k_glider.toCells ++ cts_ossifier_glider.toCells := by
  simp [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.reverse_cons, List.reverse_nil]

private theorem cts_support_k_cells_outside_slot_cone (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    ∀ p ∈ ([cts_ossifier_glider, cts_leader_k_glider]).reverse.flatMap GliderConfig.toCells, p.1 ≠ k := by
  intro p hp
  rw [cts_support_k_flatMap_eq] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ne_of_mem_outside_cone_k slot hslot k hk_lo hk_hi (Or.inr hp)
  · exact ne_of_mem_outside_cone_k slot hslot k hk_lo hk_hi (Or.inl hp)

private theorem cts_word_support_k_flatMap (w : List Bool) (idx : ℕ) :
    (cts_word_to_gliders w idx ++ [cts_ossifier_glider, cts_leader_k_glider]).reverse.flatMap
        GliderConfig.toCells =
      ([cts_ossifier_glider, cts_leader_k_glider]).reverse.flatMap GliderConfig.toCells ++
        cts_word_to_cells w idx := by
  simp only [cts_word_to_cells, List.reverse_append, List.flatMap_append]

private theorem cts_support_k_agrees_on_data_cone (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool)
    (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    gliders_to_tape (cts_word_to_gliders w idx ++ [cts_ossifier_glider, cts_leader_k_glider]) k =
      cts_to_rule110_tape cts idx w k := by
  simp only [cts_to_rule110_tape]
  rw [gliders_to_tape_eq_reverse_flatMap, gliders_to_tape_eq_reverse_flatMap,
    cts_word_support_k_flatMap, overrideCells_append]
  let supportCells :=
    ([cts_ossifier_glider, cts_leader_k_glider]).reverse.flatMap GliderConfig.toCells
  let dataCells := cts_word_to_cells w idx
  have hdisj := cts_support_k_cells_outside_slot_cone slot hslot k hk_lo hk_hi
  have hbase := overrideCells_eq_base_at cookEther supportCells k hdisj
  exact overrideCells_base_eq_at _ _ dataCells k (by rw [hbase])

/-- Support gliders do not affect the tape on the 30-step cone around data slot `slot ≤ 20`. -/
theorem cts_support_agrees_on_data_cone_gen (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool)
    (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    cts_to_rule110_tape_with_support cts idx w k = cts_to_rule110_tape cts idx w k := by
  simp only [cts_to_rule110_tape_with_support, cts_to_rule110_tape]
  rw [gliders_to_tape_eq_reverse_flatMap, gliders_to_tape_eq_reverse_flatMap,
    cts_word_support_flatMap, overrideCells_append]
  let supportCells := (cts_support_gliders).reverse.flatMap GliderConfig.toCells
  let dataCells := cts_word_to_cells w idx
  have hdisj := cts_support_cells_outside_slot_cone slot hslot k hk_lo hk_hi
  have hbase := overrideCells_eq_base_at cookEther supportCells k hdisj
  exact overrideCells_base_eq_at _ _ dataCells k (by rw [hbase])

/-- Idx-aware support gliders agree with data-only encoding on slot read cones. -/
theorem cts_support_idx_agrees_on_data_cone (cts : CyclicTagSystem) (idx₀ idx : ℕ) (w : List Bool)
    (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    cts_to_rule110_tape_with_support_idx cts idx₀ w k = cts_to_rule110_tape cts idx w k := by
  by_cases hlen : (cts.appendants.getD (idx₀ % cts.cycleLen) []).length = 0
  · have hnil := List.length_eq_zero_iff.mp hlen
    have hsup := cts_support_gliders_for_idx_empty cts idx₀ hnil
    simp only [cts_to_rule110_tape_with_support_idx, cts_to_rule110_tape_with_support, hsup]
    exact cts_support_agrees_on_data_cone_gen cts idx w slot hslot k hk_lo hk_hi
  · have hne : cts.appendants.getD (idx₀ % cts.cycleLen) [] ≠ [] := by
      intro hnil
      exact hlen (List.length_eq_zero_iff.mpr hnil)
    have hsup := cts_support_gliders_for_idx_nonempty cts idx₀ hne
    simp only [cts_to_rule110_tape_with_support_idx, hsup]
    exact cts_support_k_agrees_on_data_cone cts idx w slot hslot k hk_lo hk_hi

theorem cook_total_M_succ (cts : CyclicTagSystem) (n : ℕ) :
    cook_total_M cts (n + 1) =
      cook_total_M cts n +
        cook_M_for_appendant_len (cts.appendants.getD (n % cts.cycleLen) []).length := by
  unfold cook_total_M cook_total_M_from
  simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]

theorem cook_total_M_one (cts : CyclicTagSystem) :
    cook_total_M cts 1 =
      cook_M_for_appendant_len (cts.appendants.getD (0 % cts.cycleLen) []).length := by
  simp [cook_total_M, cook_total_M_from]

theorem cook_total_M_from_succ (cts : CyclicTagSystem) (n idx₀ : ℕ) :
    cook_total_M_from cts (n + 1) idx₀ =
      cook_total_M_from cts n idx₀ +
        cook_M_for_appendant_len (cts.appendants.getD ((idx₀ + n) % cts.cycleLen) []).length := by
  unfold cook_total_M_from
  simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## Phased support spacing (Stage 3 scaffolding) -/

theorem cts_ossifier_placement_end_le_tape_origin :
    cts_ossifier_placement.origin + cts_ossifier_placement.bits.length ≤ cts_tape_origin := by
  dsimp [cts_ossifier_placement, cts_ossifier_origin, cookOssifierPatchBits_length, cts_tape_origin]
  decide

theorem cts_tape_origin_lt_leader_origin : cts_tape_origin < cts_leader_origin := by
  simp [cts_tape_origin, cts_leader_origin]

theorem cts_leader_placement_origin_gt_slot_cone (slot : ℕ) (hslot : slot ≤ 20) :
    cts_slot_origin slot + 30 < cts_leader_placement.origin := by
  have hhi := cts_slot_cone_hi_le slot hslot
  simp [cts_leader_placement, cts_leader_origin] at hhi ⊢
  omega

theorem cts_ossifier_placement_end_lt_slot_cone (slot : ℕ) (hslot : slot ≤ 20) :
    cts_ossifier_placement.origin + cts_ossifier_placement.bits.length <
      cts_slot_origin slot - 30 := by
  have hlo := cts_slot_cone_lo_ge slot hslot
  simp [cts_ossifier_placement, cts_ossifier_origin, cookOssifierPatchBits_length,
    cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hlo ⊢
  omega

/-- Support placements are spatially disjoint from the 30-step read cone (slots ≤ 20). -/
theorem cts_phased_support_outside_slot_cone (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    ∀ g ∈ cts_support_placements,
      ¬ (g.origin ≤ k ∧ k - g.origin < g.bits.length) := by
  intro g hg
  rcases List.mem_cons.mp hg with h | hg
  · subst h
    intro ⟨_hk_origin, hk_in⟩
    have h506 : cts_ossifier_origin + 6 ≤ k := by
      have hend := cts_ossifier_placement_end_lt_slot_cone slot hslot
      simp [cts_ossifier_placement, cts_ossifier_origin, cookOssifierPatchBits_length,
        cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hend hk_lo ⊢
      omega
    have hk506 : k < cts_ossifier_origin + 6 := by
      simp [cts_ossifier_placement, cts_ossifier_origin, cookOssifierPatchBits_length] at hk_in ⊢
      omega
    exact (Nat.not_lt.mpr h506) hk506
  · simp [List.mem_singleton] at hg
    subst hg
    intro ⟨hk_origin, _⟩
    have hhi := cts_slot_cone_hi_le slot hslot
    simp [cts_leader_placement, cts_leader_origin, cts_slot_origin, cts_tape_origin,
      cts_glider_spacing] at hk_origin hk_hi hhi ⊢
    omega

private theorem cts_leader_support_origin_ge (cts : CyclicTagSystem) (idx : ℕ)
    {g : GliderPlacement} (hg : g ∈ cts_leader_support_for_idx cts idx) :
    cts_leader_origin ≤ g.origin := by
  unfold cts_leader_support_for_idx at hg
  split_ifs at hg with hlen
  · have heq : g = cts_leader_placement := List.mem_singleton.mp hg
    rw [heq]
    simp [cts_leader_placement, cts_leader_origin]
  · rcases List.mem_cons.mp hg with heq | hg
    · rw [heq]
      simp [cts_leader_k_placement, cts_leader_origin]
    · have heq' : g = cts_leader_h_placement := List.mem_singleton.mp hg
      rw [heq']
      simp [cts_leader_h_placement, cts_leader_h_origin, cts_leader_origin, cookKBlockRow0_length]

/-- Idx-selected support placements are outside the slot read cone (slots ≤ 20). -/
theorem cts_phased_support_outside_slot_cone_for_idx (cts : CyclicTagSystem) (idx : ℕ)
    (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30) :
    ∀ g ∈ cts_support_placements_for_idx cts idx,
      ¬ (g.origin ≤ k ∧ k - g.origin < g.bits.length) := by
  intro g hg
  simp only [cts_support_placements_for_idx, List.mem_cons] at hg
  rcases hg with rfl | hg
  · intro ⟨_hk_origin, hk_in⟩
    have h506 : cts_ossifier_origin + 6 ≤ k := by
      have hend := cts_ossifier_placement_end_lt_slot_cone slot hslot
      simp [cts_ossifier_placement, cts_ossifier_origin, cookOssifierPatchBits_length,
        cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hend hk_lo ⊢
      omega
    have hk506 : k < cts_ossifier_origin + 6 := by
      simp [cts_ossifier_placement, cts_ossifier_origin, cookOssifierPatchBits_length] at hk_in ⊢
      omega
    exact (Nat.not_lt.mpr h506) hk506
  · intro ⟨hk_origin, _hk_in⟩
    have hge := cts_leader_support_origin_ge cts idx hg
    have hhi := cts_slot_cone_hi_le slot hslot
    have hk8000 : cts_leader_origin ≤ k := Nat.le_trans hge hk_origin
    have hk1870 : k ≤ cts_slot_origin slot + 30 := hk_hi
    simp [cts_leader_origin, cts_slot_origin, cts_tape_origin, cts_glider_spacing] at hk8000 hk1870
    linarith

/-- Empty-word phased-with-support encoding is +6 ether on data-region slot cones. -/
theorem cts_phased_empty_support_ether_at (slot : ℕ) (hslot : slot ≤ 20) (k : ℕ)
    (hk_lo : cts_slot_origin slot - 30 ≤ k) (hk_hi : k ≤ cts_slot_origin slot + 30)
    (hdata : cts_tape_origin ≤ k) (hleader : k < cts_leader_origin) :
    cts_to_rule110_tape_phased_with_support cook_standard_empty_cts [] k =
      phaseEther k 6 := by
  unfold cts_to_rule110_tape_phased_with_support
  apply cts_to_rule110_tape_phased_with_support_outside cook_standard_empty_cts [] k
  · intro g hg
    rw [cts_word_to_placements_phased_with_support_nil] at hg
    exact cts_phased_support_outside_slot_cone slot hslot k hk_lo hk_hi g hg
  · exact hdata
  · exact hleader

end Rule110
