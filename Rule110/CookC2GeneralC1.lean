import Rule110.CookC2InfTapeBridge
import Rule110.Gliders

/-!
# General Cook C1 — arbitrary word readback via glider spacing

C2 gliders are spaced `cts_glider_spacing = 42` cells apart; each 30-step read cone has radius 30.
Since 42 > 30 + 6 = 36, no other slot's glider reaches the read cone of `readSlot`.

This proves `cook_c2_tape_bit_general` for all words `w : List Bool` and slots ≤ 20.
-/

namespace Rule110

/-! ## Cell-level spacing lemma -/

/-- Every C2 cell in the word encoding lies in [c2SimOrigin s, c2SimOrigin s + 6) for some
    active slot `s`. Uses same pattern as `cts_word_cell_lt_far_boundary`. -/
private theorem cts_word_cell_slot_range {w : List Bool} {idx : ℕ} {p : ℕ × Bool}
    (hp : p ∈ cts_word_to_cells w idx) :
    ∃ s, s < w.length ∧ w.getD s false = true ∧
      c2SimOrigin s ≤ p.1 ∧ p.1 < c2SimOrigin s + 6 := by
  simp only [cts_word_to_cells, List.mem_flatMap, List.mem_reverse] at hp
  obtain ⟨gc, hgc, hcell⟩ := hp
  simp only [cts_word_to_gliders, List.mem_filterMap, List.mem_range] at hgc
  obtain ⟨slot, hslot, hsome⟩ := hgc
  have heq_gc : cts_bit_to_glider (w.get ⟨slot, hslot⟩) slot = some gc := by
    rw [dif_pos hslot] at hsome; exact hsome
  cases hb : w.get ⟨slot, hslot⟩ with
  | false =>
    rw [cts_bit_to_glider, hb] at heq_gc
    cases heq_gc
  | true =>
    rw [cts_bit_to_glider, hb] at heq_gc
    cases heq_gc
    -- Now gc = { origin := cts_tape_origin + slot * cts_glider_spacing, bits := cookC2Bits, ... }
    have hcell_fst_lt : p.1 < cts_tape_origin + slot * cts_glider_spacing + 6 := by
      have := @GliderConfig.toCells_fst_lt
        { species := CookGliderRef.named CookNamedGlider.C2,
          origin := cts_tape_origin + slot * cts_glider_spacing,
          phase := ⟨2, by decide⟩, bits := cookC2Bits } p.1 p.2 hcell
      simpa [cookC2Bits_length] using this
    simp only [GliderConfig.toCells, List.mem_map, List.mem_range] at hcell
    obtain ⟨j, hj, heq_p⟩ := hcell
    rw [cookC2Bits_length] at hj
    have hpeq : p.1 = cts_tape_origin + slot * cts_glider_spacing + j :=
      congrArg Prod.fst heq_p.symm
    refine ⟨slot, hslot, ?_, ?_, ?_⟩
    · rw [List.getD_eq_getElem (n := slot) (hn := hslot)]; exact hb
    · rw [hpeq]; simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]
    · rw [hpeq]; simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega

/-- A C2 cell in the read cone of `readSlot` must come from slot `readSlot` itself. -/
theorem cts_word_cell_in_cone_is_readSlot (w : List Bool) (readSlot idx : ℕ)
    (p : ℕ × Bool) (hp : p ∈ cts_word_to_cells w idx)
    (hk_lo : c2SimOrigin readSlot - 30 ≤ p.1)
    (hk_hi : p.1 ≤ c2SimOrigin readSlot + 30) :
    c2SimOrigin readSlot ≤ p.1 ∧ p.1 < c2SimOrigin readSlot + 6 := by
  obtain ⟨s, _, _, hs_lo, hs_hi⟩ := cts_word_cell_slot_range hp
  simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing] at *
  omega

/-! ## Cone equality: overrideCells with no cells → cookEther -/

private theorem cts_tape_no_cell_at_k (w : List Bool) (readSlot k : ℕ)
    (hk_lo : c2SimOrigin readSlot - 30 ≤ k) (hk_hi : k ≤ c2SimOrigin readSlot + 30)
    (hno : ∀ s, s < w.length → w.getD s false = true → s = readSlot →
        ¬ (c2SimOrigin readSlot ≤ k ∧ k < c2SimOrigin readSlot + 6)) :
    overrideCells cookEther (cts_word_to_cells w 0) k = cookEther k := by
  apply overrideCells_eq_base_at
  intro p hp hpk
  rw [← hpk] at hk_lo hk_hi
  obtain ⟨hge, hlt6⟩ := cts_word_cell_in_cone_is_readSlot w readSlot 0 p hp hk_lo hk_hi
  obtain ⟨s, hs_lt, hs_bit, hs_lo, hs_hi⟩ := cts_word_cell_slot_range hp
  simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing] at hge hlt6 hs_lo hs_hi
  have hs_eq : s = readSlot := by omega
  rw [hs_eq] at hs_lt hs_bit
  exact absurd ⟨by simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega,
    by simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega⟩
    (hno readSlot hs_lt hs_bit rfl)

/-! ## CTS tape equals min-word on cone -/

/-- When `w.getD readSlot false = true`, the C2 cell at position `k ∈ [c2SimOrigin readSlot, +6)`
    belongs to `cts_word_to_cells w 0`. -/
private theorem cts_word_cell_at_readSlot_mem (w : List Bool) (readSlot k : ℕ)
    (hbit : w.getD readSlot false = true)
    (hk_ge : c2SimOrigin readSlot ≤ k)
    (hk_lt6 : k < c2SimOrigin readSlot + 6) :
    (k, cookC2Bits.getD (k - c2SimOrigin readSlot) false) ∈ cts_word_to_cells w 0 := by
  have hlen : readSlot < w.length := by
    by_contra h
    push_neg at h
    rw [List.getD_eq_default w false h] at hbit
    exact absurd hbit (by decide)
  have hget : w.get ⟨readSlot, hlen⟩ = true := by
    rw [← List.getD_eq_get w false ⟨readSlot, hlen⟩]
    exact hbit
  simp only [cts_word_to_cells, List.mem_flatMap, List.mem_reverse]
  refine ⟨{ species := CookGliderRef.named CookNamedGlider.C2,
              origin := cts_tape_origin + readSlot * cts_glider_spacing,
              phase := ⟨2, by decide⟩,
              bits := cookC2Bits }, ?_, ?_⟩
  · simp only [cts_word_to_gliders, List.mem_filterMap, List.mem_range]
    refine ⟨readSlot, hlen, ?_⟩
    simp [dif_pos hlen, cts_bit_to_glider, hget]
    exact hget
  · simp only [GliderConfig.toCells, List.mem_map, List.mem_range, cookC2Bits_length]
    refine ⟨k - c2SimOrigin readSlot, ?_, ?_⟩
    · simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing] at hk_ge hk_lt6 ⊢; omega
    · apply Prod.ext
      · simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing] at hk_ge ⊢; omega
      · rfl

/-- Every cell at position `k ∈ [c2SimOrigin readSlot, +6)` in `cts_word_to_cells w 0`
    equals `(k, cookC2Bits.getD (k - c2SimOrigin readSlot) false)`.
    (Uniqueness: the 42-cell glider spacing ensures only one slot contributes.) -/
private theorem cts_word_cell_unique_at (w : List Bool) (readSlot k : ℕ)
    (hk_ge : c2SimOrigin readSlot ≤ k)
    (hk_lt6 : k < c2SimOrigin readSlot + 6)
    (p : ℕ × Bool)
    (hp : p ∈ cts_word_to_cells w 0)
    (hpk : p.1 = k) :
    p = (k, cookC2Bits.getD (k - c2SimOrigin readSlot) false) := by
  simp only [cts_word_to_cells, List.mem_flatMap, List.mem_reverse] at hp
  obtain ⟨gc, hgc, hcell⟩ := hp
  simp only [cts_word_to_gliders, List.mem_filterMap, List.mem_range] at hgc
  obtain ⟨slot', hslot', hsome⟩ := hgc
  rw [dif_pos hslot'] at hsome
  cases hbs : w.get ⟨slot', hslot'⟩ with
  | false =>
    rw [cts_bit_to_glider, hbs] at hsome
    cases hsome
  | true =>
    rw [cts_bit_to_glider, hbs] at hsome
    cases hsome
    -- gc is now { origin := cts_tape_origin + slot' * cts_glider_spacing, bits := cookC2Bits, ... }
    simp only [GliderConfig.toCells, List.mem_map, List.mem_range] at hcell
    obtain ⟨j, hj, heq_p⟩ := hcell
    rw [cookC2Bits_length] at hj
    have hpeq_fst : p.1 = cts_tape_origin + slot' * cts_glider_spacing + j :=
      congrArg Prod.fst heq_p.symm
    have hc2 : c2SimOrigin readSlot = cts_tape_origin + readSlot * cts_glider_spacing := by
      simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]
    have hs_eq : slot' = readSlot := by
      have hk_eq : k = cts_tape_origin + slot' * cts_glider_spacing + j := hpk.symm.trans hpeq_fst
      simp only [c2SimOrigin, cts_tape_origin, cts_glider_spacing] at hk_ge hk_lt6 hk_eq ⊢
      omega
    have hk_eq : k = c2SimOrigin readSlot + j := by
      rw [← hpk, hpeq_fst, hs_eq, hc2]
    have hj_eq : j = k - c2SimOrigin readSlot := by
      rw [hk_eq, hc2, Nat.add_sub_cancel_left]
    have hpval : p.2 = cookC2Bits.getD j false := congrArg Prod.snd heq_p.symm
    exact Prod.ext hpk (hpval.trans (congrArg (cookC2Bits.getD · false) hj_eq))

/-- The CTS tape for `w` and `cts_min_word readSlot (w.getD readSlot false)` agree on the
    30-step read cone of `readSlot`. -/
theorem cts_to_rule110_tape_cone_eq_min_word (w : List Bool) (readSlot idx : ℕ) (k : ℕ)
    (hk_lo : c2SimOrigin readSlot - 30 ≤ k) (hk_hi : k ≤ c2SimOrigin readSlot + 30) :
    cts_to_rule110_tape (CyclicTagSystem.mk []) idx w k =
      cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (cts_min_word readSlot (w.getD readSlot false)) k := by
  rw [cts_tape_idx_irrelevant idx 0 w k,
    cts_to_rule110_tape_eq_overrides, cts_to_rule110_tape_eq_overrides]
  simp only [ctsTapeWithOverrides, ctsBaselineTape_eq_cookEther]
  set bit := w.getD readSlot false
  by_cases hb : bit = true
  · by_cases hk_in : c2SimOrigin readSlot ≤ k ∧ k < c2SimOrigin readSlot + 6
    · -- k is inside the readSlot glider. Both encodings give the same C2 glider value at k.
      set v := cookC2Bits.getD (k - c2SimOrigin readSlot) false
      have hlhs : overrideCells cookEther (cts_word_to_cells w 0) k = v :=
        overrideCells_singleton_at cookEther _ k v
          (cts_word_cell_at_readSlot_mem w readSlot k hb hk_in.1 hk_in.2)
          (fun p hp hpk => cts_word_cell_unique_at w readSlot k hk_in.1 hk_in.2 p hp hpk)
      have hrhs : overrideCells cookEther (cts_word_to_cells (cts_min_word readSlot bit) 0) k = v :=
        overrideCells_singleton_at cookEther _ k v
          (cts_word_cell_at_readSlot_mem (cts_min_word readSlot bit) readSlot k
            (by rw [cts_min_word_getD]; exact hb) hk_in.1 hk_in.2)
          (fun p hp hpk =>
            cts_word_cell_unique_at (cts_min_word readSlot bit) readSlot k hk_in.1 hk_in.2 p hp hpk)
      rw [hlhs, hrhs]
    · -- k is outside [c2SimOrigin readSlot, c2SimOrigin readSlot + 5].
      have hno_k : ¬ (c2SimOrigin readSlot ≤ k ∧ k < c2SimOrigin readSlot + 6) := hk_in
      have hlhs : overrideCells cookEther (cts_word_to_cells w 0) k = cookEther k := by
        apply cts_tape_no_cell_at_k w readSlot k hk_lo hk_hi
        intro _ _ _ _ h
        exact absurd h hno_k
      have hrhs : overrideCells cookEther (cts_word_to_cells (cts_min_word readSlot bit) 0) k = cookEther k := by
        apply cts_tape_no_cell_at_k _ readSlot k hk_lo hk_hi
        intro _ _ _ _ h
        exact absurd h hno_k
      rw [hlhs, hrhs]
  · -- bit = false.
    have hbf : bit = false := by
      rcases Bool.eq_false_or_eq_true bit with hf | ht
      · exact absurd hf hb
      · exact ht
    have hno_w : overrideCells cookEther (cts_word_to_cells w 0) k = cookEther k := by
      apply cts_tape_no_cell_at_k w readSlot k hk_lo hk_hi
      intro _ _ hs_bit hs_eq _
      rw [hs_eq] at hs_bit
      simp only [bit, hbf] at hs_bit
      exact absurd hs_bit (by decide)
    have hno_min : overrideCells cookEther (cts_word_to_cells (cts_min_word readSlot bit) 0) k = cookEther k := by
      apply overrideCells_eq_base_at
      intro p hp _
      obtain ⟨s, hs_lt, hs_bit, _, _⟩ := cts_word_cell_slot_range hp
      rw [hbf] at hs_bit
      simp only [cts_min_word] at hs_bit
      have hall : (List.replicate readSlot false ++ [false]).getD s false = false := by
        rcases Nat.lt_or_ge s readSlot with hlt | hge
        · rw [List.getD_append (l := List.replicate readSlot false) (l' := [false])
            (h := by simpa [List.length_replicate] using hlt)]
          simp
        · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
          · rw [List.getD_append_right (List.replicate readSlot false) [false] false readSlot
              (by simp [List.length_replicate])]
            simp
          · rw [List.getD_eq_default]
            simp [List.length_append, List.length_replicate]; omega
      rw [hall] at hs_bit
      exact absurd hs_bit (by decide)
    rw [hno_w, hno_min]

/-! ## Main theorem -/

set_option maxRecDepth 800 in
/-- For any word `w` and slot `readSlot ≤ 20`, `cook_c2_decode_at` correctly reads `w.getD readSlot false`. -/
theorem cook_c2_tape_bit_general (readSlot : ℕ) (hslot : readSlot ≤ 20)
    (w : List Bool) (idx : ℕ) :
    cook_c2_decode_at readSlot
      (infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w)) =
      w.getD readSlot false := by
  have h30 : 30 ≤ c2SimOrigin readSlot := by
    simp [c2SimOrigin, cts_tape_origin, cts_glider_spacing]; omega
  -- Reduce to the min-word result via cone agreement
  have heq :
      infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w) (c2SimOrigin readSlot) =
      infRule110Steps 30
        (cts_to_rule110_tape (CyclicTagSystem.mk []) 0 (cts_min_word readSlot (w.getD readSlot false)))
        (c2SimOrigin readSlot) :=
    infRule110Steps_agree_Icc h30 fun k hk_lo hk_hi =>
      cts_to_rule110_tape_cone_eq_min_word w readSlot idx k hk_lo hk_hi
  -- Apply tape_has_glider_at_eq_of_origin to transfer
  exact (tape_has_glider_at_eq_of_origin _ _ readSlot 0 heq).trans
    (cook_c2_tape_bit_min_word readSlot (w.getD readSlot false) hslot 0)

/-- General C1 for all words and slots ≤ 20. -/
theorem cook_c2_tape_bit_ax_general (slot : ℕ) (hslot : slot ≤ 20) :
    ∀ (w : List Bool) (idx : ℕ),
      cook_c2_decode_at slot
        (infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w)) =
        w.getD slot false :=
  fun w idx => cook_c2_tape_bit_general slot hslot w idx

/-- **Cook Collision C1 discharged (InfTape, arbitrary word, slots ≤ 20).**
    Replaces the former `cook_c2_tape_bit_ax` axiom in `CTStoRule110`. The glider decoder
    `cook_c2_decode_at` reads `w.getD slot false`; the legacy axiom's length guard
    `(slot < w.length && …)` agrees on in-range slots and is false off-range when `bit = true`,
    but cannot be recovered from tape alone for off-range `bit = false` (bare ether ≡ in-range zero).
    Full universality uses the `getD` formulation below. -/
theorem cook_c2_tape_bit_ax (slot : ℕ) (hslot : slot ≤ 20) :
    ∀ (w : List Bool) (idx : ℕ),
      cook_c2_decode_at slot
        (infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w)) =
        w.getD slot false :=
  cook_c2_tape_bit_ax_general slot hslot

end Rule110
