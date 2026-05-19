import Mathlib.Data.List.Basic

import Rule110.CookGliderCatalog
import Rule110.Ether
import Rule110.InfTape

/-!
# Glider references and finite tape overlays (Milestone 2 scaffolding)

Cook’s real glider grammar is **phase-parameterized** (`CookCollisionTaxonomy`): collisions depend on
`CookUpPhase` / `CookOverPhase`, not merely on species labels.

This module introduces:

* `CookGliderRef`, combining catalogued named gliders and indexed families from Figure 5.
* `overrideCells`, a simple utility writing finitely many cellular assignments on top of any base tape.

Placing canonical Cook bit-patterns for each species — and proving collision lemmas against
`infTapeStep` — is Milestone 2–3 work.

## Locality

`overrideCells_eq_base_on_Icc` records that patches disjoint from a finite spatial interval do not
change the tape inside that interval — combined with `infRule110Steps_agree_Icc` this yields “payload
far from cone ⇒ evolution matches ether” (`CTStoRule110.ctsTapeWithOverrides_infRule110Steps_eq_shift_of_disjoint`).
-/

namespace Rule110

/-- A Cook Figure 5 species reference (named row or indexed family instantiation). -/
inductive CookGliderRef where
  | named (g : CookNamedGlider) : CookGliderRef
  | indexed (g : CookIndexedGlider) (n : ℕ) : CookGliderRef

def CookGliderRef.widthNat : CookGliderRef → ℕ
  | .named g => g.widthNat
  | .indexed g n => g.widthNat n

/-- Apply finitely many labelled overrides to `base`, last wins on duplicate indices. -/
def overrideCells (base : InfTape) : List (ℕ × Bool) → InfTape
  | [] => base
  | (i, b) :: rest =>
      overrideCells (fun j => if j = i then b else base j) rest

@[simp] theorem overrideCells_nil (base : InfTape) : overrideCells base [] = base :=
  rfl

theorem overrideCells_cons (base : InfTape) (i : ℕ) (b : Bool) (rest : List (ℕ × Bool)) :
    overrideCells base ((i, b) :: rest) =
      overrideCells (fun j => if j = i then b else base j) rest :=
  rfl

/-- If two bases agree at `k`, an overlay produces the same value at `k`. -/
theorem overrideCells_base_eq_at (base base' : InfTape) (cells : List (ℕ × Bool)) (k : ℕ)
    (heq : base k = base' k) :
    overrideCells base cells k = overrideCells base' cells k := by
  revert base base' heq
  induction cells with
  | nil =>
    intro base base' heq
    exact heq
  | cons p ps ih =>
    intro base base' heq
    rcases p with ⟨i, b⟩
    simp only [overrideCells]
    by_cases hi : i = k
    · subst hi
      exact ih _ _ (by simp)
    · exact ih _ _ (by simp [hi, heq])

theorem overrideCells_cons_index_ne (base : InfTape) (i k : ℕ) (b : Bool) (ps : List (ℕ × Bool))
    (hi : i ≠ k) :
    overrideCells base ((i, b) :: ps) k = overrideCells base ps k := by
  rw [overrideCells]
  exact overrideCells_base_eq_at (fun j => if j = i then b else base j) base ps k
    (by simp [Ne.symm hi])

/-- If every write at `k` is absent, the overlay leaves `base k` unchanged. -/
theorem overrideCells_eq_base_at (base : InfTape) (cells : List (ℕ × Bool)) (k : ℕ)
    (h : ∀ p ∈ cells, p.1 ≠ k) :
    overrideCells base cells k = base k := by
  induction cells with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨i, b⟩
    simp only [List.mem_cons, forall_eq_or_imp] at h
    rw [overrideCells_cons_index_ne base i k b ps h.1]
    exact ih h.2

/-- When all cells at position `kk` in `cells` have value `vv` and at least one exists,
    `overrideCells base cells kk = vv`. -/
theorem overrideCells_singleton_at (base : InfTape) (cells : List (ℕ × Bool)) (kk : ℕ) (vv : Bool)
    (hmem : (kk, vv) ∈ cells)
    (huniq : ∀ p ∈ cells, p.1 = kk → p = (kk, vv)) :
    overrideCells base cells kk = vv := by
  revert base hmem huniq
  induction cells with
  | nil => intro _ hmem _; exact absurd hmem (by simp)
  | cons p ps ih =>
    intro base hmem huniq
    rcases p with ⟨pi, pv⟩
    by_cases hpi : pi = kk
    · have hpv : pv = vv := by
        have hmem_head : (pi, pv) ∈ (pi, pv) :: ps :=
          List.mem_cons.mpr (Or.inl rfl)
        have h := huniq (pi, pv) hmem_head hpi
        rw [hpi] at h; exact congrArg Prod.snd h
      rw [show pi = kk from hpi, show pv = vv from hpv, overrideCells_cons]
      -- Goal: overrideCells (fun j => if j = kk then vv else base j) ps kk = vv
      -- Apply ih with new base = (fun j => if j = kk then vv else base j)
      -- Need: (kk, vv) ∈ ps OR ps has no cell at kk (base' kk = vv directly)
      by_cases hps : ∃ q ∈ ps, q.1 = kk
      · obtain ⟨q, hq_mem, hq_kk⟩ := hps
        have hq_eq : q = (kk, vv) := huniq q (List.mem_cons_of_mem _ hq_mem) hq_kk
        apply ih (base := fun j => if j = kk then vv else base j)
        · rwa [← hq_eq]
        · intro r hr_mem hr_kk
          exact huniq r (List.mem_cons_of_mem _ hr_mem) hr_kk
      · push_neg at hps
        rw [overrideCells_eq_base_at _ ps kk (by
          intro q hqmem hqne
          exact hps q hqmem hqne)]
        simp
    · rw [overrideCells_cons_index_ne _ pi kk pv ps hpi]
      apply ih
      · simp only [List.mem_cons] at hmem
        rcases hmem with heq | h
        · -- heq : (pi, pv) = (kk, vv), but hpi : pi ≠ kk → contradiction
          have := congrArg Prod.fst heq
          simp at this
          exact absurd this.symm hpi
        · exact h
      · intro q hqmem hqkk
        exact huniq q (List.mem_cons_of_mem _ hqmem) hqkk

/-- If every write lies strictly outside `[lo, hi]`, the overlay agrees with `base` on that interval. -/
theorem overrideCells_eq_base_on_Icc (base : InfTape) (cells : List (ℕ × Bool)) (lo hi : ℕ)
    (hdisj : ∀ p ∈ cells, p.1 < lo ∨ hi < p.1) :
    ∀ j, lo ≤ j → j ≤ hi → overrideCells base cells j = base j := by
  revert base hdisj
  induction cells with
  | nil =>
    intro base _disj j _hj_lo _hj_hi
    rfl
  | cons q qs ih =>
    intro base hdisj j hj_lo hj_hi
    rcases q with ⟨i0, b0⟩
    simp only [List.mem_cons, forall_eq_or_imp] at hdisj
    rcases hdisj with ⟨hdq, htail⟩
    let base' := fun k => if k = i0 then b0 else base k
    have hn_ij : j ≠ i0 := by
      rcases hdq with hlt | hgt
      · exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt hj_lo)).symm
      · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hj_hi hgt)
    have hqs := ih base' htail j hj_lo hj_hi
    simp only [overrideCells_cons]
    rw [hqs]
    simp [base', hn_ij]

/-- Cook ether as an `InfTape`, convenient for glider-overlay experiments. -/
abbrev etherTape : InfTape := cookEther

/-! ## Glider configurations (Milestone 3)

A **`GliderConfig`** is a finite patch of cells to be overlaid on the ether background at a given
spatial origin. It bundles:

* A `CookGliderRef` naming the species.
* A `origin : ℕ` — leftmost cell of the patch on the global tape.
* A `bits : List Bool` — the explicit cell values of the glider patch (length = glider width in cells).

Placing a config on the ether background means overriding cells at positions
`[origin, origin + bits.length)` with the patch values.

**Design note:** Cook's encoding is phase-sensitive. The `phase` field carries the construction-relevant
phase offset (mod `etherPeriod` = 14) allowing downstream collision lemmas to match against
`CookUpPhase` / `CookOverPhase` data in `CookCollisionTaxonomy`.
-/

/-- A Cook glider placed at a specific position on the global ether tape. -/
structure GliderConfig where
  /-- Species and width classification from Figure 5. -/
  species : CookGliderRef
  /-- Leftmost cell index on the global tape where this glider's patch starts. -/
  origin : ℕ
  /-- Phase offset mod 14 (the ether period) at which this glider rides the ether. -/
  phase : Fin 14
  /-- Explicit boolean pattern for the glider's cells (length = glider patch width). -/
  bits : List Bool

/-- Lay a single glider config as an ordered list of `(index, value)` cell overrides. -/
def GliderConfig.toCells (gc : GliderConfig) : List (ℕ × Bool) :=
  (List.range gc.bits.length).map (fun j => (gc.origin + j, gc.bits.getD j false))

theorem GliderConfig.toCells_fst_lt (gc : GliderConfig) {i : ℕ} {b : Bool}
    (h : (i, b) ∈ gc.toCells) : i < gc.origin + gc.bits.length := by
  simp only [GliderConfig.toCells, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, heq⟩ := h
  have heqi : i = gc.origin + j := by cases heq; rfl
  rw [heqi]
  omega

/-- Place a list of glider configs atop the ether background.
    Head config wins on overlap (it is overlaid last). -/
def gliders_to_tape : List GliderConfig → InfTape
  | []          => cookEther
  | gc :: rest  => overrideCells (gliders_to_tape rest) gc.toCells

@[simp] theorem gliders_to_tape_nil : gliders_to_tape [] = cookEther := rfl

@[simp] theorem gliders_to_tape_cons (gc : GliderConfig) (rest : List GliderConfig) :
    gliders_to_tape (gc :: rest) = overrideCells (gliders_to_tape rest) gc.toCells := rfl

/-- Appending cell lists is associative for `overrideCells` (last-write-wins respects append). -/
theorem overrideCells_append (base : InfTape) (l1 l2 : List (ℕ × Bool)) :
    overrideCells base (l1 ++ l2) = overrideCells (overrideCells base l1) l2 := by
  induction l1 generalizing base with
  | nil => simp [overrideCells]
  | cons hd t ih =>
    simp only [List.cons_append]
    exact ih _

theorem gliders_to_tape_eq_reverse_flatMap (gcs : List GliderConfig) :
    gliders_to_tape gcs =
      overrideCells cookEther (gcs.reverse.flatMap GliderConfig.toCells) := by
  induction gcs with
  | nil => simp [gliders_to_tape_nil]
  | cons gc rest ih =>
    rw [gliders_to_tape_cons, List.reverse_cons, List.flatMap_append, List.flatMap_singleton,
        overrideCells_append, ih]

end Rule110
