import Rule110.CookGliderCatalog

/-!
# Cook–Neary–Woods collision taxonomy (cluster-level)

Matthew Cook’s §3 formalizes *relative* collision classification:
two-body collisions depend on discrete phase data (“ր-distance” mod **6**,
“⌢-distance” mod **4**) rather than on species labels alone.

Neary & Woods’ exposition (*A Concrete View of Rule 110 Computation*, CSP 2008;
arXiv:0906.3248) lists the **finite set of collision kinds** used in the cyclic-tag
simulation (§2, bullet list on pp. 40–41 of the arXiv PDF text extraction):

1. ossifiers hitting moving data or invisibles  
2. tape data passing through moving data or invisibles  
3. tape data hitting a prepared leader  
4. acceptor/rejector hitting table data  
5. acceptor/rejector hitting a raw leader  

They also repeat Cook’s cross-product formula for **how many** relative collision classes
two periodic particles admit in the ether background.

This module encodes:

* the **construction collision kinds** as an inductive type (documentation + bookkeeping);
* `Fin 6` / `Fin 4` as the official phase mods for **A-family × Ē** and **C2 × Ē**
  (Cook §3.2.1–3.2.2);
* arithmetic consequences of Cook’s cross-product rule for the standard pairs
  \((A,\bar E)\), \((C2,\bar E)\), \((A,B)\).

No lemmas here assert outcomes of `infTapeStep` on explicit finite patches — that is
the separate simulation layer targeted by SPEC 069.
-/

namespace Rule110

/-- Discrete phase parameter for collisions involving Ē-periodicity in Cook’s “ր” sense (mod 6). -/
abbrev CookUpPhase := Fin 6

/-- Discrete phase parameter for collisions involving Ē-periodicity in Cook’s “⌢” sense (mod 4). -/
abbrev CookOverPhase := Fin 4

/-- Cluster-level collision kinds referenced in Neary–Woods arXiv:0906.3248 §2. -/
inductive CookConstructionCollisionKind where
  /-- Ossifiers vs moving data / invisibles (their Fig. 6–8 narrative). -/
  | ossifier_meets_moving_or_invisible
  /-- Tape (`C2`) vs moving data / invisibles (their Fig. 5–6(e)–10 narrative). -/
  | tape_passes_through_moving_or_invisible
  /-- One tape cell vs prepared leader (their Fig. 11(v)–(y)). -/
  | tape_hits_prepared_leader
  /-- Acceptor/rejector vs table data (their Fig. 7). -/
  | acceptor_rejector_meets_table
  /-- Acceptor/rejector vs raw leader (their Fig. 9). -/
  | acceptor_rejector_meets_raw_leader

/-! ### Cook’s cross-product collision-class count -/

/-- Cook §3.1: number of relative collision classes for periods `(pa,pb)` and `(qa,qb)` in ω-units. -/
def cookCollisionClassCount (pa pb qa qb : ℤ) : ℕ :=
  Int.natAbs (pa * qb - pb * qa)

theorem cookCollisionClassCount_A_B :
    cookCollisionClassCount 1 0 0 1 = 1 := by
  rfl

/-- Six relative positions for an `A4` vs `Ē` interaction (Cook Fig. 6; §3.2.1). -/
theorem cookCollisionClassCount_A4_Ebar :
    cookCollisionClassCount 1 0 2 6 = 6 := by
  rfl

/-- Four relative positions for `C2` vs `Ē` (Cook Fig. 9; §3.2.2). -/
theorem cookCollisionClassCount_C2_Ebar :
    cookCollisionClassCount 1 1 2 6 = 4 := by
  rfl

/-! Alignment with `CookGliderCatalog` -/

theorem cookCollisionClassCount_named_agrees_A_Ebar :
    cookCollisionClassCount
      (CookNamedGlider.periodAB .A).ωA (CookNamedGlider.periodAB .A).ωB
      (CookNamedGlider.periodAB .Ebar).ωA (CookNamedGlider.periodAB .Ebar).ωB
      = 6 := by
  rfl

theorem cookCollisionClassCount_named_agrees_C2_Ebar :
    cookCollisionClassCount
      (CookNamedGlider.periodAB .C2).ωA (CookNamedGlider.periodAB .C2).ωB
      (CookNamedGlider.periodAB .Ebar).ωA (CookNamedGlider.periodAB .Ebar).ωB
      = 4 := by
  rfl

/-- Neary–Woods highlight: ossification uses the `A4`–`Ē` reaction with **ր-5** spacing (their §2). -/
def OssificationUpPhase : CookUpPhase := ⟨5, by decide⟩

end Rule110
