import Mathlib.Data.Fin.Basic

/-!
# Rule 110 lookup table

Matches `UgpLean.Universality.Rule110`: Wolfram code 110.
-/

namespace Rule110

/-- Rule 110: Wolfram code 110. Output for each of 8 neighborhoods.
Index convention: `val = 4·l + 2·c + r` with `l,c,r : Bool` (`false` = 0). -/
def rule110Output (i : Fin 8) : Bool :=
  match i.val with
  | 0 => false   -- 000
  | 1 => true    -- 001
  | 2 => true    -- 010
  | 3 => true    -- 011
  | 4 => false   -- 100
  | 5 => true    -- 101
  | 6 => true    -- 110
  | _ => false   -- 111

/-- Neighborhood index from three Booleans (left, center, right). -/
def neighborhoodIndex (l c r : Bool) : Fin 8 :=
  ⟨4 * l.toNat + 2 * c.toNat + r.toNat, by
    rcases l <;> rcases c <;> rcases r <;> decide⟩

end Rule110
