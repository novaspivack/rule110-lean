import Rule110.CyclicTagSystem

/-!
# Cook (2008) M and ossifier-spacing formulas

Mirrors `scripts/cook_m_values.py`. Bool appendants use `true` = Y, `false` = N.
-/

namespace Rule110

def cts_appendant_count_Y (app : List Bool) : ℕ :=
  app.filter id |>.length

def cts_appendant_count_N (app : List Bool) : ℕ :=
  app.length - cts_appendant_count_Y app

/-- Vertical ossifier spacing v (Cook 2008, §1.4). -/
def cook_ossifier_v (appendants : List (List Bool)) : ℕ :=
  let total_Y := appendants.foldl (fun acc a => acc + cts_appendant_count_Y a) 0
  let total_N := appendants.foldl (fun acc a => acc + cts_appendant_count_N a) 0
  let nonempty := (appendants.filter (fun a => 0 < a.length)).length
  let empty := (appendants.filter (fun a => a.length = 0)).length
  76 * total_Y + 80 * total_N + 60 * nonempty + 43 * empty

theorem cook_ossifier_v_empty_appendant :
    cook_ossifier_v [[]] = 43 := by native_decide

theorem cook_ossifier_v_len6_false :
    cook_ossifier_v [List.replicate 6 false] = 540 := by native_decide

theorem cook_ossifier_v_empty_and_len6 :
    cook_ossifier_v [[], List.replicate 6 false] = 583 := by native_decide

end Rule110
