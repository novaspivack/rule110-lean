import Rule110.CookMFormula
import Rule110.CTStoRule110

/-!
# Cook (2008) M / v formula verification (`scripts/cook_m_values.py` parity)

Machine-checked reference values for the Python calculator table and example cycle.
-/

namespace Rule110

/-- Sum of per-appendant M over one full CTS cycle. -/
def cook_cycle_M_sum (appendants : List (List Bool)) : ℕ :=
  appendants.foldl (fun acc a => acc + cook_M_for_appendant_len a.length) 0

/-! ### Reference table (Python `__main__` L → M) -/

theorem cook_M_len0_verify : cook_M_for_appendant_len 0 = 30 := rfl

theorem cook_M_len24_verify : cook_M_for_appendant_len 24 = 1470 := by native_decide

theorem cook_M_len30_verify : cook_M_for_appendant_len 30 = 1830 := by native_decide

theorem cook_M_len60_verify : cook_M_for_appendant_len 60 = 3630 := by native_decide

theorem cook_M_formula_table :
    cook_M_for_appendant_len 0 = 30 ∧
      cook_M_for_appendant_len 6 = 390 ∧
        cook_M_for_appendant_len 12 = 750 ∧
          cook_M_for_appendant_len 18 = 1110 ∧
            cook_M_for_appendant_len 24 = 1470 ∧
              cook_M_for_appendant_len 30 = 1830 ∧
                cook_M_for_appendant_len 60 = 3630 := by
  repeat' constructor <;> native_decide

/-! ### Python example: `["YYYYYY", "", "NNNNNN", ""]` -/

def cook_python_example_appendants : List (List Bool) :=
  [List.replicate 6 true, [], List.replicate 6 false, []]

theorem cook_v_python_example :
    cook_ossifier_v cook_python_example_appendants = 1142 := by
  native_decide

theorem cook_cycle_M_python_example :
    cook_cycle_M_sum cook_python_example_appendants = 840 := by
  native_decide

theorem cook_python_example_per_appendant_M :
    cook_M_for_appendant_len (cook_python_example_appendants[0]!).length = 390 ∧
      cook_M_for_appendant_len (cook_python_example_appendants[1]!).length = 30 ∧
        cook_M_for_appendant_len (cook_python_example_appendants[2]!).length = 390 ∧
          cook_M_for_appendant_len (cook_python_example_appendants[3]!).length = 30 := by
  repeat' constructor <;> native_decide

end Rule110
