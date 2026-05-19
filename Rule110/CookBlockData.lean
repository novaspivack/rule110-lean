import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Rule110

/-! Block bit patterns extracted from Cook (2009) PNGs via `scripts/extract_blocks.py`.
Regenerate: `python3 scripts/gen_cook_block_data.py`. -/

def cookABlockRow : Fin 3 → List Bool
  | ⟨0, _⟩ => [false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true]
  | ⟨1, _⟩ => [false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true]
  | ⟨2, _⟩ => [false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true]

theorem cookABlockRow_length (t : Fin 3) : (cookABlockRow t).length = 28 := by
  fin_cases t <;> native_decide

def cookLBlockRow0 : List Bool :=
  [true, false, false, false, false, false, true, true, false, false, false, false, false, true, false, false, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false, true, true, false, false, true, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, false, true, false, false, false, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true]

theorem cookLBlockRow0_length : cookLBlockRow0.length = 235 := by native_decide

def cookLBlockPeriod : ℕ := 30

theorem cookLBlockPeriod_eq : cookLBlockPeriod = 30 := rfl

def cookKBlockRow0 : List Bool :=
  [true, false, false, false, false, false, true, true, false, false, false, false, false, true, false, false, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false, true, true, false, false, true, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, false, true, true, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, true, true, false, false]

theorem cookKBlockRow0_length : cookKBlockRow0.length = 338 := by native_decide

def cookKBlockPeriod : ℕ := 30

theorem cookKBlockPeriod_eq : cookKBlockPeriod = 30 := rfl

end Rule110
