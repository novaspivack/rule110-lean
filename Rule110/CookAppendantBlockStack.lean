import Rule110.CookBlockData
import Rule110.CyclicTagSystem

/-!
# Cook appendant block stack (§1.4)

Right-hand periodic block sequence for a CTS appendant:
* `Y` (`true`) → `I,I`
* `N` (`false`) → `I,J`
* First `I` in a non-empty appendant → `K,H`
* First `K` moved to the end (Cook `extract_blocks.py`)

Spatial row-0 placements scaffold the blocks contiguously from `cook_appendant_field_origin`.
-/

namespace Rule110

inductive CookAppendantBlock
  | I | J | K | H | L
  deriving DecidableEq, Repr

def cookAppendantBlockRow0 : CookAppendantBlock → List Bool
  | .I => cookIBlockRow0
  | .J => cookJBlockRow0
  | .K => cookKBlockRow0
  | .H => cookHBlockRow0
  | .L => cookLBlockRow0

def cookAppendantBlockWidth : CookAppendantBlock → ℕ
  | _ => 30

theorem cookAppendantBlockRow0_length (b : CookAppendantBlock) :
    (cookAppendantBlockRow0 b).length = match b with
    | .I => 222
    | .J => 252
    | .K => 338
    | .H => 236
    | .L => 235 := by
  cases b <;> native_decide

/-- Symbol pairs before first-`I` replacement. -/
def cook_appendant_ij_symbols (app : List Bool) : List CookAppendantBlock :=
  app.foldl (fun acc b =>
    acc ++ (if b then [.I, .I] else [.I, .J])) []

private def cook_replace_first_i_with_kh (blocks : List CookAppendantBlock) : List CookAppendantBlock :=
  match blocks with
  | [] => []
  | .I :: rest => [.K, .H] ++ rest
  | b :: rest => b :: cook_replace_first_i_with_kh rest

private def cook_move_first_k_to_end (blocks : List CookAppendantBlock) : List CookAppendantBlock :=
  match blocks with
  | [] => []
  | [.K] => [.K]
  | .K :: rest => rest ++ [.K]
  | b :: rest => b :: cook_move_first_k_to_end rest

/-- Cook block stack for appendant `app` (empty → `[L]`). -/
def cook_appendant_block_stack (app : List Bool) : List CookAppendantBlock :=
  if app.length = 0 then
    [.L]
  else
    cook_move_first_k_to_end (cook_replace_first_i_with_kh (cook_appendant_ij_symbols app))

def cook_min_len6_appendant_local : List Bool := List.replicate 6 false

theorem cook_len6_block_stack_length :
    (cook_appendant_block_stack cook_min_len6_appendant_local).length = 13 := by
  native_decide

theorem cook_len6_block_stack_ends_with_k :
    (cook_appendant_block_stack cook_min_len6_appendant_local).getLast? = some .K := by
  native_decide

theorem cook_appendant_block_stack_len6_M :
    (cook_appendant_block_stack cook_min_len6_appendant_local).length * 30 = 390 := by
  native_decide

end Rule110
