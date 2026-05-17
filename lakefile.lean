import Lake
open Lake DSL

package «Rule110» where
  -- Cyclic tag systems, Rule 110 ether, and (eventually) Cook TM→Rule 110 encoding.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib «Rule110» where
