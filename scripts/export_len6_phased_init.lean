import Lean
import Rule110.CookLen6AppendantSim

open Lean IO Rule110

def boolToJson : Bool → Json := fun b => Json.bool b

def listBoolToJson (l : List Bool) : Json :=
  Json.arr <| l.toArray.map boolToJson

def main : IO Unit := do
  let path := System.FilePath.mk "len6_true_phased_support_init.json"
  let json := listBoolToJson len6TruePhasedSupportInit
  FS.writeFile path (toString json.pretty)
  IO.println s!"Wrote {path} ({len6TruePhasedSupportInit.length} cells)"
