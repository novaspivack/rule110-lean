import Rule110.CookLen6InfTapeBridge
open Rule110 IO

def main : IO Unit := do
  let evolved := c2SimRun 390 len6TruePhasedSupportInit
  let path := System.FilePath.mk "len6_evolved390.json"
  let json := "[" ++ String.intercalate "," (evolved.map fun b => if b then "true" else "false") ++ "]"
  FS.writeFile path json
  println s!"Wrote {path} ({evolved.length} cells)"
