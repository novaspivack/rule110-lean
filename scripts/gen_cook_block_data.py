#!/usr/bin/env python3
"""Regenerate Rule110/CookBlockData.lean from scripts/cook_blocks.json."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
JSON_PATH = ROOT / "scripts" / "cook_blocks.json"
OUT_PATH = ROOT / "Rule110" / "CookBlockData.lean"


def bool_list(row: list[int]) -> str:
    return ", ".join("true" if b else "false" for b in row)


def main() -> None:
    data = json.loads(JSON_PATH.read_text())
    lines = [
        "import Mathlib.Data.Fin.Basic",
        "import Mathlib.Tactic",
        "",
        "namespace Rule110",
        "",
        "/-! Block bit patterns extracted from Cook (2009) PNGs via `scripts/extract_blocks.py`.",
        "Regenerate: `python3 scripts/gen_cook_block_data.py`. -/",
        "",
        "def cookABlockRow : Fin 3 → List Bool",
    ]
    for i, row in enumerate(data["A"]["rows"]):
        lines.append(f"  | ⟨{i}, _⟩ => [{bool_list(row)}]")
    lines += [
        "",
        "theorem cookABlockRow_length (t : Fin 3) : (cookABlockRow t).length = 28 := by",
        "  fin_cases t <;> native_decide",
        "",
        "def cookLBlockRow0 : List Bool :=",
        f"  [{bool_list(data['L']['rows'][0])}]",
        "",
        "theorem cookLBlockRow0_length : cookLBlockRow0.length = 235 := by native_decide",
        "",
        "def cookLBlockPeriod : ℕ := 30",
        "",
        "theorem cookLBlockPeriod_eq : cookLBlockPeriod = 30 := rfl",
        "",
        "def cookKBlockRow0 : List Bool :=",
        f"  [{bool_list(data['K']['rows'][0])}]",
        "",
        "theorem cookKBlockRow0_length : cookKBlockRow0.length = 338 := by native_decide",
        "",
        "def cookKBlockPeriod : ℕ := 30",
        "",
        "theorem cookKBlockPeriod_eq : cookKBlockPeriod = 30 := rfl",
        "",
        "def cookIBlockRow0 : List Bool :=",
        f"  [{bool_list(data['I']['rows'][0])}]",
        "",
        "theorem cookIBlockRow0_length : cookIBlockRow0.length = 222 := by native_decide",
        "",
        "def cookJBlockRow0 : List Bool :=",
        f"  [{bool_list(data['J']['rows'][0])}]",
        "",
        "theorem cookJBlockRow0_length : cookJBlockRow0.length = 252 := by native_decide",
        "",
        "end Rule110",
        "",
    ]
    OUT_PATH.write_text("\n".join(lines))
    print(f"Wrote {OUT_PATH} ({len(lines)} lines)")


if __name__ == "__main__":
    main()
