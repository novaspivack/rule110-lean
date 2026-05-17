# rule110-lean

Lean 4 library for SPEC_069_C1R (Cook TM → Rule 110 pipeline): cyclic tag systems, Rule 110 on a one-sided infinite tape, and the Cook ether background.

## Toolchain

Matches `ugp-lean` / `ugp-lean-exp`: Lean `v4.29.1`, Mathlib `v4.29.1` (see `lakefile.lean`).

## Contents

| Module | Status |
|--------|--------|
| `Rule110.Basic` | Rule 110 lookup (`rule110Output`, `neighborhoodIndex`). |
| `Rule110.InfTape` | `InfTape`, `infTapeStep`, `infRule110Steps` (same semantics as `HypothesisB`). |
| `Rule110.CyclicTagSystem` | `CyclicTagSystem`, `cts_step`, `cts_steps`, `cts_eval`, bounds + appendant-index mod lemmas + `cts_computes`. |
| `Rule110.Ether` | Period‑14 Cook ether, periodicity, `ether_stable_phase` / `ether_stable_under_rule110` (shift by 4). |
| `Rule110.CookGliderCatalog` | Figure 5 reference table: widths, `(Δt,Δx)`, `(ω_A,ω_B)` (named + indexed families). |
| `Rule110.CookCollisionTaxonomy` | Neary–Woods (arXiv [0906.3248](https://arxiv.org/abs/0906.3248)) §2 collision-kind enum + Cook §3.1 cross-product counts (`Fin 6` / `Fin 4`). |
| `Rule110.Gliders` | `CookGliderRef`, `overrideCells` overlays on `InfTape`. |
| `Rule110.TMtoCTS` | `TMCTSCompilation` — Milestone 4 correctness bundle (witness TBD). |
| `Rule110.CTStoRule110` | Ether baseline + `ctsTapeWithOverrides` — Milestone 3 scaffolding. |

Primary PDF for numeric transcription: Cook (2004) via Wolfram mirror
[15-1-1.pdf](https://content.wolfram.com/sites/13/2018/02/15-1-1.pdf). Do **not** use `arxiv:cs/0401007` for Cook — that ID is unrelated.

## Milestone status (SPEC_069)

| Milestone | Status |
|-----------|--------|
| **1** CTS core | **Advancing** — length bounds + `(cts_steps …).snd = (idx+n)%cycle` when tape stays nonempty. |
| **2** Ether + gliders | **Scaffolding** — overlays/refs added; collision lemmas vs `infTapeStep` still open. |
| **3** CTS ↦ dynamics | Baseline tape helpers only. |
| **4** TM ↦ CTS | `TMCTSCompilation` interface only (no Mathlib `TM2` witness yet). |
| **5** UGP chain | `gte_in_rule110_sim_ax` removal blocked until Milestones 3–4. |

## Integration

`ugp-lean-exp` depends on this package (`lakefile.lean`: `".." / "rule110-lean"`) and imports `UgpLean.Universality.CookRule110Ref` from `HypothesisB.lean`.

## Build

```bash
lake build
```
