# rule110-lean

A Lean 4 formalization of Matthew Cook's proof that **Rule 110 is computationally universal** — specifically, the construction that embeds cyclic tag systems (and through them, arbitrary Turing machines) into the glider dynamics of Rule 110 on an infinite tape.

The library is self-contained and has no UGP-specific content. It is designed to be reusable by anyone working with Rule 110, cellular automaton universality, or Lean formalizations of computational models.

## Background

**Rule 110** is a one-dimensional elementary cellular automaton: at each discrete time step every cell updates its binary state based on itself and its two nearest neighbors, according to the rule

| Left · Center · Right | 111 | 110 | 101 | 100 | 011 | 010 | 001 | 000 |
|-----------------------|-----|-----|-----|-----|-----|-----|-----|-----|
| **Output**            |  0  |  1  |  1  |  0  |  1  |  1  |  1  |  0  |

Despite this simplicity, Rule 110 is **Turing-complete**. This was conjectured by Stephen Wolfram in 1985 and proved by Matthew Cook while assisting Wolfram on research for *A New Kind of Science*. The proof, published in *Complex Systems* 15(1) in 2004, proceeds in two hops:

1. **TM → Cyclic Tag System.** Any Turing machine can be simulated by a cyclic tag system, a simple string-rewriting machine whose only operation at each step is to optionally append a fixed binary string to the front of its working tape.

2. **CTS → Rule 110.** Rule 110 exhibits a periodic background pattern called the *ether* (spatial period 14, temporal period 7), through which localized finite structures called *gliders* propagate and collide. Cook showed that specific glider collision sequences faithfully simulate every step of any cyclic tag system. Because cyclic tag systems are already universal, Rule 110 is universal.

This library formalizes the mathematical infrastructure for Cook's construction in Lean 4, building toward a fully machine-verified proof.

## What is proved (zero sorry)

| Component | Theorem | Statement |
|-----------|---------|-----------|
| **CTS core** | `cts_step`, `cts_steps`, `cts_eval` | Semantics of cyclic tag systems |
| | `cts_step_length_le` | Each CTS step grows the word by at most `totalAppendantChars` |
| | `cts_steps_snd_eq_idx_add_mod` | Appendant cursor advances mod `cycleLen` on nonempty traces |
| **Ether** | `ether_stable_phase` | One Rule 110 step on `cookEther` equals `cookEther(i + 4)` |
| | `infRule110Steps_cookEther_shift` | `n` steps: `cookEther(i + 4n)` whenever `n ≤ i` |
| | Three spot-check `native_decide` theorems | Numerical regression anchors |
| **InfTape locality** | `infRule110Steps_agree_Icc` | Matching initial data on cone `[i−n, i+n]` implies equal output |
| | `infRule110Steps_shiftInfTape_four` | Shift by 4 intertwines with `n` Rule 110 steps (boundary-isolated) |
| **Overlay locality** | `overrideCells_eq_base_on_Icc` | Writes outside `[lo,hi]` are invisible inside `[lo,hi]` |
| | `ctsTapeWithOverrides_infRule110Steps_eq_shift_of_disjoint` | Payload outside the backwards cone ⇒ observer sees unperturbed ether drift |
| **Stage 1** | `cook_cts_step_sim_ax` | Far-field ether drift after M steps (theorem; was axiom) |
| | `cook_c2_tape_bit_ax` | InfTape C1 decode for arbitrary words, slots 0–20 (`CookC2GeneralC1`) |
| | `cook_c2_tape_bit_min_word` | InfTape decode after 30 steps for isolated min-word (slots 0–20) |
| | `cook_c2_tape_bit_sim_witness` | Bounded C2 read slots 0–20 via `native_decide` |
| **Stage 2 (partial)** | `OssifierGlider` | A-type catalog linkage, block A rows, `cts_ossifier_glider` scaffold |
| | `LeaderGlider` | Ē-type catalog linkage, L-block row 0, `cts_leader_glider` scaffold |
| | `CookBlockData` | Cook block A/L bit patterns from PNG extraction |
| **C-glider patterns** | `cookCGliderCycle` | Verified 7-phase cycle for C1/C2/C3 gliders |
| | `cookC1/C2/C3Bits_length` | Each glider is 6 cells wide |
| **Two-phase ether** | `phaseEther_zero` | Zero accumulated shift reduces to `cookEther` |
| | `gliders_to_tape_phased_nil` | Empty glider list produces the standard ether |

## C-glider patterns (verified)

All three C-class gliders (Cook §3) are the *same* 7-phase cycle of cell patterns, distinguished only by which phase of the surrounding ether aligns to their left — exactly as Cook states: "the subscripts for C and D gliders indicate different alignments of the ether to the left."

Ether unit cell (period 14): `10011011111000`  
Glider cycle (phases 0–6):

| Phase | Bits |
|-------|------|
| 0 | `110001` |
| 1 | `010011` |
| 2 | `110110` |
| 3 | `011111` |
| 4 | `110000` |
| 5 | `010000` |
| 6 | `110000` |

| Glider | Cook width | Left ether phase | Starts at cycle phase |
|--------|-----------|------------------|-----------------------|
| **C2** | 3          | 2                | 0 (`110001`)          |
| **C1** | 9          | 12               | 4 (`110000`)          |
| **C3** | 11         | 12               | 3 (`011111`)          |

Patterns extracted by organic emergence (random initial conditions → long Rule 110 evolution → identification of stationary period-7 disturbances) and independently cross-checked.

## Module overview

| Module | Contents |
|--------|----------|
| `Rule110.Basic` | Rule 110 local update function and neighborhood indexing |
| `Rule110.InfTape` | `InfTape = ℕ → Bool`, `infTapeStep`, `infRule110Steps`; shift and cone lemmas |
| `Rule110.Ether` | Period-14 Cook ether; one-step and multi-step shift theorems |
| `Rule110.CyclicTagSystem` | `CyclicTagSystem`, step/eval/halts semantics; determinism and length bounds |
| `Rule110.CookGliderCatalog` | Cook Figure 5 reference data (widths, periods, ω-coefficients); verified C-glider bit patterns |
| `Rule110.CookCollisionTaxonomy` | Neary–Woods §2 collision-kind enumeration; Cook §3.1 cross-product counts |
| `Rule110.Gliders` | `GliderConfig` (species, origin, phase, bits); `gliders_to_tape`; overlay utilities |
| `Rule110.CTStoRule110` | Two-phase ether infrastructure (`GliderPlacement`, `accumPhaseAt`, `gliders_to_tape_phased`, `c2CyclePhase`); CTS-word-to-glider encoding; explicit collision axioms |
| `Rule110.TMtoCTS` | `TMCTSCompilation` interface for the TM → CTS reduction |
| `Rule110.CookC2BoundedSim` | Bounded list simulator; C2 read witness slots 0–20 |
| `Rule110.CookC2InfTapeBridge` | `listToInfTape`; decode alignment with `tape_has_glider_at` |
| `Rule110.CookStage1Verification` | Stage 1 summary re-exports |

## Status toward full universality proof

| Milestone | Description | Status |
|-----------|-------------|--------|
| **M1** | CTS: semantics, bounds, appendant-index tracking | **Complete** (zero sorry) |
| **M2** | Ether: periodicity, multi-step shift, C-glider patterns | **Complete** (zero sorry) |
| **M3** | CTS → Rule 110: two-phase tape, phase-correct C2 placement, collision axioms | **Partial** — C1 and C2 discharged; global C3 operational targets remain axiomatic |
| **M4** | TM → CTS: explicit witness + correctness proof | **Partial** — `CookFinTM2Compiles (idComputer Bool)` proved; general Cook encoding open |
| **M5** | Full chain assembly; `#print axioms` clean | **Open** |

Named bridge claims in `Rule110.CTStoRule110` and related modules:
- `cook_c2_tape_bit_ax` — general multi-glider word (**discharged** in `CookC2GeneralC1`, slots 0–20)
- `cook_cts_step_sim_ax` — one CTS step = M Rule 110 steps (**discharged** as theorem, far-field)
- `cook_cts_eval_sim_ax` — legacy full-tape n-step simulation (**open**; refuted at empty n=1; use C3′′/phased targets in `CookStage3Induction`)
- `CookFinTM2Compiles (idComputer Bool)` — Mathlib identity machine (**discharged** in `CookFinTM2Compilation`)

## Toolchain

Lean `v4.29.1`, Mathlib `v4.29.1` (see `lakefile.lean`).

```bash
lake update
lake build
```

## References

- Cook, M. (2004). Universality in Elementary Cellular Automata. *Complex Systems* **15**(1), 1–40. DOI [10.25088/ComplexSystems.15.1.1](https://doi.org/10.25088/ComplexSystems.15.1.1). PDF mirror: [content.wolfram.com/sites/13/2018/02/15-1-1.pdf](https://content.wolfram.com/sites/13/2018/02/15-1-1.pdf) *(Original universality proof; source of the glider catalog, Figure 4/5, and §3–4 collision taxonomy.)*

- Cook, M. (2008/2009). A Concrete View of Rule 110 Computation. *EPTCS* **1**, 31–55. DOI [10.4204/EPTCS.1.4](https://doi.org/10.4204/EPTCS.1.4). arXiv: [0906.3248](https://arxiv.org/abs/0906.3248) *(Explicit compiler from Turing machine to Rule 110 initial state; provides exact step counts M = 30·(2L+1) per CTS step for appendant length L, and the ossifier-spacing formula v = 76·Y + 80·N + 60·(nonempty) + 43·(empty). **Primary reference for `scripts/cook_m_values.py` and the `cook_cts_step_sim_ax` step counts.)*

## Third-party assets

The block PNG images in `blocks/` (files `A.png` through `L.png`) and the block-extraction approach in `scripts/extract_blocks.py` are derived from the open-source repository:

> **inexxt/rule_110** — *From arbitrary Turing Machines to Rule 110 in Python*  
> https://github.com/inexxt/rule_110 (MIT-style; no explicit license file)

That repository implements Cook's 2004/2009 construction in Python and provides PNG images of the 12 block diagrams (Figures 1 and 2 of Cook 2009), extracted from Cook's paper. The images are reproduced here for use in Lean formalization work. If the original images are subject to copyright from Cook's paper, that claim belongs to the original authors; these assets are used here under fair use for academic research purposes.

The `symbols_to_bits.py` phase-propagation logic in that repository informed the implementation of `scripts/extract_blocks.py`.

- Wolfram, S. (2002). *A New Kind of Science.* Wolfram Media. *(Contains Wolfram's original conjecture about Rule 110 universality.)*

- Wolfram, S. (1983). Statistical Mechanics of Cellular Automata. *Reviews of Modern Physics* **55**, 601–644. *(Introduced the Wolfram numbering scheme for elementary cellular automata.)*

- Wolfram, S. (1984). Universality and Complexity in Cellular Automata. *Physica D* **10**, 1–35. *(Conjectured that class-4 cellular automata might be capable of universal computation.)*

- Wolfram, S. (1985). Undecidability and Intractability in Theoretical Physics. *Physical Review Letters* **54**, 735–738.

- Neary, T. and Woods, D. (2009). A Concrete View of Rule 110 Computation. *Proceedings of Computability in Europe (CiE 2009)*, Lecture Notes in Computer Science. arXiv: [0906.3248](https://arxiv.org/abs/0906.3248). *(Provides an explicit compiler from Turing machines to Rule 110 initial states; used for the Neary–Woods §2 collision taxonomy in this library.)*

- Minsky, M. (1972). *Computation: Finite and Infinite Machines.* Prentice-Hall. *(Tag systems and Turing machines, cited by Cook [10].)*

- Cocke, J. (1964). Universality of Tag Systems With P = 2. *Journal of the ACM* **11**(1), 15–20. *(Tag systems are universal; cited by Cook [12].)*

- Post, E. (studied tag systems ca. 1921; cited by Cook [11].)

- Smith, A.R. III (1971). Simple Computation-Universal Cellular Spaces. *Journal of the ACM* **18**(3), 339–353. *(Earlier universal one-dimensional cellular automata; cited by Cook [4].)*

- Wolfram, S. (1986). *Theory and Applications of Cellular Automata.* World Scientific. *(Contains Doug Lind's glider table for Rule 110, cited by Cook [13]; the table lists all common gliders including C1, C2, C3, D1, D2, A, B, Ē, E, F, G.)*

