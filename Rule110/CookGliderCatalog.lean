import Rule110.Ether

/-!
# Cook’s Rule 110 glider catalog (Figure 5)

Source: Matthew Cook, *Universality in Elementary Cellular Automata*,
Complex Systems **15** (1), 2004, pp. 1–40
(Wolfram mirror PDF https://content.wolfram.com/sites/13/2018/02/15-1-1.pdf ),
Figure 5.

Cook’s caption: **width** is the ether-offset mod **14** between left and right ether;
**period** is a `(Δt, Δx)` pair; the final column gives coefficients \((ω_A, ω_B)\) with
respect to the primitive periods \(ω_A\) (for `A`) and \(ω_B\) (for `B`).

Indexed rows \(\bar B_n\), \(\hat B_n\), \(E_n\), \(G_n\) use Cook’s affine formulas in the
width column; their `(Δt, Δx)` and \((ω_A, ω_B)\) entries are **independent of `n`**
in Figure 5.

This module is reference data for `CookCollisionTaxonomy.lean`; it does not prove CA dynamics.
-/

namespace Rule110

/-- Horizontal displacement `(Δt, Δx)` for one complete period. -/
structure PeriodTX where
  dt : ℤ
  dx : ℤ

 /-- Coefficients `(ω_A, ω_B)` for one period in Cook’s ω-units (Figure 5, last column). -/
structure PeriodAB where
  ωA : ℤ
  ωB : ℤ

/-! ### Named gliders (Figure 5, fixed rows) -/

inductive CookNamedGlider where
  | A | B | C1 | C2 | C3 | D1 | D2 | Ebar | F | H

/-- Width column (integer representative of the class mod 14). -/
def CookNamedGlider.widthNat : CookNamedGlider → ℕ
  | .A => 6
  | .B => 8
  | .C1 => 9
  | .C2 => 3
  | .C3 => 11
  | .D1 => 11
  | .D2 => 5
  | .Ebar => 7
  | .F => 1
  | .H => 11

/-- Period `(Δt, Δx)` column. -/
def CookNamedGlider.periodTX : CookNamedGlider → PeriodTX
  | .A => ⟨3, 2⟩
  | .B => ⟨4, -2⟩
  | .C1 => ⟨7, 0⟩
  | .C2 => ⟨7, 0⟩
  | .C3 => ⟨7, 0⟩
  | .D1 => ⟨10, 2⟩
  | .D2 => ⟨10, 2⟩
  | .Ebar => ⟨30, -8⟩
  | .F => ⟨36, -4⟩
  | .H => ⟨92, -18⟩

/-- `(ω_A, ω_B)` coefficients. -/
def CookNamedGlider.periodAB : CookNamedGlider → PeriodAB
  | .A => ⟨1, 0⟩
  | .B => ⟨0, 1⟩
  | .C1 => ⟨1, 1⟩
  | .C2 => ⟨1, 1⟩
  | .C3 => ⟨1, 1⟩
  | .D1 => ⟨2, 1⟩
  | .D2 => ⟨2, 1⟩
  | .Ebar => ⟨2, 6⟩
  | .F => ⟨4, 6⟩
  | .H => ⟨8, 17⟩

/-! ### Indexed families -/

inductive CookIndexedGlider where
  | Bbar | Bhat | En | Gn

/-- Affine width formulas from Figure 5 (`13+9n`, `2+9n`, `11+8n`, `2+8n`). -/
def CookIndexedGlider.widthNat : CookIndexedGlider → ℕ → ℕ
  | .Bbar, n => 13 + 9 * n
  | .Bhat, n => 2 + 9 * n
  | .En, n => 11 + 8 * n
  | .Gn, n => 2 + 8 * n

/-- `(Δt, Δx)` for each family (independent of `n` in Figure 5). -/
def CookIndexedGlider.periodTX : CookIndexedGlider → PeriodTX
  | .Bbar => ⟨12, -6⟩
  | .Bhat => ⟨12, -6⟩
  | .En => ⟨15, -4⟩
  | .Gn => ⟨42, -14⟩

/-- `(ω_A, ω_B)` for each family (independent of `n` in Figure 5). -/
def CookIndexedGlider.periodAB : CookIndexedGlider → PeriodAB
  | .Bbar => ⟨0, 3⟩
  | .Bhat => ⟨0, 3⟩
  | .En => ⟨1, 3⟩
  | .Gn => ⟨2, 9⟩

theorem CookNamedGlider.width_A_add_B_mod_etherPeriod :
    (CookNamedGlider.widthNat .A + CookNamedGlider.widthNat .B) % etherPeriod = 0 := by
  rfl

/-! ### Verified C-glider cell patterns (6 cells each, period 7, velocity 0)

Extracted by organic emergence (random IC → long warmup → identify stationary period-7
disturbances). Each glider is 6 cells wide. The `bits` row below is phase 0 of the 7-phase
cycle; `left_phase` (0-based index into `cookEther`) is the ether phase immediately to the
glider's left.

Ether coordinate system: `cookEther i = cookEtherBits ⟨i % 14, _⟩` = `10011011111000` (period 14).

| Glider | Cook width | left_phase | phase-0 bits |
|--------|-----------|------------|--------------|
| C2     | 3          | 2          | `110001`     |
| C1     | 9          | 12         | `110000`     |
| C3     | 11         | 12         | `011111`     |

All three are the SAME 7-cycle of states, sampled at different starting phases:
  canonical 7-cycle: 110001, 010011, 110110, 011111, 110000, 010000, 110000
  C2 starts at phase 0, C1 at phase 4, C3 at phase 3 of this cycle.
  (Cook's subscripts encode the ether alignment to the left, not a distinct object.)

Cross-reference: Cook (2004) §3, Figure 4; Neary–Woods arXiv:0906.3248 §2.
-/

/-- The canonical 7-phase C-glider cycle (phase-0 through phase-6).
    Each entry is the 6-cell bit pattern at that time step.
    `false` = 0, `true` = 1. -/
def cookCGliderCycle : Fin 7 → List Bool
  | ⟨0, _⟩ => [true,  true,  false, false, false, true]   -- 110001
  | ⟨1, _⟩ => [false, true,  false, false, true,  true]   -- 010011
  | ⟨2, _⟩ => [true,  true,  false, true,  true,  false]  -- 110110
  | ⟨3, _⟩ => [false, true,  true,  true,  true,  true]   -- 011111
  | ⟨4, _⟩ => [true,  true,  false, false, false, false]  -- 110000
  | ⟨5, _⟩ => [false, true,  false, false, false, false]  -- 010000
  | ⟨6, _⟩ => [true,  true,  false, false, false, false]  -- 110000

/-- C2 phase-0 bits (Cook width 3, left ether phase 2 in our `cookEther` coordinate). -/
def cookC2Bits : List Bool := cookCGliderCycle ⟨0, by decide⟩

/-- C1 phase-0 bits (Cook width 9, left ether phase 12 in our `cookEther` coordinate). -/
def cookC1Bits : List Bool := cookCGliderCycle ⟨4, by decide⟩

/-- C3 phase-0 bits (Cook width 11, left ether phase 12 in our `cookEther` coordinate). -/
def cookC3Bits : List Bool := cookCGliderCycle ⟨3, by decide⟩

theorem cookC2Bits_length : cookC2Bits.length = 6 := by decide
theorem cookC1Bits_length : cookC1Bits.length = 6 := by decide
theorem cookC3Bits_length : cookC3Bits.length = 6 := by decide

end Rule110
