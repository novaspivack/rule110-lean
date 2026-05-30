import Mathlib.Data.List.Basic

import Rule110.CookGliderCatalog

set_option maxRecDepth 10000

/-!
# Martinez Rule 110 glider phase catalog

Source: Genaro J. Martinez, `listPhasesR110.txt` (ESCOM IPN, September 2004).
URL: http://comunidad.escom.ipn.mx/genaro/rule110/listPhasesR110.txt

Complete ingestion of all phase-encoded glider strings from Martinez's catalog:
365 source bit patterns plus 29 resolved f4_1 alias entries = 394 total.
Families: ether, A, B, B-, B^, C1-C3, D1-D2, E, E-, F, G, H, Gun.

**Coordinate note:** Martinez strings embed gliders in the Martinez ether basis
`e(f1_1) = [11111000100110]`. The Cook/`cookEther` coordinate system uses
`10011011111000` (period 14). Dynamic verification on `cookEther` is in
`MartinezPhasesVerification.lean`; this module is reference data only.
-/

namespace Rule110

/-! ### Type hierarchy -/

inductive MartinezGliderFamily where
  | ether | A | B | Bminus | Bhat
  | C1 | C2 | C3 | D1 | D2
  | E | Eminus | F | G | H | Gun
  deriving DecidableEq

inductive MartinezParent where
  | none | A | B | C | D | E | F | G | H
  | A2 | B2 | C2p | D2p | E2 | F2 | G2 | H2
  | A3 | B3 | C3p | D3 | E3 | F3 | G3 | H3 | A4
  deriving DecidableEq

inductive MartinezPhaseIdx where | f1_1 | f2_1 | f3_1 | f4_1
  deriving DecidableEq

structure MartinezKey where
  family : MartinezGliderFamily
  parent : MartinezParent
  phase : MartinezPhaseIdx
  deriving DecidableEq

structure MartinezPhaseEntry where
  bits : List Bool
  ncells : Nat
  leftTiles : Option Nat
  rightTiles : Option Nat
  family : MartinezGliderFamily
  parent : MartinezParent
  phase : MartinezPhaseIdx
  deriving DecidableEq

def MartinezPhaseEntry.key (e : MartinezPhaseEntry) : MartinezKey :=
  ⟨e.family, e.parent, e.phase⟩

def martinezCatalogSourceCount : Nat := 365

def martinezCatalogAliasCount : Nat := 29

def martinezCatalogLength : Nat := 394

/-! ### Computable lookup (394 pattern arms) -/

def martinezEntry (key : MartinezKey) : Option MartinezPhaseEntry :=
  match key with
  | ⟨MartinezGliderFamily.ether, MartinezParent.none, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false], 14, none, none, MartinezGliderFamily.ether, MartinezParent.none, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false], 6, some 1, some 0, MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, false, true, true, false], 20, some 2, some 3, MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false], 20, some 3, some 2, MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false], 8, some 1, some 1, MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false], 8, some 2, some 0, MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 22, some 3, some 3, MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, false, true, true, false], 8, some 0, some 2, MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, false, false, true, true, false], 22, some 1, some 0, MartinezGliderFamily.Bminus, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, false, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 36, some 2, some 3, MartinezGliderFamily.Bminus, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, false, false, true, false, true, true, true, true, false, false, false, true, false, false, true, true, false], 36, some 3, some 2, MartinezGliderFamily.Bminus, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.B, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false], 22, some 0, some 1, MartinezGliderFamily.B, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false, false, true, false, true, true, false], 22, some 1, some 0, MartinezGliderFamily.Bminus, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 36, some 2, some 3, MartinezGliderFamily.Bminus, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false, true, false, false, true, true, false], 36, some 3, some 2, MartinezGliderFamily.Bminus, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false], 22, some 0, some 1, MartinezGliderFamily.Bminus, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false, false, false], 22, some 1, some 0, MartinezGliderFamily.Bminus, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, false, false, true, true, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 36, some 2, some 3, MartinezGliderFamily.Bminus, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, false, true, true, true, true, true, false, true, true, true, false, false, true, true, false], 36, some 3, some 2, MartinezGliderFamily.Bminus, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Bminus, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, false, true, true, false, false, false, true, true, true, false, true, false], 22, some 0, some 1, MartinezGliderFamily.Bminus, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, false, false, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 39, some 1, some 3, MartinezGliderFamily.Bhat, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, false, false, true, false, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 39, some 2, some 2, MartinezGliderFamily.Bhat, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, false, false, true, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, false], 39, some 3, some 1, MartinezGliderFamily.Bhat, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, false, false], 22, some 0, some 0, MartinezGliderFamily.Bhat, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 39, some 1, some 3, MartinezGliderFamily.Bhat, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, false, false, true, true, false], 39, some 2, some 2, MartinezGliderFamily.Bhat, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false, false, false, false, true, true, true, false, true, false], 39, some 3, some 1, MartinezGliderFamily.Bhat, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, false, false, false, false, true, true, false], 22, some 0, some 0, MartinezGliderFamily.Bhat, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 39, some 1, some 3, MartinezGliderFamily.Bhat, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, false, false, false, true, true, false, true, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 39, some 2, some 2, MartinezGliderFamily.Bhat, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false], 39, some 3, some 1, MartinezGliderFamily.Bhat, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Bhat, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, false, true, true, false, false, false, true, false, false, false, true, true, false, true, false], 22, some 0, some 0, MartinezGliderFamily.Bhat, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false], 9, some 1, some 0, MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 23, some 2, some 3, MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, false, true, true, false], 23, some 3, some 2, MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, false], 9, some 0, some 1, MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 23, some 1, some 3, MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false, true, false, false, true, true, false], 23, some 2, some 2, MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, false, false, true, true, false], 23, some 3, some 1, MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, false, false, true, false, false, true, true, false], 17, some 1, some 2, MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, false, false, true, true, false], 17, some 2, some 1, MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false], 17, some 3, some 0, MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 17, some 0, some 3, MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false], 17, some 1, some 2, MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, true, false], 17, some 2, some 1, MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 31, some 3, some 3, MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, false, true, false], 17, some 1, some 1, MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 31, some 2, some 3, MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false, true, false, false, true, true, false], 31, some 3, some 2, MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, false, false, false, false, true, true, false], 17, some 0, some 1, MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, false], 17, some 1, some 0, MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 31, some 2, some 3, MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true, false, false, true, true, false], 31, some 3, some 2, MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false], 11, some 1, some 1, MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], 25, some 2, some 3, MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, true, false, false, true, true, false], 25, some 3, some 2, MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, true, true, false], 11, some 0, some 1, MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 25, some 1, some 3, MartinezGliderFamily.D1, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, false, true, false, false, true, true, false], 25, some 2, some 2, MartinezGliderFamily.D1, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true, false], 25, some 3, some 1, MartinezGliderFamily.D1, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, false], 11, some 1, some 0, MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, false], 25, some 2, some 3, MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false], 25, some 3, some 2, MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, false], 19, some 1, some 3, MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, false, true, true, false], 19, some 2, some 2, MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, true, false], 19, some 3, some 1, MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], 19, some 0, some 3, MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, false, true, false, false, true, true, false], 19, some 1, some 2, MartinezGliderFamily.D2, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, false], 19, some 2, some 1, MartinezGliderFamily.D2, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 33, some 3, some 3, MartinezGliderFamily.D2, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, false, false, false, true, false, false, true, true, false], 19, some 1, some 2, MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, true, true, false], 19, some 2, some 1, MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false], 19, some 3, some 0, MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, false, false, false, false, true, false, false, true, true, false], 19, some 1, some 2, MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, false, false, false, false, true, true, false], 19, some 2, some 1, MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false], 19, some 3, some 0, MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 19, some 0, some 3, MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, false, true, true, true, false, false, true, true, false], 19, some 1, some 2, MartinezGliderFamily.E, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false, true, false], 19, some 2, some 1, MartinezGliderFamily.E, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 33, some 3, some 3, MartinezGliderFamily.E, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 19, some 1, some 2, MartinezGliderFamily.E, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, false], 19, some 2, some 1, MartinezGliderFamily.E, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false], 19, some 3, some 0, MartinezGliderFamily.E, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 19, some 0, some 3, MartinezGliderFamily.E, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.D, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, false, true, true, true, false, false, true, true, false], 19, some 1, some 2, MartinezGliderFamily.E, MartinezParent.D, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.D, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false, true, false], 19, some 2, some 1, MartinezGliderFamily.E, MartinezParent.D, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.D, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, true, true, false], 19, some 3, some 0, MartinezGliderFamily.E, MartinezParent.D, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.D, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 19, some 0, some 3, MartinezGliderFamily.E, MartinezParent.D, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, true, true, false, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, true, false, false, false], 21, some 2, some 0, MartinezGliderFamily.Eminus, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 35, some 3, some 3, MartinezGliderFamily.Eminus, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, true, true, false, true, false, true, true, true, false, false, true, true, false], 21, some 0, some 2, MartinezGliderFamily.Eminus, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, false, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, false], 21, some 2, some 0, MartinezGliderFamily.Eminus, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 35, some 3, some 3, MartinezGliderFamily.Eminus, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, true, true, false, true, true, true, false, false, true, true, false], 21, some 0, some 2, MartinezGliderFamily.Eminus, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, false, false, true, true, true, false, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false], 21, some 2, some 0, MartinezGliderFamily.Eminus, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 35, some 3, some 3, MartinezGliderFamily.Eminus, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], 21, some 0, some 2, MartinezGliderFamily.Eminus, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.D, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false, true, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.D, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.D, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, true, false, true, true, false], 21, some 2, some 0, MartinezGliderFamily.Eminus, MartinezParent.D, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.D, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 35, some 3, some 3, MartinezGliderFamily.Eminus, MartinezParent.D, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.D, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, false, true, true, false, false, false, false, true, false, false, true, true, false], 21, some 0, some 2, MartinezGliderFamily.Eminus, MartinezParent.D, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.E, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.E, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.E, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, true, false, false], 21, some 2, some 0, MartinezGliderFamily.Eminus, MartinezParent.E, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.E, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, true, false, false, true, true, false], 35, some 3, some 3, MartinezGliderFamily.Eminus, MartinezParent.E, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, false, true, false], 21, some 2, some 0, MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, false, false, true, true, false], 35, some 3, some 3, MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.G, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.G, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.G, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false], 21, some 2, some 0, MartinezGliderFamily.Eminus, MartinezParent.G, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.G, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 35, some 3, some 3, MartinezGliderFamily.Eminus, MartinezParent.G, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.G, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, false, false, false, false, false, true, false, false, true, true, false], 21, some 0, some 2, MartinezGliderFamily.Eminus, MartinezParent.G, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.H, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, false, false, false, true, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.H, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.H, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, false, false, false], 21, some 2, some 0, MartinezGliderFamily.Eminus, MartinezParent.H, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.H, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 35, some 3, some 3, MartinezGliderFamily.Eminus, MartinezParent.H, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.H, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, true, false, false, true, true, false], 21, some 0, some 2, MartinezGliderFamily.Eminus, MartinezParent.H, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, true, false], 15, some 1, some 1, MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 29, some 2, some 3, MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, false, false, false, false, true, false, false, true, true, false], 29, some 3, some 2, MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, false, false, false, false, true, true, false], 15, some 0, some 1, MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, false, false, false, false], 15, some 1, some 0, MartinezGliderFamily.F, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 29, some 2, some 3, MartinezGliderFamily.F, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, true, true, false], 29, some 3, some 2, MartinezGliderFamily.F, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, false, false, true, true, false, true, false], 15, some 0, some 1, MartinezGliderFamily.F, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 29, some 1, some 3, MartinezGliderFamily.F, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, true, false, false, true, true, false], 29, some 2, some 2, MartinezGliderFamily.F, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false, false, false, false, true, true, false], 29, some 3, some 1, MartinezGliderFamily.F, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, true, true, false, false, false], 15, some 0, some 0, MartinezGliderFamily.F, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.D, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 29, some 1, some 3, MartinezGliderFamily.F, MartinezParent.D, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.D, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, true, true, false, false, true, true, false], 29, some 2, some 2, MartinezGliderFamily.F, MartinezParent.D, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.D, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, true, true, true, true, false, true, false], 29, some 3, some 1, MartinezGliderFamily.F, MartinezParent.D, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.D, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, true, true, true, true, false, false, false], 15, some 0, some 0, MartinezGliderFamily.F, MartinezParent.D, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.E, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 29, some 1, some 3, MartinezGliderFamily.F, MartinezParent.E, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.E, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, false], 29, some 2, some 2, MartinezGliderFamily.F, MartinezParent.E, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.E, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, false, true, true, true, true, true, true, false, true, false], 29, some 3, some 1, MartinezGliderFamily.F, MartinezParent.E, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.E, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, false, true, true, false, false, false, false], 15, some 0, some 0, MartinezGliderFamily.F, MartinezParent.E, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.F, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 29, some 1, some 3, MartinezGliderFamily.F, MartinezParent.F, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.F, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false], 29, some 2, some 2, MartinezGliderFamily.F, MartinezParent.F, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.F, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, false, true, false], 29, some 3, some 1, MartinezGliderFamily.F, MartinezParent.F, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 29, some 1, some 3, MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, false, false, false, false, false, true, false, false, true, true, false], 29, some 2, some 2, MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false, false, false, false, false, true, true, false], 29, some 3, some 1, MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, false, false, false], 15, some 1, some 0, MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 29, some 2, some 3, MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false], 29, some 3, some 1, MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, true, false, true, false], 15, some 1, some 1, MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 29, some 2, some 3, MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, true, false, false, true, true, false], 29, some 3, some 2, MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.B2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, false, false, true, true, false], 15, some 1, some 1, MartinezGliderFamily.F, MartinezParent.B2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.B2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false], 15, some 2, some 0, MartinezGliderFamily.F, MartinezParent.B2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.B2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 29, some 3, some 3, MartinezGliderFamily.F, MartinezParent.B2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, false, false, true, true, false], 15, some 0, some 2, MartinezGliderFamily.F, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, false], 24, some 1, some 1, MartinezGliderFamily.G, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, true, false, true, true, false, true, false], 24, some 2, some 0, MartinezGliderFamily.G, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 38, some 3, some 3, MartinezGliderFamily.G, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, false, true, true, false, false, false, false, false, false, false, true, false, false, true, true, false], 24, some 0, some 2, MartinezGliderFamily.G, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, true, true, true, false, false, false, false, false, false, true, true, false], 24, some 1, some 1, MartinezGliderFamily.G, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false], 24, some 2, some 0, MartinezGliderFamily.G, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, true, false, false, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 38, some 3, some 3, MartinezGliderFamily.G, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, true, false, false, true, true, false], 24, some 0, some 2, MartinezGliderFamily.G, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, true, false, false, true, true, false, true, false], 24, some 1, some 1, MartinezGliderFamily.G, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, false, false, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 38, some 2, some 3, MartinezGliderFamily.G, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, false, false, true, true, false, true, true, true, false, false, false, false, false, true, false, false, true, true, false], 38, some 3, some 2, MartinezGliderFamily.G, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, false, false, true, true, true, true, true, false, true, false, false, false, false, true, true, false], 24, some 0, some 1, MartinezGliderFamily.G, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.D, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, false, false, false, true, true, true, false, false, false], 24, some 1, some 0, MartinezGliderFamily.G, MartinezParent.D, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.D, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 38, some 2, some 3, MartinezGliderFamily.G, MartinezParent.D, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.D, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true, false, true, true, true, false, false, true, true, false], 38, some 3, some 2, MartinezGliderFamily.G, MartinezParent.D, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.D, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, false], 24, some 0, some 1, MartinezGliderFamily.G, MartinezParent.D, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.E, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false], 24, some 1, some 0, MartinezGliderFamily.G, MartinezParent.E, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.E, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 38, some 2, some 3, MartinezGliderFamily.G, MartinezParent.E, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.E, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 38, some 3, some 2, MartinezGliderFamily.G, MartinezParent.E, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.E, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, true, true, false], 24, some 0, some 1, MartinezGliderFamily.G, MartinezParent.E, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.F, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, false, false, false, false, false, true, true, false], 24, some 1, some 0, MartinezGliderFamily.G, MartinezParent.F, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.F, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, true, false, true, false, false, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 28, some 2, some 3, MartinezGliderFamily.G, MartinezParent.F, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.F, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 38, some 3, some 2, MartinezGliderFamily.G, MartinezParent.F, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.F, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, true, true, false, false, false, true, false, false, true, true, true, false, false, true, true, false], 24, some 0, some 1, MartinezGliderFamily.G, MartinezParent.F, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.G, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false], 24, some 1, some 0, MartinezGliderFamily.G, MartinezParent.G, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.G, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 38, some 2, some 3, MartinezGliderFamily.G, MartinezParent.G, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.G, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, false, false, false, false, false, false, true, false, false, true, true, false], 38, some 3, some 2, MartinezGliderFamily.G, MartinezParent.G, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.G, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, true, true, false, true, false, false, false, false, false, false, false, true, true, false], 24, some 0, some 1, MartinezGliderFamily.G, MartinezParent.G, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.H, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, false, false, true, true, true, false, false, false, false, false, false], 24, some 1, some 0, MartinezGliderFamily.G, MartinezParent.H, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.H, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 38, some 2, some 3, MartinezGliderFamily.G, MartinezParent.H, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.H, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, true, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false], 38, some 3, some 2, MartinezGliderFamily.G, MartinezParent.H, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.H, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, true, false, false, false, true, true, false, true, false], 24, some 0, some 1, MartinezGliderFamily.G, MartinezParent.H, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.A2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 38, some 1, some 3, MartinezGliderFamily.G, MartinezParent.A2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.A2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 38, some 2, some 2, MartinezGliderFamily.G, MartinezParent.A2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.A2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, false, true, true, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, false], 38, some 3, some 1, MartinezGliderFamily.G, MartinezParent.A2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.A2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, false, true, true, false, false, false, false, true, true, true, false, false, true, false, false, false], 24, some 0, some 0, MartinezGliderFamily.G, MartinezParent.A2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.B2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false, true, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 38, some 1, some 3, MartinezGliderFamily.G, MartinezParent.B2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.B2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, false, false, true, true, false], 38, some 2, some 2, MartinezGliderFamily.G, MartinezParent.B2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.B2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, false, false, false, true, true, true, false, true, false], 38, some 3, some 1, MartinezGliderFamily.G, MartinezParent.B2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false], 24, some 1, some 0, MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, false, true, false, false, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 38, some 2, some 3, MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false, true, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 38, some 3, some 2, MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 1, some 3, MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, false, false, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 53, some 2, some 2, MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, true, false, false, false, false, false, false, true, true, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, false], 53, some 3, some 1, MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false], 39, some 0, some 0, MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 1, some 3, MartinezGliderFamily.H, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, false, true, false, false, false, true, true, false, false, false, false, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true, true, false, false, true, true, false], 53, some 2, some 2, MartinezGliderFamily.H, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false, true, false], 53, none, none, MartinezGliderFamily.H, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, false, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, true, true, false], 39, some 0, some 0, MartinezGliderFamily.H, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 1, some 3, MartinezGliderFamily.H, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, true, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false, false, false, false, false, true, false, false, true, true, false], 53, some 2, some 2, MartinezGliderFamily.H, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false, false, false, false, false, true, true, true, true, false, true, false, true, true, true, true, true, false, false, false, true, false, false, false, false, false, false, false, true, true, false], 53, some 3, some 1, MartinezGliderFamily.H, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, false, false, false, true, true, true, false, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false, false, true, true, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.F, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false], 39, some 2, some 0, MartinezGliderFamily.H, MartinezParent.F, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 3, some 3, MartinezGliderFamily.H, MartinezParent.F, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, false, false, false, false, false, true, true, false, true, false, false, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true, true, false, false, true, true, false], 39, some 0, some 2, MartinezGliderFamily.H, MartinezParent.F, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, false, false, true, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.G, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, true, false, true, true, false], 39, some 2, some 0, MartinezGliderFamily.H, MartinezParent.G, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, true, false, false, true, true, false, true, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 3, some 3, MartinezGliderFamily.H, MartinezParent.G, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, false, true, false, true, true, true, true, true, false, true, false, true, true, true, true, true, false, false, false, false, false, false, false, false, true, false, false, true, true, false], 39, some 0, some 2, MartinezGliderFamily.H, MartinezParent.G, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, false, false, false, false, false, false, true, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.H, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, false, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false], 39, some 2, some 0, MartinezGliderFamily.H, MartinezParent.H, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 3, some 3, MartinezGliderFamily.H, MartinezParent.H, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, true, true, false, true, false, false, false, false, true, true, true, false, false, true, true, false], 39, some 0, some 2, MartinezGliderFamily.H, MartinezParent.H, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, true, true, true, false, false, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.A2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.A2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.A2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, false], 39, some 0, some 1, MartinezGliderFamily.H, MartinezParent.A2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.B2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.B2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.B2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false, true, false], 39, some 0, some 1, MartinezGliderFamily.H, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C2p, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, false, true, true, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, true, true, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.C2p, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C2p, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.C2p, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C2p, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, false, false, true, true, true, false, true, true, true, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false, false, false, false, false, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.C2p, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C2p, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, false, false, true, false, false, false, false, false, false, false, true, true, false], 39, some 0, some 1, MartinezGliderFamily.H, MartinezParent.C2p, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D2p, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.D2p, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D2p, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.D2p, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D2p, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false, false, true, true, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.D2p, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D2p, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, true, true, false, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false, true, false], 39, some 0, some 1, MartinezGliderFamily.H, MartinezParent.D2p, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, false, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 1, some 3, MartinezGliderFamily.H, MartinezParent.E2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 53, some 2, some 2, MartinezGliderFamily.H, MartinezParent.E2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, true, false, false, false, false, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, false], 53, some 3, some 1, MartinezGliderFamily.H, MartinezParent.E2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, true, true, false, true, true, true, false, false, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false], 39, some 0, some 0, MartinezGliderFamily.H, MartinezParent.E2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 1, some 3, MartinezGliderFamily.H, MartinezParent.F2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true, true, false, false, true, true, false], 53, some 2, some 2, MartinezGliderFamily.H, MartinezParent.F2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, false, true, false], 53, some 3, some 1, MartinezGliderFamily.H, MartinezParent.F2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, false, true, true, false], 39, some 0, some 0, MartinezGliderFamily.H, MartinezParent.F2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 1, some 3, MartinezGliderFamily.H, MartinezParent.G2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, false, true, true, true, true, true, false, false, false, false, false, false, false, false, true, false, false, true, true, false], 53, some 2, some 2, MartinezGliderFamily.H, MartinezParent.G2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, false, true, true, true, true, true, true, false, false, false, true, false, true, true, false, false, false, true, true, true, false, false, false, true, false, false, false, false, false, false, false, true, true, false], 53, some 3, some 1, MartinezGliderFamily.H, MartinezParent.G2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, false, true, true, false, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false, false, true, true, false, false, false, false, false, false], 39, some 0, some 0, MartinezGliderFamily.H, MartinezParent.G2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false, true, true, false, false, false, true, false, true, true, true, true, true, false, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 1, some 3, MartinezGliderFamily.H, MartinezParent.H2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false, false, false, false, true, true, true, false, false, true, true, false], 53, some 2, some 2, MartinezGliderFamily.H, MartinezParent.H2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false, true, false], 53, some 3, some 1, MartinezGliderFamily.H, MartinezParent.H2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 1, some 3, MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, false, true, false, false, true, true, false, false, false, true, true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 53, some 2, some 2, MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false, true, true, false, true, true, true, false, false, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false], 53, some 3, some 1, MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false, true, true, true, true, true, false, false, true, false, false, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.B3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, false, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.B3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, true, false, false, false, true, false, false, true, true, true, true, true, false, true, true, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.B3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.B3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, false, false, false, true, true, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, true, false, true, false], 39, some 0, some 1, MartinezGliderFamily.H, MartinezParent.B3, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C3p, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, false, true, true, false, true, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, false, false, true, true, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.C3p, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C3p, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, false, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.C3p, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C3p, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, true, true, true, false, false, false, false, false, true, false, false, true, true, true, true, false, false, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.C3p, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C3p, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, false, true, false, true, true, false, false, true, true, false, false, true, false, false, true, true, false], 39, some 0, some 1, MartinezGliderFamily.H, MartinezParent.C3p, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.D3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.D3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.D3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, true, true, true, true, true, false, true, false, false, false, true, true, false], 39, some 0, some 1, MartinezGliderFamily.H, MartinezParent.D3, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, false, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.E3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.E3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.E3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, false, true, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.G3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, true, false, false, true, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.G3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, true, false, false, false, true, true, false, true, false, false, false, false, true, true, false, true, true, true, false, true, true, true, true, true, false, false, false, false, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.G3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.G3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, true, false, false, false, true, false, false, false, true, true, false], 39, some 0, some 1, MartinezGliderFamily.H, MartinezParent.G3, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, true, false, false, true, true, false, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.H3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.H3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false, false, true, false, true, true, true, true, true, false, true, false, true, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false], 53, some 3, some 2, MartinezGliderFamily.H, MartinezParent.H3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A4, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.A4, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A4, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 2, some 3, MartinezGliderFamily.H, MartinezParent.A4, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A4, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, false, true, false, false, true, true, false], 53, none, none, MartinezGliderFamily.H, MartinezParent.A4, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A4, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, false], 39, some 0, some 1, MartinezGliderFamily.H, MartinezParent.A4, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, true, true, false, false, true, true, true, false, true, false, false, true, true, false, false, true, false, true, true, true, true, true, false, false, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.A, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.A, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, false, true, true, false, false, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.A, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.A, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.B, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, true, false, false, true, true, true, true, true, false, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.B, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, true, false, false, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.B, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, true, true, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.C, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.C, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.C, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false, true, false, true, true, false, false, false, false, false], 27, none, none, MartinezGliderFamily.Gun, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.D, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, false, true, false, false, false, true, true, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.D, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, true, true, false, false, true, true, false, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.D, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, false, false, false, false, false, true, true, false, false, false, false, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.D, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.E, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, false, false, false, true, true, true, false, false, false, true, true, false, true, true, true, false, false, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.E, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.E, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false, false, true, true, true, true, true, false, true, false, false, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.E, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.E, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, true, true, true, false, true, true, false, false, false, true, true, true, false, false, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.E, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.E, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.E, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.F, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, true, true, true, false, false, true, true, false, false, true, false, true, true, true, true, true, false, true, true, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.F, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.F, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.F, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.F, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.F, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.F, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.F, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.G, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.G, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.G, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, true, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.G, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.G, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, true, false, false, false, false, true, false, false, false, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.G, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.G, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, false, false, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.G, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.H, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, false, false, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.H, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.H, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false, true, false, false, true, true, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.H, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.H, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.H, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.H, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.H, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false, true, true, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.A2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.A2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, false, true, true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, true, false, false, false, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.A2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, false, true, true, false, false, false, false, true, false, false, true, true, false, false, true, true, true, true, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.A2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, false, true, true, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.B2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, true, true, true, true, false, false, true, true, false, true, true, false, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.B2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, true, true, true, false, false, true, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 55, none, none, MartinezGliderFamily.Gun, MartinezParent.B2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false, false, false, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, false, false, true, false, false, false, false, false, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D2p, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.D2p, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D2p, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, false, true, true, false, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.D2p, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D2p, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, false, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.D2p, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D2p, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.D2p, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.E2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.E2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.E2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.E2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.E2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, false, false, false, false, true, false, false, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.E2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.E2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, false, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.E2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.F2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.F2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.F2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, false, true, true, true, false, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.F2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.F2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, false, true, false, false, true, true, false, false, false, true, true, true, true, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.F2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.F2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, false, true, true, true, false, false, false, true, false, true, true, false, true, true, true, false, false, true, true, false, false, false, false, true, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.F2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.G2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.G2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.G2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, true, true, false, false, false, false, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.G2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.G2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, true, false, false, false, true, true, true, false, false, false, true, false, false, true, true, false], 55, none, none, MartinezGliderFamily.Gun, MartinezParent.G2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.G2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, true, true, true, true, true, false, false, true, false, false, false, true, true, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.G2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.H2, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, true, true, false, false, false, true, false, true, true, false, false, true, true, false, true, false, true, true, true, true, true, false, false, true, false], 35, none, none, MartinezGliderFamily.Gun, MartinezParent.H2, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.H2, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.H2, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.H2, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, true, false, false, false, true, true, true, false, false, false, false, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.H2, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.H2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, false, false, true, true, true, true, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, false, true, false, true, true, false], 35, none, none, MartinezGliderFamily.Gun, MartinezParent.H2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.A3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, true, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, true, true, true, false, false, false, false, false, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.A3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, false, true, false, true, true, false, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false, true, false, false, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.A3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.A3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, false], 35, none, none, MartinezGliderFamily.Gun, MartinezParent.A3, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, true, true, true, false, false, false, true, true, true, false, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.B3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, true, true, true, false, false, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, true, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.B3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true, false, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.B3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C3p, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false], 35, none, none, MartinezGliderFamily.Gun, MartinezParent.C3p, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C3p, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false, false, true, true, true, false, true, true, false, false, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.C3p, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C3p, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, true, false, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, false, true, true, false, false, true, false, true, true, false, true, true, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.C3p, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C3p, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false], 35, none, none, MartinezGliderFamily.Gun, MartinezParent.C3p, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, false, true, true, true, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false], 35, none, none, MartinezGliderFamily.Gun, MartinezParent.D3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D3, MartinezPhaseIdx.f2_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false, false, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.D3, MartinezPhaseIdx.f2_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D3, MartinezPhaseIdx.f3_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, false, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.D3, MartinezPhaseIdx.f3_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.D3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, false, false, true, true, false, false, false, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, false, false, true, false, false, true, true, false, true, false], 35, none, none, MartinezGliderFamily.Gun, MartinezParent.D3, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.E3, MartinezPhaseIdx.f1_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, true, true, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 49, none, none, MartinezGliderFamily.Gun, MartinezParent.E3, MartinezPhaseIdx.f1_1⟩
  | ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false], 6, some 1, some 0, MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 23, some 1, some 3, MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, false, false, true, true, false], 17, some 1, some 2, MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, false], 17, some 1, some 0, MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, false], 11, some 1, some 0, MartinezGliderFamily.D1, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false], 11, some 1, some 1, MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, false, false, false, true, false, false, true, true, false], 19, some 1, some 2, MartinezGliderFamily.D2, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, false], 19, some 1, some 3, MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.E, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, true, false], 19, some 1, some 2, MartinezGliderFamily.E, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.E, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.E, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false], 21, some 1, some 1, MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.F, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 29, some 1, some 3, MartinezGliderFamily.F, MartinezParent.F, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, false, false, false], 15, some 1, some 0, MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, true, true, false, true, false], 15, some 1, some 1, MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, false, false, true, true, false], 15, some 1, some 1, MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false], 24, some 1, some 0, MartinezGliderFamily.G, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, false], 24, some 1, some 1, MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.C, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, false, false, false, false, false, false, true, true, false, false, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.C, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false], 53, some 1, some 3, MartinezGliderFamily.H, MartinezParent.H2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false, true, true, true, true, true, false, false, true, false, false, false], 39, some 1, some 0, MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.E3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, true, false, false, false, false, false, false, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.E3, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false, false, true, true, true, false, true, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.H, MartinezParent.H3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, true, false], 39, some 1, some 1, MartinezGliderFamily.H, MartinezParent.H3, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, false, false, false, true, true, true, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.B, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false, false, false, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], 41, none, none, MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f4_1⟩
  | ⟨MartinezGliderFamily.Gun, MartinezParent.B3, MartinezPhaseIdx.f4_1⟩ =>
    some ⟨[true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false], 35, none, none, MartinezGliderFamily.Gun, MartinezParent.B3, MartinezPhaseIdx.f4_1⟩
  | _ => none

def martinezEntry? (key : MartinezKey) : Option MartinezPhaseEntry := martinezEntry key

@[simp] theorem martinezEntry?_eq (key : MartinezKey) : martinezEntry? key = martinezEntry key := rfl

theorem martinezCatalog_length : martinezCatalogLength = 394 := rfl

/-! ### Martinez ether reference -/

def martinezEtherBits : List Bool :=
  [true, true, true, true, true, false, false, false, true, false, false, true, true, false]

theorem martinezEther_length : martinezEtherBits.length = 14 := by decide

theorem martinezEther_matches_catalog :
    (martinezEntry? ⟨MartinezGliderFamily.ether, MartinezParent.none, MartinezPhaseIdx.f1_1⟩).map (·.bits) =
      some martinezEtherBits := by
  native_decide

/-! ### A-glider core bridge to Cook catalog -/

theorem martinez_A_f1_1_eq_cookAGliderBits :
    (martinezEntry? ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f1_1⟩).map (·.bits) =
      some cookAGliderBits := by
  native_decide

theorem martinez_C2_A_f1_1_tile_metadata :
    (martinezEntry? ⟨MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).map (·.leftTiles) = some (1 : Nat) ∧
    (martinezEntry? ⟨MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).map (·.rightTiles) = some (2 : Nat) := by
  native_decide

/-! ### Phase aliases (29 identifications; f4_1 entries included in catalog) -/

theorem martinez_alias_0_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_1_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.C1, MartinezParent.B, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_2_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.C2, MartinezParent.B, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_3_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.C3, MartinezParent.B, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_4_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.D1, MartinezParent.B, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_5_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.D1, MartinezParent.C, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_6_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.D2, MartinezParent.B, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_7_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.D2, MartinezParent.C, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_8_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.E, MartinezParent.B, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.E, MartinezParent.C, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_9_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.Eminus, MartinezParent.E, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_10_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.Eminus, MartinezParent.F, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.Eminus, MartinezParent.G, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_11_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.F, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_12_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.G, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_13_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.H, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_14_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.A2, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.B2, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_15_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.G, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_16_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.G, MartinezParent.C2p, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.G, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_17_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.C, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_18_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.D, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_19_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.E, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.F, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_20_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.H2, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_21_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.A3, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.B3, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_22_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.E3, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_23_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.F3, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.G3, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_24_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.H3, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.A4, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_25_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.Gun, MartinezParent.B, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.Gun, MartinezParent.C, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_26_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.Gun, MartinezParent.B2, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_27_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.Gun, MartinezParent.C2p, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.Gun, MartinezParent.D2p, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

theorem martinez_alias_28_bits_eq :
    (martinezEntry? ⟨MartinezGliderFamily.Gun, MartinezParent.B3, MartinezPhaseIdx.f4_1⟩).map (·.bits) =
      (martinezEntry? ⟨MartinezGliderFamily.Gun, MartinezParent.C3p, MartinezPhaseIdx.f1_1⟩).map (·.bits) := by
  native_decide

/-! ### Cook Figure 5 family presence -/

theorem martinez_cook_family_A :
    (martinezEntry? ⟨MartinezGliderFamily.A, MartinezParent.none, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

theorem martinez_cook_family_B :
    (martinezEntry? ⟨MartinezGliderFamily.B, MartinezParent.none, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

theorem martinez_cook_family_C1 :
    (martinezEntry? ⟨MartinezGliderFamily.C1, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

theorem martinez_cook_family_C2 :
    (martinezEntry? ⟨MartinezGliderFamily.C2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

theorem martinez_cook_family_C3 :
    (martinezEntry? ⟨MartinezGliderFamily.C3, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

theorem martinez_cook_family_D1 :
    (martinezEntry? ⟨MartinezGliderFamily.D1, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

theorem martinez_cook_family_D2 :
    (martinezEntry? ⟨MartinezGliderFamily.D2, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

theorem martinez_cook_family_Ebar :
    (martinezEntry? ⟨MartinezGliderFamily.E, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

theorem martinez_cook_family_F :
    (martinezEntry? ⟨MartinezGliderFamily.F, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

theorem martinez_cook_family_H :
    (martinezEntry? ⟨MartinezGliderFamily.H, MartinezParent.A, MartinezPhaseIdx.f1_1⟩).isSome = true := by
  native_decide

def martinezFamilyCount : Nat := 16

end Rule110
