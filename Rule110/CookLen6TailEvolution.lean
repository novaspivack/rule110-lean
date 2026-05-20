import Rule110.CookLen6AppendantSim

set_option maxRecDepth 100000 in

/-!
# L=6 tail evolution certificates (Stage 3)

Bounded list simulation after `M₁ = 390` steps from the `[true]` phased encode:
does the evolved tape agree with the post-step mid-encode on Icc windows?

**Negative (Icc, `M₂ = 30`):** full 61-cell agreement fails — same obstruction class as C3′.
**Positive (origin only):** slot-origin cells agree after 390 steps.
-/

namespace Rule110

def len6TailEvolvedList : List Bool :=
  c2SimRun 390 len6TruePhasedSupportInit

def len6TailMidList : List Bool :=
  len6PostAppendantPhasedSupportInit

/-- Icc agreement (`M₂ = 30`) between evolved and mid lists on slots 0–5. -/
def len6TailEvolutionIcc30Ok : Bool :=
  (List.range 6).all fun slot =>
    (List.range 61).all fun d =>
      let j := cts_slot_origin slot - 30 + d
      decide (len6TailEvolvedList.getD j false = len6TailMidList.getD j false)

/-- **Negative witness:** post-390 evolved vs mid disagree on at least one Icc cell. -/
theorem len6_tail_evolution_icc30_not_ok : len6TailEvolutionIcc30Ok = false := by
  native_decide

/-- Origin-cell agreement only (weaker; discharged). -/
def len6TailEvolutionOriginOk : Bool :=
  (List.range 6).all fun slot =>
    decide (len6TailEvolvedList.getD (c2SimOrigin slot) false =
      len6TailMidList.getD (c2SimOrigin slot) false)

theorem len6_tail_evolution_origin_ok : len6TailEvolutionOriginOk = true := by
  native_decide

end Rule110
