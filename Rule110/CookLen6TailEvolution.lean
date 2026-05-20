import Rule110.CookLen6AppendantSim
import Rule110.CookLen6InfTapeBridge
import Rule110.InfTape

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

/-- **Tail-origin (`M₂ = 30`):** after post-390 evolved tape, 30 more list steps match mid path. -/
def len6TailOrigin30Ok : Bool :=
  let evolved30 := c2SimRun 30 len6TailEvolvedList
  let mid30 := c2SimRun 30 len6TailMidList
  (List.range 6).all fun slot =>
    decide (evolved30.getD (c2SimOrigin slot) false = mid30.getD (c2SimOrigin slot) false)

theorem len6_tail_origin30_ok : len6TailOrigin30Ok = true := by
  native_decide

/-- **Tail-origin (`M₂ = 30`) on full Icc** around each slot (stronger). -/
def len6TailOriginIcc30Ok : Bool :=
  let evolved30 := c2SimRun 30 len6TailEvolvedList
  let mid30 := c2SimRun 30 len6TailMidList
  (List.range 6).all fun slot =>
    (List.range 61).all fun d =>
      let j := cts_slot_origin slot - 30 + d
      decide (evolved30.getD j false = mid30.getD j false)

theorem len6_tail_origin_icc30_not_ok : len6TailOriginIcc30Ok = false := by
  native_decide

/-- **420-step list certificate:** `M₁ + M₂` from init vs `M₂` from mid at origins (`M₁=390`, `M₂=30`). -/
def len6Tail420OriginOk : Bool :=
  let fin420 := c2SimRun 420 len6TruePhasedSupportInit
  let mid30 := c2SimRun 30 len6TailMidList
  (List.range 6).all fun slot =>
    decide (fin420.getD (c2SimOrigin slot) false = mid30.getD (c2SimOrigin slot) false)

theorem len6_tail420_origin_ok : len6Tail420OriginOk = true := by
  native_decide

/-- List composition `420 = 390 + 30` at slot origins (feeds InfTape lift). -/
def len6Tail420ComposeOriginOk : Bool :=
  (List.range 6).all fun slot =>
    decide ((c2SimRun 420 len6TruePhasedSupportInit).getD (c2SimOrigin slot) false =
      (c2SimRun 30 (c2SimRun 390 len6TruePhasedSupportInit)).getD (c2SimOrigin slot) false)

theorem len6_tail420_compose_origin_ok : len6Tail420ComposeOriginOk = true := by
  native_decide

@[simp] theorem len6TailEvolvedList_length :
    len6TailEvolvedList.length = len6TruePhasedSupportInit.length :=
  c2SimRun_length _ _

@[simp] theorem len6TailMidList_length :
    len6TailMidList.length = len6PostAppendantPhasedSupportInit.length := rfl

end Rule110
