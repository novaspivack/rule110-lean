import Rule110.CookStage3CollisionModel
import Rule110.CookStage3Len6Refinement
import Rule110.CookC2InfTapeBridge
import Rule110.CookTM2Bridge
import Rule110.CookMValuesVerification
import Rule110.CookStage3EmptyAppendantChain
import Rule110.CookStage3C3PrimeOperationalChain
import Rule110.CookC2VerifySupportLen7
import Rule110.CookC2SupportBareEquiv

/-!
# Cook universality pipeline chain (SPEC_070_08)

Documents which stages are discharged as theorems vs. which still invoke named bridge axioms.
Full `rule110_turing_universal_from_cook` remains open pending Cook FinTM2 encoding and
global C3 / C1 discharge.
-/

namespace Rule110

open Turing

/-- Discharge facts already proved without the legacy C3 / C1 axioms. -/
structure CookUniversalityDischarged where
  stage1_far_field : ∀ (cts : CyclicTagSystem) (idx : ℕ) (w : List Bool) (i L M : ℕ)
      (hi : cts_word_far_boundary w.length + M ≤ i),
      infRule110Steps M (cts_to_rule110_tape cts idx w) i = cookEther (i + 4 * M)
  stage1b_c2_upto7 : ∀ L slot n idx, L ≤ 7 → slot < L → n < 2 ^ L →
      cook_c2_decode_at slot
        (infRule110Steps 30
          (cts_to_rule110_tape (CyclicTagSystem.mk []) idx (natToWord L n))) =
        (natToWord L n).getD slot false
  stage1b_support_upto7 : ∀ slot n, slot < 7 → n < 2 ^ 7 →
      c2SimReadAtWithOssifier slot (natToWord 7 n) = (natToWord 7 n).getD slot false
  stage3_empty_c3prime : ∀ n, CookCtsEvalSimAtDataCones cook_standard_empty_cts n [] 0
  stage3_empty_c3primeprime : ∀ n, CookCtsEvalSimAtDataConesOrigin cook_standard_empty_cts n [] 0
  stage3_len6_origin : CookCtsEvalSimAtDataConesOrigin cook_min_len6_cts 1 cook_min_len6_true_word 0
  stage3_len6_phased_decode : CookCtsPhasedPostDecodeAt cook_min_len6_cts 1 cook_min_len6_true_word 0
  stage4_tm2_anchor : Nonempty Turing.FinTM2
  stage4_cts_identity : Nonempty (TMCTSCompilation tmIdentityStep)
  stage4_bool_identity : Nonempty (TMCTSCompilation tmBoolIdentityStep)
  stage4_consume_head : Nonempty (TMCTSCompilation tmConsumeHeadStep)
  stage4_countdown : Nonempty (TMCTSCompilation tmCountDownStep)
  m_v_python_parity :
    cook_M_for_appendant_len 6 = 390 ∧
      cook_ossifier_v cook_python_example_appendants = 1142 ∧
        cook_cycle_M_sum cook_python_example_appendants = 840
  empty_appendant_c3prime : CookEmptyAppendantC3PrimeDischarged
  legacy_c3_empty_n1_blocked : CookLegacyC3EmptyN1Blocked
  stage3_operational : CookStage3OperationalDischarged

theorem cook_universality_discharged : CookUniversalityDischarged where
  stage1_far_field := fun cts idx w i L M hi =>
    cook_cts_step_sim_ax cts idx w i L M hi
  stage1b_c2_upto7 := fun L slot n idx hL hslot hn =>
    cook_c2_tape_bit_ax_partial_upto7 L slot n hL hslot hn idx
  stage1b_support_upto7 := fun slot n hslot hn =>
    c2_support_word_read_from_bare 7 slot n (by decide) hslot hn
  stage3_empty_c3prime := cook_standard_empty_cts_data_cones
  stage3_empty_c3primeprime := cook_standard_empty_cts_data_cones_origin
  stage3_len6_origin := cook_cts_eval_sim_at_data_cones_origin_len6_one
  stage3_len6_phased_decode := cook_cts_phased_post_decode_len6_one
  stage4_tm2_anchor := cook_fin_tm2_id_machine
  stage4_cts_identity := ⟨trivialIdentityTMComp⟩
  stage4_bool_identity := ⟨cookBoolIdentityTMComp⟩
  stage4_consume_head := ⟨cookConsumeHeadTMComp⟩
  stage4_countdown := ⟨cookCountDownTMComp⟩
  m_v_python_parity := by
    refine ⟨?_, cook_v_python_example, cook_cycle_M_python_example⟩
    native_decide
  empty_appendant_c3prime := cook_empty_appendant_c3prime_discharged
  legacy_c3_empty_n1_blocked := cook_legacy_c3_empty_n1_blocked
  stage3_operational := cook_stage3_operational_discharged

/-- Named bridge axioms still required for **global** Cook certification. -/
def cook_bridge_axioms_open : Prop :=
  (∀ slot bit, ∃ decode_bit : InfTape → Bool,
      ∀ w idx,
        decode_bit (infRule110Steps 30 (cts_to_rule110_tape (CyclicTagSystem.mk []) idx w)) =
          (slot < w.length && w.getD slot false = bit)) ∧
    (∀ cts n w, n > 0 ∨ w ≠ [] → CookCtsEvalSim cts n w)

/-- SPEC_070_08 top target: not yet proved (see `cook_bridge_axioms_open`). -/
def rule110_turing_universal_from_cook_open : Prop :=
  cook_bridge_axioms_open → True

theorem rule110_turing_universal_from_cook_open_trivial (_h : cook_bridge_axioms_open) :
    rule110_turing_universal_from_cook_open :=
  fun _ => trivial

end Rule110
