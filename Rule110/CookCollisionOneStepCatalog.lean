import Rule110.CookConstructionCollisionCerts
import Rule110.CookLen6DataConesOrigin
import Rule110.CookLen6PhasedPostDecode
import Rule110.CookLen6TailOrigin
import Rule110.CookStage3EmptyAppendantChain
import Rule110.CookStage3OriginSucc

/-!
# Option A: collision-catalog routing for Stage 3 one-step / tail axioms

Cook §4 / Neary–Woods collision kinds supply **finite list certificates** that discharge
appendant-local physics. This module records which configurations are proved vs. which
still route to open axioms, and links each open target to its collision kind.

## Discharged routes (no bridge axiom on these paths)

| Configuration | One-step C3′′ | Phased decode | Tail origin |
|---|---|---|---|
| Empty post-word | vacuous | vacuous | `M₂ = 0` |
| L=6 `[true]` min input | `cook_cts_eval_sim_at_data_cones_origin_len6_one` | `cook_cts_phased_post_decode_len6_one` | `cook_cts_tail_origin_len6_M390_M30` when `M₁=390`, `M₂=30` |

## Open routes (collision catalog targets)

| Collision kind | Certificate module | Stage 3 target |
|---|---|---|
| `ossifier_meets_moving_or_invisible` | `kind1_ossifier_c2_slot0_cone_not_fixed_30` | General nonempty one-step (non-L=6) |
| `tape_passes_through_moving_or_invisible` | `kind2_empty_support_slot0_cone_not_fixed_30` | Empty appendant `M₁=30` tail + legacy C3 |
| `tape_hits_prepared_leader` | `kind3_slot19_cone_not_fixed_30` | Leader-prepared encodings |
| `acceptor_rejector_meets_table` | `kind4_kh_leader_true_cone_not_fixed_30` | Table-sector collisions |
| `acceptor_rejector_meets_raw_leader` | `kind5_raw_k_leader_cone_not_fixed_30` | Raw-leader collisions |

Next work: for each kind, add **positive** bounded certificates on the configurations
that *do* appear in CTS one-step evolution (origin-cell or Icc invariants), then lift
via `c2SimRun_eq_infRule110Steps_at` as in `CookLen6DataConesOrigin`.
-/

namespace Rule110

/-- L=6 minimal one-step C3′′ (origin cells after 390 steps). -/
abbrev cook_collision_route_len6_one_step :=
  cook_cts_eval_sim_at_data_cones_origin_len6_one

/-- L=6 phased post-decode at `n = 1`. -/
abbrev cook_collision_route_len6_phased_decode :=
  cook_cts_phased_post_decode_len6_one

/-- L=6 tail-origin with micro-split `390 + 30` (list cert + InfTape lift). -/
abbrev cook_collision_route_len6_tail_M390_M30 :=
  cook_cts_tail_origin_len6_M390_M30

/-- Empty appendant: C3′′ at all `n` without legacy C3 axiom. -/
abbrev cook_collision_route_empty_c3prime :=
  cook_empty_appendant_c3prime_discharged

/-- Negative kind-2 witness on the empty phased-with-support encoding (30-step cone drift). -/
abbrev cook_collision_catalog_kind2_empty_negative :=
  cook_empty_appendant_kind2_collision_negative

/-- All five Neary–Woods construction kinds have finite negative cone witnesses. -/
theorem cook_collision_kind_certificates_complete :
    collisionSimConeFixed kind1OssifierC2Init 30 0 = false ∧
      collisionSimConeFixed kind2EmptySupportInit 30 0 = false ∧
        collisionSimConeFixed (collisionSimInit kind3Slot19Placements) 30 19 = false ∧
          collisionSimConeFixed (collisionSimInit kind4KHLeaderTruePlacements) 30 0 = false ∧
            collisionSimConeFixed (collisionSimInit kind5RawKLeaderPlacements) 30 0 = false :=
  cook_collision_all_five_kinds_certified

end Rule110
