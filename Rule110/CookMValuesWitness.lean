import Rule110.CookMValuesVerification
import Rule110.CookConstructionCollisionCerts

/-!
# Cook M / v and §4 collision certificate witnesses
-/

namespace Rule110

theorem cook_v_python_example_witness :
    cook_ossifier_v cook_python_example_appendants = 1142 :=
  cook_v_python_example

theorem cook_cycle_M_python_example_witness :
    cook_cycle_M_sum cook_python_example_appendants = 840 :=
  cook_cycle_M_python_example

theorem kind5_raw_k_leader_negative_witness :
    collisionSimConeFixed (collisionSimInit kind5RawKLeaderPlacements) 30 0 = false :=
  kind5_raw_k_leader_slot0_not_fixed_30

end Rule110
