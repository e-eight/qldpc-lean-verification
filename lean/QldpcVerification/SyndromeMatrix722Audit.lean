import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.SyndromeMatrix722

/-! Expected axiom sets for the actual matrix coefficient bridge.
Replay only in the orchestrator's detached capped runner.
-/

/--
info: 'QldpcVerification.Planar.SyndromeMatrix722.reflectPhysical_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SyndromeMatrix722.reflectPhysical_weight

/--
info: 'QldpcVerification.Planar.SyndromeMatrix722.xCoefficientChecks_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SyndromeMatrix722.xCoefficientChecks_eq

/--
info: 'QldpcVerification.Planar.SyndromeMatrix722.zCoefficientChecks_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SyndromeMatrix722.zCoefficientChecks_eq

/--
info: 'QldpcVerification.Planar.SyndromeMatrix722.x_cycle_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SyndromeMatrix722.x_cycle_coeff

/--
info: 'QldpcVerification.Planar.SyndromeMatrix722.z_cycle_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SyndromeMatrix722.z_cycle_coeff

/--
info: 'QldpcVerification.Planar.SyndromeMatrix722.x_cycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SyndromeMatrix722.x_cycle_iff

/--
info: 'QldpcVerification.Planar.SyndromeMatrix722.z_cycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SyndromeMatrix722.z_cycle_iff
