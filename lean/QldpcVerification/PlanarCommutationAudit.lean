import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.Commutation

/-!
Expected axiom audit for the explicit rectangular finite matrices.
Pending replay with the orchestrator's detached, memory/swap-capped runner.
These guards are not a record of successful compilation or draft verification.
-/

/--
info: 'QldpcVerification.Planar.Commutation.intersection_on_board' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Commutation.intersection_on_board

/--
info: 'QldpcVerification.Planar.Commutation.block_overlap_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Commutation.block_overlap_swap

/--
info: 'QldpcVerification.Planar.Commutation.rows_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Commutation.rows_orthogonal

/--
info: 'QldpcVerification.Planar.Commutation.commutation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Commutation.commutation
