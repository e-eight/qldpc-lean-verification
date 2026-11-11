import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.BulkExactness

/-! Guarded axiom expectations for the analytic polynomial bulk syzygy.
Replay only in the orchestrator's detached, memory/swap-capped allocation.
-/

/--
info: 'QldpcVerification.Planar.BulkExactness.quadratic_dvd_of_dvd_companion_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BulkExactness.quadratic_dvd_of_dvd_companion_mul

/--
info: 'QldpcVerification.Planar.BulkExactness.bulk_exactness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BulkExactness.bulk_exactness

/--
info: 'QldpcVerification.Planar.BulkExactness.bulk_exactness_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BulkExactness.bulk_exactness_iff

/--
info: 'QldpcVerification.Planar.BulkExactness.bulk_exactness_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BulkExactness.bulk_exactness_unique

/--
info: 'QldpcVerification.Planar.BulkExactness.bulk_exactness_outer_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BulkExactness.bulk_exactness_outer_support

/--
info: 'QldpcVerification.Planar.BulkExactness.bulk_exactness_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BulkExactness.bulk_exactness_square

/--
info: 'QldpcVerification.Planar.BulkExactness.bulk_exactness_square_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BulkExactness.bulk_exactness_square_coeff
