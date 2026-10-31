import Lean.Elab.GuardMsgs
import QldpcVerification.Distance566SectorZ

/-! Literal Z-sector proof and data-interface guards. The combined replay runs
the frozen public helper audit separately; its guards/controls are not copied. -/

open QldpcVerification.Distance566SectorZ
open QldpcVerification.Input.Sparse

-- Check the literal suffix ordering and the zero-prefix shift.
#guard (residualTail 0 = ![1, 0, 0])
#guard (residualTail 2 = ![1, 1, 0])
#guard (residualTail 6 = ![1, 1, 1])
#guard !(bit (3 * 2 ^ 15) 14)
#guard (bit (3 * 2 ^ 15) 15)
#guard (bit (3 * 2 ^ 15) 16)
#guard !(bit (3 * 2 ^ 15) 17)

/--
info: 'QldpcVerification.Distance566SectorZ.residualTail_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.residualTail_ne_zero

/--
info: 'QldpcVerification.Distance566SectorZ.residualTail_exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.residualTail_exhaustive

/--
info: 'QldpcVerification.Distance566SectorZ.shifted_pattern' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.shifted_pattern

/--
info: 'QldpcVerification.Distance566SectorZ.reference_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.reference_cycle

/--
info: 'QldpcVerification.Distance566SectorZ.base_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.base_cycle

/--
info: 'QldpcVerification.Distance566SectorZ.base_vector' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.base_vector

/--
info: 'QldpcVerification.Distance566SectorZ.reference_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.reference_coordinates

/--
info: 'QldpcVerification.Distance566SectorZ.good_family_class' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.good_family_class

/--
info: 'QldpcVerification.Distance566SectorZ.good_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.good_lower_bound

/--
info: 'QldpcVerification.Distance566SectorZ.residual_family_class' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.residual_family_class

/--
info: 'QldpcVerification.Distance566SectorZ.residual_family_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.residual_family_cycle

/--
info: 'QldpcVerification.Distance566SectorZ.reference_pairs_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.reference_pairs_one

/--
info: 'QldpcVerification.Distance566SectorZ.residual_boundary_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.residual_boundary_zero

/--
info: 'QldpcVerification.Distance566SectorZ.residualCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.residualCertificate

/--
info: 'QldpcVerification.Distance566SectorZ.residual_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.residual_lower_bound

/--
info: 'QldpcVerification.Distance566SectorZ.lower_Z_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.lower_Z_cycle

/--
info: 'QldpcVerification.Distance566SectorZ.lower_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.lower_Z

/--
info: 'QldpcVerification.Distance566SectorZ.Checks.baseKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.Checks.baseKernel

/--
info: 'QldpcVerification.Distance566SectorZ.Checks.baseVector' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.Checks.baseVector

/--
info: 'QldpcVerification.Distance566SectorZ.Checks.refKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.Checks.refKernel

/--
info: 'QldpcVerification.Distance566SectorZ.Checks.refPattern' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.Checks.refPattern

/--
info: 'QldpcVerification.Distance566SectorZ.PackingData.goodClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.PackingData.goodClass

/--
info: 'QldpcVerification.Distance566SectorZ.PackingData.goodCap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.PackingData.goodCap

/--
info: 'QldpcVerification.Distance566SectorZ.PackingData.goodThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.PackingData.goodThreshold

/--
info: 'QldpcVerification.Distance566SectorZ.PackingData.residualClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.PackingData.residualClass

/--
info: 'QldpcVerification.Distance566SectorZ.PackingData.residualCap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.PackingData.residualCap

/--
info: 'QldpcVerification.Distance566SectorZ.PackingData.residualThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.PackingData.residualThreshold

/--
info: 'QldpcVerification.Distance566SectorZ.PackingData.residualPair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.PackingData.residualPair

/--
info: 'QldpcVerification.Distance566SectorZ.Checks.baseSupports_range' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.Checks.baseSupports_range

/--
info: 'QldpcVerification.Distance566SectorZ.Checks.baseMasks_range' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.Checks.baseMasks_range

/--
info: 'QldpcVerification.Distance566SectorZ.Checks.referenceMasks_range' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.Checks.referenceMasks_range

/--
info: 'QldpcVerification.Distance566SectorZ.PackingData.goodRange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.PackingData.goodRange

/--
info: 'QldpcVerification.Distance566SectorZ.PackingData.residualRange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566SectorZ.PackingData.residualRange

