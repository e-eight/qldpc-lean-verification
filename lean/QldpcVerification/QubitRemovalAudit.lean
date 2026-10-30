import Lean.Elab.GuardMsgs
import QldpcVerification.QubitRemovalExamples

/-! Guarded axiom audit for the elementary qubit-removal pilot. -/

/--
info: 'QldpcVerification.QubitRemoval.snoc_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.snoc_dot

/--
info: 'QldpcVerification.QubitRemoval.snoc_dot_any' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.snoc_dot_any

/--
info: 'QldpcVerification.QubitRemoval.pad' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.pad

/--
info: 'QldpcVerification.QubitRemoval.liftZ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftZ

/--
info: 'QldpcVerification.QubitRemoval.decodeX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.decodeX

/--
info: 'QldpcVerification.QubitRemoval.liftX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftX

/--
info: 'QldpcVerification.QubitRemoval.decode_liftX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.decode_liftX

/--
info: 'QldpcVerification.QubitRemoval.liftX_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftX_decode

/--
info: 'QldpcVerification.QubitRemoval.liftX_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftX_zero

/--
info: 'QldpcVerification.QubitRemoval.old' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.old

/--
info: 'QldpcVerification.QubitRemoval.old_HX_castSucc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.old_HX_castSucc

/--
info: 'QldpcVerification.QubitRemoval.old_HX_last' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.old_HX_last

/--
info: 'QldpcVerification.QubitRemoval.old_HZ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.old_HZ

/--
info: 'QldpcVerification.QubitRemoval.pad_mem_xStab' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.pad_mem_xStab

/--
info: 'QldpcVerification.QubitRemoval.liftZ_mem_zStab' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftZ_mem_zStab

/--
info: 'QldpcVerification.QubitRemoval.liftX_mem_xStab' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftX_mem_xStab

/--
info: 'QldpcVerification.QubitRemoval.mem_xStab_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.mem_xStab_iff

/--
info: 'QldpcVerification.QubitRemoval.mem_zStab_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.mem_zStab_iff

/--
info: 'QldpcVerification.QubitRemoval.liftZ_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftZ_mem_iff

/--
info: 'QldpcVerification.QubitRemoval.x_cycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.x_cycle_iff

/--
info: 'QldpcVerification.QubitRemoval.z_cycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.z_cycle_iff

/--
info: 'QldpcVerification.QubitRemoval.x_logical_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.x_logical_iff

/--
info: 'QldpcVerification.QubitRemoval.z_logical_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.z_logical_iff

/--
info: 'QldpcVerification.QubitRemoval.liftX_logical_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftX_logical_iff

/--
info: 'QldpcVerification.QubitRemoval.liftZ_logical_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftZ_logical_iff

/--
info: 'QldpcVerification.QubitRemoval.xStabEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.xStabEquiv

/--
info: 'QldpcVerification.QubitRemoval.zStabEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.zStabEquiv

/--
info: 'QldpcVerification.QubitRemoval.rankX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.rankX

/--
info: 'QldpcVerification.QubitRemoval.rankZ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.rankZ

/--
info: 'QldpcVerification.QubitRemoval.encoded_dimension' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.encoded_dimension

/--
info: 'QldpcVerification.QubitRemoval.bitWeight' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.bitWeight

/--
info: 'QldpcVerification.QubitRemoval.bitWeight_le_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.bitWeight_le_one

/--
info: 'QldpcVerification.QubitRemoval.snoc_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.snoc_weight

/--
info: 'QldpcVerification.QubitRemoval.pad_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.pad_weight

/--
info: 'QldpcVerification.QubitRemoval.liftX_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftX_weight

/--
info: 'QldpcVerification.QubitRemoval.liftZ_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftZ_weight

/--
info: 'QldpcVerification.QubitRemoval.liftZ_weight_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.liftZ_weight_bounds

/--
info: 'QldpcVerification.QubitRemoval.logical_X_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.logical_X_lift

/--
info: 'QldpcVerification.QubitRemoval.logical_Z_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.logical_Z_lift

/--
info: 'QldpcVerification.QubitRemoval.lift_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.lift_pairing

/--
info: 'QldpcVerification.QubitRemoval.distX_old_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.distX_old_iff

/--
info: 'QldpcVerification.QubitRemoval.distZ_old_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.distZ_old_iff

/--
info: 'QldpcVerification.QubitRemoval.new_X_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.new_X_lower

/--
info: 'QldpcVerification.QubitRemoval.new_Z_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.new_Z_lower

/--
info: 'QldpcVerification.QubitRemoval.old_Z_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.old_Z_lower

/--
info: 'QldpcVerification.QubitRemoval.distZ_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.distZ_preserved

/--
info: 'QldpcVerification.QubitRemoval.distX_preserved_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.distX_preserved_iff

/--
info: 'QldpcVerification.QubitRemoval.distZ_preserved_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.distZ_preserved_iff

/--
info: 'QldpcVerification.QubitRemoval.distZ_loss_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.distZ_loss_iff

/--
info: 'QldpcVerification.QubitRemoval.distance_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.distance_comparison

/--
info: 'QldpcVerification.QubitRemoval.Examples.four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.four

/--
info: 'QldpcVerification.QubitRemoval.Examples.singleFan' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.singleFan

/--
info: 'QldpcVerification.QubitRemoval.Examples.doubleFan' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.doubleFan

/--
info: 'QldpcVerification.QubitRemoval.Examples.four_ranks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.four_ranks

/--
info: 'QldpcVerification.QubitRemoval.Examples.four_distances' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.four_distances

/--
info: 'QldpcVerification.QubitRemoval.Examples.preserving_ranks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.preserving_ranks

/--
info: 'QldpcVerification.QubitRemoval.Examples.preserving_distances' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.preserving_distances

/--
info: 'QldpcVerification.QubitRemoval.Examples.preserving_parameters' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.preserving_parameters

/--
info: 'QldpcVerification.QubitRemoval.Examples.increasing_distances' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.increasing_distances

/--
info: 'QldpcVerification.QubitRemoval.Examples.three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.three

/--
info: 'QldpcVerification.QubitRemoval.Examples.tripleFan' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.tripleFan

/--
info: 'QldpcVerification.QubitRemoval.Examples.three_ranks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.three_ranks

/--
info: 'QldpcVerification.QubitRemoval.Examples.three_distances' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.three_distances

/--
info: 'QldpcVerification.QubitRemoval.Examples.losing_ranks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.losing_ranks

/--
info: 'QldpcVerification.QubitRemoval.Examples.losing_distances' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.losing_distances

/--
info: 'QldpcVerification.QubitRemoval.Examples.losing_parameters' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.losing_parameters

/--
info: 'QldpcVerification.QubitRemoval.Examples.losing_matrices' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.losing_matrices

/--
info: 'QldpcVerification.QubitRemoval.Examples.preserving_via_criteria' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.preserving_via_criteria

/--
info: 'QldpcVerification.QubitRemoval.Examples.losing_via_criterion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.losing_via_criterion

/--
info: 'QldpcVerification.QubitRemoval.Examples.preserving_canonical_lift_grows' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitRemoval.Examples.preserving_canonical_lift_grows
