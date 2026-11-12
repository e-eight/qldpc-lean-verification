import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.RectangleFamilyDistance

/-! Guarded audit for constructive rectangle family distance bounds. -/

/--
info: 'QldpcVerification.Planar.RectangleFamilyMatrix.xCoefficientChecks_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyMatrix.xCoefficientChecks_eq

/--
info: 'QldpcVerification.Planar.RectangleFamilyMatrix.zCoefficientChecks_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyMatrix.zCoefficientChecks_eq

/--
info: 'QldpcVerification.Planar.RectangleFamilyPeeling.factor_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyPeeling.factor_support

/--
info: 'QldpcVerification.Planar.RectangleFamilyPeeling.prefix_fill' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyPeeling.prefix_fill

/--
info: 'QldpcVerification.Planar.RectangleFamilyPeeling.suffix_fill' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyPeeling.suffix_fill

/--
info: 'QldpcVerification.Planar.RectangleFamilyGap.two_empty_rows_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyGap.two_empty_rows_boundary

/--
info: 'QldpcVerification.Planar.RectangleFamilyGap.x_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyGap.x_adjacent

/--
info: 'QldpcVerification.Planar.RectangleFamilyDistance.row_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyDistance.row_weight

/--
info: 'QldpcVerification.Planar.RectangleFamilyDistance.x_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyDistance.x_lower

/--
info: 'QldpcVerification.Planar.RectangleFamily.x_logical_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamily.x_logical_iff

/--
info: 'QldpcVerification.Planar.RectangleFamily.x_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamily.x_lower

/--
info: 'QldpcVerification.Planar.RectangleFamilyZPeeling.view_synthesis' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyZPeeling.view_synthesis

/--
info: 'QldpcVerification.Planar.RectangleFamilyZPeeling.stab_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyZPeeling.stab_iff

/--
info: 'QldpcVerification.Planar.RectangleFamilyZPeeling.prefix_fill' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyZPeeling.prefix_fill

/--
info: 'QldpcVerification.Planar.RectangleFamilyZPeeling.suffix_fill' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyZPeeling.suffix_fill

/--
info: 'QldpcVerification.Planar.RectangleFamilyZGap.two_empty_slices_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyZGap.two_empty_slices_boundary

/--
info: 'QldpcVerification.Planar.RectangleFamilyZGap.z_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyZGap.z_adjacent

/--
info: 'QldpcVerification.Planar.RectangleFamilyZGap.z_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyZGap.z_recurrence

/--
info: 'QldpcVerification.Planar.RectangleFamilyDistance.column_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyDistance.column_weight

/--
info: 'QldpcVerification.Planar.RectangleFamilyDistance.z_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamilyDistance.z_lower

/--
info: 'QldpcVerification.Planar.RectangleFamily.z_logical_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamily.z_logical_iff

/--
info: 'QldpcVerification.Planar.RectangleFamily.z_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamily.z_lower

/--
info: 'QldpcVerification.Planar.RectangleFamily.pauli_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamily.pauli_lower

/--
info: 'QldpcVerification.Planar.RectangleFamily.parameters_and_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamily.parameters_and_bounds
