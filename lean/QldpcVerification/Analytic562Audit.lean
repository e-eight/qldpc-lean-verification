import Lean.Elab.GuardMsgs
import QldpcVerification.Lattice.Analytic562

/-! Guarded axiom audit for the symbolic 562 lattice arithmetic. -/

/--
info: 'QldpcVerification.Lattice.Analytic562.basis_det' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Analytic562.basis_det

/--
info: 'QldpcVerification.Lattice.Analytic562.basis_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Analytic562.basis_coordinates

/--
info: 'QldpcVerification.Lattice.Analytic562.basis_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Analytic562.basis_iff

/--
info: 'QldpcVerification.Lattice.Analytic562.coefficient_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Analytic562.coefficient_bounds

/--
info: 'QldpcVerification.Lattice.Analytic562.norm_ge_23' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Analytic562.norm_ge_23

/--
info: 'QldpcVerification.Lattice.Analytic562.norm_ge_23_of_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Analytic562.norm_ge_23_of_cast

/--
info: 'QldpcVerification.Lattice.Analytic562.shortest_vector_witness' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Analytic562.shortest_vector_witness
