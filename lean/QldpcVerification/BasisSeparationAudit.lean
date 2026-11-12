import Lean.Elab.GuardMsgs
import QldpcVerification.Lattice.BasisSeparation

/-! Guarded audit of the analytic basis criterion for cyclic relation lattices. -/

/-- info: 'QldpcVerification.Lattice.BasisSeparation.BasisData.determinant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.BasisSeparation.BasisData.determinant

/-- info: 'QldpcVerification.Lattice.BasisSeparation.BasisData.coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.BasisSeparation.BasisData.coordinates

/-- info: 'QldpcVerification.Lattice.BasisSeparation.BasisData.basis_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.BasisSeparation.BasisData.basis_iff

/-- info: 'QldpcVerification.Lattice.BasisSeparation.BasisData.short_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.BasisSeparation.BasisData.short_coordinates

/-- info: 'QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge

/-- info: 'QldpcVerification.Lattice.BasisSeparation.BasisData.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.BasisSeparation.BasisData.bound
