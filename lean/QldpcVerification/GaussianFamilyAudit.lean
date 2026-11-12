import Lean.Elab.GuardMsgs
import QldpcVerification.Bicycle.GaussianFamily

/-! Guarded audit for the symbolic rotated-square family. -/

/-- info: 'QldpcVerification.Lattice.Gaussian.rotated_norm_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Gaussian.rotated_norm_ge

/-- info: 'QldpcVerification.Lattice.Gaussian.coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Gaussian.coordinates

/-- info: 'QldpcVerification.Lattice.Gaussian.norm_ge_of_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Gaussian.norm_ge_of_cast

/-- info: 'QldpcVerification.Lattice.Gaussian.minimizing_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Lattice.Gaussian.minimizing_pair

/-- info: 'QldpcVerification.Bicycle.GaussianFamily.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.GaussianFamily.parameters

/-- info: 'QldpcVerification.Bicycle.GaussianFamily.ranks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.GaussianFamily.ranks
