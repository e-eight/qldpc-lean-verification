import Lean.Elab.GuardMsgs
import QldpcVerification.FamilyTheory

/-! Aggregate capstone audit for the analytic family theory. -/

/-- info: 'QldpcVerification.Bicycle.Connected.Match.parameters_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.Connected.Match.parameters_all

/-- info: 'QldpcVerification.Bicycle.GaussianFamily.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.GaussianFamily.parameters

/-- info: 'QldpcVerification.Planar.RectangleFamily.parameters_and_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamily.parameters_and_bounds

/-- info: 'QldpcVerification.Planar.RectangleFamily.pauli_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.RectangleFamily.pauli_lower

/-- info: 'QldpcVerification.QubitReplication.exact_distances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitReplication.exact_distances

/-- info: 'QldpcVerification.QubitReplication.ranks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.QubitReplication.ranks
