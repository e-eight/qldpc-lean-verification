import Lean.Elab.GuardMsgs
import QldpcVerification.Bicycle.CyclicDistance

/-! Guarded audit of exact parameters for arbitrary cyclic binomial steps. -/

/-- info: 'QldpcVerification.Bicycle.Connected.relation_scaled_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.Connected.relation_scaled_iff

/-- info: 'QldpcVerification.Bicycle.Connected.minimumNorm_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.Connected.minimumNorm_scaled

/-- info: 'QldpcVerification.Bicycle.Connected.Match.parameters_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.Connected.Match.parameters_all

/-- info: 'QldpcVerification.Bicycle.Connected.Match.rankX_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.Connected.Match.rankX_all

/-- info: 'QldpcVerification.Bicycle.Connected.Match.rankZ_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.Connected.Match.rankZ_all
