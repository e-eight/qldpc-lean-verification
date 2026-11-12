import QldpcVerification.BicycleFamilyDependencyAudit
import QldpcVerification.Rectangle722FamilyDependencyAudit
import QldpcVerification.BasisSeparationAudit
import QldpcVerification.NormalizedShortestAudit
import QldpcVerification.Rectangle722FamilyAudit
import Lean.Elab.GuardMsgs

/-! Focused axiom and proof-path audit of the existing instances after migration. -/

/-- info: 'QldpcVerification.Bicycle4.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle4.parameters

/-- info: 'QldpcVerification.Bicycle58.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle58.parameters

/-- info: 'QldpcVerification.Bicycle82.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle82.parameters

/-- info: 'QldpcVerification.Bicycle100.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle100.parameters

/-- info: 'QldpcVerification.Bicycle110.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle110.parameters

/-- info: 'QldpcVerification.Bicycle122.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle122.parameters

/-- info: 'QldpcVerification.Bicycle170.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle170.parameters

/-- info: 'QldpcVerification.Bicycle226.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle226.parameters

/-- info: 'QldpcVerification.Bicycle262Lattice.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle262Lattice.parameters

/-- info: 'QldpcVerification.Bicycle278.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle278.parameters

/-- info: 'QldpcVerification.Bicycle298.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle298.parameters

/-- info: 'QldpcVerification.Bicycle346.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle346.parameters

/-- info: 'QldpcVerification.Bicycle362.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle362.parameters

/-- info: 'QldpcVerification.Bicycle422.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle422.parameters

/-- info: 'QldpcVerification.Bicycle454.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle454.parameters

/-- info: 'QldpcVerification.Bicycle562Family.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle562Family.parameters

/-- info: 'QldpcVerification.BicycleEven16Family.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.BicycleEven16Family.parameters

/-- info: 'QldpcVerification.BicycleEvenStep16.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.BicycleEvenStep16.parameters

/-- info: 'QldpcVerification.Bicycle262.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle262.parameters

/-- info: 'QldpcVerification.Bicycle562.parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle562.parameters

/-- info: 'QldpcVerification.Bicycle262.HX_eq_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle262.HX_eq_original

/-- info: 'QldpcVerification.Bicycle262.HZ_eq_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle262.HZ_eq_original

/-- info: 'QldpcVerification.Bicycle262.rankX_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle262.rankX_lower

/-- info: 'QldpcVerification.Bicycle262.rankZ_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle262.rankZ_lower

/-- info: 'QldpcVerification.Bicycle562.HX_eq_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle562.HX_eq_original

/-- info: 'QldpcVerification.Bicycle562.HZ_eq_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle562.HZ_eq_original

/-- info: 'QldpcVerification.Bicycle562.rankX_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle562.rankX_lower

/-- info: 'QldpcVerification.Bicycle562.rankZ_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle562.rankZ_lower
