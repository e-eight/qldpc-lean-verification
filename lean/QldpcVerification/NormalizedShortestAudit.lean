import Lean.Elab.GuardMsgs
import QldpcVerification.Bicycle.NormalizedShortest

/-! Guarded dependency audit of the normalized shortest-relation adapter. -/

/-- info: 'QldpcVerification.Bicycle.Match.parameters_of_shortest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.Match.parameters_of_shortest

/-- info: 'QldpcVerification.Bicycle.Match.parameters_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Bicycle.Match.parameters_minimum
