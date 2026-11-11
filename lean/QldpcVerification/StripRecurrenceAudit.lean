import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.StripRecurrence

/-! Guarded axiom expectations for the array-to-counting bridge.
No local Lean run: replay through the main agent's detached capped runner.
-/

/-- info: 'QldpcVerification.Planar.StripRecurrence.forward_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.forward_three

/-- info: 'QldpcVerification.Planar.StripRecurrence.backward_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.backward_three

/-- info: 'QldpcVerification.Planar.StripRecurrence.forward_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.forward_four

/-- info: 'QldpcVerification.Planar.StripRecurrence.backward_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.backward_four

/-- info: 'QldpcVerification.Planar.StripRecurrence.forward_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.forward_five

/-- info: 'QldpcVerification.Planar.StripRecurrence.backward_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.backward_five

/-- info: 'QldpcVerification.Planar.StripRecurrence.forward_gapCosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.forward_gapCosts

/-- info: 'QldpcVerification.Planar.StripRecurrence.backward_gapCosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.backward_gapCosts

/-- info: 'QldpcVerification.Planar.StripRecurrence.forward_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.forward_branch

/-- info: 'QldpcVerification.Planar.StripRecurrence.backward_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.backward_branch

/-- info: 'QldpcVerification.Planar.StripRecurrence.forward_weight_ge_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.forward_weight_ge_fifteen

/-- info: 'QldpcVerification.Planar.StripRecurrence.backward_weight_ge_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.backward_weight_ge_fifteen

/-- info: 'QldpcVerification.Planar.StripRecurrence.weight_ge_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRecurrence.weight_ge_fifteen

