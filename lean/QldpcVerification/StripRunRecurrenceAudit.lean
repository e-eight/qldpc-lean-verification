import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.StripRunRecurrence

/-! Guarded expectations for the actual-array seventeen/eighteen bounds.
Unrun by the author; root detached capped replay is required.
-/

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.forward_long' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.forward_long

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.backward_long' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.backward_long

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.forward_incoming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.forward_incoming

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.backward_incoming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.backward_incoming

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.forward_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.forward_costs

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.backward_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.backward_costs

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.forward_weight_ge_seventeen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.forward_weight_ge_seventeen

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.backward_weight_ge_seventeen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.backward_weight_ge_seventeen

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.forward_weight_ge_eighteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.forward_weight_ge_eighteen

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.backward_weight_ge_eighteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.backward_weight_ge_eighteen

/-- info: 'QldpcVerification.Planar.StripRunRecurrence.weight_ge_seventeen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunRecurrence.weight_ge_seventeen

