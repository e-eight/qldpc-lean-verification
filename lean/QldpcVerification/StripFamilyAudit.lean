import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.StripFamilyRunRecurrence

/-! Guarded audit of arbitrary-length polynomial strip bounds. -/

/-- info: 'QldpcVerification.Planar.StripFamilyRunCounting.forward_excess_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripFamilyRunCounting.forward_excess_budget

/-- info: 'QldpcVerification.Planar.StripFamilyRunCounting.backward_excess_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripFamilyRunCounting.backward_excess_budget

/-- info: 'QldpcVerification.Planar.StripFamilyRunRecurrence.forward_weight_ge_length_sub_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripFamilyRunRecurrence.forward_weight_ge_length_sub_two

/-- info: 'QldpcVerification.Planar.StripFamilyRunRecurrence.backward_weight_ge_length_sub_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripFamilyRunRecurrence.backward_weight_ge_length_sub_two

/-- info: 'QldpcVerification.Planar.StripFamilyRunRecurrence.forward_weight_ge_length_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripFamilyRunRecurrence.forward_weight_ge_length_sub_one

/-- info: 'QldpcVerification.Planar.StripFamilyRunRecurrence.backward_weight_ge_length_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripFamilyRunRecurrence.backward_weight_ge_length_sub_one
