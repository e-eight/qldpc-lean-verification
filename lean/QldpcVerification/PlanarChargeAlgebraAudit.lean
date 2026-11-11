import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.ChargeAlgebra

/-! Kernel axiom gates for the actual722 charge algebra.
Run with the orchestrator’s capped Lean runner; no finite enumeration is used. -/

/-- info: 'QldpcVerification.Planar.ChargeAlgebra.finrank_eq_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.ChargeAlgebra.finrank_eq_eight

/-- info: 'QldpcVerification.Planar.ChargeAlgebra.x_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.ChargeAlgebra.x_isUnit

/-- info: 'QldpcVerification.Planar.ChargeAlgebra.y_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.ChargeAlgebra.y_isUnit

/-- info: 'QldpcVerification.Planar.ChargeAlgebra.xEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.ChargeAlgebra.xEquiv

/-- info: 'QldpcVerification.Planar.ChargeAlgebra.span_y_powers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.ChargeAlgebra.span_y_powers

/-- info: 'QldpcVerification.Planar.ChargeAlgebra.span_x_powers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.ChargeAlgebra.span_x_powers

/-- info: 'QldpcVerification.Planar.ChargeAlgebra.y_coordinates_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.ChargeAlgebra.y_coordinates_surjective

/-- info: 'QldpcVerification.Planar.ChargeAlgebra.x_coordinates_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.ChargeAlgebra.x_coordinates_surjective
