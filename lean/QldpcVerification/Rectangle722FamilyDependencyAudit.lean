import QldpcVerification.Audit.Dependencies
import QldpcVerification.Rectangle722SubmittedBounds
import Lean.Elab.GuardMsgs

/-! Check the proof bodies, not merely the imports: literal 722 bounds must use
the new physical family theorems and avoid the old charge-dependent route. -/

#guard_dependencies QldpcVerification.Rectangle722Submitted.parameters_and_bounds requires [
  QldpcVerification.Planar.RectangleFamily.rankX,
  QldpcVerification.Planar.RectangleFamily.rankZ,
  QldpcVerification.Planar.RectangleFamily.x_lower,
  QldpcVerification.Planar.RectangleFamily.z_lower]
  excludes ["ChargeCompleteness722", "BoundaryCharge", "PhysicalStrips722",
    "Distance722Seventeen", "Parameters722", "StripRunRecurrence"]

#guard_dependencies QldpcVerification.Rectangle722Submitted.pauli_bounds requires [
  QldpcVerification.Planar.RectangleFamily.x_lower,
  QldpcVerification.Planar.RectangleFamily.z_lower]
  excludes ["ChargeCompleteness722", "BoundaryCharge", "PhysicalStrips722",
    "Distance722Seventeen", "Parameters722", "StripRunRecurrence"]

/-- error: QldpcVerification.Planar.Rectangle722Family.HX_eq does not depend on required theorem QldpcVerification.Rectangle722Submitted.parameters_and_bounds -/
#guard_msgs (whitespace := lax) in
#guard_dependencies QldpcVerification.Planar.Rectangle722Family.HX_eq requires [
  QldpcVerification.Rectangle722Submitted.parameters_and_bounds] excludes []

/-- error: QldpcVerification.Planar.Rectangle722Family.HX_eq still depends on forbidden declaration QldpcVerification.Planar.Rectangle722Family.HX_eq -/
#guard_msgs (whitespace := lax) in
#guard_dependencies QldpcVerification.Planar.Rectangle722Family.HX_eq requires []
  excludes ["Rectangle722Family.HX_eq"]
