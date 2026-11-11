import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.BoundaryPolynomial

/-! Axiom gates for finite boundary encoding and residue correspondence. -/

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.extract_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.extract_encode

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.encode_injective

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.encode_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.encode_extract

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.encode_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.encode_gap

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.encode_inSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.encode_inSquare

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.below_two_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.below_two_encode

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.residue_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.residue_encode

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.residue_below_two_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.residue_below_two_encode

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.columnResidue_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.columnResidue_encode

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.columnResidue_below_two_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.columnResidue_below_two_encode

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.residue_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.residue_extract

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.low_residue_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.low_residue_extract

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.columnResidue_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.columnResidue_extract

/-- info: 'QldpcVerification.Planar.BoundaryPolynomial.low_columnResidue_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryPolynomial.low_columnResidue_extract
