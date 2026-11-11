import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.CutCharge

/-!
Guarded axiom expectations for the symbolic quadratic cut-gap proof.
Replay only in the orchestrator's detached, memory/swap-capped allocation.
These expectations have not been replayed by the source-writing worker.
-/

/--
info: 'QldpcVerification.Planar.CutCharge.coeff_mul_below' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.coeff_mul_below

/--
info: 'QldpcVerification.Planar.CutCharge.coeff_below_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.coeff_below_gap

/--
info: 'QldpcVerification.Planar.CutCharge.coeff_mul_below_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.coeff_mul_below_gap

/--
info: 'QldpcVerification.Planar.CutCharge.cut_syndrome_eq_low' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.cut_syndrome_eq_low

/--
info: 'QldpcVerification.Planar.CutCharge.cut_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.cut_gap

/--
info: 'QldpcVerification.Planar.CutCharge.residue_f' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.residue_f

/--
info: 'QldpcVerification.Planar.CutCharge.residue_g' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.residue_g

/--
info: 'QldpcVerification.Planar.CutCharge.residue_syndrome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.residue_syndrome

/--
info: 'QldpcVerification.Planar.CutCharge.row_cut_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.row_cut_gap

/--
info: 'QldpcVerification.Planar.CutCharge.columnResidue_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.columnResidue_swap

/--
info: 'QldpcVerification.Planar.CutCharge.column_cut_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.CutCharge.column_cut_gap
