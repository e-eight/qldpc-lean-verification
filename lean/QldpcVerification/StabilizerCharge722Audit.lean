import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.StabilizerCharge722

/-! Guarded audit for charge vanishing on the actual finite stabilizer rows.
Pending replay in the orchestrator's detached, memory/swap-capped runner. -/

/--
info: 'QldpcVerification.Planar.StabilizerCharge722.HX_row_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StabilizerCharge722.HX_row_zero

/--
info: 'QldpcVerification.Planar.StabilizerCharge722.HZ_column_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StabilizerCharge722.HZ_column_zero

/--
info: 'QldpcVerification.Planar.StabilizerCharge722.HX_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StabilizerCharge722.HX_cycle

/--
info: 'QldpcVerification.Planar.StabilizerCharge722.HZ_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StabilizerCharge722.HZ_cycle

/--
info: 'QldpcVerification.Planar.StabilizerCharge722.HX_lowCharge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StabilizerCharge722.HX_lowCharge

/--
info: 'QldpcVerification.Planar.StabilizerCharge722.HZ_lowColumnCharge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StabilizerCharge722.HZ_lowColumnCharge
