import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.PhysicalStrips722

/-! Guarded axiom audit for the actual physical polynomial-strip bridges.
Replay only through the main detached, capped runner.
-/

/--
info: 'QldpcVerification.Planar.PhysicalStrips722.forward_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.PhysicalStrips722.forward_weight

/--
info: 'QldpcVerification.Planar.PhysicalStrips722.backward_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.PhysicalStrips722.backward_weight

/--
info: 'QldpcVerification.Planar.PhysicalStrips722.syndrome_coeff_add_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.PhysicalStrips722.syndrome_coeff_add_two

/--
info: 'QldpcVerification.Planar.PhysicalStrips722.swapped_syndrome_coeff_add_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.PhysicalStrips722.swapped_syndrome_coeff_add_two

/--
info: 'QldpcVerification.Planar.PhysicalStrips722.forward_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.PhysicalStrips722.forward_recurrence

/--
info: 'QldpcVerification.Planar.PhysicalStrips722.backward_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.PhysicalStrips722.backward_recurrence

/--
info: 'QldpcVerification.Planar.PhysicalStrips722.forward_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.PhysicalStrips722.forward_adjacent

/--
info: 'QldpcVerification.Planar.PhysicalStrips722.backward_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.PhysicalStrips722.backward_adjacent
