import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.SmallSupport

/-! Guarded axiom audit for the analytic small-support tool.
Run using the repository's detached, memory-capped Lean runner.
-/

/--
info: 'QldpcVerification.Planar.SmallSupport.classify_weight_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SmallSupport.classify_weight_le_two

/--
info: 'QldpcVerification.Planar.SmallSupport.small_cycle_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SmallSupport.small_cycle_mem

/--
info: 'QldpcVerification.Planar.SmallSupport.weight_ge_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SmallSupport.weight_ge_three

/--
info: 'QldpcVerification.Planar.SmallSupport.x_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SmallSupport.x_lower

/--
info: 'QldpcVerification.Planar.SmallSupport.z_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SmallSupport.z_lower

/--
info: 'QldpcVerification.Planar.SmallSupport.pauli_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.SmallSupport.pauli_lower
