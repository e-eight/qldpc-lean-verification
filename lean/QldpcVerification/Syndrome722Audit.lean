import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.Syndrome722

/-!
Guarded audit target for the concrete physical/full-syndrome bridge.
These are expected axiom sets, pending replay by the detached capped runner.
No source author Lean run, kernel pass, or distance theorem is asserted here.
-/

/--
info: 'QldpcVerification.Planar.Syndrome722.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Syndrome722.decode_encode

/--
info: 'QldpcVerification.Planar.Syndrome722.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Syndrome722.encode_decode

/--
info: 'QldpcVerification.Planar.Syndrome722.encode_finiteBulk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Syndrome722.encode_finiteBulk

/--
info: 'QldpcVerification.Planar.Syndrome722.finiteBulk_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Syndrome722.finiteBulk_injective

/--
info: 'QldpcVerification.Planar.Syndrome722.finiteBulk_range_eq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Syndrome722.finiteBulk_range_eq_kernel

/--
info: 'QldpcVerification.Planar.Syndrome722.fullSyndrome_kernel_finrank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Syndrome722.fullSyndrome_kernel_finrank
