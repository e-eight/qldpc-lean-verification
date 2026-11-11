import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.Parameters722

/-!
Guarded axiom audit of the rectangular matrix correspondence and parameter capstone.
Run using the orchestrator's detached, memory/swap-capped runner.
These guards are expectations pending successful replay, not a verification record.
-/

/--
info: 'QldpcVerification.Planar.Parameters722.xSynthesis_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Parameters722.xSynthesis_eq

/--
info: 'QldpcVerification.Planar.Parameters722.zSynthesis_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Parameters722.zSynthesis_eq

/--
info: 'QldpcVerification.Planar.Parameters722.matrix_ranks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Parameters722.matrix_ranks

/--
info: 'QldpcVerification.Planar.Parameters722.quotient_finrank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Parameters722.quotient_finrank

/--
info: 'QldpcVerification.Planar.Parameters722.parameters722' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.Parameters722.parameters722
