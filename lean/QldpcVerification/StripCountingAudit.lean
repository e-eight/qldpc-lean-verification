import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.StripCounting

/-! Guarded axiom audit for the analytic global strip-counting argument.
Run only through the orchestrator's detached, memory-capped Lean runner.
-/

/--
info: 'QldpcVerification.Planar.StripCounting.gap_span_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripCounting.gap_span_cost

/--
info: 'QldpcVerification.Planar.StripCounting.span_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripCounting.span_budget

/--
info: 'QldpcVerification.Planar.StripCounting.forward_branch_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripCounting.forward_branch_budget

/--
info: 'QldpcVerification.Planar.StripCounting.backward_branch_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripCounting.backward_branch_budget

/--
info: 'QldpcVerification.Planar.StripCounting.weight_ge_fifteen_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripCounting.weight_ge_fifteen_forward

/--
info: 'QldpcVerification.Planar.StripCounting.weight_ge_fifteen_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripCounting.weight_ge_fifteen_backward
