import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.StripRunCounting

/-! Guarded audit of actual-sequence disjoint run accounting.
Replay only through the root's detached, capped runner.
-/

/--
info: 'QldpcVerification.Planar.StripRunCounting.zero_suffix_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.zero_suffix_budget

/--
info: 'QldpcVerification.Planar.StripRunCounting.forward_excess_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.forward_excess_budget

/--
info: 'QldpcVerification.Planar.StripRunCounting.backwardCosts_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.backwardCosts_reverse

/--
info: 'QldpcVerification.Planar.StripRunCounting.backward_excess_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.backward_excess_budget

/--
info: 'QldpcVerification.Planar.StripRunCounting.forward_weight_with_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.forward_weight_with_endpoint

/--
info: 'QldpcVerification.Planar.StripRunCounting.backward_weight_with_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.backward_weight_with_endpoint

/--
info: 'QldpcVerification.Planar.StripRunCounting.weight_ge_seventeen_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.weight_ge_seventeen_forward

/--
info: 'QldpcVerification.Planar.StripRunCounting.weight_ge_seventeen_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.weight_ge_seventeen_backward

/--
info: 'QldpcVerification.Planar.StripRunCounting.weight_ge_eighteen_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.weight_ge_eighteen_forward

/--
info: 'QldpcVerification.Planar.StripRunCounting.weight_ge_eighteen_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunCounting.weight_ge_eighteen_backward
