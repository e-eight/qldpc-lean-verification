import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.StripRunLocal

/-! Guarded axiom expectations for the polynomial run-exit lemmas.
Unrun by the author; replay with the root agent's detached capped runner.
-/

/-- info: 'QldpcVerification.Planar.StripRunLocal.singleton_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.singleton_cancellation

/-- info: 'QldpcVerification.Planar.StripRunLocal.feed_weight_ge_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.feed_weight_ge_three

/-- info: 'QldpcVerification.Planar.StripRunLocal.cheap_exit_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.cheap_exit_forward

/-- info: 'QldpcVerification.Planar.StripRunLocal.cheap_exit_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.cheap_exit_backward

/-- info: 'QldpcVerification.Planar.StripRunLocal.exit_alternative_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.exit_alternative_forward

/-- info: 'QldpcVerification.Planar.StripRunLocal.exit_alternative_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.exit_alternative_backward

/-- info: 'QldpcVerification.Planar.StripRunLocal.exitExcess_le_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.exitExcess_le_interior

/-- info: 'QldpcVerification.Planar.StripRunLocal.longer_gap_exit_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.longer_gap_exit_forward

/-- info: 'QldpcVerification.Planar.StripRunLocal.longer_gap_exit_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.longer_gap_exit_backward

/-- info: 'QldpcVerification.Planar.StripRunLocal.gap_three_excess_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.gap_three_excess_forward

/-- info: 'QldpcVerification.Planar.StripRunLocal.gap_three_excess_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunLocal.gap_three_excess_backward

