import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.StripRunClassification

/-! Guarded axiom expectations for exact cheap-exit feed normal forms.
Replay with the root's detached capped runner; no local Lean run claimed.
-/

/-- info: 'QldpcVerification.Planar.StripRunClassification.feed_normal_forms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunClassification.feed_normal_forms

/-- info: 'QldpcVerification.Planar.StripRunClassification.cheap_exit_forward_normal_forms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunClassification.cheap_exit_forward_normal_forms

/-- info: 'QldpcVerification.Planar.StripRunClassification.cheap_exit_backward_normal_forms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripRunClassification.cheap_exit_backward_normal_forms

