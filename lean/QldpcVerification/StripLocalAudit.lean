import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.StripLocal

/-! Guarded axiom gates for universally quantified strip-local polynomial costs.
Expected standard kernel axioms only. Replay is delegated to the main agent's
detached memory/swap-capped runner; this audit has not been run by the author.
The scalar budget endpoint is conditional on the global counting budgets.
-/

/-- info: 'QldpcVerification.Planar.StripLocal.wt_mul_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.wt_mul_X_pow

/-- info: 'QldpcVerification.Planar.StripLocal.wt_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.wt_add_le

/-- info: 'QldpcVerification.Planar.StripLocal.eval_one_eq_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.eval_one_eq_weight

/-- info: 'QldpcVerification.Planar.StripLocal.singleton_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.singleton_monomial

/-- info: 'QldpcVerification.Planar.StripLocal.singleton_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.singleton_pair

/-- info: 'QldpcVerification.Planar.StripLocal.two_le_wt_t_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.two_le_wt_t_mul

/-- info: 'QldpcVerification.Planar.StripLocal.two_le_wt_mul_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.two_le_wt_mul_t

/-- info: 'QldpcVerification.Planar.StripLocal.two_le_wt_one_add_s_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.two_le_wt_one_add_s_mul

/-- info: 'QldpcVerification.Planar.StripLocal.wt_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.wt_terminal

/-- info: 'QldpcVerification.Planar.StripLocal.branch_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.branch_forward

/-- info: 'QldpcVerification.Planar.StripLocal.branch_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.branch_backward

/-- info: 'QldpcVerification.Planar.StripLocal.eval_one_zero_of_t_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.eval_one_zero_of_t_mul_eq

/-- info: 'QldpcVerification.Planar.StripLocal.gap_three_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.gap_three_forward

/-- info: 'QldpcVerification.Planar.StripLocal.gap_three_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.gap_three_backward

/-- info: 'QldpcVerification.Planar.StripLocal.gap_four_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.gap_four_forward

/-- info: 'QldpcVerification.Planar.StripLocal.gap_four_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.gap_four_backward

/-- info: 'QldpcVerification.Planar.StripLocal.gap_five_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.gap_five_forward

/-- info: 'QldpcVerification.Planar.StripLocal.gap_five_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.gap_five_backward

/-- info: 'QldpcVerification.Planar.StripLocal.fifteen_of_budgets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.StripLocal.fifteen_of_budgets

