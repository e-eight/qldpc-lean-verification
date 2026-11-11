import Lean.Elab.GuardMsgs
import QldpcVerification.Planar.BoundaryRecurrence

/-!
Guarded axiom audit for analytic directional recurrence injectivity.
Run only with the repository's detached, memory/swap-capped runner.
These guards are expectations pending that run, not a record of a successful audit.
The permitted dependencies are the usual mathlib logical axioms only.
-/

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.x_recurrence_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.x_recurrence_zero

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.z_recurrence_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.z_recurrence_zero

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.xMap_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.xMap_injective

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.zMap_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.zMap_injective

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.xChecks_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.xChecks_injective

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.zChecks_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.zChecks_injective

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.xChecks722_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.xChecks722_injective

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.zChecks722_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.zChecks722_injective

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.physicalProjection_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.physicalProjection_eq_zero

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.physical722_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.physical722_injective

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.physical722_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.physical722_rank

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.xSynthesis_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.xSynthesis_rank

/--
info: 'QldpcVerification.Planar.BoundaryRecurrence.zSynthesis_rank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Planar.BoundaryRecurrence.zSynthesis_rank
