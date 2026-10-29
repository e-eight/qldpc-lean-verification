import Lean.Elab.GuardMsgs
import QldpcCert.Surface225

/-! Fail if the concrete distance theorem acquires any extra axiom. -/

/--
info: 'Surface225.distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Surface225.distance

#print axioms Surface225.distance
