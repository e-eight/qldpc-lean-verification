import Lean.Elab.GuardMsgs
import QldpcVerification.Distance566
import QldpcVerification.Distance566Packing
import QldpcVerification.Distance566Pauli

/-! Guarded dependency audit for the literal 566 coordinate and upper-witness results. -/

/-- info: 'QldpcVerification.Distance566.xCoverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.xCoverage

/-- info: 'QldpcVerification.Distance566.zCoverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.zCoverage

/-- info: 'QldpcVerification.Distance566.detects_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.detects_X

/-- info: 'QldpcVerification.Distance566.detects_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.detects_Z

/-- info: 'QldpcVerification.Distance566.X_upper_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.X_upper_witness

/-- info: 'QldpcVerification.Distance566Certificates.rowCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Certificates.rowCheck_sound

/-- info: 'QldpcVerification.Distance566Certificates.classCheck_map_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Certificates.classCheck_map_sound

/-- info: 'QldpcVerification.Distance566.lower_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.lower_X

/-- info: 'QldpcVerification.Distance566.lower_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.lower_Z

/-- info: 'QldpcVerification.Distance566.partial_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.partial_bounds

/-- info: 'QldpcVerification.Distance566.pauli_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.pauli_lower

/-- info: 'QldpcVerification.Distance566.pauli_upper_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566.pauli_upper_witness

/-- info: 'QldpcVerification.Removal566.Stage12.hx_range' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Removal566.Stage12.hx_range

/-- info: 'QldpcVerification.Removal566.Stage12.hz_range' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Removal566.Stage12.hz_range

open QldpcVerification.Distance566Certificates in
example : rowCheck ([{0, 1}] : List (Finset (Fin 2))) 1 2 [⟨0, by decide⟩] = true := by
  decide +kernel

open QldpcVerification.Distance566Certificates in
example : rowCheck ([{0, 1}] : List (Finset (Fin 2))) 1 2 [] = false := by
  decide +kernel
