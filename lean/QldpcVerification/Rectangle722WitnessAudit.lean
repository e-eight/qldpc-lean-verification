import Lean.Elab.GuardMsgs
import QldpcVerification.Rectangle722Witness

/-! Pending external bounded replay. Guards audit both fixed syndrome identities
transitively through the cycle and logical capstones. No additional axioms allowed. -/

/-- info: 'QldpcVerification.Rectangle722Witness.x_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Witness.x_cycle

/-- info: 'QldpcVerification.Rectangle722Witness.z_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Witness.z_cycle

/-- info: 'QldpcVerification.Rectangle722Witness.x_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Witness.x_logical

/-- info: 'QldpcVerification.Rectangle722Witness.z_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Witness.z_logical

/-- info: 'QldpcVerification.Rectangle722Witness.z_upper_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Witness.z_upper_witness

/-- info: 'QldpcVerification.Rectangle722Witness.pauli_upper_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Rectangle722Witness.pauli_upper_witness

/-
Source SHA-256 manifest for pending replay, not a build receipt.
Source limits: maxHeartbeats 800000; maxRecDepth 4096.
No Lean process run by this author. Root runner must enforce detached memory
and swap limits and record actual resource limits, outcomes, and source hashes.
7bca386aa08bddc041e52ed42a04837515aa25576e7ef290fff64f001d2b4cd9  lean/QldpcVerification/Rectangle722Witness.lean
ab82cf13487aefe6fed1ce6f7f37b5e33890af0eee103000018410ca7012fe93  lean/QldpcVerification/Rectangle722Submitted.lean
716f7af2875ca7d0ff206257122783a54857d7739c3c74072aa9ddbfaa56a1a5  scripts/check_rectangle722_witness.py
0dd94e8b54288ca008df7b756185021cac12fa296a6f013f8c171ede3777db78  analytical/rectangle722-submitted/WITNESS.typ
-/
