import QldpcVerification.Input.SparseCertificates

/-! Negative controls: corrupted finite certificates must evaluate to false. -/

namespace QldpcVerification.CertificateControls

open Input.Sparse

example : commCheck ([{0}] : List (Finset (Fin 2))) [{0}] = false := by decide +kernel

-- Repeated detector classes cannot supply an identity pairing matrix.
example : pairingCheck ([{0}, {0}] : List (Finset (Fin 2))) [1, 2] = false := by
  decide +kernel

example : columnCheck ([{0}, {1}] : List (Finset (Fin 2))) [0] [{1}] = false := by
  decide +kernel

example : pivotCheck [1, 2] ([{0}, {0}] : List (Finset (Fin 2))) = false := by
  decide +kernel

example : capCheck 2 [(1, 2)] 1 = false := by decide +kernel

-- A commuting representative in the wrong class still fails.
example : familyCheck ([] : List (Finset (Fin 2))) [{0}] 1 [(0, 1)] = false := by
  decide +kernel

end QldpcVerification.CertificateControls
