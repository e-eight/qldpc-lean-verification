set -eu
lake --log-level=error -d lean build QldpcVerification.QubitRemoval
lake --log-level=error -d lean build QldpcVerification.QubitRemovalExamples
lake --log-level=error -d lean build QldpcVerification
lake -d lean env lean lean/QldpcVerification/QubitRemovalAudit.lean
lake -d lean env lean lean/QldpcVerification/ComponentAudit.lean
lake -d lean env lean lean/QldpcVerification/JointAudit.lean
lake -d lean env lean lean/QldpcVerification/ConnectivityAudit.lean
lake -d lean env lean lean/QldpcVerification/BatchAudit.lean
lake -d lean env lean lean/QldpcVerification/FamilyAudit.lean
lake -d lean env lean lean/QldpcVerification/WindingAudit.lean
lake -d lean env lean lean/QldpcVerification/BicycleAudit.lean
lake -d lean env lean lean/QldpcVerification/KernelAudit.lean
