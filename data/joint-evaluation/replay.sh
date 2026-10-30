set -eu
lake --log-level=error -d lean build QldpcVerification.Bicycle.PeriodBasis
lake --log-level=error -d lean build QldpcVerification.Bicycle.SignedPaths
lake --log-level=error -d lean build QldpcVerification.Bicycle.JointCoverage
lake --log-level=error -d lean build QldpcVerification.Bicycle.JointMatch
lake --log-level=error -d lean build QldpcVerification.Lattice.JointFiniteBound
lake --log-level=error -d lean build QldpcVerification.Bicycle.JointExamples
lake --log-level=error -d lean build QldpcVerification
lake -d lean env lean lean/QldpcVerification/JointAudit.lean
lake -d lean env lean lean/QldpcVerification/ConnectivityAudit.lean
lake -d lean env lean lean/QldpcVerification/BatchAudit.lean
lake -d lean env lean lean/QldpcVerification/FamilyAudit.lean
lake -d lean env lean lean/QldpcVerification/WindingAudit.lean
lake -d lean env lean lean/QldpcVerification/BicycleAudit.lean
lake -d lean env lean lean/QldpcVerification/KernelAudit.lean
