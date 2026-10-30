set -eu
lake --log-level=error -d lean build QldpcVerification.Components
lake --log-level=error -d lean build QldpcVerification.CoverageTransport
lake --log-level=error -d lean build QldpcVerification.Bicycle.CyclicComponents
lake --log-level=error -d lean build QldpcVerification.Bicycle.ComponentBounds
lake --log-level=error -d lean build QldpcVerification.ComponentDistance
lake --log-level=error -d lean build QldpcVerification.Bicycle.ComponentParameters
lake --log-level=error -d lean build QldpcVerification.Bicycle.GcdComponents
lake --log-level=error -d lean build QldpcVerification.BicycleComponents24
lake --log-level=error -d lean build QldpcVerification
lake -d lean env lean lean/QldpcVerification/ComponentAudit.lean
lake -d lean env lean lean/QldpcVerification/JointAudit.lean
lake -d lean env lean lean/QldpcVerification/ConnectivityAudit.lean
lake -d lean env lean lean/QldpcVerification/BatchAudit.lean
lake -d lean env lean lean/QldpcVerification/FamilyAudit.lean
lake -d lean env lean lean/QldpcVerification/WindingAudit.lean
lake -d lean env lean lean/QldpcVerification/BicycleAudit.lean
lake -d lean env lean lean/QldpcVerification/KernelAudit.lean
