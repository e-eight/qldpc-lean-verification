set -eu
lake --log-level=error -d lean build QldpcVerification.Lattice.Connectivity
lake --log-level=error -d lean build QldpcVerification.Bicycle.Connected
lake --log-level=error -d lean build QldpcVerification
lake -d lean env lean lean/QldpcVerification/ConnectivityAudit.lean
lake -d lean env lean lean/QldpcVerification/BatchAudit.lean
lake -d lean env lean lean/QldpcVerification/FamilyAudit.lean
lake -d lean env lean lean/QldpcVerification/WindingAudit.lean
lake -d lean env lean lean/QldpcVerification/BicycleAudit.lean
lake -d lean env lean lean/QldpcVerification/KernelAudit.lean
