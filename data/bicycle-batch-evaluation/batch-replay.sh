set -eu
for target in \
  QldpcVerification.Input.Bicycle4Data \
  QldpcVerification.Input.Bicycle4Match \
  QldpcVerification.Lattice.Bicycle4Arithmetic \
  QldpcVerification.Bicycle4 \
  QldpcVerification.Input.Bicycle58Data \
  QldpcVerification.Input.Bicycle58Match \
  QldpcVerification.Lattice.Bicycle58Arithmetic \
  QldpcVerification.Bicycle58 \
  QldpcVerification.Input.Bicycle82Data \
  QldpcVerification.Input.Bicycle82Match \
  QldpcVerification.Lattice.Bicycle82Arithmetic \
  QldpcVerification.Bicycle82 \
  QldpcVerification.Input.Bicycle100Data \
  QldpcVerification.Input.Bicycle100Match \
  QldpcVerification.Lattice.Bicycle100Arithmetic \
  QldpcVerification.Bicycle100 \
  QldpcVerification.Input.Bicycle110Data \
  QldpcVerification.Input.Bicycle110Match \
  QldpcVerification.Lattice.Bicycle110Arithmetic \
  QldpcVerification.Bicycle110 \
  QldpcVerification.Input.Bicycle122Data \
  QldpcVerification.Input.Bicycle122Match \
  QldpcVerification.Lattice.Bicycle122Arithmetic \
  QldpcVerification.Bicycle122 \
  QldpcVerification.Input.Bicycle170Data \
  QldpcVerification.Input.Bicycle170Match \
  QldpcVerification.Lattice.Bicycle170Arithmetic \
  QldpcVerification.Bicycle170 \
  QldpcVerification.Input.Bicycle226Data \
  QldpcVerification.Input.Bicycle226Match \
  QldpcVerification.Lattice.Bicycle226Arithmetic \
  QldpcVerification.Bicycle226 \
  QldpcVerification.Input.Bicycle278Data \
  QldpcVerification.Input.Bicycle278Match \
  QldpcVerification.Lattice.Bicycle278Arithmetic \
  QldpcVerification.Bicycle278 \
  QldpcVerification.Input.Bicycle298Data \
  QldpcVerification.Input.Bicycle298Match \
  QldpcVerification.Lattice.Bicycle298Arithmetic \
  QldpcVerification.Bicycle298 \
  QldpcVerification.Input.Bicycle346Data \
  QldpcVerification.Input.Bicycle346Match \
  QldpcVerification.Lattice.Bicycle346Arithmetic \
  QldpcVerification.Bicycle346 \
  QldpcVerification.Input.Bicycle422Data \
  QldpcVerification.Input.Bicycle422Match \
  QldpcVerification.Lattice.Bicycle422Arithmetic \
  QldpcVerification.Bicycle422 \
  QldpcVerification.Input.Bicycle454Data \
  QldpcVerification.Input.Bicycle454Match \
  QldpcVerification.Lattice.Bicycle454Arithmetic \
  QldpcVerification.Bicycle454 \
  QldpcVerification \
; do
  lake --log-level=error -d lean build "$target"
done
lake -d lean env lean lean/QldpcVerification/BatchAudit.lean
lake -d lean env lean lean/QldpcVerification/FamilyAudit.lean
lake -d lean env lean lean/QldpcVerification/WindingAudit.lean
lake -d lean env lean lean/QldpcVerification/BicycleAudit.lean
lake -d lean env lean lean/QldpcVerification/KernelAudit.lean
