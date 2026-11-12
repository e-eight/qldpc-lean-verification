import QldpcVerification.Audit.Dependencies
import QldpcVerification.Bicycle4
import QldpcVerification.Bicycle58
import QldpcVerification.Bicycle82
import QldpcVerification.Bicycle100
import QldpcVerification.Bicycle110
import QldpcVerification.Bicycle122
import QldpcVerification.Bicycle170
import QldpcVerification.Bicycle226
import QldpcVerification.Bicycle262Lattice
import QldpcVerification.Bicycle278
import QldpcVerification.Bicycle298
import QldpcVerification.Bicycle346
import QldpcVerification.Bicycle362
import QldpcVerification.Bicycle422
import QldpcVerification.Bicycle454
import QldpcVerification.Bicycle562Family
import QldpcVerification.BicycleEven16Family
import QldpcVerification.BicycleEvenStep16
import QldpcVerification.Bicycle262
import QldpcVerification.Bicycle562

/-! Every migrated instance uses the new shortest-relation theorem and analytic
basis bound. The audit rejects stored physical witnesses and grid exclusions. -/

#guard_dependencies QldpcVerification.Bicycle4.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle58.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle82.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle100.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle110.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle122.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle170.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle226.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle262Lattice.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle278.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle298.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle346.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle362.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle422.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle454.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle562Family.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.BicycleEven16Family.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.BicycleEvenStep16.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle262.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]

#guard_dependencies QldpcVerification.Bicycle562.parameters requires [
  QldpcVerification.Bicycle.Connected.Match.parameters_of_shortest,
  QldpcVerification.Lattice.BasisSeparation.BasisData.norm_ge]
  excludes ["finite_exclusion", ".wx", ".wz", "Bicycle262.xCoverage",
    "Bicycle262.zCoverage", "Bicycle562.xCoverage", "Bicycle562.zCoverage",
    "Bicycle262Checks", "Bicycle562Checks"]
