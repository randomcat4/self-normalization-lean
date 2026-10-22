import Shao.OQ4.AveragedResidual
import Shao.OQ4.BoundaryOccupation
import Shao.OQ4.CosineCoefficients
import Shao.OQ4.CosinePowers
import Shao.OQ4.DelayedRecurrence
import Shao.OQ4.EnergyE1Bounds
import Shao.OQ4.EnergyE2Bounds
import Shao.OQ4.EnergyJointTransport
import Shao.OQ4.EnergyLinearPathLaw
import Shao.OQ4.EnergyLinearTiltCentering
import Shao.OQ4.EnergyLinearTiltComparisons
import Shao.OQ4.EnergyLinearTiltDerivatives
import Shao.OQ4.EnergyLinearTiltLaw
import Shao.OQ4.EnergyLinearTiltVarianceWindow
import Shao.OQ4.EnergyLogNormalizer
import Shao.OQ4.EnergyPathLaw
import Shao.OQ4.EnergyRelativePathBounds
import Shao.OQ4.EnergyTiltedLaw
import Shao.OQ4.FiniteSurvivalLaplace
import Shao.OQ4.Foundations
import Shao.OQ4.IntervalConcentration
import Shao.OQ4.KernelAbsorption
import Shao.OQ4.KernelRecurrence
import Shao.OQ4.KilledBlockBounds
import Shao.OQ4.KilledCosine
import Shao.OQ4.KilledIteration
import Shao.OQ4.KilledKernel
import Shao.OQ4.KilledPathLaw
import Shao.OQ4.LaplaceGenerating
import Shao.OQ4.LaplaceTail
import Shao.OQ4.OccupationPayment
import Shao.OQ4.OvershootMoment
import Shao.OQ4.OvershootSum
import Shao.OQ4.RademacherAllModes
import Shao.OQ4.RademacherCosine
import Shao.OQ4.RademacherFiniteBasis
import Shao.OQ4.RademacherFiniteS1
import Shao.OQ4.RademacherIteration
import Shao.OQ4.RademacherScalarBounds
import Shao.OQ4.ReflectedSurvival
import Shao.OQ4.SpitzerKernelBounds
import Shao.OQ4.TruncatedEnergy
import Shao.OQ4.VarianceScaling
import Shao.OQ4.RademacherSpectralPairing
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedModules : List Name := [
    `Shao.OQ4.AveragedResidual,
    `Shao.OQ4.BoundaryOccupation,
    `Shao.OQ4.CosineCoefficients,
    `Shao.OQ4.CosinePowers,
    `Shao.OQ4.DelayedRecurrence,
    `Shao.OQ4.EnergyE1Bounds,
    `Shao.OQ4.EnergyE2Bounds,
    `Shao.OQ4.EnergyJointTransport,
    `Shao.OQ4.EnergyLinearPathLaw,
    `Shao.OQ4.EnergyLinearTiltCentering,
    `Shao.OQ4.EnergyLinearTiltComparisons,
    `Shao.OQ4.EnergyLinearTiltDerivatives,
    `Shao.OQ4.EnergyLinearTiltLaw,
    `Shao.OQ4.EnergyLinearTiltVarianceWindow,
    `Shao.OQ4.EnergyLogNormalizer,
    `Shao.OQ4.EnergyPathLaw,
    `Shao.OQ4.EnergyRelativePathBounds,
    `Shao.OQ4.EnergyTiltedLaw,
    `Shao.OQ4.FiniteSurvivalLaplace,
    `Shao.OQ4.Foundations,
    `Shao.OQ4.IntervalConcentration,
    `Shao.OQ4.KernelAbsorption,
    `Shao.OQ4.KernelRecurrence,
    `Shao.OQ4.KilledBlockBounds,
    `Shao.OQ4.KilledCosine,
    `Shao.OQ4.KilledIteration,
    `Shao.OQ4.KilledKernel,
    `Shao.OQ4.KilledPathLaw,
    `Shao.OQ4.LaplaceGenerating,
    `Shao.OQ4.LaplaceTail,
    `Shao.OQ4.OccupationPayment,
    `Shao.OQ4.OvershootMoment,
    `Shao.OQ4.OvershootSum,
    `Shao.OQ4.RademacherAllModes,
    `Shao.OQ4.RademacherCosine,
    `Shao.OQ4.RademacherFiniteBasis,
    `Shao.OQ4.RademacherFiniteS1,
    `Shao.OQ4.RademacherIteration,
    `Shao.OQ4.RademacherScalarBounds,
    `Shao.OQ4.ReflectedSurvival,
    `Shao.OQ4.SpitzerKernelBounds,
    `Shao.OQ4.TruncatedEnergy,
    `Shao.OQ4.VarianceScaling,
    `Shao.OQ4.RademacherSpectralPairing]
  for name in expectedModules do
    unless env.header.moduleNames.contains name do throwError "Missing actual module {name}"
  let mut actualModuleCount : Nat := 0
  for name in env.header.moduleNames do
    if (`Shao.OQ4).isPrefixOf name then
      actualModuleCount := actualModuleCount + 1
      unless expectedModules.contains name do throwError "Unexpected OQ4 module {name}"
  unless actualModuleCount == expectedModules.length do throwError "Actual module count mismatch"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    if (`Shao.OQ4).isPrefixOf name || (`Shao.OQ4).isPrefixOf owner then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nOWNER {owner}\nAXIOMS {axioms}"
      count := count + 1
      if owner == `Shao.OQ4.RademacherSpectralPairing then newCount := newCount + 1
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_PAIRING_ALL_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_PAIRING_ALL_AUDITED_CONSTANTS {count}"
