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
import Shao.OQ4.RademacherLatticeShift
import Shao.OQ4.RademacherS2Assembly
import Shao.OQ4.RademacherScalarBounds
import Shao.OQ4.RademacherSpectralPairing
import Shao.OQ4.RademacherSpectralTail
import Shao.OQ4.ReflectedSurvival
import Shao.OQ4.SpitzerKernelBounds
import Shao.OQ4.TruncatedEnergy
import Shao.OQ4.VarianceScaling
import Shao.OQ4.RademacherScaleAssembly
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedTheorems : List Name := [
    `Shao.OQ4.RademacherScaleAssembly.DA2,
    `Shao.OQ4.RademacherScaleAssembly.DA2_subcritical]
  let expectedDefinitions : List Name := [
    `Shao.OQ4.RademacherScaleAssembly.eta3]
  let expectedOwned : List String := [
    "Shao.OQ4.RademacherScaleAssembly.DA2",
    "Shao.OQ4.RademacherScaleAssembly.DA2_subcritical",
    "Shao.OQ4.RademacherScaleAssembly.eta3",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.zero_of_abs_le",
    "Shao.OQ4.RademacherLatticeShift.delta.eq_1",
    "Shao.OQ4.RademacherScalarBounds.lambda.eq_1",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_1",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_2",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_3",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_4",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_5",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_6",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_7",
    "Shao.OQ4.RademacherScaleAssembly.eta3.eq_1",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_1",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_2",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_3",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_4",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_5",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_6",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_7"]
  for name in expectedTheorems do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  for name in expectedDefinitions do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing public definition: {name}"
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
    `Shao.OQ4.RademacherLatticeShift,
    `Shao.OQ4.RademacherS2Assembly,
    `Shao.OQ4.RademacherScalarBounds,
    `Shao.OQ4.RademacherSpectralPairing,
    `Shao.OQ4.RademacherSpectralTail,
    `Shao.OQ4.ReflectedSurvival,
    `Shao.OQ4.SpitzerKernelBounds,
    `Shao.OQ4.TruncatedEnergy,
    `Shao.OQ4.VarianceScaling,
    `Shao.OQ4.RademacherScaleAssembly]
  for name in expectedModules do
    unless env.header.moduleNames.contains name do throwError "Missing actual module {name}"
  let actualModules := env.header.moduleNames.filter fun n => (`Shao.OQ4).isPrefixOf n
  unless actualModules.size == expectedModules.length do throwError "Actual OQ4 module count mismatch"
  for name in actualModules do
    unless expectedModules.contains name do throwError "Unexpected OQ4 module {name}"
  let mut count : Nat := 0
  let mut definitionCount : Nat := 0
  let mut owned : List Name := []
  let mut ownedDefinitions : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    if (`Shao).isPrefixOf owner || (`Shao.OQ4).isPrefixOf name || (`Shao.OQ4).isPrefixOf (privateToUserName name) then
      if info.isUnsafe || info.isPartial then throwError "Unsafe or partial selected declaration {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      count := count + 1
      let isDefinition := match info with | .defnInfo _ => true | _ => false
      if isDefinition then definitionCount := definitionCount + 1
      if owner == `Shao.OQ4.RademacherScaleAssembly then
        owned := name :: owned
        if isDefinition then ownedDefinitions := ownedDefinitions + 1
  unless owned.length == expectedOwned.length do throwError "Target actual owner count mismatch"
  for name in expectedOwned do
    unless owned.any (fun n => n.toString == name) do throwError "Expected target-owned declaration missing {name}"
  for name in owned do
    unless expectedOwned.contains name.toString do throwError "Unexpected target-owned declaration {name}"
  unless ownedDefinitions == expectedDefinitions.length do throwError "Target definition count mismatch"
  logInfo m!"OQ4_DA2_PARENT_PUBLIC_THEOREMS {expectedTheorems.length}"
  logInfo m!"OQ4_DA2_PARENT_PUBLIC_DEFINITIONS {expectedDefinitions.length}"
  logInfo m!"OQ4_DA2_PARENT_TARGET_OWNED {owned.length}"
  logInfo m!"OQ4_DA2_PARENT_PROJECT_RECORDS {count}"
  logInfo m!"OQ4_DA2_PARENT_PROJECT_DEFINITIONS {definitionCount}"
  logInfo m!"OQ4_DA2_PARENT_TARGET_DEFINITIONS {ownedDefinitions}"
