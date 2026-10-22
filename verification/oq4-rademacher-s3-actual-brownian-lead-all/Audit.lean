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
import Shao.OQ4.RademacherCriticalPhase
import Shao.OQ4.RademacherFiniteBasis
import Shao.OQ4.RademacherFiniteS1
import Shao.OQ4.RademacherIteration
import Shao.OQ4.RademacherLatticeShift
import Shao.OQ4.RademacherS2Assembly
import Shao.OQ4.RademacherS3Assembly
import Shao.OQ4.RademacherScalarBounds
import Shao.OQ4.RademacherScaleAssembly
import Shao.OQ4.RademacherSpectralPairing
import Shao.OQ4.RademacherSpectralTail
import Shao.OQ4.ReflectedSurvival
import Shao.OQ4.SpitzerKernelBounds
import Shao.OQ4.TruncatedEnergy
import Shao.OQ4.VarianceScaling
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedTheorems : List Name := [
    `Shao.OQ4.RademacherS3Assembly.definition_bridges,
    `Shao.OQ4.RademacherS3Assembly.finite_identities,
    `Shao.OQ4.RademacherS3Assembly.zero_time,
    `Shao.OQ4.RademacherS3Assembly.small_cells,
    `Shao.OQ4.RademacherS3Assembly.brownian_object,
    `Shao.OQ4.RademacherS3Assembly.g_pos,
    `Shao.OQ4.RademacherS3Assembly.finite_ALG,
    `Shao.OQ4.RademacherS3Assembly.S3_DOM,
    `Shao.OQ4.RademacherS3Assembly.S3_ALG,
    `Shao.OQ4.RademacherS3Assembly.S3_MAIN,
    `Shao.OQ4.RademacherS3Assembly.S3_MAIN_epsilon]
  let expectedDefinitions : List Name := [
    `Shao.OQ4.RademacherS3Assembly.H,
    `Shao.OQ4.RademacherS3Assembly.N,
    `Shao.OQ4.RademacherS3Assembly.t,
    `Shao.OQ4.RademacherS3Assembly.a,
    `Shao.OQ4.RademacherS3Assembly.rho,
    `Shao.OQ4.RademacherS3Assembly.eps,
    `Shao.OQ4.RademacherS3Assembly.q,
    `Shao.OQ4.RademacherS3Assembly.R,
    `Shao.OQ4.RademacherS3Assembly.A,
    `Shao.OQ4.RademacherS3Assembly.p,
    `Shao.OQ4.RademacherS3Assembly.K,
    `Shao.OQ4.RademacherS3Assembly.D,
    `Shao.OQ4.RademacherS3Assembly.u,
    `Shao.OQ4.RademacherS3Assembly.z,
    `Shao.OQ4.RademacherS3Assembly.lambda,
    `Shao.OQ4.RademacherS3Assembly.x,
    `Shao.OQ4.RademacherS3Assembly.g,
    `Shao.OQ4.RademacherS3Assembly.G,
    `Shao.OQ4.RademacherS3Assembly.b,
    `Shao.OQ4.RademacherS3Assembly.T,
    `Shao.OQ4.RademacherS3Assembly.W,
    `Shao.OQ4.RademacherS3Assembly.C]
  let expectedOwned : List String := [
    "Shao.OQ4.RademacherS3Assembly.A",
    "Shao.OQ4.RademacherS3Assembly.C",
    "Shao.OQ4.RademacherS3Assembly.C.eq_1",
    "Shao.OQ4.RademacherS3Assembly.D",
    "Shao.OQ4.RademacherS3Assembly.G",
    "Shao.OQ4.RademacherS3Assembly.G._proof_1",
    "Shao.OQ4.RademacherS3Assembly.H",
    "Shao.OQ4.RademacherS3Assembly.K",
    "Shao.OQ4.RademacherS3Assembly.N",
    "Shao.OQ4.RademacherS3Assembly.N.eq_1",
    "Shao.OQ4.RademacherS3Assembly.R",
    "Shao.OQ4.RademacherS3Assembly.R.eq_1",
    "Shao.OQ4.RademacherS3Assembly.S3_ALG",
    "Shao.OQ4.RademacherS3Assembly.S3_DOM",
    "Shao.OQ4.RademacherS3Assembly.S3_MAIN",
    "Shao.OQ4.RademacherS3Assembly.S3_MAIN_epsilon",
    "Shao.OQ4.RademacherS3Assembly.T",
    "Shao.OQ4.RademacherS3Assembly.T.congr_simp",
    "Shao.OQ4.RademacherS3Assembly.T.eq_1",
    "Shao.OQ4.RademacherS3Assembly.W",
    "Shao.OQ4.RademacherS3Assembly.a",
    "Shao.OQ4.RademacherS3Assembly.a.eq_1",
    "Shao.OQ4.RademacherS3Assembly.b",
    "Shao.OQ4.RademacherS3Assembly.b.congr_simp",
    "Shao.OQ4.RademacherS3Assembly.b.eq_1",
    "Shao.OQ4.RademacherS3Assembly.brownian_object",
    "Shao.OQ4.RademacherS3Assembly.definition_bridges",
    "Shao.OQ4.RademacherS3Assembly.eps",
    "Shao.OQ4.RademacherS3Assembly.finite_ALG",
    "Shao.OQ4.RademacherS3Assembly.finite_ALG._simp_1_1",
    "Shao.OQ4.RademacherS3Assembly.finite_identities",
    "Shao.OQ4.RademacherS3Assembly.g",
    "Shao.OQ4.RademacherS3Assembly.g.eq_1",
    "Shao.OQ4.RademacherS3Assembly.g_pos",
    "Shao.OQ4.RademacherS3Assembly.lambda",
    "Shao.OQ4.RademacherS3Assembly.p",
    "Shao.OQ4.RademacherS3Assembly.q",
    "Shao.OQ4.RademacherS3Assembly.rho",
    "Shao.OQ4.RademacherS3Assembly.small_cells",
    "Shao.OQ4.RademacherS3Assembly.t",
    "Shao.OQ4.RademacherS3Assembly.u",
    "Shao.OQ4.RademacherS3Assembly.x",
    "Shao.OQ4.RademacherS3Assembly.x.eq_1",
    "Shao.OQ4.RademacherS3Assembly.z",
    "Shao.OQ4.RademacherS3Assembly.zero_time",
    "_private.Shao.OQ4.RademacherS3Assembly.0.Shao.OQ4.RademacherS3Assembly.scale_domain"]
  for name in expectedTheorems do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  for name in expectedDefinitions do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing public definition: {name}"
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
      if owner == `Shao.OQ4.RademacherS3Assembly then
        owned := name :: owned
        if isDefinition then ownedDefinitions := ownedDefinitions + 1
  unless owned.length == expectedOwned.length do throwError "Target actual owner count mismatch"
  for name in expectedOwned do
    unless owned.any (fun n => n.toString == name) do throwError "Expected target-owned declaration missing {name}"
  for name in owned do
    unless expectedOwned.contains name.toString do throwError "Unexpected target-owned declaration {name}"
  unless ownedDefinitions == 22 do throwError "Target definition count mismatch"
  logInfo m!"OQ4_S3_PARENT_PUBLIC_THEOREMS {expectedTheorems.length}"
  logInfo m!"OQ4_S3_PARENT_PUBLIC_DEFINITIONS {expectedDefinitions.length}"
  logInfo m!"OQ4_S3_PARENT_TARGET_OWNED {owned.length}"
  logInfo m!"OQ4_S3_PARENT_PROJECT_RECORDS {count}"
  logInfo m!"OQ4_S3_PARENT_PROJECT_DEFINITIONS {definitionCount}"
  logInfo m!"OQ4_S3_PARENT_TARGET_DEFINITIONS {ownedDefinitions}"
