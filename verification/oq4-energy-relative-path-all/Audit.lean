import Shao.OQ4.DelayedRecurrence
import Shao.OQ4.OvershootSum
import Shao.OQ4.OvershootMoment
import Shao.OQ4.VarianceScaling
import Shao.OQ4.Foundations
import Shao.OQ4.CosineCoefficients
import Shao.OQ4.KilledCosine
import Shao.OQ4.OccupationPayment
import Shao.OQ4.AveragedResidual
import Shao.OQ4.KilledKernel
import Shao.OQ4.KilledIteration
import Shao.OQ4.KernelRecurrence
import Shao.OQ4.CosinePowers
import Shao.OQ4.KilledPathLaw
import Shao.OQ4.KernelAbsorption
import Shao.OQ4.BoundaryOccupation
import Shao.OQ4.KilledBlockBounds
import Shao.OQ4.IntervalConcentration
import Shao.OQ4.LaplaceTail
import Shao.OQ4.LaplaceGenerating
import Shao.OQ4.FiniteSurvivalLaplace
import Shao.OQ4.ReflectedSurvival
import Shao.OQ4.SpitzerKernelBounds
import Shao.OQ4.TruncatedEnergy
import Shao.OQ4.EnergyTiltedLaw
import Shao.OQ4.EnergyLogNormalizer
import Shao.OQ4.EnergyE1Bounds
import Shao.OQ4.EnergyLinearTiltLaw
import Shao.OQ4.EnergyLinearTiltDerivatives
import Shao.OQ4.EnergyLinearTiltComparisons
import Shao.OQ4.EnergyLinearTiltVarianceWindow
import Shao.OQ4.EnergyLinearTiltCentering
import Shao.OQ4.EnergyPathLaw
import Shao.OQ4.EnergyE2Bounds
import Shao.OQ4.EnergyLinearPathLaw
import Shao.OQ4.RademacherCosine
import Shao.OQ4.EnergyRelativePathBounds
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
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
      if [`Shao.OQ4.EnergyRelativePathBounds].contains owner then
        newCount := newCount + 1
  logInfo m!"OQ4_ENERGY_RELATIVE_PATH_ALL_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_ENERGY_RELATIVE_PATH_ALL_AUDITED_CONSTANTS {count}"
