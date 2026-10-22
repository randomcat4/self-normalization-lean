import Shao.OQ4.EnergyLinearTiltLaw
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.energyLinear_density_measurable,
    `Shao.OQ4.energyLinear_exponent_bounds,
    `Shao.OQ4.energyLinearTiltLaw_ae_support,
    `Shao.OQ4.energyLinear_power_exp_integrable,
    `Shao.OQ4.energyLinear_integrability,
    `Shao.OQ4.energyLinearNormalizer_bounds,
    `Shao.OQ4.energyLinearNormalizer_pos,
    `Shao.OQ4.energyLinearTiltLaw_isProbabilityMeasure,
    `Shao.OQ4.energyLinearTiltLaw_real_apply,
    `Shao.OQ4.energyLinearTiltLaw_integral,
    `Shao.OQ4.energyLinearTiltLaw_moments,
    `Shao.OQ4.energyLinearNormalizer_zero,
    `Shao.OQ4.energyLinearTiltLaw_zero,
    `Shao.OQ4.energyLinearMean_zero]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
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
      if owner == `Shao.OQ4.EnergyLinearTiltLaw then newCount := newCount + 1
  unless newCount == 24 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_ENERGY_LINEAR_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_ENERGY_LINEAR_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_ENERGY_LINEAR_AUDITED_CONSTANTS {count}"
