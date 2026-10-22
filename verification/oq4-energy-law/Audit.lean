import Shao.OQ4.EnergyTiltedLaw
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.energyTiltedLaw_density_measurable,
    `Shao.OQ4.energyTiltedLaw_normalizer_pos,
    `Shao.OQ4.energyTiltedLaw_isProbabilityMeasure,
    `Shao.OQ4.energyTiltedLaw_real_apply,
    `Shao.OQ4.energyTiltedLaw_ae_support,
    `Shao.OQ4.energyTiltedLaw_integral,
    `Shao.OQ4.energyTilt_original_moment_inputs,
    `Shao.OQ4.energyTilt_weighted_integrable,
    `Shao.OQ4.energyTilt_exp_difference_bound,
    `Shao.OQ4.energyTilt_weight_difference_inside,
    `Shao.OQ4.energyTilt_moment_pointwise,
    `Shao.OQ4.energyTilt_weighted_moment_integrability,
    `Shao.OQ4.energyTiltedLaw_moment_integrability,
    `Shao.OQ4.energyTilt_first_numerator_bound,
    `Shao.OQ4.energyTilt_second_numerator_bound,
    `Shao.OQ4.energyTilt_third_numerator_bound,
    `Shao.OQ4.energyTilt_inverse_normalizer_le,
    `Shao.OQ4.energyTilt_normalizer_difference_bound,
    `Shao.OQ4.energyTilt_constants_nonneg,
    `Shao.OQ4.energyTiltedLaw_mean_bound,
    `Shao.OQ4.energyTiltedLaw_second_moment_bound,
    `Shao.OQ4.energyTiltedLaw_third_moment_bound]
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
      if owner == `Shao.OQ4.EnergyTiltedLaw then newCount := newCount + 1
  unless newCount == 54 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_ENERGY_LAW_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_ENERGY_LAW_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_ENERGY_LAW_AUDITED_CONSTANTS {count}"
