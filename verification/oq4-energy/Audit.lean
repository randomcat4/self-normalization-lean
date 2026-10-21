import Shao.OQ4.TruncatedEnergy
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.energyWeight_measurable,
    `Shao.OQ4.energyWeight_nonneg,
    `Shao.OQ4.energyWeight_at_zero,
    `Shao.OQ4.energyNormalizer_at_zero,
    `Shao.OQ4.energy_argument_bounds,
    `Shao.OQ4.energyWeight_le,
    `Shao.OQ4.energyWeight_lower_indicator,
    `Shao.OQ4.energyWeight_integrable,
    `Shao.OQ4.energy_third_moment_pointwise,
    `Shao.OQ4.energy_third_moment_payments,
    `Shao.OQ4.energy_cutoff_mass_lower,
    `Shao.OQ4.energyNormalizer_bounds,
    `Shao.OQ4.energy_exp_remainder_bound,
    `Shao.OQ4.energyRemainder_measurable,
    `Shao.OQ4.energyRemainder_pointwise,
    `Shao.OQ4.energyRemainder_integral_bound,
    `Shao.OQ4.energyNormalizerErrorConstant_nonneg,
    `Shao.OQ4.energyNormalizer_expansion]
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
      if owner == `Shao.OQ4.TruncatedEnergy then newCount := newCount + 1
  unless newCount == 50 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_ENERGY_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_ENERGY_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_ENERGY_AUDITED_CONSTANTS {count}"
