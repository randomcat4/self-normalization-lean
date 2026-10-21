import Shao.OQ4.ReflectedSurvival
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.reflected_prefixSum,
    `Shao.OQ4.reflection_preimage_closedUpper,
    `Shao.OQ4.reflection_preimage_lowerBlockSurvival,
    `Shao.OQ4.lowerBlockSurvival_eq_closed_lower_prefixes,
    `Shao.OQ4.iid_reflected_product_law,
    `Shao.OQ4.reflected_closedUpper_probability,
    `Shao.OQ4.reflected_lowerBlockSurvival_probability,
    `Shao.OQ4.standardNormalCDF_reflection,
    `Shao.OQ4.strict_cdf_error_of_standardNormalCDF_error,
    `Shao.OQ4.iid_reflected_cdf_error,
    `Shao.OQ4.reflected_concentration_constant_nonneg,
    `Shao.OQ4.reflected_survival_constant_nonneg,
    `Shao.OQ4.iidIntervalConcentration_of_standardNormalCDF_error,
    `Shao.OQ4.iidOneSidedSurvival_of_cdf_and_two_original_sp,
    `Shao.OQ4.iid_survival_and_concentration_of_cdf_and_two_original_sp]
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
      if owner == `Shao.OQ4.ReflectedSurvival then newCount := newCount + 1
  unless newCount == 29 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_REFLECTED_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_REFLECTED_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_REFLECTED_AUDITED_CONSTANTS {count}"
