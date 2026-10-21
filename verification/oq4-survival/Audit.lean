import Shao.OQ4.FiniteSurvivalLaplace
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.measurable_maxLaplaceIntegrand,
    `Shao.OQ4.measurable_endpointLaplaceIntegrand,
    `Shao.OQ4.maxLaplaceIntegrand_bounds,
    `Shao.OQ4.endpointLaplaceIntegrand_bounds,
    `Shao.OQ4.integrable_maxLaplaceIntegrand,
    `Shao.OQ4.integrable_endpointLaplaceIntegrand,
    `Shao.OQ4.maxLaplaceMean_bounds,
    `Shao.OQ4.endpointLaplaceMean_bounds,
    `Shao.OQ4.maxWithZero_empty,
    `Shao.OQ4.maxLaplaceMean_zero,
    `Shao.OQ4.finiteSumLaplacePayment_eq_one_sub_endpoint,
    `Shao.OQ4.prefix_projection_map_pi,
    `Shao.OQ4.prefix_projection_prefixSum,
    `Shao.OQ4.prefix_projection_max_le,
    `Shao.OQ4.measurable_paymentLaplaceIntegrand,
    `Shao.OQ4.maxLaplaceMean_antitone,
    `Shao.OQ4.summable_maxLaplace_series,
    `Shao.OQ4.summable_endpointLaplace_series,
    `Shao.OQ4.summable_paymentLaplace_series,
    `Shao.OQ4.maxLaplace_original_sp_to_normalized,
    `Shao.OQ4.maxLaplaceMean_bound_of_cdf_and_original_sp,
    `Shao.OQ4.measurableSet_closedUpper_laplace,
    `Shao.OQ4.closedUpper_probability_le_laplace,
    `Shao.OQ4.closedUpper_bound_of_cdf_and_original_sp]
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
    let owned := owner == `Shao.OQ4.FiniteSurvivalLaplace
    if (`Shao.OQ4).isPrefixOf name || (`Shao.OQ4).isPrefixOf owner then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then newCount := newCount + 1
  unless newCount == 30 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_SURVIVAL_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_SURVIVAL_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_SURVIVAL_AUDITED_CONSTANTS {count}"
