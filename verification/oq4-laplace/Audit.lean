import Shao.OQ4.LaplaceTail
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.positiveLaplace_bounds,
    `Shao.OQ4.integrable_positiveLaplace,
    `Shao.OQ4.laplacePayment_bounds,
    `Shao.OQ4.laplaceWeight_nonneg,
    `Shao.OQ4.measurable_strictTail,
    `Shao.OQ4.integrable_laplaceWeight,
    `Shao.OQ4.integral_laplaceWeight,
    `Shao.OQ4.integrable_laplaceTail,
    `Shao.OQ4.laplaceWeight_primitive,
    `Shao.OQ4.laplacePayment_eq_strictTail,
    `Shao.OQ4.standardGaussian_positive_mass,
    `Shao.OQ4.standardNormalCDF_zero,
    `Shao.OQ4.integrable_mul_laplaceWeight,
    `Shao.OQ4.integral_mul_laplaceWeight,
    `Shao.OQ4.strictTail_lower_bound_of_cdf,
    `Shao.OQ4.laplacePayment_lower_bound_of_cdf,
    `Shao.OQ4.iid_integrable_positiveLaplace,
    `Shao.OQ4.finiteSumLaplacePayment_bounds,
    `Shao.OQ4.finiteSumLaplacePayment_lower_bound_of_cdf]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `Shao.OQ4.LaplaceTail
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then newCount := newCount + 1
  unless newCount == 29 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_LAPLACE_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_LAPLACE_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_LAPLACE_AUDITED_CONSTANTS {count}"
