import Shao.OQ4.Foundations
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.overshootCell_nonneg,
    `Shao.OQ4.overshoot_sum_le_cubic,
    `Shao.OQ4.integrable_overshootCell,
    `Shao.OQ4.integral_overshootCell_nonneg,
    `Shao.OQ4.sum_integral_overshootCell_le,
    `Shao.OQ4.summable_integral_overshootCell,
    `Shao.OQ4.tsum_integral_overshootCell_le,
    `Shao.OQ4.delayed_recurrence_bound,
    `Shao.OQ4.path_variance_scaling,
    `Shao.OQ4.standardized_moments,
    `Shao.OQ4.standardized_third_moment_bound,
    `Shao.OQ4.sqrt_variance_parameters,
    `Shao.OQ4.sqrt_variance_standardization,
    `Shao.OQ4.normalized_scale_ratios,
    `Shao.OQ4.sqrt_variance_scale_ratios]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing OQ4 public theorem: {name}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Shao.OQ4).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
  logInfo m!"OQ4_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_AUDITED_CONSTANTS {count}"
