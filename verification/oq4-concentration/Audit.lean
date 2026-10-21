import Shao.OQ4.IntervalConcentration
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.real_Ioc_eq_real_Iic_sub,
    `Shao.OQ4.closed_interval_mass_bound_from_cdf,
    `Shao.OQ4.standardNormalCDF_eq_real,
    `Shao.OQ4.standardGaussian_density_le_one,
    `Shao.OQ4.standardGaussian_Ioc_mass_le_length,
    `Shao.OQ4.standardNormalCDF_lipschitz,
    `Shao.OQ4.third_absolute_moment_ge_one,
    `Shao.OQ4.iid_closed_unit_concentration_of_cdf_error]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `Shao.OQ4.IntervalConcentration
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then newCount := newCount + 1
  unless newCount == 13 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_CONCENTRATION_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_CONCENTRATION_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_CONCENTRATION_AUDITED_CONSTANTS {count}"
