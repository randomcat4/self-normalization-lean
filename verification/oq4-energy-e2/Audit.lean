import Shao.OQ4.EnergyE2Bounds
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.energyE2Constant_dominates,
    `Shao.OQ4.energyE2_abs_sub_zero_bound,
    `Shao.OQ4.energyE2_mean_small,
    `Shao.OQ4.energyE2_log_bound,
    `Shao.OQ4.energyE2_common_bounds,
    `Shao.OQ4.energyE2_fixed_law_bounds]
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
      if owner == `Shao.OQ4.EnergyE2Bounds then newCount := newCount + 1
  logInfo m!"OQ4_ENERGY_E2_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_ENERGY_E2_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_ENERGY_E2_AUDITED_CONSTANTS {count}"
