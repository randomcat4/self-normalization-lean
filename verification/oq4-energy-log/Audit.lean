import Shao.OQ4.EnergyLogNormalizer
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.energyLog_constants_nonneg,
    `Shao.OQ4.energyLog_threshold_bounds,
    `Shao.OQ4.energyLog_normalizer_close,
    `Shao.OQ4.energyLog_quadratic_bound,
    `Shao.OQ4.energyLog_square_payment,
    `Shao.OQ4.energyLog_normalizer_error]
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
      if owner == `Shao.OQ4.EnergyLogNormalizer then newCount := newCount + 1
  unless newCount == 17 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_ENERGY_LOG_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_ENERGY_LOG_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_ENERGY_LOG_AUDITED_CONSTANTS {count}"
