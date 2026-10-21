import Shao.OQ4.EnergyRelativePathBounds
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.energyRelativePath_errors_nonneg,
    `Shao.OQ4.energyRelativePath_bounds_of_e2,
    `Shao.OQ4.energyRelativePath_common_bounds,
    `Shao.OQ4.energyRelativePath_integral_iid,
    `Shao.OQ4.energyRelativePath_iid_of_e2,
    `Shao.OQ4.energyRelativePath_common_bounds_iid]
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
      if owner == `Shao.OQ4.EnergyRelativePathBounds then newCount := newCount + 1
  logInfo m!"OQ4_ENERGY_RELATIVE_PATH_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_ENERGY_RELATIVE_PATH_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_ENERGY_RELATIVE_PATH_AUDITED_CONSTANTS {count}"
