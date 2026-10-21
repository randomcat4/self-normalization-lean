import Shao.OQ4.KilledBlockBounds
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.hsq_block_parameters,
    `Shao.OQ4.principalCosine_depth_lower_bound,
    `Shao.OQ4.killed_block_layer_bound,
    `Shao.OQ4.killed_block_residual_bound,
    `Shao.OQ4.killed_block_mass_bound,
    `Shao.OQ4.killed_block_finite_absorption]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `Shao.OQ4.KilledBlockBounds
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then newCount := newCount + 1
  unless newCount == 23 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_BLOCK_BOUNDS_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_BLOCK_BOUNDS_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_BLOCK_BOUNDS_AUDITED_CONSTANTS {count}"
