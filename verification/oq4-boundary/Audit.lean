import Shao.OQ4.BoundaryOccupation
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.measurable_reverseBlock,
    `Shao.OQ4.measurableSet_closedUpper,
    `Shao.OQ4.measurableSet_lowerBlockSurvival,
    `Shao.OQ4.prefixSum_append,
    `Shao.OQ4.prefixSum_reverseBlock,
    `Shao.OQ4.measurePreserving_reverseBlock,
    `Shao.OQ4.measurePreserving_append,
    `Shao.OQ4.measurableSet_movingIntervalEvent,
    `Shao.OQ4.movingIntervalEvent_probability_le,
    `Shao.OQ4.surviving_layer_subset,
    `Shao.OQ4.boundary_occupation_block_bound,
    `Shao.OQ4.half_blocks_sqrt_bound,
    `Shao.OQ4.boundary_occupation_half_bound,
    `Shao.OQ4.boundary_occupation_hsq_bound]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `Shao.OQ4.BoundaryOccupation
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then newCount := newCount + 1
  unless newCount == 41 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_BOUNDARY_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_BOUNDARY_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_BOUNDARY_AUDITED_CONSTANTS {count}"
