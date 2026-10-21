import Shao.OQ4.KernelAbsorption
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.kernel_finite_absorption]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `Shao.OQ4.KernelAbsorption
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then newCount := newCount + 1
  unless newCount == 4 do
    throwError "Unexpected actual module constant count: {newCount}"
  logInfo m!"OQ4_ABSORPTION_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_ABSORPTION_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_ABSORPTION_AUDITED_CONSTANTS {count}"
