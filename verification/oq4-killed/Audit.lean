import Shao.OQ4.KilledCosine
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.integral_strict_exit_cosine_eq,
    `Shao.OQ4.killed_cosine_identity,
    `Shao.OQ4.killed_cosine_boundary_bound,
    `Shao.OQ4.killed_cosine_residual_bound]
  let roots : List Name := [
    `Shao.OQ4.Kcos, `Shao.OQ4.cosineCoefficient, `Shao.OQ4.sineCoefficient] ++ expected
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing R1/R2 public theorem: {name}"
  let mut allCount : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Shao.OQ4).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if roots.any (fun root => root.isPrefixOf name) then newCount := newCount + 1
  logInfo m!"OQ4_KILLED_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_KILLED_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_KILLED_IMPORTED_CONSTANTS {allCount}"
