import Shao.OQ4.AveragedResidual
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.measurable_Kcos,
    `Shao.OQ4.measurable_overshootPotential,
    `Shao.OQ4.integrable_overshoot_integrand,
    `Shao.OQ4.integrable_abs_cosineResidual,
    `Shao.OQ4.averaged_cosine_residual_bound]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing averaged-residual public theorem: {name}"
  let roots : List Name := [
    `Shao.OQ4.cosineResidual, `Shao.OQ4.overshootPotential] ++ expected
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Shao.OQ4).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if roots.any (fun root => root.isPrefixOf name) then
        newCount := newCount + 1
  unless newCount == 8 do
    throwError "Unexpected number of averaged-residual constants: {newCount}"
  logInfo m!"OQ4_AVERAGED_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_AVERAGED_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_AVERAGED_AUDITED_CONSTANTS {count}"
