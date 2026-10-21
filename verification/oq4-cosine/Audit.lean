import Shao.OQ4.CosineCoefficients
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.sin_taylor_cubic_bound,
    `Shao.OQ4.cos_taylor_cubic_bound,
    `Shao.OQ4.cosine_coefficients_third_moment_bound,
    `Shao.OQ4.cosine_coefficients_h_bound]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing OQ4 R0 public theorem: {name}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Shao.OQ4).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
  logInfo m!"OQ4_R0_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_R0_AUDITED_CONSTANTS {count}"
