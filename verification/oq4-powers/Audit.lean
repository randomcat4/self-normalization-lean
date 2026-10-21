import Shao.OQ4.CosinePowers
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.cosine_powers_scalar_bounds,
    `Shao.OQ4.cosine_powers_inverse_scalar,
    `Shao.OQ4.cosine_powers_log_linear_scalar,
    `Shao.OQ4.cosine_powers_log_error_scalar,
    `Shao.OQ4.cosineCoefficient_large_h_remainder,
    `Shao.OQ4.cosineCoefficient_large_h_bounds,
    `Shao.OQ4.cosineCoefficient_inverse_pow_bound,
    `Shao.OQ4.cosineCoefficient_inverse_pow_uniform,
    `Shao.OQ4.cosineCoefficient_floor_inverse_bounds,
    `Shao.OQ4.cosineCoefficient_log_error,
    `Shao.OQ4.cosineCoefficient_log_error_mul]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing cosine-powers public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `Shao.OQ4.CosinePowers
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then
        newCount := newCount + 1
  unless newCount == 25 do
    throwError "Unexpected number of cosine-powers constants: {newCount}"
  logInfo m!"OQ4_POWERS_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_POWERS_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_POWERS_AUDITED_CONSTANTS {count}"
