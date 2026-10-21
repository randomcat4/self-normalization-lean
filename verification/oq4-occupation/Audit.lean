import Shao.OQ4.OccupationPayment
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.measurableSet_boundaryLayer,
    `Shao.OQ4.finite_occupation_payment,
    `Shao.OQ4.finite_occupation_payment_of_le]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing finite occupation public theorem: {name}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Shao.OQ4).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
  logInfo m!"OQ4_OCCUPATION_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_OCCUPATION_AUDITED_CONSTANTS {count}"
