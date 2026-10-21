import Shao
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if `Shao.isPrefixOf name && info.isTheorem then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}
TYPE {info.type}
AXIOMS {axioms}"
      elabCommand (← `(#print axioms $(mkIdent name)))
      count := count + 1
  unless count > 0 do
    throwError "No project theorem was audited"
  logInfo m!"AUDITED_THEOREMS {count}"
