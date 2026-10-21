import Shao
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => (`Shao).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"OWNED_DECL {name} AXIOMS {axioms}"
      count := count + 1
  unless count > 0 do
    throwError "Empty project declaration audit"
  logInfo m!"AUDITED_PROJECT_CONSTANTS {count}"
