import Shao.OQ3.SourceGlobalExponentialTests
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.source_saddle_exponential_value_bound,
    `Shao.OQ3.exists_source_tail_exponential_separator]
  let defs : Array Name := #[]
  let stems := defs ++ targets
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  for name in defs do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing frozen definition {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut targetCount : Nat := 0
  for (name, info) in env.constants.toList do
    if stems.any (fun stem => stem.isPrefixOf name) ||
        (`_private.Shao.OQ3.SourceGlobalExponentialTests).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 2 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U19A_FROZEN_DEFINITIONS {defs.size}"
  logInfo m!"U19A_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U19A_ALL_THEOREMS {theoremCount}"
  logInfo m!"U19A_ALL_DECLARATIONS {allCount}"
  logInfo m!"U19A_AXIOM_GATE PASS"
