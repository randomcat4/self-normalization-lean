import Shao.OQ3.AtomicMeasure
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.atomicMeasure_singleton, `Shao.OQ3.atomicMeasure_real_singleton,
    `Shao.OQ3.atomicMeasure_isProbabilityMeasure, `Shao.OQ3.atomicMeasure_ae_range,
    `Shao.OQ3.atomicMeasure_ae_bounds, `Shao.OQ3.integrable_atomicMeasure_iff,
    `Shao.OQ3.integral_atomicMeasure, `Shao.OQ3.atomicMeasure_integral_of_hasSum,
    `Shao.OQ3.atomicMeasure_constraints, `Shao.OQ3.atomicMeasure_mean,
    `Shao.OQ3.exists_source_measure_family]
  let definitions : Array Name := #[`Shao.OQ3.atomicMeasure]
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  for name in definitions do
    unless (env.find? name).isSome do throwError "Missing definition {name}"
  let prefixes := targets ++ definitions
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut targetCount : Nat := 0
  for (name, info) in env.constants.toList do
    if prefixes.any (fun stem => stem.isPrefixOf name) ||
        (`_private.Shao.OQ3.AtomicMeasure).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 11 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U3B_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U3B_ALL_THEOREMS {theoremCount}"
  logInfo m!"U3B_ALL_DECLARATIONS {allCount}"
  logInfo m!"U3B_AXIOM_GATE PASS"
