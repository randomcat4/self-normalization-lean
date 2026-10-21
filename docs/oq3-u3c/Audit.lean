import Shao.OQ3.FiniteStageMeasure
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.finiteMass_constraints, `Shao.OQ3.exists_uniform_finite_radius,
    `Shao.OQ3.finiteMass_nonneg, `Shao.OQ3.atomicMeasure_finiteMass_ae_range,
    `Shao.OQ3.originalMeasure_finiteMass_ae_range, `Shao.OQ3.finite_original_properties,
    `Shao.OQ3.finite_original_atom_pos, `Shao.OQ3.exists_source_finite_and_limit_family]
  let definitions : Array Name := #[`Shao.OQ3.finiteMass]
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
        (`_private.Shao.OQ3.FiniteStageMeasure).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 8 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U3C_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U3C_ALL_THEOREMS {theoremCount}"
  logInfo m!"U3C_ALL_DECLARATIONS {allCount}"
  logInfo m!"U3C_AXIOM_GATE PASS"
