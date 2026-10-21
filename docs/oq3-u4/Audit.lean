import Shao.OQ3.InverseTilt
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.integrable_continuous_of_fixed_bounds, `Shao.OQ3.inverseExp_integrable,
    `Shao.OQ3.inverseNormalizer_pos, `Shao.OQ3.originalMeasure_isProbabilityMeasure,
    `Shao.OQ3.originalMeasure_ae_bounds, `Shao.OQ3.originalMeasure_integrable_id,
    `Shao.OQ3.originalMeasure_singleton, `Shao.OQ3.originalMeasure_real_singleton,
    `Shao.OQ3.originalMeasure_atom_pos, `Shao.OQ3.originalMeasure_centered,
    `Shao.OQ3.originalMeasure_retilt, `Shao.OQ3.originalMeasure_forward_normalizer,
    `Shao.OQ3.exists_source_original_family]
  let definitions : Array Name := #[`Shao.OQ3.inverseNormalizer, `Shao.OQ3.originalMeasure]
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
        (`_private.Shao.OQ3.InverseTilt).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 13 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U4_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U4_ALL_THEOREMS {theoremCount}"
  logInfo m!"U4_ALL_DECLARATIONS {allCount}"
  logInfo m!"U4_AXIOM_GATE PASS"
