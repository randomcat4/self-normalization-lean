import Shao.OQ3.PositiveRate
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.originalMeasure_ae_range, `Shao.OQ3.atomicMeasure_normalValue,
    `Shao.OQ3.original_log_atom_ratio, `Shao.OQ3.originalAtomEntropy_hasSum,
    `Shao.OQ3.originalAtomEntropy_eq, `Shao.OQ3.inverseNormalizer_gt_exp_neg_mean,
    `Shao.OQ3.saddleRate_pos, `Shao.OQ3.originalAtomEntropy_pos,
    `Shao.OQ3.exists_source_positive_entropy_family]
  let definitions : Array Name := #[`Shao.OQ3.saddleRate, `Shao.OQ3.originalAtomEntropy]
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
        (`_private.Shao.OQ3.PositiveRate).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 9 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U5A_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U5A_ALL_THEOREMS {theoremCount}"
  logInfo m!"U5A_ALL_DECLARATIONS {allCount}"
  logInfo m!"U5A_AXIOM_GATE PASS"
