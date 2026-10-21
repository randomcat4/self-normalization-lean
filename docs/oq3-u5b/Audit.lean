import Shao.OQ3.FiniteStageRate
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.weighted_original_log_atom_ratio,
    `Shao.OQ3.originalAtomEntropy_hasSum_of_nonneg,
    `Shao.OQ3.originalAtomEntropy_eq_of_nonneg,
    `Shao.OQ3.inverseNormalizer_gt_exp_of_two_positive_atoms,
    `Shao.OQ3.entropy_rate_pos_of_two_positive_atoms,
    `Shao.OQ3.finite_original_entropy_rate,
    `Shao.OQ3.exists_source_finite_and_limit_entropy_family]
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut targetCount : Nat := 0
  for (name, info) in env.constants.toList do
    if targets.any (fun stem => stem.isPrefixOf name) ||
        (`_private.Shao.OQ3.FiniteStageRate).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 7 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U5B_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U5B_ALL_THEOREMS {theoremCount}"
  logInfo m!"U5B_ALL_DECLARATIONS {allCount}"
  logInfo m!"U5B_AXIOM_GATE PASS"
