import Shao.OQ3.SourceStarter
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.sourceEll_pos, `Shao.OQ3.source_base_centering_values,
    `Shao.OQ3.sourceConstraint3_det, `Shao.OQ3.sourceConstraint3_det_neg,
    `Shao.OQ3.source_constraintMatrix_det, `Shao.OQ3.source_constraintMatrix_det_neg,
    `Shao.OQ3.source_constraintMatrix_nonsingular, `Shao.OQ3.sourceTripleMass_pos,
    `Shao.OQ3.sourceTriple_constraints, `Shao.OQ3.sourceTriple_square_moment,
    `Shao.OQ3.sourceTripleQ_bounds, `Shao.OQ3.sourceStarter_constraints,
    `Shao.OQ3.exists_source_starter_delta, `Shao.OQ3.exists_source_starter]
  let definitions : Array Name := #[
    `Shao.OQ3.sourceU, `Shao.OQ3.sourceEll, `Shao.OQ3.sourceA,
    `Shao.OQ3.sourceB, `Shao.OQ3.sourceC, `Shao.OQ3.sourceDenominator,
    `Shao.OQ3.sourceZ, `Shao.OQ3.sourceTripleMass, `Shao.OQ3.sourceTripleQ,
    `Shao.OQ3.sourceConstraint3, `Shao.OQ3.sourceTripleCorrection,
    `Shao.OQ3.sourceStarterWeight, `Shao.OQ3.sourceStarterQ]
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
        (`_private.Shao.OQ3.SourceStarter).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 14 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U2_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U2_ALL_THEOREMS {theoremCount}"
  logInfo m!"U2_ALL_DECLARATIONS {allCount}"
  logInfo m!"U2_AXIOM_GATE PASS"
