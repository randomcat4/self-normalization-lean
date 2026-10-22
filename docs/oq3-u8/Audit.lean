import Shao.OQ3.FiniteNormalSpan
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.stageAtom_normalValue_lattice,
    `Shao.OQ3.addedAtom_normal_difference,
    `Shao.OQ3.normal_lattice_of_stage_range,
    `Shao.OQ3.normal_lattice_span_le_of_positive_atoms,
    `Shao.OQ3.stage_normal_span_maximal,
    `Shao.OQ3.finite_atomic_normal_span_maximal,
    `Shao.OQ3.finite_original_normal_span_maximal,
    `Shao.OQ3.exists_source_finite_maximal_normal_family]
  let stems : Array Name := #[
    `Shao.OQ3.HasNormalLattice,
    `Shao.OQ3.IsMaximalNormalLattice,
    `Shao.OQ3.stageAtom_normalValue_lattice,
    `Shao.OQ3.addedAtom_normal_difference,
    `Shao.OQ3.normal_lattice_of_stage_range,
    `Shao.OQ3.normal_lattice_span_le_of_positive_atoms,
    `Shao.OQ3.stage_normal_span_maximal,
    `Shao.OQ3.finite_atomic_normal_span_maximal,
    `Shao.OQ3.finite_original_normal_span_maximal,
    `Shao.OQ3.exists_source_finite_maximal_normal_family]
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut targetCount : Nat := 0
  for (name, info) in env.constants.toList do
    if stems.any (fun stem => stem.isPrefixOf name) ||
        (`_private.Shao.OQ3.FiniteNormalSpan).isPrefixOf name then
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
  logInfo m!"U8_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U8_ALL_THEOREMS {theoremCount}"
  logInfo m!"U8_ALL_DECLARATIONS {allCount}"
  logInfo m!"U8_AXIOM_GATE PASS"
