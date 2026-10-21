import Shao.OQ3.FiniteConstraints
import Lean

/- Lane-local audit; the shared integration manifest is root-owned. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `Shao.OQ3.compensated_stageMoment,
    `Shao.OQ3.compensatedBase_pos,
    `Shao.OQ3.stageWeight_pos,
    `Shao.OQ3.exists_compensation_radius,
    `Shao.OQ3.stage_mass_one,
    `Shao.OQ3.stage_boundary_moment,
    `Shao.OQ3.addedAtom_normalValue,
    `Shao.OQ3.addedAtom_gt_four,
    `Shao.OQ3.addedAtom_lt_limit,
    `Shao.OQ3.addedAtom_injective,
    `Shao.OQ3.normalValue_baseAtom]
  for name in expected do
    match env.find? name with
    | some info =>
      unless info.isTheorem do
        throwError "Expected theorem: {name}"
    | none => throwError "Missing frozen public theorem: {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut publicCount : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Shao.OQ3).isPrefixOf name ||
        (`_private.Shao.OQ3.FiniteConstraints).isPrefixOf name then
      if info.isAxiom then
        throwError "New project axiom: {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then
        theoremCount := theoremCount + 1
        if expected.contains name then
          publicCount := publicCount + 1
  unless publicCount == 11 do
    throwError "Frozen theorem count changed: {publicCount}"
  logInfo m!"U1_FROZEN_THEOREMS {publicCount}"
  logInfo m!"U1_ALL_THEOREMS {theoremCount}"
  logInfo m!"U1_ALL_DECLARATIONS {allCount}"
  logInfo m!"U1_AXIOM_GATE PASS"
