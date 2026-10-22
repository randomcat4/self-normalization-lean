import Shao.OQ3.NormalTangentMoments
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.centeredNormalProjection_memLp_two,
    `Shao.OQ3.centeredNormalProjection_integral_zero,
    `Shao.OQ3.centeredNormalProjection_second_moment,
    `Shao.OQ3.finite_atomic_normal_tangent_moments]
  let stems : Array Name := #[`Shao.OQ3.centeredNormalProjection] ++ targets
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut targetCount : Nat := 0
  for (name, info) in env.constants.toList do
    if stems.any (fun stem => stem.isPrefixOf name) ||
        (`_private.Shao.OQ3.NormalTangentMoments).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 4 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U12C_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U12C_ALL_THEOREMS {theoremCount}"
  logInfo m!"U12C_ALL_DECLARATIONS {allCount}"
  logInfo m!"U12C_AXIOM_GATE PASS"
