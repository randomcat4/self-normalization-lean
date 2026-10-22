import Shao.OQ3.SampleBoundary
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.normalDeviation_eq_sum_energy,
    `Shao.OQ3.curved_sample_identity,
    `Shao.OQ3.sourceTail_measurable,
    `Shao.OQ3.sourceTail_iff_curved,
    `Shao.OQ3.sourceTail_on_normal_layer,
    `Shao.OQ3.stage_sample_normal_layer,
    `Shao.OQ3.fixedAtom_normalValue_lower,
    `Shao.OQ3.atomicMeasure_ae_normalValue_lower,
    `Shao.OQ3.originalMeasure_ae_normalValue_lower,
    `Shao.OQ3.normal_likelihood_weight_bound,
    `Shao.OQ3.iid_normal_likelihood_ae_bound,
    `Shao.OQ3.source_atomic_iid_likelihood_ae_bound]
  let stems : Array Name := #[
    `Shao.OQ3.normalDeviation,
    `Shao.OQ3.tangentDeviation,
    `Shao.OQ3.sourceTail,
    `Shao.OQ3.normalDeviation_eq_sum_energy,
    `Shao.OQ3.curved_sample_identity,
    `Shao.OQ3.sourceTail_measurable,
    `Shao.OQ3.sourceTail_iff_curved,
    `Shao.OQ3.sourceTail_on_normal_layer,
    `Shao.OQ3.stage_sample_normal_layer,
    `Shao.OQ3.fixedAtom_normalValue_lower,
    `Shao.OQ3.atomicMeasure_ae_normalValue_lower,
    `Shao.OQ3.originalMeasure_ae_normalValue_lower,
    `Shao.OQ3.normal_likelihood_weight_bound,
    `Shao.OQ3.iid_normal_likelihood_ae_bound,
    `Shao.OQ3.source_atomic_iid_likelihood_ae_bound]
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut targetCount : Nat := 0
  for (name, info) in env.constants.toList do
    if stems.any (fun stem => stem.isPrefixOf name) ||
        (`_private.Shao.OQ3.SampleBoundary).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 12 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U9A_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U9A_ALL_THEOREMS {theoremCount}"
  logInfo m!"U9A_ALL_DECLARATIONS {allCount}"
  logInfo m!"U9A_AXIOM_GATE PASS"
