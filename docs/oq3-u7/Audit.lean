import Shao.OQ3.RegularCovariance
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.centered_parabola_integral_eq,
    `Shao.OQ3.centered_parabola_integral_pos,
    `Shao.OQ3.parabolaCovariance_det_pos,
    `Shao.OQ3.normalVariance_eq_covariance,
    `Shao.OQ3.normalVariance_pos,
    `Shao.OQ3.transverseVariance_pos,
    `Shao.OQ3.transverseVariance_le_variance_id,
    `Shao.OQ3.atomic_id_variance,
    `Shao.OQ3.sourceEll_lt_one_div_thirty,
    `Shao.OQ3.atomic_transverse_bounds,
    `Shao.OQ3.atomic_curvature_pos,
    `Shao.OQ3.exists_source_finite_and_limit_regular_family]
  let stems : Array Name := #[
    `Shao.OQ3.parabolaCovariance,
    `Shao.OQ3.normalVariance,
    `Shao.OQ3.transverseVariance,
    `Shao.OQ3.centered_parabola_integral_eq,
    `Shao.OQ3.centered_parabola_integral_pos,
    `Shao.OQ3.parabolaCovariance_det_pos,
    `Shao.OQ3.normalVariance_eq_covariance,
    `Shao.OQ3.normalVariance_pos,
    `Shao.OQ3.transverseVariance_pos,
    `Shao.OQ3.transverseVariance_le_variance_id,
    `Shao.OQ3.atomic_id_variance,
    `Shao.OQ3.sourceEll_lt_one_div_thirty,
    `Shao.OQ3.atomic_transverse_bounds,
    `Shao.OQ3.atomic_curvature_pos,
    `Shao.OQ3.exists_source_finite_and_limit_regular_family]
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut targetCount : Nat := 0
  for (name, info) in env.constants.toList do
    if stems.any (fun stem => stem.isPrefixOf name) ||
        (`_private.Shao.OQ3.RegularCovariance).isPrefixOf name then
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
  logInfo m!"U7_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U7_ALL_THEOREMS {theoremCount}"
  logInfo m!"U7_ALL_DECLARATIONS {allCount}"
  logInfo m!"U7_AXIOM_GATE PASS"
