import Shao.OQ3.NormalLayerConditionalLaw
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.normalLayerCharacteristic_zero_eq_mass,
    `Shao.OQ3.normalLayerConditionalLaw_isProbabilityMeasure,
    `Shao.OQ3.charFun_normalLayerConditionalLaw,
    `Shao.OQ3.eventually_stage_normalLayer_mass_pos,
    `Shao.OQ3.stage_normalLayerConditionalLaw_charFun_tendsto]
  let stems : Array Name := #[`Shao.OQ3.normalLayerConditionalLaw] ++ targets
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut targetCount : Nat := 0
  for (name, info) in env.constants.toList do
    if stems.any (fun stem => stem.isPrefixOf name) ||
        (`_private.Shao.OQ3.NormalLayerConditionalLaw).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 5 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U13C_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U13C_ALL_THEOREMS {theoremCount}"
  logInfo m!"U13C_ALL_DECLARATIONS {allCount}"
  logInfo m!"U13C_AXIOM_GATE PASS"
