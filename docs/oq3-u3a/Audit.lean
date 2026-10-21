import Shao.OQ3.SummableAtoms
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `Shao.OQ3.addedAtom_feature_bound, `Shao.OQ3.summable_addedFeature,
    `Shao.OQ3.finiteBase_tendsto, `Shao.OQ3.limitingMoment_hasSum,
    `Shao.OQ3.exists_limiting_radius, `Shao.OQ3.limitingMass_pos_of_lower,
    `Shao.OQ3.exists_source_limit_family, `Shao.OQ3.exists_positive_small_summable,
    `Shao.OQ3.fixedAtom_injective, `Shao.OQ3.fixedAtom_bounds]
  let definitions : Array Name := #[
    `Shao.OQ3.AtomicIndex, `Shao.OQ3.fixedAtom, `Shao.OQ3.infiniteAddedMoment,
    `Shao.OQ3.limitingBase, `Shao.OQ3.limitingMass, `Shao.OQ3.finiteBase]
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
        (`_private.Shao.OQ3.SummableAtoms).isPrefixOf name then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless targetCount == 10 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U3A_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U3A_ALL_THEOREMS {theoremCount}"
  logInfo m!"U3A_ALL_DECLARATIONS {allCount}"
  logInfo m!"U3A_AXIOM_GATE PASS"
