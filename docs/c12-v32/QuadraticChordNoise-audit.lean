import Shao.Probability.QuadraticChordNoise
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `Shao.Probability.QuadraticChordNoise
  let publicNames := #[
    `Shao.Probability.quadraticTriangle_probability_char,
    `Shao.Probability.quadraticChord_law_data,
    `Shao.Probability.quadraticChordChar_exact,
    `Shao.Probability.quadraticChordChar_cone_gap]
  let definitionNames := #[
    `Shao.Probability.quadraticTriangleLaw,
    `Shao.Probability.quadraticBiasedPairLaw,
    `Shao.Probability.quadraticChordLaw,
    `Shao.Probability.quadraticChordChar]
  let mut targetCount := 0
  let mut targetTheorems := 0
  let mut publicCount := 0
  let mut definitionsCount := 0
  let mut dependencyCount := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    if (`Shao).isPrefixOf owner then
      dependencyCount := dependencyCount + 1
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name} (owner {owner})"
      logInfo m!"DEPENDENCY_DECL {name} OWNER {owner} AXIOMS {axioms}"
      if owner == target then
        targetCount := targetCount + 1
        if info matches .thmInfo _ then
          targetTheorems := targetTheorems + 1
        if publicNames.contains name then
          publicCount := publicCount + 1
        if definitionNames.contains name then
          definitionsCount := definitionsCount + 1
        logInfo m!"TARGET_DECL {name} AXIOMS {axioms}"
  unless targetCount > 0 && publicCount == 4 && definitionsCount == 4 &&
      dependencyCount > targetCount do
    throwError "Incomplete audit target={targetCount}, public={publicCount}, defs={definitionsCount}, dependency={dependencyCount}"
  logInfo m!"AUDITED_TARGET_CONSTANTS {targetCount}"
  logInfo m!"AUDITED_TARGET_THEOREMS {targetTheorems}"
  logInfo m!"AUDITED_PUBLIC_THEOREMS {publicCount}"
  logInfo m!"AUDITED_PUBLIC_DEFINITIONS {definitionsCount}"
  logInfo m!"AUDITED_DEPENDENCY_CONSTANTS {dependencyCount}"
  logInfo "WHITELIST_ONLY propext Classical.choice Quot.sound"

#print axioms Shao.Probability.quadraticTriangle_probability_char
#print axioms Shao.Probability.quadraticChord_law_data
#print axioms Shao.Probability.quadraticChordChar_exact
#print axioms Shao.Probability.quadraticChordChar_cone_gap
