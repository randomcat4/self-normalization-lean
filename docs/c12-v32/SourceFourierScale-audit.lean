import Shao.Probability.SourceFourierScale
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `Shao.Probability.SourceFourierScale
  let publicNames := #[`Shao.sourceTruncation_gamma_bounds,
    `Shao.sourceTruncation_oddPower_scale_inputs]
  let mut targetCount := 0
  let mut targetTheorems := 0
  let mut publicCount := 0
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
        logInfo m!"TARGET_DECL {name} AXIOMS {axioms}"
  unless targetCount >= 4 && publicCount == 2 && dependencyCount > targetCount do
    throwError "Incomplete audit target={targetCount}, public={publicCount}, dependency={dependencyCount}"
  logInfo m!"AUDITED_TARGET_CONSTANTS {targetCount}"
  logInfo m!"AUDITED_TARGET_THEOREMS {targetTheorems}"
  logInfo m!"AUDITED_PUBLIC_THEOREMS {publicCount}"
  logInfo m!"AUDITED_DEPENDENCY_CONSTANTS {dependencyCount}"
  logInfo "WHITELIST_ONLY propext Classical.choice Quot.sound"

set_option pp.all true in
#check @Shao.sourceTruncation_gamma_bounds
set_option pp.all true in
#check @Shao.sourceTruncation_oddPower_scale_inputs

#print axioms Shao.sourceTruncation_gamma_bounds
#print axioms Shao.sourceTruncation_oddPower_scale_inputs
