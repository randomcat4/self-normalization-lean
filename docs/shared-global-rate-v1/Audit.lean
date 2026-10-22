import Shao.Probability.BivariateLegendre
import Lean

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleName := `Shao.Probability.BivariateLegendre
  let defs : Array Name := #[
    `Shao.Probability.bivariateMGFDomain,
    `Shao.Probability.bivariateLogMGF,
    `Shao.Probability.bivariateLegendreRate]
  let targets : Array Name := #[
    `Shao.Probability.bivariateLogMGF_spec,
    `Shao.Probability.bivariateLegendreRate_test_le,
    `Shao.Probability.bivariateLegendreRate_eq_of_attained_bound,
    `Shao.Probability.bivariateLegendreRate_unique_minimizer_of_tests]
  for name in defs do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing frozen definition {name}"
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut publicCount : Nat := 0
  let mut defsCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == moduleName
      | none => false
    if owned then
      if info.isAxiom then throwError "New module-owned axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"OWNED_DECL {name}\nLEVEL_PARAMS {info.levelParams}\nTYPE {info.type}\nAXIOMS {axioms}"
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then publicCount := publicCount + 1
      if defs.contains name then defsCount := defsCount + 1
  unless publicCount == 4 do throwError "Frozen public theorem count mismatch {publicCount}"
  unless defsCount == 3 do throwError "Frozen definition count mismatch {defsCount}"
  logInfo m!"BIVARIATE_FROZEN_DEFINITIONS {defsCount}"
  logInfo m!"BIVARIATE_PUBLIC_THEOREMS {publicCount}"
  logInfo m!"BIVARIATE_ALL_THEOREMS {theoremCount}"
  logInfo m!"BIVARIATE_ALL_MODULE_OWNED_CONSTANTS {allCount}"
  logInfo m!"BIVARIATE_MODULE_OWNER_AXIOM_GATE PASS"
