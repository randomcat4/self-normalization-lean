import Shao.OQ4.LaplaceGenerating
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.summable_laplaceW,
    `Shao.OQ4.summable_laplaceG,
    `Shao.OQ4.exp_neg_reciprocal_gap,
    `Shao.OQ4.generating_upper_of_W_lower,
    `Shao.OQ4.antitone_coefficient_bound_of_generating_bound,
    `Shao.OQ4.reciprocal_log_step,
    `Shao.OQ4.finite_harmonic_log_bound,
    `Shao.OQ4.sqrt_reciprocal_step,
    `Shao.OQ4.finite_sqrt_tail_bound,
    `Shao.OQ4.reciprocal_sqrt_tail,
    `Shao.OQ4.laplaceW_lower_bound,
    `Shao.OQ4.laplaceG_upper_bound,
    `Shao.OQ4.laplace_coefficient_bound]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `Shao.OQ4.LaplaceGenerating
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then newCount := newCount + 1
  unless newCount == 25 do
    throwError "Unexpected module-owned count: {newCount}"
  logInfo m!"OQ4_GENERATING_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_GENERATING_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_GENERATING_AUDITED_CONSTANTS {count}"
