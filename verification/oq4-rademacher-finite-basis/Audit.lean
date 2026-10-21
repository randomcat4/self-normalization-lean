import Shao.OQ4.RademacherFiniteBasis
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.RademacherFiniteBasis.theta_one,
    `Shao.OQ4.RademacherFiniteBasis.mu_one,
    `Shao.OQ4.RademacherFiniteBasis.phi_one,
    `Shao.OQ4.RademacherFiniteBasis.orthogonal,
    `Shao.OQ4.RademacherFiniteBasis.square_norm,
    `Shao.OQ4.RademacherFiniteBasis.dual_orthogonal,
    `Shao.OQ4.RademacherFiniteBasis.reconstruction,
    `Shao.OQ4.RademacherFiniteBasis.killedKernel_integrable,
    `Shao.OQ4.RademacherFiniteBasis.killedKernel_integral]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    if (`Shao.OQ4).isPrefixOf name || (`Shao.OQ4).isPrefixOf owner then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nOWNER {owner}\nAXIOMS {axioms}"
      count := count + 1
      if owner == `Shao.OQ4.RademacherFiniteBasis then newCount := newCount + 1
  logInfo m!"OQ4_RADEMACHER_FINITE_BASIS_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_RADEMACHER_FINITE_BASIS_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_RADEMACHER_FINITE_BASIS_AUDITED_CONSTANTS {count}"
