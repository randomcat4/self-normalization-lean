import Shao.OQ4.RademacherCosine
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.RademacherCosine.integer_closed_iff,
    `Shao.OQ4.RademacherCosine.killedKernel_row,
    `Shao.OQ4.RademacherCosine.killedKernel_cos_integrable,
    `Shao.OQ4.RademacherCosine.Kcos_principal,
    `Shao.OQ4.RademacherCosine.killedKernel_integral_principal,
    `Shao.OQ4.RademacherCosine.angle_pos,
    `Shao.OQ4.RademacherCosine.angle_lt_pi_div_two,
    `Shao.OQ4.RademacherCosine.rho_pos,
    `Shao.OQ4.RademacherCosine.rho_lt_one]
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
      if owner == `Shao.OQ4.RademacherCosine then newCount := newCount + 1
  logInfo m!"OQ4_RADEMACHER_COSINE_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_RADEMACHER_COSINE_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_RADEMACHER_COSINE_AUDITED_CONSTANTS {count}"
