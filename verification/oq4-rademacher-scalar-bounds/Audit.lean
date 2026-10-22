import Shao.OQ4.RademacherScalarBounds
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.RademacherScalarBounds.z_eq_angle,
    `Shao.OQ4.RademacherScalarBounds.rho_eq_cosine_rho,
    `Shao.OQ4.RademacherScalarBounds.H_ge_two,
    `Shao.OQ4.RademacherScalarBounds.H_pos,
    `Shao.OQ4.RademacherScalarBounds.u_pos,
    `Shao.OQ4.RademacherScalarBounds.u_le_pi_div_eight,
    `Shao.OQ4.RademacherScalarBounds.z_pos,
    `Shao.OQ4.RademacherScalarBounds.z_le_pi_div_four,
    `Shao.OQ4.RademacherScalarBounds.sin_u_pos,
    `Shao.OQ4.RademacherScalarBounds.cos_u_pos,
    `Shao.OQ4.RademacherScalarBounds.cos_z_pos,
    `Shao.OQ4.RademacherScalarBounds.a_pos,
    `Shao.OQ4.RademacherScalarBounds.rho_pos,
    `Shao.OQ4.RademacherScalarBounds.rho_lt_one,
    `Shao.OQ4.RademacherScalarBounds.pi_mul_a_div_four_pos,
    `Shao.OQ4.RademacherScalarBounds.SCA0,
    `Shao.OQ4.RademacherScalarBounds.C_a_pos,
    `Shao.OQ4.RademacherScalarBounds.C_rho_pos,
    `Shao.OQ4.RademacherScalarBounds.SCA1,
    `Shao.OQ4.RademacherScalarBounds.SCA2,
    `Shao.OQ4.RademacherScalarBounds.scalar_bounds]
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
      if owner == `Shao.OQ4.RademacherScalarBounds then newCount := newCount + 1
  logInfo m!"OQ4_RADEMACHER_SCALAR_BOUNDS_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_RADEMACHER_SCALAR_BOUNDS_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_RADEMACHER_SCALAR_BOUNDS_AUDITED_CONSTANTS {count}"
