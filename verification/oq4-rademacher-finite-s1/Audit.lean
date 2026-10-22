import Shao.OQ4.RademacherFiniteS1
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.RademacherFiniteS1.vector_zero,
    `Shao.OQ4.RademacherFiniteS1.modes_eq,
    `Shao.OQ4.RademacherFiniteS1.even_mode_mem_iff,
    `Shao.OQ4.RademacherFiniteS1.odd_mode_mem_iff,
    `Shao.OQ4.RademacherFiniteS1.mode_parity_partition,
    `Shao.OQ4.RademacherFiniteS1.odd_mode_inverse,
    `Shao.OQ4.RademacherFiniteS1.odd_mode_injective,
    `Shao.OQ4.RademacherFiniteS1.vector_even_zero,
    `Shao.OQ4.RademacherFiniteS1.vector_odd_zero,
    `Shao.OQ4.RademacherFiniteS1.odd_half_angle_bounds,
    `Shao.OQ4.RademacherFiniteS1.odd_half_angle_sin_ne_zero,
    `Shao.OQ4.RademacherFiniteS1.sum_vector_odd,
    `Shao.OQ4.RademacherFiniteS1.survivalCoefficient_odd,
    `Shao.OQ4.RademacherFiniteS1.killedMass_finite_s1,
    `Shao.OQ4.RademacherFiniteS1.closedStrip_probability_finite_s1,
    `Shao.OQ4.RademacherFiniteS1.finite_s1_zero,
    `Shao.OQ4.RademacherFiniteS1.killedKernel_zero_low,
    `Shao.OQ4.RademacherFiniteS1.killedMass_low,
    `Shao.OQ4.RademacherFiniteS1.closedStrip_probability_low]
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
      if owner == `Shao.OQ4.RademacherFiniteS1 then newCount := newCount + 1
  logInfo m!"OQ4_RADEMACHER_FINITE_S1_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_RADEMACHER_FINITE_S1_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_RADEMACHER_FINITE_S1_AUDITED_CONSTANTS {count}"
