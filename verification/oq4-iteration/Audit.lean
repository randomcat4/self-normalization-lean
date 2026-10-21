import Shao.OQ4.KilledIteration
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.killedIterKernel_zero,
    `Shao.OQ4.killedIterKernel_mass_le_one,
    `Shao.OQ4.killedIterKernel_real_mass_le_one,
    `Shao.OQ4.killedIterKernel_ae_support_pos,
    `Shao.OQ4.killedIterKernel_ae_support,
    `Shao.OQ4.killedAction_integrable,
    `Shao.OQ4.killedAction_measurable,
    `Shao.OQ4.killedMass_eq_real,
    `Shao.OQ4.killedMass_nonneg,
    `Shao.OQ4.killedMass_le_one,
    `Shao.OQ4.killedAction_bound_mass,
    `Shao.OQ4.killedAction_bound,
    `Shao.OQ4.killedAction_bounded,
    `Shao.OQ4.killedAction_zero,
    `Shao.OQ4.killedAction_one,
    `Shao.OQ4.killedAction_iterated_integrable,
    `Shao.OQ4.killedAction_semigroup,
    `Shao.OQ4.killedAction_add,
    `Shao.OQ4.killedAction_smul,
    `Shao.OQ4.killedAction_abs,
    `Shao.OQ4.killedAction_mono,
    `Shao.OQ4.killedAction_mono_closed]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing killed-iteration public theorem: {name}"
  let roots : List Name := [
    `Shao.OQ4.killedIterKernel, `Shao.OQ4.killedAction, `Shao.OQ4.killedMass,
    `Shao.OQ4.killedIterKernel_isFiniteKernel] ++ expected
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Shao.OQ4).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if roots.any (fun root => root.isPrefixOf name) then
        newCount := newCount + 1
  unless newCount == 33 do
    throwError "Unexpected number of killed-iteration constants: {newCount}"
  logInfo m!"OQ4_ITERATION_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_ITERATION_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_ITERATION_AUDITED_CONSTANTS {count}"
