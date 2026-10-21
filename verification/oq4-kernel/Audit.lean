import Shao.OQ4.KilledKernel
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.translationKernel_apply,
    `Shao.OQ4.killedKernel_apply,
    `Shao.OQ4.killedKernel_mass_le_one,
    `Shao.OQ4.killedKernel_real_mass_le_one,
    `Shao.OQ4.killedKernel_ae_support,
    `Shao.OQ4.killedKernel_integral_bounded,
    `Shao.OQ4.killedKernel_integral_cos]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing killed-kernel public theorem: {name}"
  let roots : List Name := [
    `Shao.OQ4.translationKernel, `Shao.OQ4.killedKernel,
    `Shao.OQ4.killedKernel_isFiniteKernel] ++ expected
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
  unless newCount == 15 do
    throwError "Unexpected number of killed-kernel constants: {newCount}"
  logInfo m!"OQ4_KERNEL_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_KERNEL_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_KERNEL_AUDITED_CONSTANTS {count}"
