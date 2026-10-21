import Shao.OQ4.KernelRecurrence
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.principalCosine_measurable,
    `Shao.OQ4.principalCosine_abs_le_one,
    `Shao.OQ4.principalCosine_nonneg,
    `Shao.OQ4.kernelCosine_measurable,
    `Shao.OQ4.kernelCosine_bounds,
    `Shao.OQ4.principalKcos_eq_action,
    `Shao.OQ4.principalResidual_measurable,
    `Shao.OQ4.principalResidual_bound,
    `Shao.OQ4.principalResidual_integrable,
    `Shao.OQ4.kernelCosine_defect,
    `Shao.OQ4.kernelCosine_delayed_defect,
    `Shao.OQ4.kernelMass_block,
    `Shao.OQ4.normalizedKernelCosine_step,
    `Shao.OQ4.normalizedKernelCosine_delayed,
    `Shao.OQ4.normalizedKernelMass_block,
    `Shao.OQ4.normalizedKernelMass_nonneg,
    `Shao.OQ4.normalizedKernelCosine_nonneg,
    `Shao.OQ4.normalizedKernelMass_finite_bound]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing kernel-recurrence public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `Shao.OQ4.KernelRecurrence
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then
        newCount := newCount + 1
  unless newCount == 37 do
    throwError "Unexpected number of kernel-recurrence constants: {newCount}"
  logInfo m!"OQ4_KERNEL_RECURRENCE_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_KERNEL_RECURRENCE_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_KERNEL_RECURRENCE_AUDITED_CONSTANTS {count}"
