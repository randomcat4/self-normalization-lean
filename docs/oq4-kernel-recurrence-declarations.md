# KernelRecurrence declaration ledger

Source SHA256: a4a5fc67cf47c8e188cbe2e2360afa4fa1bfe0a7082bb9f30fbacd6a5ad5c940.

23 explicit declarations: 5 definitions and 18 theorems. Corrected dynamic imported-environment audit found 37 total constants, including 14 generated constants. Every transitive axiom set is a subset of {propext, Classical.choice, Quot.sound}.

## Mechanical correction of the original audit range

The previous count of 36 used explicit declaration roots and their descendants. It missed Shao.OQ4.killedAction.congr_simp, a new constant generated under an imported name. The mathematical source and olean are unchanged. The corrected helper selects every declaration owned by the imported Shao.OQ4.KernelRecurrence module using env.getModuleIdxFor? and env.header.moduleNames, without any namespace/root-name filter. Its actual server import audit passed with 37 declaration records and 37 axiom records. The formerly omitted constant depends on propext, Classical.choice, and Quot.sound.

Frozen-goal correspondence: principal cosine positivity and kernelCosine_bounds cover item 1; kernelCosine_defect is the exact defect; principalResidual_* establish bounded Borel and actual integrability. kernelCosine_delayed_defect is conditional D0 (item 2). kernelMass_block is conditional D1 (item 3). normalizedKernelCosine_step/delayed and normalizedKernelMass_block give exact D2/D3 (item 4). normalizedKernelMass_nonneg, normalizedKernelCosine_nonneg, and normalizedKernelMass_finite_bound give D4 (item 5).

## Explicit declarations

- Shao.OQ4.principalCosine
- Shao.OQ4.principalRate
- Shao.OQ4.kernelCosine
- Shao.OQ4.normalizedKernelCosine
- Shao.OQ4.normalizedKernelMass
- Shao.OQ4.principalCosine_measurable
- Shao.OQ4.principalCosine_abs_le_one
- Shao.OQ4.principalCosine_nonneg
- Shao.OQ4.kernelCosine_measurable
- Shao.OQ4.kernelCosine_bounds
- Shao.OQ4.principalKcos_eq_action
- Shao.OQ4.principalResidual_measurable
- Shao.OQ4.principalResidual_bound
- Shao.OQ4.principalResidual_integrable
- Shao.OQ4.kernelCosine_defect
- Shao.OQ4.kernelCosine_delayed_defect
- Shao.OQ4.kernelMass_block
- Shao.OQ4.normalizedKernelCosine_step
- Shao.OQ4.normalizedKernelCosine_delayed
- Shao.OQ4.normalizedKernelMass_block
- Shao.OQ4.normalizedKernelMass_nonneg
- Shao.OQ4.normalizedKernelCosine_nonneg
- Shao.OQ4.normalizedKernelMass_finite_bound

## Generated declarations

- Shao.OQ4.kernelCosine.congr_simp
- Shao.OQ4.kernelCosine.eq_1
- Shao.OQ4.killedAction.congr_simp
- Shao.OQ4.normalizedKernelCosine_delayed._proof_1_1
- Shao.OQ4.normalizedKernelCosine_step._simp_1_2
- Shao.OQ4.normalizedKernelCosine_step._simp_1_3
- Shao.OQ4.normalizedKernelCosine_step._simp_1_4
- Shao.OQ4.normalizedKernelCosine_step._simp_1_5
- Shao.OQ4.normalizedKernelCosine_step._simp_1_6
- Shao.OQ4.normalizedKernelCosine_step._simp_1_7
- Shao.OQ4.normalizedKernelCosine_step._simp_1_8
- Shao.OQ4.normalizedKernelMass.eq_1
- Shao.OQ4.principalCosine._proof_1
- Shao.OQ4.principalCosine.eq_1

## Complete dynamically enumerated constants

- Shao.OQ4.kernelCosine
- Shao.OQ4.kernelCosine.congr_simp
- Shao.OQ4.kernelCosine.eq_1
- Shao.OQ4.kernelCosine_bounds
- Shao.OQ4.kernelCosine_defect
- Shao.OQ4.kernelCosine_delayed_defect
- Shao.OQ4.kernelCosine_measurable
- Shao.OQ4.kernelMass_block
- Shao.OQ4.killedAction.congr_simp
- Shao.OQ4.normalizedKernelCosine
- Shao.OQ4.normalizedKernelCosine_delayed
- Shao.OQ4.normalizedKernelCosine_delayed._proof_1_1
- Shao.OQ4.normalizedKernelCosine_nonneg
- Shao.OQ4.normalizedKernelCosine_step
- Shao.OQ4.normalizedKernelCosine_step._simp_1_2
- Shao.OQ4.normalizedKernelCosine_step._simp_1_3
- Shao.OQ4.normalizedKernelCosine_step._simp_1_4
- Shao.OQ4.normalizedKernelCosine_step._simp_1_5
- Shao.OQ4.normalizedKernelCosine_step._simp_1_6
- Shao.OQ4.normalizedKernelCosine_step._simp_1_7
- Shao.OQ4.normalizedKernelCosine_step._simp_1_8
- Shao.OQ4.normalizedKernelMass
- Shao.OQ4.normalizedKernelMass.eq_1
- Shao.OQ4.normalizedKernelMass_block
- Shao.OQ4.normalizedKernelMass_finite_bound
- Shao.OQ4.normalizedKernelMass_nonneg
- Shao.OQ4.principalCosine
- Shao.OQ4.principalCosine._proof_1
- Shao.OQ4.principalCosine.eq_1
- Shao.OQ4.principalCosine_abs_le_one
- Shao.OQ4.principalCosine_measurable
- Shao.OQ4.principalCosine_nonneg
- Shao.OQ4.principalKcos_eq_action
- Shao.OQ4.principalRate
- Shao.OQ4.principalResidual_bound
- Shao.OQ4.principalResidual_integrable
- Shao.OQ4.principalResidual_measurable

## Curated axiom summary

- 29 constants: propext, Classical.choice, Quot.sound.
- 7 generated simplification constants: propext.
- 1 generated arithmetic proof: propext, Quot.sound.

The corrected full original audit log remains on the server at repro_outputs/oq4-kernel-recurrence/audit-module.log. The previous incomplete audit.log is preserved for history. The local kernel-summary.json is a curated names/counts/hash/correction summary, not a raw log.
