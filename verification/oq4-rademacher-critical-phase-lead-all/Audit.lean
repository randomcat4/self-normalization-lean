import Shao.OQ4.AveragedResidual
import Shao.OQ4.BoundaryOccupation
import Shao.OQ4.CosineCoefficients
import Shao.OQ4.CosinePowers
import Shao.OQ4.DelayedRecurrence
import Shao.OQ4.EnergyE1Bounds
import Shao.OQ4.EnergyE2Bounds
import Shao.OQ4.EnergyJointTransport
import Shao.OQ4.EnergyLinearPathLaw
import Shao.OQ4.EnergyLinearTiltCentering
import Shao.OQ4.EnergyLinearTiltComparisons
import Shao.OQ4.EnergyLinearTiltDerivatives
import Shao.OQ4.EnergyLinearTiltLaw
import Shao.OQ4.EnergyLinearTiltVarianceWindow
import Shao.OQ4.EnergyLogNormalizer
import Shao.OQ4.EnergyPathLaw
import Shao.OQ4.EnergyRelativePathBounds
import Shao.OQ4.EnergyTiltedLaw
import Shao.OQ4.FiniteSurvivalLaplace
import Shao.OQ4.Foundations
import Shao.OQ4.IntervalConcentration
import Shao.OQ4.KernelAbsorption
import Shao.OQ4.KernelRecurrence
import Shao.OQ4.KilledBlockBounds
import Shao.OQ4.KilledCosine
import Shao.OQ4.KilledIteration
import Shao.OQ4.KilledKernel
import Shao.OQ4.KilledPathLaw
import Shao.OQ4.LaplaceGenerating
import Shao.OQ4.LaplaceTail
import Shao.OQ4.OccupationPayment
import Shao.OQ4.OvershootMoment
import Shao.OQ4.OvershootSum
import Shao.OQ4.RademacherAllModes
import Shao.OQ4.RademacherCosine
import Shao.OQ4.RademacherFiniteBasis
import Shao.OQ4.RademacherFiniteS1
import Shao.OQ4.RademacherIteration
import Shao.OQ4.RademacherLatticeShift
import Shao.OQ4.RademacherS2Assembly
import Shao.OQ4.RademacherScalarBounds
import Shao.OQ4.RademacherSpectralPairing
import Shao.OQ4.RademacherSpectralTail
import Shao.OQ4.ReflectedSurvival
import Shao.OQ4.SpitzerKernelBounds
import Shao.OQ4.TruncatedEnergy
import Shao.OQ4.VarianceScaling
import Shao.OQ4.RademacherScaleAssembly
import Shao.OQ4.RademacherCriticalPhase
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedTheorems : List Name := [
    `Shao.OQ4.RademacherCriticalPhase.root_spec,
    `Shao.OQ4.RademacherCriticalPhase.zero_prefix,
    `Shao.OQ4.RademacherCriticalPhase.positive_time,
    `Shao.OQ4.RademacherCriticalPhase.finite_phase,
    `Shao.OQ4.RademacherCriticalPhase.cutoff_spec,
    `Shao.OQ4.RademacherCriticalPhase.scales,
    `Shao.OQ4.RademacherCriticalPhase.scales_on_strict_subsequence,
    `Shao.OQ4.RademacherCriticalPhase.exact_cube,
    `Shao.OQ4.RademacherCriticalPhase.exact_below_cube,
    `Shao.OQ4.RademacherCriticalPhase.cube_subsequence,
    `Shao.OQ4.RademacherCriticalPhase.below_cube_subsequence,
    `Shao.OQ4.RademacherCriticalPhase.up_rounding,
    `Shao.OQ4.RademacherCriticalPhase.down_rounding,
    `Shao.OQ4.RademacherCriticalPhase.nearest_rounding,
    `Shao.OQ4.RademacherCriticalPhase.up_phase,
    `Shao.OQ4.RademacherCriticalPhase.down_phase,
    `Shao.OQ4.RademacherCriticalPhase.nearest_phase,
    `Shao.OQ4.RademacherCriticalPhase.up_subsequence,
    `Shao.OQ4.RademacherCriticalPhase.down_subsequence,
    `Shao.OQ4.RademacherCriticalPhase.nearest_subsequence,
    `Shao.OQ4.RademacherCriticalPhase.phase_realization,
    `Shao.OQ4.RademacherCriticalPhase.cluster_sets,
    `Shao.OQ4.RademacherCriticalPhase.not_convergent]
  let expectedDefinitions : List Name := [
    `Shao.OQ4.RademacherCriticalPhase.root,
    `Shao.OQ4.RademacherCriticalPhase.height,
    `Shao.OQ4.RademacherCriticalPhase.phaseFloor,
    `Shao.OQ4.RademacherCriticalPhase.upperHeight,
    `Shao.OQ4.RademacherCriticalPhase.delta,
    `Shao.OQ4.RademacherCriticalPhase.q,
    `Shao.OQ4.RademacherCriticalPhase.exponent,
    `Shao.OQ4.RademacherCriticalPhase.factor,
    `Shao.OQ4.RademacherCriticalPhase.cutoff,
    `Shao.OQ4.RademacherCriticalPhase.WeakCell,
    `Shao.OQ4.RademacherCriticalPhase.Cluster,
    `Shao.OQ4.RademacherCriticalPhase.target,
    `Shao.OQ4.RademacherCriticalPhase.upIndex,
    `Shao.OQ4.RademacherCriticalPhase.downIndex,
    `Shao.OQ4.RademacherCriticalPhase.nearestIndex,
    `Shao.OQ4.RademacherCriticalPhase.cubeIndex,
    `Shao.OQ4.RademacherCriticalPhase.belowCubeIndex,
    `Shao.OQ4.RademacherCriticalPhase.phaseIndex]
  let expectedOwned : List String := [
    "Shao.OQ4.RademacherCriticalPhase.Cluster",
    "Shao.OQ4.RademacherCriticalPhase.WeakCell",
    "Shao.OQ4.RademacherCriticalPhase.belowCubeIndex",
    "Shao.OQ4.RademacherCriticalPhase.below_cube_subsequence",
    "Shao.OQ4.RademacherCriticalPhase.cluster_sets",
    "Shao.OQ4.RademacherCriticalPhase.cubeIndex",
    "Shao.OQ4.RademacherCriticalPhase.cube_subsequence",
    "Shao.OQ4.RademacherCriticalPhase.cutoff",
    "Shao.OQ4.RademacherCriticalPhase.cutoff_spec",
    "Shao.OQ4.RademacherCriticalPhase.delta",
    "Shao.OQ4.RademacherCriticalPhase.downIndex",
    "Shao.OQ4.RademacherCriticalPhase.down_phase",
    "Shao.OQ4.RademacherCriticalPhase.down_rounding",
    "Shao.OQ4.RademacherCriticalPhase.down_subsequence",
    "Shao.OQ4.RademacherCriticalPhase.exact_below_cube",
    "Shao.OQ4.RademacherCriticalPhase.exact_cube",
    "Shao.OQ4.RademacherCriticalPhase.exponent",
    "Shao.OQ4.RademacherCriticalPhase.factor",
    "Shao.OQ4.RademacherCriticalPhase.finite_phase",
    "Shao.OQ4.RademacherCriticalPhase.height",
    "Shao.OQ4.RademacherCriticalPhase.nearestIndex",
    "Shao.OQ4.RademacherCriticalPhase.nearest_phase",
    "Shao.OQ4.RademacherCriticalPhase.nearest_rounding",
    "Shao.OQ4.RademacherCriticalPhase.nearest_subsequence",
    "Shao.OQ4.RademacherCriticalPhase.not_convergent",
    "Shao.OQ4.RademacherCriticalPhase.phaseFloor",
    "Shao.OQ4.RademacherCriticalPhase.phaseIndex",
    "Shao.OQ4.RademacherCriticalPhase.phase_realization",
    "Shao.OQ4.RademacherCriticalPhase.positive_time",
    "Shao.OQ4.RademacherCriticalPhase.q",
    "Shao.OQ4.RademacherCriticalPhase.root",
    "Shao.OQ4.RademacherCriticalPhase.root_spec",
    "Shao.OQ4.RademacherCriticalPhase.scales",
    "Shao.OQ4.RademacherCriticalPhase.scales_on_strict_subsequence",
    "Shao.OQ4.RademacherCriticalPhase.target",
    "Shao.OQ4.RademacherCriticalPhase.upIndex",
    "Shao.OQ4.RademacherCriticalPhase.up_phase",
    "Shao.OQ4.RademacherCriticalPhase.up_rounding",
    "Shao.OQ4.RademacherCriticalPhase.up_subsequence",
    "Shao.OQ4.RademacherCriticalPhase.upperHeight",
    "Shao.OQ4.RademacherCriticalPhase.zero_prefix",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_DownStable",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_InternalStable",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_TailResult",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_UpStable",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_actual_phase_tail",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_below_cube_cast",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_below_cube_delta_limit",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_below_cube_rounding",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_build_tail_result",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_delta",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_exponent",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_factor",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_injective_nonneg",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_le_inv",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_lt_inv",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_mono",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cube_strict",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cutoff_one",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cutoff_pos",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_delta_not_convergent",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_delta_of_nat_height",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_delta_range",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_cast",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_delta_limit",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_error",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_height_error",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_rounding",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_stable",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_subsequence",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_zero",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube_delta_subsequence",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube_subsequence",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube_weakCell",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_cube",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_cube_delta_subsequence",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_cube_subsequence",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_cube_weakCell",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exponent_not_convergent",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exponent_range",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_factor_not_convergent",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_factor_range",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_height_cube",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_height_nonneg",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_height_pos",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_height_tendsto_atTop",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_height_zero",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_inverse_square_zero",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nat_ceil_error",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nat_floor_agrees_int",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nat_floor_bounds",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nearest_delta_limit",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nearest_error",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nearest_height_error",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nearest_stable",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nearest_subsequence",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_nearest_tie_up",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_q_pos",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_realize_every_phase",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_root_cube",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_root_nonneg",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_root_pos",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_root_zero",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_above",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_below",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_error_bound",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_error_tendsto",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_indices_atTop",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_strict_tail",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_tail_construct",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_simultaneous_of_delta",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_square_scale",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_square_scale_tendsto_atTop",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_strict_index_id_le",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_target_cube",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_time_scale",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_delta_limit",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_error",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_height_error",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_positive",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_rounding",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_stable",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_subsequence",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_zero",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_weakCell_of_cutoff",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_zero_prefix",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_zero_time_scale",
    "Shao.OQ4.RademacherCriticalPhase.belowCubeIndex.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.cubeIndex.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.cutoff.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.delta.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.downIndex.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.down_phase._proof_1_1",
    "Shao.OQ4.RademacherCriticalPhase.exact_below_cube._proof_1_1",
    "Shao.OQ4.RademacherCriticalPhase.exact_below_cube._proof_1_2",
    "Shao.OQ4.RademacherCriticalPhase.exponent.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.factor.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.height.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.nearestIndex._proof_1",
    "Shao.OQ4.RademacherCriticalPhase.nearest_subsequence._proof_1_1",
    "Shao.OQ4.RademacherCriticalPhase.phaseFloor.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.phaseIndex.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.q._proof_1",
    "Shao.OQ4.RademacherCriticalPhase.q.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.root._proof_1",
    "Shao.OQ4.RademacherCriticalPhase.root.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.target.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.upIndex.eq_1",
    "Shao.OQ4.RademacherCriticalPhase.up_subsequence._proof_1_1",
    "Shao.OQ4.RademacherCriticalPhase.upperHeight.eq_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_below_cube_cast._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_exponent._simp_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_exponent._simp_1_2",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_exponent._simp_1_3",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_exponent._simp_1_4",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_exponent._simp_1_5",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_exponent._simp_1_6",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_exponent._simp_1_7",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_factor._simp_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_factor._simp_1_2",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_factor._simp_1_3",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_factor._simp_1_4",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_factor._simp_1_5",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_factor._simp_1_6",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_cluster_factor._simp_1_7",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_delta_limit._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_down_stable._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube_subsequence._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube_subsequence._proof_1_2",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_below_cube_subsequence._proof_1_3",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_cube_subsequence._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_exact_cube_weakCell._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_root_pos._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_strict_tail._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_tail_construct._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_tail_construct._proof_1_2",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_tail_construct._proof_1_3",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_tail_construct._proof_1_4",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_tail_construct._proof_1_5",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_tail_construct._proof_1_6",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_rounded_tail_construct._proof_1_7",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_target_cube._simp_1_2",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_target_cube._simp_1_3",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_target_cube._simp_1_4",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_target_cube._simp_1_5",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_target_cube._simp_1_6",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_target_cube._simp_1_7",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_target_cube._simp_1_8",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_time_scale._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_positive._proof_1_1",
    "_private.Shao.OQ4.RademacherCriticalPhase.0.Shao.OQ4.RademacherCriticalPhase.aux_up_positive._proof_1_2"]
  for name in expectedTheorems do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  for name in expectedDefinitions do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing public definition: {name}"
  let mut count : Nat := 0
  let mut definitionCount : Nat := 0
  let mut owned : List Name := []
  let mut ownedDefinitions : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    if (`Shao).isPrefixOf owner || (`Shao.OQ4).isPrefixOf name || (`Shao.OQ4).isPrefixOf (privateToUserName name) then
      if info.isUnsafe || info.isPartial then throwError "Unsafe or partial selected declaration {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      count := count + 1
      let isDefinition := match info with | .defnInfo _ => true | _ => false
      if isDefinition then definitionCount := definitionCount + 1
      if owner == `Shao.OQ4.RademacherCriticalPhase then
        owned := name :: owned
        if isDefinition then ownedDefinitions := ownedDefinitions + 1
  unless owned.length == expectedOwned.length do throwError "Target actual owner count mismatch"
  for name in expectedOwned do
    unless owned.any (fun n => n.toString == name) do throwError "Expected target-owned declaration missing {name}"
  for name in owned do
    unless expectedOwned.contains name.toString do throwError "Unexpected target-owned declaration {name}"
  unless ownedDefinitions == 22 do throwError "Target definition count mismatch"
  logInfo m!"OQ4_CP_PARENT_PUBLIC_THEOREMS {expectedTheorems.length}"
  logInfo m!"OQ4_CP_PARENT_PUBLIC_DEFINITIONS {expectedDefinitions.length}"
  logInfo m!"OQ4_CP_PARENT_TARGET_OWNED {owned.length}"
  logInfo m!"OQ4_CP_PARENT_PROJECT_RECORDS {count}"
  logInfo m!"OQ4_CP_PARENT_PROJECT_DEFINITIONS {definitionCount}"
  logInfo m!"OQ4_CP_PARENT_TARGET_DEFINITIONS {ownedDefinitions}"
