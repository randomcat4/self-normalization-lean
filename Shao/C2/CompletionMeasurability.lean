import Shao.C2.BridgeDomination
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
namespace Shao.C2.CompletionMeasurability
open MeasureTheory Set
open Shao.C2.BridgeDomination

abbrev CompletionParameters := ℝ × ℝ × ℝ × ℝ

theorem continuous_bridgePath_parameters :
    Continuous (fun q : BridgeNoise × CompletionParameters =>
      bridgePath q.2.2.1 q.2.2.2.1 q.2.2.2.2 q.1) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (BridgeNoise × CompletionParameters) × BridgeTime =>
    (1 - (p.2 : ℝ)) * p.1.2.2.1 + (p.2 : ℝ) * p.1.2.2.2.2 +
      Real.sqrt p.1.2.2.2.1 * p.1.1.val p.2)
  fun_prop

theorem isOpen_strictUpper_parameters :
    IsOpen {q : BridgeNoise × CompletionParameters |
      q.1 ∈ strictUpper q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2} := by
  let f : BridgeNoise × CompletionParameters → C(BridgeTime, ℝ) := fun q =>
    bridgePath q.2.2.1 q.2.2.2.1 q.2.2.2.2 q.1 - ContinuousMap.const BridgeTime q.2.1
  have hc : Continuous (fun q : BridgeNoise × CompletionParameters =>
      ContinuousMap.const BridgeTime q.2.1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : (BridgeNoise × CompletionParameters) × BridgeTime => p.1.2.1)
    fun_prop
  have hf : Continuous f := continuous_bridgePath_parameters.sub hc
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo
    (X := BridgeTime) isCompact_univ (isOpen_Iio (a := (0 : ℝ)))
  simpa [f, strictUpper, Set.MapsTo, sub_neg] using ho.preimage hf

theorem isOpen_strictLower_parameters :
    IsOpen {q : BridgeNoise × CompletionParameters |
      q.1 ∈ strictLower q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2} := by
  let f : BridgeNoise × CompletionParameters → C(BridgeTime, ℝ) := fun q =>
    bridgePath q.2.2.1 q.2.2.2.1 q.2.2.2.2 q.1 + ContinuousMap.const BridgeTime q.2.1
  have hc : Continuous (fun q : BridgeNoise × CompletionParameters =>
      ContinuousMap.const BridgeTime q.2.1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : (BridgeNoise × CompletionParameters) × BridgeTime => p.1.2.1)
    fun_prop
  have hf : Continuous f := continuous_bridgePath_parameters.add hc
  have ho := ContinuousMap.isOpen_setOfPred_mapsTo
    (X := BridgeTime) isCompact_univ (isOpen_Ioi (a := (0 : ℝ)))
  simpa [f, strictLower, Set.MapsTo, neg_lt_iff_pos_add', add_comm] using ho.preimage hf

theorem isOpen_strictInterval_parameters :
    IsOpen {q : BridgeNoise × CompletionParameters |
      q.1 ∈ strictInterval q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2} := by
  exact isOpen_strictUpper_parameters.inter isOpen_strictLower_parameters

theorem measurable_upperCompletion_parameters (ν : Measure BridgeNoise) [SFinite ν] :
    Measurable (fun p : CompletionParameters => upperCompletion ν p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (measurable_measure_prodMk_right (μ := ν)
    isOpen_strictUpper_parameters.measurableSet).ennreal_toReal

theorem measurable_lowerCompletion_parameters (ν : Measure BridgeNoise) [SFinite ν] :
    Measurable (fun p : CompletionParameters => lowerCompletion ν p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (measurable_measure_prodMk_right (μ := ν)
    isOpen_strictLower_parameters.measurableSet).ennreal_toReal

theorem measurable_intervalCompletion_parameters (ν : Measure BridgeNoise) [SFinite ν] :
    Measurable (fun p : CompletionParameters => intervalCompletion ν p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  exact (measurable_measure_prodMk_right (μ := ν)
    isOpen_strictInterval_parameters.measurableSet).ennreal_toReal

end Shao.C2.CompletionMeasurability
