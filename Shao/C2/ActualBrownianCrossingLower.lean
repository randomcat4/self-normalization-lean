import Shao.C2.BrownianBridgeLaw
import Shao.Probability.GaussianTail

set_option autoImplicit false
noncomputable section
namespace Shao.C2.ActualBrownianCrossingLower
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination
open scoped NNReal

theorem brownian_weak_absolute_crossing_lower
    {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (x : ℝ) :
    Shao.standardNormalTail x ≤ PB.real {omegaB | ∃ t : BridgeTime,
        x ≤ |B ⟨(t : ℝ), t.property.1⟩ omegaB|} := by
  have hEndpoint : PB.real {omegaB | x < B 1 omegaB} = Shao.standardNormalTail x := by
    exact (hB.toIsPreBrownianReal.hasLaw_eval 1).measureReal_eq measurableSet_Ioi
  rw [← hEndpoint]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro omegaB homega
  refine ⟨(1 : BridgeTime), ?_⟩
  change x ≤ |B 1 omegaB|
  exact homega.le.trans (le_abs_self _)

theorem brownian_weak_absolute_crossing_pos
    {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (x : ℝ) :
    0 < PB.real {omegaB | ∃ t : BridgeTime,
        x ≤ |B ⟨(t : ℝ), t.property.1⟩ omegaB|} := by
  exact ((Shao.standardNormalTail_basic.2.2.1 x).1).trans_le
    (brownian_weak_absolute_crossing_lower B PB hB x)

theorem brownian_weak_absolute_crossing_small_window_lower
    {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (x : ℝ) (hx : x ≤ 1) :
    Shao.standardNormalTail 1 ≤ PB.real {omegaB | ∃ t : BridgeTime,
        x ≤ |B ⟨(t : ℝ), t.property.1⟩ omegaB|} := by
  exact (Shao.standardNormalTail_basic.1 hx).trans
    (brownian_weak_absolute_crossing_lower B PB hB x)

end Shao.C2.ActualBrownianCrossingLower
