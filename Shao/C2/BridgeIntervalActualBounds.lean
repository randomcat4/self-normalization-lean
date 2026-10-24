import Shao.C2.BridgeLowerIdentification
import Shao.C2.IntervalGaussianLargeStep

noncomputable section
namespace Shao.C2.BridgeIntervalActualBounds
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.SourceIntervalCompletion Shao.C2.IntervalGaussianLargeStep
open Shao.C2.ActualIntervalProjection

theorem actual_interval_deriv_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (a y T z : ℝ) (hT : 0 < T) (hy : |y| < a) (hz : |z| < a)
    (hRegular : DifferentiableAt ℝ (fun s : ℝ => intervalCompletion (bridgeLaw B P) a s T z) y) :
    |deriv (fun s : ℝ => intervalCompletion (bridgeLaw B P) a s T z) y| ≤
      4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T) := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  apply Shao.C2.IntervalDerivativeBound.interval_deriv_bound_of_reflection
    (bridgeLaw B P) a y T z hT hy hz ?_ ?_ hRegular
  · intro w hw
    exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B P hB a w T z hT hw (abs_lt.mp hz).2
  · intro w hw
    exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B P hB a w T z hT hw (abs_lt.mp hz).1

theorem actual_interval_deriv_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (a y T z H A : ℝ) (hH : 0 < H) (hHT : H ≤ T) (haA : a ≤ A)
    (hy : |y| < a) (hz : |z| < a)
    (hRegular : DifferentiableAt ℝ (fun s : ℝ => intervalCompletion (bridgeLaw B P) a s T z) y) :
    |deriv (fun s : ℝ => intervalCompletion (bridgeLaw B P) a s T z) y| ≤
      4 / Real.sqrt H * (1 + 2 * A / Real.sqrt H) := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  have hT : 0 < T := hH.trans_le hHT
  apply Shao.C2.IntervalDerivativeBound.interval_deriv_uniform_bound_of_reflection
    (bridgeLaw B P) a y T z H A hH hHT haA hy hz ?_ ?_ hRegular
  · intro w hw
    exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B P hB a w T z hT hw (abs_lt.mp hz).2
  · intro w hw
    exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B P hB a w T z hT hw (abs_lt.mp hz).1

theorem actual_completion_difference_envelope_bound {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (a y T z b : ℝ) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T) (hb : b ^ 2 ≤ T)
    (hzero : T - b ^ 2 = 0 → y + b = z) :
    |sourceIntervalCompletion (bridgeLaw B P) a (y + b) (T - b ^ 2) z - sourceIntervalCompletion (bridgeLaw B P) a y T z| ≤
      2 * intervalEnvelope a y T z b := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  apply Shao.C2.IntervalGaussianLargeStep.completion_difference_envelope_bound (bridgeLaw B P) a y T z b hy hz hT hb hzero
  · intro S hS w hw
    exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B P hB a w S z hS hw (abs_lt.mp hz).2
  · intro S hS w hw
    exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B P hB a w S z hS hw (abs_lt.mp hz).1

theorem actual_interval_large_gaussian_bound {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (a y T z b : ℝ) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T)
    (hb : b ^ 2 ≤ T) (hlarge : T / 2 < b ^ 2) (hzero : T - b ^ 2 = 0 → y + b = z)
    (hRegular : DifferentiableAt ℝ (fun w => sourceIntervalCompletion (bridgeLaw B P) a w T z) y) :
    |sourceRemainder (bridgeLaw B P) a y T z b| ≤
      40 * (|b| / Real.sqrt T) ^ 3 * (1 + |z - y| / Real.sqrt T) ^ 3 * intervalEnvelope a y T z b := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  apply Shao.C2.IntervalGaussianLargeStep.actual_interval_large_gaussian_bound (bridgeLaw B P) a y T z b hy hz hT hb hlarge hzero hRegular
  · intro S hS w hw
    exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B P hB a w S z hS hw (abs_lt.mp hz).2
  · intro S hS w hw
    exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B P hB a w S z hS hw (abs_lt.mp hz).1

end Shao.C2.BridgeIntervalActualBounds
