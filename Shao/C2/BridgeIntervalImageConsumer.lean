import Shao.C2.IntervalImageWallLimit
import Shao.C2.IntervalImageWallValues
import Shao.C2.BridgeIntervalActualBounds
import Shao.C2.IntervalGaussianLocal

noncomputable section
namespace Shao.C2.BridgeIntervalImageConsumer
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.SourceIntervalCompletion Shao.C2.ActualIntervalProjection
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageWallValues
open Shao.C2.IntervalImageRevealBounds Shao.C2.IntervalImageWallLimit
open Shao.C2.IntervalGaussianLocal Shao.C2.IntervalGaussianLargeStep

theorem sourceIntervalCompletion_eq_image_of_interior (ν : Measure BridgeNoise)
    (a z S w : ℝ) (ha : 0 < a) (hz : |z| ≤ a) (hS : 0 < S) (hw : |w| ≤ a)
    (hImage : ∀ U : ℝ, 0 < U → ∀ v : ℝ, |v| < a →
      intervalCompletion ν a v U z = intervalImageCandidate a z U v) :
    sourceIntervalCompletion ν a w S z = intervalImageCandidate a z S w := by
  by_cases hw' : |w| < a
  · rw [sourceIntervalCompletion_pos ν a w S z hS]
    exact hImage S hS w hw'
  · have hzero : sourceIntervalCompletion ν a w S z = 0 :=
      sourceIntervalCompletion_exterior ν a w S z (fun h => hw' h.1)
    rw [hzero]
    have heq : |w| = a := le_antisymm hw (le_of_not_gt hw')
    rcases le_total 0 w with hw0 | hw0
    · have hwA : w = a := by simpa only [abs_of_nonneg hw0] using heq
      rw [hwA]
      exact (intervalImageCandidate_upper_wall a z S ha hz hS).symm
    · have hneg : -w = a := by simpa only [abs_of_nonpos hw0] using heq
      have hwA : w = -a := by linarith only [hneg]
      rw [hwA]
      exact (intervalImageCandidate_lower_wall a z S ha hz hS).symm

theorem sourceIntervalCompletion_spatial_hasDerivAt_of_image (ν : Measure BridgeNoise)
    (a y T z : ℝ) (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a) (hT : 0 < T)
    (hImage : ∀ U : ℝ, 0 < U → ∀ v : ℝ, |v| < a →
      intervalCompletion ν a v U z = intervalImageCandidate a z U v) :
    HasDerivAt (fun w => sourceIntervalCompletion ν a w T z)
      (deriv (intervalImageCandidate a z T) y) y := by
  have hDiff : DifferentiableAt ℝ (intervalImageCandidate a z T) y :=
    (imageCandidateSpatial_hasDerivAt 0 a z T y ha hz hT hy).differentiableAt
  have heq : (fun w => sourceIntervalCompletion ν a w T z) =ᶠ[𝓝 y]
      intervalImageCandidate a z T := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with w hw
    rw [sourceIntervalCompletion_pos ν a w T z hT]
    exact hImage T hT w (abs_lt.mpr hw)
  exact hDiff.hasDerivAt.congr_of_eventuallyEq heq

theorem sourceRemainder_eq_image_of_interior (ν : Measure BridgeNoise)
    (a y T z b : ℝ) (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a) (hT : 0 < T)
    (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| ≤ a)
    (hImage : ∀ U : ℝ, 0 < U → ∀ v : ℝ, |v| < a →
      intervalCompletion ν a v U z = intervalImageCandidate a z U v) :
    sourceRemainder ν a y T z b =
      intervalImageCandidate a z (T - b ^ 2) (y + b) - intervalImageCandidate a z T y -
        (b - b ^ 2 * (z - y) / T) * deriv (intervalImageCandidate a z T) y := by
  have hS : 0 < T - b ^ 2 := by linarith only [hT, hsmall]
  unfold sourceRemainder
  rw [sourceIntervalCompletion_eq_image_of_interior ν a z (T - b ^ 2) (y + b) ha hz hS hnew hImage,
    sourceIntervalCompletion_eq_image_of_interior ν a z T y ha hz hT hy.le hImage,
    (sourceIntervalCompletion_spatial_hasDerivAt_of_image ν a y T z ha hy hz hT hImage).deriv]

theorem sourceRemainder_small_bound_of_image (ν : Measure BridgeNoise)
    (a y T z b : ℝ) (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a) (hT : 0 < T)
    (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| ≤ a)
    (hImage : ∀ U : ℝ, 0 < U → ∀ v : ℝ, |v| < a →
      intervalCompletion ν a v U z = intervalImageCandidate a z U v) :
    |sourceRemainder ν a y T z b| ≤
      compensatedProfileConstant * (|b| / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 * intervalIncrementProfile a y T z b := by
  rw [sourceRemainder_eq_image_of_interior ν a y T z b ha hy hz hT hsmall hnew hImage]
  exact intervalImageCandidate_compensated_small_step_closed_bound a y z T b ha hy hz hT hsmall hnew

theorem actual_interval_retained_bound_of_image
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (a y T z b : ℝ) (ha : 0 < a) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T)
    (hb : b ^ 2 ≤ T) (hzero : T - b ^ 2 = 0 → y + b = z)
    (hImage : ∀ U : ℝ, 0 < U → ∀ v : ℝ, |v| < a →
      intervalCompletion (bridgeLaw B P) a v U z = intervalImageCandidate a z U v) :
    |retainedRemainder (bridgeLaw B P) a y T z b| + negativeOvershoot (bridgeLaw B P) a y T z b ≤
      (2 * compensatedProfileConstant + 40) * (|b| / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 * intervalEnvelope a y T z b := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  have hRegular := (sourceIntervalCompletion_spatial_hasDerivAt_of_image
    (bridgeLaw B P) a y T z ha hy hz.le hT hImage).differentiableAt
  apply actual_interval_local_gaussian_bound (bridgeLaw B P) a y T z b compensatedProfileConstant
    ha hy hz hT hb compensatedProfileConstant_nonneg hzero hRegular
  · intro S hS w hw
    exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B P hB a w S z hS hw (abs_lt.mp hz).2
  · intro S hS w hw
    exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B P hB a w S z hS hw (abs_lt.mp hz).1
  · intro β hβ hnew
    have hbound := sourceRemainder_small_bound_of_image (bridgeLaw B P) a y T z β
      ha hy hz.le hT hβ hnew hImage
    convert hbound using 1 <;> ring

end Shao.C2.BridgeIntervalImageConsumer
