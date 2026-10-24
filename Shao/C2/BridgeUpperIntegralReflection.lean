import Shao.C2.BrownianUpperJointReflection
import Shao.C2.BridgeHalfLineJointLaw

noncomputable section
namespace Shao.C2.BridgeUpperIntegralReflection
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeHalfLineJointLaw Shao.C2.BrownianUpperJointReflection

theorem upperCompletion_antitone_endpoint (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T : ℝ) : Antitone (fun z : ℝ => upperCompletion ν a y T z) := by
  intro z z' hzz
  refine measureReal_mono ?_ (by finiteness)
  intro g hg t
  exact (bridgePath_mono y y T z z' le_rfl hzz g t).trans_lt (hg t)

theorem upperCompletion_measurable_endpoint (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T : ℝ) : Measurable (fun z : ℝ => upperCompletion ν a y T z) := by
  exact (upperCompletion_antitone_endpoint ν a y T).measurable

theorem upperCompletion_integrable_gaussian (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T : ℝ) : Integrable (fun z : ℝ => upperCompletion ν a y T z) (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono'
    (upperCompletion_measurable_endpoint ν a y T).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (completion_bounds ν a y T z).1]
    exact (completion_bounds ν a y T z).2.1)

theorem bridge_upper_setIntegral_cdf_reflection {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a v : ℝ) (ha : 0 < a) (hv : v < a) :
    (∫ w : ℝ in Iic v, upperCompletion (bridgeLaw B P) a 0 1 w ∂(gaussianReal 0 1)) +
      (gaussianReal 0 1).real (Ici (2 * a - v)) = (gaussianReal 0 1).real (Iic v) := by
  have hj := brownian_upper_joint B P hB a 0 1 v
  simp only [Real.sqrt_one, one_mul, zero_add] at hj
  have hr := brownian_upper_joint_reflection B P hB a v ha hv
  rw [hj] at hr
  have hi : (∫ w : ℝ, (if w ≤ v then upperCompletion (bridgeLaw B P) a 0 1 w else 0)
      ∂(gaussianReal 0 1)) =
      ∫ w : ℝ in Iic v, upperCompletion (bridgeLaw B P) a 0 1 w ∂(gaussianReal 0 1) := by
    rw [← integral_indicator measurableSet_Iic]
    rfl
  rw [hi] at hr
  exact hr

end Shao.C2.BridgeUpperIntegralReflection
