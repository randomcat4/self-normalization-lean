import Shao.C2.BridgeUpperIntegralReflection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
namespace Shao.C2.GaussianCDFBridgeDerivative
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeUpperIntegralReflection

theorem standardGaussian_cdf_eq_integral (v : ℝ) :
    (gaussianReal 0 1).real (Iic v) = ∫ x : ℝ in Iic v, gaussianPDFReal 0 1 x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))

theorem standardGaussian_tail_eq_one_sub_cdf (v : ℝ) :
    (gaussianReal 0 1).real (Ici v) = 1 - (gaussianReal 0 1).real (Iic v) := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have he : (gaussianReal 0 1).real (Ici v) = (gaussianReal 0 1).real (Ioi v) :=
    (measureReal_congr (Ioi_ae_eq_Ici' (measure_singleton v))).symm
  rw [he]
  simpa only [compl_Iic] using
    (probReal_compl_eq_one_sub (μ := gaussianReal 0 1) (s := Iic v) measurableSet_Iic)

theorem standardGaussian_cdf_hasDerivAt (v : ℝ) :
    HasDerivAt (fun r : ℝ => (gaussianReal 0 1).real (Iic r)) (gaussianPDFReal 0 1 v) v := by
  have hi := integrable_gaussianPDFReal 0 1
  have hc : Continuous (gaussianPDFReal 0 1) := by
    unfold gaussianPDFReal
    fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hi.intervalIntegrable (a := 0) (b := v))
    (stronglyMeasurable_gaussianPDFReal 0 1).stronglyMeasurableAtFilter hc.continuousAt
  have he : (fun r : ℝ => (gaussianReal 0 1).real (Iic r)) =
      (fun r : ℝ => (∫ x : ℝ in Iic 0, gaussianPDFReal 0 1 x) +
        ∫ x : ℝ in (0 : ℝ)..r, gaussianPDFReal 0 1 x) := by
    funext r
    rw [standardGaussian_cdf_eq_integral]
    have hdiff := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := r)
      hi.integrableOn hi.integrableOn
    linarith
  rw [he]
  exact hd.const_add _

theorem standardGaussian_tail_hasDerivAt (v : ℝ) :
    HasDerivAt (fun r : ℝ => (gaussianReal 0 1).real (Ici r)) (-gaussianPDFReal 0 1 v) v := by
  have he : (fun r : ℝ => (gaussianReal 0 1).real (Ici r)) =
      (fun r : ℝ => 1 - (gaussianReal 0 1).real (Iic r)) :=
    funext standardGaussian_tail_eq_one_sub_cdf
  rw [he]
  exact (standardGaussian_cdf_hasDerivAt v).const_sub 1

theorem standardGaussian_reflected_density (a z : ℝ) :
    gaussianPDFReal 0 1 (2 * a - z) =
      gaussianPDFReal 0 1 z * Real.exp (-2 * a * (a - z)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [show -(2 * a - z) ^ 2 / 2 = -z ^ 2 / 2 + (-2 * a * (a - z)) by ring, Real.exp_add]
  ring

theorem bridge_upper_integral_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z : ℝ) (ha : 0 < a) (hz : z < a) :
    HasDerivAt (fun v : ℝ =>
      ∫ w : ℝ in Iic v, upperCompletion (bridgeLaw B P) a 0 1 w ∂(gaussianReal 0 1))
      (gaussianPDFReal 0 1 z - gaussianPDFReal 0 1 (2 * a - z)) z := by
  have hi := (hasDerivAt_const z (2 * a)).sub (hasDerivAt_id z)
  have ht := (standardGaussian_tail_hasDerivAt (2 * a - z)).comp z hi
  have hd := (standardGaussian_cdf_hasDerivAt z).sub ht
  have hformula : HasDerivAt (fun v : ℝ => (gaussianReal 0 1).real (Iic v) -
      (gaussianReal 0 1).real (Ici (2 * a - v)))
      (gaussianPDFReal 0 1 z - gaussianPDFReal 0 1 (2 * a - z)) z := by
    convert hd using 1 <;> first | rfl | ring
  have he : (fun v : ℝ =>
      ∫ w : ℝ in Iic v, upperCompletion (bridgeLaw B P) a 0 1 w ∂(gaussianReal 0 1)) =ᶠ[𝓝 z]
      (fun v : ℝ => (gaussianReal 0 1).real (Iic v) -
        (gaussianReal 0 1).real (Ici (2 * a - v))) := by
    filter_upwards [gt_mem_nhds hz] with v hv
    have hid := bridge_upper_setIntegral_cdf_reflection B P hB a v ha hv
    linarith
  exact hformula.congr_of_eventuallyEq he

end Shao.C2.GaussianCDFBridgeDerivative
