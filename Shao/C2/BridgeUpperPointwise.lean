import Shao.C2.GaussianCDFBridgeDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
namespace Shao.C2.BridgeUpperPointwise
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeUpperIntegralReflection Shao.C2.GaussianCDFBridgeDerivative

theorem antitone_centered_cdf_isLocalMax (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Antitone f) (hi : Integrable f μ) (z : ℝ) :
    IsLocalMax (fun v : ℝ => ∫ x : ℝ in Iic v, (f x - f z) ∂μ) z := by
  have hg : Integrable (fun x : ℝ => f x - f z) μ := hi.sub (integrable_const _)
  apply Filter.Eventually.of_forall
  intro v
  by_cases hv : v ≤ z
  · have hd := intervalIntegral.integral_Iic_sub_Iic (μ := μ) (a := v) (b := z)
      hg.integrableOn hg.integrableOn
    rw [intervalIntegral.integral_of_le hv] at hd
    have hn : 0 ≤ ∫ x : ℝ in Ioc v z, (f x - f z) ∂μ :=
      setIntegral_nonneg measurableSet_Ioc (fun x hx => sub_nonneg.mpr (hf hx.2))
    linarith
  · have hzv : z ≤ v := (lt_of_not_ge hv).le
    have hd := intervalIntegral.integral_Iic_sub_Iic (μ := μ) (a := z) (b := v)
      hg.integrableOn hg.integrableOn
    rw [intervalIntegral.integral_of_le hzv] at hd
    have hn : (∫ x : ℝ in Ioc z v, (f x - f z) ∂μ) ≤ 0 :=
      setIntegral_nonpos measurableSet_Ioc (fun x hx => sub_nonpos.mpr (hf hx.1.le))
    linarith

theorem antitone_cdf_derivative_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hf : Antitone f) (hi : Integrable f μ) (z dF dM : ℝ)
    (hF : HasDerivAt (fun v : ℝ => ∫ x : ℝ in Iic v, f x ∂μ) dF z)
    (hM : HasDerivAt (fun v : ℝ => μ.real (Iic v)) dM z) :
    dF = f z * dM := by
  have he : (fun v : ℝ => ∫ x : ℝ in Iic v, (f x - f z) ∂μ) =
      (fun v : ℝ => (∫ x : ℝ in Iic v, f x ∂μ) - f z * μ.real (Iic v)) := by
    funext v
    rw [integral_sub hi.integrableOn (integrable_const (f z)), setIntegral_const]
    simp only [smul_eq_mul, mul_comm]
  have hd := hF.sub (hM.const_mul (f z))
  have hd' : HasDerivAt (fun v : ℝ =>
      (∫ x : ℝ in Iic v, f x ∂μ) - f z * μ.real (Iic v)) (dF - f z * dM) z := by
    convert hd using 1 <;> rfl
  rw [← he] at hd'
  have hz := (antitone_centered_cdf_isLocalMax μ f hf hi z).hasDerivAt_eq_zero hd'
  linarith

theorem bridge_upper_unit_formula {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z : ℝ) (ha : 0 < a) (hz : z < a) :
    upperCompletion (bridgeLaw B P) a 0 1 z = 1 - Real.exp (-2 * a * (a - z)) := by
  letI := isProbabilityMeasure_bridgeLaw B P hB
  have hid := antitone_cdf_derivative_identity (gaussianReal 0 1)
    (fun w : ℝ => upperCompletion (bridgeLaw B P) a 0 1 w)
    (upperCompletion_antitone_endpoint (bridgeLaw B P) a 0 1)
    (upperCompletion_integrable_gaussian (bridgeLaw B P) a 0 1) z
    (gaussianPDFReal 0 1 z - gaussianPDFReal 0 1 (2 * a - z)) (gaussianPDFReal 0 1 z)
    (bridge_upper_integral_hasDerivAt B P hB a z ha hz) (standardGaussian_cdf_hasDerivAt z)
  rw [standardGaussian_reflected_density a z] at hid
  have hp : 0 < gaussianPDFReal 0 1 z := gaussianPDFReal_pos 0 1 z (by norm_num)
  apply mul_left_cancel₀ (ne_of_gt hp)
  nlinarith

end Shao.C2.BridgeUpperPointwise
