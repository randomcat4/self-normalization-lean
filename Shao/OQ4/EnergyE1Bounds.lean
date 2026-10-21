import Shao.OQ4.EnergyTiltedLaw
import Shao.OQ4.EnergyLogNormalizer

/-! The original finite E1 interface with one T-only constant and one common threshold. -/

namespace Shao.OQ4

open MeasureTheory

noncomputable def energyE1Constant (T : ℝ) : ℝ :=
  1 + energyLogErrorConstant T + energyTiltMeanConstant T +
    energyTiltSecondMomentConstant T + energyTiltThirdMomentConstant T

theorem energyE1Constant_dominates (T : ℝ) (hT : 0 ≤ T) :
    1 ≤ energyE1Constant T ∧ energyLogErrorConstant T ≤ energyE1Constant T ∧
    energyTiltMeanConstant T ≤ energyE1Constant T ∧
    energyTiltSecondMomentConstant T ≤ energyE1Constant T ∧
    energyTiltThirdMomentConstant T ≤ energyE1Constant T := by
  have hl := (energyLog_constants_nonneg 0 T (by norm_num) hT).2
  obtain ⟨_h1, _h2, _hD, hm, hq, hc⟩ := energyTilt_constants_nonneg T hT
  unfold energyE1Constant
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- A conclusion about the same actual law and genuine integrals, never a premise. -/
def energyE1Conclusion (ν : Measure ℝ) (T h s : ℝ) : Prop :=
  IsProbabilityMeasure (energyTiltedLaw ν h s) ∧
  Integrable (fun x : ℝ => x) (energyTiltedLaw ν h s) ∧
  Integrable (fun x : ℝ => x ^ 2) (energyTiltedLaw ν h s) ∧
  Integrable (fun x : ℝ => |x| ^ 3) (energyTiltedLaw ν h s) ∧
  (∀ᵐ x ∂energyTiltedLaw ν h s, |x| ≤ 2 * h) ∧
  2 ≤ h ∧ ((1 / 2 : ℝ) ≤ energyNormalizer ν h s ∧ energyNormalizer ν h s ≤ (3 / 2 : ℝ)) ∧
  |Real.log (energyNormalizer ν h s) - s / h ^ 2| ≤
    energyE1Constant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 3 ∧
  |∫ x : ℝ, x ∂energyTiltedLaw ν h s| ≤
    energyE1Constant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ^ 2 ∧
  |(∫ x : ℝ, x ^ 2 ∂energyTiltedLaw ν h s) - 1| ≤
    energyE1Constant T * (∫ x : ℝ, |x| ^ 3 ∂ν) / h ∧
  (∫ x : ℝ, |x| ^ 3 ∂energyTiltedLaw ν h s) ≤
    energyE1Constant T * (∫ x : ℝ, |x| ^ 3 ∂ν)

/-- The actual common-moment-class E1 bounds, with no assumed law or moment conclusions. -/
theorem energyE1_common_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (M T h s : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) (hh : energyLogThreshold M T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hβM : (∫ x : ℝ, |x| ^ 3 ∂ν) ≤ M) : energyE1Conclusion ν T h s := by
  obtain ⟨_hw, hh2, _hβM, _hMh, _hraw, _hc, hZbounds, _hZ⟩ :=
    energyLog_normalizer_close ν M T h s hM hT hh hs hSq hCube hsecond hβM
  have hh1 : 1 ≤ h := by linarith
  have hh0 : 0 < h := by linarith
  have hβ0 : 0 ≤ ∫ x : ℝ, |x| ^ 3 ∂ν := integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3
  obtain ⟨_hC1, hClog, hCmean, hCsecond, hCthird⟩ := energyE1Constant_dominates T hT
  obtain ⟨hi, hq, hc⟩ := energyTiltedLaw_moment_integrability ν T h s hT hh1 hs hSq hCube hsecond
  unfold energyE1Conclusion
  refine ⟨energyTiltedLaw_isProbabilityMeasure ν T h s hT hh1 hs hSq hsecond,
    hi, hq, hc, energyTiltedLaw_ae_support ν h s, hh2, hZbounds, ?_, ?_, ?_, ?_⟩
  · exact (energyLog_normalizer_error ν M T h s hM hT hh hs hSq hCube hsecond hβM).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hClog hβ0) (by positivity))
  · exact (energyTiltedLaw_mean_bound ν T h s hT hh1 hs hSq hCube hsecond hmean).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCmean hβ0) (sq_nonneg h))
  · exact (energyTiltedLaw_second_moment_bound ν T h s hT hh1 hs hSq hCube hsecond).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCsecond hβ0) hh0.le)
  · exact (energyTiltedLaw_third_moment_bound ν T h s hT hh1 hs hSq hCube hsecond).trans
      (mul_le_mul_of_nonneg_right hCthird hβ0)

/-- Fixed-law E1 follows with M equal to the actual third absolute moment. -/
theorem energyE1_fixed_law_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (T h s : ℝ) (hT : 0 ≤ T)
    (hh : energyLogThreshold (∫ x : ℝ, |x| ^ 3 ∂ν) T ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hCube : Integrable (fun x : ℝ => |x| ^ 3) ν)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) (hmean : (∫ x : ℝ, x ∂ν) = 0) :
    energyE1Conclusion ν T h s :=
  energyE1_common_bounds ν (∫ x : ℝ, |x| ^ 3 ∂ν) T h s
    (integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3) hT hh hs hSq hCube hsecond hmean le_rfl

end Shao.OQ4
