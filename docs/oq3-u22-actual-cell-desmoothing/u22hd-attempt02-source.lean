import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Ring

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem density_weighted_test_error_bound
    (rho : Measure (ℝ × ℝ)) [IsProbabilityMeasure rho]
    (k reference f : (ℝ × ℝ) → ℝ)
    (hk : Measurable k) (hk0 : ∀ z : ℝ × ℝ, 0 ≤ k z)
    (hrho : rho = volume.withDensity (fun z => ENNReal.ofReal (k z)))
    (href : Measurable reference) (hf : Measurable f) (hfi : Integrable f)
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hfBound : ∀ z : ℝ × ℝ, |f z| ≤ C)
    (herror : ∀ z : ℝ × ℝ, |k z - reference z| ≤ delta) :
    Integrable f rho ∧
      Integrable (fun z : ℝ × ℝ => f z * k z) ∧
        Integrable (fun z : ℝ × ℝ => f z * reference z) ∧
          |(∫ z : ℝ × ℝ, f z ∂rho) - (∫ z : ℝ × ℝ, f z * reference z)| ≤
            delta * (∫ z : ℝ × ℝ, |f z|) := by
  have hiRho : Integrable f rho := by
    apply (integrable_const C).mono' hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs] using hfBound z)
  have hfk : Integrable (fun z : ℝ × ℝ => f z * k z) := by
    have h := (integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp
        (show Integrable f (volume.withDensity (fun z => ENNReal.ofReal (k z))) from
          hrho ▸ hiRho)
    simpa only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul, mul_comm] using h
  have hint : (∫ z : ℝ × ℝ, f z ∂rho) = ∫ z : ℝ × ℝ, f z * k z := by
    rw [hrho, integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul, mul_comm]
  have hiAbs : Integrable (fun z : ℝ × ℝ => |f z|) := by
    simpa only [Real.norm_eq_abs] using hfi.norm
  have hpoint (z : ℝ × ℝ) : ‖f z * (k z - reference z)‖ ≤ delta * |f z| := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |f z| * delta := mul_le_mul_of_nonneg_left (herror z) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hiDiff : Integrable (fun z : ℝ × ℝ => f z * (k z - reference z)) := by
    apply (hiAbs.const_mul delta).mono' (hf.mul (hk.sub href)).aestronglyMeasurable
    exact Filter.Eventually.of_forall hpoint
  have hiRef : Integrable (fun z : ℝ × ℝ => f z * reference z) := by
    apply (hfk.sub hiDiff).congr
    exact Filter.Eventually.of_forall (fun z => by ring)
  refine ⟨hiRho, hfk, hiRef, ?_⟩
  calc
    _ = ‖∫ z : ℝ × ℝ, f z * (k z - reference z)‖ := by
      rw [Real.norm_eq_abs, hint, ← integral_sub hfk hiRef]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)
    _ ≤ ∫ z : ℝ × ℝ, ‖f z * (k z - reference z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ × ℝ, delta * |f z| := integral_mono hiDiff.norm (hiAbs.const_mul delta) hpoint
    _ = _ := integral_const_mul _ _

end
end Shao.OQ3
