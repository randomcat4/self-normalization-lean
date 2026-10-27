import Shao.OQ3.GaussianSmoothedPairLaw
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3
open MeasureTheory
open scoped NNReal
noncomputable section

theorem pair_real_gaussian_integral
    (b : ℝ) (hb : 0 < b) :
    Integrable (fun z : ℝ × ℝ => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))) ∧
      (∫ z : ℝ × ℝ, Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))) = Real.pi / b := by
  obtain ⟨hi, hv⟩ := pair_gaussian_oscillatory_integral b hb (0, 0)
  have hiC : Integrable (fun z : ℝ × ℝ =>
      ((Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)) : ℝ) : ℂ)) := by
    simpa [Complex.ofReal_exp] using hi
  have hiR : Integrable (fun z : ℝ × ℝ => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))) := by
    apply hiC.norm.congr (Filter.Eventually.of_forall (fun z => ?_))
    change ‖((Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)) : ℝ) : ℂ)‖ =
      Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))
    exact (Complex.norm_real _).trans (Real.norm_of_nonneg (Real.exp_nonneg _))
  have hvC : (∫ z : ℝ × ℝ, ((Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)) : ℝ) : ℂ)) =
      ((Real.pi / b : ℝ) : ℂ) := by
    simpa [Complex.ofReal_exp] using hv
  rw [integral_complex_ofReal] at hvC
  exact ⟨hiR, Complex.ofReal_injective hvC⟩

theorem gaussian_smoothed_pair_inverse_tail_bound
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (b R : ℝ) (hb : 0 < b) (hR : 0 ≤ R) (x : ℝ × ℝ) :
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
    let tail : Set (ℝ × ℝ) := {z | R ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2}
    let f : (ℝ × ℝ) → ℂ := fun z =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
        ∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho
    Integrable f ∧ IntegrableOn f tail ∧
      ‖∫ z in tail, f z‖ ≤ (2 * Real.pi / b) * Real.exp (-b * R ^ 2 / 2) := by
  intro v gamma rho tail f
  obtain ⟨hrho, hcf, hall⟩ := gaussian_smoothed_pair_law_fourier_integral nu b hb
  have hi : Integrable f := (hall x).1
  have hnu := (pair_characteristic_measurable_norm_le_one nu).2
  obtain ⟨hig, hvg⟩ := pair_real_gaussian_integral (b / 2) (half_pos hb)
  let envelope : (ℝ × ℝ) → ℝ := fun z =>
    Real.exp (-b * R ^ 2 / 2) * Real.exp (-(b / 2) * (z.1 ^ 2 + z.2 ^ 2))
  have hie : Integrable envelope := hig.const_mul _
  have hen (z : ℝ × ℝ) : 0 ≤ envelope z := by dsimp only [envelope]; positivity
  have ht : MeasurableSet tail := by
    dsimp only [tail]
    apply measurableSet_le measurable_const
    fun_prop
  have hdom (z : ℝ × ℝ) (hz : z ∈ tail) : ‖f z‖ ≤ envelope z := by
    have hphase : ‖Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    have hgauss : ‖Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ))‖ =
        Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hnorm : ‖f z‖ ≤ Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)) := by
      dsimp only [f]
      rw [hcf z]
      simp only [norm_mul]
      rw [hphase, hgauss, one_mul]
      exact mul_le_of_le_one_left (Real.exp_nonneg _) (hnu z)
    have henv : Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2)) ≤ envelope z := by
      dsimp only [envelope]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      change R ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 at hz
      nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hz)]
    exact hnorm.trans henv
  have hmono : (∫ z in tail, ‖f z‖) ≤ ∫ z in tail, envelope z :=
    integral_mono_ae hi.norm.integrableOn hie.integrableOn
      ((ae_restrict_mem ht).mono (fun z hz => hdom z hz))
  refine ⟨hi, hi.integrableOn, ?_⟩
  calc
    ‖∫ z in tail, f z‖ ≤ ∫ z in tail, ‖f z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in tail, envelope z := hmono
    _ ≤ ∫ z : ℝ × ℝ, envelope z :=
      setIntegral_le_integral hie (Filter.Eventually.of_forall hen)
    _ = (2 * Real.pi / b) * Real.exp (-b * R ^ 2 / 2) := by
      dsimp only [envelope]
      rw [integral_const_mul, hvg]
      ring

end
end Shao.OQ3
