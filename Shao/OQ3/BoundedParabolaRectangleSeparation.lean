import Shao.OQ3.TiltedMeasureDomination
import Shao.Probability.BivariateLegendre

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem bounded_parabola_rectangle_exponential_separation
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (lower upper : ℝ)
    (henergy : ∀ᵐ x ∂mu, lower ≤ x ^ 2 ∧ x ^ 2 ≤ upper) :
    Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) = Set.univ ∧
      ∀ z : ℝ × ℝ, (z.1 < -M ∨ M < z.1 ∨ z.2 < lower ∨ upper < z.2) →
        ∀ L : ℝ, ∃ theta : Shao.Probability.bivariateMGFDomain mu
          (fun x : ℝ => (x, x ^ 2)),
          L < (theta : ℝ × ℝ).1 * z.1 + (theta : ℝ × ℝ).2 * z.2 -
            Shao.Probability.bivariateLogMGF mu (fun x : ℝ => (x, x ^ 2)) theta := by
  have hfull (theta : ℝ × ℝ) : theta ∈
      Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) :=
    quadratic_exp_integrable_of_ae_abs_le mu M hM hb theta.1 theta.2
  refine ⟨Set.eq_univ_of_forall hfull, ?_⟩
  intro z hz L
  have hsep (d1 d2 B : ℝ)
      (hfeature : ∀ᵐ x ∂mu, d1 * x + d2 * x ^ 2 ≤ B)
      (hgap : B < d1 * z.1 + d2 * z.2) :
      ∃ theta : Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)),
        L < (theta : ℝ × ℝ).1 * z.1 + (theta : ℝ × ℝ).2 * z.2 -
          Shao.Probability.bivariateLogMGF mu (fun x : ℝ => (x, x ^ 2)) theta := by
    let t : ℝ := (|L| + 1) / (d1 * z.1 + d2 * z.2 - B)
    have hden : 0 < d1 * z.1 + d2 * z.2 - B := sub_pos.mpr hgap
    have ht : 0 < t := div_pos (by positivity) hden
    have hprod : t * (d1 * z.1 + d2 * z.2 - B) = |L| + 1 := by
      dsimp [t]
      field_simp [hden.ne']
    have hI := quadratic_exp_integrable_of_ae_abs_le mu M hM hb (t * d1) (t * d2)
    have hbound : (∫ x : ℝ, Real.exp ((t * d1) * x + (t * d2) * x ^ 2) ∂mu) ≤
        Real.exp (t * B) := by
      have hi := integral_mono_ae hI (integrable_const (Real.exp (t * B)))
        (show ∀ᵐ x ∂mu, Real.exp ((t * d1) * x + (t * d2) * x ^ 2) ≤
          Real.exp (t * B) from by
          filter_upwards [hfeature] with x hx
          apply Real.exp_le_exp.mpr
          nlinarith only [mul_le_mul_of_nonneg_left hx ht.le])
      simpa using hi
    have hlog := Real.log_le_log (integral_exp_pos hI) hbound
    rw [Real.log_exp] at hlog
    refine ⟨⟨(t * d1, t * d2), hfull (t * d1, t * d2)⟩, ?_⟩
    change L < (t * d1) * z.1 + (t * d2) * z.2 -
      Real.log (∫ x : ℝ, Real.exp ((t * d1) * x + (t * d2) * x ^ 2) ∂mu)
    nlinarith only [hlog, hprod, le_abs_self L]
  rcases hz with hleft | hright | hlower | hupper
  · apply hsep (-1) 0 M
    · filter_upwards [hb] with x hx
      simp only [neg_one_mul, zero_mul, add_zero]
      linarith [(abs_le.mp hx).1]
    · simp only [neg_one_mul, zero_mul, add_zero]
      linarith
  · apply hsep 1 0 M
    · filter_upwards [hb] with x hx
      simp only [one_mul, zero_mul, add_zero]
      exact (abs_le.mp hx).2
    · simpa only [one_mul, zero_mul, add_zero] using hright
  · apply hsep 0 (-1) (-lower)
    · filter_upwards [henergy] with x hx
      simp only [zero_mul, zero_add, neg_one_mul]
      linarith [hx.1]
    · simp only [zero_mul, zero_add, neg_one_mul]
      linarith
  · apply hsep 0 1 upper
    · filter_upwards [henergy] with x hx
      simpa only [zero_mul, zero_add, one_mul] using hx.2
    · simpa only [zero_mul, zero_add, one_mul] using hupper

end
end Shao.OQ3
