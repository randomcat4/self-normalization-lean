import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem integrable_scalar_power_of_absolute_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℕ)
    (hM : Integrable (fun x : ℝ => |x| ^ m) ν) (j : ℕ) (hjm : j ≤ m) :
    Integrable (fun x : ℝ => |x| ^ j) ν ∧ Integrable (fun x : ℝ => x ^ j) ν := by
  have hdom : Integrable (fun x : ℝ => 1 + |x| ^ m) ν :=
    (integrable_const (1 : ℝ)).add hM
  have hbound (x : ℝ) : |x| ^ j ≤ 1 + |x| ^ m := by
    by_cases hx : |x| ≤ 1
    · have hpow : |x| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
      linarith [pow_nonneg (abs_nonneg x) m]
    · have hpow : |x| ^ j ≤ |x| ^ m :=
        pow_le_pow_right₀ (lt_of_not_ge hx).le hjm
      linarith
  have ha : Integrable (fun x : ℝ => |x| ^ j) ν := by
    apply hdom.mono' (continuous_abs.pow j).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      change ‖|x| ^ j‖ ≤ 1 + |x| ^ m
      simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hbound x)
  refine ⟨ha, ?_⟩
  apply ha.mono' (continuous_id.pow j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖x ^ j‖ ≤ |x| ^ j
    simp only [Real.norm_eq_abs, abs_pow, le_refl])

theorem scalar_integral_taylor_polynomial_eq_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℕ)
    (hM : Integrable (fun x : ℝ => |x| ^ m) ν) (t : ℝ) :
    let P : ℝ → ℂ := fun x =>
      ∑ j ∈ Finset.range m, (((t * x : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)
    Integrable P ν ∧
      (∫ x, P x ∂ν) =
        ∑ j ∈ Finset.range m,
          (((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) *
            ((∫ x : ℝ, x ^ j ∂ν : ℝ) : ℂ) := by
  classical
  intro P
  have hform (j : ℕ) (x : ℝ) :
      (((t * x : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ) =
        (((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) * ((x ^ j : ℝ) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, mul_pow]
    ring
  have hterms : ∀ j ∈ Finset.range m,
      Integrable (fun x : ℝ =>
        (((t * x : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) ν := by
    intro j hj
    have hr := (integrable_scalar_power_of_absolute_moment ν m hM j
      (Finset.mem_range.mp hj).le).2
    have hc : Integrable (fun x : ℝ => ((x ^ j : ℝ) : ℂ)) ν := hr.ofReal
    exact (hc.const_mul (((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ))).congr
      (Filter.Eventually.of_forall (fun x => (hform j x).symm))
  have hP : Integrable P ν := integrable_finsetSum (Finset.range m) hterms
  refine ⟨hP, ?_⟩
  change (∫ x : ℝ,
      ∑ j ∈ Finset.range m,
        (((t * x : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ) ∂ν) = _
  rw [integral_finsetSum (Finset.range m) hterms]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = ∫ x : ℝ,
        (((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) * ((x ^ j : ℝ) : ℂ) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall (hform j))
    _ = (((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) *
          ((∫ x : ℝ, x ^ j ∂ν : ℝ) : ℂ) := by
      rw [integral_const_mul, integral_complex_ofReal]

end
end Shao.OQ3

