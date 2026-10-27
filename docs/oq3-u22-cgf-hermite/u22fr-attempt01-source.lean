import Shao.OQ3.GaussianHermiteIntegral

namespace Shao.OQ3
open MeasureTheory Real
open scoped BigOperators
noncomputable section

theorem pair_standard_gaussian_finite_hermite_integral
    (s : Finset (ℕ × ℕ)) (a : (ℕ × ℕ) → ℝ) (x : ℝ × ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
        (∑ d ∈ s, (a d : ℂ) *
          (Complex.I * (z.1 : ℂ)) ^ d.1 * (Complex.I * (z.2 : ℂ)) ^ d.2) *
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
      (∫ z : ℝ × ℝ,
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          (∑ d ∈ s, (a d : ℂ) *
            (Complex.I * (z.1 : ℂ)) ^ d.1 * (Complex.I * (z.2 : ℂ)) ^ d.2) *
              Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) =
        ((2 * Real.pi *
          (∑ d ∈ s, a d * (gaussianHermitePolynomial d.1).eval x.1 *
            (gaussianHermitePolynomial d.2).eval x.2) *
              Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ) := by
  classical
  let term : (ℕ × ℕ) → (ℝ × ℝ) → ℂ := fun d z =>
    Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
      (Complex.I * (z.1 : ℂ)) ^ d.1 * (Complex.I * (z.2 : ℂ)) ^ d.2 *
        Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)
  have ht (d : ℕ × ℕ) : Integrable (fun z : ℝ × ℝ => (a d : ℂ) * term d z) :=
    (pair_standard_gaussian_hermite_integral d.1 d.2 x).1.const_mul (a d : ℂ)
  have hid (z : ℝ × ℝ) :
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
        (∑ d ∈ s, (a d : ℂ) *
          (Complex.I * (z.1 : ℂ)) ^ d.1 * (Complex.I * (z.2 : ℂ)) ^ d.2) *
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) =
        ∑ d ∈ s, (a d : ℂ) * term d z := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    dsimp [term]
    ring
  refine ⟨(integrable_finsetSum s (fun d _ => ht d)).congr
    (Filter.Eventually.of_forall (fun z => (hid z).symm)), ?_⟩
  calc
    _ = ∫ z : ℝ × ℝ, ∑ d ∈ s, (a d : ℂ) * term d z :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    _ = ∑ d ∈ s, ∫ z : ℝ × ℝ, (a d : ℂ) * term d z :=
      integral_finsetSum s (fun d _ => ht d)
    _ = ∑ d ∈ s, (a d : ℂ) *
        ((2 * Real.pi * (gaussianHermitePolynomial d.1).eval x.1 *
          (gaussianHermitePolynomial d.2).eval x.2 *
            Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [integral_const_mul]
      exact congrArg (fun w : ℂ => (a d : ℂ) * w)
        (pair_standard_gaussian_hermite_integral d.1 d.2 x).2
    _ = ((∑ d ∈ s, a d *
        (2 * Real.pi * (gaussianHermitePolynomial d.1).eval x.1 *
          (gaussianHermitePolynomial d.2).eval x.2 *
            Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)) : ℝ) : ℂ) := by
      push_cast
    _ = _ := by
      apply congrArg Complex.ofReal
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring

end
end Shao.OQ3
