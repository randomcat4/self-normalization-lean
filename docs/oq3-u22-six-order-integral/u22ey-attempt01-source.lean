import Shao.OQ3.ComplexSixOrderPolynomialCoefficients
import Shao.OQ3.ActualCGFNormalizedOcticPolynomial

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

theorem actual_cgf_six_order_edgeworth_polynomial_identification
    (mu : Measure (Fin 2 → ℝ)) (n : ℕ) (u v : ℝ) :
    let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
    let kappa : ℕ → ℝ := fun j => iteratedDeriv j (ProbabilityTheory.cgf X mu) 0
    let A : Fin 6 → ℂ := fun j =>
      (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
        (kappa (j.val + 3) : ℂ)
    let a : Fin 6 → ℂ := fun j => A j /
      (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
    let B1 := A 0
    let B2 := A 1 + A 0 ^ 2 / 2
    let B3 := A 2 + A 0 * A 1 + A 0 ^ 3 / 6
    let B4 := A 3 + A 0 * A 2 + A 1 ^ 2 / 2 +
      A 0 ^ 2 * A 1 / 2 + A 0 ^ 4 / 24
    let B5 := A 4 + A 0 * A 3 + A 1 * A 2 +
      A 0 ^ 2 * A 2 / 2 + A 0 * A 1 ^ 2 / 2 +
      A 0 ^ 3 * A 1 / 6 + A 0 ^ 5 / 120
    let B6 := A 5 + A 0 * A 4 + A 1 * A 3 + A 2 ^ 2 / 2 +
      A 0 ^ 2 * A 3 / 2 + A 0 * A 1 * A 2 + A 1 ^ 3 / 6 +
      A 0 ^ 3 * A 2 / 6 + A 0 ^ 2 * A 1 ^ 2 / 4 +
      A 0 ^ 4 * A 1 / 24 + A 0 ^ 6 / 720
    Complex.exp (-((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2) *
      (∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a (sigma i) else 0) =
      Complex.exp (-((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2) *
        (1 + B1 / (Real.sqrt (n : ℝ) : ℂ) +
          B2 / (Real.sqrt (n : ℝ) : ℂ) ^ 2 +
          B3 / (Real.sqrt (n : ℝ) : ℂ) ^ 3 +
          B4 / (Real.sqrt (n : ℝ) : ℂ) ^ 4 +
          B5 / (Real.sqrt (n : ℝ) : ℂ) ^ 5 +
          B6 / (Real.sqrt (n : ℝ) : ℂ) ^ 6) := by
  intro X kappa A a B1 B2 B3 B4 B5 B6
  apply congrArg (fun z : ℂ => Complex.exp (-((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2) * z)
  simpa only [a, B1, B2, B3, B4, B5, B6, one_div, inv_pow, div_eq_mul_inv] using
    (complex_six_order_weighted_polynomial_coefficients A
      (1 / (Real.sqrt (n : ℝ) : ℂ)))

end
end Shao.OQ3
