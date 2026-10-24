import Shao.OQ3.ScalarCharacteristicIntegratedTaylorRemainder
import Shao.OQ3.ScalarTaylorMomentPolynomial

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem scalar_characteristic_moment_remainder_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℕ)
    (hM : Integrable (fun x : ℝ => |x| ^ m) ν) (t : ℝ) :
    ‖(∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν) -
        (∑ j ∈ Finset.range m,
          (((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) *
            ((∫ x : ℝ, x ^ j ∂ν : ℝ) : ℂ))‖ ≤
      (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m * (∫ x : ℝ, |x| ^ m ∂ν) := by
  have hr := (scalar_characteristic_integrated_taylor_remainder ν m hM t).2.2.2
  rw [(scalar_integral_taylor_polynomial_eq_moments ν m hM t).2] at hr
  exact hr

theorem uniform_scalar_characteristic_moment_remainder_bound
    {ι : Type*} (law : ι → Measure ℝ)
    (hprob : ∀ i, IsProbabilityMeasure (law i)) (m : ℕ) (M : ℝ)
    (hI : ∀ i, Integrable (fun x : ℝ => |x| ^ m) (law i))
    (hM : ∀ i, (∫ x : ℝ, |x| ^ m ∂(law i)) ≤ M) :
    ∀ (i : ι) (t : ℝ),
      ‖(∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂(law i)) -
          (∑ j ∈ Finset.range m,
            (((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) *
              ((∫ x : ℝ, x ^ j ∂(law i) : ℝ) : ℂ))‖ ≤
        (Real.exp 1 + (m : ℝ) + 1) * M * |t| ^ m := by
  intro i t
  letI : IsProbabilityMeasure (law i) := hprob i
  have hC : 0 ≤ (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m := by positivity
  calc
    _ ≤ (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m *
          (∫ x : ℝ, |x| ^ m ∂(law i)) :=
      scalar_characteristic_moment_remainder_bound (law i) m (hI i) t
    _ ≤ (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m * M :=
      mul_le_mul_of_nonneg_left (hM i) hC
    _ = (Real.exp 1 + (m : ℝ) + 1) * M * |t| ^ m := by ring

end
end Shao.OQ3

