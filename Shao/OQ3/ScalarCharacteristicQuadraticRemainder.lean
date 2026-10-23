import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace Shao.OQ3
open MeasureTheory
open scoped Topology BigOperators
noncomputable section

theorem imaginary_exponential_quadratic_remainder_bound (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) -
      (1 + (t : ℂ) * Complex.I - (t : ℂ) ^ 2 / 2)‖ ≤
        (Real.exp 1 + 4) * |t| ^ 3 := by
  have hsum : (∑ m ∈ Finset.range 3,
      ((t : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
        1 + (t : ℂ) * Complex.I - (t : ℂ) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq] <;> ring
  have hn : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
  by_cases hsmall : |t| ≤ 1
  · have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((t : ℂ) * Complex.I) 3
    rw [hsum, hn] at h
    refine h.trans ?_
    calc
      |t| ^ 3 * Real.exp |t| ≤ |t| ^ 3 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsmall)
          (pow_nonneg (abs_nonneg t) 3)
      _ ≤ (Real.exp 1 + 4) * |t| ^ 3 := by
        nlinarith [pow_nonneg (abs_nonneg t) 3]
  · have hr : 1 ≤ |t| := le_of_lt (lt_of_not_ge hsmall)
    have hp : ‖(1 : ℂ) + (t : ℂ) * Complex.I - (t : ℂ) ^ 2 / 2‖ ≤
        1 + |t| + |t| ^ 2 / 2 := by
      calc
        _ ≤ ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ + ‖(t : ℂ) ^ 2 / 2‖ :=
          norm_sub_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) + ‖(t : ℂ) ^ 2 / 2‖ :=
          add_le_add (norm_add_le _ _) le_rfl
        _ = 1 + |t| + |t| ^ 2 / 2 := by simp [norm_div, norm_pow]
    have hr12 : |t| ≤ |t| ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hr)]
    have hr2 : 1 ≤ |t| ^ 2 := hr.trans hr12
    have hr23 : |t| ^ 2 ≤ |t| ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg |t|) (sub_nonneg.mpr hr)]
    calc
      _ ≤ ‖Complex.exp ((t : ℂ) * Complex.I)‖ +
          ‖(1 : ℂ) + (t : ℂ) * Complex.I - (t : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + |t| + |t| ^ 2 / 2) := by
        rw [Complex.norm_exp_ofReal_mul_I]
        exact add_le_add le_rfl hp
      _ ≤ 4 * |t| ^ 3 := by nlinarith
      _ ≤ (Real.exp 1 + 4) * |t| ^ 3 := by
        nlinarith [mul_nonneg (Real.exp_pos 1).le (pow_nonneg (abs_nonneg t) 3)]

theorem probability_characteristic_quadratic_remainder_bound
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h1 : Integrable (fun x : ℝ => x) nu)
    (h2 : Integrable (fun x : ℝ => x ^ 2) nu)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) nu)
    (hmean : (∫ x : ℝ, x ∂nu) = 0) (t : ℝ) :
    ‖(∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂nu) -
      (1 - (t : ℂ) ^ 2 * ((∫ x : ℝ, x ^ 2 ∂nu) : ℝ) / 2)‖ ≤
        (Real.exp 1 + 4) * |t| ^ 3 * (∫ x : ℝ, |x| ^ 3 ∂nu) := by
  let e : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
  let P : ℝ → ℂ := fun x =>
    1 + ((t : ℂ) * Complex.I) * (x : ℂ) -
      ((t : ℂ) ^ 2 / 2) * ((x ^ 2 : ℝ) : ℂ)
  have h1c : Integrable (fun x : ℝ => (x : ℂ)) nu := h1.ofReal
  have h2c : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) nu := h2.ofReal
  have he : Integrable e nu :=
    (integrable_const (1 : ℝ)).mono' (by dsimp [e]; fun_prop)
      (Filter.Eventually.of_forall (fun x => by
        dsimp [e]
        rw [Complex.norm_exp_ofReal_mul_I]))
  have hP : Integrable P nu :=
    ((integrable_const (1 : ℂ)).add (h1c.const_mul ((t : ℂ) * Complex.I))).sub
      (h2c.const_mul ((t : ℂ) ^ 2 / 2))
  have hPint : (∫ x : ℝ, P x ∂nu) =
      1 - (t : ℂ) ^ 2 * ((∫ x : ℝ, x ^ 2 ∂nu) : ℝ) / 2 := by
    have hlin : Integrable (fun x : ℝ =>
        (1 : ℂ) + ((t : ℂ) * Complex.I) * (x : ℂ)) nu :=
      (integrable_const (1 : ℂ)).add (h1c.const_mul ((t : ℂ) * Complex.I))
    have hquad : Integrable (fun x : ℝ =>
        ((t : ℂ) ^ 2 / 2) * ((x ^ 2 : ℝ) : ℂ)) nu :=
      h2c.const_mul ((t : ℂ) ^ 2 / 2)
    dsimp only [P]
    rw [integral_sub hlin hquad]
    rw [integral_add (f := fun x : ℝ => (1 : ℂ))
      (g := fun x : ℝ => ((t : ℂ) * Complex.I) * (x : ℂ))
      (integrable_const (1 : ℂ)) (h1c.const_mul ((t : ℂ) * Complex.I))]
    rw [integral_const_mul, integral_const_mul, integral_complex_ofReal,
      integral_complex_ofReal, hmean]
    simp only [integral_const, probReal_univ, one_smul, Complex.ofReal_zero,
      mul_zero, add_zero] <;> ring
  have hpoint : ∀ x : ℝ, ‖e x - P x‖ ≤
      ((Real.exp 1 + 4) * |t| ^ 3) * |x| ^ 3 := by
    intro x
    have hp : P x =
        1 + ((t * x : ℝ) : ℂ) * Complex.I - ((t * x : ℝ) : ℂ) ^ 2 / 2 := by
      dsimp only [P]
      push_cast
      ring
    dsimp only [e]
    rw [hp]
    simpa only [abs_mul, mul_pow, mul_assoc] using
      imaginary_exponential_quadratic_remainder_bound (t * x)
  have hbound := norm_integral_le_of_norm_le
    (h3.const_mul ((Real.exp 1 + 4) * |t| ^ 3)) (Filter.Eventually.of_forall hpoint)
  rw [integral_sub he hP, hPint, integral_const_mul] at hbound
  simpa only [e] using hbound

end
end Shao.OQ3
