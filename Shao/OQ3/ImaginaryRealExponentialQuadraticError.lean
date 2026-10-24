import Shao.OQ3.ImaginaryExponentialTaylorRemainder
import Mathlib.Analysis.Complex.Trigonometric

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem imaginary_real_exponential_quadratic_error (b c : ℝ) :
    ‖Complex.exp ((b : ℂ) * Complex.I + (c : ℂ)) -
        (1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2 + (c : ℂ))‖ ≤
      (Real.exp 1 + 4) * |b| ^ 3 +
        (Real.exp 1 + 2) * |c| * |b| + c ^ 2 * Real.exp |c| := by
  have hpoly :
      (∑ j ∈ Finset.range 3, (((b : ℂ) * Complex.I) ^ j / (j.factorial : ℂ))) =
        1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq] <;> ring
  have h3 : ‖Complex.exp ((b : ℂ) * Complex.I) -
      (1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2)‖ ≤
        (Real.exp 1 + 4) * |b| ^ 3 := by
    have h := imaginary_exponential_taylor_remainder_bound 3 b
    norm_num [hpoly, add_assoc] at h
    exact h
  have h1 : ‖Complex.exp ((b : ℂ) * Complex.I) - 1‖ ≤
      (Real.exp 1 + 2) * |b| := by
    have h := imaginary_exponential_taylor_remainder_bound 1 b
    norm_num [Finset.sum_range_succ, add_assoc] at h
    exact h
  have hc : ‖Complex.exp (c : ℂ) - 1 - (c : ℂ)‖ ≤ c ^ 2 * Real.exp |c| := by
    simpa [Finset.sum_range_succ, sub_sub, sq_abs] using
      Complex.norm_exp_sub_sum_le_norm_mul_exp (c : ℂ) 2
  have hcross : ‖(c : ℂ) * (Complex.exp ((b : ℂ) * Complex.I) - 1)‖ ≤
      (Real.exp 1 + 2) * |c| * |b| := by
    calc
      ‖(c : ℂ) * (Complex.exp ((b : ℂ) * Complex.I) - 1)‖ =
          |c| * ‖Complex.exp ((b : ℂ) * Complex.I) - 1‖ := by
        rw [Complex.norm_mul]
        simp
      _ ≤ |c| * ((Real.exp 1 + 2) * |b|) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = (Real.exp 1 + 2) * |c| * |b| := by ring
  have hlast : ‖Complex.exp ((b : ℂ) * Complex.I) *
      (Complex.exp (c : ℂ) - 1 - (c : ℂ))‖ ≤ c ^ 2 * Real.exp |c| := by
    rw [Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hc
  have hid : Complex.exp ((b : ℂ) * Complex.I + (c : ℂ)) -
      (1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2 + (c : ℂ)) =
        (Complex.exp ((b : ℂ) * Complex.I) -
          (1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2)) +
        (c : ℂ) * (Complex.exp ((b : ℂ) * Complex.I) - 1) +
        Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp (c : ℂ) - 1 - (c : ℂ)) := by
    rw [Complex.exp_add]
    ring
  rw [hid]
  let A : ℂ := Complex.exp ((b : ℂ) * Complex.I) -
    (1 + (b : ℂ) * Complex.I - (b : ℂ) ^ 2 / 2)
  let B : ℂ := (c : ℂ) * (Complex.exp ((b : ℂ) * Complex.I) - 1)
  let D : ℂ := Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp (c : ℂ) - 1 - (c : ℂ))
  change ‖A + B + D‖ ≤ _
  have htri : ‖A + B + D‖ ≤ ‖A‖ + ‖B‖ + ‖D‖ :=
    (norm_add_le (A + B) D).trans (add_le_add (norm_add_le A B) (le_refl ‖D‖))
  exact htri.trans (add_le_add (add_le_add h3 hcross) hlast)

end
end Shao.OQ3
