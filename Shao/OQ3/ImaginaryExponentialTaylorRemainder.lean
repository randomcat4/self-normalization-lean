import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem imaginary_exponential_taylor_remainder_bound
    (m : ℕ) (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) -
        (∑ j ∈ Finset.range m, ((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ))‖ ≤
      (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m := by
  classical
  have hnorm : ‖((t : ℂ) * Complex.I)‖ = |t| := by
    simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hp0 : 0 ≤ |t| ^ m := pow_nonneg (abs_nonneg t) m
  by_cases hsmall : |t| ≤ 1
  · have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp ((t : ℂ) * Complex.I) m
    rw [hnorm] at hrem
    calc
      _ ≤ |t| ^ m * Real.exp |t| := hrem
      _ ≤ |t| ^ m * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsmall) hp0
      _ = Real.exp 1 * |t| ^ m := mul_comm _ _
      _ ≤ (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m :=
        mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) m]) hp0
  · have hlarge : 1 ≤ |t| := (lt_of_not_ge hsmall).le
    have hp1 : 1 ≤ |t| ^ m := one_le_pow₀ hlarge
    have hterm : ∀ j ∈ Finset.range m,
        ‖((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)‖ ≤ |t| ^ m := by
      intro j hj
      have hfact : (1 : ℝ) ≤ (j.factorial : ℝ) := by
        exact_mod_cast (Nat.one_le_of_lt (Nat.factorial_pos j))
      have hfact0 : (0 : ℝ) < (j.factorial : ℝ) := by
        exact_mod_cast (Nat.factorial_pos j)
      have hjm : j ≤ m := (Finset.mem_range.mp hj).le
      calc
        _ = |t| ^ j / (j.factorial : ℝ) := by
          rw [Complex.norm_div, Complex.norm_pow, hnorm, Complex.norm_natCast]
        _ ≤ |t| ^ j := (div_le_iff₀ hfact0).2 (by
          have hmul := mul_le_mul_of_nonneg_left hfact (pow_nonneg (abs_nonneg t) j)
          simpa only [mul_one] using hmul)
        _ ≤ |t| ^ m := pow_le_pow_right₀ hlarge hjm
    have hsum : ‖∑ j ∈ Finset.range m,
        ((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)‖ ≤ (m : ℝ) * |t| ^ m := by
      calc
        _ ≤ ∑ j ∈ Finset.range m, ‖((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.range m, |t| ^ m := Finset.sum_le_sum hterm
        _ = (m : ℝ) * |t| ^ m := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc
      _ ≤ ‖Complex.exp ((t : ℂ) * Complex.I)‖ +
          ‖∑ j ∈ Finset.range m, ((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)‖ :=
        norm_sub_le _ _
      _ = 1 + ‖∑ j ∈ Finset.range m,
          ((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)‖ := by
        rw [Complex.norm_exp_ofReal_mul_I]
      _ ≤ 1 + (m : ℝ) * |t| ^ m := add_le_add (le_refl 1) hsum
      _ ≤ ((m : ℝ) + 1) * |t| ^ m := by nlinarith
      _ ≤ (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m :=
        mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (1 : ℝ)]) hp0

end
end Shao.OQ3
