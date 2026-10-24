import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem complex_power_difference_bound_on_unit_ball
    (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (j : ℕ) :
    ‖z ^ j - w ^ j‖ ≤ (j : ℝ) * ‖z - w‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hzj : ‖z‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
      calc
        _ = ‖(z ^ j - w ^ j) * w + z ^ j * (z - w)‖ := by
          congr 1
          rw [pow_succ, pow_succ]
          ring
        _ ≤ ‖(z ^ j - w ^ j) * w‖ + ‖z ^ j * (z - w)‖ := norm_add_le _ _
        _ = ‖z ^ j - w ^ j‖ * ‖w‖ + ‖z‖ ^ j * ‖z - w‖ := by
          rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_pow]
        _ ≤ ((j : ℝ) * ‖z - w‖) * 1 + 1 * ‖z - w‖ := by
          apply add_le_add
          · exact mul_le_mul ih hw (norm_nonneg w)
              (mul_nonneg (Nat.cast_nonneg j) (norm_nonneg _))
          · exact mul_le_mul_of_nonneg_right hzj (norm_nonneg _)
        _ = ((j + 1 : ℕ) : ℝ) * ‖z - w‖ := by
          push_cast
          ring

theorem complex_log_taylor_difference_bound_on_unit_ball
    (n : ℕ) (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖Complex.logTaylor n z - Complex.logTaylor n w‖ ≤ (n : ℝ) * ‖z - w‖ := by
  classical
  change ‖(∑ j ∈ Finset.range n, (-1 : ℂ) ^ (j + 1) * z ^ j / (j : ℂ)) -
      (∑ j ∈ Finset.range n, (-1 : ℂ) ^ (j + 1) * w ^ j / (j : ℂ))‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  have hterm (j : ℕ) :
      ‖(-1 : ℂ) ^ (j + 1) * z ^ j / (j : ℂ) -
        (-1 : ℂ) ^ (j + 1) * w ^ j / (j : ℂ)‖ ≤ ‖z - w‖ := by
    by_cases hj : j = 0
    · subst j
      simp
    · have hjpos : (0 : ℝ) < (j : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hj
      have heq : (-1 : ℂ) ^ (j + 1) * z ^ j / (j : ℂ) -
          (-1 : ℂ) ^ (j + 1) * w ^ j / (j : ℂ) =
          (-1 : ℂ) ^ (j + 1) * (z ^ j - w ^ j) / (j : ℂ) := by ring
      rw [heq, Complex.norm_div, Complex.norm_mul, Complex.norm_pow]
      simp only [norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
      apply (div_le_iff₀ hjpos).2
      simpa only [mul_comm] using complex_power_difference_bound_on_unit_ball z w hz hw j
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        ‖(-1 : ℂ) ^ (j + 1) * z ^ j / (j : ℂ) -
          (-1 : ℂ) ^ (j + 1) * w ^ j / (j : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n, ‖z - w‖ := Finset.sum_le_sum (fun j _ => hterm j)
    _ = (n : ℝ) * ‖z - w‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem complex_log_taylor_perturbation_bound
    (n : ℕ) (z w : ℂ) (hz : ‖z‖ ≤ (1 : ℝ) / 2) (hw : ‖w‖ ≤ 1) :
    ‖Complex.log (1 + z) - Complex.logTaylor (n + 1) w‖ ≤
      2 * ‖z‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) +
        ((n + 1 : ℕ) : ℝ) * ‖z - w‖ := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (sub_pos_of_lt hz1) two_pos]
    linarith
  have hrem : ‖Complex.log (1 + z) - Complex.logTaylor (n + 1) z‖ ≤
      2 * ‖z‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / ((n + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_log_sub_logTaylor_le n hz1
      _ ≤ ‖z‖ ^ (n + 1) * 2 / ((n + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinv (pow_nonneg (norm_nonneg z) (n + 1))) (by positivity)
      _ = 2 * ‖z‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by ring
  have hpoly := complex_log_taylor_difference_bound_on_unit_ball (n + 1) z w (by linarith) hw
  calc
    _ = ‖(Complex.log (1 + z) - Complex.logTaylor (n + 1) z) +
        (Complex.logTaylor (n + 1) z - Complex.logTaylor (n + 1) w)‖ := by
      congr 1
      ring
    _ ≤ ‖Complex.log (1 + z) - Complex.logTaylor (n + 1) z‖ +
        ‖Complex.logTaylor (n + 1) z - Complex.logTaylor (n + 1) w‖ := norm_add_le _ _
    _ ≤ 2 * ‖z‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ) +
        ((n + 1 : ℕ) : ℝ) * ‖z - w‖ := add_le_add hrem hpoly

end
end Shao.OQ3

