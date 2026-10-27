import Shao.OQ3.ActualCGFNormalizedOcticPolynomial

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem pair_directional_moment_binomial_continuous
    (mu : Measure (Fin 2 → ℝ)) (k : ℕ)
    (hM : Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ k) mu) :
    let M : (ℝ × ℝ) → ℝ := fun z =>
      ∫ y : Fin 2 → ℝ, (z.1 * y 0 + z.2 * y 1) ^ k ∂mu
    let b : ℕ → ℝ := fun j =>
      ∫ y : Fin 2 → ℝ, y 0 ^ j * y 1 ^ (k - j) ∂mu
    (∀ j : ℕ, j ≤ k → Integrable
      (fun y : Fin 2 → ℝ => y 0 ^ j * y 1 ^ (k - j)) mu) ∧
      (∀ z : ℝ × ℝ, M z =
        ∑ j ∈ Finset.range (k + 1),
          z.1 ^ j * z.2 ^ (k - j) * (k.choose j : ℝ) * b j) ∧
      Continuous M := by
  intro M b
  have hmixed (j : ℕ) (hj : j ≤ k) :
      Integrable (fun y : Fin 2 → ℝ => y 0 ^ j * y 1 ^ (k - j)) mu := by
    apply hM.mono' (by fun_prop)
    filter_upwards [] with y
    let r : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hy0 : |y 0| ≤ r := by
      simpa only [Real.sqrt_sq_eq_abs] using
        (Real.sqrt_le_sqrt (show y 0 ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2 by nlinarith [sq_nonneg (y 1)]))
    have hy1 : |y 1| ≤ r := by
      simpa only [Real.sqrt_sq_eq_abs] using
        (Real.sqrt_le_sqrt (show y 1 ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2 by nlinarith [sq_nonneg (y 0)]))
    change ‖y 0 ^ j * y 1 ^ (k - j)‖ ≤ r ^ k
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
    calc
      _ ≤ r ^ j * r ^ (k - j) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy0 _)
          (pow_le_pow_left₀ (abs_nonneg _) hy1 _)
          (pow_nonneg (abs_nonneg _) _) (pow_nonneg hr _)
      _ = r ^ k := by rw [← pow_add, Nat.add_sub_of_le hj]
  have hformula (z : ℝ × ℝ) : M z =
      ∑ j ∈ Finset.range (k + 1),
        z.1 ^ j * z.2 ^ (k - j) * (k.choose j : ℝ) * b j := by
    have hterm (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
        Integrable (fun y : Fin 2 → ℝ =>
          (z.1 ^ j * z.2 ^ (k - j) * (k.choose j : ℝ)) *
            (y 0 ^ j * y 1 ^ (k - j))) mu :=
      (hmixed j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).const_mul _
    have heq (y : Fin 2 → ℝ) : (z.1 * y 0 + z.2 * y 1) ^ k =
        ∑ j ∈ Finset.range (k + 1),
          (z.1 ^ j * z.2 ^ (k - j) * (k.choose j : ℝ)) *
            (y 0 ^ j * y 1 ^ (k - j)) := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_pow, mul_pow]
      ring
    calc
      M z = ∫ y : Fin 2 → ℝ, ∑ j ∈ Finset.range (k + 1),
          (z.1 ^ j * z.2 ^ (k - j) * (k.choose j : ℝ)) *
            (y 0 ^ j * y 1 ^ (k - j)) ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall heq)
      _ = ∑ j ∈ Finset.range (k + 1), ∫ y : Fin 2 → ℝ,
          (z.1 ^ j * z.2 ^ (k - j) * (k.choose j : ℝ)) *
            (y 0 ^ j * y 1 ^ (k - j)) ∂mu := integral_finset_sum _ hterm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul]
  refine ⟨hmixed, hformula, ?_⟩
  rw [show M = (fun z : ℝ × ℝ => ∑ j ∈ Finset.range (k + 1),
    z.1 ^ j * z.2 ^ (k - j) * (k.choose j : ℝ) * b j) from funext hformula]
  fun_prop

end
end Shao.OQ3
