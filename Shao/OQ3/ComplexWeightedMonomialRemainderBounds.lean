import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem complex_weighted_monomial_bound
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (A : ι → ℝ)
    (w p : ι → ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hA : ∀ j, 0 ≤ A j) (ha : ∀ j, ‖a j‖ ≤ A j * r ^ w j) :
    ‖∏ j, a j ^ p j‖ ≤ (∏ j, A j ^ p j) * r ^ (∑ j, w j * p j) := by
  calc
    _ = ∏ j, ‖a j‖ ^ p j := by simp only [Complex.norm_prod, norm_pow]
    _ ≤ ∏ j, (A j * r ^ w j) ^ p j := by
      apply Finset.prod_le_prod₀
      · intro j hj; positivity
      · intro j hj; exact pow_le_pow_left₀ (norm_nonneg _) (ha j) _
    _ = (∏ j, A j ^ p j) * ∏ j, r ^ (w j * p j) := by
      simp_rw [mul_pow, ← pow_mul]
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]

theorem complex_weighted_polynomial_tail_bound
    {ι τ : Type*} [Fintype ι] [Fintype τ]
    (a : ι → ℂ) (A : ι → ℝ) (w : ι → ℕ)
    (c : τ → ℂ) (p : τ → ι → ℕ) (d : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hA : ∀ j, 0 ≤ A j) (ha : ∀ j, ‖a j‖ ≤ A j * r ^ w j)
    (hdegree : ∀ t, d ≤ ∑ j, w j * p t j) :
    ‖∑ t, c t * ∏ j, a j ^ p t j‖ ≤
      (∑ t, ‖c t‖ * ∏ j, A j ^ p t j) * r ^ d := by
  calc
    _ ≤ ∑ t, ‖c t * ∏ j, a j ^ p t j‖ := norm_sum_le _ _
    _ = ∑ t, ‖c t‖ * ‖∏ j, a j ^ p t j‖ := by
      apply Finset.sum_congr rfl
      intro t ht
      exact norm_mul _ _
    _ ≤ ∑ t, ‖c t‖ * ((∏ j, A j ^ p t j) * r ^ (∑ j, w j * p t j)) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (complex_weighted_monomial_bound a A w (p t) r hr0 hA ha) (norm_nonneg _)
    _ ≤ ∑ t, (‖c t‖ * ∏ j, A j ^ p t j) * r ^ d := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        _ = (‖c t‖ * ∏ j, A j ^ p t j) * r ^ (∑ j, w j * p t j) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 (hdegree t))
          (mul_nonneg (norm_nonneg _)
            (Finset.prod_nonneg (fun j hj => pow_nonneg (hA j) _)))
    _ = _ := (Finset.sum_mul _ _ _).symm

end
end Shao.OQ3
