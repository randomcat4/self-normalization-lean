import Shao.OQ3.ComplexWeightedMonomialRemainderBounds

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem complex_two_scale_weighted_polynomial_tail_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℂ) (p : ι → κ → ℕ) (w : κ → ℕ) (A : κ → ℝ)
    (hA : ∀ j, 0 ≤ A j)
    (hdeg : ∀ i,
      7 ≤ ∑ j, w j * p i j ∧
        9 ≤ ∑ j, (w j + 2) * p i j ∧
          (∑ j, (w j + 2) * p i j) ≤ 48) :
    ∃ K : ℝ, 0 < K ∧ ∀ t r : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ r →
      ∀ a : κ → ℂ,
        (∀ j, ‖a j‖ ≤ A j * t ^ (w j) * r ^ (w j + 2)) →
        ‖∑ i, c i * ∏ j, (a j) ^ (p i j)‖ ≤
          K * t ^ 7 * (r ^ 9 + r ^ 48) := by
  classical
  let B : ℝ := ∑ i, ‖c i‖ * ∏ j, A j ^ p i j
  have hprod (i : ι) : 0 ≤ ∏ j, A j ^ p i j :=
    Finset.prod_nonneg (fun j _ => pow_nonneg (hA j) _)
  have hB : 0 ≤ B := Finset.sum_nonneg
    (fun i _ => mul_nonneg (norm_nonneg _) (hprod i))
  refine ⟨B + 1, by linarith, ?_⟩
  intro t r ht0 ht1 hr0 a ha
  have hA' (j : κ) : 0 ≤ A j * r ^ (w j + 2) :=
    mul_nonneg (hA j) (pow_nonneg hr0 _)
  have ha' (j : κ) : ‖a j‖ ≤ (A j * r ^ (w j + 2)) * t ^ w j := by
    calc
      _ ≤ A j * t ^ w j * r ^ (w j + 2) := ha j
      _ = _ := by ring
  have htail := complex_weighted_polynomial_tail_bound
    a (fun j => A j * r ^ (w j + 2)) w c p 7 t ht0 ht1 hA' ha'
      (fun i => (hdeg i).1)
  have hrad (i : ι) : r ^ (∑ j, (w j + 2) * p i j) ≤ r ^ 9 + r ^ 48 := by
    by_cases hr1 : r ≤ 1
    · exact (pow_le_pow_of_le_one hr0 hr1 (hdeg i).2.1).trans
        (le_add_of_nonneg_right (pow_nonneg hr0 _))
    · exact (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hr1)) (hdeg i).2.2).trans
        (le_add_of_nonneg_left (pow_nonneg hr0 _))
  have hproducts (i : ι) :
      (∏ j, (A j * r ^ (w j + 2)) ^ p i j) =
        (∏ j, A j ^ p i j) * r ^ (∑ j, (w j + 2) * p i j) := by
    simp_rw [mul_pow, ← pow_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hcoeff :
      (∑ i, ‖c i‖ * ∏ j, (A j * r ^ (w j + 2)) ^ p i j) ≤
        B * (r ^ 9 + r ^ 48) := by
    dsimp only [B]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [hproducts]
    calc
      _ = (‖c i‖ * ∏ j, A j ^ p i j) * r ^ (∑ j, (w j + 2) * p i j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrad i) (mul_nonneg (norm_nonneg _) (hprod i))
  calc
    _ ≤ (∑ i, ‖c i‖ * ∏ j, (A j * r ^ (w j + 2)) ^ p i j) * t ^ 7 := htail
    _ ≤ (B * (r ^ 9 + r ^ 48)) * t ^ 7 :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg ht0 _)
    _ ≤ ((B + 1) * (r ^ 9 + r ^ 48)) * t ^ 7 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : B ≤ B + 1) (by positivity))
        (pow_nonneg ht0 _)
    _ = (B + 1) * t ^ 7 * (r ^ 9 + r ^ 48) := by ring

end
end Shao.OQ3
