import Shao.OQ3.ComplexWeightedMonomialRemainderBounds
import Shao.OQ3.FiniteWordMonomialEncoding

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000 in
theorem complex_finite_weighted_polynomial_growth_bound
    {ι τ : Type*} [Fintype ι] [Fintype τ]
    (A : ι → ℝ) (hA : ∀ j, 0 ≤ A j) (w : ι → ℕ)
    (c : τ → ℂ) (p : τ → ι → ℕ) (d : ℕ)
    (hdegree : ∀ i, (∑ j, w j * p i j) ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 ≤ r → ∀ a : ι → ℂ,
      (∀ j, ‖a j‖ ≤ A j * r ^ w j) →
        ‖∑ i, c i * ∏ j, a j ^ p i j‖ ≤ K * (1 + r ^ d) := by
  classical
  let B : ℝ := ∑ i, ‖c i‖ * ∏ j, A j ^ p i j
  have hB : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun j hj => pow_nonneg (hA j) _))
  refine ⟨B + 1, by positivity, ?_⟩
  intro r hr a ha
  have hrad (i : τ) : r ^ (∑ j, w j * p i j) ≤ 1 + r ^ d := by
    by_cases hr1 : r ≤ 1
    · exact (pow_le_one₀ hr hr1).trans (le_add_of_nonneg_right (pow_nonneg hr _))
    · exact (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hr1)) (hdegree i)).trans
        (le_add_of_nonneg_left (by norm_num))
  calc
    ‖∑ i, c i * ∏ j, a j ^ p i j‖ ≤
        ∑ i, ‖c i * ∏ j, a j ^ p i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ * ((∏ j, A j ^ p i j) * r ^ (∑ j, w j * p i j)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (complex_weighted_monomial_bound a A w (p i) r hr hA ha) (norm_nonneg _)
    _ ≤ ∑ i, (‖c i‖ * ∏ j, A j ^ p i j) * (1 + r ^ d) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = (‖c i‖ * ∏ j, A j ^ p i j) * r ^ (∑ j, w j * p i j) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hrad i)
          (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun j hj => pow_nonneg (hA j) _)))
    _ = B * (1 + r ^ d) := by rw [← Finset.sum_mul]
    _ ≤ (B + 1) * (1 + r ^ d) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) (by positivity)

set_option maxHeartbeats 1000000 in
theorem complex_six_order_filtered_polynomial_growth_bound
    (A : Fin 6 → ℝ) (hA : ∀ j, 0 ≤ A j) :
    let P : (Fin 6 → ℂ) → ℂ := fun a =>
      ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a (sigma i) else 0
    ∃ K : ℝ, 0 < K ∧ ∀ t r : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ r →
      ∀ a : Fin 6 → ℂ,
        (∀ j, ‖a j‖ ≤ A j * t ^ (j.val + 1) * r ^ (j.val + 3)) →
        ‖P a‖ ≤ K * (1 + r ^ 18) := by
  classical
  intro P
  let ι := Σ q : Fin 7, {sigma : Fin q.val → Fin 6 //
    (∑ i, ((sigma i).val + 1)) ≤ 6}
  let p : ι → Fin 6 → ℕ := fun i j => Fintype.card {l : Fin i.1.val // i.2.val l = j}
  let w : Fin 6 → ℕ := fun j => j.val + 3
  let c : ι → ℂ := fun i => 1 / (i.1.val.factorial : ℂ)
  have hdegree (i : ι) : (∑ j, w j * p i j) ≤ 18 := by
    have he := (finite_word_monomial_encoding i.2.val).2.1 w
    change (∑ j, w j * p i j) = ∑ l, ((i.2.val l).val + 3) at he
    rw [he]
    have hs : (∑ l, ((i.2.val l).val + 3)) =
        (∑ l, ((i.2.val l).val + 1)) + 2 * i.1.val := by
      calc
        _ = ∑ l, (((i.2.val l).val + 1) + 2) := by
          apply Finset.sum_congr rfl
          intro l hl
          omega
        _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]
    rw [hs]
    have hq : i.1.val ≤ 6 := Nat.le_of_lt_succ i.1.isLt
    have hw := i.2.property
    omega
  obtain ⟨K, hK, hbound⟩ := complex_finite_weighted_polynomial_growth_bound
    A hA w c p 18 hdegree
  have hmonomial (i : ι) (a : Fin 6 → ℂ) :
      (∏ j, a j ^ p i j) = ∏ l, a (i.2.val l) :=
    (finite_word_monomial_encoding i.2.val).2.2 a
  have hidentity (a : Fin 6 → ℂ) : P a = ∑ i : ι, c i * ∏ j, a j ^ p i j := by
    have hsub (q : Fin 7) :
        (∑ sigma : Fin q.val → Fin 6,
          if (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a (sigma l) else 0) =
          ∑ sigma : {sigma : Fin q.val → Fin 6 //
            (∑ l, ((sigma l).val + 1)) ≤ 6}, ∏ l, a (sigma.val l) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by intro sigma; simp) _
    calc
      P a = ∑ q : Fin 7, ∑ sigma : {sigma : Fin q.val → Fin 6 //
          (∑ l, ((sigma l).val + 1)) ≤ 6}, c ⟨q, sigma⟩ * ∏ j, a j ^ p ⟨q, sigma⟩ j := by
        dsimp only [P]
        apply Finset.sum_congr rfl
        intro q hq
        rw [hsub, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma hsigma
        rw [hmonomial]
      _ = ∑ i : ι, c i * ∏ j, a j ^ p i j :=
        (Fintype.sum_sigma (fun i : ι => c i * ∏ j, a j ^ p i j)).symm
  refine ⟨K, hK, ?_⟩
  intro t r ht0 ht1 hr a ha
  have ha' (j : Fin 6) : ‖a j‖ ≤ A j * r ^ w j := by
    calc
      ‖a j‖ ≤ A j * t ^ (j.val + 1) * r ^ (j.val + 3) := ha j
      _ ≤ (A j * 1) * r ^ (j.val + 3) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1) (hA j)) (pow_nonneg hr _)
      _ = A j * r ^ w j := by dsimp [w]; ring
  rw [hidentity]
  exact hbound r hr a ha'

end
end Shao.OQ3
