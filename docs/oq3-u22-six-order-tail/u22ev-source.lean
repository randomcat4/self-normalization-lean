import Shao.OQ3.ComplexSixOrderFilteredPolynomial
import Mathlib.Analysis.Complex.Trigonometric

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem complex_gaussian_six_order_exponential_polynomial_error
    (A : Fin 6 → ℝ) (hA : ∀ j, 0 ≤ A j) :
    let P : (Fin 6 → ℂ) → ℂ := fun a =>
      ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
        ∑ sigma : Fin q.val → Fin 6,
          if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a (sigma i) else 0
    ∃ K : ℝ, 0 < K ∧ ∀ t r : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ r →
      ∀ a : Fin 6 → ℂ,
        (∀ j, ‖a j‖ ≤ A j * t ^ (j.val + 1) * r ^ (j.val + 3)) →
        ‖∑ j, a j‖ ≤ r ^ 2 / 4 →
        ‖Complex.exp (-((r ^ 2 : ℝ) : ℂ) / 2) *
            (Complex.exp (∑ j, a j) - P a)‖ ≤
          K * t ^ 7 * (r ^ 9 + r ^ 56) * Real.exp (-(r ^ 2) / 4) := by
  classical
  intro P
  obtain ⟨K0, hK0, hEU⟩ := complex_exp_taylor_six_weighted_tail_bound A hA
  let B : ℝ := ∑ j, A j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hA j)
  refine ⟨128 * B ^ 7 + 2 * K0, by positivity, ?_⟩
  intro t r ht0 ht1 hr0 a ha hz
  let z : ℂ := ∑ j, a j
  let T6 : ℂ := ∑ q : Fin 7, z ^ q.val / (q.val.factorial : ℂ)
  let g : ℂ := Complex.exp (-((r ^ 2 : ℝ) : ℂ) / 2)
  change ‖z‖ ≤ r ^ 2 / 4 at hz
  have hrad (j : Fin 6) : r ^ (j.val + 3) ≤ r ^ 3 + r ^ 8 := by
    by_cases hr1 : r ≤ 1
    · exact (pow_le_pow_of_le_one hr0 hr1 (by omega : 3 ≤ j.val + 3)).trans
        (le_add_of_nonneg_right (pow_nonneg hr0 _))
    · have hj : j.val + 3 ≤ 8 := by have h := j.isLt; omega
      exact (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hr1)) hj).trans
        (le_add_of_nonneg_left (pow_nonneg hr0 _))
  have ht (j : Fin 6) : t ^ (j.val + 1) ≤ t := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one ht0 ht1 (by omega : 1 ≤ j.val + 1)
  have hNorm : ‖z‖ ≤ B * t * (r ^ 3 + r ^ 8) := by
    calc
      _ ≤ ∑ j, ‖a j‖ := norm_sum_le _ _
      _ ≤ ∑ j, A j * t * (r ^ 3 + r ^ 8) := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          _ ≤ A j * t ^ (j.val + 1) * r ^ (j.val + 3) := ha j
          _ ≤ A j * t * r ^ (j.val + 3) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (ht j) (hA j)) (pow_nonneg hr0 _)
          _ ≤ _ := mul_le_mul_of_nonneg_left (hrad j) (mul_nonneg (hA j) ht0)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hR7 : (r ^ 3 + r ^ 8) ^ 7 ≤ 128 * (r ^ 9 + r ^ 56) := by
    by_cases hr1 : r ≤ 1
    · have hR : r ^ 3 + r ^ 8 ≤ 2 * r ^ 3 := by
        have h := pow_le_pow_of_le_one hr0 hr1 (by norm_num : 3 ≤ 8)
        linarith
      calc
        _ ≤ (2 * r ^ 3) ^ 7 := pow_le_pow_left₀ (by positivity) hR _
        _ = 128 * r ^ 21 := by ring
        _ ≤ 128 * r ^ 9 := mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hr0 hr1 (by norm_num : 9 ≤ 21)) (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (pow_nonneg hr0 _)) (by norm_num)
    · have hr1' : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
      have hR : r ^ 3 + r ^ 8 ≤ 2 * r ^ 8 := by
        have h := pow_le_pow_right₀ hr1' (by norm_num : 3 ≤ 8)
        linarith
      calc
        _ ≤ (2 * r ^ 8) ^ 7 := pow_le_pow_left₀ (by positivity) hR _
        _ = 128 * r ^ 56 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (pow_nonneg hr0 _)) (by norm_num)
  have hPow : ‖z‖ ^ 7 ≤ 128 * B ^ 7 * t ^ 7 * (r ^ 9 + r ^ 56) := by
    calc
      _ ≤ (B * t * (r ^ 3 + r ^ 8)) ^ 7 :=
        pow_le_pow_left₀ (norm_nonneg _) hNorm _
      _ = B ^ 7 * t ^ 7 * (r ^ 3 + r ^ 8) ^ 7 := by ring
      _ ≤ B ^ 7 * t ^ 7 * (128 * (r ^ 9 + r ^ 56)) :=
        mul_le_mul_of_nonneg_left hR7 (mul_nonneg (pow_nonneg hB _) (pow_nonneg ht0 _))
      _ = _ := by ring
  have hT : T6 = ∑ q ∈ Finset.range 7, z ^ q / (q.factorial : ℂ) := by
    norm_num [T6, Fin.sum_univ_succ, Finset.sum_range_succ] <;> ring
  have hTaylor : ‖Complex.exp z - T6‖ ≤ ‖z‖ ^ 7 * Real.exp ‖z‖ := by
    rw [hT]
    exact Complex.norm_exp_sub_sum_le_norm_mul_exp z 7
  have hg : ‖g‖ = Real.exp (-(r ^ 2) / 2) := by
    dsimp only [g]
    rw [Complex.norm_exp]
    congr 1
    norm_num [pow_two, Complex.mul_re]
  have hTaylorWeighted :
      ‖g * (Complex.exp z - T6)‖ ≤
        128 * B ^ 7 * t ^ 7 * (r ^ 9 + r ^ 56) * Real.exp (-(r ^ 2) / 4) := by
    calc
      _ = Real.exp (-(r ^ 2) / 2) * ‖Complex.exp z - T6‖ := by rw [norm_mul, hg]
      _ ≤ Real.exp (-(r ^ 2) / 2) * (‖z‖ ^ 7 * Real.exp ‖z‖) :=
        mul_le_mul_of_nonneg_left hTaylor (Real.exp_pos _).le
      _ = ‖z‖ ^ 7 * Real.exp (-(r ^ 2) / 2 + ‖z‖) := by rw [Real.exp_add]; ring
      _ ≤ ‖z‖ ^ 7 * Real.exp (-(r ^ 2) / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (pow_nonneg (norm_nonneg _) _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hPow (Real.exp_pos _).le
  have hr48 : r ^ 48 ≤ r ^ 9 + r ^ 56 := by
    by_cases hr1 : r ≤ 1
    · exact (pow_le_pow_of_le_one hr0 hr1 (by norm_num : 9 ≤ 48)).trans
        (le_add_of_nonneg_right (pow_nonneg hr0 _))
    · exact (pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hr1)) (by norm_num : 48 ≤ 56)).trans
        (le_add_of_nonneg_left (pow_nonneg hr0 _))
  have hRad : r ^ 9 + r ^ 48 ≤ 2 * (r ^ 9 + r ^ 56) := by
    have h := pow_nonneg hr0 56
    linarith
  have hPoly : ‖T6 - P a‖ ≤ 2 * K0 * t ^ 7 * (r ^ 9 + r ^ 56) := by
    have h := hEU t r ht0 ht1 hr0 a ha
    calc
      _ ≤ K0 * t ^ 7 * (r ^ 9 + r ^ 48) := h
      _ ≤ K0 * t ^ 7 * (2 * (r ^ 9 + r ^ 56)) :=
        mul_le_mul_of_nonneg_left hRad (mul_nonneg hK0.le (pow_nonneg ht0 _))
      _ = _ := by ring
  have hgLe : Real.exp (-(r ^ 2) / 2) ≤ Real.exp (-(r ^ 2) / 4) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg r])
  have hPolyWeighted :
      ‖g * (T6 - P a)‖ ≤
        2 * K0 * t ^ 7 * (r ^ 9 + r ^ 56) * Real.exp (-(r ^ 2) / 4) := by
    calc
      _ = ‖T6 - P a‖ * Real.exp (-(r ^ 2) / 2) := by rw [norm_mul, hg]; ring
      _ ≤ _ := mul_le_mul hPoly hgLe (Real.exp_pos _).le (by positivity)
  calc
    _ = ‖g * (Complex.exp z - T6) + g * (T6 - P a)‖ := by congr 1; dsimp only [g, z]; ring
    _ ≤ ‖g * (Complex.exp z - T6)‖ + ‖g * (T6 - P a)‖ := norm_add_le _ _
    _ ≤ 128 * B ^ 7 * t ^ 7 * (r ^ 9 + r ^ 56) * Real.exp (-(r ^ 2) / 4) +
        2 * K0 * t ^ 7 * (r ^ 9 + r ^ 56) * Real.exp (-(r ^ 2) / 4) :=
      add_le_add hTaylorWeighted hPolyWeighted
    _ = _ := by ring

end
end Shao.OQ3
