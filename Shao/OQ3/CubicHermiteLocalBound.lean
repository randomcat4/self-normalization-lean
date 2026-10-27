import Shao.OQ3.GaussianHermitePolynomialRecursor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem gaussian_hermite_first_four_local_bounds
    (x : ℝ) (hx : |x| ≤ 1) :
    |(gaussianHermitePolynomial 0).eval x| ≤ 1 ∧
      |(gaussianHermitePolynomial 1).eval x| ≤ |x| ∧
      |(gaussianHermitePolynomial 2).eval x| ≤ 2 ∧
      |(gaussianHermitePolynomial 3).eval x| ≤ 4 * |x| := by
  obtain ⟨h0, h1, h2, h3⟩ := gaussian_hermite_polynomial_first_four
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hsq : |x| ^ 2 ≤ 1 := by nlinarith
  have hcube : |x| ^ 3 ≤ |x| := by
    nlinarith [mul_le_mul_of_nonneg_right hsq hx0]
  have htwo : |x ^ 2 - 1| ≤ 2 := by
    calc
      |x ^ 2 - 1| ≤ |x ^ 2| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 2 := by rw [abs_pow, abs_one]; nlinarith
  have hthree : |x ^ 3 - 3 * x| ≤ 4 * |x| := by
    calc
      |x ^ 3 - 3 * x| ≤ |x ^ 3| + |3 * x| := abs_sub _ _
      _ = |x| ^ 3 + 3 * |x| := by rw [abs_pow, abs_mul]; norm_num
      _ ≤ 4 * |x| := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [h0]
  · simp [h1]
  · simpa [h2] using htwo
  · simpa [h3] using hthree

theorem cubic_hermite_coefficient_sum_local_bound
    (b : Fin 4 → ℝ) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ j : Fin 4, |b j| ≤ B) :
    let P1 : (ℝ × ℝ) → ℝ := fun x => (1 / 6 : ℝ) *
      ∑ j : Fin 4, (Nat.choose 3 j.val : ℝ) * b j *
        (gaussianHermitePolynomial j.val).eval x.1 *
          (gaussianHermitePolynomial (3 - j.val)).eval x.2
    P1 (0, 0) = 0 ∧ ∀ x : ℝ × ℝ,
      Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ 1 →
        |P1 x| ≤ (16 / 3 : ℝ) * B * Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := by
  classical
  intro P1
  obtain ⟨hH0, hH1, hH2, hH3⟩ := gaussian_hermite_polynomial_first_four
  constructor
  · norm_num [P1, Fin.sum_univ_succ, hH0, hH1, hH2, hH3]
  · intro x hx
    let r : ℝ := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r ^ 2 = x.1 ^ 2 + x.2 ^ 2 :=
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hcoord1 : |x.1| ≤ r := by
      nlinarith [sq_abs x.1, sq_nonneg x.2, abs_nonneg x.1]
    have hcoord2 : |x.2| ≤ r := by
      nlinarith [sq_abs x.2, sq_nonneg x.1, abs_nonneg x.2]
    have hr1 : r ≤ 1 := hx
    have hf1 := gaussian_hermite_first_four_local_bounds x.1 (hcoord1.trans hr1)
    have hf2 := gaussian_hermite_first_four_local_bounds x.2 (hcoord2.trans hr1)
    have hterm (j : Fin 4) :
        |(gaussianHermitePolynomial j.val).eval x.1 *
          (gaussianHermitePolynomial (3 - j.val)).eval x.2| ≤ 4 * r := by
      fin_cases j
      · change |(gaussianHermitePolynomial 0).eval x.1 *
          (gaussianHermitePolynomial 3).eval x.2| ≤ 4 * r
        rw [hH0, Polynomial.eval_one, one_mul]
        exact hf2.2.2.2.trans (mul_le_mul_of_nonneg_left hcoord2 (by norm_num))
      · change |(gaussianHermitePolynomial 1).eval x.1 *
          (gaussianHermitePolynomial 2).eval x.2| ≤ 4 * r
        rw [abs_mul]
        calc
          _ ≤ |x.1| * 2 := mul_le_mul hf1.2.1 hf2.2.2.1 (abs_nonneg _) (abs_nonneg _)
          _ ≤ 4 * r := by nlinarith
      · change |(gaussianHermitePolynomial 2).eval x.1 *
          (gaussianHermitePolynomial 1).eval x.2| ≤ 4 * r
        rw [abs_mul]
        calc
          _ ≤ 2 * |x.2| := mul_le_mul hf1.2.2.1 hf2.2.1 (abs_nonneg _) (by norm_num)
          _ ≤ 4 * r := by nlinarith
      · change |(gaussianHermitePolynomial 3).eval x.1 *
          (gaussianHermitePolynomial 0).eval x.2| ≤ 4 * r
        rw [hH0, Polynomial.eval_one, mul_one]
        exact hf1.2.2.2.trans (mul_le_mul_of_nonneg_left hcoord1 (by norm_num))
    have hsum :
        |∑ j : Fin 4, (Nat.choose 3 j.val : ℝ) * b j *
          (gaussianHermitePolynomial j.val).eval x.1 *
            (gaussianHermitePolynomial (3 - j.val)).eval x.2| ≤ 32 * B * r := by
      calc
        _ ≤ ∑ j : Fin 4, |(Nat.choose 3 j.val : ℝ) * b j *
          (gaussianHermitePolynomial j.val).eval x.1 *
            (gaussianHermitePolynomial (3 - j.val)).eval x.2| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin 4, (Nat.choose 3 j.val : ℝ) * B * (4 * r) := by
          apply Finset.sum_le_sum
          intro j _
          have hcb : |(Nat.choose 3 j.val : ℝ) * b j| ≤
              (Nat.choose 3 j.val : ℝ) * B := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            exact mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg _)
          calc
            _ = |(Nat.choose 3 j.val : ℝ) * b j| *
                |(gaussianHermitePolynomial j.val).eval x.1 *
                  (gaussianHermitePolynomial (3 - j.val)).eval x.2| := by
              rw [← abs_mul]
              congr 1
              ring
            _ ≤ _ := mul_le_mul hcb (hterm j) (abs_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) hB)
        _ = 32 * B * r := by norm_num [Fin.sum_univ_succ] <;> ring
    change |(1 / 6 : ℝ) *
      ∑ j : Fin 4, (Nat.choose 3 j.val : ℝ) * b j *
        (gaussianHermitePolynomial j.val).eval x.1 *
          (gaussianHermitePolynomial (3 - j.val)).eval x.2| ≤ (16 / 3 : ℝ) * B * r
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    calc
      _ ≤ (1 / 6 : ℝ) * (32 * B * r) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (16 / 3 : ℝ) * B * r := by ring

end
end Shao.OQ3
