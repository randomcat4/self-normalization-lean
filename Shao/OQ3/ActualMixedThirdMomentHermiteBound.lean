import Shao.OQ3.DirectionalMomentPolynomialContinuity
import Shao.OQ3.CubicHermiteLocalBound

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem pair_mixed_third_moment_bound
    (mu : Measure (Fin 2 → ℝ))
    (hM : Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) mu) (j : Fin 4) :
    Integrable (fun y : Fin 2 → ℝ => y 0 ^ j.val * y 1 ^ (3 - j.val)) mu ∧
      |∫ y : Fin 2 → ℝ, y 0 ^ j.val * y 1 ^ (3 - j.val) ∂mu| ≤
        ∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂mu := by
  have hj : j.val ≤ 3 := Nat.le_of_lt_succ j.isLt
  have hmixed := (pair_directional_moment_binomial_continuous mu 3 hM).1 j.val hj
  have hdom (y : Fin 2 → ℝ) :
      |y 0 ^ j.val * y 1 ^ (3 - j.val)| ≤
        Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 := by
    let r : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r ^ 2 = y 0 ^ 2 + y 1 ^ 2 :=
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hcoord0 : |y 0| ≤ r := by
      nlinarith [sq_abs (y 0), sq_nonneg (y 1), abs_nonneg (y 0)]
    have hcoord1 : |y 1| ≤ r := by
      nlinarith [sq_abs (y 1), sq_nonneg (y 0), abs_nonneg (y 1)]
    rw [abs_mul, abs_pow, abs_pow]
    calc
      _ ≤ r ^ j.val * r ^ (3 - j.val) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hcoord0 _)
          (pow_le_pow_left₀ (abs_nonneg _) hcoord1 _)
          (pow_nonneg (abs_nonneg _) _) (pow_nonneg hr0 _)
      _ = r ^ 3 := by rw [← pow_add, Nat.add_sub_of_le hj]
  have hIntegral :
      ‖∫ y : Fin 2 → ℝ, y 0 ^ j.val * y 1 ^ (3 - j.val) ∂mu‖ ≤
        ∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂mu := by
    calc
      _ ≤ ∫ y : Fin 2 → ℝ, ‖y 0 ^ j.val * y 1 ^ (3 - j.val)‖ ∂mu :=
        norm_integral_le_integral_norm _
      _ ≤ _ := integral_mono hmixed.norm hM (fun y => by
        simpa only [Real.norm_eq_abs] using hdom y)
  exact ⟨hmixed, by simpa only [Real.norm_eq_abs] using hIntegral⟩

theorem uniform_actual_moment_cubic_hermite_local_bound
    {iota : Type*} (laws : iota → Measure (Fin 2 → ℝ))
    (B : ℝ) (hB : 0 ≤ B)
    (hM : ∀ p : iota, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) (laws p))
    (hBound : ∀ p : iota,
      (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂laws p) ≤ B) :
    let b : iota → Fin 4 → ℝ := fun p j =>
      ∫ y : Fin 2 → ℝ, y 0 ^ j.val * y 1 ^ (3 - j.val) ∂laws p
    let P1 : iota → (ℝ × ℝ) → ℝ := fun p x => (1 / 6 : ℝ) *
      ∑ j : Fin 4, (Nat.choose 3 j.val : ℝ) * b p j *
        (gaussianHermitePolynomial j.val).eval x.1 *
          (gaussianHermitePolynomial (3 - j.val)).eval x.2
    ∀ p : iota, P1 p (0, 0) = 0 ∧ ∀ x : ℝ × ℝ,
      Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ 1 →
        |P1 p x| ≤ (16 / 3 : ℝ) * B * Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := by
  intro b P1 p
  have hb (j : Fin 4) : |b p j| ≤ B :=
    (pair_mixed_third_moment_bound (laws p) (hM p) j).2.trans (hBound p)
  exact cubic_hermite_coefficient_sum_local_bound (b p) B hB hb

end
end Shao.OQ3
