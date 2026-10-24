import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

namespace Shao.OQ3
open MeasureTheory
open scoped Topology BigOperators
noncomputable section

theorem one_add_nonnegative_power_bound (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k ≤ (2 : ℝ) ^ k * (1 + x ^ k) := by
  by_cases hx1 : x ≤ 1
  · calc
      (1 + x) ^ k ≤ (2 : ℝ) ^ k :=
        pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = (2 : ℝ) ^ k * 1 := by ring
      _ ≤ (2 : ℝ) ^ k * (1 + x ^ k) :=
        mul_le_mul_of_nonneg_left (by have h := pow_nonneg hx k; linarith) (by positivity)
  · have hxge : 1 ≤ x := (lt_of_not_ge hx1).le
    calc
      (1 + x) ^ k ≤ (2 * x) ^ k :=
        pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = (2 : ℝ) ^ k * x ^ k := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ k * (1 + x ^ k) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem integrable_even_power_gaussian (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => x ^ (2 * k) * Real.exp (-a * x ^ 2)) := by
  have hs : (-1 : ℝ) < ((2 * k : ℕ) : ℝ) := by
    have h0 : 0 ≤ ((2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  simpa only [Real.rpow_natCast] using
    (integrable_rpow_mul_exp_neg_mul_sq (s := ((2 * k : ℕ) : ℝ)) ha hs)

theorem integrable_one_add_square_power_gaussian (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ k * Real.exp (-a * x ^ 2)) := by
  have hg : Integrable (fun x : ℝ =>
      (2 : ℝ) ^ k * (Real.exp (-a * x ^ 2) +
        x ^ (2 * k) * Real.exp (-a * x ^ 2))) :=
    ((integrable_exp_neg_mul_sq ha).add (integrable_even_power_gaussian k a ha)).const_mul _
  apply hg.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (1 + x ^ 2) ^ k * Real.exp (-a * x ^ 2) ≤
        ((2 : ℝ) ^ k * (1 + (x ^ 2) ^ k)) * Real.exp (-a * x ^ 2) :=
      mul_le_mul_of_nonneg_right (one_add_nonnegative_power_bound (x ^ 2) (sq_nonneg x) k)
        (Real.exp_nonneg _)
    _ = (2 : ℝ) ^ k * (Real.exp (-a * x ^ 2) +
        x ^ (2 * k) * Real.exp (-a * x ^ 2)) := by
      rw [← pow_mul]
      ring

theorem integrable_euclidean_radius_power_gaussian (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun w : ℝ × ℝ =>
      (Real.sqrt (w.1 ^ 2 + w.2 ^ 2)) ^ k * Real.exp (-a * (w.1 ^ 2 + w.2 ^ 2))) := by
  have h1 := integrable_one_add_square_power_gaussian k a ha
  have hg : Integrable (fun w : ℝ × ℝ =>
      ((1 + w.1 ^ 2) ^ k * Real.exp (-a * w.1 ^ 2)) *
        ((1 + w.2 ^ 2) ^ k * Real.exp (-a * w.2 ^ 2))) := h1.mul_prod h1
  apply hg.mono' (by fun_prop)
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  let r : ℝ := Real.sqrt (w.1 ^ 2 + w.2 ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = w.1 ^ 2 + w.2 ^ 2 := Real.sq_sqrt (by positivity)
  have hr : r ≤ (1 + w.1 ^ 2) * (1 + w.2 ^ 2) := by
    nlinarith [sq_nonneg (r - 1), mul_nonneg (sq_nonneg w.1) (sq_nonneg w.2)]
  have hp : r ^ k ≤ (1 + w.1 ^ 2) ^ k * (1 + w.2 ^ 2) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hr0 hr k
  have hexp : Real.exp (-a * (w.1 ^ 2 + w.2 ^ 2)) =
      Real.exp (-a * w.1 ^ 2) * Real.exp (-a * w.2 ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    r ^ k * Real.exp (-a * (w.1 ^ 2 + w.2 ^ 2)) =
        r ^ k * (Real.exp (-a * w.1 ^ 2) * Real.exp (-a * w.2 ^ 2)) := by rw [hexp]
    _ ≤ ((1 + w.1 ^ 2) ^ k * (1 + w.2 ^ 2) ^ k) *
        (Real.exp (-a * w.1 ^ 2) * Real.exp (-a * w.2 ^ 2)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = ((1 + w.1 ^ 2) ^ k * Real.exp (-a * w.1 ^ 2)) *
        ((1 + w.2 ^ 2) ^ k * Real.exp (-a * w.2 ^ 2)) := by ring

end
end Shao.OQ3
