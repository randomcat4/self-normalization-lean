import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace Shao.OQ3

open scoped BigOperators
noncomputable section

theorem complex_log_taylor_quartic_correction_bound
    (a b c : ℂ) (r A B C : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ A * r ^ 2)
    (hb : ‖b‖ ≤ B * r ^ 3)
    (hc : ‖c‖ ≤ C * r ^ 4) :
    ‖Complex.logTaylor 3 (a + b + c) -
      (a + b + c - a ^ 2 / 2)‖ ≤
        (A * (B + C) + (B + C) ^ 2) * r ^ 5 := by
  have hlog (z : ℂ) : Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
    norm_num [Complex.logTaylor, Finset.sum_range_succ] <;> ring
  have hS : 0 ≤ B + C := add_nonneg hB hC
  have hr43 : r ^ 4 ≤ r ^ 3 := by
    calc
      r ^ 4 = r ^ 3 * r := by ring
      _ ≤ r ^ 3 * 1 := mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 3)
      _ = r ^ 3 := by ring
  have hr65 : r ^ 6 ≤ r ^ 5 := by
    calc
      r ^ 6 = r ^ 5 * r := by ring
      _ ≤ r ^ 5 * 1 := mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 5)
      _ = r ^ 5 := by ring
  have hx : ‖b + c‖ ≤ (B + C) * r ^ 3 := by
    calc
      ‖b + c‖ ≤ ‖b‖ + ‖c‖ := norm_add_le b c
      _ ≤ B * r ^ 3 + C * r ^ 3 :=
        add_le_add hb (hc.trans (mul_le_mul_of_nonneg_left hr43 hC))
      _ = (B + C) * r ^ 3 := by ring
  have hab : ‖a * (b + c)‖ ≤ A * (B + C) * r ^ 5 := by
    calc
      ‖a * (b + c)‖ = ‖a‖ * ‖b + c‖ := Complex.norm_mul _ _
      _ ≤ (A * r ^ 2) * ((B + C) * r ^ 3) :=
        mul_le_mul ha hx (norm_nonneg _) (mul_nonneg hA (pow_nonneg hr0 2))
      _ = A * (B + C) * r ^ 5 := by ring
  have hx2 : ‖b + c‖ ^ 2 ≤ (B + C) ^ 2 * r ^ 6 := by
    calc
      ‖b + c‖ ^ 2 ≤ ((B + C) * r ^ 3) * ((B + C) * r ^ 3) := by
        simpa only [pow_two] using
          mul_le_mul hx hx (norm_nonneg _) (mul_nonneg hS (pow_nonneg hr0 3))
      _ = (B + C) ^ 2 * r ^ 6 := by ring
  have hhalf : ‖(b + c) ^ 2 / (2 : ℂ)‖ ≤ (B + C) ^ 2 * r ^ 5 := by
    calc
      ‖(b + c) ^ 2 / (2 : ℂ)‖ = ‖b + c‖ ^ 2 / 2 := by
        rw [Complex.norm_div, Complex.norm_pow]
        norm_num
      _ ≤ ‖b + c‖ ^ 2 := div_le_self (sq_nonneg _) (by norm_num)
      _ ≤ (B + C) ^ 2 * r ^ 6 := hx2
      _ ≤ (B + C) ^ 2 * r ^ 5 :=
        mul_le_mul_of_nonneg_left hr65 (sq_nonneg _)
  have heq : Complex.logTaylor 3 (a + b + c) -
      (a + b + c - a ^ 2 / 2) =
        -(a * (b + c)) - (b + c) ^ 2 / (2 : ℂ) := by
    rw [hlog]
    ring
  rw [heq]
  calc
    ‖-(a * (b + c)) - (b + c) ^ 2 / (2 : ℂ)‖ ≤
        ‖a * (b + c)‖ + ‖(b + c) ^ 2 / (2 : ℂ)‖ := by
      simpa only [norm_neg] using
        norm_sub_le (-(a * (b + c))) ((b + c) ^ 2 / (2 : ℂ))
    _ ≤ A * (B + C) * r ^ 5 + (B + C) ^ 2 * r ^ 5 :=
      add_le_add hab hhalf
    _ = (A * (B + C) + (B + C) ^ 2) * r ^ 5 := by ring

end
end Shao.OQ3
