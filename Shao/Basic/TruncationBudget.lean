import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The scalar integrand of the truncated-moment budget

The source budget is `Rₙ(t) = n E[F((1+t)ξ)]`, with
`F(z) = z² min(|z|,1)`. This module proves its pointwise real-analysis inputs.
The marked inequalities are the kernels for the tail first and second moments
and the truncated third moment. They preserve the cutoff conventions: the
retained region is closed, and the deleted region is its strict complement.

No integration or measure-level continuity, strict increase, or limit of `Rₙ`
is asserted here. Those require a separate probability interface.
-/

set_option autoImplicit false

namespace Shao

/-- The actual scalar integrand in the source's truncated-moment budget. -/
def truncationF (z : ℝ) : ℝ := z ^ 2 * min |z| 1

theorem truncationF_nonneg (z : ℝ) : 0 ≤ truncationF z := by
  exact mul_nonneg (sq_nonneg z) (le_min (abs_nonneg z) zero_le_one)

theorem truncationF_neg (z : ℝ) : truncationF (-z) = truncationF z := by
  simp [truncationF]

theorem continuous_truncationF : Continuous truncationF := by
  unfold truncationF
  exact (continuous_id.pow 2).mul (continuous_abs.min continuous_const)

/-- The small region includes its boundary. -/
theorem truncationF_of_abs_le_one (z : ℝ) (hz : |z| ≤ 1) :
    truncationF z = |z| ^ 3 := by
  rw [truncationF, min_eq_left hz, ← sq_abs z]
  ring

/-- At the joining boundary the quadratic and cubic formulas agree. -/
theorem truncationF_of_one_le_abs (z : ℝ) (hz : 1 ≤ |z|) :
    truncationF z = z ^ 2 := by
  rw [truncationF, min_eq_right hz, mul_one]

theorem truncationF_le_sq (z : ℝ) : truncationF z ≤ z ^ 2 := by
  calc
    truncationF z = z ^ 2 * min |z| 1 := rfl
    _ ≤ z ^ 2 * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg z)
    _ = z ^ 2 := mul_one _

/-- The exponent is a genuine real exponent, including both endpoints 2 and 3. -/
theorem truncationF_le_rpow (z p : ℝ) (hp2 : 2 ≤ p) (hp3 : p ≤ 3) :
    truncationF z ≤ Real.rpow |z| p := by
  by_cases hz : |z| ≤ 1
  · rw [truncationF_of_abs_le_one z hz]
    calc
      |z| ^ 3 = Real.rpow |z| (3 : ℝ) := (Real.rpow_natCast _ 3).symm
      _ ≤ Real.rpow |z| p :=
        Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg z) hz (by linarith) hp3
  · have hz1 : 1 ≤ |z| := (lt_of_not_ge hz).le
    rw [truncationF_of_one_le_abs z hz1, ← sq_abs z]
    calc
      |z| ^ 2 = Real.rpow |z| (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ ≤ Real.rpow |z| p := Real.rpow_le_rpow_of_exponent_le hz1 hp2

/-- Downscaling has cubic lower and quadratic upper bounds, also at scale zero. -/
theorem truncationF_scale_le_one (c z : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c ^ 3 * truncationF z ≤ truncationF (c * z) ∧
      truncationF (c * z) ≤ c ^ 2 * truncationF z := by
  have hF : truncationF (c * z) = c ^ 2 * z ^ 2 * min (c * |z|) 1 := by
    rw [truncationF, mul_pow, abs_mul, abs_of_nonneg hc0]
  have hlow : c * min |z| 1 ≤ min (c * |z|) 1 := by
    rw [mul_min_of_nonneg _ _ hc0, mul_one]
    exact min_le_min le_rfl hc1
  have hmul : c * |z| ≤ |z| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (abs_nonneg z)
  have hupp : min (c * |z|) 1 ≤ min |z| 1 := min_le_min hmul le_rfl
  constructor
  · calc
      c ^ 3 * truncationF z = (c ^ 2 * z ^ 2) * (c * min |z| 1) := by
        unfold truncationF
        ring
      _ ≤ (c ^ 2 * z ^ 2) * min (c * |z|) 1 :=
        mul_le_mul_of_nonneg_left hlow (mul_nonneg (sq_nonneg c) (sq_nonneg z))
      _ = truncationF (c * z) := hF.symm
  · calc
      truncationF (c * z) = (c ^ 2 * z ^ 2) * min (c * |z|) 1 := hF
      _ ≤ (c ^ 2 * z ^ 2) * min |z| 1 :=
        mul_le_mul_of_nonneg_left hupp (mul_nonneg (sq_nonneg c) (sq_nonneg z))
      _ = c ^ 2 * truncationF z := by
        unfold truncationF
        ring

/-- Upscaling has quadratic lower and cubic upper bounds. -/
theorem truncationF_scale_one_le (c z : ℝ) (hc : 1 ≤ c) :
    c ^ 2 * truncationF z ≤ truncationF (c * z) ∧
      truncationF (c * z) ≤ c ^ 3 * truncationF z := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hF : truncationF (c * z) = c ^ 2 * z ^ 2 * min (c * |z|) 1 := by
    rw [truncationF, mul_pow, abs_mul, abs_of_nonneg hc0]
  have hmul : |z| ≤ c * |z| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (abs_nonneg z)
  have hlow : min |z| 1 ≤ min (c * |z|) 1 := min_le_min hmul le_rfl
  have hupp : min (c * |z|) 1 ≤ c * min |z| 1 := by
    rw [mul_min_of_nonneg _ _ hc0, mul_one]
    exact min_le_min le_rfl hc
  constructor
  · calc
      c ^ 2 * truncationF z = (c ^ 2 * z ^ 2) * min |z| 1 := by
        unfold truncationF
        ring
      _ ≤ (c ^ 2 * z ^ 2) * min (c * |z|) 1 :=
        mul_le_mul_of_nonneg_left hlow (mul_nonneg (sq_nonneg c) (sq_nonneg z))
      _ = truncationF (c * z) := hF.symm
  · calc
      truncationF (c * z) = (c ^ 2 * z ^ 2) * min (c * |z|) 1 := hF
      _ ≤ (c ^ 2 * z ^ 2) * (c * min |z| 1) :=
        mul_le_mul_of_nonneg_left hupp (mul_nonneg (sq_nonneg c) (sq_nonneg z))
      _ = c ^ 3 * truncationF z := by
        unfold truncationF
        ring

theorem truncationF_mono_abs (z w : ℝ) (hzw : |z| ≤ |w|) :
    truncationF z ≤ truncationF w := by
  have hsq : z ^ 2 ≤ w ^ 2 := by
    rw [← sq_abs z, ← sq_abs w]
    exact pow_le_pow_left₀ (abs_nonneg z) hzw 2
  exact mul_le_mul hsq (min_le_min hzw le_rfl)
    (le_min (abs_nonneg z) zero_le_one) (sq_nonneg w)

theorem truncationF_mono_scale (a b z : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    truncationF (a * z) ≤ truncationF (b * z) := by
  apply truncationF_mono_abs
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]
  exact mul_le_mul_of_nonneg_right hab (abs_nonneg z)

/-- The exact pointwise kernel of the source's retained/tail moment decomposition. -/
theorem truncationF_scaled_decomposition (a z : ℝ) (ha : 0 < a) :
    truncationF (a * z) =
      a ^ 3 * (if |z| ≤ 1 / a then |z| ^ 3 else 0) +
        a ^ 2 * (if 1 / a < |z| then z ^ 2 else 0) := by
  by_cases hs : |z| ≤ 1 / a
  · have hsmall : |a * z| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ha.le]
      nlinarith [(le_div_iff₀ ha).mp hs]
    rw [truncationF_of_abs_le_one _ hsmall, ite_eq_left hs,
      ite_eq_right (not_lt_of_ge hs)]
    simp only [abs_mul, abs_of_nonneg ha.le, mul_pow, mul_zero, add_zero]
  · have hl : 1 / a < |z| := lt_of_not_ge hs
    have hlarge : 1 ≤ |a * z| := by
      rw [abs_mul, abs_of_nonneg ha.le]
      nlinarith [(div_lt_iff₀ ha).mp hl]
    rw [truncationF_of_one_le_abs _ hlarge, ite_eq_right hs, ite_eq_left hl]
    simp only [mul_pow, mul_zero, zero_add]

/-- The tail first moment, with the source's strict large-observation cutoff. -/
theorem truncationF_tail_one (a z : ℝ) (ha : 0 < a) :
    a * (if 1 / a < |z| then |z| else 0) ≤ truncationF (a * z) := by
  by_cases hl : 1 / a < |z|
  · have hlarge : 1 ≤ a * |z| := by
      nlinarith [(div_lt_iff₀ ha).mp hl]
    have hlarge' : 1 ≤ |a * z| := by
      simpa only [abs_mul, abs_of_nonneg ha.le] using hlarge
    rw [ite_eq_left hl, truncationF_of_one_le_abs _ hlarge']
    calc
      a * |z| ≤ (a * |z|) ^ 2 := by nlinarith [sq_nonneg (a * |z| - 1)]
      _ = (a * z) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  · simp only [ite_eq_right hl, mul_zero]
    exact truncationF_nonneg _

/-- The tail second moment is one of the two nonnegative budget components. -/
theorem truncationF_tail_two (a z : ℝ) (ha : 0 < a) :
    a ^ 2 * (if 1 / a < |z| then z ^ 2 else 0) ≤ truncationF (a * z) := by
  rw [truncationF_scaled_decomposition a z ha]
  apply le_add_of_nonneg_left
  split_ifs <;> positivity

/-- The truncated third moment includes the entire small-observation boundary. -/
theorem truncationF_truncated_three (a z : ℝ) (ha : 0 < a) :
    a ^ 3 * (if |z| ≤ 1 / a then |z| ^ 3 else 0) ≤ truncationF (a * z) := by
  rw [truncationF_scaled_decomposition a z ha]
  apply le_add_of_nonneg_right
  split_ifs <;> positivity

end Shao
