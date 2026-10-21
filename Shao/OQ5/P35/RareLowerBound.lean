import Shao.OQ5.P35.RareEvents
import Shao.OQ5.P35.BinomialBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Eventual lower bounds for the actual p35 rare-category event

Source: p35 §4, formula (9). All events use the same fixed sample law.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open Filter
open scoped Topology

private theorem targetCategoryCount_cast (j : ℕ) :
    (targetCategoryCount j : ℝ) = categoryScale j := by
  simp [targetCategoryCount, categoryScale]

private theorem categoryScale_pos (j : ℕ) : 0 < categoryScale j := by
  unfold categoryScale
  positivity

theorem rareSampleSize_tail_error (j : ℕ) (hj : 1 ≤ j) :
    (rareSampleSize j : ℝ) * (1 - categoryBelowMass j) =
      (16384 / 16383 : ℝ) * (1 / 64 : ℝ) ^ j := by
  rw [categoryBelowMass_eq j hj]
  simp only [rareSampleSize, targetCategoryCount, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ = (16384 / 16383 : ℝ) * ((4 : ℝ) ^ 4) ^ j * (1 / 16384 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j 4, pow_mul]
      ring
    _ = _ := by
      rw [mul_assoc, ← mul_pow]
      norm_num

private theorem categoryBelowMass_power_lower (j : ℕ) (hj : 1 ≤ j) :
    1 - (16384 / 16383 : ℝ) * (1 / 64 : ℝ) ^ j ≤
      categoryBelowMass j ^ (rareSampleSize j - targetCategoryCount j) := by
  have hq0 := categoryBelowMass_nonneg j
  have hq1 := (categoryBelowMass_bounds j hj).2.le
  have hm : ((rareSampleSize j - targetCategoryCount j : ℕ) : ℝ) ≤ rareSampleSize j := by
    exact_mod_cast Nat.sub_le (rareSampleSize j) (targetCategoryCount j)
  have hmul := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hq1)
  have hbern := one_add_mul_sub_le_pow (by linarith : -1 ≤ categoryBelowMass j)
    (rareSampleSize j - targetCategoryCount j)
  rw [← rareSampleSize_tail_error j hj]
  nlinarith

theorem categoryBelowMass_power_tendsto :
    Tendsto (fun j => categoryBelowMass j ^ (rareSampleSize j - targetCategoryCount j))
      atTop (nhds (1 : ℝ)) := by
  have hgeom : Tendsto (fun j : ℕ => (16384 / 16383 : ℝ) * (1 / 64 : ℝ) ^ j)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (by norm_num : (1 / 64 : ℝ) < 1))
  have hl : Tendsto (fun j : ℕ => 1 - (16384 / 16383 : ℝ) * (1 / 64 : ℝ) ^ j)
      atTop (nhds (1 : ℝ)) := by simpa using tendsto_const_nhds.sub hgeom
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with j hj
    exact categoryBelowMass_power_lower j hj
  · filter_upwards [eventually_ge_atTop 1] with j hj
    exact pow_le_one₀ (categoryBelowMass_nonneg j) (categoryBelowMass_bounds j hj).2.le

private theorem categoryMass_eq_inv_scale_pow (j : ℕ) (hj : 1 ≤ j) :
    categoryMass j = (categoryScale j)⁻¹ ^ 7 := by
  simp only [categoryMass, show j ≠ 0 by omega, ite_false]
  unfold categoryScale
  calc
    (1 / 16384 : ℝ) ^ j = ((4 : ℝ) ^ 7)⁻¹ ^ j := by norm_num
    _ = ((4 : ℝ) ^ j)⁻¹ ^ 7 := by
      rw [← inv_pow, ← inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 7 j]

private theorem rare_coefficient_identity (j : ℕ) (hj : 1 ≤ j) :
    (((rareSampleSize j : ℝ) / (targetCategoryCount j : ℝ)) ^ targetCategoryCount j) *
        categoryMass j ^ targetCategoryCount j =
      (categoryScale j)⁻¹ ^ (4 * targetCategoryCount j) := by
  have hk : categoryScale j ≠ 0 := (categoryScale_pos j).ne'
  have hratio : (rareSampleSize j : ℝ) / (targetCategoryCount j : ℝ) =
      categoryScale j ^ 3 := by
    rw [rareSampleSize, Nat.cast_pow, targetCategoryCount_cast]
    field_simp [hk]
  rw [hratio, categoryMass_eq_inv_scale_pow j hj, ← mul_pow]
  have hbase : categoryScale j ^ 3 * (categoryScale j)⁻¹ ^ 7 =
      (categoryScale j)⁻¹ ^ 4 := by
    field_simp [hk]
  rw [hbase, ← pow_mul]

theorem rareCategoryEvent_half_lower :
    ∀ᶠ j in atTop,
      (1 / 2 : ℝ) * (categoryScale j)⁻¹ ^ (4 * targetCategoryCount j) ≤
        sampleLaw.real (rareCategoryEvent j) := by
  have hhalf : ∀ᶠ j in atTop, (1 / 2 : ℝ) ≤
      categoryBelowMass j ^ (rareSampleSize j - targetCategoryCount j) :=
    (categoryBelowMass_power_tendsto.eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  filter_upwards [eventually_ge_atTop 1, hhalf] with j hj hh
  have hk : 0 < targetCategoryCount j := by unfold targetCategoryCount; positivity
  have hchoose := real_pow_div_le_choose (rareSampleSize j) (targetCategoryCount j) hk
    (targetCategoryCount_le_rareSampleSize j)
  have hcoef := mul_le_mul_of_nonneg_right hchoose
    (pow_nonneg (categoryMass_nonneg j) (targetCategoryCount j))
  rw [rare_coefficient_identity j hj] at hcoef
  rw [rareCategoryEvent_probability j hj]
  calc
    _ = (categoryScale j)⁻¹ ^ (4 * targetCategoryCount j) * (1 / 2 : ℝ) := by ring
    _ ≤ (((rareSampleSize j).choose (targetCategoryCount j) : ℝ) *
        categoryMass j ^ targetCategoryCount j) *
        categoryBelowMass j ^ (rareSampleSize j - targetCategoryCount j) :=
      mul_le_mul hcoef hh (by norm_num)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (categoryMass_nonneg j) _))

theorem rareCategoryEvent_exp_comparison :
    ∀ᶠ j in atTop,
      Real.exp (-5 * categoryScale j * Real.log (categoryScale j)) ≤
        (1 / 2 : ℝ) * (categoryScale j)⁻¹ ^ (4 * targetCategoryCount j) := by
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hk0 := categoryScale_pos j
  have hk1 := categoryScale_one_le j
  have hk4 : 4 ≤ categoryScale j := by
    cases j with
    | zero => omega
    | succ j => exact categoryScale_succ_ge j
  have hlog0 : 0 ≤ Real.log (categoryScale j) := Real.log_nonneg hk1
  have hlog2 : Real.log 2 ≤ Real.log (categoryScale j) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hprod : Real.log 2 ≤ categoryScale j * Real.log (categoryScale j) := by
    exact hlog2.trans (le_mul_of_one_le_left hlog0 hk1)
  have hright : 0 < (1 / 2 : ℝ) * (categoryScale j)⁻¹ ^ (4 * targetCategoryCount j) := by
    positivity
  apply (Real.log_le_log_iff (Real.exp_pos _) hright).mp
  rw [Real.log_exp, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    Real.log_inv, Real.log_div (by norm_num) (by norm_num), Real.log_one]
  simp only [Nat.cast_mul, Nat.cast_ofNat, targetCategoryCount_cast]
  nlinarith

theorem rareCategoryEvent_exp_lower :
    ∀ᶠ j in atTop,
      Real.exp (-5 * categoryScale j * Real.log (categoryScale j)) ≤
        sampleLaw.real (rareCategoryEvent j) := by
  filter_upwards [rareCategoryEvent_exp_comparison, rareCategoryEvent_half_lower] with j he hh
  exact he.trans hh

end

end Shao.OQ5.P35
