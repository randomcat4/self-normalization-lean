import Shao.OQ5.P35.RareEvents
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The complete deterministic threshold and sparse subsequence scales for p35

Source: original p35 section7, lines209-216. These statements concern only
the fixed deterministic sequences; they impose no tail probability premise.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open Filter
open scoped Topology

/-- The one complete threshold sequence, fixed for every sample size. -/
def counterexampleThreshold (n : ℕ) : ℝ := (n : ℝ) ^ (3 / 20 : ℝ) / 16

theorem counterexampleThreshold_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < counterexampleThreshold n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) hn)
  exact div_pos (Real.rpow_pos_of_pos hn0 _) (by norm_num)

theorem counterexampleThreshold_tendsto :
    Tendsto counterexampleThreshold atTop atTop := by
  exact Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 16)
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 20)).comp
      tendsto_natCast_atTop_atTop)

private theorem threshold_div_rpow_tendsto_zero (r : ℝ) (hr : 3 / 20 < r) :
    Tendsto (fun n : ℕ => counterexampleThreshold n / (n : ℝ) ^ r) atTop (nhds 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim := h.div_const 16
  simp only [zero_div] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) hn)
  change (n : ℝ) ^ (-(r - 3 / 20)) / 16 =
    counterexampleThreshold n / (n : ℝ) ^ r
  rw [show -(r - 3 / 20) = 3 / 20 - r by ring, Real.rpow_sub hn0]
  unfold counterexampleThreshold
  ring

theorem counterexampleThreshold_div_sixth_tendsto_zero :
    Tendsto (fun n : ℕ => counterexampleThreshold n / (n : ℝ) ^ (1 / 6 : ℝ))
      atTop (nhds 0) :=
  threshold_div_rpow_tendsto_zero (1 / 6) (by norm_num)

theorem counterexampleThreshold_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => counterexampleThreshold n / Real.sqrt (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Real.sqrt_eq_rpow] using
    threshold_div_rpow_tendsto_zero (1 / 2) (by norm_num)

theorem strictMono_rareSampleSize : StrictMono rareSampleSize := by
  intro i j hij
  simpa only [rareSampleSize, targetCategoryCount, ← pow_mul] using
    pow_lt_pow_right₀ (by decide : 1 < (4 : ℕ))
      (Nat.mul_lt_mul_of_pos_right hij (by decide : 0 < 4))

theorem rareSampleSize_tendsto : Tendsto rareSampleSize atTop atTop :=
  strictMono_rareSampleSize.tendsto_atTop

private theorem cast_rareSampleSize (j : ℕ) :
    (rareSampleSize j : ℝ) = categoryScale j ^ 4 := by
  simp only [rareSampleSize, targetCategoryCount, categoryScale, Nat.cast_pow, Nat.cast_ofNat]

theorem counterexampleThreshold_rareSampleSize (j : ℕ) :
    counterexampleThreshold (rareSampleSize j) = categoryScale j ^ (3 / 5 : ℝ) / 16 := by
  have hk : 0 ≤ categoryScale j := le_trans (by norm_num) (categoryScale_one_le j)
  rw [counterexampleThreshold, cast_rareSampleSize,
    ← Real.rpow_natCast_mul hk 4 (3 / 20)]
  norm_num

theorem counterexampleThreshold_sq_half_rareSampleSize (j : ℕ) :
    counterexampleThreshold (rareSampleSize j) ^ 2 / 2 =
      categoryScale j ^ (6 / 5 : ℝ) / 512 := by
  have hk : 0 ≤ categoryScale j := le_trans (by norm_num) (categoryScale_one_le j)
  rw [counterexampleThreshold_rareSampleSize, div_pow,
    ← Real.rpow_mul_natCast hk (3 / 5) 2]
  norm_num
  ring

theorem rareLogCost_div_threshold_sq_tendsto_zero :
    Tendsto (fun j : ℕ => (5 * categoryScale j * Real.log (categoryScale j)) /
      (counterexampleThreshold (rareSampleSize j) ^ 2 / 2)) atTop (nhds 0) := by
  have hk : Tendsto categoryScale atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)
  have hbase := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).tendsto_div_nhds_zero
  have h := (hbase.comp hk).const_mul (2560 : ℝ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with j
  dsimp only [Function.comp_def]
  have hk0 : 0 < categoryScale j := lt_of_lt_of_le (by norm_num) (categoryScale_one_le j)
  have hp : 0 < categoryScale j ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hk0 _
  rw [counterexampleThreshold_sq_half_rareSampleSize,
    show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, Real.rpow_add hk0, Real.rpow_one]
  field_simp [ne_of_gt hk0, ne_of_gt hp]
  ring

theorem counterexampleThreshold_window (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ counterexampleThreshold n ∧ counterexampleThreshold n < 2 * counterexampleThreshold n := by
  have h := counterexampleThreshold_pos n hn
  constructor <;> linarith

end

end Shao.OQ5.P35
