import Shao.C2.IntervalImageSmallTimeTails

noncomputable section
namespace Shao.C2.IntervalImageSmallTimeSum
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedConvergence Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageMixedIntSeries Shao.C2.CompletionFirstProfile
open Shao.C2.IntervalImageSmallTimeTails

def smallTimeMixedBlock (j l : ℕ) (a z T y : ℝ) (n : ℕ) : ℝ :=
  mixedImageA j l a z T y ((n : ℤ) + 1) +
    mixedImageA j l a z T y (-((n : ℤ) + 1)) -
    mixedImageB j l a z T y (n : ℤ) -
    mixedImageB j l a z T y (-((n : ℤ) + 1))

theorem smallTimeMixedBlock_bound (j l : ℕ) (a z T y : ℝ) (n : ℕ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a)
    (hSmall : T ≤ a ^ 2) :
    ‖smallTimeMixedBlock j l a z T y n‖ ≤
      (2 * (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        mixedTimeConstant j l / T ^ l * intervalProfile a y T z) * Real.exp (-4) ^ n := by
  let K : ℝ := (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
    mixedTimeConstant j l / T ^ l
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact div_nonneg (mul_nonneg (by positivity) (mixedTimeConstant_nonneg j l)) (by positivity)
  rcases signed_image_half_exp_bounds a y z T n ha hy hz hT hSmall with ⟨hAp, hAn, hBp, hBn⟩
  have h1 : |mixedImageA j l a z T y ((n : ℤ) + 1)| ≤
      K * (lowerProfile a y T z * Real.exp (-4) ^ n) :=
    (spatialImageA_mixed_profile j l a z T y ((n : ℤ) + 1) hl ha hz hT hy).trans
      (mul_le_mul_of_nonneg_left hAp hK)
  have h2 : |mixedImageA j l a z T y (-((n : ℤ) + 1))| ≤
      K * (upperProfile a y T z * Real.exp (-4) ^ n) :=
    (spatialImageA_mixed_profile j l a z T y (-((n : ℤ) + 1)) hl ha hz hT hy).trans
      (mul_le_mul_of_nonneg_left hAn hK)
  have h3 : |mixedImageB j l a z T y (n : ℤ)| ≤
      K * (lowerProfile a y T z * Real.exp (-4) ^ n) :=
    (spatialImageB_mixed_profile j l a z T y (n : ℤ) hl ha hz hT hy).trans
      (mul_le_mul_of_nonneg_left hBp hK)
  have h4 : |mixedImageB j l a z T y (-((n : ℤ) + 1))| ≤
      K * (upperProfile a y T z * Real.exp (-4) ^ n) :=
    (spatialImageB_mixed_profile j l a z T y (-((n : ℤ) + 1)) hl ha hz hT hy).trans
      (mul_le_mul_of_nonneg_left hBn hK)
  have ht1 := norm_add_le (mixedImageA j l a z T y ((n : ℤ) + 1))
    (mixedImageA j l a z T y (-((n : ℤ) + 1)))
  have ht2 := norm_sub_le (mixedImageA j l a z T y ((n : ℤ) + 1) +
    mixedImageA j l a z T y (-((n : ℤ) + 1))) (mixedImageB j l a z T y (n : ℤ))
  have ht3 := norm_sub_le (mixedImageA j l a z T y ((n : ℤ) + 1) +
    mixedImageA j l a z T y (-((n : ℤ) + 1)) - mixedImageB j l a z T y (n : ℤ))
    (mixedImageB j l a z T y (-((n : ℤ) + 1)))
  simp only [Real.norm_eq_abs] at ht1 ht2 ht3
  have he : (2 * (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
      mixedTimeConstant j l / T ^ l * intervalProfile a y T z) * Real.exp (-4) ^ n =
      K * (lowerProfile a y T z * Real.exp (-4) ^ n) +
      K * (upperProfile a y T z * Real.exp (-4) ^ n) +
      K * (lowerProfile a y T z * Real.exp (-4) ^ n) +
      K * (upperProfile a y T z * Real.exp (-4) ^ n) := by
    dsimp only [K, intervalProfile]
    ring
  rw [he, Real.norm_eq_abs]
  dsimp only [smallTimeMixedBlock]
  linarith only [ht1, ht2, ht3, h1, h2, h3, h4]

theorem smallTimeMixedBlock_summable (j l : ℕ) (a z T y : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a)
    (hSmall : T ≤ a ^ 2) :
    Summable (smallTimeMixedBlock j l a z T y) := by
  exact (geometric_four_sum_bound.1.mul_left _).of_norm_bounded
    (fun n => smallTimeMixedBlock_bound j l a z T y n hl ha hz hT hy hSmall)

theorem smallTimeMixedBlock_tsum_eq (j l : ℕ) (a z T y : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    (∑' n : ℕ, smallTimeMixedBlock j l a z T y n) =
      mixedImageCandidate j l a z T y - (if j = 0 ∧ l = 0 then 1 else 0) := by
  let p : StripPoint a T T := ⟨(y, T), hy, le_refl T, le_refl T⟩
  have ht := mixedTailBlock_summable j l a z T T p hl ha hz hT (le_refl T)
  have hs : HasSum (fun n : ℕ => smallTimeMixedBlock j l a z T y (n + 1))
      (mixedTailSum j l a z T y) := by
    simpa only [smallTimeMixedBlock, mixedImageA, mixedImageB, mixedTailBlock,
      mixedTailSum, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using ht.hasSum
  have hw := HasSum.zero_add (f := smallTimeMixedBlock j l a z T y) hs
  rw [hw.tsum_eq]
  have hh : smallTimeMixedBlock j l a z T y 0 =
      mixedFiniteImages j l a z T y - mixedImageA j l a z T y 0 := by
    simp only [smallTimeMixedBlock, mixedFiniteImages, mixedImageA, mixedImageB,
      Nat.cast_zero, zero_add]
    ring
  rw [hh, mixedImageA_zero]
  dsimp only [mixedImageCandidate]
  ring

theorem mixedImageCandidate_smallTime_profile (j l : ℕ) (a z T y : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a)
    (hSmall : T ≤ a ^ 2) :
    |mixedImageCandidate j l a z T y - (if j = 0 ∧ l = 0 then 1 else 0)| ≤
      4 * (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        mixedTimeConstant j l / T ^ l * intervalProfile a y T z := by
  let C : ℝ := 2 * (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
    mixedTimeConstant j l / T ^ l * intervalProfile a y T z
  have hC : 0 ≤ C := by
    dsimp only [C, intervalProfile, upperProfile, lowerProfile]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by positivity) (mixedTimeConstant_nonneg j l)) (by positivity))
      (by positivity)
  have hg := geometric_four_sum_bound.1.mul_left C
  have hb : ∀ n : ℕ, ‖smallTimeMixedBlock j l a z T y n‖ ≤ C * Real.exp (-4) ^ n :=
    fun n => smallTimeMixedBlock_bound j l a z T y n hl ha hz hT hy hSmall
  have hsum : ‖∑' n : ℕ, smallTimeMixedBlock j l a z T y n‖ ≤
      C * (∑' n : ℕ, Real.exp (-4) ^ n) := by
    exact (hg.of_norm_bounded hb).hasSum.norm_le_of_bounded
      ((geometric_four_sum_bound.1.hasSum).mul_left C) hb
  rw [smallTimeMixedBlock_tsum_eq j l a z T y hl ha hz hT hy, Real.norm_eq_abs] at hsum
  calc
    _ ≤ C * (∑' n : ℕ, Real.exp (-4) ^ n) := hsum
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left geometric_four_sum_bound.2 hC
    _ = _ := by dsimp only [C]; ring

theorem intervalImageCandidate_mixed_smallTime_profile (j l : ℕ) (a z T y : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a)
    (hSmall : T ≤ a ^ 2) :
    |iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T -
      (if j = 0 ∧ l = 0 then 1 else 0)| ≤
      4 * (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        mixedTimeConstant j l / T ^ l * intervalProfile a y T z := by
  rw [intervalImageCandidate_mixed_iteratedDeriv j l a z T y hl ha hz hT hy]
  exact mixedImageCandidate_smallTime_profile j l a z T y hl ha hz hT hy.le hSmall

theorem intervalImageCandidate_nonzero_mixed_smallTime_profile (j l : ℕ) (a z T y : ℝ)
    (hl : l ≤ 3) (hjl : 0 < j + l) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T)
    (hy : |y| < a) (hSmall : T ≤ a ^ 2) :
    |iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T| ≤
      4 * (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        mixedTimeConstant j l / T ^ l * intervalProfile a y T z := by
  have hh : ¬(j = 0 ∧ l = 0) := by omega
  simpa only [if_neg hh, sub_zero] using
    intervalImageCandidate_mixed_smallTime_profile j l a z T y hl ha hz hT hy hSmall

theorem intervalImageCandidate_sub_one_smallTime_profile (a z T y : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a)
    (hSmall : T ≤ a ^ 2) :
    |intervalImageCandidate a z T y - 1| ≤ 8 * intervalProfile a y T z := by
  have hh := mixedImageCandidate_smallTime_profile 0 0 a z T y (by omega) ha hz hT hy hSmall
  rw [mixedImageCandidate_zero] at hh
  norm_num [mixedTimeConstant] at hh
  exact hh

end Shao.C2.IntervalImageSmallTimeSum

