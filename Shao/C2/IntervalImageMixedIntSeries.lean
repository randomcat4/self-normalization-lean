import Shao.C2.IntervalImageMixedCandidate

noncomputable section
namespace Shao.C2.IntervalImageMixedIntSeries
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedConvergence Shao.C2.IntervalImageMixedCandidate

def mixedImageA (j l : ℕ) (a z T y : ℝ) (m : ℤ) : ℝ :=
  iteratedDeriv l (fun S => spatialImageA j a z S y m) T

def mixedImageB (j l : ℕ) (a z T y : ℝ) (m : ℤ) : ℝ :=
  iteratedDeriv l (fun S => spatialImageB j a z S y m) T

def mixedImageSeries (j l : ℕ) (a z T y : ℝ) : ℝ :=
  ∑' m : ℤ, (mixedImageA j l a z T y m - mixedImageB j l a z T y m)

theorem mixed_image_tails_summable (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    Summable (fun n : ℕ => mixedImageA j l a z T y ((n : ℤ) + 2)) ∧
      Summable (fun n : ℕ => mixedImageA j l a z T y (-((n : ℤ) + 2))) ∧
      Summable (fun n : ℕ => mixedImageB j l a z T y ((n : ℤ) + 1)) ∧
      Summable (fun n : ℕ => mixedImageB j l a z T y (-((n : ℤ) + 2))) := by
  have hK : 0 ≤ spatialPrefactor j a T := by dsimp only [spatialPrefactor]; positivity
  have hC := mixedTimeConstant_nonneg j l
  have hs := (gaussianMajorant_summable a T ha hT).mul_left
    (spatialPrefactor j a T * mixedTimeConstant j l / T ^ l)
  have hb := spatial_prefactor_bound j a T T y z ha hT le_rfl hy hz
  have hb0 : (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j ≤
      (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)) := by
    have hh : 0 ≤ (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        (2 : ℝ) ^ j * (Nat.factorial j : ℝ) := by positivity
    nlinarith only [hh]
  have hcoef := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hb0.trans hb) hC) (pow_nonneg hT.le l)
  have hterm (n : ℕ) (f : ℝ → ℝ) (C : ℝ)
      (hp : |iteratedDeriv l f T| ≤
        (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j * mixedTimeConstant j l / T ^ l *
          Real.exp (-C / (2 * T)))
      (hCe : 8 * (n : ℝ) ^ 2 * a ^ 2 ≤ C) :
      ‖iteratedDeriv l f T‖ ≤
        (spatialPrefactor j a T * mixedTimeConstant j l / T ^ l) * gaussianMajorant a T n := by
    rw [Real.norm_eq_abs]
    exact hp.trans (mul_le_mul hcoef (exponent_half_le_majorant a C T T n hT le_rfl hCe)
      (Real.exp_pos _).le (by positivity))
  refine ⟨hs.of_norm_bounded ?_, hs.of_norm_bounded ?_, hs.of_norm_bounded ?_, hs.of_norm_bounded ?_⟩
  · intro n
    exact hterm n _ _ (spatialImageA_mixed_profile j l a z T y ((n : ℤ) + 2) hl ha hz hT hy)
      (tail_exponent_lower_bounds a y z n ha hy hz).1
  · intro n
    exact hterm n _ _ (spatialImageA_mixed_profile j l a z T y (-((n : ℤ) + 2)) hl ha hz hT hy)
      (tail_exponent_lower_bounds a y z n ha hy hz).2.1
  · intro n
    exact hterm n _ _ (spatialImageB_mixed_profile j l a z T y ((n : ℤ) + 1) hl ha hz hT hy)
      (tail_exponent_lower_bounds a y z n ha hy hz).2.2.1
  · intro n
    exact hterm n _ _ (spatialImageB_mixed_profile j l a z T y (-((n : ℤ) + 2)) hl ha hz hT hy)
      (tail_exponent_lower_bounds a y z n ha hy hz).2.2.2

theorem mixed_image_summable (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    Summable (mixedImageA j l a z T y) ∧ Summable (mixedImageB j l a z T y) := by
  obtain ⟨hAp, hAn, hBp, hBn⟩ := mixed_image_tails_summable j l a z T y hl ha hz hT hy
  have hApCast : Summable (fun n : ℕ => mixedImageA j l a z T y ((n + 2 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hAp
  have hAnCast : Summable (fun n : ℕ => mixedImageA j l a z T y (-(((n + 1 : ℕ) : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hAn
  have hBpCast : Summable (fun n : ℕ => mixedImageB j l a z T y ((n + 1 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hBp
  have hBnCast : Summable (fun n : ℕ => mixedImageB j l a z T y (-(((n + 1 : ℕ) : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hBn
  have hAP := HasSum.sum_range_add (f := fun n : ℕ => mixedImageA j l a z T y (n : ℤ))
    (k := 2) hApCast.hasSum
  have hAN := HasSum.zero_add (f := fun n : ℕ => mixedImageA j l a z T y (-((n : ℤ) + 1)))
    hAnCast.hasSum
  have hBP := HasSum.zero_add (f := fun n : ℕ => mixedImageB j l a z T y (n : ℤ))
    hBpCast.hasSum
  have hBN := HasSum.zero_add (f := fun n : ℕ => mixedImageB j l a z T y (-((n : ℤ) + 1)))
    hBnCast.hasSum
  have hAS := HasSum.of_nat_of_neg_add_one (f := mixedImageA j l a z T y) hAP hAN
  have hBS := HasSum.of_nat_of_neg_add_one (f := mixedImageB j l a z T y) hBP hBN
  exact ⟨hAS.summable, hBS.summable⟩

theorem mixedImageSeries_eq_candidate (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    mixedImageSeries j l a z T y = mixedImageCandidate j l a z T y := by
  obtain ⟨hAp, hAn, hBp, hBn⟩ := mixed_image_tails_summable j l a z T y hl ha hz hT hy
  have hApCast : Summable (fun n : ℕ => mixedImageA j l a z T y ((n + 2 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hAp
  have hAnCast : Summable (fun n : ℕ => mixedImageA j l a z T y (-(((n + 1 : ℕ) : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hAn
  have hBpCast : Summable (fun n : ℕ => mixedImageB j l a z T y ((n + 1 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hBp
  have hBnCast : Summable (fun n : ℕ => mixedImageB j l a z T y (-(((n + 1 : ℕ) : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hBn
  have hAP := HasSum.sum_range_add (f := fun n : ℕ => mixedImageA j l a z T y (n : ℤ))
    (k := 2) hApCast.hasSum
  have hAN := HasSum.zero_add (f := fun n : ℕ => mixedImageA j l a z T y (-((n : ℤ) + 1)))
    hAnCast.hasSum
  have hBP := HasSum.zero_add (f := fun n : ℕ => mixedImageB j l a z T y (n : ℤ))
    hBpCast.hasSum
  have hBN := HasSum.zero_add (f := fun n : ℕ => mixedImageB j l a z T y (-((n : ℤ) + 1)))
    hBnCast.hasSum
  have hAS := HasSum.of_nat_of_neg_add_one (f := mixedImageA j l a z T y) hAP hAN
  have hBS := HasSum.of_nat_of_neg_add_one (f := mixedImageB j l a z T y) hBP hBN
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, Nat.cast_one] at hAS hBS
  have htail : mixedTailSum j l a z T y =
      (∑' n : ℕ, mixedImageA j l a z T y ((n : ℤ) + 2)) +
        (∑' n : ℕ, mixedImageA j l a z T y (-((n : ℤ) + 2))) -
        (∑' n : ℕ, mixedImageB j l a z T y ((n : ℤ) + 1)) -
        (∑' n : ℕ, mixedImageB j l a z T y (-((n : ℤ) + 2))) := by
    change (∑' n : ℕ, (mixedImageA j l a z T y ((n : ℤ) + 2) +
      mixedImageA j l a z T y (-((n : ℤ) + 2)) -
      mixedImageB j l a z T y ((n : ℤ) + 1) -
      mixedImageB j l a z T y (-((n : ℤ) + 2)))) = _
    rw [((hAp.add hAn).sub hBp).tsum_sub hBn, (hAp.add hAn).tsum_sub hBp,
      hAp.tsum_add hAn]
  change (∑' m : ℤ, (mixedImageA j l a z T y m - mixedImageB j l a z T y m)) =
    mixedFiniteImages j l a z T y + mixedTailSum j l a z T y
  rw [(hAS.sub hBS).tsum_eq, htail]
  have hfinite : mixedFiniteImages j l a z T y =
    (mixedImageA j l a z T y 0 + mixedImageA j l a z T y 1 +
    mixedImageA j l a z T y (-1) - mixedImageB j l a z T y 0 -
    mixedImageB j l a z T y (-1)) := by
    simp only [mixedFiniteImages, mixedImageA, mixedImageB, Int.cast_zero,
      Int.cast_one, Int.cast_neg]
  rw [hfinite]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, add_assoc, one_add_one_eq_two]
  ring

theorem intervalImageCandidate_mixed_eq_intSeries (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T =
      ∑' m : ℤ, (iteratedDeriv l (fun S => spatialImageA j a z S y m) T -
        iteratedDeriv l (fun S => spatialImageB j a z S y m) T) := by
  rw [intervalImageCandidate_mixed_iteratedDeriv j l a z T y hl ha hz hT hy,
    ← mixedImageSeries_eq_candidate j l a z T y hl ha hz hT (le_of_lt hy)]
  rfl

end Shao.C2.IntervalImageMixedIntSeries
