import Shao.C2.IntervalImageCandidateSpatial
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section
namespace Shao.C2.IntervalImageIntSeries
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial

def spatialImageA (j : ℕ) (a z T y : ℝ) (m : ℤ) : ℝ :=
  iteratedDeriv j (fun w => Real.exp (-imageA a w z (m : ℝ) / T)) y

def spatialImageB (j : ℕ) (a z T y : ℝ) (m : ℤ) : ℝ :=
  iteratedDeriv j (fun w => Real.exp (-imageB a w z (m : ℝ) / T)) y

def imageSeriesSpatial (j : ℕ) (a z T y : ℝ) : ℝ :=
  ∑' m : ℤ, (spatialImageA j a z T y m - spatialImageB j a z T y m)

theorem image_spatial_tails_summable (j : ℕ) (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    Summable (fun n : ℕ => spatialImageA j a z T y ((n : ℤ) + 2)) ∧
      Summable (fun n : ℕ => spatialImageA j a z T y (-((n : ℤ) + 2))) ∧
      Summable (fun n : ℕ => spatialImageB j a z T y ((n : ℤ) + 1)) ∧
      Summable (fun n : ℕ => spatialImageB j a z T y (-((n : ℤ) + 2))) := by
  have hs := (gaussianMajorant_summable a T ha hT).mul_left (spatialPrefactor j a T)
  have hK : 0 ≤ spatialPrefactor j a T := by dsimp only [spatialPrefactor]; positivity
  have hcoef := spatial_prefactor_bound j a T T y z ha hT le_rfl hy hz
  have hterm (n : ℕ) (f : ℝ → ℝ) (C : ℝ)
      (hp : |iteratedDeriv j f y| ≤
        (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
          (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)) * Real.exp (-C / (2 * T)))
      (hC : 8 * (n : ℝ) ^ 2 * a ^ 2 ≤ C) :
      ‖iteratedDeriv j f y‖ ≤ spatialPrefactor j a T * gaussianMajorant a T n := by
    rw [Real.norm_eq_abs]
    exact hp.trans (mul_le_mul hcoef
      (exponent_half_le_majorant a C T T n hT le_rfl hC) (Real.exp_pos _).le hK)
  refine ⟨hs.of_norm_bounded ?_, hs.of_norm_bounded ?_, hs.of_norm_bounded ?_, hs.of_norm_bounded ?_⟩
  · intro n
    exact hterm n _ _ (imageA_spatial_profile j a y z T ((n : ℤ) + 2) ha hy hz hT)
      (tail_exponent_lower_bounds a y z n ha hy hz).1
  · intro n
    exact hterm n _ _ (imageA_spatial_profile j a y z T (-((n : ℤ) + 2)) ha hy hz hT)
      (tail_exponent_lower_bounds a y z n ha hy hz).2.1
  · intro n
    exact hterm n _ _ (imageB_spatial_profile j a y z T ((n : ℤ) + 1) ha hy hz hT)
      (tail_exponent_lower_bounds a y z n ha hy hz).2.2.1
  · intro n
    exact hterm n _ _ (imageB_spatial_profile j a y z T (-((n : ℤ) + 2)) ha hy hz hT)
      (tail_exponent_lower_bounds a y z n ha hy hz).2.2.2

theorem image_spatial_summable (j : ℕ) (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    Summable (spatialImageA j a z T y) ∧ Summable (spatialImageB j a z T y) := by
  obtain ⟨hAp, hAn, hBp, hBn⟩ := image_spatial_tails_summable j a z T y ha hz hT hy
  have hApCast : Summable (fun n : ℕ => spatialImageA j a z T y ((n + 2 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hAp
  have hAnCast : Summable (fun n : ℕ => spatialImageA j a z T y (-(((n + 1 : ℕ) : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hAn
  have hBpCast : Summable (fun n : ℕ => spatialImageB j a z T y ((n + 1 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hBp
  have hBnCast : Summable (fun n : ℕ => spatialImageB j a z T y (-(((n + 1 : ℕ) : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hBn
  have hAP := HasSum.sum_range_add (f := fun n : ℕ => spatialImageA j a z T y (n : ℤ))
    (k := 2) hApCast.hasSum
  have hAN := HasSum.zero_add (f := fun n : ℕ => spatialImageA j a z T y (-((n : ℤ) + 1)))
    hAnCast.hasSum
  have hBP := HasSum.zero_add (f := fun n : ℕ => spatialImageB j a z T y (n : ℤ))
    hBpCast.hasSum
  have hBN := HasSum.zero_add (f := fun n : ℕ => spatialImageB j a z T y (-((n : ℤ) + 1)))
    hBnCast.hasSum
  have hAS := HasSum.of_nat_of_neg_add_one (f := spatialImageA j a z T y) hAP hAN
  have hBS := HasSum.of_nat_of_neg_add_one (f := spatialImageB j a z T y) hBP hBN
  exact ⟨hAS.summable, hBS.summable⟩

theorem imageSeriesSpatial_eq_candidate (j : ℕ) (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    imageSeriesSpatial j a z T y = imageCandidateSpatial j a z T y := by
  obtain ⟨hAp, hAn, hBp, hBn⟩ := image_spatial_tails_summable j a z T y ha hz hT hy
  have hApCast : Summable (fun n : ℕ => spatialImageA j a z T y ((n + 2 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hAp
  have hAnCast : Summable (fun n : ℕ => spatialImageA j a z T y (-(((n + 1 : ℕ) : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hAn
  have hBpCast : Summable (fun n : ℕ => spatialImageB j a z T y ((n + 1 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hBp
  have hBnCast : Summable (fun n : ℕ => spatialImageB j a z T y (-(((n + 1 : ℕ) : ℤ) + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hBn
  have hAP := HasSum.sum_range_add (f := fun n : ℕ => spatialImageA j a z T y (n : ℤ))
    (k := 2) hApCast.hasSum
  have hAN := HasSum.zero_add (f := fun n : ℕ => spatialImageA j a z T y (-((n : ℤ) + 1)))
    hAnCast.hasSum
  have hBP := HasSum.zero_add (f := fun n : ℕ => spatialImageB j a z T y (n : ℤ))
    hBpCast.hasSum
  have hBN := HasSum.zero_add (f := fun n : ℕ => spatialImageB j a z T y (-((n : ℤ) + 1)))
    hBnCast.hasSum
  have hAS := HasSum.of_nat_of_neg_add_one (f := spatialImageA j a z T y) hAP hAN
  have hBS := HasSum.of_nat_of_neg_add_one (f := spatialImageB j a z T y) hBP hBN
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, Nat.cast_one] at hAS hBS
  have htail : spatialTailSum j a z T y =
      (∑' n : ℕ, spatialImageA j a z T y ((n : ℤ) + 2)) +
        (∑' n : ℕ, spatialImageA j a z T y (-((n : ℤ) + 2))) -
        (∑' n : ℕ, spatialImageB j a z T y ((n : ℤ) + 1)) -
        (∑' n : ℕ, spatialImageB j a z T y (-((n : ℤ) + 2))) := by
    change (∑' n : ℕ, (spatialImageA j a z T y ((n : ℤ) + 2) +
      spatialImageA j a z T y (-((n : ℤ) + 2)) -
      spatialImageB j a z T y ((n : ℤ) + 1) -
      spatialImageB j a z T y (-((n : ℤ) + 2)))) = _
    rw [((hAp.add hAn).sub hBp).tsum_sub hBn, (hAp.add hAn).tsum_sub hBp,
      hAp.tsum_add hAn]
  change (∑' m : ℤ, (spatialImageA j a z T y m - spatialImageB j a z T y m)) =
    finiteSpatialImages j a z T y + spatialTailSum j a z T y
  rw [(hAS.sub hBS).tsum_eq, htail]
  have hfinite : finiteSpatialImages j a z T y =
    (spatialImageA j a z T y 0 + spatialImageA j a z T y 1 +
    spatialImageA j a z T y (-1) - spatialImageB j a z T y 0 -
    spatialImageB j a z T y (-1)) := by
    simp only [finiteSpatialImages, spatialImageA, spatialImageB, Int.cast_zero,
      Int.cast_one, Int.cast_neg]
  rw [hfinite]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, add_assoc, one_add_one_eq_two]
  ring

theorem intervalImageCandidate_eq_intSeries (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    intervalImageCandidate a z T y =
      ∑' m : ℤ, (Real.exp (-imageA a y z (m : ℝ) / T) -
        Real.exp (-imageB a y z (m : ℝ) / T)) := by
  have hh := imageSeriesSpatial_eq_candidate 0 a z T y ha hz hT hy
  simpa only [imageSeriesSpatial, spatialImageA, spatialImageB, iteratedDeriv_zero,
    intervalImageCandidate] using hh.symm

theorem intervalImageCandidate_iteratedDeriv_eq_intSeries (j : ℕ) (a z T y : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    iteratedDeriv j (intervalImageCandidate a z T) y =
      ∑' m : ℤ, (iteratedDeriv j (fun w => Real.exp (-imageA a w z (m : ℝ) / T)) y -
        iteratedDeriv j (fun w => Real.exp (-imageB a w z (m : ℝ) / T)) y) := by
  rw [intervalImageCandidate_iteratedDeriv j a z T y ha hz hT hy,
    ← imageSeriesSpatial_eq_candidate j a z T y ha hz hT (le_of_lt hy)]
  rfl

end Shao.C2.IntervalImageIntSeries
