import Shao.C2.IntervalImageMixedIntSeries
import Shao.C2.CompletionFirstProfile

noncomputable section
namespace Shao.C2.IntervalImageSmallTimeTails
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedConvergence Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageMixedIntSeries Shao.C2.CompletionFirstProfile

theorem geometric_four_sum_bound :
    Summable (fun n : ℕ => Real.exp (-4) ^ n) ∧ (∑' n : ℕ, Real.exp (-4) ^ n) ≤ 2 := by
  have hE : (2 : ℝ) ≤ Real.exp 4 := by
    have hh := Real.add_one_le_exp (4 : ℝ)
    linarith only [hh]
  have hr : Real.exp (-4) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hE
  have hnorm : ‖Real.exp (-4)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    linarith only [hr]
  refine ⟨(hasSum_geometric_of_norm_lt_one hnorm).summable, ?_⟩
  rw [tsum_geometric_of_norm_lt_one hnorm, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith only [hr] : 0 < 1 - Real.exp (-4))).2
  linarith only [hr]

theorem half_exponent_le_geometric_wall (a C B T : ℝ) (n : ℕ) (hT : 0 < T)
    (hSmall : T ≤ a ^ 2) (hC : B + 8 * (n : ℝ) ^ 2 * a ^ 2 ≤ C) :
    Real.exp (-C / (2 * T)) ≤ Real.exp (-B / (2 * T)) * Real.exp (-4) ^ n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst n
      norm_num
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt h)
      nlinarith only [h1]
  have hcore : (n : ℝ) * T ≤ (n : ℝ) ^ 2 * a ^ 2 :=
    (mul_le_mul_of_nonneg_left hSmall hn).trans
      (mul_le_mul_of_nonneg_right hnsq (sq_nonneg a))
  have hrhs : -B / (2 * T) - 4 * (n : ℝ) = (-B - 8 * (n : ℝ) * T) / (2 * T) := by
    field_simp [ne_of_gt hT] <;> ring
  have he : -C / (2 * T) ≤ -B / (2 * T) - 4 * (n : ℝ) := by
    rw [hrhs]
    exact div_le_div_of_nonneg_right (by nlinarith only [hC, hcore]) (by positivity)
  calc
    _ ≤ Real.exp (-B / (2 * T) - 4 * (n : ℝ)) := Real.exp_le_exp.2 he
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, ← Real.exp_nat_mul]
      congr 2 <;> ring

theorem imageB_zero_half_exp (a y z T : ℝ) (hT : 0 < T) :
    Real.exp (-imageB a y z 0 / (2 * T)) = lowerProfile a y T z := by
  dsimp only [lowerProfile]
  congr 1
  dsimp only [imageB]
  field_simp [ne_of_gt hT] <;> ring

theorem imageB_neg_one_half_exp (a y z T : ℝ) (hT : 0 < T) :
    Real.exp (-imageB a y z (-1) / (2 * T)) = upperProfile a y T z := by
  dsimp only [upperProfile]
  congr 1
  dsimp only [imageB]
  field_simp [ne_of_gt hT] <;> ring

theorem signed_image_half_exp_bounds (a y z T : ℝ) (n : ℕ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) (hT : 0 < T) (hSmall : T ≤ a ^ 2) :
    Real.exp (-imageA a y z ((n : ℤ) + 1 : ℤ) / (2 * T)) ≤ lowerProfile a y T z * Real.exp (-4) ^ n ∧
      Real.exp (-imageA a y z (-((n : ℤ) + 1) : ℤ) / (2 * T)) ≤ upperProfile a y T z * Real.exp (-4) ^ n ∧
      Real.exp (-imageB a y z (n : ℤ) / (2 * T)) ≤ lowerProfile a y T z * Real.exp (-4) ^ n ∧
      Real.exp (-imageB a y z (-((n : ℤ) + 1) : ℤ) / (2 * T)) ≤ upperProfile a y T z * Real.exp (-4) ^ n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx : 0 ≤ 8 * (n : ℝ) * a ^ 2 := by positivity
  have hAp := imageA_positive_tail a y z ((n : ℝ) + 1) ha hy hz (by linarith only [hn])
  have hAn := imageA_negative_tail a y z ((n : ℝ) + 1) ha hy hz (by linarith only [hn])
  have hBp := imageB_positive_tail a y z (n : ℝ) ha hy hz hn
  have hBn := imageB_negative_tail a y z (n : ℝ) ha hy hz hn
  have hAp' : imageB a y z 0 + 8 * (n : ℝ) ^ 2 * a ^ 2 ≤ imageA a y z ((n : ℝ) + 1) := by
    nlinarith only [hAp, hx]
  have hAn' : imageB a y z (-1) + 8 * (n : ℝ) ^ 2 * a ^ 2 ≤ imageA a y z (-((n : ℝ) + 1)) := by
    nlinarith only [hAn, hx]
  have hi : -(n : ℝ) - 1 = -((n : ℝ) + 1) := by ring
  rw [hi] at hBn
  have h1 := half_exponent_le_geometric_wall a _ _ T n hT hSmall hAp'
  have h2 := half_exponent_le_geometric_wall a _ _ T n hT hSmall hAn'
  have h3 := half_exponent_le_geometric_wall a _ _ T n hT hSmall hBp
  have h4 := half_exponent_le_geometric_wall a _ _ T n hT hSmall hBn
  rw [imageB_zero_half_exp a y z T hT] at h1 h3
  rw [imageB_neg_one_half_exp a y z T hT] at h2 h4
  push_cast
  exact ⟨h1, h2, h3, h4⟩

theorem mixedImageA_zero (j l : ℕ) (a z T y : ℝ) :
    mixedImageA j l a z T y 0 = if j = 0 ∧ l = 0 then 1 else 0 := by
  have hwhole : (fun S => spatialImageA j a z S y 0) =
      (fun _ : ℝ => if j = 0 then (1 : ℝ) else 0) := by
    funext S
    have hf : (fun w : ℝ => Real.exp (-imageA a w z ((0 : ℤ) : ℝ) / S)) =
        (fun _ : ℝ => 1) := by
      funext w
      simp only [Int.cast_zero, imageA_zero, neg_zero, zero_div, Real.exp_zero]
    rw [spatialImageA, hf, iteratedDeriv_const]
  rw [mixedImageA, hwhole, iteratedDeriv_const]
  by_cases hj : j = 0 <;> by_cases hl : l = 0 <;> simp [hj, hl]

end Shao.C2.IntervalImageSmallTimeTails
