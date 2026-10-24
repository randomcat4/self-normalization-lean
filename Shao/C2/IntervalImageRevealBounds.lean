import Shao.C2.IntervalImageGlobalProfiles
import Shao.C2.HalfLineSmallTaylor

noncomputable section
namespace Shao.C2.IntervalImageRevealBounds
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageRevealDerivatives Shao.C2.IntervalImageLagrangeRemainder
open Shao.C2.IntervalImageGlobalProfiles Shao.C2.IntervalGaussianLocal
open Shao.C2.HalfLineSmallTaylor Shao.C2.HalfLineTaylorSegment

def segmentMixedProfileConstant (j l : ℕ) : ℝ :=
  globalMixedProfileConstant j l * (2 : ℝ) ^ (j + 2 * l) * (3 : ℝ) ^ j

def thirdPathProfileConstant : ℝ :=
  segmentMixedProfileConstant 3 0 + 3 * segmentMixedProfileConstant 2 1 +
    3 * segmentMixedProfileConstant 1 2 + segmentMixedProfileConstant 0 3

def compensatedProfileConstant : ℝ :=
  thirdPathProfileConstant / 6 + segmentMixedProfileConstant 1 1 +
    segmentMixedProfileConstant 0 2 / 2

theorem segmentMixedProfileConstant_nonneg (j l : ℕ) :
    0 ≤ segmentMixedProfileConstant j l := by
  dsimp only [segmentMixedProfileConstant]
  exact mul_nonneg (mul_nonneg (globalMixedProfileConstant_nonneg j l) (by positivity)) (by positivity)

theorem thirdPathProfileConstant_nonneg : 0 ≤ thirdPathProfileConstant := by
  have h30 := segmentMixedProfileConstant_nonneg 3 0
  have h21 := segmentMixedProfileConstant_nonneg 2 1
  have h12 := segmentMixedProfileConstant_nonneg 1 2
  have h03 := segmentMixedProfileConstant_nonneg 0 3
  dsimp only [thirdPathProfileConstant]
  positivity

theorem compensatedProfileConstant_nonneg : 0 ≤ compensatedProfileConstant := by
  have h3 := thirdPathProfileConstant_nonneg
  have h11 := segmentMixedProfileConstant_nonneg 1 1
  have h02 := segmentMixedProfileConstant_nonneg 0 2
  dsimp only [compensatedProfileConstant]
  positivity

theorem weighted_segment_mixed_bound (j l : ℕ) (a y z T b θ : ℝ)
    (hjl : j + l ≤ 3) (horder : 3 ≤ j + 2 * l)
    (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| ≤ a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    |b| ^ (j + 2 * l) * |mixedImageCandidate j l a z (T - θ * b ^ 2) (y + θ * b)| ≤
      segmentMixedProfileConstant j l * (|b| / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 * intervalIncrementProfile a y T z b := by
  let q : ℝ := |b| / Real.sqrt T
  let D : ℝ := 1 + |z - y| / Real.sqrt T
  let P : ℝ := intervalIncrementProfile a y T z b
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hs2 : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
  have hbs : |b| ≤ Real.sqrt T := by
    nlinarith [sq_abs b, abs_nonneg b, Real.sqrt_nonneg T]
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hs).2 hbs
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith only [div_nonneg (abs_nonneg (z - y)) hs.le]
  have hP : 0 ≤ P := by
    dsimp only [P, intervalIncrementProfile, incrementProfile]
    positivity
  have hnot : ¬(j = 0 ∧ l = 0) := by omega
  have hb : |mixedImageCandidate j l a z (T - θ * b ^ 2) (y + θ * b)| ≤
      segmentMixedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) * D ^ j * P := by
    simpa only [if_neg hnot, sub_zero, segmentMixedProfileConstant, D, P] using
      mixedImageCandidate_segment_global_profile j l a y z T b θ hjl ha hy hz hT hsmall hnew hθ0 hθ1
  have hd := normalized_power_domination q D hq0 hq1 hD (j + 2 * l - 3) j (by omega)
  have hr : 3 + (j + 2 * l - 3) = j + 2 * l := by omega
  rw [hr] at hd
  have hqeq : |b| ^ (j + 2 * l) * (1 / Real.sqrt T) ^ (j + 2 * l) = q ^ (j + 2 * l) := by
    dsimp only [q]
    simp only [div_pow, one_pow]
    ring
  have hC := segmentMixedProfileConstant_nonneg j l
  calc
    _ ≤ |b| ^ (j + 2 * l) *
        (segmentMixedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) * D ^ j * P) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg b) _)
    _ = segmentMixedProfileConstant j l * (q ^ (j + 2 * l) * D ^ j) * P := by
      rw [← hqeq]
      ring
    _ ≤ segmentMixedProfileConstant j l * (q ^ 3 * D ^ 3) * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hC) hP
    _ = _ := by dsimp only [q, D, P]; ring

theorem pathThird_segment_profile (a y z T b θ : ℝ)
    (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| ≤ a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    |pathThird a z T y b θ| ≤
      thirdPathProfileConstant * (|b| / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 * intervalIncrementProfile a y T z b := by
  let R : ℝ := (|b| / Real.sqrt T) ^ 3 *
    (1 + |z - y| / Real.sqrt T) ^ 3 * intervalIncrementProfile a y T z b
  let A := b ^ 3 * mixedImageCandidate 3 0 a z (T - θ * b ^ 2) (y + θ * b)
  let B := 3 * b ^ 4 * mixedImageCandidate 2 1 a z (T - θ * b ^ 2) (y + θ * b)
  let C := 3 * b ^ 5 * mixedImageCandidate 1 2 a z (T - θ * b ^ 2) (y + θ * b)
  let F := b ^ 6 * mixedImageCandidate 0 3 a z (T - θ * b ^ 2) (y + θ * b)
  have h30 : |b| ^ 3 * |mixedImageCandidate 3 0 a z (T - θ * b ^ 2) (y + θ * b)| ≤
      segmentMixedProfileConstant 3 0 * R := by
    simpa only [R, mul_assoc] using
      weighted_segment_mixed_bound 3 0 a y z T b θ (by norm_num) (by norm_num) ha hy hz hT hsmall hnew hθ0 hθ1
  have h21 : |b| ^ 4 * |mixedImageCandidate 2 1 a z (T - θ * b ^ 2) (y + θ * b)| ≤
      segmentMixedProfileConstant 2 1 * R := by
    simpa only [R, mul_assoc] using
      weighted_segment_mixed_bound 2 1 a y z T b θ (by norm_num) (by norm_num) ha hy hz hT hsmall hnew hθ0 hθ1
  have h12 : |b| ^ 5 * |mixedImageCandidate 1 2 a z (T - θ * b ^ 2) (y + θ * b)| ≤
      segmentMixedProfileConstant 1 2 * R := by
    simpa only [R, mul_assoc] using
      weighted_segment_mixed_bound 1 2 a y z T b θ (by norm_num) (by norm_num) ha hy hz hT hsmall hnew hθ0 hθ1
  have h03 : |b| ^ 6 * |mixedImageCandidate 0 3 a z (T - θ * b ^ 2) (y + θ * b)| ≤
      segmentMixedProfileConstant 0 3 * R := by
    simpa only [R, mul_assoc] using
      weighted_segment_mixed_bound 0 3 a y z T b θ (by norm_num) (by norm_num) ha hy hz hT hsmall hnew hθ0 hθ1
  have hA : |A| ≤ segmentMixedProfileConstant 3 0 * R := by
    simpa only [A, abs_mul, abs_pow] using h30
  have hB : |B| ≤ 3 * segmentMixedProfileConstant 2 1 * R := by
    calc
      _ = 3 * (|b| ^ 4 * |mixedImageCandidate 2 1 a z (T - θ * b ^ 2) (y + θ * b)|) := by
        dsimp only [B]
        simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
        ring
      _ ≤ 3 * (segmentMixedProfileConstant 2 1 * R) := mul_le_mul_of_nonneg_left h21 (by norm_num)
      _ = _ := by ring
  have hC : |C| ≤ 3 * segmentMixedProfileConstant 1 2 * R := by
    calc
      _ = 3 * (|b| ^ 5 * |mixedImageCandidate 1 2 a z (T - θ * b ^ 2) (y + θ * b)|) := by
        dsimp only [C]
        simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
        ring
      _ ≤ 3 * (segmentMixedProfileConstant 1 2 * R) := mul_le_mul_of_nonneg_left h12 (by norm_num)
      _ = _ := by ring
  have hF : |F| ≤ segmentMixedProfileConstant 0 3 * R := by
    simpa only [F, abs_mul, abs_pow] using h03
  have hab : |A - B| ≤ |A| + |B| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le A (-B)
  have habc := abs_add_le (A - B) C
  have habcf : |A - B + C - F| ≤ |A - B + C| + |F| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (A - B + C) (-F)
  have htri : |A - B + C - F| ≤ |A| + |B| + |C| + |F| := by
    linarith only [hab, habc, habcf]
  have hfinal : |A - B + C - F| ≤ thirdPathProfileConstant * R := by
    dsimp only [thirdPathProfileConstant]
    linarith only [htri, hA, hB, hC, hF]
  simpa only [pathThird, A, B, C, F, R, mul_assoc] using hfinal

theorem intervalImageCandidate_compensated_small_step_bound (a y z T b : ℝ)
    (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| < a) :
    |intervalImageCandidate a z (T - b ^ 2) (y + b) - intervalImageCandidate a z T y -
        (b - b ^ 2 * (z - y) / T) * deriv (intervalImageCandidate a z T) y| ≤
      compensatedProfileConstant * (|b| / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 * intervalIncrementProfile a y T z b := by
  obtain ⟨θ, hθ, heq⟩ := compensated_lagrange_remainder a z T y b ha hz hT hy hsmall hnew
  let R : ℝ := (|b| / Real.sqrt T) ^ 3 *
    (1 + |z - y| / Real.sqrt T) ^ 3 * intervalIncrementProfile a y T z b
  let A := (1 / 6 : ℝ) * pathThird a z T y b θ
  let B := b ^ 3 * mixedImageCandidate 1 1 a z T y
  let C := (1 / 2 : ℝ) * (b ^ 4 * mixedImageCandidate 0 2 a z T y)
  have h3 : |pathThird a z T y b θ| ≤ thirdPathProfileConstant * R := by
    simpa only [R, mul_assoc] using
      pathThird_segment_profile a y z T b θ ha hy hz hT hsmall hnew.le hθ.1.le hθ.2
  have hA : |A| ≤ thirdPathProfileConstant / 6 * R := by
    calc
      _ = (1 / 6 : ℝ) * |pathThird a z T y b θ| := by dsimp only [A]; rw [abs_mul]; norm_num
      _ ≤ (1 / 6 : ℝ) * (thirdPathProfileConstant * R) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = _ := by ring
  have hB : |B| ≤ segmentMixedProfileConstant 1 1 * R := by
    simpa only [B, abs_mul, abs_pow, zero_mul, sub_zero, add_zero, R, mul_assoc] using
      weighted_segment_mixed_bound 1 1 a y z T b 0 (by norm_num) (by norm_num) ha hy hz hT hsmall hnew.le (by norm_num) (by norm_num)
  have h02 : |b ^ 4 * mixedImageCandidate 0 2 a z T y| ≤ segmentMixedProfileConstant 0 2 * R := by
    simpa only [abs_mul, abs_pow, zero_mul, sub_zero, add_zero, R, mul_assoc] using
      weighted_segment_mixed_bound 0 2 a y z T b 0 (by norm_num) (by norm_num) ha hy hz hT hsmall hnew.le (by norm_num) (by norm_num)
  have hC : |C| ≤ segmentMixedProfileConstant 0 2 / 2 * R := by
    calc
      _ = (1 / 2 : ℝ) * |b ^ 4 * mixedImageCandidate 0 2 a z T y| := by dsimp only [C]; rw [abs_mul]; norm_num
      _ ≤ (1 / 2 : ℝ) * (segmentMixedProfileConstant 0 2 * R) := mul_le_mul_of_nonneg_left h02 (by norm_num)
      _ = _ := by ring
  have hab : |A - B| ≤ |A| + |B| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le A (-B)
  have habc := abs_add_le (A - B) C
  have hfinal : |A - B + C| ≤ compensatedProfileConstant * R := by
    dsimp only [compensatedProfileConstant]
    linarith only [hab, habc, hA, hB, hC]
  rw [heq]
  simpa only [A, B, C, R, mul_assoc] using hfinal

end Shao.C2.IntervalImageRevealBounds
