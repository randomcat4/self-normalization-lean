import Shao.C2.IntervalImageLagrangeRemainder

noncomputable section
namespace Shao.C2.IntervalImageGlobalProfiles
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageMixedTerms Shao.C2.IntervalImageSmallTimeSum
open Shao.C2.IntervalImageTaylorSegment Shao.C2.HalfLineTaylorSegment
open Shao.C2.IntervalImageSineProfiles Shao.C2.IntervalSineHighTimeProfiles
open Shao.C2.CompletionFirstProfile Shao.C2.IntervalGaussianLocal

def globalMixedProfileConstant (j l : ℕ) : ℝ :=
  4 * (4 : ℝ) ^ j * mixedTimeConstant j l + normalizedProfileConstant j l

theorem globalMixedProfileConstant_nonneg (j l : ℕ) :
    0 ≤ globalMixedProfileConstant j l := by
  have hM := mixedTimeConstant_nonneg j l
  have hN := normalizedProfileConstant_nonneg j l
  dsimp only [globalMixedProfileConstant]
  positivity

theorem intervalImageCandidate_sub_one_mixed_iteratedDeriv (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    iteratedDeriv l (fun S => iteratedDeriv j (fun w => intervalImageCandidate a z S w - 1) y) T =
      mixedImageCandidate j l a z T y - (if j = 0 ∧ l = 0 then 1 else 0) := by
  have hshift (n : ℕ) (f : ℝ → ℝ) (x : ℝ) (hn : 0 < n) :
      iteratedDeriv n (fun w => f w - 1) x = iteratedDeriv n f x := by
    have heq : (fun w => f w - 1) = (fun w => (-1 : ℝ) + f w) := by funext w; ring
    rw [heq]
    exact iteratedDeriv_const_add hn (-1 : ℝ)
  by_cases hzero : j + l = 0
  · have hj : j = 0 := by omega
    have hl : l = 0 := by omega
    subst j
    subst l
    have hh := intervalImageCandidate_mixed_iteratedDeriv 0 0 a z T y (by norm_num) ha hz hT hy
    simp only [iteratedDeriv_zero] at hh
    simpa using congrArg (fun q : ℝ => q - 1) hh
  · have hnot : ¬(j = 0 ∧ l = 0) := by omega
    rw [if_neg hnot, sub_zero]
    by_cases hj : j = 0
    · subst j
      have hl : 0 < l := by omega
      change iteratedDeriv l (fun S => intervalImageCandidate a z S y - 1) T = _
      rw [hshift l (fun S => intervalImageCandidate a z S y) T hl]
      simpa only [iteratedDeriv_zero] using
        intervalImageCandidate_mixed_iteratedDeriv 0 l a z T y (by omega) ha hz hT hy
    · have hj' : 0 < j := by omega
      have heq : (fun S => iteratedDeriv j (fun w => intervalImageCandidate a z S w - 1) y) =
          (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) := by
        funext S
        exact hshift j (intervalImageCandidate a z S) y hj'
      rw [heq]
      exact intervalImageCandidate_mixed_iteratedDeriv j l a z T y (by omega) ha hz hT hy

theorem mixedImageCandidate_highTime_profile (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T)
    (hlarge : a ^ 2 ≤ T) (hy : |y| < a) :
    |mixedImageCandidate j l a z T y - (if j = 0 ∧ l = 0 then 1 else 0)| ≤
      normalizedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) *
        (1 + |z - y| / Real.sqrt T) ^ j * intervalProfile a y T z := by
  have h := intervalImageCandidate_sub_one_highTime_profile j l a z T y hjl ha hz hT hlarge hy
  rw [intervalImageCandidate_sub_one_mixed_iteratedDeriv j l a z T y hjl ha hz hT hy] at h
  simpa only [Real.norm_eq_abs] using h

theorem mixedImageCandidate_global_profile (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    |mixedImageCandidate j l a z T y - (if j = 0 ∧ l = 0 then 1 else 0)| ≤
      globalMixedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) *
        (1 + |z - y| / Real.sqrt T) ^ j * intervalProfile a y T z := by
  let R : ℝ := (1 / Real.sqrt T) ^ (j + 2 * l) *
    (1 + |z - y| / Real.sqrt T) ^ j * intervalProfile a y T z
  have hP : 0 ≤ intervalProfile a y T z := by
    dsimp only [intervalProfile, upperProfile, lowerProfile]
    positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  by_cases hSmall : T ≤ a ^ 2
  · have hb := mixedImageCandidate_smallTime_profile j l a z T y (by omega) ha hz hT hy.le hSmall
    have hs := mixed_scale_inv_sqrt j l (z - y) T hT
    have heq : 4 * (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        mixedTimeConstant j l / T ^ l * intervalProfile a y T z =
        (4 * (4 : ℝ) ^ j * mixedTimeConstant j l) * R := by
      calc
        _ = (4 * mixedTimeConstant j l) *
            ((4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j / T ^ l) *
              intervalProfile a y T z := by ring
        _ = _ := by rw [hs]; dsimp only [R]; ring
    have hC : 4 * (4 : ℝ) ^ j * mixedTimeConstant j l ≤ globalMixedProfileConstant j l := by
      dsimp only [globalMixedProfileConstant]
      linarith only [normalizedProfileConstant_nonneg j l]
    calc
      _ ≤ (4 * (4 : ℝ) ^ j * mixedTimeConstant j l) * R := heq ▸ hb
      _ ≤ globalMixedProfileConstant j l * R := mul_le_mul_of_nonneg_right hC hR
      _ = _ := by dsimp only [R]; ring
  · have hb := mixedImageCandidate_highTime_profile j l a z T y hjl ha hz hT (le_of_not_ge hSmall) hy
    have hM : 0 ≤ 4 * (4 : ℝ) ^ j * mixedTimeConstant j l :=
      mul_nonneg (by positivity) (mixedTimeConstant_nonneg j l)
    have hC : normalizedProfileConstant j l ≤ globalMixedProfileConstant j l := by
      dsimp only [globalMixedProfileConstant]
      linarith only [hM]
    calc
      _ ≤ normalizedProfileConstant j l * R := by simpa only [R, mul_assoc] using hb
      _ ≤ globalMixedProfileConstant j l * R := mul_le_mul_of_nonneg_right hC hR
      _ = _ := by dsimp only [R]; ring

theorem mixedImageCandidate_segment_global_profile (j l : ℕ) (a y z T b θ : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| ≤ a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    |mixedImageCandidate j l a z (T - θ * b ^ 2) (y + θ * b) -
        (if j = 0 ∧ l = 0 then 1 else 0)| ≤
      (globalMixedProfileConstant j l * (2 : ℝ) ^ (j + 2 * l) * (3 : ℝ) ^ j) *
        (1 / Real.sqrt T) ^ (j + 2 * l) * (1 + |z - y| / Real.sqrt T) ^ j *
          intervalIncrementProfile a y T z b := by
  have hS := (segment_energy_bounds T b θ hT hsmall hθ0 hθ1.le).1
  have hyS := segment_space_interior a y b θ hy hnew hθ0 hθ1
  have hb := mixedImageCandidate_global_profile j l a z (T - θ * b ^ 2) (y + θ * b)
    hjl ha hz hS hyS
  have ht := interval_segment_profile_transport a y z T b θ (j + 2 * l) j
    hy hz hT hsmall hnew hθ0 hθ1.le
  have hC := globalMixedProfileConstant_nonneg j l
  calc
    _ ≤ globalMixedProfileConstant j l *
        ((1 / Real.sqrt (segmentEnergy T b θ)) ^ (j + 2 * l) *
          (1 + |z - (y + θ * b)| / Real.sqrt (segmentEnergy T b θ)) ^ j *
            intervalProfile a (y + θ * b) (segmentEnergy T b θ) z) := by
      simpa only [segmentEnergy, mul_assoc] using hb
    _ ≤ globalMixedProfileConstant j l *
        ((2 : ℝ) ^ (j + 2 * l) * (3 : ℝ) ^ j * (1 / Real.sqrt T) ^ (j + 2 * l) *
          (1 + |z - y| / Real.sqrt T) ^ j * intervalIncrementProfile a y T z b) :=
      mul_le_mul_of_nonneg_left ht hC
    _ = _ := by ring

end Shao.C2.IntervalImageGlobalProfiles
