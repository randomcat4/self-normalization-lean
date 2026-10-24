import Shao.C2.IntervalImageHigherTime

noncomputable section
namespace Shao.C2.IntervalImageMixedTerms
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime

def mixedTimeConstant (j l : ℕ) : ℝ :=
  match l with
  | 0 => 1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)
  | 1 => mixedFirstConstant j
  | 2 => mixedSecondConstant j
  | _ => mixedThirdConstant j

theorem mixedTimeConstant_nonneg (j l : ℕ) : 0 ≤ mixedTimeConstant j l := by
  unfold mixedTimeConstant
  split <;> (try dsimp only [mixedFirstConstant, mixedSecondConstant, mixedThirdConstant]) <;> positivity

theorem affineSpatial_time_iterated_hasDerivAt (j l : ℕ) (c k y T : ℝ)
    (hl : l ≤ 2) (hT : 0 < T) :
    HasDerivAt (iteratedDeriv l (fun S => iteratedDeriv j (affineImageTerm c k S) y))
      (iteratedDeriv (l + 1) (fun S => iteratedDeriv j (affineImageTerm c k S) y) T) T := by
  have hcases : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (affineSpatial_time_hasDerivAt j c k y T hT).differentiableAt.hasDerivAt
  · rw [affineSpatial_time_iteratedDeriv_two j c k y T hT]
    have heq : iteratedDeriv 1 (fun S => iteratedDeriv j (affineImageTerm c k S) y) =ᶠ[𝓝 T]
        affineSpatialTimeSlope j c k y := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
      rw [iteratedDeriv_succ, iteratedDeriv_zero]
      exact (affineSpatial_time_hasDerivAt j c k y S hS).deriv
    exact (affineSpatialTimeSlope_hasDerivAt j c k y T hT).congr_of_eventuallyEq heq
  · rw [affineSpatial_time_iteratedDeriv_three j c k y T hT]
    have heq : iteratedDeriv 2 (fun S => iteratedDeriv j (affineImageTerm c k S) y) =ᶠ[𝓝 T]
        affineSpatialTimeSecond j c k y := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
      exact affineSpatial_time_iteratedDeriv_two j c k y S hS
    exact (affineSpatialTimeSecond_hasDerivAt j c k y T hT).congr_of_eventuallyEq heq

theorem spatialImageA_time_iterated_hasDerivAt (j l : ℕ) (a z T y : ℝ) (m : ℤ)
    (hl : l ≤ 2) (hT : 0 < T) :
    HasDerivAt (iteratedDeriv l (fun S => spatialImageA j a z S y m))
      (iteratedDeriv (l + 1) (fun S => spatialImageA j a z S y m) T) T := by
  let c := -4 * (m : ℝ) * a
  let k := 8 * (m : ℝ) ^ 2 * a ^ 2 + 4 * (m : ℝ) * a * z
  have hf (S : ℝ) : (fun w => Real.exp (-imageA a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageA, c, k]
    ring
  have hwhole : (fun S => spatialImageA j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageA, hf]
  rw [hwhole]
  exact affineSpatial_time_iterated_hasDerivAt j l c k y T hl hT

theorem spatialImageB_time_iterated_hasDerivAt (j l : ℕ) (a z T y : ℝ) (m : ℤ)
    (hl : l ≤ 2) (hT : 0 < T) :
    HasDerivAt (iteratedDeriv l (fun S => spatialImageB j a z S y m))
      (iteratedDeriv (l + 1) (fun S => spatialImageB j a z S y m) T) T := by
  let c := 2 * (z + (2 * (m : ℝ) + 1) * a)
  let k := 2 * ((2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a)
  have hf (S : ℝ) : (fun w => Real.exp (-imageB a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageB, c, k]
    ring
  have hwhole : (fun S => spatialImageB j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageB, hf]
  rw [hwhole]
  exact affineSpatial_time_iterated_hasDerivAt j l c k y T hl hT

theorem spatialImageA_mixed_profile (j l : ℕ) (a z T y : ℝ) (m : ℤ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    |iteratedDeriv l (fun S => spatialImageA j a z S y m) T| ≤
      (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j * mixedTimeConstant j l / T ^ l *
        Real.exp (-imageA a y z (m : ℝ) / (2 * T)) := by
  let c := -4 * (m : ℝ) * a
  let k := 8 * (m : ℝ) ^ 2 * a ^ 2 + 4 * (m : ℝ) * a * z
  have hf (S : ℝ) : (fun w => Real.exp (-imageA a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageA, c, k]
    ring
  have hwhole : (fun S => spatialImageA j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageA, hf]
  have heq : c * y + k = imageA a y z (m : ℝ) := by dsimp only [c, k, imageA]; ring
  have hn : 0 ≤ c * y + k := by rw [heq]; exact imageA_nonneg a y z m ha hy hz
  have hi : c * y + k = (c - (z - y)) ^ 2 / 2 - (z - y) ^ 2 / 2 := by
    rw [heq]
    exact imageA_affine_identity a y z (m : ℝ)
  rw [hwhole, ← heq]
  have hcases : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa only [iteratedDeriv_zero, mixedTimeConstant, pow_zero, div_one] using
      affineImageTerm_spatial_profile j c k (z - y) T y hT hn hi
  · rw [iteratedDeriv_succ, iteratedDeriv_zero, (affineSpatial_time_hasDerivAt j c k y T hT).deriv]
    simpa only [mixedTimeConstant, pow_one] using
      affineSpatialTimeSlope_profile j c k (z - y) y T hT hn hi
  · rw [affineSpatial_time_iteratedDeriv_two j c k y T hT]
    simpa only [mixedTimeConstant] using
      affineSpatialTimeSecond_profile j c k (z - y) y T hT hn hi
  · rw [affineSpatial_time_iteratedDeriv_three j c k y T hT]
    simpa only [mixedTimeConstant] using
      affineSpatialTimeThird_profile j c k (z - y) y T hT hn hi

theorem spatialImageB_mixed_profile (j l : ℕ) (a z T y : ℝ) (m : ℤ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    |iteratedDeriv l (fun S => spatialImageB j a z S y m) T| ≤
      (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j * mixedTimeConstant j l / T ^ l *
        Real.exp (-imageB a y z (m : ℝ) / (2 * T)) := by
  let c := 2 * (z + (2 * (m : ℝ) + 1) * a)
  let k := 2 * ((2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a)
  have hf (S : ℝ) : (fun w => Real.exp (-imageB a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageB, c, k]
    ring
  have hwhole : (fun S => spatialImageB j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageB, hf]
  have heq : c * y + k = imageB a y z (m : ℝ) := by dsimp only [c, k, imageB]; ring
  have hn : 0 ≤ c * y + k := by rw [heq]; exact imageB_nonneg a y z m ha hy hz
  have hi : c * y + k = (c - (z - y)) ^ 2 / 2 - (z - y) ^ 2 / 2 := by
    rw [heq]
    exact imageB_affine_identity a y z (m : ℝ)
  rw [hwhole, ← heq]
  have hcases : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa only [iteratedDeriv_zero, mixedTimeConstant, pow_zero, div_one] using
      affineImageTerm_spatial_profile j c k (z - y) T y hT hn hi
  · rw [iteratedDeriv_succ, iteratedDeriv_zero, (affineSpatial_time_hasDerivAt j c k y T hT).deriv]
    simpa only [mixedTimeConstant, pow_one] using
      affineSpatialTimeSlope_profile j c k (z - y) y T hT hn hi
  · rw [affineSpatial_time_iteratedDeriv_two j c k y T hT]
    simpa only [mixedTimeConstant] using
      affineSpatialTimeSecond_profile j c k (z - y) y T hT hn hi
  · rw [affineSpatial_time_iteratedDeriv_three j c k y T hT]
    simpa only [mixedTimeConstant] using
      affineSpatialTimeThird_profile j c k (z - y) y T hT hn hi

end Shao.C2.IntervalImageMixedTerms
