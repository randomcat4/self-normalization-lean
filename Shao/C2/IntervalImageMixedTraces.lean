import Shao.C2.IntervalImageSpatialTraces
import Mathlib.Tactic.FunProp

noncomputable section
namespace Shao.C2.IntervalImageMixedTraces
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedConvergence Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageMixedIntSeries Shao.C2.IntervalImageWallValues
open Shao.C2.IntervalImageSpatialTraces

theorem affineSpatial_mixed_continuous (j l : ℕ) (c k T : ℝ) (hl : l ≤ 3) (hT : 0 < T) :
    Continuous (fun y => iteratedDeriv l (fun S => iteratedDeriv j (affineImageTerm c k S) y) T) := by
  have hcases : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa only [iteratedDeriv_zero, affineImageTerm_iteratedDeriv] using
      (show Continuous (fun y : ℝ => (-c / T) ^ j * Real.exp (-(c * y + k) / T)) by fun_prop)
  · have he : (fun y => iteratedDeriv 1 (fun S => iteratedDeriv j (affineImageTerm c k S) y) T) =
        (fun y => affineSpatialTimeSlope j c k y T) := by
      funext y
      rw [iteratedDeriv_succ, iteratedDeriv_zero]
      exact (affineSpatial_time_hasDerivAt j c k y T hT).deriv
    rw [he]
    dsimp only [affineSpatialTimeSlope]
    fun_prop
  · have he : (fun y => iteratedDeriv 2 (fun S => iteratedDeriv j (affineImageTerm c k S) y) T) =
        (fun y => affineSpatialTimeSecond j c k y T) := by
      funext y
      exact affineSpatial_time_iteratedDeriv_two j c k y T hT
    rw [he]
    dsimp only [affineSpatialTimeSecond]
    fun_prop
  · have he : (fun y => iteratedDeriv 3 (fun S => iteratedDeriv j (affineImageTerm c k S) y) T) =
        (fun y => affineSpatialTimeThird j c k y T) := by
      funext y
      exact affineSpatial_time_iteratedDeriv_three j c k y T hT
    rw [he]
    dsimp only [affineSpatialTimeThird]
    fun_prop

theorem mixedImageA_continuous (j l : ℕ) (a z T : ℝ) (m : ℤ)
    (hl : l ≤ 3) (hT : 0 < T) :
    Continuous (fun y => mixedImageA j l a z T y m) := by
  let c : ℝ := -4 * (m : ℝ) * a
  let k : ℝ := 8 * (m : ℝ) ^ 2 * a ^ 2 + 4 * (m : ℝ) * a * z
  have hf (S : ℝ) : (fun w => Real.exp (-imageA a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageA, c, k]
    ring
  have hwhole (y : ℝ) : (fun S => spatialImageA j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageA, hf]
  have he : (fun y => mixedImageA j l a z T y m) =
      (fun y => iteratedDeriv l (fun S => iteratedDeriv j (affineImageTerm c k S) y) T) := by
    funext y
    rw [mixedImageA, hwhole]
  rw [he]
  exact affineSpatial_mixed_continuous j l c k T hl hT

theorem mixedImageB_continuous (j l : ℕ) (a z T : ℝ) (m : ℤ)
    (hl : l ≤ 3) (hT : 0 < T) :
    Continuous (fun y => mixedImageB j l a z T y m) := by
  let c : ℝ := 2 * (z + (2 * (m : ℝ) + 1) * a)
  let k : ℝ := 2 * ((2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a)
  have hf (S : ℝ) : (fun w => Real.exp (-imageB a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageB, c, k]
    ring
  have hwhole (y : ℝ) : (fun S => spatialImageB j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageB, hf]
  have he : (fun y => mixedImageB j l a z T y m) =
      (fun y => iteratedDeriv l (fun S => iteratedDeriv j (affineImageTerm c k S) y) T) := by
    funext y
    rw [mixedImageB, hwhole]
  rw [he]
  exact affineSpatial_mixed_continuous j l c k T hl hT

theorem mixedTailBlock_continuous (j l : ℕ) (a z T : ℝ) (n : ℕ)
    (hl : l ≤ 3) (hT : 0 < T) :
    Continuous (fun y => mixedTailBlock j l a z T y n) := by
  change Continuous (fun y => mixedImageA j l a z T y ((n : ℤ) + 2) +
    mixedImageA j l a z T y (-((n : ℤ) + 2)) - mixedImageB j l a z T y ((n : ℤ) + 1) -
    mixedImageB j l a z T y (-((n : ℤ) + 2)))
  exact (((mixedImageA_continuous j l a z T ((n : ℤ) + 2) hl hT).add
    (mixedImageA_continuous j l a z T (-((n : ℤ) + 2)) hl hT)).sub
    (mixedImageB_continuous j l a z T ((n : ℤ) + 1) hl hT)).sub
    (mixedImageB_continuous j l a z T (-((n : ℤ) + 2)) hl hT)

theorem mixedTailSum_continuousOn (j l : ℕ) (a z T : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    ContinuousOn (mixedTailSum j l a z T) (Icc (-a) a) := by
  apply continuousOn_tsum (f := fun n y => mixedTailBlock j l a z T y n)
    (u := fun n => (4 * spatialPrefactor j a T * mixedTimeConstant j l / T ^ l) *
      gaussianMajorant a T n)
  · intro n
    exact (mixedTailBlock_continuous j l a z T n hl hT).continuousOn
  · exact (gaussianMajorant_summable a T ha hT).mul_left _
  · intro n y hy
    let p : StripPoint a T T := ⟨(y, T), abs_le.2 hy, le_refl T, le_refl T⟩
    exact mixedTailBlock_bound j l a z T T n p hl ha hz hT (le_refl T)

theorem mixedFiniteImages_continuous (j l : ℕ) (a z T : ℝ)
    (hl : l ≤ 3) (hT : 0 < T) :
    Continuous (mixedFiniteImages j l a z T) := by
  change Continuous (fun y => mixedImageA j l a z T y 0 + mixedImageA j l a z T y 1 +
    mixedImageA j l a z T y (-1) - mixedImageB j l a z T y 0 - mixedImageB j l a z T y (-1))
  exact ((((mixedImageA_continuous j l a z T 0 hl hT).add
    (mixedImageA_continuous j l a z T 1 hl hT)).add
    (mixedImageA_continuous j l a z T (-1) hl hT)).sub
    (mixedImageB_continuous j l a z T 0 hl hT)).sub
    (mixedImageB_continuous j l a z T (-1) hl hT)

theorem mixedImageCandidate_continuousOn (j l : ℕ) (a z T : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    ContinuousOn (mixedImageCandidate j l a z T) (Icc (-a) a) := by
  exact (mixedFiniteImages_continuous j l a z T hl hT).continuousOn.add
    (mixedTailSum_continuousOn j l a z T hl ha hz hT)

theorem intervalImageCandidate_lower_mixed_trace (j l : ℕ) (a z T : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    Tendsto (fun y => iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T)
      (𝓝[Ioo (-a) a] (-a)) (𝓝 (mixedImageCandidate j l a z T (-a))) := by
  have hx : (-a) ∈ Icc (-a) a := by constructor <;> linarith only [ha]
  have ht := ((mixedImageCandidate_continuousOn j l a z T hl ha hz hT) (-a) hx).mono
    (show Ioo (-a) a ⊆ Icc (-a) a from fun _ hy => ⟨hy.1.le, hy.2.le⟩)
  have heq : (fun y => mixedImageCandidate j l a z T y) =ᶠ[𝓝[Ioo (-a) a] (-a)]
      (fun y => iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (intervalImageCandidate_mixed_iteratedDeriv j l a z T y hl ha hz hT (abs_lt.2 hy)).symm
  exact ht.congr' heq

theorem intervalImageCandidate_upper_mixed_trace (j l : ℕ) (a z T : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    Tendsto (fun y => iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T)
      (𝓝[Ioo (-a) a] a) (𝓝 (mixedImageCandidate j l a z T a)) := by
  have hx : a ∈ Icc (-a) a := by constructor <;> linarith only [ha]
  have ht := ((mixedImageCandidate_continuousOn j l a z T hl ha hz hT) a hx).mono
    (show Ioo (-a) a ⊆ Icc (-a) a from fun _ hy => ⟨hy.1.le, hy.2.le⟩)
  have heq : (fun y => mixedImageCandidate j l a z T y) =ᶠ[𝓝[Ioo (-a) a] a]
      (fun y => iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (intervalImageCandidate_mixed_iteratedDeriv j l a z T y hl ha hz hT (abs_lt.2 hy)).symm
  exact ht.congr' heq

theorem intervalImageCandidate_lower_time_zero_trace (l : ℕ) (a z T : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    Tendsto (fun y => iteratedDeriv l (fun S => intervalImageCandidate a z S y) T)
      (𝓝[Ioo (-a) a] (-a)) (𝓝 0) := by
  have hh := intervalImageCandidate_lower_mixed_trace 0 l a z T hl ha hz hT
  simp only [iteratedDeriv_zero] at hh
  rw [mixedImageCandidate_lower_wall_zero_spatial l a z T hl ha hz hT] at hh
  exact hh

theorem intervalImageCandidate_upper_time_zero_trace (l : ℕ) (a z T : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    Tendsto (fun y => iteratedDeriv l (fun S => intervalImageCandidate a z S y) T)
      (𝓝[Ioo (-a) a] a) (𝓝 0) := by
  have hh := intervalImageCandidate_upper_mixed_trace 0 l a z T hl ha hz hT
  simp only [iteratedDeriv_zero] at hh
  rw [mixedImageCandidate_upper_wall_zero_spatial l a z T hl ha hz hT] at hh
  exact hh

end Shao.C2.IntervalImageMixedTraces

