import Shao.C2.IntervalImageSmallTimeSum

noncomputable section
namespace Shao.C2.IntervalImageWallValues
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedConvergence Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageMixedIntSeries Shao.C2.CompletionFirstProfile
open Shao.C2.IntervalImageSmallTimeTails Shao.C2.IntervalImageSmallTimeSum

theorem imageB_lower_wall (a z m : ℝ) :
    imageB a (-a) z m = imageA a (-a) z m := by
  dsimp only [imageA, imageB]
  ring

theorem imageB_upper_wall (a z m : ℝ) :
    imageB a a z m = imageA a a z (m + 1) := by
  dsimp only [imageA, imageB]
  ring

theorem intervalImageCandidate_lower_wall (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    intervalImageCandidate a z T (-a) = 0 := by
  rw [intervalImageCandidate_eq_intSeries a z T (-a) ha hz hT (by simpa [abs_of_pos ha])]
  simp only [imageB_lower_wall, sub_self, tsum_zero]

theorem intervalImageCandidate_upper_wall (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    intervalImageCandidate a z T a = 0 := by
  have hs := image_spatial_summable 0 a z T a ha hz hT (by simp [abs_of_pos ha])
  have hA : Summable (fun m : ℤ => Real.exp (-imageA a a z (m : ℝ) / T)) := by
    have heq : spatialImageA 0 a z T a =
        (fun m : ℤ => Real.exp (-imageA a a z (m : ℝ) / T)) := by
      funext m
      simp only [spatialImageA, iteratedDeriv_zero]
    rw [← heq]
    exact hs.1
  have hB : Summable (fun m : ℤ => Real.exp (-imageB a a z (m : ℝ) / T)) := by
    have heq : spatialImageB 0 a z T a =
        (fun m : ℤ => Real.exp (-imageB a a z (m : ℝ) / T)) := by
      funext m
      simp only [spatialImageB, iteratedDeriv_zero]
    rw [← heq]
    exact hs.2
  let e : ℤ ≃ ℤ := {
    toFun := fun m => m + 1
    invFun := fun m => m - 1
    left_inv := by intro m; dsimp; omega
    right_inv := by intro m; dsimp; omega }
  have he := e.tsum_eq (fun m : ℤ => Real.exp (-imageA a a z (m : ℝ) / T))
  have hAB : (fun m : ℤ => Real.exp (-imageB a a z (m : ℝ) / T)) =
      (fun m : ℤ => Real.exp (-imageA a a z ((m + 1 : ℤ) : ℝ) / T)) := by
    funext m
    push_cast
    rw [imageB_upper_wall]
  rw [intervalImageCandidate_eq_intSeries a z T a ha hz hT (by simp [abs_of_pos ha]),
    hA.tsum_sub hB, hAB]
  change (∑' m : ℤ, Real.exp (-imageA a a z (m : ℝ) / T)) -
    (∑' m : ℤ, Real.exp (-imageA a a z ((e m : ℤ) : ℝ) / T)) = 0
  rw [he, sub_self]

theorem intervalImageCandidate_lower_wall_time_iteratedDeriv (l : ℕ) (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    iteratedDeriv l (fun S => intervalImageCandidate a z S (-a)) T = 0 := by
  have heq : (fun S => intervalImageCandidate a z S (-a)) =ᶠ[𝓝 T] (fun _ : ℝ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
    exact intervalImageCandidate_lower_wall a z S ha hz hS
  rw [Filter.EventuallyEq.iteratedDeriv_eq l heq, iteratedDeriv_const]
  split <;> rfl

theorem intervalImageCandidate_upper_wall_time_iteratedDeriv (l : ℕ) (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    iteratedDeriv l (fun S => intervalImageCandidate a z S a) T = 0 := by
  have heq : (fun S => intervalImageCandidate a z S a) =ᶠ[𝓝 T] (fun _ : ℝ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
    exact intervalImageCandidate_upper_wall a z S ha hz hS
  rw [Filter.EventuallyEq.iteratedDeriv_eq l heq, iteratedDeriv_const]
  split <;> rfl

theorem mixedImageCandidate_lower_wall_zero_spatial (l : ℕ) (a z T : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    mixedImageCandidate 0 l a z T (-a) = 0 := by
  rw [← imageCandidateSpatial_time_iteratedDeriv 0 l a z T (-a) hl ha hz hT
    (by simp [abs_of_pos ha])]
  exact intervalImageCandidate_lower_wall_time_iteratedDeriv l a z T ha hz hT

theorem mixedImageCandidate_upper_wall_zero_spatial (l : ℕ) (a z T : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    mixedImageCandidate 0 l a z T a = 0 := by
  rw [← imageCandidateSpatial_time_iteratedDeriv 0 l a z T a hl ha hz hT
    (by simp [abs_of_pos ha])]
  exact intervalImageCandidate_upper_wall_time_iteratedDeriv l a z T ha hz hT

end Shao.C2.IntervalImageWallValues

