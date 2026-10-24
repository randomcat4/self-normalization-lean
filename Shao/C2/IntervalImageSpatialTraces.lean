import Shao.C2.IntervalImageWallValues
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
namespace Shao.C2.IntervalImageSpatialTraces
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageWallValues

theorem spatialTailSum_continuousOn (j : ℕ) (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    ContinuousOn (spatialTailSum j a z T) (Icc (-a) a) := by
  apply continuousOn_tsum (f := fun n y => spatialTailBlock j a z T y n)
    (u := fun n => 4 * spatialPrefactor j a T * gaussianMajorant a T n)
  · intro n y hy
    exact (spatialTailBlock_hasDerivAt j a z T y n).continuousAt.continuousWithinAt
  · exact (gaussianMajorant_summable a T ha hT).mul_left _
  · intro n y hy
    let p : StripPoint a T T := ⟨(y, T), abs_le.2 hy, le_refl T, le_refl T⟩
    exact spatialTailBlock_bound j a z T T n p ha hz hT (le_refl T)

theorem imageCandidateSpatial_continuousOn (j : ℕ) (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    ContinuousOn (imageCandidateSpatial j a z T) (Icc (-a) a) := by
  have hf : ContinuousOn (finiteSpatialImages j a z T) (Icc (-a) a) := by
    intro y hy
    exact (finiteSpatialImages_hasDerivAt j a z T y).continuousAt.continuousWithinAt
  exact hf.add (spatialTailSum_continuousOn j a z T ha hz hT)

theorem intervalImageCandidate_lower_spatial_trace (j : ℕ) (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    Tendsto (iteratedDeriv j (intervalImageCandidate a z T)) (𝓝[Ioo (-a) a] (-a))
      (𝓝 (imageCandidateSpatial j a z T (-a))) := by
  have hx : (-a) ∈ Icc (-a) a := by constructor <;> linarith only [ha]
  have ht := ((imageCandidateSpatial_continuousOn j a z T ha hz hT) (-a) hx).mono
    (show Ioo (-a) a ⊆ Icc (-a) a from fun _ hy => ⟨hy.1.le, hy.2.le⟩)
  have heq : (fun y => imageCandidateSpatial j a z T y) =ᶠ[𝓝[Ioo (-a) a] (-a)]
      iteratedDeriv j (intervalImageCandidate a z T) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (intervalImageCandidate_iteratedDeriv j a z T y ha hz hT (abs_lt.2 hy)).symm
  exact ht.congr' heq

theorem intervalImageCandidate_upper_spatial_trace (j : ℕ) (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    Tendsto (iteratedDeriv j (intervalImageCandidate a z T)) (𝓝[Ioo (-a) a] a)
      (𝓝 (imageCandidateSpatial j a z T a)) := by
  have hx : a ∈ Icc (-a) a := by constructor <;> linarith only [ha]
  have ht := ((imageCandidateSpatial_continuousOn j a z T ha hz hT) a hx).mono
    (show Ioo (-a) a ⊆ Icc (-a) a from fun _ hy => ⟨hy.1.le, hy.2.le⟩)
  have heq : (fun y => imageCandidateSpatial j a z T y) =ᶠ[𝓝[Ioo (-a) a] a]
      iteratedDeriv j (intervalImageCandidate a z T) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (intervalImageCandidate_iteratedDeriv j a z T y ha hz hT (abs_lt.2 hy)).symm
  exact ht.congr' heq

theorem intervalImageCandidate_lower_zero_trace (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    Tendsto (intervalImageCandidate a z T) (𝓝[Ioo (-a) a] (-a)) (𝓝 0) := by
  have hh := intervalImageCandidate_lower_spatial_trace 0 a z T ha hz hT
  change Tendsto (intervalImageCandidate a z T) (𝓝[Ioo (-a) a] (-a))
    (𝓝 (intervalImageCandidate a z T (-a))) at hh
  rw [intervalImageCandidate_lower_wall a z T ha hz hT] at hh
  exact hh

theorem intervalImageCandidate_upper_zero_trace (a z T : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) :
    Tendsto (intervalImageCandidate a z T) (𝓝[Ioo (-a) a] a) (𝓝 0) := by
  have hh := intervalImageCandidate_upper_spatial_trace 0 a z T ha hz hT
  change Tendsto (intervalImageCandidate a z T) (𝓝[Ioo (-a) a] a)
    (𝓝 (intervalImageCandidate a z T a)) at hh
  rw [intervalImageCandidate_upper_wall a z T ha hz hT] at hh
  exact hh

end Shao.C2.IntervalImageSpatialTraces

