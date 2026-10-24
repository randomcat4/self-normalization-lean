import Shao.C2.IntervalImageMixedConvergence

noncomputable section
namespace Shao.C2.IntervalImageMixedCandidate
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedConvergence

def mixedFiniteImages (j l : ℕ) (a z T y : ℝ) : ℝ :=
  iteratedDeriv l (fun S => spatialImageA j a z S y 0) T +
    iteratedDeriv l (fun S => spatialImageA j a z S y 1) T +
    iteratedDeriv l (fun S => spatialImageA j a z S y (-1)) T -
    iteratedDeriv l (fun S => spatialImageB j a z S y 0) T -
    iteratedDeriv l (fun S => spatialImageB j a z S y (-1)) T

def mixedImageCandidate (j l : ℕ) (a z T y : ℝ) : ℝ :=
  mixedFiniteImages j l a z T y + mixedTailSum j l a z T y

theorem mixedFiniteImages_zero (j : ℕ) (a z T y : ℝ) :
    mixedFiniteImages j 0 a z T y = finiteSpatialImages j a z T y := by
  simp only [mixedFiniteImages, iteratedDeriv_zero, spatialImageA, spatialImageB,
    Int.cast_zero, Int.cast_one, Int.cast_neg, finiteSpatialImages]

theorem mixedFiniteImages_time_hasDerivAt (j l : ℕ) (a z T y : ℝ)
    (hl : l ≤ 2) (hT : 0 < T) :
    HasDerivAt (fun S => mixedFiniteImages j l a z S y)
      (mixedFiniteImages j (l + 1) a z T y) T := by
  exact ((((spatialImageA_time_iterated_hasDerivAt j l a z T y 0 hl hT).add
    (spatialImageA_time_iterated_hasDerivAt j l a z T y 1 hl hT)).add
    (spatialImageA_time_iterated_hasDerivAt j l a z T y (-1) hl hT)).sub
    (spatialImageB_time_iterated_hasDerivAt j l a z T y 0 hl hT)).sub
    (spatialImageB_time_iterated_hasDerivAt j l a z T y (-1) hl hT)

theorem mixedImageCandidate_zero (j : ℕ) (a z T y : ℝ) :
    mixedImageCandidate j 0 a z T y = imageCandidateSpatial j a z T y := by
  simp only [mixedImageCandidate, mixedFiniteImages_zero, mixedTailSum_zero, imageCandidateSpatial]

theorem mixedImageCandidate_time_hasDerivAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 2)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    HasDerivAt (fun S => mixedImageCandidate j l a z S y)
      (mixedImageCandidate j (l + 1) a z T y) T := by
  exact (mixedFiniteImages_time_hasDerivAt j l a z T y hl hT).add
    (mixedTailSum_time_hasDerivAt j l a z T y hl ha hz hT hy)

theorem imageCandidateSpatial_time_iteratedDeriv (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    iteratedDeriv l (fun S => imageCandidateSpatial j a z S y) T =
      mixedImageCandidate j l a z T y := by
  induction l generalizing T with
  | zero =>
    simpa only [iteratedDeriv_zero] using (mixedImageCandidate_zero j a z T y).symm
  | succ l ih =>
    have hl2 : l ≤ 2 := by omega
    have heq : iteratedDeriv l (fun S => imageCandidateSpatial j a z S y) =ᶠ[𝓝 T]
        (fun S => mixedImageCandidate j l a z S y) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
      exact ih S (by omega) hS
    rw [iteratedDeriv_succ]
    exact heq.deriv_eq.trans (mixedImageCandidate_time_hasDerivAt j l a z T y hl2 ha hz hT hy).deriv

theorem intervalImageCandidate_mixed_iteratedDeriv (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T =
      mixedImageCandidate j l a z T y := by
  have heq : (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) =ᶠ[𝓝 T]
      (fun S => imageCandidateSpatial j a z S y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
    exact intervalImageCandidate_iteratedDeriv j a z S y ha hz hS hy
  exact (Filter.EventuallyEq.iteratedDeriv_eq l heq).trans
    (imageCandidateSpatial_time_iteratedDeriv j l a z T y hl ha hz hT (le_of_lt hy))

end Shao.C2.IntervalImageMixedCandidate
