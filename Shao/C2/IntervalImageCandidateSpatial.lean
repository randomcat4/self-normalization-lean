import Shao.C2.IntervalImageSpatialDerivatives

noncomputable section
namespace Shao.C2.IntervalImageCandidateSpatial
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives

def finiteSpatialImages (j : ℕ) (a z T y : ℝ) : ℝ :=
  iteratedDeriv j (fun w => Real.exp (-imageA a w z 0 / T)) y +
    iteratedDeriv j (fun w => Real.exp (-imageA a w z 1 / T)) y +
    iteratedDeriv j (fun w => Real.exp (-imageA a w z (-1) / T)) y -
    iteratedDeriv j (fun w => Real.exp (-imageB a w z 0 / T)) y -
    iteratedDeriv j (fun w => Real.exp (-imageB a w z (-1) / T)) y

def imageCandidateSpatial (j : ℕ) (a z T y : ℝ) : ℝ :=
  finiteSpatialImages j a z T y + spatialTailSum j a z T y

def intervalImageCandidate (a z T y : ℝ) : ℝ :=
  imageCandidateSpatial 0 a z T y

theorem finiteSpatialImages_zero (a z T y : ℝ) :
    finiteSpatialImages 0 a z T y =
      1 + Real.exp (-imageA a y z 1 / T) + Real.exp (-imageA a y z (-1) / T) -
        Real.exp (-imageB a y z 0 / T) - Real.exp (-imageB a y z (-1) / T) := by
  have h0 : imageA a y z 0 = 0 := by simp [imageA]
  simp only [finiteSpatialImages, iteratedDeriv_zero, h0, neg_zero, zero_div, Real.exp_zero]

theorem finiteSpatialImages_hasDerivAt (j : ℕ) (a z T y : ℝ) :
    HasDerivAt (finiteSpatialImages j a z T)
      (finiteSpatialImages (j + 1) a z T y) y := by
  exact ((((imageA_iterated_hasDerivAt j a z T y 0).add
    (imageA_iterated_hasDerivAt j a z T y 1)).add
    (imageA_iterated_hasDerivAt j a z T y (-1))).sub
    (imageB_iterated_hasDerivAt j a z T y 0)).sub
    (imageB_iterated_hasDerivAt j a z T y (-1))

theorem imageCandidateSpatial_hasDerivAt (j : ℕ) (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    HasDerivAt (imageCandidateSpatial j a z T)
      (imageCandidateSpatial (j + 1) a z T y) y := by
  exact (finiteSpatialImages_hasDerivAt j a z T y).add
    (spatialTailSum_hasDerivAt j a z T y ha hz hT hy)

theorem intervalImageCandidate_iteratedDeriv (j : ℕ) (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    iteratedDeriv j (intervalImageCandidate a z T) y = imageCandidateSpatial j a z T y := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    have heq : iteratedDeriv j (intervalImageCandidate a z T) =ᶠ[𝓝 y]
        imageCandidateSpatial j a z T := by
      filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with w hw
      exact ih w (abs_lt.mpr hw)
    rw [iteratedDeriv_succ]
    exact heq.deriv_eq.trans (imageCandidateSpatial_hasDerivAt j a z T y ha hz hT hy).deriv

theorem intervalImageCandidate_eq_images (a z T y : ℝ) :
    intervalImageCandidate a z T y =
      1 + Real.exp (-imageA a y z 1 / T) + Real.exp (-imageA a y z (-1) / T) -
        Real.exp (-imageB a y z 0 / T) - Real.exp (-imageB a y z (-1) / T) +
          ∑' n : ℕ, spatialTailBlock 0 a z T y n := by
  change finiteSpatialImages 0 a z T y + spatialTailSum 0 a z T y = _
  rw [finiteSpatialImages_zero]
  rfl

end Shao.C2.IntervalImageCandidateSpatial
