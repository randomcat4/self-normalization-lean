import Shao.C2.IntervalImageSpatialConvergence
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section
namespace Shao.C2.IntervalImageSpatialDerivatives
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence

def spatialTailSum (j : ℕ) (a z T y : ℝ) : ℝ :=
  ∑' n : ℕ, spatialTailBlock j a z T y n

theorem affineImageTerm_iterated_hasDerivAt (j : ℕ) (c k T y : ℝ) :
    HasDerivAt (iteratedDeriv j (affineImageTerm c k T))
      (iteratedDeriv (j + 1) (affineImageTerm c k T) y) y := by
  have hf : iteratedDeriv j (affineImageTerm c k T) =
      (fun w => (-c / T) ^ j * Real.exp (-(c * w + k) / T)) := by
    funext w
    exact affineImageTerm_iteratedDeriv j c k T w
  have hh := (((hasDerivAt_id y).const_mul c).add_const k).neg.div_const T
  have he := hh.exp.const_mul ((-c / T) ^ j)
  rw [hf, affineImageTerm_iteratedDeriv]
  convert he using 1 <;> (try funext w) <;>
    (try simp only [pow_succ, Pi.neg_apply, id_eq, mul_one]) <;> ring

theorem imageA_iterated_hasDerivAt (j : ℕ) (a z T y m : ℝ) :
    HasDerivAt (iteratedDeriv j (fun w => Real.exp (-imageA a w z m / T)))
      (iteratedDeriv (j + 1) (fun w => Real.exp (-imageA a w z m / T)) y) y := by
  have hf : (fun w => Real.exp (-imageA a w z m / T)) =
      affineImageTerm (-4 * m * a) (8 * m ^ 2 * a ^ 2 + 4 * m * a * z) T := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageA]
    ring
  rw [hf]
  exact affineImageTerm_iterated_hasDerivAt j _ _ T y

theorem imageB_iterated_hasDerivAt (j : ℕ) (a z T y m : ℝ) :
    HasDerivAt (iteratedDeriv j (fun w => Real.exp (-imageB a w z m / T)))
      (iteratedDeriv (j + 1) (fun w => Real.exp (-imageB a w z m / T)) y) y := by
  have hf : (fun w => Real.exp (-imageB a w z m / T)) =
      affineImageTerm (2 * (z + (2 * m + 1) * a))
        (2 * ((2 * m + 1) * a) * (z + (2 * m + 1) * a)) T := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageB]
    ring
  rw [hf]
  exact affineImageTerm_iterated_hasDerivAt j _ _ T y

theorem spatialTailBlock_hasDerivAt (j : ℕ) (a z T y : ℝ) (n : ℕ) :
    HasDerivAt (fun w => spatialTailBlock j a z T w n)
      (spatialTailBlock (j + 1) a z T y n) y := by
  exact (((imageA_iterated_hasDerivAt j a z T y (((n : ℤ) + 2 : ℤ) : ℝ)).add
    (imageA_iterated_hasDerivAt j a z T y ((-((n : ℤ) + 2) : ℤ) : ℝ))).sub
    (imageB_iterated_hasDerivAt j a z T y (((n : ℤ) + 1 : ℤ) : ℝ))).sub
    (imageB_iterated_hasDerivAt j a z T y ((-((n : ℤ) + 2) : ℤ) : ℝ))

theorem spatialTailSum_hasDerivAt (j : ℕ) (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    HasDerivAt (spatialTailSum j a z T) (spatialTailSum (j + 1) a z T y) y := by
  have hyI : y ∈ Ioo (-a) a := abs_lt.mp hy
  have hu := (gaussianMajorant_summable a T ha hT).mul_left
    (4 * spatialPrefactor (j + 1) a T)
  have hg : ∀ n w, w ∈ Ioo (-a) a →
      HasDerivAt (fun v => spatialTailBlock j a z T v n)
        (spatialTailBlock (j + 1) a z T w n) w := by
    intro n w _
    exact spatialTailBlock_hasDerivAt j a z T w n
  have hg' : ∀ n w, w ∈ Ioo (-a) a →
      ‖spatialTailBlock (j + 1) a z T w n‖ ≤
        4 * spatialPrefactor (j + 1) a T * gaussianMajorant a T n := by
    intro n w hw
    exact spatialTailBlock_bound (j + 1) a z T T n
      ⟨(w, T), le_of_lt (abs_lt.mpr hw), le_rfl, le_rfl⟩ ha hz hT le_rfl
  have hg0 := spatialTailBlock_summable j a z T T
    ⟨(y, T), le_of_lt hy, le_rfl, le_rfl⟩ ha hz hT le_rfl
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    hg hg' hyI hg0 hyI

theorem spatialTailSum_iteratedDeriv (j : ℕ) (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    iteratedDeriv j (spatialTailSum 0 a z T) y = spatialTailSum j a z T y := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    have heq : iteratedDeriv j (spatialTailSum 0 a z T) =ᶠ[𝓝 y]
        spatialTailSum j a z T := by
      filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with w hw
      exact ih w (abs_lt.mpr hw)
    rw [iteratedDeriv_succ]
    exact heq.deriv_eq.trans (spatialTailSum_hasDerivAt j a z T y ha hz hT hy).deriv

end Shao.C2.IntervalImageSpatialDerivatives
