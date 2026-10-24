import Shao.C2.IntervalSineCosineSeries
import Shao.C2.IntervalImageIntSeries

noncomputable section
namespace Shao.C2.IntervalImagePeriodization
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageCandidateSpatial

def periodGaussian (a T u : ℝ) (m : ℤ) : ℝ :=
  Real.exp (-(u + 4 * (m : ℝ) * a) ^ 2 / (2 * T))

theorem imageA_eq_periodGaussian (a z T y : ℝ) (m : ℤ) (hT : 0 < T) :
    Real.exp (-imageA a y z (m : ℝ) / T) =
      Real.exp ((z - y) ^ 2 / (2 * T)) * periodGaussian a T (z - y) m := by
  dsimp only [periodGaussian]
  rw [← Real.exp_add]
  congr 1
  dsimp only [imageA]
  field_simp [ne_of_gt hT] <;> ring

theorem imageB_eq_periodGaussian (a z T y : ℝ) (m : ℤ) (hT : 0 < T) :
    Real.exp (-imageB a y z (m : ℝ) / T) =
      Real.exp ((z - y) ^ 2 / (2 * T)) * periodGaussian a T (z + y + 2 * a) m := by
  dsimp only [periodGaussian]
  rw [← Real.exp_add]
  congr 1
  dsimp only [imageB]
  field_simp [ne_of_gt hT] <;> ring

theorem periodGaussian_summable (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    Summable (periodGaussian a T (z - y)) ∧
      Summable (periodGaussian a T (z + y + 2 * a)) := by
  obtain ⟨hA, hB⟩ := image_spatial_summable 0 a z T y ha hz hT hy
  change Summable (fun m : ℤ => Real.exp (-imageA a y z (m : ℝ) / T)) at hA
  change Summable (fun m : ℤ => Real.exp (-imageB a y z (m : ℝ) / T)) at hB
  have hEA : Summable (fun m : ℤ => Real.exp ((z - y) ^ 2 / (2 * T)) *
      periodGaussian a T (z - y) m) := by
    simpa only [spatialImageA, iteratedDeriv_zero, imageA_eq_periodGaussian a z T y _ hT] using hA
  have hEB : Summable (fun m : ℤ => Real.exp ((z - y) ^ 2 / (2 * T)) *
      periodGaussian a T (z + y + 2 * a) m) := by
    simpa only [spatialImageB, iteratedDeriv_zero, imageB_eq_periodGaussian a z T y _ hT] using hB
  have hc (u : ℝ) : (fun m : ℤ => (1 / Real.exp ((z - y) ^ 2 / (2 * T))) *
      (Real.exp ((z - y) ^ 2 / (2 * T)) * periodGaussian a T u m)) = periodGaussian a T u := by
    funext m
    field_simp [Real.exp_ne_zero ((z - y) ^ 2 / (2 * T))]
  constructor
  · have h := hEA.mul_left (1 / Real.exp ((z - y) ^ 2 / (2 * T)))
    rw [hc] at h
    exact h
  · have h := hEB.mul_left (1 / Real.exp ((z - y) ^ 2 / (2 * T)))
    rw [hc] at h
    exact h

theorem intervalImageCandidate_eq_periodization (a z T y : ℝ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    intervalImageCandidate a z T y = Real.exp ((z - y) ^ 2 / (2 * T)) *
      ((∑' m : ℤ, periodGaussian a T (z - y) m) -
        ∑' m : ℤ, periodGaussian a T (z + y + 2 * a) m) := by
  obtain ⟨hA, hB⟩ := periodGaussian_summable a z T y ha hz hT hy
  rw [intervalImageCandidate_eq_intSeries a z T y ha hz hT hy]
  have heq : (fun m : ℤ => Real.exp (-imageA a y z (m : ℝ) / T) -
      Real.exp (-imageB a y z (m : ℝ) / T)) =
      (fun m : ℤ => Real.exp ((z - y) ^ 2 / (2 * T)) *
        (periodGaussian a T (z - y) m - periodGaussian a T (z + y + 2 * a) m)) := by
    funext m
    rw [imageA_eq_periodGaussian a z T y m hT, imageB_eq_periodGaussian a z T y m hT]
    ring
  rw [heq, ((hA.hasSum.sub hB.hasSum).mul_left (Real.exp ((z - y) ^ 2 / (2 * T)))).tsum_eq]

end Shao.C2.IntervalImagePeriodization
