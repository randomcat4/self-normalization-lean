import Shao.C2.IntervalGaussianCosinePoisson
import Shao.C2.IntervalImagePeriodization
import Shao.C2.IntervalSineNormalizedDerivatives

noncomputable section
namespace Shao.C2.IntervalImageSineIdentity
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalGaussianCosinePoisson Shao.C2.IntervalImagePeriodization
open Shao.C2.IntervalSineCosineSeries Shao.C2.IntervalSineSeries
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalReciprocalDerivatives
open Shao.C2.IntervalSineNormalizedDerivatives

theorem periodGaussian_eq_integer_cosine (a T u : ℝ) (ha : 0 < a) (hT : 0 < T) :
    (∑' m : ℤ, periodGaussian a T u m) =
      (Real.sqrt (2 * Real.pi) * Real.sqrt T / (4 * a)) *
        (∑' n : ℤ, integerCosineTerm a T u n) := by
  have hc : 0 < T / (8 * a ^ 2) := by positivity
  have he (m : ℤ) : periodGaussian a T u m =
      Real.exp (-((m : ℝ) + u / (4 * a)) ^ 2 / (T / (8 * a ^ 2))) := by
    unfold periodGaussian
    congr 1
    field_simp [ne_of_gt ha, ne_of_gt hT] <;> ring
  have hcos (n : ℤ) : Real.exp (-(Real.pi ^ 2) * (T / (8 * a ^ 2)) * (n : ℝ) ^ 2) *
      Real.cos (2 * Real.pi * (n : ℝ) * (u / (4 * a))) = integerCosineTerm a T u n := by
    unfold integerCosineTerm
    congr 2 <;> field_simp [ne_of_gt ha] <;> ring
  have hK0 : 0 ≤ Real.sqrt (2 * Real.pi) * Real.sqrt T / (4 * a) := by positivity
  have hKsq : (Real.sqrt (2 * Real.pi) * Real.sqrt T / (4 * a)) ^ 2 =
      Real.pi * (T / (8 * a ^ 2)) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Real.sq_sqrt hT.le]
    field_simp [ne_of_gt ha] <;> ring
  have hroot : Real.sqrt (Real.pi * (T / (8 * a ^ 2))) =
      Real.sqrt (2 * Real.pi) * Real.sqrt T / (4 * a) := by
    rw [← hKsq, Real.sqrt_sq hK0]
  calc
    _ = ∑' m : ℤ, Real.exp (-((m : ℝ) + u / (4 * a)) ^ 2 / (T / (8 * a ^ 2))) := tsum_congr he
    _ = Real.sqrt (Real.pi * (T / (8 * a ^ 2))) *
        (∑' n : ℤ, Real.exp (-(Real.pi ^ 2) * (T / (8 * a ^ 2)) * (n : ℝ) ^ 2) *
          Real.cos (2 * Real.pi * (n : ℝ) * (u / (4 * a)))) :=
      shifted_gaussian_cosine_poisson (T / (8 * a ^ 2)) (u / (4 * a)) hc
    _ = _ := by
      rw [hroot]
      congr 1
      exact tsum_congr hcos

theorem intervalImageCandidate_eq_normalizedSineCandidate (a z T y : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    intervalImageCandidate a z T y = normalizedSineCandidate a z T y := by
  rw [intervalImageCandidate_eq_periodization a z T y ha hz hT hy,
    periodGaussian_eq_integer_cosine a T (z - y) ha hT,
    periodGaussian_eq_integer_cosine a T (z + y + 2 * a) ha hT]
  unfold normalizedSineCandidate reciprocalFreeDensity
  rw [sineSeries_eq_integer_cosine a z T y ha hT]
  simp only [div_eq_mul_inv]
  ring

end Shao.C2.IntervalImageSineIdentity
