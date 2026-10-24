import Shao.C2.HalfLineSmallTaylor

noncomputable section
namespace Shao.C2.HalfLineCompensatedBounds
open Shao.C2.HalfLineReflectionFormula Shao.C2.HalfLineSmallTaylor
open Shao.C2.HalfLineTaylorPath Shao.C2.HalfLineTaylorSegment
open Shao.C2.HalfLineMixedProfiles

theorem upperReflection_small_taylor_bound (a y z T b : ℝ) (ha : 0 < a)
    (hy : y < a) (hz : z < a) (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2)
    (hnew : y + b ≤ a) :
    |upperReflection a (y + b) (T - b ^ 2) z - upperReflection a y T z -
        (b - b ^ 2 * (z - y) / T) * deriv (fun x : ℝ => upperReflection a x T z) y| ≤
      8000100 * |b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 *
          Real.exp (-(max (a - y - |b|) 0) * (a - z) / T) := by
  have h := compensated_small_taylor_bound (a - y) (a - z) T b
    (sub_pos.mpr hy) (sub_pos.mpr hz) hT hsmall (by linarith)
  have hpath (t : ℝ) : completionAlongSegment (a - y) (a - z) T b t =
      upperReflection a (y + t * b) (T - t * b ^ 2) z := by
    dsimp only [completionAlongSegment, segmentDistance, segmentEnergy, upperReflection]
    congr 2 <;> ring
  rw [hpath 1, hpath 0] at h
  simp only [one_mul, zero_mul, add_zero, sub_zero] at h
  have hd : (a - y) - (a - z) = z - y := by ring
  rw [hd] at h
  rw [(upperReflection_hasDerivAt a y T z).deriv]
  dsimp only [incrementProfile, slopeTime] at h
  convert h using 1 <;> congr 1 <;> ring

theorem lowerReflection_small_taylor_bound (a y z T b : ℝ) (ha : 0 < a)
    (hy : -a < y) (hz : -a < z) (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2)
    (hnew : -a ≤ y + b) :
    |lowerReflection a (y + b) (T - b ^ 2) z - lowerReflection a y T z -
        (b - b ^ 2 * (z - y) / T) * deriv (fun x : ℝ => lowerReflection a x T z) y| ≤
      8000100 * |b| ^ 3 * (1 / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 *
          Real.exp (-(max (a + y - |b|) 0) * (a + z) / T) := by
  have h := compensated_small_taylor_bound (a + y) (a + z) T (-b)
    (by linarith) (by linarith) hT (by simpa only [neg_sq] using hsmall) (by linarith)
  have hpath (t : ℝ) : completionAlongSegment (a + y) (a + z) T (-b) t =
      lowerReflection a (y + t * b) (T - t * b ^ 2) z := by
    dsimp only [completionAlongSegment, segmentDistance, segmentEnergy, lowerReflection]
    congr 2 <;> ring
  rw [hpath 1, hpath 0] at h
  simp only [one_mul, zero_mul, add_zero, sub_zero, neg_sq, abs_neg] at h
  have hd : (a + y) - (a + z) = y - z := by ring
  rw [hd, abs_sub_comm y z] at h
  rw [(lowerReflection_hasDerivAt a y T z).deriv]
  dsimp only [incrementProfile, slopeTime] at h
  simp only [abs_neg] at h
  convert h using 1 <;> congr 1 <;> ring

end Shao.C2.HalfLineCompensatedBounds
