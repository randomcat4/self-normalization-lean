import Shao.C2.IntervalImageIntSeries
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
namespace Shao.C2.IntervalImageTimeDerivatives
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries

def affineSpatialTimeSlope (j : ℕ) (c k y T : ℝ) : ℝ :=
  ((c * y + k) / T ^ 2 - (j : ℝ) / T) * (-c / T) ^ j *
    Real.exp (-(c * y + k) / T)

theorem affineSpatial_time_hasDerivAt (j : ℕ) (c k y T : ℝ) (hT : 0 < T) :
    HasDerivAt (fun S => iteratedDeriv j (affineImageTerm c k S) y)
      (affineSpatialTimeSlope j c k y T) T := by
  have hf : (fun S => iteratedDeriv j (affineImageTerm c k S) y) =
      (fun S => (-c / S) ^ j * Real.exp (-(c * y + k) / S)) := by
    funext S
    exact affineImageTerm_iteratedDeriv j c k S y
  rw [hf]
  have hq := (hasDerivAt_const T (-c)).div (hasDerivAt_id T) (ne_of_gt hT)
  have he := ((hasDerivAt_const T (-(c * y + k))).div
    (hasDerivAt_id T) (ne_of_gt hT)).exp
  have hh := (hq.pow j).mul he
  convert hh using 1 <;> (try funext S) <;>
    (try simp only [affineSpatialTimeSlope, Pi.pow_apply, Pi.mul_apply, Pi.div_apply, id_eq])
  all_goals
    cases j with
    | zero => simp only [Nat.cast_zero, pow_zero, zero_mul, zero_div, zero_add,
        mul_one, sub_zero, zero_sub, one_mul]; ring
    | succ j =>
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
        pow_succ, zero_mul, mul_one, zero_sub]
      field_simp [ne_of_gt hT]
      ring

theorem spatialImageA_time_hasDerivAt (j : ℕ) (a z T y : ℝ) (m : ℤ) (hT : 0 < T) :
    HasDerivAt (fun S => spatialImageA j a z S y m)
      (1 / 2 * spatialImageA (j + 2) a z T y m +
        (z - y) / T * spatialImageA (j + 1) a z T y m -
          (j : ℝ) / T * spatialImageA j a z T y m) T := by
  let c := -4 * (m : ℝ) * a
  let k := 8 * (m : ℝ) ^ 2 * a ^ 2 + 4 * (m : ℝ) * a * z
  have hf (S : ℝ) : (fun w => Real.exp (-imageA a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageA, c, k]
    ring
  have hform (r : ℕ) (S : ℝ) : spatialImageA r a z S y m =
      (-c / S) ^ r * Real.exp (-(c * y + k) / S) := by
    rw [spatialImageA, hf, affineImageTerm_iteratedDeriv]
  have hwhole : (fun S => spatialImageA j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageA, hf]
  rw [hwhole]
  convert affineSpatial_time_hasDerivAt j c k y T hT using 1
  rw [hform (j + 2), hform (j + 1), hform j]
  dsimp only [affineSpatialTimeSlope]
  have hid : c * y + k = c ^ 2 / 2 - (z - y) * c := by dsimp only [c, k]; ring
  rw [hid]
  simp only [pow_add, pow_one, pow_two]
  field_simp [ne_of_gt hT]
  ring

theorem spatialImageB_time_hasDerivAt (j : ℕ) (a z T y : ℝ) (m : ℤ) (hT : 0 < T) :
    HasDerivAt (fun S => spatialImageB j a z S y m)
      (1 / 2 * spatialImageB (j + 2) a z T y m +
        (z - y) / T * spatialImageB (j + 1) a z T y m -
          (j : ℝ) / T * spatialImageB j a z T y m) T := by
  let c := 2 * (z + (2 * (m : ℝ) + 1) * a)
  let k := 2 * ((2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a)
  have hf (S : ℝ) : (fun w => Real.exp (-imageB a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageB, c, k]
    ring
  have hform (r : ℕ) (S : ℝ) : spatialImageB r a z S y m =
      (-c / S) ^ r * Real.exp (-(c * y + k) / S) := by
    rw [spatialImageB, hf, affineImageTerm_iteratedDeriv]
  have hwhole : (fun S => spatialImageB j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageB, hf]
  rw [hwhole]
  convert affineSpatial_time_hasDerivAt j c k y T hT using 1
  rw [hform (j + 2), hform (j + 1), hform j]
  dsimp only [affineSpatialTimeSlope]
  have hid : c * y + k = c ^ 2 / 2 - (z - y) * c := by dsimp only [c, k]; ring
  rw [hid]
  simp only [pow_add, pow_one, pow_two]
  field_simp [ne_of_gt hT]
  ring

theorem spatialTailBlock_time_hasDerivAt (j : ℕ) (a z T y : ℝ) (n : ℕ) (hT : 0 < T) :
    HasDerivAt (fun S => spatialTailBlock j a z S y n)
      (1 / 2 * spatialTailBlock (j + 2) a z T y n +
        (z - y) / T * spatialTailBlock (j + 1) a z T y n -
          (j : ℝ) / T * spatialTailBlock j a z T y n) T := by
  have hh := (((spatialImageA_time_hasDerivAt j a z T y ((n : ℤ) + 2) hT).add
    (spatialImageA_time_hasDerivAt j a z T y (-((n : ℤ) + 2)) hT)).sub
    (spatialImageB_time_hasDerivAt j a z T y ((n : ℤ) + 1) hT)).sub
    (spatialImageB_time_hasDerivAt j a z T y (-((n : ℤ) + 2)) hT)
  have hb (r : ℕ) : spatialTailBlock r a z T y n =
      spatialImageA r a z T y ((n : ℤ) + 2) + spatialImageA r a z T y (-((n : ℤ) + 2)) -
        spatialImageB r a z T y ((n : ℤ) + 1) - spatialImageB r a z T y (-((n : ℤ) + 2)) := rfl
  convert hh using 1 <;> (try funext S) <;> (try rfl)
  rw [hb (j + 2), hb (j + 1), hb j]
  ring

end Shao.C2.IntervalImageTimeDerivatives
