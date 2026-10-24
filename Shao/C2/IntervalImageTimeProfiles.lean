import Shao.C2.IntervalImageCandidatePDE

noncomputable section
namespace Shao.C2.IntervalImageTimeProfiles
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE

def mixedFirstConstant (j : ℕ) : ℝ :=
  (j : ℝ) * (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)) +
    (1 + (2 : ℝ) ^ (j + 1) * (Nat.factorial (j + 1) : ℝ))

theorem mixedFirstConstant_nonneg (j : ℕ) : 0 ≤ mixedFirstConstant j := by
  dsimp only [mixedFirstConstant]
  positivity

theorem affineSpatialTimeSlope_profile (j : ℕ) (c k d y T : ℝ)
    (hT : 0 < T) (hC : 0 ≤ c * y + k)
    (hid : c * y + k = (c - d) ^ 2 / 2 - d ^ 2 / 2) :
    |affineSpatialTimeSlope j c k y T| ≤
      (4 / Real.sqrt T * (1 + |d| / Real.sqrt T)) ^ j * mixedFirstConstant j / T *
        Real.exp (-(c * y + k) / (2 * T)) := by
  let C := c * y + k
  let q := C / T
  let X := (|c| / T) ^ j * Real.exp (-C / T)
  let A := (4 / Real.sqrt T * (1 + |d| / Real.sqrt T)) ^ j
  let E := Real.exp (-C / (2 * T))
  have hq : 0 ≤ q := div_nonneg hC hT.le
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have habs : |q - (j : ℝ)| ≤ q + (j : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith only [hq, Nat.cast_nonneg (α := ℝ) j]
  have hfactor : C / T ^ 2 - (j : ℝ) / T = (q - (j : ℝ)) / T := by
    dsimp only [q]
    field_simp [ne_of_gt hT] <;> ring
  have hnorm : |affineSpatialTimeSlope j c k y T| ≤
      (X * q + (j : ℝ) * X) / T := by
    dsimp only [affineSpatialTimeSlope]
    rw [hfactor, abs_mul, abs_mul, abs_div, abs_pow, abs_div, abs_neg,
      abs_of_pos hT, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ ((q + (j : ℝ)) / T) * (|c| / T) ^ j * Real.exp (-C / T) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right habs hT.le)
            (by positivity)) (Real.exp_pos _).le
      _ = _ := by dsimp only [X]; ring
  have hM0 := affine_monomial_profile C c d T hT hC hid j 0
  have hM1 := affine_monomial_profile C c d T hT hC hid j 1
  simp only [Nat.add_zero, pow_zero, mul_one] at hM0
  simp only [pow_one] at hM1
  have hbound : X * q + (j : ℝ) * X ≤ A * mixedFirstConstant j * E := by
    have hh := add_le_add hM1 (mul_le_mul_of_nonneg_left hM0 (Nat.cast_nonneg j))
    convert hh using 1 <;> (try dsimp only [X, q, A, E, mixedFirstConstant]) <;> ring
  calc
    _ ≤ (X * q + (j : ℝ) * X) / T := hnorm
    _ ≤ (A * mixedFirstConstant j * E) / T := div_le_div_of_nonneg_right hbound hT.le
    _ = _ := by dsimp only [A, E]; ring

theorem spatialImageA_time_profile (j : ℕ) (a z T y : ℝ) (m : ℤ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    |deriv (fun S => spatialImageA j a z S y m) T| ≤
      (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j * mixedFirstConstant j / T *
        Real.exp (-imageA a y z (m : ℝ) / (2 * T)) := by
  let c := -4 * (m : ℝ) * a
  let k := 8 * (m : ℝ) ^ 2 * a ^ 2 + 4 * (m : ℝ) * a * z
  have hf (S : ℝ) : (fun w => Real.exp (-imageA a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageA, c, k]
    ring
  have hwhole : (fun S => spatialImageA j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageA, hf]
  have heq : c * y + k = imageA a y z (m : ℝ) := by dsimp only [c, k, imageA]; ring
  have hn : 0 ≤ c * y + k := by rw [heq]; exact imageA_nonneg a y z m ha hy hz
  have hi : c * y + k = (c - (z - y)) ^ 2 / 2 - (z - y) ^ 2 / 2 := by
    rw [heq]
    exact imageA_affine_identity a y z (m : ℝ)
  rw [hwhole, (affineSpatial_time_hasDerivAt j c k y T hT).deriv]
  have hh := affineSpatialTimeSlope_profile j c k (z - y) y T hT hn hi
  rw [heq] at hh
  exact hh

theorem spatialImageB_time_profile (j : ℕ) (a z T y : ℝ) (m : ℤ) (ha : 0 < a)
    (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| ≤ a) :
    |deriv (fun S => spatialImageB j a z S y m) T| ≤
      (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j * mixedFirstConstant j / T *
        Real.exp (-imageB a y z (m : ℝ) / (2 * T)) := by
  let c := 2 * (z + (2 * (m : ℝ) + 1) * a)
  let k := 2 * ((2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a)
  have hf (S : ℝ) : (fun w => Real.exp (-imageB a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageB, c, k]
    ring
  have hwhole : (fun S => spatialImageB j a z S y m) =
      (fun S => iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [spatialImageB, hf]
  have heq : c * y + k = imageB a y z (m : ℝ) := by dsimp only [c, k, imageB]; ring
  have hn : 0 ≤ c * y + k := by rw [heq]; exact imageB_nonneg a y z m ha hy hz
  have hi : c * y + k = (c - (z - y)) ^ 2 / 2 - (z - y) ^ 2 / 2 := by
    rw [heq]
    exact imageB_affine_identity a y z (m : ℝ)
  rw [hwhole, (affineSpatial_time_hasDerivAt j c k y T hT).deriv]
  have hh := affineSpatialTimeSlope_profile j c k (z - y) y T hT hn hi
  rw [heq] at hh
  exact hh

end Shao.C2.IntervalImageTimeProfiles
