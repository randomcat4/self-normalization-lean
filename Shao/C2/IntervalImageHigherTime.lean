import Shao.C2.IntervalImageTimeProfiles

noncomputable section
namespace Shao.C2.IntervalImageHigherTime
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles

def affineSpatialTimeSecond (j : ℕ) (c k y T : ℝ) : ℝ :=
  (((c * y + k) / T) ^ 2 - 2 * ((j : ℝ) + 1) * ((c * y + k) / T) +
    (j : ℝ) * ((j : ℝ) + 1)) / T ^ 2 * (-c / T) ^ j * Real.exp (-(c * y + k) / T)

def affineSpatialTimeThird (j : ℕ) (c k y T : ℝ) : ℝ :=
  (((c * y + k) / T) ^ 3 - 3 * ((j : ℝ) + 2) * ((c * y + k) / T) ^ 2 +
    3 * ((j : ℝ) + 1) * ((j : ℝ) + 2) * ((c * y + k) / T) -
    (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2)) / T ^ 3 *
      (-c / T) ^ j * Real.exp (-(c * y + k) / T)

def mixedSecondConstant (j : ℕ) : ℝ :=
  (1 + (2 : ℝ) ^ (j + 2) * (Nat.factorial (j + 2) : ℝ)) +
    2 * ((j : ℝ) + 1) * (1 + (2 : ℝ) ^ (j + 1) * (Nat.factorial (j + 1) : ℝ)) +
      (j : ℝ) * ((j : ℝ) + 1) * (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ))

def mixedThirdConstant (j : ℕ) : ℝ :=
  (1 + (2 : ℝ) ^ (j + 3) * (Nat.factorial (j + 3) : ℝ)) +
    3 * ((j : ℝ) + 2) * (1 + (2 : ℝ) ^ (j + 2) * (Nat.factorial (j + 2) : ℝ)) +
      3 * ((j : ℝ) + 1) * ((j : ℝ) + 2) *
        (1 + (2 : ℝ) ^ (j + 1) * (Nat.factorial (j + 1) : ℝ)) +
          (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2) *
            (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ))

theorem affineSpatialTimeSlope_hasDerivAt (j : ℕ) (c k y T : ℝ) (hT : 0 < T) :
    HasDerivAt (affineSpatialTimeSlope j c k y) (affineSpatialTimeSecond j c k y T) T := by
  let C := c * y + k
  have hbase := affineSpatial_time_hasDerivAt j c k y T hT
  have hc := ((hasDerivAt_const T C).div ((hasDerivAt_id T).pow 2)
    (pow_ne_zero 2 (ne_of_gt hT))).sub
    ((hasDerivAt_const T (j : ℝ)).div (hasDerivAt_id T) (ne_of_gt hT))
  have hf : affineSpatialTimeSlope j c k y =
      (fun S => (C / S ^ 2 - (j : ℝ) / S) *
        iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [affineSpatialTimeSlope, affineImageTerm_iteratedDeriv]
    dsimp only [C]
    ring
  rw [hf]
  convert hc.mul hbase using 1 <;> (try funext S) <;>
    (try simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id_eq])
  all_goals
    rw [affineImageTerm_iteratedDeriv]
    dsimp only [affineSpatialTimeSecond, affineSpatialTimeSlope, C]
    field_simp [ne_of_gt hT] <;> ring_nf <;> (try field_simp [ne_of_gt hT]) <;> ring

theorem affineSpatialTimeSecond_hasDerivAt (j : ℕ) (c k y T : ℝ) (hT : 0 < T) :
    HasDerivAt (affineSpatialTimeSecond j c k y) (affineSpatialTimeThird j c k y T) T := by
  let C := c * y + k
  have hbase := affineSpatial_time_hasDerivAt j c k y T hT
  have hq := (hasDerivAt_const T C).div (hasDerivAt_id T) (ne_of_gt hT)
  have hp := ((hq.pow 2).sub (hq.const_mul (2 * ((j : ℝ) + 1)))).add_const
    ((j : ℝ) * ((j : ℝ) + 1))
  have hc := hp.div ((hasDerivAt_id T).pow 2) (pow_ne_zero 2 (ne_of_gt hT))
  have hf : affineSpatialTimeSecond j c k y =
      (fun S => ((C / S) ^ 2 - 2 * ((j : ℝ) + 1) * (C / S) +
        (j : ℝ) * ((j : ℝ) + 1)) / S ^ 2 *
          iteratedDeriv j (affineImageTerm c k S) y) := by
    funext S
    rw [affineSpatialTimeSecond, affineImageTerm_iteratedDeriv]
    dsimp only [C]
    ring
  rw [hf]
  convert hc.mul hbase using 1 <;> (try funext S) <;>
    (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id_eq])
  all_goals
    rw [affineImageTerm_iteratedDeriv]
    dsimp only [affineSpatialTimeThird, affineSpatialTimeSlope, C]
    field_simp [ne_of_gt hT] <;> ring_nf <;> (try field_simp [ne_of_gt hT]) <;> ring

theorem affineSpatial_time_iteratedDeriv_two (j : ℕ) (c k y T : ℝ) (hT : 0 < T) :
    iteratedDeriv 2 (fun S => iteratedDeriv j (affineImageTerm c k S) y) T =
      affineSpatialTimeSecond j c k y T := by
  have heq : deriv (fun S => iteratedDeriv j (affineImageTerm c k S) y) =ᶠ[𝓝 T]
      affineSpatialTimeSlope j c k y := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
    exact (affineSpatial_time_hasDerivAt j c k y S hS).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  exact heq.deriv_eq.trans (affineSpatialTimeSlope_hasDerivAt j c k y T hT).deriv

theorem affineSpatial_time_iteratedDeriv_three (j : ℕ) (c k y T : ℝ) (hT : 0 < T) :
    iteratedDeriv 3 (fun S => iteratedDeriv j (affineImageTerm c k S) y) T =
      affineSpatialTimeThird j c k y T := by
  have heq : iteratedDeriv 2 (fun S => iteratedDeriv j (affineImageTerm c k S) y) =ᶠ[𝓝 T]
      affineSpatialTimeSecond j c k y := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
    exact affineSpatial_time_iteratedDeriv_two j c k y S hS
  rw [iteratedDeriv_succ]
  exact heq.deriv_eq.trans (affineSpatialTimeSecond_hasDerivAt j c k y T hT).deriv

theorem affineSpatialTimeSecond_profile (j : ℕ) (c k d y T : ℝ)
    (hT : 0 < T) (hC : 0 ≤ c * y + k)
    (hid : c * y + k = (c - d) ^ 2 / 2 - d ^ 2 / 2) :
    |affineSpatialTimeSecond j c k y T| ≤
      (4 / Real.sqrt T * (1 + |d| / Real.sqrt T)) ^ j * mixedSecondConstant j / T ^ 2 *
        Real.exp (-(c * y + k) / (2 * T)) := by
  let C := c * y + k
  let q := C / T
  let X := (|c| / T) ^ j * Real.exp (-C / T)
  let A := (4 / Real.sqrt T * (1 + |d| / Real.sqrt T)) ^ j
  let E := Real.exp (-C / (2 * T))
  have hq : 0 ≤ q := div_nonneg hC hT.le
  have hp1 : 0 ≤ 2 * ((j : ℝ) + 1) * q := by positivity
  have hp0 : 0 ≤ (j : ℝ) * ((j : ℝ) + 1) := by positivity
  have hpoly : |q ^ 2 - 2 * ((j : ℝ) + 1) * q + (j : ℝ) * ((j : ℝ) + 1)| ≤
      q ^ 2 + 2 * ((j : ℝ) + 1) * q + (j : ℝ) * ((j : ℝ) + 1) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg q, hp1, hp0]
  have hnorm : |affineSpatialTimeSecond j c k y T| ≤
      (X * q ^ 2 + 2 * ((j : ℝ) + 1) * (X * q) +
        (j : ℝ) * ((j : ℝ) + 1) * X) / T ^ 2 := by
    dsimp only [affineSpatialTimeSecond]
    rw [abs_mul, abs_mul, abs_div, abs_of_pos (pow_pos hT 2), abs_pow, abs_div,
      abs_neg, abs_of_pos hT, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ ((q ^ 2 + 2 * ((j : ℝ) + 1) * q + (j : ℝ) * ((j : ℝ) + 1)) / T ^ 2) *
          (|c| / T) ^ j * Real.exp (-C / T) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpoly (by positivity))
            (by positivity)) (Real.exp_pos _).le
      _ = _ := by dsimp only [X]; ring
  have hM0 := affine_monomial_profile C c d T hT hC hid j 0
  have hM1 := affine_monomial_profile C c d T hT hC hid j 1
  have hM2 := affine_monomial_profile C c d T hT hC hid j 2
  simp only [Nat.add_zero, pow_zero, mul_one] at hM0
  simp only [pow_one] at hM1
  have hbound : X * q ^ 2 + 2 * ((j : ℝ) + 1) * (X * q) +
      (j : ℝ) * ((j : ℝ) + 1) * X ≤ A * mixedSecondConstant j * E := by
    have hh := add_le_add
      (add_le_add hM2 (mul_le_mul_of_nonneg_left hM1 (by positivity : 0 ≤ 2 * ((j : ℝ) + 1))))
      (mul_le_mul_of_nonneg_left hM0 (by positivity : 0 ≤ (j : ℝ) * ((j : ℝ) + 1)))
    convert hh using 1 <;> (try dsimp only [X, q, A, E, mixedSecondConstant]) <;> ring
  calc
    _ ≤ _ := hnorm
    _ ≤ (A * mixedSecondConstant j * E) / T ^ 2 := div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by dsimp only [A, E]; ring

theorem affineSpatialTimeThird_profile (j : ℕ) (c k d y T : ℝ)
    (hT : 0 < T) (hC : 0 ≤ c * y + k)
    (hid : c * y + k = (c - d) ^ 2 / 2 - d ^ 2 / 2) :
    |affineSpatialTimeThird j c k y T| ≤
      (4 / Real.sqrt T * (1 + |d| / Real.sqrt T)) ^ j * mixedThirdConstant j / T ^ 3 *
        Real.exp (-(c * y + k) / (2 * T)) := by
  let C := c * y + k
  let q := C / T
  let X := (|c| / T) ^ j * Real.exp (-C / T)
  let A := (4 / Real.sqrt T * (1 + |d| / Real.sqrt T)) ^ j
  let E := Real.exp (-C / (2 * T))
  have hq : 0 ≤ q := div_nonneg hC hT.le
  have hp3 : 0 ≤ q ^ 3 := by positivity
  have hp2 : 0 ≤ 3 * ((j : ℝ) + 2) * q ^ 2 := by positivity
  have hp1 : 0 ≤ 3 * ((j : ℝ) + 1) * ((j : ℝ) + 2) * q := by positivity
  have hp0 : 0 ≤ (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
  have hpoly : |q ^ 3 - 3 * ((j : ℝ) + 2) * q ^ 2 +
      3 * ((j : ℝ) + 1) * ((j : ℝ) + 2) * q - (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2)| ≤
      q ^ 3 + 3 * ((j : ℝ) + 2) * q ^ 2 +
        3 * ((j : ℝ) + 1) * ((j : ℝ) + 2) * q + (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hp3, hp2, hp1, hp0]
  have hnorm : |affineSpatialTimeThird j c k y T| ≤
      (X * q ^ 3 + 3 * ((j : ℝ) + 2) * (X * q ^ 2) +
        3 * ((j : ℝ) + 1) * ((j : ℝ) + 2) * (X * q) +
          (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2) * X) / T ^ 3 := by
    dsimp only [affineSpatialTimeThird]
    rw [abs_mul, abs_mul, abs_div, abs_of_pos (pow_pos hT 3), abs_pow, abs_div,
      abs_neg, abs_of_pos hT, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ ((q ^ 3 + 3 * ((j : ℝ) + 2) * q ^ 2 +
          3 * ((j : ℝ) + 1) * ((j : ℝ) + 2) * q +
            (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2)) / T ^ 3) *
              (|c| / T) ^ j * Real.exp (-C / T) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpoly (by positivity))
            (by positivity)) (Real.exp_pos _).le
      _ = _ := by dsimp only [X]; ring
  have hM0 := affine_monomial_profile C c d T hT hC hid j 0
  have hM1 := affine_monomial_profile C c d T hT hC hid j 1
  have hM2 := affine_monomial_profile C c d T hT hC hid j 2
  have hM3 := affine_monomial_profile C c d T hT hC hid j 3
  simp only [Nat.add_zero, pow_zero, mul_one] at hM0
  simp only [pow_one] at hM1
  have hbound : X * q ^ 3 + 3 * ((j : ℝ) + 2) * (X * q ^ 2) +
      3 * ((j : ℝ) + 1) * ((j : ℝ) + 2) * (X * q) +
        (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2) * X ≤ A * mixedThirdConstant j * E := by
    have hh := add_le_add
      (add_le_add (add_le_add hM3
        (mul_le_mul_of_nonneg_left hM2 (by positivity : 0 ≤ 3 * ((j : ℝ) + 2))))
        (mul_le_mul_of_nonneg_left hM1 (by positivity : 0 ≤ 3 * ((j : ℝ) + 1) * ((j : ℝ) + 2))))
      (mul_le_mul_of_nonneg_left hM0 (by positivity : 0 ≤ (j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2)))
    convert hh using 1 <;> (try dsimp only [X, q, A, E, mixedThirdConstant]) <;> ring
  calc
    _ ≤ _ := hnorm
    _ ≤ (A * mixedThirdConstant j * E) / T ^ 3 := div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by dsimp only [A, E]; ring

end Shao.C2.IntervalImageHigherTime
