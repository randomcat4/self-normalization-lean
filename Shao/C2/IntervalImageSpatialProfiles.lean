import Shao.C2.IntervalImageExponents
import Shao.C2.HalfLineTimeProfiles

noncomputable section
namespace Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageExponents Shao.C2.HalfLineTimeProfiles

def affineImageTerm (c k T y : ℝ) : ℝ := Real.exp (-(c * y + k) / T)

theorem normalized_affine_slope (C c d T : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hid : C = (c - d) ^ 2 / 2 - d ^ 2 / 2) :
    |c| / Real.sqrt T ≤ 2 * (1 + |d| / Real.sqrt T) * (1 + C / T) := by
  let s := Real.sqrt T
  let q := C / T
  let t := |d| / s
  let r := Real.sqrt (2 * C) / s
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
  have hq : 0 ≤ q := by positivity
  have ht : 0 ≤ t := by positivity
  have hr : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = 2 * q := by
    dsimp only [r, q]
    rw [div_pow, Real.sq_sqrt (by positivity), hs2]
    ring
  have hrbound : r ≤ 1 + q := by nlinarith [sq_nonneg (q + 1 - r)]
  have hc : |c| / s ≤ 2 * t + r := by
    have hh := (div_le_div_iff_of_pos_right hs).2 (affine_slope_abs_bound C c d hC hid)
    convert hh using 1 <;> dsimp only [t, r] <;> ring
  change |c| / s ≤ 2 * (1 + t) * (1 + q)
  nlinarith only [hc, hrbound, hq, ht, mul_nonneg ht hq]

theorem nonneg_shifted_monomial_profile (q : ℝ) (hq : 0 ≤ q) (j m : ℕ) :
    (1 + q) ^ j * q ^ m * Real.exp (-q) ≤
      (2 : ℝ) ^ j * (1 + (2 : ℝ) ^ (j + m) * (Nat.factorial (j + m) : ℝ)) *
        Real.exp (-q / 2) := by
  let N := (2 : ℝ) ^ (j + m) * (Nat.factorial (j + m) : ℝ)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have h2j : 0 ≤ (2 : ℝ) ^ j := by positivity
  have he : 0 ≤ Real.exp (-q / 2) := (Real.exp_pos _).le
  change _ ≤ (2 : ℝ) ^ j * (1 + N) * Real.exp (-q / 2)
  by_cases hq1 : q ≤ 1
  · have hp : (1 + q) ^ j ≤ (2 : ℝ) ^ j :=
      pow_le_pow_left₀ (by linarith only [hq]) (by linarith only [hq1]) j
    have hm : q ^ m ≤ 1 := pow_le_one₀ hq hq1
    have hprod : (1 + q) ^ j * q ^ m ≤ (2 : ℝ) ^ j := by
      simpa only [mul_one] using mul_le_mul hp hm (pow_nonneg hq m) h2j
    have hexp : Real.exp (-q) ≤ Real.exp (-q / 2) := Real.exp_le_exp.2 (by linarith only [hq])
    have hh := mul_le_mul hprod hexp (Real.exp_pos (-q)).le h2j
    calc
      _ ≤ (2 : ℝ) ^ j * Real.exp (-q / 2) := hh
      _ = (2 : ℝ) ^ j * 1 * Real.exp (-q / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hN] : (1 : ℝ) ≤ 1 + N) h2j) he
  · have hqbig : 1 ≤ q := (lt_of_not_ge hq1).le
    have hp : (1 + q) ^ j ≤ (2 * q) ^ j :=
      pow_le_pow_left₀ (by linarith only [hq]) (by linarith only [hqbig]) j
    have hh := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (pow_nonneg hq m) (Real.exp_pos (-q)).le)
    have hprod : (1 + q) ^ j * q ^ m * Real.exp (-q) ≤
        (2 : ℝ) ^ j * (q ^ (j + m) * Real.exp (-q)) := by
      convert hh using 1 <;> (try rw [mul_pow, pow_add]) <;> ring
    have hm := nonneg_exp_monomial_profile q hq (j + m)
    change q ^ (j + m) * Real.exp (-q) ≤ N * Real.exp (-q / 2) at hm
    calc
      _ ≤ (2 : ℝ) ^ j * (q ^ (j + m) * Real.exp (-q)) := hprod
      _ ≤ (2 : ℝ) ^ j * (N * Real.exp (-q / 2)) := mul_le_mul_of_nonneg_left hm h2j
      _ = (2 : ℝ) ^ j * N * Real.exp (-q / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : N ≤ 1 + N) h2j) he

theorem affine_monomial_profile (C c d T : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hid : C = (c - d) ^ 2 / 2 - d ^ 2 / 2) (j m : ℕ) :
    (|c| / T) ^ j * (C / T) ^ m * Real.exp (-C / T) ≤
      (4 / Real.sqrt T * (1 + |d| / Real.sqrt T)) ^ j *
        (1 + (2 : ℝ) ^ (j + m) * (Nat.factorial (j + m) : ℝ)) *
          Real.exp (-C / (2 * T)) := by
  let s := Real.sqrt T
  let D := 1 + |d| / s
  let q := C / T
  let N := 1 + (2 : ℝ) ^ (j + m) * (Nat.factorial (j + m) : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hs2 : s ^ 2 = T := Real.sq_sqrt hT.le
  have hq : 0 ≤ q := by positivity
  have hn := normalized_affine_slope C c d T hT hC hid
  change |c| / s ≤ 2 * D * (1 + q) at hn
  have hb : |c| / T ≤ (2 / s * D) * (1 + q) := by
    have hh := mul_le_mul_of_nonneg_right hn (inv_nonneg.mpr hs.le)
    convert hh using 1 <;> (try rw [← hs2]) <;> field_simp [ne_of_gt hs] <;> ring
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ |c| / T) hb j
  have hm := nonneg_shifted_monomial_profile q hq j m
  change (1 + q) ^ j * q ^ m * Real.exp (-q) ≤ (2 : ℝ) ^ j * N * Real.exp (-q / 2) at hm
  have he : -q / 2 = -C / (2 * T) := by dsimp only [q]; field_simp [ne_of_gt hT] <;> ring
  rw [he] at hm
  have hc : (2 / s * D) ^ j * (2 : ℝ) ^ j = (4 / s * D) ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  have he0 : -C / T = -q := by dsimp only [q]; ring
  rw [he0]
  calc
    _ ≤ (2 / s * D) ^ j * ((1 + q) ^ j * q ^ m * Real.exp (-q)) := by
      have hh := mul_le_mul_of_nonneg_right hp
        (mul_nonneg (pow_nonneg hq m) (Real.exp_pos (-q)).le)
      convert hh using 1 <;> (try dsimp only [q]) <;> (try simp only [mul_pow]) <;> ring
    _ ≤ (2 / s * D) ^ j * ((2 : ℝ) ^ j * N * Real.exp (-C / (2 * T))) :=
      mul_le_mul_of_nonneg_left hm (by dsimp only [D]; positivity)
    _ = ((2 / s * D) ^ j * (2 : ℝ) ^ j) * N * Real.exp (-C / (2 * T)) := by ring
    _ = _ := by rw [hc]

theorem affineImageTerm_iteratedDeriv (j : ℕ) (c k T y : ℝ) :
    iteratedDeriv j (affineImageTerm c k T) y =
      (-c / T) ^ j * Real.exp (-(c * y + k) / T) := by
  have hf : affineImageTerm c k T =
      (fun w => Real.exp (-k / T) * Real.exp ((-c / T) * w)) := by
    funext w
    dsimp only [affineImageTerm]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf, iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  change Real.exp (-k / T) * ((-c / T) ^ j * Real.exp ((-c / T) * y)) = _
  calc
    _ = (-c / T) ^ j * (Real.exp (-k / T) * Real.exp ((-c / T) * y)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring

theorem affineImageTerm_spatial_profile (j : ℕ) (c k d T y : ℝ)
    (hT : 0 < T) (hC : 0 ≤ c * y + k)
    (hid : c * y + k = (c - d) ^ 2 / 2 - d ^ 2 / 2) :
    |iteratedDeriv j (affineImageTerm c k T) y| ≤
      (4 / Real.sqrt T * (1 + |d| / Real.sqrt T)) ^ j *
        (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)) *
          Real.exp (-(c * y + k) / (2 * T)) := by
  rw [affineImageTerm_iteratedDeriv, abs_mul, abs_pow, abs_div, abs_neg,
    abs_of_pos hT, abs_of_pos (Real.exp_pos _)]
  have hh := affine_monomial_profile (c * y + k) c d T hT hC hid j 0
  simpa only [Nat.add_zero, pow_zero, mul_one] using hh

theorem imageA_spatial_profile (j : ℕ) (a y z T : ℝ) (m : ℤ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) (hT : 0 < T) :
    |iteratedDeriv j (fun w => Real.exp (-imageA a w z (m : ℝ) / T)) y| ≤
      (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)) *
          Real.exp (-imageA a y z (m : ℝ) / (2 * T)) := by
  let c := -4 * (m : ℝ) * a
  let k := 8 * (m : ℝ) ^ 2 * a ^ 2 + 4 * (m : ℝ) * a * z
  have hf : (fun w => Real.exp (-imageA a w z (m : ℝ) / T)) = affineImageTerm c k T := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageA, c, k]
    ring
  have heq : c * y + k = imageA a y z (m : ℝ) := by dsimp only [c, k, imageA]; ring
  have hn : 0 ≤ c * y + k := by rw [heq]; exact imageA_nonneg a y z m ha hy hz
  have hi : c * y + k = (c - (z - y)) ^ 2 / 2 - (z - y) ^ 2 / 2 := by
    rw [heq]
    exact imageA_affine_identity a y z (m : ℝ)
  rw [hf]
  have hh := affineImageTerm_spatial_profile j c k (z - y) T y hT hn hi
  rw [heq] at hh
  exact hh

theorem imageB_spatial_profile (j : ℕ) (a y z T : ℝ) (m : ℤ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) (hT : 0 < T) :
    |iteratedDeriv j (fun w => Real.exp (-imageB a w z (m : ℝ) / T)) y| ≤
      (4 / Real.sqrt T * (1 + |z - y| / Real.sqrt T)) ^ j *
        (1 + (2 : ℝ) ^ j * (Nat.factorial j : ℝ)) *
          Real.exp (-imageB a y z (m : ℝ) / (2 * T)) := by
  let c := 2 * (z + (2 * (m : ℝ) + 1) * a)
  let k := 2 * ((2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a)
  have hf : (fun w => Real.exp (-imageB a w z (m : ℝ) / T)) = affineImageTerm c k T := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageB, c, k]
    ring
  have heq : c * y + k = imageB a y z (m : ℝ) := by dsimp only [c, k, imageB]; ring
  have hn : 0 ≤ c * y + k := by rw [heq]; exact imageB_nonneg a y z m ha hy hz
  have hi : c * y + k = (c - (z - y)) ^ 2 / 2 - (z - y) ^ 2 / 2 := by
    rw [heq]
    exact imageB_affine_identity a y z (m : ℝ)
  rw [hf]
  have hh := affineImageTerm_spatial_profile j c k (z - y) T y hT hn hi
  rw [heq] at hh
  exact hh

end Shao.C2.IntervalImageSpatialProfiles
