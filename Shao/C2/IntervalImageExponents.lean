import Shao.C2.HalfLineSpatialProfiles
import Lean.Elab.Tactic.Omega

noncomputable section
namespace Shao.C2.IntervalImageExponents

def imageA (a y z m : ℝ) : ℝ := 8 * m ^ 2 * a ^ 2 + 4 * m * a * (z - y)
def imageB (a y z m : ℝ) : ℝ := 2 * (y + (2 * m + 1) * a) * (z + (2 * m + 1) * a)

theorem int_abs_ge_one (m : ℤ) (hm : m ≠ 0) : 1 ≤ |(m : ℝ)| := by
  by_cases h0 : 0 ≤ m
  · have h1 : 1 ≤ m := by omega
    have hr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    rw [abs_of_nonneg (by exact_mod_cast h0 : (0 : ℝ) ≤ (m : ℝ))]
    exact hr
  · have h1 : m ≤ -1 := by omega
    have hr : (m : ℝ) ≤ -1 := by exact_mod_cast h1
    rw [abs_of_nonpos (by linarith only [hr] : (m : ℝ) ≤ 0)]
    linarith only [hr]

theorem imageA_zero (a y z : ℝ) : imageA a y z 0 = 0 := by
  simp [imageA]

theorem imageA_nonneg (a y z : ℝ) (m : ℤ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) : 0 ≤ imageA a y z (m : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simpa only [Int.cast_zero] using le_of_eq (imageA_zero a y z).symm
  · let r := |(m : ℝ)|
    have hr : 1 ≤ r := int_abs_ge_one m hm
    have hr0 : 0 ≤ r := abs_nonneg _
    have hd : |z - y| ≤ 2 * a := by
      apply abs_le.mpr
      constructor <;> linarith only [(abs_le.mp hy).1, (abs_le.mp hy).2,
        (abs_le.mp hz).1, (abs_le.mp hz).2]
    have hmd : -r * |z - y| ≤ (m : ℝ) * (z - y) := by
      simpa only [r, abs_mul, neg_mul] using neg_abs_le ((m : ℝ) * (z - y))
    have hd' := mul_le_mul_of_nonneg_left hd hr0
    have hlin : 0 ≤ 4 * a * ((m : ℝ) * (z - y) + 2 * r * a) := by
      apply mul_nonneg (by positivity)
      nlinarith only [hmd, hd']
    have hquad : 0 ≤ 8 * a ^ 2 * (r ^ 2 - r) := by
      apply mul_nonneg (by positivity)
      nlinarith only [hr]
    calc
      _ = 8 * a ^ 2 * (r ^ 2 - r) + 4 * a * ((m : ℝ) * (z - y) + 2 * r * a) := by
        dsimp only [imageA, r]
        rw [sq_abs]
        ring
      _ ≥ 0 := add_nonneg hquad hlin

theorem imageB_nonneg (a y z : ℝ) (m : ℤ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) : 0 ≤ imageB a y z (m : ℝ) := by
  obtain ⟨hyl, hyu⟩ := abs_le.mp hy
  obtain ⟨hzl, hzu⟩ := abs_le.mp hz
  by_cases hm : 0 ≤ m
  · have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hk : a ≤ (2 * (m : ℝ) + 1) * a := by nlinarith [mul_nonneg hm0 ha.le]
    have hp : 0 ≤ (y + (2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a) :=
      mul_nonneg (by linarith only [hyl, hk]) (by linarith only [hzl, hk])
    dsimp only [imageB]
    nlinarith only [hp]
  · have hm1 : m ≤ -1 := by omega
    have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast hm1
    have hk : (2 * (m : ℝ) + 1) * a ≤ -a := by
      have hh := mul_le_mul_of_nonneg_right hm' ha.le
      nlinarith only [hh]
    have hp : 0 ≤ (y + (2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith only [hyu, hk]) (by linarith only [hzu, hk])
    dsimp only [imageB]
    nlinarith only [hp]

theorem imageA_affine_identity (a y z m : ℝ) :
    imageA a y z m = ((-4 * m * a - (z - y)) ^ 2) / 2 - (z - y) ^ 2 / 2 := by
  dsimp only [imageA]
  ring

theorem imageB_affine_identity (a y z m : ℝ) :
    imageB a y z m = ((2 * (z + (2 * m + 1) * a) - (z - y)) ^ 2) / 2 -
      (z - y) ^ 2 / 2 := by
  dsimp only [imageB]
  ring

theorem imageA_hasDerivAt (a y z m : ℝ) :
    HasDerivAt (fun w => imageA a w z m) (-4 * m * a) y := by
  have hh := (hasDerivAt_const y (8 * m ^ 2 * a ^ 2)).add
    (((hasDerivAt_const y z).sub (hasDerivAt_id y)).const_mul (4 * m * a))
  convert hh using 1 <;> (try funext w) <;> (try simp only [imageA, Pi.add_apply, Pi.sub_apply, id_eq]) <;> ring

theorem imageB_hasDerivAt (a y z m : ℝ) :
    HasDerivAt (fun w => imageB a w z m) (2 * (z + (2 * m + 1) * a)) y := by
  have hh := ((hasDerivAt_id y).add_const ((2 * m + 1) * a)).mul_const
    (2 * (z + (2 * m + 1) * a))
  convert hh using 1 <;> (try funext w) <;> (try simp only [imageB, Pi.add_apply, Pi.sub_apply, id_eq]) <;> ring

theorem imageB_positive_tail (a y z m : ℝ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) (hm : 0 ≤ m) :
    imageB a y z 0 + 8 * m ^ 2 * a ^ 2 ≤ imageB a y z m := by
  have hs : 0 ≤ y + z + 2 * a := by
    linarith only [(abs_le.mp hy).1, (abs_le.mp hz).1]
  have hp : 0 ≤ 4 * m * a * (y + z + 2 * a) := by positivity
  have heq : imageB a y z m - (imageB a y z 0 + 8 * m ^ 2 * a ^ 2) =
      4 * m * a * (y + z + 2 * a) := by dsimp only [imageB]; ring
  linarith only [heq, hp]

theorem imageB_negative_tail (a y z m : ℝ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) (hm : 0 ≤ m) :
    imageB a y z (-1) + 8 * m ^ 2 * a ^ 2 ≤ imageB a y z (-m - 1) := by
  have hh := imageB_positive_tail a (-y) (-z) m ha
    (by simpa only [abs_neg] using hy) (by simpa only [abs_neg] using hz) hm
  convert hh using 1 <;> dsimp only [imageB] <;> ring

theorem imageA_positive_tail (a y z m : ℝ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) (hm : 1 ≤ m) :
    imageB a y z 0 + 8 * m * (m - 1) * a ^ 2 ≤ imageA a y z m := by
  have hda : 0 ≤ z - y + 2 * a := by
    linarith only [(abs_le.mp hy).2, (abs_le.mp hz).1]
  have hstep : 0 ≤ 4 * (m - 1) * a * (z - y + 2 * a) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hm)) ha.le) hda
  have hbase : 0 ≤ 2 * (a - y) * (3 * a + z) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith only [(abs_le.mp hy).2]))
      (by linarith only [ha, (abs_le.mp hz).1])
  have heq : imageA a y z m - (imageB a y z 0 + 8 * m * (m - 1) * a ^ 2) =
      2 * (a - y) * (3 * a + z) + 4 * (m - 1) * a * (z - y + 2 * a) := by
    dsimp only [imageA, imageB]
    ring
  linarith only [heq, hbase, hstep]

theorem imageA_negative_tail (a y z m : ℝ) (ha : 0 < a)
    (hy : |y| ≤ a) (hz : |z| ≤ a) (hm : 1 ≤ m) :
    imageB a y z (-1) + 8 * m * (m - 1) * a ^ 2 ≤ imageA a y z (-m) := by
  have hh := imageA_positive_tail a (-y) (-z) m ha
    (by simpa only [abs_neg] using hy) (by simpa only [abs_neg] using hz) hm
  convert hh using 1 <;> dsimp only [imageA, imageB] <;> ring

theorem affine_slope_abs_bound (C c d : ℝ) (hC : 0 ≤ C)
    (hid : C = (c - d) ^ 2 / 2 - d ^ 2 / 2) :
    |c| ≤ 2 * |d| + Real.sqrt (2 * C) := by
  have hs0 : 0 ≤ Real.sqrt (2 * C) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * C) ^ 2 = 2 * C := Real.sq_sqrt (by positivity)
  have hprod := le_abs_self (c * d)
  rw [abs_mul] at hprod
  have hcsq : |c| ^ 2 ≤ 2 * |c| * |d| + 2 * C := by
    nlinarith only [hid, hprod, sq_abs c]
  by_contra h
  have hh : 2 * |d| + Real.sqrt (2 * C) < |c| := lt_of_not_ge h
  have hc0 : 0 < |c| := by linarith only [hh, hs0, abs_nonneg d]
  have h1 := mul_lt_mul_of_pos_right
    (show Real.sqrt (2 * C) < |c| - 2 * |d| by linarith only [hh]) hc0
  have h2 : Real.sqrt (2 * C) ^ 2 ≤ Real.sqrt (2 * C) * |c| := by
    have hp := mul_nonneg hs0 (show 0 ≤ |c| - Real.sqrt (2 * C) by
      linarith only [hh, abs_nonneg d])
    nlinarith only [hp]
  nlinarith only [hcsq, hs2, h1, h2]

end Shao.C2.IntervalImageExponents
