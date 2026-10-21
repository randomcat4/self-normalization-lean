import Shao.OQ3.BinaryEntropyBounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace Shao.OQ3
noncomputable section

theorem binaryRelativeEntropy_ge_first_term (p z : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    p * Real.log (p / z) - p + z ≤ binaryRelativeEntropy p z := by
  have _hfirst_ratio : 0 ≤ p / z := div_nonneg hp0 hz0.le
  have hcz : 0 < 1 - z := sub_pos.mpr hz1
  have hratio : 0 ≤ (1 - p) / (1 - z) :=
    div_nonneg (sub_nonneg.mpr hp1) hcz.le
  have h := mul_nonneg hcz.le (entropyRemainder_nonneg _ hratio)
  have heq : (1 - z) * entropyRemainder ((1 - p) / (1 - z)) =
      (1 - p) * Real.log ((1 - p) / (1 - z)) - (1 - p) + (1 - z) := by
    unfold entropyRemainder
    field_simp [hcz.ne']
  rw [heq] at h
  unfold binaryRelativeEntropy
  linarith

theorem binaryRelativeEntropy_gt_two_mul (p z : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    (hlog : 3 < Real.log (p / z)) :
    2 * p < binaryRelativeEntropy p z := by
  have h := binaryRelativeEntropy_ge_first_term p z hp0.le hp1 hz0 hz1
  nlinarith [mul_pos hp0 (sub_pos.mpr hlog)]

private theorem exp_three_le_twenty_seven : Real.exp 3 ≤ 27 := by
  have he := Real.abs_exp_sub_one_sub_id_le (by norm_num : |(1 : ℝ)| ≤ 1)
  have h1 : Real.exp 1 ≤ 3 := by
    have h := le_abs_self (Real.exp 1 - 1 - 1)
    nlinarith
  calc
    Real.exp 3 = (Real.exp 1) ^ 3 := by simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul (1 : ℝ) 3
    _ ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_nonneg 1) h1 3
    _ = 27 := by norm_num

theorem binaryRelativeEntropy_source_gap (q H R : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hH0 : 50 < H) (hH1 : H < 51) (hR0 : 0 < R) (hR1 : R ≠ 1)
    (hp0 : 0 ≤ (q * R ^ 2 - 1) / H) (hp1 : (q * R ^ 2 - 1) / H ≤ 1) :
    (7 / 200) * (R - 1) ^ 2 <
      binaryRelativeEntropy ((q * R ^ 2 - 1) / H) ((q - 1) / H) := by
  let p : ℝ := (q * R ^ 2 - 1) / H
  let z : ℝ := (q - 1) / H
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hqm : 0 < q - 1 := sub_pos.mpr hq0
  have hqm1 : q - 1 < 3 / 100 := by linarith
  have hH : 0 < H := by linarith
  have hz0 : 0 < z := div_pos hqm hH
  have hz1 : z < 1 := (div_lt_one hH).mpr (by linarith)
  have hsq : 0 < (R - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hR1)
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hbase := binaryRelativeEntropy_refined_lower p z hp0 hp1 hz0 hz1
  by_cases hRlt : R < 1
  · have hR2 : R ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hRlt) (show 0 < 1 + R by linarith)]
    have hpz : p ≤ z := by
      apply (div_le_div_iff_of_pos_right hH).mpr
      have hmul := mul_lt_mul_of_pos_left hR2 hq
      nlinarith
    rw [max_eq_right hpz] at hbase
    have heq : (p - z) ^ 2 / (2 * z) =
        (q ^ 2 * (R + 1) ^ 2 / (2 * H * (q - 1))) * (R - 1) ^ 2 := by
      dsimp [p, z]
      field_simp [hH.ne', hqm.ne']
      ring
    have hnum : 1 < q ^ 2 * (R + 1) ^ 2 := by
      have hplus : 1 < (R + 1) ^ 2 := by nlinarith [sq_nonneg R]
      calc
        1 < q ^ 2 := hq2
        _ = q ^ 2 * 1 := by ring
        _ < q ^ 2 * (R + 1) ^ 2 := mul_lt_mul_of_pos_left hplus (sq_pos_of_pos hq)
    have hprod : H * (q - 1) < 51 * (3 / 100) := by
      calc
        H * (q - 1) < 51 * (q - 1) := mul_lt_mul_of_pos_right hH1 hqm
        _ < 51 * (3 / 100) := mul_lt_mul_of_pos_left hqm1 (by norm_num)
    have hc : 7 / 200 < q ^ 2 * (R + 1) ^ 2 / (2 * H * (q - 1)) := by
      apply (lt_div_iff₀ (by positivity : 0 < 2 * H * (q - 1))).mpr
      nlinarith
    calc
      (7 / 200) * (R - 1) ^ 2 <
          (q ^ 2 * (R + 1) ^ 2 / (2 * H * (q - 1))) * (R - 1) ^ 2 :=
        mul_lt_mul_of_pos_right hc hsq
      _ = (p - z) ^ 2 / (2 * z) := heq.symm
      _ ≤ binaryRelativeEntropy p z := hbase
  · have hRgt : 1 < R := lt_of_le_of_ne (le_of_not_gt hRlt) hR1.symm
    have hR2 : 1 < R ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hRgt) (show 0 < R + 1 by linarith)]
    have hqR : R ^ 2 < q * R ^ 2 := by
      simpa using mul_lt_mul_of_pos_right hq0 (sq_pos_of_pos hR0)
    have hA : 0 < q * R ^ 2 - 1 := by linarith
    have hp : 0 < p := div_pos hA hH
    have hzp : z ≤ p := by
      apply (div_le_div_iff_of_pos_right hH).mpr
      have hmul := mul_lt_mul_of_pos_left hR2 hq
      nlinarith
    by_cases hRmid : R ≤ 3 / 2
    · rw [max_eq_left hzp] at hbase
      have heq : (p - z) ^ 2 / (2 * p) =
          (q ^ 2 * (R + 1) ^ 2 / (2 * H * (q * R ^ 2 - 1))) * (R - 1) ^ 2 := by
        dsimp [p, z]
        field_simp [hH.ne', hA.ne']
        ring
      have hcert : 0 < (R + 1) ^ 2 -
          (7 / 100) * 51 * ((103 / 100) * R ^ 2 - 1) := by
        have hid : (R + 1) ^ 2 - (7 / 100) * 51 * ((103 / 100) * R ^ 2 - 1) =
            61861 / 40000 + (3 / 2 - R) * ((26771 / 10000) * R + 40313 / 20000) := by
          ring
        rw [hid]
        exact add_pos_of_pos_of_nonneg (by norm_num)
          (mul_nonneg (sub_nonneg.mpr hRmid) (by positivity))
      have hden : H * (q * R ^ 2 - 1) < 51 * ((103 / 100) * R ^ 2 - 1) := by
        calc
          H * (q * R ^ 2 - 1) < 51 * (q * R ^ 2 - 1) :=
            mul_lt_mul_of_pos_right hH1 hA
          _ < 51 * ((103 / 100) * R ^ 2 - 1) :=
            mul_lt_mul_of_pos_left
              (sub_lt_sub_right (mul_lt_mul_of_pos_right hq1 (sq_pos_of_pos hR0)) 1)
              (by norm_num)
      have hnum : (R + 1) ^ 2 ≤ q ^ 2 * (R + 1) ^ 2 := by
        simpa using mul_le_mul_of_nonneg_right hq2.le (sq_nonneg (R + 1))
      have hc : 7 / 200 < q ^ 2 * (R + 1) ^ 2 / (2 * H * (q * R ^ 2 - 1)) := by
        apply (lt_div_iff₀ (by positivity : 0 < 2 * H * (q * R ^ 2 - 1))).mpr
        nlinarith
      calc
        (7 / 200) * (R - 1) ^ 2 <
            (q ^ 2 * (R + 1) ^ 2 / (2 * H * (q * R ^ 2 - 1))) * (R - 1) ^ 2 :=
          mul_lt_mul_of_pos_right hc hsq
        _ = (p - z) ^ 2 / (2 * p) := heq.symm
        _ ≤ binaryRelativeEntropy p z := hbase
    · have hRlarge : 3 / 2 < R := lt_of_not_ge hRmid
      have hRlarge2 : 9 / 4 ≤ R ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hRlarge.le)
          (show 0 ≤ R + 3 / 2 by linarith)]
      have hA1 : 5 / 4 < q * R ^ 2 - 1 := by linarith
      have hratio : p / z = (q * R ^ 2 - 1) / (q - 1) := by
        dsimp [p, z]
        field_simp [hH.ne', hqm.ne']
      have hratio27 : 27 < p / z := by
        rw [hratio]
        apply (lt_div_iff₀ hqm).mpr
        nlinarith
      have hlog : 3 < Real.log (p / z) :=
        (Real.lt_log_iff_exp_lt (by linarith : 0 < p / z)).mpr
          (lt_of_le_of_lt exp_three_le_twenty_seven hratio27)
      have hD := binaryRelativeEntropy_gt_two_mul p z hp hp1 hz0 hz1 hlog
      have hpoly : (7 / 200) * (R - 1) ^ 2 < 2 * (R ^ 2 - 1) / 51 := by
        have hid : 2 * (R ^ 2 - 1) / 51 - (7 / 200) * (R - 1) ^ 2 =
            (R - 1) * (43 * R + 757) / 10200 := by ring
        have hpos : 0 < (R - 1) * (43 * R + 757) / 10200 := by positivity
        linarith
      have hRminus : 0 < R ^ 2 - 1 := sub_pos.mpr hR2
      have hplower : (R ^ 2 - 1) / 51 < p := by
        calc
          (R ^ 2 - 1) / 51 < (R ^ 2 - 1) / H :=
            (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 51) hH).mpr
              (mul_lt_mul_of_pos_left hH1 hRminus)
          _ < (q * R ^ 2 - 1) / H :=
            (div_lt_div_iff_of_pos_right hH).mpr (sub_lt_sub_right hqR 1)
          _ = p := rfl
      exact lt_trans hpoly (lt_trans (by linarith : 2 * (R ^ 2 - 1) / 51 < 2 * p) hD)

end
end Shao.OQ3
