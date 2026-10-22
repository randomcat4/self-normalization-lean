import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace Shao.OQ3
noncomputable section

open Set

def entropyRemainder (x : ℝ) : ℝ := x * Real.log x - x + 1

def binaryRelativeEntropy (p z : ℝ) : ℝ :=
  p * Real.log (p / z) + (1 - p) * Real.log ((1 - p) / (1 - z))

private theorem entropyRemainder_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt entropyRemainder (Real.log x) x := by
  change HasDerivAt (fun y : ℝ => y * Real.log y - y + 1) (Real.log x) x
  convert ((Real.hasDerivAt_mul_log hx).sub (hasDerivAt_id x)).add_const (1 : ℝ) using 1 <;>
    first | rfl | ring

private theorem entropyRemainder_continuous : Continuous entropyRemainder := by
  exact (Real.continuous_mul_log.sub continuous_id).add continuous_const

theorem entropyRemainder_quadratic_of_le_one (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (x - 1) ^ 2 / 2 ≤ entropyRemainder x := by
  let g : ℝ → ℝ := fun y => entropyRemainder y - (y - 1) ^ 2 / 2
  have hd (y : ℝ) (hy : y ≠ 0) : HasDerivAt g (Real.log y - (y - 1)) y := by
    convert (entropyRemainder_hasDerivAt y hy).sub
      ((((hasDerivAt_id y).sub_const 1).pow 2).div_const 2) using 1 <;>
      first | rfl | (dsimp only [id]; ring)
  have hanti : AntitoneOn g (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (entropyRemainder_continuous.sub
        (((continuous_id.sub continuous_const).pow 2).div_const 2)).continuousOn
    · intro y hy
      rw [interior_Icc] at hy
      exact (hd y hy.1.ne').differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hd y hy.1.ne').deriv]
      exact sub_nonpos.mpr (Real.log_le_sub_one_of_pos hy.1)
  have h := hanti ⟨hx0, hx1⟩ (by simp) hx1
  have hzero : g 1 = 0 := by norm_num [g, entropyRemainder]
  rw [hzero] at h
  exact sub_nonneg.mp h

theorem entropyRemainder_quadratic_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    (x - 1) ^ 2 / (2 * x) ≤ entropyRemainder x := by
  let g : ℝ → ℝ := fun y => entropyRemainder y - y / 2 + 1 - y⁻¹ / 2
  have hd (y : ℝ) (hy : y ≠ 0) :
      HasDerivAt g (Real.log y - 1 / 2 + (y⁻¹) ^ 2 / 2) y := by
    convert (((entropyRemainder_hasDerivAt y hy).sub
      ((hasDerivAt_id y).div_const 2)).add_const 1).sub
      (((hasDerivAt_id y).inv hy).div_const 2) using 1 <;>
      first | rfl | (dsimp only [id]; simp only [one_div, inv_pow]; ring)
  have hdiff : DifferentiableOn ℝ g (Ici 1) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
    exact (hd y hy0.ne').differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn g (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1) hdiff.continuousOn
    · exact hdiff.mono interior_subset
    · intro y hy
      have hy1 : 1 ≤ y := interior_subset hy
      have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
      rw [(hd y hy0.ne').deriv]
      nlinarith [Real.one_sub_inv_le_log_of_pos hy0, sq_nonneg (y⁻¹ - 1)]
  have h := hmono (by simp) hx hx
  have hzero : g 1 = 0 := by norm_num [g, entropyRemainder]
  rw [hzero] at h
  have hxne : x ≠ 0 := (lt_of_lt_of_le zero_lt_one hx).ne'
  have heq : g x = entropyRemainder x - (x - 1) ^ 2 / (2 * x) := by
    dsimp [g]
    field_simp [hxne]
    ring
  rw [heq] at h
  exact sub_nonneg.mp h

theorem entropyRemainder_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ entropyRemainder x := by
  rcases le_total x 1 with hx1 | hx1
  · exact le_trans (by positivity) (entropyRemainder_quadratic_of_le_one x hx hx1)
  · exact le_trans (by positivity) (entropyRemainder_quadratic_of_one_le x hx1)

theorem binaryRelativeEntropy_refined_lower (p z : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    (p - z) ^ 2 / (2 * max p z) ≤ binaryRelativeEntropy p z := by
  have hcz : 0 < 1 - z := sub_pos.mpr hz1
  have hratio : 0 ≤ p / z := div_nonneg hp0 hz0.le
  have hcomp : 0 ≤ (1 - p) / (1 - z) := div_nonneg (sub_nonneg.mpr hp1) hcz.le
  have hdecomp : binaryRelativeEntropy p z =
      z * entropyRemainder (p / z) +
        (1 - z) * entropyRemainder ((1 - p) / (1 - z)) := by
    unfold binaryRelativeEntropy entropyRemainder
    field_simp [hz0.ne', hcz.ne']
    ring
  have hcompnonneg : 0 ≤ (1 - z) * entropyRemainder ((1 - p) / (1 - z)) :=
    mul_nonneg hcz.le (entropyRemainder_nonneg _ hcomp)
  rw [hdecomp]
  rcases le_total p z with hpz | hzp
  · rw [max_eq_right hpz]
    have hr := entropyRemainder_quadratic_of_le_one (p / z) hratio
      ((div_le_one hz0).mpr hpz)
    have heq : z * ((p / z - 1) ^ 2 / 2) = (p - z) ^ 2 / (2 * z) := by
      field_simp [hz0.ne']
    calc
      (p - z) ^ 2 / (2 * z) = z * ((p / z - 1) ^ 2 / 2) := heq.symm
      _ ≤ z * entropyRemainder (p / z) := mul_le_mul_of_nonneg_left hr hz0.le
      _ ≤ _ := le_add_of_nonneg_right hcompnonneg
  · rw [max_eq_left hzp]
    have hp : 0 < p := lt_of_lt_of_le hz0 hzp
    have hr := entropyRemainder_quadratic_of_one_le (p / z)
      ((one_le_div hz0).mpr hzp)
    have heq : z * ((p / z - 1) ^ 2 / (2 * (p / z))) =
        (p - z) ^ 2 / (2 * p) := by
      field_simp [hz0.ne', hp.ne']
    calc
      (p - z) ^ 2 / (2 * p) = z * ((p / z - 1) ^ 2 / (2 * (p / z))) := heq.symm
      _ ≤ z * entropyRemainder (p / z) := mul_le_mul_of_nonneg_left hr hz0.le
      _ ≤ _ := le_add_of_nonneg_right hcompnonneg

end
end Shao.OQ3
