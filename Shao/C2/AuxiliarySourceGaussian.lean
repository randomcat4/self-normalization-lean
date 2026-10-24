import Shao.C2.AuxiliarySourceEvent
import Shao.Probability.GaussianTail

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliarySourceGaussian
open MeasureTheory ProbabilityTheory

theorem auxiliary_rare_threshold_gaussian_geometry
    (x : ℝ) (hx : 1 ≤ x) :
    let a : ℝ := Real.sqrt (9 * x ^ 2 / 4 - 1)
    let y : ℝ := a - 1 / (100 * (1 + x))
    x ≤ y ∧ y ≤ 3 * x / 2 ∧
      (3 * x / 2) ^ 2 - y ^ 2 ≤ 2 := by
  intro a y
  let delta : ℝ := 1 / (100 * (1 + x))
  have hx0 : 0 ≤ x := by linarith
  have hX2 : 1 ≤ x ^ 2 := by nlinarith
  have hRad : 0 ≤ 9 * x ^ 2 / 4 - 1 := by nlinarith
  have hA0 : 0 ≤ a := Real.sqrt_nonneg _
  have hA2 : a ^ 2 = 9 * x ^ 2 / 4 - 1 := Real.sq_sqrt hRad
  have hd0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdEq : delta * (100 * (1 + x)) = 1 := by
    dsimp [delta]
    exact div_mul_cancel₀ 1 (by positivity)
  have hdX : delta * x ≤ 1 / 100 := by nlinarith
  have hdBound : delta ≤ 1 / 100 := by
    have hh := mul_nonneg hd0 hx0
    nlinarith
  have hALower : 11 * x / 10 ≤ a := by
    apply (sq_le_sq₀ (by positivity) hA0).1
    nlinarith
  have hAUpper : a ≤ 3 * x / 2 := by
    apply (sq_le_sq₀ hA0 (by positivity)).1
    nlinarith
  have hY : y = a - delta := rfl
  have hCross := mul_le_mul_of_nonneg_right hAUpper (show 0 ≤ 2 * delta by positivity)
  refine ⟨?_, ?_, ?_⟩
  · rw [hY]
    linarith
  · rw [hY]
    linarith
  · rw [hY]
    nlinarith [sq_nonneg delta]

theorem auxiliary_rare_threshold_gaussian_tail
    (x : ℝ) (hx : 1 ≤ x) :
    let y : ℝ := Real.sqrt (9 * x ^ 2 / 4 - 1) - 1 / (100 * (1 + x))
    Shao.standardNormalTail y ≤ 12 * Shao.standardNormalTail (3 * x / 2) := by
  intro y
  let u : ℝ := 3 * x / 2
  rcases auxiliary_rare_threshold_gaussian_geometry x hx with ⟨hXY, hYU, hGap⟩
  have hx0 : 0 ≤ x := by linarith
  have hy : 0 ≤ y := hx0.trans hXY
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hRatio0 : 0 ≤ (1 + u) / (1 + y) := by positivity
  have hRatio : (1 + u) / (1 + y) ≤ 2 := by
    apply (div_le_iff₀ (show 0 < 1 + y by linarith)).2
    dsimp [u]
    linarith
  have hHalf : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have hh := Real.exp_bound_div_one_sub_of_interval
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    norm_num at hh ⊢
    exact hh
  have hOne : Real.exp (1 : ℝ) ≤ 4 := by
    have heq : Real.exp (1 : ℝ) = Real.exp (1 / 2 : ℝ) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    rw [heq]
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hExp : Real.exp ((u ^ 2 - y ^ 2) / 2) ≤ 4 := by
    apply (Real.exp_le_exp.mpr (show (u ^ 2 - y ^ 2) / 2 ≤ 1 by
      change (3 * x / 2) ^ 2 - y ^ 2 ≤ 2 at hGap
      dsimp [u]
      linarith)).trans hOne
  have hTail0 : 0 ≤ Shao.standardNormalTail u :=
    (Shao.standardNormalTail_basic.2.2.1 u).1.le
  have hMills := Shao.standardNormalTail_ratio_bound u y hu hy
  calc
    Shao.standardNormalTail y ≤
        (4 / 3 : ℝ) * ((1 + u) / (1 + y)) *
          Real.exp ((u ^ 2 - y ^ 2) / 2) * Shao.standardNormalTail u := by
      convert hMills using 1 <;> ring
    _ ≤ (4 / 3 : ℝ) * 2 * 4 * Shao.standardNormalTail u := by
      gcongr
    _ ≤ 12 * Shao.standardNormalTail u := by nlinarith
    _ = _ := rfl

end Shao.C2.AuxiliarySourceGaussian
