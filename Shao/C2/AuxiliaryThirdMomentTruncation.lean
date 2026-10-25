import Shao.C2.AuxiliaryEnergyCentered

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryThirdMomentTruncation
open MeasureTheory ProbabilityTheory

theorem auxiliary_actual_third_moment_retains_half
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hNorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    0 < 4 * beta ^ 2 ∧
      1 / 2 ≤ ∫ z : ℝ, if z ^ 2 ≤ 4 * beta ^ 2 then z ^ 2 else 0 ∂nu := by
  intro beta
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one nu h2 h3 hNorm
  have hBeta0 : 0 < beta := by linarith
  have hDen : 0 < 2 * beta := by positivity
  refine ⟨by positivity, ?_⟩
  let R : ℝ → ℝ := fun z => if z ^ 2 ≤ 4 * beta ^ 2 then z ^ 2 else 0
  have hRMeas : Measurable R :=
    Measurable.ite (measurableSet_le (measurable_id.pow_const 2) measurable_const)
      (measurable_id.pow_const 2) measurable_const
  have hRInt : Integrable R nu := by
    refine h2.mono' hRMeas.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    by_cases hz : z ^ 2 ≤ 4 * beta ^ 2
    · simpa only [R, if_pos hz, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)] using (le_refl (z ^ 2))
    · simp only [R, if_neg hz, norm_zero]
      exact sq_nonneg z
  have hPoint (z : ℝ) : z ^ 2 - |z| ^ 3 / (2 * beta) ≤ R z := by
    by_cases hz : z ^ 2 ≤ 4 * beta ^ 2
    · rw [show R z = if z ^ 2 ≤ 4 * beta ^ 2 then z ^ 2 else 0 from rfl, if_pos hz]
      exact sub_le_self _ (div_nonneg (pow_nonneg (abs_nonneg z) 3) hDen.le)
    · have hLarge : 2 * beta < |z| := by
        by_contra hh
        have hSmall : |z| ≤ 2 * beta := le_of_not_gt hh
        have hSquare := pow_le_pow_left₀ (abs_nonneg z) hSmall 2
        rw [sq_abs] at hSquare
        nlinarith [lt_of_not_ge hz]
      have hProduct : z ^ 2 * (2 * beta) ≤ |z| ^ 3 := by
        calc
          _ ≤ z ^ 2 * |z| := mul_le_mul_of_nonneg_left hLarge.le (sq_nonneg z)
          _ = _ := by rw [← sq_abs z]; ring
      have hTail : z ^ 2 ≤ |z| ^ 3 / (2 * beta) := (le_div_iff₀ hDen).2 hProduct
      rw [show R z = if z ^ 2 ≤ 4 * beta ^ 2 then z ^ 2 else 0 from rfl, if_neg hz]
      linarith
  have hLower := integral_mono (h2.sub (h3.div_const (2 * beta))) hRInt hPoint
  simp only [Pi.sub_apply] at hLower
  rw [integral_sub h2 (h3.div_const (2 * beta)), integral_div, hNorm] at hLower
  change 1 - beta / (2 * beta) ≤ ∫ z : ℝ, R z ∂nu at hLower
  have hRatio : beta / (2 * beta) = (1 : ℝ) / 2 :=
    (div_eq_iff (ne_of_gt hDen)).2 (by ring)
  change (1 : ℝ) / 2 ≤ ∫ z : ℝ, R z ∂nu
  rw [hRatio] at hLower
  linarith

end Shao.C2.AuxiliaryThirdMomentTruncation
