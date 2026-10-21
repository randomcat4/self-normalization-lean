import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Free one-step trigonometric coefficients

This is the frozen finite R0 input from `b01/proof01.md`, Section 6.  The bounds
are global in the real frequency and use only the displayed third absolute moment.
They do not identify the free cosine coefficient with a killed-kernel eigenvalue.
-/

namespace Shao.OQ4

open MeasureTheory

/-- Global cubic remainder for sine, valid at every real argument. -/
theorem sin_taylor_cubic_bound (t : ℝ) :
    |Real.sin t - t| ≤ |t| ^ 3 / 6 := by
  simpa only [abs_sub_comm] using Real.abs_sub_sin_le t

/-- Global cubic remainder for cosine, without a small-argument restriction. -/
theorem cos_taylor_cubic_bound (t : ℝ) :
    |Real.cos t - (1 - t ^ 2 / 2)| ≤ |t| ^ 3 / 6 := by
  have hnonneg : ∀ x : ℝ, 0 ≤ x →
      |Real.cos x - (1 - x ^ 2 / 2)| ≤ x ^ 3 / 6 := by
    intro x hx
    have hres : 0 ≤ Real.cos x - (1 - x ^ 2 / 2) :=
      sub_nonneg.mpr Real.one_sub_sq_div_two_le_cos
    rw [abs_of_nonneg hres]
    by_cases hlarge : 3 ≤ x
    · have hprod := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hlarge)
      nlinarith [Real.cos_le_one x]
    · let F : ℝ → ℝ := fun u => u ^ 3 / 6 - (Real.cos u - (1 - u ^ 2 / 2))
      have hderiv (u : ℝ) : deriv F u = u ^ 2 / 2 + Real.sin u - u := by
        simp (disch := fun_prop) [F]
        ring
      have hmono : MonotoneOn F (Set.Icc 0 3) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 3) (by fun_prop) (by fun_prop)
        intro u hu
        have hu' : u ∈ Set.Icc (0 : ℝ) 3 := interior_subset hu
        rw [hderiv]
        have hsin := Real.sin_ge_sub_cube hu'.1
        have hprod := mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu'.2)
        nlinarith
      have hF : F 0 ≤ F x := hmono (by norm_num) ⟨hx, le_of_not_ge hlarge⟩ hx
      have hFzero : F 0 = 0 := by norm_num [F]
      rw [hFzero] at hF
      dsimp only [F] at hF
      linarith
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using hnonneg t ht
  · have htneg : t < 0 := lt_of_not_ge ht
    simpa only [Real.cos_neg, neg_sq, abs_of_neg htneg] using
      hnonneg (-t) (neg_nonneg.mpr htneg.le)

/-- Global third-moment bounds for the ordinary one-step cosine and sine coefficients.
All three moment-integrability requirements are explicit; atoms are permitted. -/
theorem cosine_coefficients_third_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (a : ℝ)
    (hY : Integrable Y μ)
    (hYsq : Integrable (fun ω => (Y ω) ^ 2) μ)
    (hYcube : Integrable (fun ω => |Y ω| ^ 3) μ)
    (hmean : (∫ ω, Y ω ∂μ) = 0)
    (hsecond : (∫ ω, (Y ω) ^ 2 ∂μ) = 1) :
    let β : ℝ := ∫ ω, |Y ω| ^ 3 ∂μ
    let ρ : ℝ := ∫ ω, Real.cos (a * Y ω) ∂μ
    let η : ℝ := ∫ ω, Real.sin (a * Y ω) ∂μ
    |ρ - (1 - a ^ 2 / 2)| ≤ |a| ^ 3 * β / 6 ∧
      |η| ≤ |a| ^ 3 * β / 6 := by
  dsimp only
  have hcosint : Integrable (fun ω => Real.cos (a * Y ω)) μ := by
    apply Integrable.of_bound
      (Real.continuous_cos.comp_aestronglyMeasurable (hY.aestronglyMeasurable.const_mul a)) 1
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (a * Y ω)
  have hsinint : Integrable (fun ω => Real.sin (a * Y ω)) μ := by
    apply Integrable.of_bound
      (Real.continuous_sin.comp_aestronglyMeasurable (hY.aestronglyMeasurable.const_mul a)) 1
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (a * Y ω)
  let P : Ω → ℝ := fun ω => 1 - (a ^ 2 / 2) * (Y ω) ^ 2
  have hPint : Integrable P μ :=
    (integrable_const 1).sub (hYsq.const_mul (a ^ 2 / 2))
  have hPmean : (∫ ω, P ω ∂μ) = 1 - a ^ 2 / 2 := by
    dsimp only [P]
    rw [integral_sub (integrable_const 1) (hYsq.const_mul (a ^ 2 / 2)),
      integral_const_mul, hsecond]
    simp
  have hCmean : (∫ ω, Real.cos (a * Y ω) - P ω ∂μ) =
      (∫ ω, Real.cos (a * Y ω) ∂μ) - (1 - a ^ 2 / 2) := by
    rw [integral_sub hcosint hPint, hPmean]
  have hSmean : (∫ ω, Real.sin (a * Y ω) - a * Y ω ∂μ) =
      (∫ ω, Real.sin (a * Y ω) ∂μ) := by
    rw [integral_sub hsinint (hY.const_mul a), integral_const_mul, hmean, mul_zero, sub_zero]
  have hboundint : Integrable (fun ω => (|a| ^ 3 / 6) * |Y ω| ^ 3) μ :=
    hYcube.const_mul (|a| ^ 3 / 6)
  have hCbound : |∫ ω, Real.cos (a * Y ω) - P ω ∂μ| ≤
      (|a| ^ 3 / 6) * (∫ ω, |Y ω| ^ 3 ∂μ) := by
    calc
      _ ≤ ∫ ω, (|a| ^ 3 / 6) * |Y ω| ^ 3 ∂μ := by
        rw [← Real.norm_eq_abs]
        apply norm_integral_le_of_norm_le hboundint
        exact Filter.Eventually.of_forall fun ω => by
          calc
            ‖Real.cos (a * Y ω) - P ω‖ =
                |Real.cos (a * Y ω) - (1 - (a * Y ω) ^ 2 / 2)| := by
              rw [Real.norm_eq_abs]
              congr 1
              dsimp only [P]
              ring
            _ ≤ |a * Y ω| ^ 3 / 6 := cos_taylor_cubic_bound (a * Y ω)
            _ = (|a| ^ 3 / 6) * |Y ω| ^ 3 := by rw [abs_mul, mul_pow]; ring
      _ = _ := integral_const_mul _ _
  have hSbound : |∫ ω, Real.sin (a * Y ω) - a * Y ω ∂μ| ≤
      (|a| ^ 3 / 6) * (∫ ω, |Y ω| ^ 3 ∂μ) := by
    calc
      _ ≤ ∫ ω, (|a| ^ 3 / 6) * |Y ω| ^ 3 ∂μ := by
        rw [← Real.norm_eq_abs]
        apply norm_integral_le_of_norm_le hboundint
        exact Filter.Eventually.of_forall fun ω => by
          calc
            ‖Real.sin (a * Y ω) - a * Y ω‖ = |Real.sin (a * Y ω) - a * Y ω| :=
              Real.norm_eq_abs _
            _ ≤ |a * Y ω| ^ 3 / 6 := sin_taylor_cubic_bound (a * Y ω)
            _ = (|a| ^ 3 / 6) * |Y ω| ^ 3 := by rw [abs_mul, mul_pow]; ring
      _ = _ := integral_const_mul _ _
  rw [hCmean] at hCbound
  rw [hSmean] at hSbound
  constructor
  · convert hCbound using 1; ring
  · convert hSbound using 1; ring

/-- The exact R0 bounds at a_h = pi / (2h), for every positive h. -/
theorem cosine_coefficients_h_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (h : ℝ) (hh : 0 < h)
    (hY : Integrable Y μ)
    (hYsq : Integrable (fun ω => (Y ω) ^ 2) μ)
    (hYcube : Integrable (fun ω => |Y ω| ^ 3) μ)
    (hmean : (∫ ω, Y ω ∂μ) = 0)
    (hsecond : (∫ ω, (Y ω) ^ 2 ∂μ) = 1) :
    let β : ℝ := ∫ ω, |Y ω| ^ 3 ∂μ
    let ρ : ℝ := ∫ ω, Real.cos ((Real.pi / (2 * h)) * Y ω) ∂μ
    let η : ℝ := ∫ ω, Real.sin ((Real.pi / (2 * h)) * Y ω) ∂μ
    |ρ - (1 - Real.pi ^ 2 / (8 * h ^ 2))| ≤ Real.pi ^ 3 * β / (48 * h ^ 3) ∧
      |η| ≤ Real.pi ^ 3 * β / (48 * h ^ 3) := by
  have ha : 0 < Real.pi / (2 * h) := div_pos Real.pi_pos (by positivity)
  have hcenter : 1 - (Real.pi / (2 * h)) ^ 2 / 2 =
      1 - Real.pi ^ 2 / (8 * h ^ 2) := by field_simp; ring
  have hfactor : |Real.pi / (2 * h)| ^ 3 * (∫ ω, |Y ω| ^ 3 ∂μ) / 6 =
      Real.pi ^ 3 * (∫ ω, |Y ω| ^ 3 ∂μ) / (48 * h ^ 3) := by
    rw [abs_of_pos ha]
    field_simp
    ring
  simpa only [hcenter, hfactor] using
    cosine_coefficients_third_moment_bound μ Y (Real.pi / (2 * h)) hY hYsq hYcube hmean hsecond

end Shao.OQ4
