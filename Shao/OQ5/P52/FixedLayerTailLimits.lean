import Shao.OQ5.P52.FixedLayerStudentizedTail
import Shao.OQ5.P52.FixedLayerRareMassAsymptotics
import Shao.OQ5.P35.GaussianTail

/-!
# Original fixed-layer tail limits and complete-window failures

Both half-factors produce the actual quarter floor before logarithms.
The negative log denominator, log4 and rate2cost remain explicit. Only the
generic Gaussian comparison law is imported from P35; no old model enters.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

private theorem threshold_pos (j : ℕ) :
    0 < fixedLayerTailThreshold (fixedLayerN j) :=
  fixedLayerTailThreshold_pos _ (le_trans (by norm_num : 2 ≤ 8) (fixedLayerN_ge_eight j))

private theorem threshold_tendsto :
    Tendsto (fun j : ℕ => fixedLayerTailThreshold (fixedLayerN j)) atTop atTop :=
  fixedLayerTailThreshold_tendsto.comp fixedLayerN_tendsto

private theorem threshold_sq_tendsto :
    Tendsto (fun j : ℕ => (fixedLayerTailThreshold (fixedLayerN j)) ^ 2) atTop atTop :=
  threshold_tendsto.atTop_pow₀ (by decide : (2 : ℕ) ≠ 0)

private theorem log_floor_bounds (p C x : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hx : 0 < x) (hf : (1 / 4 : ℝ) * Real.exp (-2 * C) ≤ p) :
    0 ≤ Real.log p / (-(x ^ 2) / 2) ∧
      Real.log p / (-(x ^ 2) / 2) ≤ (2 * C + Real.log 4) / (x ^ 2 / 2) := by
  have hlog := Real.log_le_log
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 4) (Real.exp_pos _)) hf
  rw [Real.log_mul (by norm_num : (1 / 4 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  have hquarter : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  rw [hquarter] at hlog
  have hup : Real.log p ≤ 0 := Real.log_nonpos hp.le hp1
  have hA : 0 < x ^ 2 / 2 := div_pos (sq_pos_of_pos hx) (by norm_num)
  have hratio : Real.log p / (-(x ^ 2) / 2) = -Real.log p / (x ^ 2 / 2) := by ring
  rw [hratio]
  exact ⟨div_nonneg (by linarith) hA.le,
    (div_le_div_iff_of_pos_right hA).mpr (by linarith)⟩

private theorem log_upper_tendsto :
    Tendsto (fun j : ℕ =>
      (2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j + Real.log 4) /
        ((fixedLayerTailThreshold (fixedLayerN j)) ^ 2 / 2)) atTop (nhds 0) := by
  have h1 := fixedLayerTailThreshold_cost_tendsto_zero.const_mul (4 : ℝ)
  have h2 := threshold_sq_tendsto.const_div_atTop (2 * Real.log 4)
  have h := h1.add h2
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [] with j
  have hs : (fixedLayerTailThreshold (fixedLayerN j)) ^ 2 ≠ 0 :=
    (sq_pos_of_pos (threshold_pos j)).ne'
  field_simp [hs]
  ring

private theorem exponent_tendsto :
    Tendsto (fun j : ℕ =>
      (fixedLayerTailThreshold (fixedLayerN j)) ^ 2 / 2 -
        2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) atTop atTop := by
  have hc := fixedLayerTailThreshold_cost_tendsto_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 8)
  have hb : ∀ᶠ j : ℕ in atTop,
      (fixedLayerTailThreshold (fixedLayerN j)) ^ 2 / 4 ≤
        (fixedLayerTailThreshold (fixedLayerN j)) ^ 2 / 2 -
          2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j := by
    filter_upwards [hc] with j hj
    have hclear := (div_le_iff₀ (sq_pos_of_pos (threshold_pos j))).mp hj
    linarith
  exact tendsto_atTop_mono' atTop hb
    (threshold_sq_tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 4))

private theorem relative_lower (p C x : ℝ) (hx : 0 ≤ x)
    (hf : (1 / 4 : ℝ) * Real.exp (-2 * C) ≤ p) :
    (1 / 4 : ℝ) * Real.exp (x ^ 2 / 2 - 2 * C) ≤
      p / Shao.OQ5.P35.standardNormalUpperTail x := by
  have hPsi := Shao.OQ5.P35.standardNormalUpperTail_pos x
  have hupper := Shao.OQ5.P35.standardNormalUpperTail_le_exp x hx
  apply (le_div_iff₀ hPsi).mpr
  calc
    _ ≤ ((1 / 4 : ℝ) * Real.exp (x ^ 2 / 2 - 2 * C)) *
        Real.exp (-(x ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hupper
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    _ = (1 / 4 : ℝ) * Real.exp (-2 * C) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring
    _ ≤ _ := hf

theorem fixedSampleStudentizedTailProbability_ge_quarter_exp_eventually :
    ∀ᶠ j : ℕ in atTop,
      (1 / 4 : ℝ) * Real.exp
        (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) ≤
        fixedSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) := by
  let B : ℝ := (4 / 3 : ℝ) + 4 *
    (∫ z : (ℝ × (ℕ → Fin 3)) × (ℝ × (ℕ → Fin 3)), (fixedResidualKernel z) ^ 2
      ∂fixedObservationLaw.prod fixedObservationLaw)
  have hfactor : Tendsto (fun j : ℕ =>
      1 - B * ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
        1 / (Real.log (fixedLayerN j : ℝ)) ^ 2)) atTop (nhds 1) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (fixedLayer_conditional_error_scale_tendsto_zero.const_mul B))
  have hh := Tendsto.eventually_const_le (by norm_num : (1 / 2 : ℝ) < 1) hfactor
  filter_upwards [hh, fixedLayerRareEvent_mass_ge_half_exp_eventually] with j hj hmass
  have hpi : 0 ≤ fixedSampleLaw.real (fixedLayerRareEvent j) := ENNReal.toReal_nonneg
  calc
    (1 / 4 : ℝ) * Real.exp (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) =
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) * Real.exp
          (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j)) := by ring
    _ ≤ (1 / 2 : ℝ) * fixedSampleLaw.real (fixedLayerRareEvent j) :=
      mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ = fixedSampleLaw.real (fixedLayerRareEvent j) * (1 / 2 : ℝ) := mul_comm _ _
    _ ≤ fixedSampleLaw.real (fixedLayerRareEvent j) *
        (1 - B * ((fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
          1 / (Real.log (fixedLayerN j : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hj hpi
    _ ≤ _ := fixedSampleStudentizedTailProbability_ge_fixedLayerRareEvent_mul j

theorem fixedSampleStudentizedTailProbability_eventually_pos :
    ∀ᶠ j : ℕ in atTop,
      0 < fixedSampleStudentizedTailProbability
        (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) := by
  filter_upwards [fixedSampleStudentizedTailProbability_ge_quarter_exp_eventually] with j hj
  exact lt_of_lt_of_le
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 4) (Real.exp_pos _)) hj

theorem fixedLayer_log_tail_ratio_tendsto_zero :
    Tendsto (fun j : ℕ =>
      Real.log (fixedSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))) /
        (-((fixedLayerTailThreshold (fixedLayerN j)) ^ 2) / 2))
      atTop (nhds 0) := by
  have hb : ∀ᶠ j : ℕ in atTop,
      0 ≤ Real.log (fixedSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))) /
          (-((fixedLayerTailThreshold (fixedLayerN j)) ^ 2) / 2) ∧
      Real.log (fixedSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j))) /
          (-((fixedLayerTailThreshold (fixedLayerN j)) ^ 2) / 2) ≤
        (2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j + Real.log 4) /
          ((fixedLayerTailThreshold (fixedLayerN j)) ^ 2 / 2) := by
    filter_upwards [fixedSampleStudentizedTailProbability_ge_quarter_exp_eventually,
      fixedSampleStudentizedTailProbability_eventually_pos] with j hf hp
    exact log_floor_bounds _ _ _ hp
      (fixedSampleStudentizedTailProbability_le_one _ _) (threshold_pos j) hf
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds log_upper_tendsto
    (hb.mono (fun _ h => h.1)) (hb.mono (fun _ h => h.2))

theorem fixedLayer_relative_tail_ratio_tendsto_atTop :
    Tendsto (fun j : ℕ =>
      fixedSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) /
        Shao.OQ5.P35.standardNormalUpperTail
          (fixedLayerTailThreshold (fixedLayerN j)))
      atTop atTop := by
  have hlow : Tendsto (fun j : ℕ =>
      (1 / 4 : ℝ) * Real.exp ((fixedLayerTailThreshold (fixedLayerN j)) ^ 2 / 2 -
        2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j)) atTop atTop := by
    simpa only [Function.comp_def] using
      (Real.tendsto_exp_atTop.comp exponent_tendsto).const_mul_atTop
        (by norm_num : (0 : ℝ) < 1 / 4)
  apply tendsto_atTop_mono' atTop _ hlow
  filter_upwards [fixedSampleStudentizedTailProbability_ge_quarter_exp_eventually] with j hj
  exact relative_lower _ _ _ (threshold_pos j).le hj

theorem fixedLayer_full_log_tail_ratio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ =>
      Real.log (fixedSampleStudentizedTailProbability n (fixedLayerTailThreshold n)) /
        (-((fixedLayerTailThreshold n) ^ 2) / 2))
      atTop (nhds 1) := by
  intro h
  have hs := h.comp fixedLayerN_tendsto
  have h01 := tendsto_nhds_unique fixedLayer_log_tail_ratio_tendsto_zero hs
  norm_num at h01

theorem fixedLayer_full_relative_tail_ratio_not_tendsto_one :
    ¬ Tendsto (fun n : ℕ =>
      fixedSampleStudentizedTailProbability n (fixedLayerTailThreshold n) /
        Shao.OQ5.P35.standardNormalUpperTail (fixedLayerTailThreshold n))
      atTop (nhds 1) := by
  intro h
  have hsmall := (h.comp fixedLayerN_tendsto).eventually_le_const
    (by norm_num : (1 : ℝ) < 2)
  have hlarge := fixedLayer_relative_tail_ratio_tendsto_atTop.eventually_ge_atTop (3 : ℝ)
  obtain ⟨j, hj1, hj2⟩ := (hsmall.and hlarge).exists
  dsimp only [Function.comp_def] at hj1
  linarith

theorem fixedLayer_double_threshold_div_sixth_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (2 * fixedLayerTailThreshold n) / (n : ℝ) ^ (1 / 6 : ℝ))
      atTop (nhds 0) := by
  simpa only [mul_div_assoc, mul_zero] using
    fixedLayerTailThreshold_div_sixth_tendsto_zero.const_mul (2 : ℝ)

theorem fixedLayer_uniform_relative_tail_window_fails :
    ¬ (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∀ x : ℝ, 0 ≤ x → x ≤ 2 * fixedLayerTailThreshold n →
          |fixedSampleStudentizedTailProbability n x /
            Shao.OQ5.P35.standardNormalUpperTail x - 1| ≤ ε) := by
  intro h
  have hw := fixedLayerN_tendsto.eventually (h 1 (by norm_num))
  have hsmall : ∀ᶠ j : ℕ in atTop,
      fixedSampleStudentizedTailProbability
          (fixedLayerN j) (fixedLayerTailThreshold (fixedLayerN j)) /
        Shao.OQ5.P35.standardNormalUpperTail (fixedLayerTailThreshold (fixedLayerN j)) ≤ 2 := by
    filter_upwards [hw] with j hj
    have hx := threshold_pos j
    have hab := hj (fixedLayerTailThreshold (fixedLayerN j)) hx.le (by linarith)
    have hupper := (abs_le.mp hab).2
    linarith
  have hlarge := fixedLayer_relative_tail_ratio_tendsto_atTop.eventually_ge_atTop (3 : ℝ)
  obtain ⟨j, hj1, hj2⟩ := (hsmall.and hlarge).exists
  linarith

end
end Shao.OQ5.P52
