import Shao.OQ5.P52.FixedLayerRareEvents
import Shao.OQ5.P52.FixedLayerTailScales

/-!
# Exact asymptotics of the original fixed-layer rare-event mass

The event retains all two-element sets of target positions. The survival
factor has its original natural exponent; the logarithmic limit retains
the exact binomial factor. No conditional or Studentized-tail claim is made.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

private theorem rare_N_ge_eight (j : ℕ) : (8 : ℝ) ≤ (fixedLayerN j : ℝ) := by
  exact_mod_cast fixedLayerN_ge_eight j

private theorem rare_base_pos (j : ℕ) :
    0 < 1 - fixedLayerP j - fixedLayerQ j := by
  linarith [fixedLayerP_add_Q_lt_one j]

private theorem rare_survival_pos (j : ℕ) :
    0 < (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2) :=
  pow_pos (rare_base_pos j) _

private theorem rare_choose_identity (j : ℕ) :
    ((fixedLayerN j).choose 2 : ℝ) =
      (fixedLayerN j : ℝ) * ((fixedLayerN j : ℝ) - 1) / 2 := by
  rw [← Shao.OQ5.P35.pairCount_eq_choose, Shao.OQ5.P35.pairCount]

private theorem rare_survival_lower (j : ℕ) :
    1 - (fixedLayerN j : ℝ) * (fixedLayerP j + fixedLayerQ j) ≤
      (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2) := by
  have hs : 0 ≤ fixedLayerP j + fixedLayerQ j :=
    add_nonneg (fixedLayerP_bounds j).1.le (fixedLayerQ_bounds j).1.le
  have hm : ((fixedLayerN j - 2 : ℕ) : ℝ) ≤ (fixedLayerN j : ℝ) := by
    exact_mod_cast Nat.sub_le (fixedLayerN j) 2
  have hb : -(2 : ℝ) ≤ -(fixedLayerP j + fixedLayerQ j) := by
    linarith [fixedLayerP_add_Q_lt_one j]
  calc
    1 - (fixedLayerN j : ℝ) * (fixedLayerP j + fixedLayerQ j) ≤
        1 - ((fixedLayerN j - 2 : ℕ) : ℝ) * (fixedLayerP j + fixedLayerQ j) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_right hm hs) 1
    _ = 1 + ((fixedLayerN j - 2 : ℕ) : ℝ) *
        (-(fixedLayerP j + fixedLayerQ j)) := by ring
    _ ≤ (1 + (-(fixedLayerP j + fixedLayerQ j))) ^ (fixedLayerN j - 2) :=
      one_add_mul_le_pow hb (fixedLayerN j - 2)
    _ = (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2) := by
      congr 1
      ring

theorem fixedLayerRare_survival_tendsto_one :
    Tendsto (fun j : ℕ =>
      (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2))
      atTop (nhds 1) := by
  have hlo : Tendsto (fun j : ℕ =>
      1 - (fixedLayerN j : ℝ) * (fixedLayerP j + fixedLayerQ j))
      atTop (nhds 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub fixedLayer_N_mul_P_add_Q_tendsto_zero)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    rare_survival_lower
  intro j
  exact pow_le_one₀ (rare_base_pos j).le
    (by linarith [(fixedLayerP_bounds j).1, (fixedLayerQ_bounds j).1])

theorem fixedLayerRareEvent_mass_ge_half_P_sq_eventually :
    ∀ᶠ j : ℕ in atTop,
      (1 / 2 : ℝ) * (fixedLayerP j) ^ 2 ≤
        fixedSampleLaw.real (fixedLayerRareEvent j) := by
  have hsurvival : ∀ᶠ j : ℕ in atTop,
      (1 / 2 : ℝ) ≤ (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2) :=
    Tendsto.eventually_const_le (by norm_num : (1 / 2 : ℝ) < 1)
      fixedLayerRare_survival_tendsto_one
  filter_upwards [hsurvival] with j hj
  have hc : (1 : ℝ) ≤ ((fixedLayerN j).choose 2 : ℝ) := by
    rw [rare_choose_identity]
    nlinarith [rare_N_ge_eight j, sq_nonneg ((fixedLayerN j : ℝ) - 8)]
  rw [fixedLayerRareEvent_probability]
  calc
    (1 / 2 : ℝ) * (fixedLayerP j) ^ 2 ≤
        (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2) *
          (fixedLayerP j) ^ 2 :=
      mul_le_mul_of_nonneg_right hj (sq_nonneg _)
    _ = 1 * (fixedLayerP j) ^ 2 *
        (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2) := by ring
    _ ≤ ((fixedLayerN j).choose 2 : ℝ) * (fixedLayerP j) ^ 2 *
        (1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (rare_survival_pos j).le

private theorem rare_P_sq_exp (j : ℕ) :
    (fixedLayerP j) ^ 2 =
      Real.exp (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) := by
  rw [fixedLayerP, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem fixedLayerRareEvent_mass_ge_half_exp_eventually :
    ∀ᶠ j : ℕ in atTop,
      (1 / 2 : ℝ) * Real.exp
        (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) ≤
        fixedSampleLaw.real (fixedLayerRareEvent j) := by
  filter_upwards [fixedLayerRareEvent_mass_ge_half_P_sq_eventually] with j hj
  rwa [rare_P_sq_exp] at hj

private theorem rare_log_identity (j : ℕ) :
    Real.log (fixedSampleLaw.real (fixedLayerRareEvent j)) +
        2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j -
        2 * Real.log (fixedLayerN j : ℝ) + Real.log 2 =
      Real.log (1 - 1 / (fixedLayerN j : ℝ)) +
        Real.log ((1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2)) := by
  have hN : (0 : ℝ) < (fixedLayerN j : ℝ) := by linarith [rare_N_ge_eight j]
  have hNm : (0 : ℝ) < (fixedLayerN j : ℝ) - 1 := by
    linarith [rare_N_ge_eight j]
  have hc : (0 : ℝ) < ((fixedLayerN j).choose 2 : ℝ) := by
    rw [rare_choose_identity]
    positivity
  have hp : (fixedLayerP j) ^ 2 ≠ 0 := (pow_pos (fixedLayerP_bounds j).1 2).ne'
  have hs := (rare_survival_pos j).ne'
  have hratio : 1 - 1 / (fixedLayerN j : ℝ) =
      ((fixedLayerN j : ℝ) - 1) / (fixedLayerN j : ℝ) := by
    field_simp [hN.ne']
  rw [fixedLayerRareEvent_probability,
    Real.log_mul (mul_ne_zero hc.ne' hp) hs, Real.log_mul hc.ne' hp,
    rare_choose_identity,
    Real.log_div (mul_ne_zero hN.ne' hNm.ne') (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_mul hN.ne' hNm.ne', Real.log_pow, fixedLayerP, Real.log_exp,
    hratio, Real.log_div hNm.ne' hN.ne']
  ring

theorem fixedLayerRareEvent_log_mass_asymptotic :
    Tendsto (fun j : ℕ =>
      Real.log (fixedSampleLaw.real (fixedLayerRareEvent j)) +
        2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j -
        2 * Real.log (fixedLayerN j : ℝ) + Real.log 2)
      atTop (nhds 0) := by
  have hN : Tendsto (fun j : ℕ => (fixedLayerN j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp fixedLayerN_tendsto
  have hrecip : Tendsto (fun j : ℕ => 1 / (fixedLayerN j : ℝ)) atTop (nhds 0) :=
    hN.const_div_atTop 1
  have hratio : Tendsto (fun j : ℕ => 1 - 1 / (fixedLayerN j : ℝ))
      atTop (nhds 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hrecip)
  have hlogratio : Tendsto (fun j : ℕ => Real.log (1 - 1 / (fixedLayerN j : ℝ)))
      atTop (nhds 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hlogsurvival : Tendsto (fun j : ℕ =>
      Real.log ((1 - fixedLayerP j - fixedLayerQ j) ^ (fixedLayerN j - 2)))
      atTop (nhds 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        fixedLayerRare_survival_tendsto_one
  have hsum := hlogratio.add hlogsurvival
  simp only [add_zero] at hsum
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun j => (rare_log_identity j).symm

end
end Shao.OQ5.P52
