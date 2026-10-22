import Shao.OQ5.P52.FixedLayerGrowth
import Shao.OQ5.P52.FixedLayerCostScales

/-!
# The complete threshold and fixed dyadic tail scales

All statements are deterministic. Full natural-sequence threshold limits
are kept separate from the exact fixed-layer dyadic identities.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

def fixedLayerTailThreshold (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 6 : ℝ) / Real.log (n : ℝ)

private theorem real_nat_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop

private theorem real_N_tendsto :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ)) atTop atTop :=
  real_nat_tendsto.comp fixedLayerN_tendsto

private theorem real_nat_gt_one (n : ℕ) (hn : 2 ≤ n) : (1 : ℝ) < n := by
  have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private theorem real_N_gt_one (j : ℕ) : (1 : ℝ) < fixedLayerN j :=
  real_nat_gt_one _ (le_trans (by norm_num : 2 ≤ 8) (fixedLayerN_ge_eight j))

private theorem log_nat_tendsto :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp real_nat_tendsto

private theorem N_mul_Q_identity (j : ℕ) :
    (fixedLayerN j : ℝ) * fixedLayerQ j =
      (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)) := by
  have hN : (0 : ℝ) < fixedLayerN j := lt_trans zero_lt_one (real_N_gt_one j)
  change (fixedLayerN j : ℝ) * (fixedLayerN j : ℝ) ^ (-fixedLayerC j) = _
  calc
    _ = (fixedLayerN j : ℝ) ^ ((1 : ℝ) + -fixedLayerC j) := by
      rw [Real.rpow_add hN, Real.rpow_one]
    _ = _ := by congr 1; unfold fixedLayerC; ring

theorem fixedLayerTailThreshold_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < fixedLayerTailThreshold n := by
  unfold fixedLayerTailThreshold
  have h := real_nat_gt_one n hn
  exact div_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one h) _) (Real.log_pos h)

theorem fixedLayerTailThreshold_tendsto :
    Tendsto fixedLayerTailThreshold atTop atTop := by
  have hzero : Tendsto (fun n : ℕ =>
      Real.log (n : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero.comp
      real_nat_tendsto
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (n : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h := real_nat_gt_one n hn
    exact div_pos (Real.log_pos h) (Real.rpow_pos_of_pos (lt_trans zero_lt_one h) _)
  have hright : Tendsto (fun n : ℕ =>
      Real.log (n : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have h := hright.inv_tendsto_nhdsGT_zero
  change Tendsto (fun n : ℕ =>
    (Real.log (n : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ))⁻¹) atTop atTop at h
  change Tendsto (fun n : ℕ =>
    (n : ℝ) ^ (1 / 6 : ℝ) / Real.log (n : ℝ)) atTop atTop
  simpa only [inv_div] using h

theorem fixedLayerTailThreshold_div_sixth_tendsto_zero :
    Tendsto (fun n : ℕ => fixedLayerTailThreshold n / (n : ℝ) ^ (1 / 6 : ℝ))
      atTop (nhds 0) := by
  apply (log_nat_tendsto.const_div_atTop 1).congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnpos : (0 : ℝ) < n := lt_trans zero_lt_one (real_nat_gt_one n hn)
  have hp : (n : ℝ) ^ (1 / 6 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
  have hl : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (real_nat_gt_one n hn)).ne'
  unfold fixedLayerTailThreshold
  field_simp [hp, hl]

theorem fixedLayerTailThreshold_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => fixedLayerTailThreshold n / Real.sqrt (n : ℝ))
      atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp real_nat_tendsto
  have h := hp.mul (log_nat_tendsto.const_div_atTop 1)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnpos : (0 : ℝ) < n := lt_trans zero_lt_one (real_nat_gt_one n hn)
  rw [show -(1 / 3 : ℝ) = (1 / 6 : ℝ) - 1 / 2 by norm_num, Real.rpow_sub hnpos,
    fixedLayerTailThreshold, Real.sqrt_eq_rpow]
  ring

theorem fixedLayerTailThreshold_cost_identity (j : ℕ) :
    (fixedLayerN j : ℝ) ^ fixedLayerTau j /
        (fixedLayerTailThreshold (fixedLayerN j)) ^ 2 =
      (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)) *
        (Real.log (fixedLayerN j : ℝ)) ^ 2 := by
  have hN : (0 : ℝ) < fixedLayerN j := lt_trans zero_lt_one (real_N_gt_one j)
  have hl : Real.log (fixedLayerN j : ℝ) ≠ 0 := (Real.log_pos (real_N_gt_one j)).ne'
  have hp : ((fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)) ^ 2 =
      (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hN.le]
    congr 1
    norm_num
  have ht : fixedLayerTau j =
      (-1 / ((j + 6 : ℕ) : ℝ)) + (1 / 3 : ℝ) := by
    unfold fixedLayerTau
    ring
  rw [fixedLayerTailThreshold, div_pow, hp, ht, Real.rpow_add hN]
  field_simp [(Real.rpow_pos_of_pos hN (1 / 3 : ℝ)).ne', hl]

theorem fixedLayerTailThreshold_cost_tendsto_zero :
    Tendsto (fun j : ℕ =>
      (fixedLayerN j : ℝ) ^ fixedLayerTau j /
        (fixedLayerTailThreshold (fixedLayerN j)) ^ 2) atTop (nhds 0) := by
  exact fixedLayer_log_cost_tendsto_zero.congr'
    (Eventually.of_forall fun j => (fixedLayerTailThreshold_cost_identity j).symm)

theorem fixedLayer_N_mul_Q_tendsto_zero :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) * fixedLayerQ j) atTop (nhds 0) := by
  have hJ : Tendsto (fun j : ℕ => ((j + 6 : ℕ) : ℝ)) atTop atTop :=
    real_nat_tendsto.comp (tendsto_add_atTop_nat 6)
  have hJ2 : Tendsto (fun j : ℕ => ((j + 6 : ℕ) : ℝ) ^ 2) atTop atTop :=
    hJ.atTop_pow₀ (by decide : (2 : ℕ) ≠ 0)
  have hrate : 0 < 3 * Real.log 2 :=
    mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (3 * Real.log 2) hrate).comp hJ2
  simp only [Real.rpow_zero, one_mul] at h
  apply h.congr'
  filter_upwards [] with j
  dsimp only [Function.comp_def]
  rw [N_mul_Q_identity, fixedLayerN_rpow_neg_inv,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem fixedLayer_N_mul_P_add_Q_tendsto_zero :
    Tendsto (fun j : ℕ =>
      (fixedLayerN j : ℝ) * (fixedLayerP j + fixedLayerQ j)) atTop (nhds 0) := by
  simpa only [mul_add, zero_add] using
    fixedLayer_N_mul_P_tendsto_zero.add fixedLayer_N_mul_Q_tendsto_zero

theorem fixedLayer_conditional_error_scale_tendsto_zero :
    Tendsto (fun j : ℕ =>
      (fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ) +
        1 / (Real.log (fixedLayerN j : ℝ)) ^ 2) atTop (nhds 0) := by
  have hp : Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ (-1 / 3 : ℝ))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp real_N_tendsto
  have hl : Tendsto (fun j : ℕ => (Real.log (fixedLayerN j : ℝ)) ^ 2) atTop atTop :=
    (Real.tendsto_log_atTop.comp real_N_tendsto).atTop_pow₀ (by decide : (2 : ℕ) ≠ 0)
  simpa only [zero_add] using hp.add (hl.const_div_atTop 1)

end
end Shao.OQ5.P52
