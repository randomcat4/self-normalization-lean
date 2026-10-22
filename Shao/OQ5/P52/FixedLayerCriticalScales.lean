import Shao.OQ5.P52.FixedLayerGrowth

/-!
# Critical fifth-root scales for the one fixed p52 family

The exact two-P exponential cost is factored before taking its limit. These
are scalar bounds and limits; an actual expectation lower bound is separate.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

private theorem N_real_pos (j : ℕ) : (0 : ℝ) < (fixedLayerN j : ℝ) := by
  have h : (8 : ℝ) ≤ (fixedLayerN j : ℝ) := by
    exact_mod_cast fixedLayerN_ge_eight j
  linarith

private theorem N_real_tendsto :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp fixedLayerN_tendsto

theorem fixedLayer_pairAA_shift_lower (j : ℕ) :
    (fixedLayerN j : ℝ) ^ (5 / 3 : ℝ) / 2 ≤
      ((fixedLayerN j : ℝ) - 4) * fixedLayerT j := by
  have hN : (8 : ℝ) ≤ (fixedLayerN j : ℝ) := by
    exact_mod_cast fixedLayerN_ge_eight j
  have hp : (fixedLayerN j : ℝ) * fixedLayerT j =
      (fixedLayerN j : ℝ) ^ (5 / 3 : ℝ) := by
    calc
      _ = (fixedLayerN j : ℝ) ^ (1 : ℝ) *
          (fixedLayerN j : ℝ) ^ (2 / 3 : ℝ) := by
        rw [Real.rpow_one, fixedLayerT_eq_rpow_N]
      _ = (fixedLayerN j : ℝ) ^ ((1 : ℝ) + 2 / 3) :=
        (Real.rpow_add (N_real_pos j) _ _).symm
      _ = _ := by congr 1; norm_num
  calc
    _ = ((fixedLayerN j : ℝ) / 2) * fixedLayerT j := by rw [← hp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (fixedLayerT_pos j).le

theorem fixedLayer_critical_radius_tendsto :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ (5 / 3 : ℝ) / 4)
      atTop atTop := by
  have h : Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ (5 / 3 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 3)).comp N_real_tendsto
  simpa only [div_eq_mul_inv] using
    h.atTop_mul_const (by norm_num : (0 : ℝ) < (4 : ℝ)⁻¹)

theorem fixedLayer_critical_radius_rpow (j : ℕ) :
    ((fixedLayerN j : ℝ) ^ (5 / 3 : ℝ) / 4) ^ (1 / 5 : ℝ) =
      (4 : ℝ) ^ (-1 / 5 : ℝ) * (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ) := by
  calc
    _ = (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ) / (4 : ℝ) ^ (1 / 5 : ℝ) := by
      rw [Real.div_rpow (Real.rpow_nonneg (N_real_pos j).le _) (by norm_num),
        ← Real.rpow_mul (N_real_pos j).le,
        show (5 / 3 : ℝ) * (1 / 5 : ℝ) = 1 / 3 by norm_num]
    _ = _ := by
      rw [show (-1 / 5 : ℝ) = -(1 / 5 : ℝ) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_eq_mul_inv]
      exact mul_comm _ _

theorem fixedLayer_critical_mass_exp_identity (j : ℕ) (lambda : ℝ) :
    (1 / 2 : ℝ) * (fixedLayerP j) ^ 2 *
      Real.exp (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) *
        (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ)) =
      (1 / 2 : ℝ) * Real.exp
        ((fixedLayerN j : ℝ) ^ (1 / 3 : ℝ) *
          (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) -
            2 * (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)))) := by
  have hs : (fixedLayerN j : ℝ) ^ fixedLayerTau j =
      (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ) *
        (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)) := by
    rw [fixedLayerTau,
      show (1 / 3 : ℝ) - 1 / ((j + 6 : ℕ) : ℝ) =
        1 / 3 + (-1 / ((j + 6 : ℕ) : ℝ)) by ring,
      Real.rpow_add (N_real_pos j)]
  have hp : (fixedLayerP j) ^ 2 =
      Real.exp (-2 * (fixedLayerN j : ℝ) ^ fixedLayerTau j) := by
    rw [fixedLayerP, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hp, mul_assoc, ← Real.exp_add]
  congr 2
  rw [hs]
  ring

private theorem negative_inv_tendsto :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  have hJ : Tendsto (fun j : ℕ => ((j + 6 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 6)
  have hJ2 := hJ.atTop_pow₀ (by decide : (2 : ℕ) ≠ 0)
  have hc : 0 < 3 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have he := Real.tendsto_exp_atBot.comp
    (hJ2.const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
  apply he.congr'
  filter_upwards [] with j
  dsimp only [Function.comp_def]
  rw [fixedLayerN_rpow_neg_inv, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem fixedLayer_critical_mass_exp_tendsto (lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (fun j : ℕ =>
      (1 / 2 : ℝ) * (fixedLayerP j) ^ 2 *
        Real.exp (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) *
          (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ)))
      atTop atTop := by
  have hN : Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ (1 / 3 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp N_real_tendsto
  have hc : 0 < lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) :=
    mul_pos hlambda (Real.rpow_pos_of_pos (by norm_num) _)
  have hb : Tendsto (fun j : ℕ => lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) -
      2 * (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)))
      atTop (nhds (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ))) := by
    simpa only [mul_zero, sub_zero] using
      tendsto_const_nhds.sub (negative_inv_tendsto.const_mul 2)
  have he := Filter.Tendsto.atTop_mul_pos hc hN hb
  have hf : Tendsto (fun j : ℕ => (1 / 2 : ℝ) *
      Real.exp ((fixedLayerN j : ℝ) ^ (1 / 3 : ℝ) *
        (lambda * (4 : ℝ) ^ (-1 / 5 : ℝ) -
          2 * (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ))))) atTop atTop := by
    simpa only [Function.comp_def, mul_comm (1 / 2 : ℝ)] using
      (Real.tendsto_exp_atTop.comp he).atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2)
  simpa only [fixedLayer_critical_mass_exp_identity] using hf

end
end Shao.OQ5.P52
