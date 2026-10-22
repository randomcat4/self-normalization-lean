import Shao.OQ5.P52.FixedLayerGrowth
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Scalar cost scales for the fixed p52 layers

These statements use the same coefficients at every layer. The diagonal
profile below is a scalar scale, rather than an identity for a matrix entry.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

private theorem fixedLayerN_real_ge_one (j : ℕ) :
    (1 : ℝ) ≤ (fixedLayerN j : ℝ) := by
  have h : (8 : ℝ) ≤ (fixedLayerN j : ℝ) := by
    exact_mod_cast fixedLayerN_ge_eight j
  linarith

private theorem fixedLayerN_real_pos (j : ℕ) :
    (0 : ℝ) < (fixedLayerN j : ℝ) := by
  linarith [fixedLayerN_real_ge_one j]

private theorem fixedLayerN_real_tendsto :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp fixedLayerN_tendsto

theorem fixedLayer_tau_power_lower (j : ℕ) :
    (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ) ≤
      (fixedLayerN j : ℝ) ^ fixedLayerTau j := by
  exact Real.rpow_le_rpow_of_exponent_le
    (fixedLayerN_real_ge_one j) (fixedLayerTau_bounds j).1

theorem fixedLayer_polynomial_exp_tendsto_zero (b a : ℝ) (ha : 0 < a) :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ b *
      Real.exp (-a * ((fixedLayerN j : ℝ) ^ fixedLayerTau j))) atTop (nhds 0) := by
  have hu : Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ (1 / 6 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      fixedLayerN_real_tendsto
  have hpoly (j : ℕ) :
      ((fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)) ^ (6 * b) =
        (fixedLayerN j : ℝ) ^ b := by
    rw [← Real.rpow_mul (fixedLayerN_real_pos j).le]
    congr 1
    ring
  have hcomp : Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ b *
      Real.exp (-a * ((fixedLayerN j : ℝ) ^ (1 / 6 : ℝ)))) atTop (nhds 0) := by
    simpa only [Function.comp_def, hpoly] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6 * b) a ha).comp hu
  apply squeeze_zero
    (fun j => mul_nonneg (Real.rpow_nonneg (fixedLayerN_real_pos j).le b)
      (Real.exp_pos _).le) _ hcomp
  intro j
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (fixedLayerN_real_pos j).le b)
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (fixedLayer_tau_power_lower j) (by linarith))

theorem fixedLayer_N_mul_P_tendsto_zero :
    Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) * fixedLayerP j) atTop (nhds 0) := by
  simpa only [Real.rpow_one, neg_one_mul, fixedLayerP] using
    fixedLayer_polynomial_exp_tendsto_zero 1 1 (by norm_num)

private theorem fixedLayer_T_div_Q_le_cube (j : ℕ) :
    fixedLayerT j / fixedLayerQ j ≤ (fixedLayerN j : ℝ) ^ (3 : ℝ) := by
  rw [fixedLayerT_eq_rpow_N, fixedLayerQ, ← Real.rpow_sub (fixedLayerN_real_pos j)]
  exact Real.rpow_le_rpow_of_exponent_le (fixedLayerN_real_ge_one j)
    (by linarith [(fixedLayerC_bounds j).2])

private theorem fixedLayer_T_div_Q_sq_le_cube (j : ℕ) :
    fixedLayerT j / (fixedLayerQ j) ^ 2 ≤
      (fixedLayerN j : ℝ) ^ (3 : ℝ) := by
  have hq : (fixedLayerQ j) ^ 2 =
      (fixedLayerN j : ℝ) ^ (-2 * fixedLayerC j) := by
    unfold fixedLayerQ
    rw [← Real.rpow_natCast ((fixedLayerN j : ℝ) ^ (-fixedLayerC j)) 2,
      ← Real.rpow_mul (fixedLayerN_real_pos j).le]
    congr 1
    ring
  rw [fixedLayerT_eq_rpow_N, hq, ← Real.rpow_sub (fixedLayerN_real_pos j)]
  exact Real.rpow_le_rpow_of_exponent_le (fixedLayerN_real_ge_one j)
    (by linarith [(fixedLayerC_bounds j).2])

private theorem fixedLayer_P_mul_cube_tendsto_zero :
    Tendsto (fun j : ℕ => fixedLayerP j * (fixedLayerN j : ℝ) ^ (3 : ℝ))
      atTop (nhds 0) := by
  simpa only [fixedLayerP, neg_one_mul, mul_comm] using
    fixedLayer_polynomial_exp_tendsto_zero 3 1 (by norm_num)

theorem fixedLayer_small_entry_scale_tendsto_zero :
    Tendsto (fun j : ℕ => fixedLayerP j * fixedLayerT j / fixedLayerQ j)
      atTop (nhds 0) := by
  apply squeeze_zero
    (fun j => div_nonneg
      (mul_nonneg (fixedLayerP_bounds j).1.le (fixedLayerT_pos j).le)
      (fixedLayerQ_bounds j).1.le) _ fixedLayer_P_mul_cube_tendsto_zero
  intro j
  calc
    fixedLayerP j * fixedLayerT j / fixedLayerQ j =
        fixedLayerP j * (fixedLayerT j / fixedLayerQ j) := by ring
    _ ≤ fixedLayerP j * (fixedLayerN j : ℝ) ^ (3 : ℝ) :=
      mul_le_mul_of_nonneg_left (fixedLayer_T_div_Q_le_cube j)
        (fixedLayerP_bounds j).1.le

theorem fixedLayer_diag_scale_tendsto_zero :
    Tendsto (fun j : ℕ => 3 * fixedLayerP j * fixedLayerT j / (fixedLayerQ j) ^ 2)
      atTop (nhds 0) := by
  have hlim : Tendsto
      (fun j : ℕ => 3 * (fixedLayerP j * (fixedLayerN j : ℝ) ^ (3 : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using fixedLayer_P_mul_cube_tendsto_zero.const_mul 3
  apply squeeze_zero
    (fun j => div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (fixedLayerP_bounds j).1.le)
        (fixedLayerT_pos j).le) (sq_nonneg _)) _ hlim
  intro j
  calc
    3 * fixedLayerP j * fixedLayerT j / (fixedLayerQ j) ^ 2 =
        3 * (fixedLayerP j * (fixedLayerT j / (fixedLayerQ j) ^ 2)) := by ring
    _ ≤ 3 * (fixedLayerP j * (fixedLayerN j : ℝ) ^ (3 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (fixedLayer_T_div_Q_sq_le_cube j)
          (fixedLayerP_bounds j).1.le) (by norm_num)

theorem summable_fixedLayer_exp_neg (a : ℝ) (ha : 0 < a) :
    Summable (fun j : ℕ =>
      Real.exp (-a * ((fixedLayerN j : ℝ) ^ fixedLayerTau j))) := by
  have hlinear : ∀ᶠ j : ℕ in atTop, (j : ℝ) ≤ (2 : ℝ) ^ j := by
    have hlim := tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
    have he := hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [he] with j hj
    simp only [pow_one] at hj
    have htwo : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    simpa only [one_mul] using (div_le_iff₀ htwo).mp hj
  have hdyadic (j : ℕ) :
      (2 : ℝ) ^ j ≤ (fixedLayerN j : ℝ) ^ fixedLayerTau j := by
    rw [fixedLayerN_rpow_tau]
    have hsq : 1 ≤ (j + 6) ^ 2 := by
      have hpos : 0 < (j + 6) ^ 2 := by positivity
      exact hpos
    have hm := Nat.mul_le_mul_right (j + 3) hsq
    simp only [one_mul] at hm
    have he : j ≤ (j + 6) ^ 2 * (j + 3) := (Nat.le_add_right j 3).trans hm
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he
  have hg : Summable (fun j : ℕ => (Real.exp (-a)) ^ j) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by linarith))
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [hlinear] with j hj
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-a * ((fixedLayerN j : ℝ) ^ fixedLayerTau j)) ≤
        Real.exp (-a * (j : ℝ)) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (hj.trans (hdyadic j)) (by linarith))
    _ = (Real.exp (-a)) ^ j := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private theorem fixedLayer_absorb_of_gap (j : ℕ) (δ B b : ℝ)
    (hB : 0 ≤ B)
    (hsmall : B * (fixedLayerN j : ℝ) ^ (-δ) ≤ 1 / 2)
    (hgap : δ ≤ fixedLayerTau j - b) :
    B * (fixedLayerN j : ℝ) ^ b ≤
      ((fixedLayerN j : ℝ) ^ fixedLayerTau j) / 2 := by
  have hratio :
      (fixedLayerN j : ℝ) ^ b / (fixedLayerN j : ℝ) ^ fixedLayerTau j ≤
        (fixedLayerN j : ℝ) ^ (-δ) := by
    rw [← Real.rpow_sub (fixedLayerN_real_pos j)]
    exact Real.rpow_le_rpow_of_exponent_le (fixedLayerN_real_ge_one j)
      (by linarith)
  have hbound := (mul_le_mul_of_nonneg_left hratio hB).trans hsmall
  have hquot :
      (B * (fixedLayerN j : ℝ) ^ b) /
        (fixedLayerN j : ℝ) ^ fixedLayerTau j ≤ 1 / 2 := by
    simpa only [mul_div_assoc] using hbound
  have hclear := (div_le_iff₀
    (Real.rpow_pos_of_pos (fixedLayerN_real_pos j) (fixedLayerTau j))).mp hquot
  linarith

theorem fixedLayer_eventually_absorbs_positive_powers (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    ∀ᶠ j in atTop,
      «λ» * (fixedLayerN j : ℝ) ^ (2 * η / 3) ≤
        ((fixedLayerN j : ℝ) ^ fixedLayerTau j) / 2 ∧
      «λ» * (fixedLayerN j : ℝ) ^ (5 * η / 3) ≤
        ((fixedLayerN j : ℝ) ^ fixedLayerTau j) / 2 ∧
      «λ» * (2 : ℝ) ^ η *
          (fixedLayerN j : ℝ) ^ (η * (fixedLayerC j + 2 / 3)) ≤
        ((fixedLayerN j : ℝ) ^ fixedLayerTau j) / 2 := by
  obtain ⟨δ, hδ, hgap⟩ := fixedLayer_exponent_gap η hη0 hη
  have hdecay : Tendsto (fun j : ℕ => (fixedLayerN j : ℝ) ^ (-δ))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hδ).comp fixedLayerN_real_tendsto
  have hlim1 : Tendsto (fun j : ℕ => «λ» * (fixedLayerN j : ℝ) ^ (-δ))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hdecay.const_mul «λ»
  have hlim3 : Tendsto
      (fun j : ℕ => («λ» * (2 : ℝ) ^ η) * (fixedLayerN j : ℝ) ^ (-δ))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hdecay.const_mul («λ» * (2 : ℝ) ^ η)
  have he1 := hlim1.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  have he3 := hlim3.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hgap, he1, he3] with j hj h1 h3
  exact ⟨fixedLayer_absorb_of_gap j δ «λ» (2 * η / 3) «hλ».le h1 hj.2.2,
    fixedLayer_absorb_of_gap j δ «λ» (5 * η / 3) «hλ».le h1 hj.2.1,
    fixedLayer_absorb_of_gap j δ («λ» * (2 : ℝ) ^ η)
      (η * (fixedLayerC j + 2 / 3))
      (mul_pos «hλ» (Real.rpow_pos_of_pos (by norm_num) η)).le h3 hj.1⟩

theorem fixedLayer_small_cost_exponents_neg (j : ℕ) (η : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) :
    2 * η / 3 - fixedLayerC j * (1 - η) < 0 ∧
      2 * η / 3 - 2 * fixedLayerC j * (1 - η) < 0 := by
  have hη1 : 0 < 1 - η := by linarith
  have hC := (fixedLayerC_bounds j).1
  have hprod := mul_lt_mul_of_pos_right hC hη1
  have hprodpos : 0 < fixedLayerC j * (1 - η) :=
    mul_pos (by linarith) hη1
  constructor <;> nlinarith

end
end Shao.OQ5.P52
