import Shao.OQ5.P52.FixedLayerCoefficients

/-!
# Growth and exponent separation for the fixed p52 layers

All statements concern the same source coefficients with J = j + 6.
The logarithmic cost result is a scalar limit and asserts no tail theorem.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P52

noncomputable section

private theorem sourceIndex_tendsto :
    Tendsto (fun j : ℕ => ((j + 6 : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 6)

private theorem sourceIndex_recip_tendsto :
    Tendsto (fun j : ℕ => 1 / ((j + 6 : ℕ) : ℝ)) atTop (nhds 0) :=
  sourceIndex_tendsto.const_div_atTop 1

private theorem sourceIndex_ne_zero (j : ℕ) : (j : ℝ) + 6 ≠ 0 := by
  positivity

theorem strictMono_fixedLayerN : StrictMono fixedLayerN := by
  intro i j hij
  change 2 ^ (3 * (i + 6) ^ 3) < 2 ^ (3 * (j + 6) ^ 3)
  apply pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < 2)
  exact Nat.mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ (Nat.add_lt_add_right hij 6) (Nat.zero_le _)
      (by decide : (3 : ℕ) ≠ 0)) (by decide : (0 : ℕ) < 3)

theorem fixedLayerN_tendsto : Tendsto fixedLayerN atTop atTop :=
  strictMono_fixedLayerN.tendsto_atTop

theorem fixedLayerC_tendsto : Tendsto fixedLayerC atTop (nhds 1) := by
  change Tendsto (fun j : ℕ => 1 + 1 / ((j + 6 : ℕ) : ℝ)) atTop (nhds 1)
  simpa only [add_zero] using sourceIndex_recip_tendsto.const_add 1

theorem fixedLayerTau_tendsto : Tendsto fixedLayerTau atTop (nhds (1 / 3)) := by
  change Tendsto (fun j : ℕ => (1 / 3 : ℝ) - 1 / ((j + 6 : ℕ) : ℝ)) atTop (nhds (1 / 3))
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub sourceIndex_recip_tendsto :
      Tendsto (fun j : ℕ => (1 / 3 : ℝ) - 1 / ((j + 6 : ℕ) : ℝ))
        atTop (nhds (1 / 3 - 0)))

theorem fixedLayer_log_N (j : ℕ) :
    Real.log (fixedLayerN j : ℝ) =
      3 * (((j + 6 : ℕ) : ℝ) ^ 3) * Real.log 2 := by
  simp only [fixedLayerN, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]

theorem fixedLayerN_rpow_tau (j : ℕ) :
    (fixedLayerN j : ℝ) ^ fixedLayerTau j =
      (2 : ℝ) ^ ((j + 6) ^ 2 * (j + 3)) := by
  have hexponent :
      ((3 * (j + 6) ^ 3 : ℕ) : ℝ) * fixedLayerTau j =
        (((j + 6) ^ 2 * (j + 3) : ℕ) : ℝ) := by
    simp only [fixedLayerTau, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add]
    field_simp [sourceIndex_ne_zero j]
    ring
  unfold fixedLayerN
  rw [Nat.cast_pow, Nat.cast_ofNat,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) (3 * (j + 6) ^ 3)
      (fixedLayerTau j),
    hexponent, Real.rpow_natCast]

theorem fixedLayerN_rpow_neg_inv (j : ℕ) :
    (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)) =
      (2 : ℝ) ^ (-3 * (((j + 6 : ℕ) : ℝ) ^ 2)) := by
  have hexponent :
      ((3 * (j + 6) ^ 3 : ℕ) : ℝ) * (-1 / ((j + 6 : ℕ) : ℝ)) =
        -3 * (((j + 6 : ℕ) : ℝ) ^ 2) := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add]
    field_simp [sourceIndex_ne_zero j]
  unfold fixedLayerN
  rw [Nat.cast_pow, Nat.cast_ofNat,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) (3 * (j + 6) ^ 3)
      (-1 / ((j + 6 : ℕ) : ℝ)),
    hexponent]

theorem fixedLayer_exponent_gap (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 5) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop,
      δ ≤ fixedLayerTau j - η * (fixedLayerC j + 2 / 3) ∧
      δ ≤ fixedLayerTau j - 5 * η / 3 ∧
      δ ≤ fixedLayerTau j - 2 * η / 3 := by
  let δ : ℝ := (1 - 5 * η) / 6
  have hlim1 :
      Tendsto (fun j => fixedLayerTau j - η * (fixedLayerC j + 2 / 3)) atTop
        (nhds (1 / 3 - η * (1 + 2 / 3))) :=
    fixedLayerTau_tendsto.sub ((fixedLayerC_tendsto.add_const (2 / 3 : ℝ)).const_mul η)
  have hlim2 :
      Tendsto (fun j => fixedLayerTau j - 5 * η / 3) atTop
        (nhds (1 / 3 - 5 * η / 3)) :=
    fixedLayerTau_tendsto.sub tendsto_const_nhds
  have hlim3 :
      Tendsto (fun j => fixedLayerTau j - 2 * η / 3) atTop
        (nhds (1 / 3 - 2 * η / 3)) :=
    fixedLayerTau_tendsto.sub tendsto_const_nhds
  refine ⟨δ, ?_, ?_⟩
  · dsimp [δ]
    linarith
  · have he1 : ∀ᶠ j in atTop, δ ≤ fixedLayerTau j - η * (fixedLayerC j + 2 / 3) :=
      Tendsto.eventually_const_le (by dsimp [δ]; linarith) hlim1
    have he2 : ∀ᶠ j in atTop, δ ≤ fixedLayerTau j - 5 * η / 3 :=
      Tendsto.eventually_const_le (by dsimp [δ]; linarith) hlim2
    have he3 : ∀ᶠ j in atTop, δ ≤ fixedLayerTau j - 2 * η / 3 :=
      Tendsto.eventually_const_le (by dsimp [δ]; linarith) hlim3
    exact he1.and (he2.and he3)

theorem fixedLayer_log_cost_tendsto_zero :
    Tendsto (fun j : ℕ =>
      (fixedLayerN j : ℝ) ^ (-1 / ((j + 6 : ℕ) : ℝ)) *
        (Real.log (fixedLayerN j : ℝ)) ^ 2) atTop (nhds 0) := by
  have hJ2 : Tendsto (fun j : ℕ => (((j + 6 : ℕ) : ℝ) ^ 2)) atTop atTop :=
    sourceIndex_tendsto.atTop_pow₀ (by decide : (2 : ℕ) ≠ 0)
  have hrate : 0 < 3 * Real.log 2 :=
    mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hbase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 (3 * Real.log 2) hrate).comp hJ2
  have hlim := hbase.const_mul (9 * (Real.log 2) ^ 2)
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [] with j
  dsimp only [Function.comp_def]
  rw [fixedLayerN_rpow_neg_inv, fixedLayer_log_N,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show Real.log 2 * (-3 * (((j + 6 : ℕ) : ℝ) ^ 2)) =
    -(3 * Real.log 2) * (((j + 6 : ℕ) : ℝ) ^ 2) by ring]
  rw [Real.rpow_ofNat]
  ring

end
end Shao.OQ5.P52
