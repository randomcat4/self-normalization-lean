import Shao.OQ5.P53.SparseFixedRealCounterexample
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The two concrete original p53 section5 windows

The given power/log sequence satisfies the exact two input limits under the
original strict alpha threshold. The two-fifths example uses the fifth power.
Each instance selects one fixed real law through the actual constructor.
Only eventual positive natural arguments enter logarithm/power rewrites.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Shao.OQ5.P53

def sparseRelativeWindowExponent (p : ℝ) : ℝ := (p - 2) / (2 * p)

def sparseRelativeWindow (p : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ sparseRelativeWindowExponent p / Real.log (n : ℝ)

def sparseFifthPowerWindow (n : ℕ) : ℝ := (n : ℝ) ^ (1 / 5 : ℝ)

private theorem nat_rpow_div_log_atTop (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ r / Real.log (n : ℝ)) atTop atTop := by
  have hzero : Tendsto (fun z : ℝ => Real.log z / z ^ r) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  have hpos : ∀ᶠ z : ℝ in atTop, 0 < Real.log z / z ^ r := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
    exact div_pos (Real.log_pos hz) (Real.rpow_pos_of_pos (by linarith) r)
  have hright : Tendsto (fun z : ℝ => Real.log z / z ^ r) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_inf.2 ⟨hzero, tendsto_principal.mpr hpos⟩
  have hinv : Tendsto (fun z : ℝ => (Real.log z / z ^ r)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hright
  have hreal : Tendsto (fun z : ℝ => z ^ r / Real.log z) atTop atTop := by
    simpa only [inv_div] using hinv
  exact hreal.comp tendsto_natCast_atTop_atTop

private theorem nat_rpow_div_log_small (β : ℝ) (hβ : β < (1 / 2 : ℝ)) :
    Tendsto (fun n : ℕ => sparseRatio
      (fun k : ℕ => (k : ℝ) ^ β / Real.log (k : ℝ)) n) atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-((1 / 2 : ℝ) - β)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hβ)).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun n : ℕ =>
      (n : ℝ) ^ (-((1 / 2 : ℝ) - β)) * (Real.log (n : ℝ))⁻¹) atTop (nhds 0) := by
    simpa only [Pi.inv_apply, zero_mul] using hpow.mul hlog.inv_tendsto_atTop
  have heq : (fun n : ℕ => sparseRatio
      (fun k : ℕ => (k : ℝ) ^ β / Real.log (k : ℝ)) n) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-((1 / 2 : ℝ) - β)) * (Real.log (n : ℝ))⁻¹) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    dsimp only [sparseRatio]
    rw [Real.sqrt_eq_rpow]
    rw [show -((1 / 2 : ℝ) - β) = β - (1 / 2 : ℝ) by ring,
      Real.rpow_sub hn0]
    ring
  exact (tendsto_congr' heq).mpr hprod

theorem sparseRelativeWindowExponent_bounds :
  ∀ p : ℝ, 2 < p → 0 < sparseRelativeWindowExponent p ∧ sparseRelativeWindowExponent p < (1 / 2 : ℝ) := by
  intro p hp
  have hp0 : 0 < p := by linarith
  have hden : 0 < 2 * p := mul_pos (by norm_num) hp0
  constructor
  · exact div_pos (sub_pos.mpr hp) hden
  · change (p - 2) / (2 * p) < (1 / 2 : ℝ)
    exact (div_lt_iff₀ hden).mpr (by nlinarith)

theorem sparseDelta_lt_relativeWindowExponent :
  ∀ (p α : ℝ), 2 < p → 0 < α → α < 2 * (p - 2) / (2 * p - 1) →
  α < 1 ∧ sparseDelta α < sparseRelativeWindowExponent p := by
  intro p α hp hα hcut
  have hp0 : 0 < p := by linarith
  have hden : 0 < 2 * p - 1 := by linarith
  have hcut1 : 2 * (p - 2) / (2 * p - 1) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  have hα1 : α < 1 := hcut.trans hcut1
  have hdeltaDen : 0 < 8 - 2 * α := by linarith
  have hcutMul : α * (2 * p - 1) < 2 * (p - 2) :=
    (lt_div_iff₀ hden).mp hcut
  refine ⟨hα1, ?_⟩
  dsimp only [sparseDelta, sparseRelativeWindowExponent]
  apply (div_lt_div_iff₀ hdeltaDen (mul_pos (by norm_num) hp0)).mpr
  nlinarith only [hcutMul]

theorem sparseRelativeWindow_input_limits :
  ∀ (p α : ℝ), 2 < p → p ≤ 3 → 0 < α → α < 2 * (p - 2) / (2 * p - 1) →
  Tendsto (fun n : ℕ => sparseRelativeWindow p n / (n : ℝ) ^ sparseDelta α) atTop atTop ∧
  Tendsto (fun n : ℕ => sparseRatio (sparseRelativeWindow p) n) atTop (nhds 0) := by
  intro p α hp _hp3 hα hcut
  obtain ⟨_hβ0, hβhalf⟩ := sparseRelativeWindowExponent_bounds p hp
  obtain ⟨_hα1, hdelta⟩ := sparseDelta_lt_relativeWindowExponent p α hp hα hcut
  constructor
  · have hpow := nat_rpow_div_log_atTop
      (sparseRelativeWindowExponent p - sparseDelta α) (sub_pos.mpr hdelta)
    have heq : (fun n : ℕ => sparseRelativeWindow p n / (n : ℝ) ^ sparseDelta α) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (sparseRelativeWindowExponent p - sparseDelta α) /
          Real.log (n : ℝ)) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      dsimp only [sparseRelativeWindow]
      rw [Real.rpow_sub hn0]
      ring
    exact (tendsto_congr' heq).mpr hpow
  · exact nat_rpow_div_log_small (sparseRelativeWindowExponent p) hβhalf

theorem exists_sparseFixedRealCounterexample_relativeWindow :
  ∀ (p α : ℝ) (hα : 0 < α), 2 < p → p ≤ 3 → α < 2 * (p - 2) / (2 * p - 1) →
  ∃ N : ℕ → ℕ, SparseFixedRealCounterexample α (sparseRelativeWindow p) N hα := by
  intro p α hα hp hp3 hcut
  obtain ⟨hα1, _hdelta⟩ := sparseDelta_lt_relativeWindowExponent p α hp hα hcut
  obtain ⟨hSuper, hSmall⟩ := sparseRelativeWindow_input_limits p α hp hp3 hα hcut
  exact exists_sparseFixedRealCounterexample α (sparseRelativeWindow p) hα hα1 hSuper hSmall

theorem sparseFifthPowerWindow_input_limits :
  Tendsto (fun n : ℕ => sparseFifthPowerWindow n / (n : ℝ) ^ sparseDelta (2 / 5 : ℝ)) atTop atTop ∧
  Tendsto (fun n : ℕ => sparseRatio sparseFifthPowerWindow n) atTop (nhds 0) := by
  have hdelta : sparseDelta (2 / 5 : ℝ) = (1 / 6 : ℝ) := by
    norm_num [sparseDelta]
  constructor
  · have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 30 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 30)).comp
        tendsto_natCast_atTop_atTop
    have heq : (fun n : ℕ => sparseFifthPowerWindow n /
        (n : ℝ) ^ sparseDelta (2 / 5 : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (1 / 30 : ℝ)) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      dsimp only [sparseFifthPowerWindow]
      rw [hdelta, ← Real.rpow_sub hn0]
      norm_num
    exact (tendsto_congr' heq).mpr hpow
  · have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(3 / 10 : ℝ))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 10)).comp
        tendsto_natCast_atTop_atTop
    have heq : (fun n : ℕ => sparseRatio sparseFifthPowerWindow n) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (-(3 / 10 : ℝ))) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      dsimp only [sparseRatio, sparseFifthPowerWindow]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn0]
      norm_num
    exact (tendsto_congr' heq).mpr hpow

theorem exists_sparseFixedRealCounterexample_twoFifths :
  ∃ N : ℕ → ℕ, SparseFixedRealCounterexample (2 / 5 : ℝ) sparseFifthPowerWindow N (by norm_num) := by
  obtain ⟨hSuper, hSmall⟩ := sparseFifthPowerWindow_input_limits
  exact exists_sparseFixedRealCounterexample (2 / 5 : ℝ) sparseFifthPowerWindow
    (by norm_num) (by norm_num) hSuper hSmall

end Shao.OQ5.P53
