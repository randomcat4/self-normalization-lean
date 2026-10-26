import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Deterministic polylogarithmic admissibility window for original p51 S16

This file implements the seven declarations frozen in unit194 parent-freeze-v1.
It supplies only the deterministic growth prerequisite at p51 lines197-204.
The full natural sequences include zero; sign-sensitive identities are used
on the eventual set `1 < n`. No statistical or desired-window premise is added.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Shao.OQ5.P51

noncomputable section

def boundedPolylogHeight (C a : ℝ) (n : ℕ) : ℝ :=
  C * Real.rpow (Real.log (n : ℝ)) a

def boundedPolylogMomentOrder (t0 : ℝ) (n : ℕ) : ℝ :=
  t0 * Real.rpow (n : ℝ) (1 / 3 : ℝ)

theorem boundedPolylog_ratio_tendsto_zero
    (C a t0 : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) :
    Tendsto (fun n : ℕ =>
      (boundedPolylogHeight C a n) ^ (2 : ℕ) *
        boundedPolylogMomentOrder t0 n / (n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  have hreal : Asymptotics.IsLittleO atTop
      (fun x : ℝ => Real.rpow (Real.log x) (2 * a))
      (fun x : ℝ => Real.rpow x (2 / 3 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (2 * a) (by norm_num : (0 : ℝ) < 2 / 3)
  have hnat : Asymptotics.IsLittleO atTop
      (fun n : ℕ => Real.rpow (Real.log (n : ℝ)) (2 * a))
      (fun n : ℕ => Real.rpow (n : ℝ) (2 / 3 : ℝ)) :=
    hreal.natCast_atTop
  have hbase : Tendsto (fun n : ℕ =>
      Real.rpow (Real.log (n : ℝ)) (2 * a) /
        Real.rpow (n : ℝ) (2 / 3 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    hnat.tendsto_div_nhds_zero
  have hscaled : Tendsto (fun n : ℕ =>
      (C ^ (2 : ℕ) * t0) *
        (Real.rpow (Real.log (n : ℝ)) (2 * a) /
          Real.rpow (n : ℝ) (2 / 3 : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul (C ^ (2 : ℕ) * t0) hbase
  have heq : ∀ᶠ n : ℕ in atTop,
      (boundedPolylogHeight C a n) ^ (2 : ℕ) *
          boundedPolylogMomentOrder t0 n / (n : ℝ) =
        (C ^ (2 : ℕ) * t0) *
          (Real.rpow (Real.log (n : ℝ)) (2 * a) /
            Real.rpow (n : ℝ) (2 / 3 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn1
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    have hlogpow : (Real.rpow (Real.log (n : ℝ)) a) ^ (2 : ℕ) =
        Real.rpow (Real.log (n : ℝ)) (2 * a) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul_natCast hlog.le a (2 : ℕ)]
      congr 1
      ring
    have hthird : Real.rpow (n : ℝ) (1 / 3 : ℝ) / (n : ℝ) =
        1 / Real.rpow (n : ℝ) (2 / 3 : ℝ) := by
      calc
        _ = Real.rpow (n : ℝ) ((1 / 3 : ℝ) - (1 : ℝ)) := by
          simpa only [Real.rpow_eq_pow, Real.rpow_one] using
            (Real.rpow_sub hn0 (1 / 3 : ℝ) (1 : ℝ)).symm
        _ = Real.rpow (n : ℝ) (-(2 / 3 : ℝ)) := by
          congr 1
          norm_num
        _ = _ := by
          simpa only [Real.rpow_eq_pow, one_div] using Real.rpow_neg hn0.le (2 / 3 : ℝ)
    unfold boundedPolylogHeight boundedPolylogMomentOrder
    rw [mul_pow, hlogpow]
    calc
      _ = (C ^ (2 : ℕ) * Real.rpow (Real.log (n : ℝ)) (2 * a) * t0) *
          (Real.rpow (n : ℝ) (1 / 3 : ℝ) / (n : ℝ)) := by ring
      _ = _ := by
        rw [hthird]
        ring
  apply hscaled.congr'
  filter_upwards [heq] with n hn
  exact hn.symm

theorem eventually_boundedPolylog_window
    (C a t0 : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (ht0 : 0 < t0) :
    ∀ᶠ n : ℕ in atTop,
      1 < n ∧
        (2 : ℝ) ≤ boundedPolylogMomentOrder t0 n ∧
          (2 : ℝ) * (boundedPolylogHeight C a n) ^ (2 : ℕ) *
            boundedPolylogMomentOrder t0 n ≤ (n : ℝ) := by
  have hratio : Tendsto (fun n : ℕ =>
      (boundedPolylogHeight C a n) ^ (2 : ℕ) *
        boundedPolylogMomentOrder t0 n / (n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    boundedPolylog_ratio_tendsto_zero C a t0 hC ha ht0
  have htwice : Tendsto (fun n : ℕ =>
      (2 : ℝ) * (boundedPolylogHeight C a n) ^ (2 : ℕ) *
        boundedPolylogMomentOrder t0 n / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, mul_div_assoc, mul_assoc] using
      Filter.Tendsto.const_mul (2 : ℝ) hratio
  have hnegative : Tendsto (fun n : ℕ =>
      (-1 : ℝ) * ((2 : ℝ) * (boundedPolylogHeight C a n) ^ (2 : ℕ) *
        boundedPolylogMomentOrder t0 n / (n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul (-1 : ℝ) htwice
  have hnegativeLower : ∀ᶠ n : ℕ in atTop,
      (-1 : ℝ) < (-1 : ℝ) *
        ((2 : ℝ) * (boundedPolylogHeight C a n) ^ (2 : ℕ) *
          boundedPolylogMomentOrder t0 n / (n : ℝ)) :=
    Filter.Tendsto.eventually_const_lt (by norm_num : (-1 : ℝ) < 0) hnegative
  have hupper : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) * (boundedPolylogHeight C a n) ^ (2 : ℕ) *
        boundedPolylogMomentOrder t0 n / (n : ℝ) < (1 : ℝ) := by
    filter_upwards [hnegativeLower] with n hn
    linarith
  have hpower : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (1 / 3 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowerLower : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) / t0 ≤ Real.rpow (n : ℝ) (1 / 3 : ℝ) :=
    Filter.Tendsto.eventually_ge_atTop hpower ((2 : ℝ) / t0)
  filter_upwards [eventually_gt_atTop (1 : ℕ), hupper, hpowerLower]
    with n hn hupperN hpowerN
  refine ⟨hn, ?_, ?_⟩
  · change (2 : ℝ) ≤ t0 * Real.rpow (n : ℝ) (1 / 3 : ℝ)
    calc
      (2 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 3 : ℝ) * t0 :=
        (div_le_iff₀ ht0).mp hpowerN
      _ = _ := mul_comm _ _
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn1
    exact le_of_lt (by simpa only [one_mul] using (div_lt_iff₀ hn0).mp hupperN)

def boundedLogCutoffHeight (A tau alpha : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (A * Real.log (n : ℝ) / tau) (1 / alpha : ℝ)

theorem boundedLogCutoff_ratio_tendsto_zero
    (A tau alpha t0 : ℝ)
    (hA : 0 < A) (htau : 0 < tau) (halpha : 0 < alpha) (ht0 : 0 < t0) :
    Tendsto (fun n : ℕ =>
      (boundedLogCutoffHeight A tau alpha n) ^ (2 : ℕ) *
        boundedPolylogMomentOrder t0 n / (n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  have hCoefficient : 0 ≤ Real.rpow (A / tau) (1 / alpha : ℝ) :=
    (Real.rpow_pos_of_pos (div_pos hA htau) (1 / alpha : ℝ)).le
  have hExponent : 0 ≤ (1 / alpha : ℝ) := (div_pos zero_lt_one halpha).le
  have hgeneric : Tendsto (fun n : ℕ =>
      (boundedPolylogHeight (Real.rpow (A / tau) (1 / alpha : ℝ))
          (1 / alpha : ℝ) n) ^ (2 : ℕ) *
        boundedPolylogMomentOrder t0 n / (n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    boundedPolylog_ratio_tendsto_zero
      (Real.rpow (A / tau) (1 / alpha : ℝ)) (1 / alpha : ℝ) t0
      hCoefficient hExponent ht0
  have heq : ∀ᶠ n : ℕ in atTop,
      boundedLogCutoffHeight A tau alpha n =
        boundedPolylogHeight (Real.rpow (A / tau) (1 / alpha : ℝ))
          (1 / alpha : ℝ) n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    unfold boundedLogCutoffHeight boundedPolylogHeight
    rw [show A * Real.log (n : ℝ) / tau =
        (A / tau) * Real.log (n : ℝ) by ring]
    exact Real.mul_rpow (div_pos hA htau).le (Real.log_pos hn1).le
  apply hgeneric.congr'
  filter_upwards [heq] with n hn
  rw [hn]

theorem eventually_boundedLogCutoff_window
    (A tau alpha t0 : ℝ)
    (hA : 0 < A) (htau : 0 < tau) (halpha : 0 < alpha) (ht0 : 0 < t0) :
    ∀ᶠ n : ℕ in atTop,
      1 < n ∧
        (2 : ℝ) ≤ boundedPolylogMomentOrder t0 n ∧
          (2 : ℝ) * (boundedLogCutoffHeight A tau alpha n) ^ (2 : ℕ) *
            boundedPolylogMomentOrder t0 n ≤ (n : ℝ) := by
  have hCoefficient : 0 ≤ Real.rpow (A / tau) (1 / alpha : ℝ) :=
    (Real.rpow_pos_of_pos (div_pos hA htau) (1 / alpha : ℝ)).le
  have hExponent : 0 ≤ (1 / alpha : ℝ) := (div_pos zero_lt_one halpha).le
  have hgeneric : ∀ᶠ n : ℕ in atTop,
      1 < n ∧
        (2 : ℝ) ≤ boundedPolylogMomentOrder t0 n ∧
          (2 : ℝ) *
              (boundedPolylogHeight (Real.rpow (A / tau) (1 / alpha : ℝ))
                (1 / alpha : ℝ) n) ^ (2 : ℕ) *
            boundedPolylogMomentOrder t0 n ≤ (n : ℝ) :=
    eventually_boundedPolylog_window
      (Real.rpow (A / tau) (1 / alpha : ℝ)) (1 / alpha : ℝ) t0
      hCoefficient hExponent ht0
  have heq : ∀ᶠ n : ℕ in atTop,
      boundedLogCutoffHeight A tau alpha n =
        boundedPolylogHeight (Real.rpow (A / tau) (1 / alpha : ℝ))
          (1 / alpha : ℝ) n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    unfold boundedLogCutoffHeight boundedPolylogHeight
    rw [show A * Real.log (n : ℝ) / tau =
        (A / tau) * Real.log (n : ℝ) by ring]
    exact Real.mul_rpow (div_pos hA htau).le (Real.log_pos hn1).le
  filter_upwards [hgeneric, heq] with n hn heqN
  refine ⟨hn.1, hn.2.1, ?_⟩
  rw [heqN]
  exact hn.2.2

end

end Shao.OQ5.P51
