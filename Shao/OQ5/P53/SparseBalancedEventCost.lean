import Shao.OQ5.P53.SparseBalancedMass
import Shao.OQ5.P53.SparseMassLimits

/-!
# Actual balanced-prefix-event logarithmic cost

This module covers only the event-cost part of p53 section 4, equation (8).
The measure is the already fixed infinite population sample law. In particular,
the probability in these statements is not a supplied proxy lower bound.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace Shao.OQ5.P53

theorem eventually_sparseBalancedPrefixEvent_mass_ge :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  SparseSelectionCore α x N →
  ∀ᶠ j : ℕ in atTop,
    sparsePositiveMass α x N j ^ 4 / 16 ≤
      (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent (N j) j) := by
  intro α x N hN
  have hq := (tendsto_sparsePriorMass_background_power_one α x N hN).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hq, eventually_ge_atTop 1] with j hqj hj
  have hn4 : 4 ≤ N j := by
    simpa only [Nat.sub_add_cancel hj] using (hN.2.2 (j - 1)).2.1
  have hcNat : 1 ≤ (N j).choose 2 := Nat.choose_pos (by omega)
  have hc : (1 : ℝ) ≤ ((N j).choose 2 : ℝ) := by exact_mod_cast hcNat
  have hp : 0 ≤ sparsePositiveMass α x N j ^ 4 :=
    pow_nonneg (sparsePositiveMass_nonneg α x N j) 4
  have hq0 : 0 ≤ sparsePriorMass α x N j ^ (2 * (N j - 2)) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_of_lt hqj)
  have hhalf := mul_le_mul_of_nonneg_left (le_of_lt hqj) hp
  have hchoose := mul_le_mul_of_nonneg_right hc (mul_nonneg hp hq0)
  rw [sparseBalancedPrefixEvent_positive_level_mass α x N (N j) j hj]
  nlinarith

theorem eventually_log_sparseBalancedPrefixEvent_ge :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  SparseSelectionCore α x N →
  ∀ᶠ j : ℕ in atTop,
    -(4 : ℝ) * (sparseLevelAmplitude α x N j) ^ α -
      4 * ((j : ℝ) + 2) * Real.log 2 - Real.log 16 ≤
      Real.log ((sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent (N j) j)) := by
  intro α x N hN
  filter_upwards [eventually_sparseBalancedPrefixEvent_mass_ge α x N hN,
    eventually_ge_atTop 1] with j hmass hj
  have hn4 : 4 ≤ N j := by
    simpa only [Nat.sub_add_cancel hj] using (hN.2.2 (j - 1)).2.1
  have hp : 0 < sparsePositiveMass α x N j := sparsePositiveMass_pos α x N j hj
  have hprob : 0 < (sparsePopulationSampleMeasure α x N).real
      (sparseBalancedPrefixEvent (N j) j) :=
    sparseBalancedPrefixEvent_real_pos α x N (N j) j (by omega) hj
  have hlower : 0 < sparsePositiveMass α x N j ^ 4 / 16 := by positivity
  have hlog := (Real.log_le_log_iff hlower hprob).2 hmass
  have hj0 : j ≠ 0 := by omega
  have hlogpi : Real.log (sparsePositiveMass α x N j) =
      -((j : ℝ) + 2) * Real.log 2 - (sparseLevelAmplitude α x N j) ^ α := by
    rw [sparsePositiveMass, ite_eq_right hj0, sparseDyadic,
      Real.log_mul (inv_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)))
        (Real.exp_ne_zero _),
      Real.log_inv, Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hloglower : Real.log (sparsePositiveMass α x N j ^ 4 / 16) =
      -(4 : ℝ) * (sparseLevelAmplitude α x N j) ^ α -
        4 * ((j : ℝ) + 2) * Real.log 2 - Real.log 16 := by
    rw [Real.log_div (pow_ne_zero _ hp.ne') (by norm_num), Real.log_pow, hlogpi]
    ring
  rw [hloglower] at hlog
  exact hlog

theorem tendsto_sparseLevelAmplitude_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => (sparseLevelAmplitude α x N j) ^ α / (x (N j)) ^ 2)
    atTop (nhds 0) := by
  intro α x N hα0 hα1 hN hSuper hSmall
  have hwhole := (sparseAmplitude_cost_tendsto_zero α x hα0 hα1 hSuper hSmall).comp
    (sparseSelectionCore_tendsto α x N hN)
  refine hwhole.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with j hj
  simp only [sparseLevelAmplitude, ite_eq_right (by omega : j ≠ 0), Function.comp_apply]

theorem tendsto_sparseSelectedIndex_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => (j : ℝ) / (x (N j)) ^ 2) atTop (nhds 0) := by
  intro α x N hα0 hα1 hN hSuper hSmall
  have hd : 0 < sparseDelta α := (sparse_exponent_bounds α hα0 hα1).1
  let c : ℝ := 2 * sparseDelta α * Real.log 2
  have hc : 0 < c := mul_pos (mul_pos (by norm_num) hd) (Real.log_pos (by norm_num))
  have hExp : Tendsto (fun j : ℕ => (j : ℝ) * Real.exp (-c * (j : ℝ)))
      atTop (nhds 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop)
  have hsuper := (hSuper.comp (sparseSelectionCore_tendsto α x N hN)).eventually_ge_atTop 1
  have hbound : ∀ᶠ j : ℕ in atTop,
      (j : ℝ) / (x (N j)) ^ 2 ≤ (j : ℝ) * Real.exp (-c * (j : ℝ)) := by
    filter_upwards [hsuper] with j hj
    have hn0 : 0 < N j := lt_of_lt_of_le (pow_pos (by norm_num : 0 < (2 : ℕ)) j)
      (hN.2.1 j)
    have hn0r : 0 < (N j : ℝ) := by exact_mod_cast hn0
    have hnrpow : 0 < (N j : ℝ) ^ sparseDelta α := Real.rpow_pos_of_pos hn0r _
    have hx : (N j : ℝ) ^ sparseDelta α ≤ x (N j) := by
      simpa only [one_mul] using (le_div_iff₀ hnrpow).mp hj
    have hnexp : (2 : ℝ) ^ j ≤ (N j : ℝ) := by exact_mod_cast hN.2.1 j
    have hxexp : ((2 : ℝ) ^ j) ^ sparseDelta α ≤ x (N j) :=
      (Real.rpow_le_rpow (by positivity) hnexp hd.le).trans hx
    have hbase : 0 ≤ ((2 : ℝ) ^ j) ^ sparseDelta α := Real.rpow_nonneg (by positivity) _
    have hsquare : (((2 : ℝ) ^ j) ^ sparseDelta α) ^ 2 ≤ (x (N j)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxexp)
        (add_nonneg (hbase.trans hxexp) hbase)]
    have hexp : Real.exp (c * (j : ℝ)) = (((2 : ℝ) ^ j) ^ sparseDelta α) ^ 2 := by
      rw [Real.rpow_def_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j),
        pow_two, ← Real.exp_add]
      congr 1
      rw [Real.log_pow]
      dsimp only [c]
      ring
    calc
      (j : ℝ) / (x (N j)) ^ 2 ≤ (j : ℝ) / Real.exp (c * (j : ℝ)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg j) (Real.exp_pos _) (hexp.symm ▸ hsquare)
      _ = (j : ℝ) * Real.exp (-c * (j : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        ring
  exact squeeze_zero' (Eventually.of_forall (fun j =>
    div_nonneg (Nat.cast_nonneg j) (sq_nonneg (x (N j))))) hbound hExp

theorem tendsto_log_sparseBalancedPrefixEvent_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => Real.log ((sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent (N j) j)) /
    (x (N j)) ^ 2) atTop (nhds 0) := by
  intro α x N hα0 hα1 hN hSuper hSmall
  let : IsProbabilityMeasure (sparsePopulationSampleMeasure α x N) :=
    sparsePopulationSampleMeasure_probability α x N
  have hAmp := tendsto_sparseLevelAmplitude_cost_zero α x N hα0 hα1 hN hSuper hSmall
  have hIndex := tendsto_sparseSelectedIndex_cost_zero α x N hα0 hα1 hN hSuper hSmall
  have hx := (sparse_input_tendsto α x hα0 hα1 hSuper hSmall).comp
    (sparseSelectionCore_tendsto α x N hN)
  have hInv : Tendsto (fun j : ℕ => 1 / (x (N j)) ^ 2) atTop (nhds 0) := by
    simpa only [Function.comp_apply, one_div, inv_pow, zero_pow (by decide : 2 ≠ 0)] using
      ((tendsto_inv_atTop_zero.comp hx).pow 2)
  have hUpper : Tendsto (fun j : ℕ =>
      4 * ((sparseLevelAmplitude α x N j) ^ α / (x (N j)) ^ 2) +
        (4 * Real.log 2) * ((j : ℝ) / (x (N j)) ^ 2) +
        (8 * Real.log 2 + Real.log 16) * (1 / (x (N j)) ^ 2)) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      ((hAmp.const_mul 4).add (hIndex.const_mul (4 * Real.log 2))).add
        (hInv.const_mul (8 * Real.log 2 + Real.log 16))
  have hNonneg : ∀ᶠ j : ℕ in atTop,
      0 ≤ -(Real.log ((sparsePopulationSampleMeasure α x N).real
        (sparseBalancedPrefixEvent (N j) j)) / (x (N j)) ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hn4 : 4 ≤ N j := by
      simpa only [Nat.sub_add_cancel hj] using (hN.2.2 (j - 1)).2.1
    have hprob := sparseBalancedPrefixEvent_real_pos α x N (N j) j (by omega) hj
    have hlog : Real.log ((sparsePopulationSampleMeasure α x N).real
        (sparseBalancedPrefixEvent (N j) j)) ≤ 0 :=
      Real.log_nonpos hprob.le measureReal_le_one
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hlog (sq_nonneg _))
  have hBound : ∀ᶠ j : ℕ in atTop,
      -(Real.log ((sparsePopulationSampleMeasure α x N).real
        (sparseBalancedPrefixEvent (N j) j)) / (x (N j)) ^ 2) ≤
      4 * ((sparseLevelAmplitude α x N j) ^ α / (x (N j)) ^ 2) +
        (4 * Real.log 2) * ((j : ℝ) / (x (N j)) ^ 2) +
        (8 * Real.log 2 + Real.log 16) * (1 / (x (N j)) ^ 2) := by
    filter_upwards [eventually_log_sparseBalancedPrefixEvent_ge α x N hN] with j hj
    have hdiv := div_le_div_of_nonneg_right hj (sq_nonneg (x (N j)))
    calc
      -(Real.log ((sparsePopulationSampleMeasure α x N).real
          (sparseBalancedPrefixEvent (N j) j)) / (x (N j)) ^ 2) ≤
        -((-(4 : ℝ) * (sparseLevelAmplitude α x N j) ^ α -
          4 * ((j : ℝ) + 2) * Real.log 2 - Real.log 16) / (x (N j)) ^ 2) :=
        neg_le_neg hdiv
      _ = _ := by ring
  simpa only [neg_neg, neg_zero] using (squeeze_zero' hNonneg hBound hUpper).neg

end Shao.OQ5.P53
