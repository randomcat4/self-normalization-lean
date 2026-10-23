import Shao.OQ5.P53.SparseBalancedConcentration
import Shao.OQ5.P53.SparseBalancedEventCost
import Shao.OQ5.P53.SparseRealStatistics
import Shao.OQ5.P35.GaussianTail

/-!
# Actual fixed real-sample tail limits for p53

Local proof candidate. No kernel or independent final acceptance yet.
The finite prefix and real sample are the same fixed laws qualified earlier.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

private theorem prefix_real (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n : ℕ) (S : Set (Fin n → SparseObs)) (hS : MeasurableSet S) :
    (sparsePopulationSampleMeasure α x N).real
      {ω : ℕ → SparseObs | (fun i : Fin n => ω i.val) ∈ S} =
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real S := by
  have hm := Measure.map_apply
    (Measurable.of_eval (fun i : Fin n => measurable_pi_apply i.val)) hS
    (μ := sparsePopulationSampleMeasure α x N)
  rw [sparsePopulationSample_prefix_law α x N n] at hm
  exact congrArg ENNReal.toReal hm.symm

private theorem selected_four (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hN : SparseSelectionCore α x N) (hj : 1 ≤ j) : 4 ≤ N j := by
  have he : j - 1 + 1 = j := by omega
  have h := hN.2.2 (j - 1)
  simpa only [he] using h.2.1

theorem sparseSampleStudentizedTailProbability_eq_finite :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n : ℕ) (y : ℝ),
  sparseSampleStudentizedTailProbability α x N n y =
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
      {ω : Fin n → SparseObs | y ≤ sparseSampleStudentized α x N ω} := by
  intro α x N n y
  exact prefix_real α x N n
    {ω : Fin n → SparseObs | y ≤ sparseSampleStudentized α x N ω}
    (measurableSet_le measurable_const (measurable_sparseSampleStudentized α x N n))

theorem eventually_sparseSampleStudentizedTailProbability_ge_balanced_half :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop,
    (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent (N j) j) / 2 ≤
      sparseSampleStudentizedTailProbability α x N (N j) (x (N j)) := by
  intro α x N hα hα1 hN hSuper hSmall
  filter_upwards [eventually_sparseBalancedEvent_tail_half α x N hα hα1 hN hSuper hSmall]
    with j hj
  have hE : (sparsePopulationSampleMeasure α x N).real
      (sparseBalancedPrefixEvent (N j) j) =
      (Measure.pi (fun _ : Fin (N j) => sparsePopulationMeasure α x N)).real
        (sparseBalancedEvent (N j) j) :=
    prefix_real α x N (N j) (sparseBalancedEvent (N j) j)
      (measurableSet_sparseBalancedEvent (N j) j)
  rw [hE, sparseSampleStudentizedTailProbability_eq_finite]
  exact hj

theorem eventually_sparseRealSampleStudentizedTailProbability_ge_balanced_half :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop,
    (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent (N j) j) / 2 ≤
      sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j)) := by
  intro α x N hα hα1 hN hSuper hSmall
  simpa only [sparseRealSampleStudentizedTailProbability_eq] using
    eventually_sparseSampleStudentizedTailProbability_ge_balanced_half
      α x N hα hα1 hN hSuper hSmall

theorem eventually_sparseRealSampleStudentizedTailProbability_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop,
    0 < sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j)) := by
  intro α x N hα hα1 hN hSuper hSmall
  filter_upwards [eventually_sparseRealSampleStudentizedTailProbability_ge_balanced_half
    α x N hα hα1 hN hSuper hSmall, eventually_ge_atTop (1 : ℕ)] with j hj hj1
  have hE := sparseBalancedPrefixEvent_real_pos α x N (N j) j
    (by have h4 := selected_four α x N j hN hj1; omega) hj1
  exact (half_pos hE).trans_le hj

theorem tendsto_sparseRealSampleStudentized_logTail_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => Real.log (sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))) / x (N j) ^ 2)
    atTop (nhds 0) := by
  intro α x N hα hα1 hN hSuper hSmall
  let p : ℕ → ℝ := fun j => sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))
  let e : ℕ → ℝ := fun j =>
    (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent (N j) j)
  have hx : Tendsto (fun j : ℕ => x (N j)) atTop atTop :=
    (sparse_input_tendsto α x hα hα1 hSuper hSmall).comp
      (sparseSelectionCore_tendsto α x N hN)
  have hcraw : Tendsto (fun j : ℕ => Real.log 2 * ((x (N j))⁻¹) ^ 2)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_inv_atTop_zero.comp hx).pow 2)
  have hc : Tendsto (fun j : ℕ => Real.log 2 / x (N j) ^ 2) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, inv_pow] using hcraw
  have he : Tendsto (fun j : ℕ => Real.log (e j) / x (N j) ^ 2) atTop (nhds 0) :=
    tendsto_log_sparseBalancedPrefixEvent_cost_zero α x N hα hα1 hN hSuper hSmall
  have hlower : Tendsto (fun j : ℕ => -((Real.log (e j) - Real.log 2) / x (N j) ^ 2))
      atTop (nhds 0) := by
    simpa only [sub_div, sub_zero, neg_zero] using (he.sub hc).neg
  have hhalf := eventually_sparseRealSampleStudentizedTailProbability_ge_balanced_half
    α x N hα hα1 hN hSuper hSmall
  have hpos := eventually_sparseRealSampleStudentizedTailProbability_pos
    α x N hα hα1 hN hSuper hSmall
  have hnonneg : ∀ j : ℕ, 0 ≤ -(Real.log (p j) / x (N j) ^ 2) := by
    intro j
    have hp0 := sparseRealSampleStudentizedTailProbability_nonneg α x N (N j) (x (N j))
    have hp1 := sparseRealSampleStudentizedTailProbability_le_one α x N (N j) (x (N j))
    exact neg_nonneg.mpr
      (div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hp0 hp1) (sq_nonneg _))
  have hbound : ∀ᶠ j : ℕ in atTop,
      -(Real.log (p j) / x (N j) ^ 2) ≤ -((Real.log (e j) - Real.log 2) / x (N j) ^ 2) := by
    filter_upwards [hhalf, hpos, eventually_ge_atTop (1 : ℕ)] with j hj hp hj1
    have hE : 0 < e j := sparseBalancedPrefixEvent_real_pos α x N (N j) j
      (by have h4 := selected_four α x N j hN hj1; omega) hj1
    have hlog : Real.log (e j) - Real.log 2 ≤ Real.log (p j) := by
      have h := Real.log_le_log (half_pos hE) hj
      rw [Real.log_div (ne_of_gt hE) (by norm_num : (2 : ℝ) ≠ 0)] at h
      exact h
    exact neg_le_neg (div_le_div_of_nonneg_right hlog (sq_nonneg _))
  have hs := squeeze_zero' (Eventually.of_forall hnonneg) hbound hlower
  simpa only [neg_neg, neg_zero] using hs.neg

theorem tendsto_sparseRealSampleStudentized_logTail_normalized_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => Real.log (sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))) / (-(x (N j) ^ 2) / 2))
    atTop (nhds 0) := by
  intro α x N hα hα1 hN hSuper hSmall
  have h := tendsto_sparseRealSampleStudentized_logTail_cost_zero
    α x N hα hα1 hN hSuper hSmall
  have hs : Tendsto (fun j : ℕ => (-2 : ℝ) *
      (Real.log (sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))) /
        x (N j) ^ 2)) atTop (nhds 0) := by
    simpa using h.const_mul (-2 : ℝ)
  have heq : (fun j : ℕ => Real.log
      (sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))) /
        (-(x (N j) ^ 2) / 2)) = (fun j : ℕ => (-2 : ℝ) *
      (Real.log (sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))) /
        x (N j) ^ 2)) := by
    funext j
    by_cases hz : x (N j) = 0
    · simp [hz]
    · field_simp [hz]
  rw [heq]
  exact hs

theorem tendsto_sparseRealSampleStudentized_gaussianTail_ratio_atTop :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j)) /
    Shao.OQ5.P35.standardNormalUpperTail (x (N j))) atTop atTop := by
  intro α x N hα hα1 hN hSuper hSmall
  let p : ℕ → ℝ := fun j => sparseRealSampleStudentizedTailProbability α x N (N j) (x (N j))
  have hx : Tendsto (fun j : ℕ => x (N j)) atTop atTop :=
    (sparse_input_tendsto α x hα hα1 hSuper hSmall).comp
      (sparseSelectionCore_tendsto α x N hN)
  have harg : Tendsto (fun j : ℕ => x (N j) ^ 2 / 4) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hx
    filter_upwards [hx.eventually_ge_atTop 4] with j hj
    nlinarith
  have hexp : Tendsto (fun j : ℕ => Real.exp (x (N j) ^ 2 / 4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp harg
  have hlog := tendsto_sparseRealSampleStudentized_logTail_cost_zero
    α x N hα hα1 hN hSuper hSmall
  have hlogbound : ∀ᶠ j : ℕ in atTop,
      -(1 / 4 : ℝ) < Real.log (p j) / x (N j) ^ 2 :=
    hlog.eventually (lt_mem_nhds (by norm_num : -(1 / 4 : ℝ) < 0))
  have hpos := eventually_sparseRealSampleStudentizedTailProbability_pos
    α x N hα hα1 hN hSuper hSmall
  apply tendsto_atTop_mono' atTop _ hexp
  filter_upwards [hx.eventually_ge_atTop 4, hlogbound, hpos] with j hj hl hp
  have hxpos : 0 < x (N j) := by linarith
  have hxx : 0 < x (N j) ^ 2 := sq_pos_of_pos hxpos
  have hloglower : -(x (N j) ^ 2) / 4 ≤ Real.log (p j) := by
    have h := (lt_div_iff₀ hxx).mp hl
    linarith
  have hpbound : Real.exp (-(x (N j) ^ 2) / 4) ≤ p j := by
    have h := Real.exp_le_exp.mpr hloglower
    rw [Real.exp_log hp] at h
    exact h
  have hPsi := Shao.OQ5.P35.standardNormalUpperTail_pos (x (N j))
  have hPsibound := Shao.OQ5.P35.standardNormalUpperTail_le_exp (x (N j)) hxpos.le
  apply (le_div_iff₀ hPsi).mpr
  calc
    Real.exp (x (N j) ^ 2 / 4) * Shao.OQ5.P35.standardNormalUpperTail (x (N j)) ≤
        Real.exp (x (N j) ^ 2 / 4) * Real.exp (-(x (N j) ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hPsibound (Real.exp_pos _).le
    _ = Real.exp (-(x (N j) ^ 2) / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ p j := hpbound

end Shao.OQ5.P53
