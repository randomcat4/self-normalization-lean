import Shao.OQ5.P52.FixedLayerPowerMoments
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Absolute convergence and exponential moments of the actual fixed kernel

All series comparisons are made on honest summability sets. The residual
retains its source absolute-set mask, and noise support is used only a.e.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem summable_of_summable_power (f : ℕ → ℝ)
    (hf : ∀ j, 0 ≤ f j) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hs : Summable (fun j => f j ^ η)) : Summable f := by
  have he := hs.tendsto_atTop_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [he] with j hj
  have hj1 : f j ≤ 1 := (Real.rpow_le_rpow_iff (hf j) (by norm_num) hη0).mp
    (by simpa only [Real.one_rpow] using hj)
  rw [Real.norm_of_nonneg (hf j)]
  exact Real.self_le_rpow_of_le_one (hf j) hj1 hη1

theorem ae_mem_fixedAbsoluteConvergenceSet :
    ∀ᵐ z : LayerObs × LayerObs ∂fixedObservationLaw.prod fixedObservationLaw,
      z ∈ fixedAbsoluteConvergenceSet := by
  filter_upwards [ae_summable_fixedLayerAbsPower (1 / 10)
    (by norm_num) (by norm_num)] with z hz
  exact summable_of_summable_power (fun j => |fixedLayerTerm j z|)
    (fun j => abs_nonneg _) (1 / 10) (by norm_num) (by norm_num) hz

theorem fixedResidualKernel_ae_eq_tsum :
    fixedResidualKernel =ᵐ[fixedObservationLaw.prod fixedObservationLaw]
      (fun z : LayerObs × LayerObs => ∑' j : ℕ, fixedLayerTerm j z) := by
  filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
  exact fixedResidualKernel_eq_tsum z hz

private theorem finite_sum_rpow_le (J : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ j, 0 ≤ f j) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (∑ j ∈ J, f j) ^ η ≤ ∑ j ∈ J, f j ^ η := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Real.zero_rpow hη0.ne', le_refl]
  | @insert a J ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Real.rpow_add_le_add_rpow (hf a)
      (Finset.sum_nonneg (fun j _ => hf j)) hη0.le hη1).trans
      (add_le_add le_rfl ih)

private theorem tsum_rpow_le (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hs : Summable f) (hp : Summable (fun j => f j ^ η)) :
    (∑' j, f j) ^ η ≤ ∑' j, f j ^ η := by
  apply le_of_tendsto' (hs.tendsto_sum_tsum_nat.rpow_const (.inr hη0.le))
  intro n
  exact (finite_sum_rpow_le (Finset.range n) f hf η hη0 hη1).trans
    (Summable.sum_le_tsum (Finset.range n)
      (fun j _ => Real.rpow_nonneg (hf j) η) hp)

private theorem measurable_absSum :
    Measurable (fun z : LayerObs × LayerObs => ∑' j : ℕ, |fixedLayerTerm j z|) := by
  simpa only [Real.norm_eq_abs] using
    Measurable.tsum (fun j => (measurable_fixedLayerTerm j).norm)

private theorem residual_abs_le_absSum (z : LayerObs × LayerObs)
    (hz : z ∈ fixedAbsoluteConvergenceSet) :
    |fixedResidualKernel z| ≤ ∑' j : ℕ, |fixedLayerTerm j z| := by
  rw [fixedResidualKernel_eq_tsum z hz]
  change Summable (fun j => |fixedLayerTerm j z|) at hz
  have hs : Summable (fun j => ‖fixedLayerTerm j z‖) := by
    simpa only [Real.norm_eq_abs] using hz
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs

theorem integrable_fixedLayerAbsSumExp (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    Integrable (fun z : LayerObs × LayerObs =>
      Real.exp («λ» * (∑' j : ℕ, |fixedLayerTerm j z|) ^ η))
      (fixedObservationLaw.prod fixedObservationLaw) := by
  apply (integrable_fixedLayerPowerSumExp η «λ» hη0 hη «hλ»).mono_nonneg
    (measurable_const.mul (measurable_absSum.pow_const η)).exp.aestronglyMeasurable
    (Eventually.of_forall (fun z => (Real.exp_pos _).le))
  filter_upwards [ae_mem_fixedAbsoluteConvergenceSet,
    ae_summable_fixedLayerAbsPower η hη0 hη] with z hz hp
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (tsum_rpow_le (fun j => |fixedLayerTerm j z|) (fun j => abs_nonneg _)
      η hη0 (by linarith) hz hp) «hλ».le)

theorem integrable_fixedResidualKernelExp (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    Integrable (fun z : LayerObs × LayerObs =>
      Real.exp («λ» * |fixedResidualKernel z| ^ η))
      (fixedObservationLaw.prod fixedObservationLaw) := by
  have hm : Measurable (fun z : LayerObs × LayerObs =>
      Real.exp («λ» * |fixedResidualKernel z| ^ η)) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using
      (measurable_const.mul (measurable_fixedResidualKernel.norm.pow_const η)).exp
  apply (integrable_fixedLayerAbsSumExp η «λ» hη0 hη «hλ»).mono_nonneg
    hm.aestronglyMeasurable (Eventually.of_forall (fun z => (Real.exp_pos _).le))
  filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) (residual_abs_le_absSum z hz) hη0.le) «hλ».le)

theorem integrable_fixedKernelExp (η «λ» : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) («hλ» : 0 < «λ») :
    Integrable (fun z : LayerObs × LayerObs =>
      Real.exp («λ» * |fixedKernel z| ^ η))
      (fixedObservationLaw.prod fixedObservationLaw) := by
  let _ : IsProbabilityMeasure fixedObservationLaw := fixedObservationLaw_isProbabilityMeasure
  have hnoise : ∀ᵐ z : LayerObs × LayerObs
      ∂fixedObservationLaw.prod fixedObservationLaw,
      z.1.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ z.2.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae ?_).mpr
    · filter_upwards [fixedObservation_first_ae_mem] with o ho
      filter_upwards [fixedObservation_first_ae_mem] with o' ho'
      exact ⟨ho, ho'⟩
    · exact (measurableSet_Icc.preimage (measurable_fst.comp measurable_fst)).inter
        (measurableSet_Icc.preimage (measurable_fst.comp measurable_snd))
  have hm : Measurable (fun z : LayerObs × LayerObs =>
      Real.exp («λ» * |fixedKernel z| ^ η)) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using
      (measurable_const.mul (measurable_fixedKernel.norm.pow_const η)).exp
  have hdom : Integrable (fun z : LayerObs × LayerObs =>
      Real.exp (2 * «λ») *
        Real.exp («λ» * (∑' j : ℕ, |fixedLayerTerm j z|) ^ η))
      (fixedObservationLaw.prod fixedObservationLaw) :=
    (integrable_fixedLayerAbsSumExp η «λ» hη0 hη «hλ»).const_mul _
  apply hdom.mono_nonneg hm.aestronglyMeasurable
    (Eventually.of_forall (fun z => (Real.exp_pos _).le))
  filter_upwards [hnoise, ae_mem_fixedAbsoluteConvergenceSet] with z hn hz
  have hη1 : η ≤ 1 := by linarith
  have hG : |z.1.1| ≤ 1 := abs_le.mpr hn.1
  have hG' : |z.2.1| ≤ 1 := abs_le.mpr hn.2
  have hGp : |z.1.1| ^ η ≤ 1 := Real.rpow_le_one (abs_nonneg _) hG hη0.le
  have hG'p : |z.2.1| ^ η ≤ 1 := Real.rpow_le_one (abs_nonneg _) hG' hη0.le
  have hrp : |fixedResidualKernel z| ^ η ≤
      (∑' j : ℕ, |fixedLayerTerm j z|) ^ η :=
    Real.rpow_le_rpow (abs_nonneg _) (residual_abs_le_absSum z hz) hη0.le
  have htriangle : |fixedKernel z| ≤ |z.1.1| + |z.2.1| + |fixedResidualKernel z| := by
    change |z.1.1 + z.2.1 + fixedResidualKernel z| ≤ _
    simpa only [Real.norm_eq_abs] using
      (norm_add_le (z.1.1 + z.2.1) (fixedResidualKernel z)).trans
        (add_le_add (norm_add_le z.1.1 z.2.1) le_rfl)
  have hp := Real.rpow_le_rpow (abs_nonneg _) htriangle hη0.le
  have hsplit1 := Real.rpow_add_le_add_rpow
    (add_nonneg (abs_nonneg z.1.1) (abs_nonneg z.2.1))
    (abs_nonneg (fixedResidualKernel z)) hη0.le hη1
  have hsplit2 := Real.rpow_add_le_add_rpow
    (abs_nonneg z.1.1) (abs_nonneg z.2.1) hη0.le hη1
  have hbound : |fixedKernel z| ^ η ≤
      2 + (∑' j : ℕ, |fixedLayerTerm j z|) ^ η := by
    linarith only [hp, hsplit1, hsplit2, hGp, hG'p, hrp]
  calc
    Real.exp («λ» * |fixedKernel z| ^ η) ≤
        Real.exp («λ» * (2 + (∑' j : ℕ, |fixedLayerTerm j z|) ^ η)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbound «hλ».le)
    _ = Real.exp (2 * «λ») *
        Real.exp («λ» * (∑' j : ℕ, |fixedLayerTerm j z|) ^ η) := by
      rw [← Real.exp_add]
      congr 1
      ring

end
end Shao.OQ5.P52
