import Shao.OQ5.P52.FixedLayerAbsoluteMoments
import Mathlib.MeasureTheory.Function.UniformIntegrable

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem polynomial_le_tenth_exp (ν : ℝ) (hν : 1 ≤ ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      u ^ ν ≤ C * Real.exp (u ^ (1 / 10 : ℝ)) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (10 * ν)
  have hCpos : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hC : (1 : ℝ) ≤ (m.factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_pos m)
  refine ⟨m.factorial, hCpos.le, ?_⟩
  intro u hu
  by_cases hsmall : u ≤ 1
  · calc
      u ^ ν ≤ 1 := Real.rpow_le_one hu hsmall (by linarith)
      _ ≤ Real.exp (u ^ (1 / 10 : ℝ)) :=
        Real.one_le_exp_iff.mpr (Real.rpow_nonneg hu _)
      _ ≤ (m.factorial : ℝ) * Real.exp (u ^ (1 / 10 : ℝ)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hC)
          (Real.exp_pos (u ^ (1 / 10 : ℝ))).le]
  · have hu1 : 1 ≤ u := le_of_lt (lt_of_not_ge hsmall)
    calc
      u ^ ν ≤ u ^ ((1 / 10 : ℝ) * (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
      _ = (u ^ (1 / 10 : ℝ)) ^ m := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
      _ ≤ Real.exp (u ^ (1 / 10 : ℝ)) * (m.factorial : ℝ) :=
        (div_le_iff₀ hCpos).mp
          (Real.pow_div_factorial_le_exp (u ^ (1 / 10 : ℝ)) (Real.rpow_nonneg hu _) m)
      _ = _ := mul_comm _ _

private theorem memLp_of_tenth_exp {f : LayerObs × LayerObs → ℝ}
    (hf : Measurable f)
    (hI : Integrable (fun z => Real.exp (‖f z‖ ^ (1 / 10 : ℝ)))
      (fixedObservationLaw.prod fixedObservationLaw))
    (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp f (ENNReal.ofReal ν) (fixedObservationLaw.prod fixedObservationLaw) := by
  obtain ⟨C, hC, hbound⟩ := polynomial_le_tenth_exp ν hν
  have hp : Integrable (fun z => ‖f z‖ ^ ν)
      (fixedObservationLaw.prod fixedObservationLaw) :=
    (hI.const_mul C).mono_nonneg (hf.norm.pow_const ν).aestronglyMeasurable
      (Eventually.of_forall (fun z => Real.rpow_nonneg (norm_nonneg _) _))
      (Eventually.of_forall (fun z => hbound ‖f z‖ (norm_nonneg _)))
  have hν0 : 0 < ν := by linarith
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hν0) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hν0.le] using hp

theorem fixedLayerAbsSum_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp (fun z : LayerObs × LayerObs => ∑' j : ℕ, |fixedLayerTerm j z|)
      (ENNReal.ofReal ν) (fixedObservationLaw.prod fixedObservationLaw) := by
  have hn (z : LayerObs × LayerObs) :
      ‖∑' j : ℕ, |fixedLayerTerm j z|‖ = ∑' j : ℕ, |fixedLayerTerm j z| :=
    Real.norm_of_nonneg (tsum_nonneg (fun j => abs_nonneg _))
  apply memLp_of_tenth_exp
    (f := fun z : LayerObs × LayerObs => ∑' j : ℕ, |fixedLayerTerm j z|)
    (by simpa only [Real.norm_eq_abs] using
      (Measurable.tsum (fun j => (measurable_fixedLayerTerm j).norm))) _ ν hν
  simpa only [hn, one_mul] using
    integrable_fixedLayerAbsSumExp (1 / 10) 1 (by norm_num) (by norm_num) (by norm_num)

theorem fixedResidualKernel_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp fixedResidualKernel (ENNReal.ofReal ν)
      (fixedObservationLaw.prod fixedObservationLaw) := by
  apply memLp_of_tenth_exp measurable_fixedResidualKernel _ ν hν
  simpa only [Real.norm_eq_abs, one_mul] using
    integrable_fixedResidualKernelExp (1 / 10) 1 (by norm_num) (by norm_num) (by norm_num)

theorem fixedKernel_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp fixedKernel (ENNReal.ofReal ν)
      (fixedObservationLaw.prod fixedObservationLaw) := by
  apply memLp_of_tenth_exp measurable_fixedKernel _ ν hν
  simpa only [Real.norm_eq_abs, one_mul] using
    integrable_fixedKernelExp (1 / 10) 1 (by norm_num) (by norm_num) (by norm_num)

theorem fixedLayerPartialSum_tendsto_eLpNorm (ν : ℝ) (hν : 1 ≤ ν) :
    Tendsto (fun n : ℕ =>
      eLpNorm (fun z : LayerObs × LayerObs =>
        (∑ j ∈ Finset.range n, fixedLayerTerm j z) - fixedResidualKernel z)
        (ENNReal.ofReal ν) (fixedObservationLaw.prod fixedObservationLaw))
      atTop (nhds 0) := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  let M := fixedObservationLaw.prod fixedObservationLaw
  let p := ENNReal.ofReal ν
  let S : LayerObs × LayerObs → ℝ := fun z => ∑' j : ℕ, |fixedLayerTerm j z|
  let F : ℕ → LayerObs × LayerObs → ℝ := fun n z =>
    ∑ j ∈ Finset.range n, fixedLayerTerm j z
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.mpr hν
  have hpt : p ≠ ∞ := ENNReal.ofReal_ne_top
  have hS : MemLp S p M := fixedLayerAbsSum_memLp ν hν
  have hr : MemLp fixedResidualKernel p M := fixedResidualKernel_memLp ν hν
  have hf (n : ℕ) : Measurable (F n) :=
    (Finset.range n).measurable_sum (fun j _ => measurable_fixedLayerTerm j)
  have hdom (n : ℕ) : ∀ᵐ z ∂M, ‖F n z‖ₑ ≤ ‖S z‖ₑ := by
    filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
    change Summable (fun j : ℕ => |fixedLayerTerm j z|) at hz
    have hreal : ‖F n z‖ ≤ S z := by
      calc
        _ ≤ ∑ j ∈ Finset.range n, ‖fixedLayerTerm j z‖ := norm_sum_le _ _
        _ = ∑ j ∈ Finset.range n, |fixedLayerTerm j z| := by
          simp only [Real.norm_eq_abs]
        _ ≤ _ := hz.sum_le_tsum (Finset.range n) (fun j _ => abs_nonneg _)
    have hn : ‖S z‖ = S z := Real.norm_of_nonneg (tsum_nonneg (fun j => abs_nonneg _))
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by rw [hn]; exact hreal)
  have hui : UnifIntegrable (fun _ : ℕ => S) p M := unifIntegrable_const hp hpt hS
  have huf : UnifIntegrable F p M := hui.ae_mono
    (fun n => (hf n).aestronglyMeasurable) hdom
  have hconv : ∀ᵐ z ∂M, Tendsto (fun n : ℕ => F n z) atTop (nhds (fixedResidualKernel z)) := by
    filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
    have hsAbs : Summable (fun j : ℕ => |fixedLayerTerm j z|) := by
      change Summable (fun j : ℕ => |fixedLayerTerm j z|) at hz
      exact hz
    have hs : Summable (fun j : ℕ => fixedLayerTerm j z) :=
      Summable.of_norm (by simpa only [Real.norm_eq_abs] using hsAbs)
    rw [fixedResidualKernel_eq_tsum z hz]
    exact hs.tendsto_sum_tsum_nat
  exact tendsto_Lp_finite_of_tendsto_ae hp hpt
    (fun n => (hf n).aestronglyMeasurable) hr huf hconv

end
end Shao.OQ5.P52
