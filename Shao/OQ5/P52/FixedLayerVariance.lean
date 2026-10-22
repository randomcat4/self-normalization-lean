import Shao.OQ5.P52.FixedLayerLpLimits
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Integration

/-!
# The actual residual second moment as a summable layer variance series

Finite prefixes are orthogonal sums of genuine centered L2 variables.
Their squares are dominated by the genuinely integrable square of the
absolute sum, and converge a.e. to the exact source-masked residual square.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem layer_pair_mean_zero (j : ℕ) :
    (∫ z : LayerObs × LayerObs, fixedLayerTerm j z
      ∂fixedObservationLaw.prod fixedObservationLaw) = 0 := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  have hi : Integrable (fixedLayerTerm j)
      (fixedObservationLaw.prod fixedObservationLaw) :=
    (fixedLayerTerm_memLp_two j).integrable (by norm_num)
  rw [integral_prod (fixedLayerTerm j) hi]
  simp only [integral_fixedLayerTerm_row_zero, integral_zero]

private theorem prefix_memLp_two (n : ℕ) :
    MemLp (fun z : LayerObs × LayerObs => ∑ j ∈ Finset.range n, fixedLayerTerm j z)
      2 (fixedObservationLaw.prod fixedObservationLaw) := by
  induction n with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty] using
      (MemLp.zero' : MemLp (fun _ : LayerObs × LayerObs => (0 : ℝ)) 2
        (fixedObservationLaw.prod fixedObservationLaw))
  | succ n ih =>
      convert ih.add (fixedLayerTerm_memLp_two n) using 1
      funext z
      exact Finset.sum_range_succ (fun j => fixedLayerTerm j z) n

private theorem prefix_second_moment (n : ℕ) :
    (∫ z : LayerObs × LayerObs,
      (∑ j ∈ Finset.range n, fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw) =
      ∑ j ∈ Finset.range n, ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw := by
  induction n with
  | zero => simp
  | succ n ih =>
      let F : LayerObs × LayerObs → ℝ := fun z =>
        ∑ j ∈ Finset.range n, fixedLayerTerm j z
      let M := fixedObservationLaw.prod fixedObservationLaw
      have hF : MemLp F 2 M := prefix_memLp_two n
      have hk : MemLp (fixedLayerTerm n) 2 M := fixedLayerTerm_memLp_two n
      have hm : Integrable (fun z => F z * fixedLayerTerm n z) M :=
        hF.integrable_mul hk
      have hind : ProbabilityTheory.IndepFun F (fixedLayerTerm n) M := by
        simpa only [Finset.sum_fn] using
          iIndepFun_fixedLayerTerms.indepFun_sum_range_succ
            (fun j => measurable_fixedLayerTerm j) n
      have hcross : (∫ z, F z * fixedLayerTerm n z ∂M) = 0 := by
        rw [hind.integral_fun_mul_eq_mul_integral
          hF.aestronglyMeasurable hk.aestronglyMeasurable,
          layer_pair_mean_zero]
        exact mul_zero _
      have he : (fun z : LayerObs × LayerObs =>
          (∑ j ∈ Finset.range (n + 1), fixedLayerTerm j z) ^ 2) =
          (fun z => F z ^ 2 + 2 * (F z * fixedLayerTerm n z) +
            (fixedLayerTerm n z) ^ 2) := by
        funext z
        simp only [Finset.sum_range_succ]
        change (F z + fixedLayerTerm n z) ^ 2 = _
        ring
      have hsum : Integrable (fun z => F z ^ 2 + 2 * (F z * fixedLayerTerm n z)) M :=
        hF.integrable_sq.add (hm.const_mul 2)
      rw [he, integral_add hsum hk.integrable_sq,
        integral_add hF.integrable_sq (hm.const_mul 2), integral_const_mul, hcross]
      change (∫ z : LayerObs × LayerObs,
        (∑ j ∈ Finset.range n, fixedLayerTerm j z) ^ 2 ∂M) + 2 * 0 +
        (∫ z : LayerObs × LayerObs, (fixedLayerTerm n z) ^ 2 ∂M) = _
      rw [ih, Finset.sum_range_succ]
      ring

private theorem hasSum_layer_second_moment :
    HasSum (fun j : ℕ =>
      ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw)
      (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw) := by
  let M := fixedObservationLaw.prod fixedObservationLaw
  let S : LayerObs × LayerObs → ℝ := fun z => ∑' j : ℕ, |fixedLayerTerm j z|
  let F : ℕ → LayerObs × LayerObs → ℝ := fun n z =>
    ∑ j ∈ Finset.range n, fixedLayerTerm j z
  have hS : MemLp S 2 M := by
    simpa only [ENNReal.ofReal_ofNat] using fixedLayerAbsSum_memLp 2 (by norm_num)
  have hr : MemLp fixedResidualKernel 2 M := by
    simpa only [ENNReal.ofReal_ofNat] using fixedResidualKernel_memLp 2 (by norm_num)
  have _hrsq : Integrable (fun z => (fixedResidualKernel z) ^ 2) M := hr.integrable_sq
  have hbound (n : ℕ) : ∀ᵐ z ∂M, ‖(F n z) ^ 2‖ ≤ (S z) ^ 2 := by
    filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
    change Summable (fun j : ℕ => |fixedLayerTerm j z|) at hz
    have hb : |F n z| ≤ S z := by
      calc
        _ = ‖F n z‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑ j ∈ Finset.range n, ‖fixedLayerTerm j z‖ := norm_sum_le _ _
        _ = ∑ j ∈ Finset.range n, |fixedLayerTerm j z| := by
          simp only [Real.norm_eq_abs]
        _ ≤ _ := hz.sum_le_tsum (Finset.range n) (fun j _ => abs_nonneg _)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (F n z)) hb 2
  have hlim : ∀ᵐ z ∂M,
      Tendsto (fun n : ℕ => (F n z) ^ 2) atTop (nhds ((fixedResidualKernel z) ^ 2)) := by
    filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
    have hsabs : Summable (fun j : ℕ => |fixedLayerTerm j z|) := by
      change Summable (fun j : ℕ => |fixedLayerTerm j z|) at hz
      exact hz
    have hs : Summable (fun j : ℕ => fixedLayerTerm j z) :=
      Summable.of_norm (by simpa only [Real.norm_eq_abs] using hsabs)
    rw [fixedResidualKernel_eq_tsum z hz]
    exact hs.tendsto_sum_tsum_nat.pow 2
  have hc := tendsto_integral_of_dominated_convergence (fun z => (S z) ^ 2)
    (fun n => (prefix_memLp_two n).aestronglyMeasurable.pow 2)
    hS.integrable_sq hbound hlim
  have hc' : Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range n, ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2 ∂M)
      atTop (nhds (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2 ∂M)) := by
    change Tendsto (fun n : ℕ => ∫ z : LayerObs × LayerObs,
      (∑ j ∈ Finset.range n, fixedLayerTerm j z) ^ 2 ∂M) atTop
      (nhds (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2 ∂M)) at hc
    simpa only [M, prefix_second_moment] using hc
  exact (hasSum_iff_tendsto_nat_of_nonneg
    (fun j => integral_nonneg (fun z => sq_nonneg (fixedLayerTerm j z))) _).mpr hc'

theorem summable_integral_fixedLayerTerm_sq :
    Summable (fun j : ℕ =>
      ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw) :=
  hasSum_layer_second_moment.summable

theorem integral_fixedResidualKernel_sq_eq_tsum :
    (∫ z : LayerObs × LayerObs, (fixedResidualKernel z) ^ 2
      ∂fixedObservationLaw.prod fixedObservationLaw) =
      ∑' j : ℕ, ∫ z : LayerObs × LayerObs, (fixedLayerTerm j z) ^ 2
        ∂fixedObservationLaw.prod fixedObservationLaw :=
  hasSum_layer_second_moment.tsum_eq.symm

end
end Shao.OQ5.P52
