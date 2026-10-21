import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum

/-!
# Canonical L2 edge primitives

Source: p50 lines169–208, used by p52 lines88–108. Pair and triple laws
are derived from the actual independent observation family. No symmetry,
row-energy formula, conditional law or tail conclusion is asserted here.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P50

noncomputable section

private theorem marginal_map
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} {ν : Measure E} {X : ι → Ω → E}
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν) (i : ι) :
    μ.map (X i) = ν := by
  simpa using (hLaw i).map_eq

private theorem pair_preserving
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν] {X : ι → Ω → E}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (i j : ι) (hij : i ≠ j) :
    MeasurePreserving (fun ω => (X i ω, X j ω)) μ (ν.prod ν) := by
  refine ⟨(hX i).prodMk (hX j), ?_⟩
  calc
    μ.map (fun ω => (X i ω, X j ω)) = (μ.map (X i)).prod (μ.map (X j)) :=
      (indepFun_iff_map_prod_eq_prod_map_map
        (hX i).aemeasurable (hX j).aemeasurable).mp (hIndep.indepFun hij)
    _ = ν.prod ν := by rw [marginal_map hLaw i, marginal_map hLaw j]

private theorem triple_preserving
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν] {X : ι → Ω → E}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MeasurePreserving (fun ω => ((X i ω, X j ω), X k ω)) μ ((ν.prod ν).prod ν) := by
  have hp := pair_preserving hX hIndep hLaw i j hij
  refine ⟨hp.measurable.prodMk (hX k), ?_⟩
  calc
    μ.map (fun ω => ((X i ω, X j ω), X k ω)) =
        (μ.map (fun ω => (X i ω, X j ω))).prod (μ.map (X k)) :=
      (indepFun_iff_map_prod_eq_prod_map_map
        hp.measurable.aemeasurable (hX k).aemeasurable).mp
        (hIndep.indepFun_prodMk hX i j k hik hjk)
    _ = (ν.prod ν).prod ν := by rw [hp.map_eq, marginal_map hLaw k]

theorem pairKernel_memLp_two
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (i j : ι) (hij : i ≠ j) :
    MemLp (fun ω => r (X i ω, X j ω)) 2 μ := by
  simpa only [Function.comp_def] using
    hr2.comp_measurePreserving (pair_preserving hX hIndep hLaw i j hij)

theorem integral_pairKernel_sq
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (i j : ι) (hij : i ≠ j) :
    (∫ ω, r (X i ω, X j ω) ^ 2 ∂μ) =
      ∫ ab, r ab ^ 2 ∂(ν.prod ν) := by
  have hp := pair_preserving hX hIndep hLaw i j hij
  have hm : AEStronglyMeasurable (fun ab => r ab ^ 2)
      (μ.map (fun ω => (X i ω, X j ω))) := by
    rw [hp.map_eq]
    exact hr2.integrable_sq.aestronglyMeasurable
  have ht := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at ht
  exact ht.symm

theorem integral_pairKernel_eq_zero
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (hcan : ∀ᵐ a ∂ν, (∫ b, r (a, b) ∂ν) = 0)
    (i j : ι) (hij : i ≠ j) :
    (∫ ω, r (X i ω, X j ω) ∂μ) = 0 := by
  have hp := pair_preserving hX hIndep hLaw i j hij
  have hri : Integrable r (ν.prod ν) := hr2.integrable (by norm_num)
  have hz : (∫ ab, r ab ∂(ν.prod ν)) = 0 := by
    rw [integral_prod r hri]
    exact integral_eq_zero_of_ae hcan
  have hm : AEStronglyMeasurable r (μ.map (fun ω => (X i ω, X j ω))) := by
    rw [hp.map_eq]
    exact hri.aestronglyMeasurable
  have ht := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at ht
  exact ht.symm.trans hz

theorem sharedEdgeProduct_integrable
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (hr : Measurable r) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Integrable (fun ω => r (X i ω, X j ω) * r (X i ω, X k ω)) μ := by
  have _ := hr
  have _ := hjk
  exact (pairKernel_memLp_two hX hIndep hLaw hr2 i j hij).integrable_mul
    (pairKernel_memLp_two hX hIndep hLaw hr2 i k hik)

theorem integral_sharedEdgeProduct_eq_zero
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (hr : Measurable r)
    (hcan : ∀ᵐ a ∂ν, (∫ b, r (a, b) ∂ν) = 0)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ ω, r (X i ω, X j ω) * r (X i ω, X k ω) ∂μ) = 0 := by
  let F : (E × E) × E → ℝ := fun p => r p.1 * r (p.1.1, p.2)
  have hT := triple_preserving hX hIndep hLaw i j k hij hik hjk
  have hFm : Measurable F :=
    (hr.comp measurable_fst).mul
      (hr.comp (measurable_fst.fst.prodMk measurable_snd))
  have hsample : Integrable
      (F ∘ (fun ω => ((X i ω, X j ω), X k ω))) μ := by
    simpa only [F, Function.comp_def] using
      sharedEdgeProduct_integrable hX hIndep hLaw hr2 hr i j k hij hik hjk
  have hFi : Integrable F ((ν.prod ν).prod ν) :=
    (hT.integrable_comp hFm.aestronglyMeasurable).mp hsample
  have hri : Integrable r (ν.prod ν) := hr2.integrable (by norm_num)
  have hsections : ∀ᵐ a ∂ν, Integrable (fun b => r (a, b)) ν :=
    hri.prod_right_ae
  have hfst : MeasurePreserving (Prod.fst : E × E → E) (ν.prod ν) ν :=
    measurePreserving_fst
  have hcan' := hfst.quasiMeasurePreserving.ae hcan
  have hsections' := hfst.quasiMeasurePreserving.ae hsections
  have hinner : ∀ᵐ ab ∂(ν.prod ν), (∫ c, F (ab, c) ∂ν) = 0 := by
    filter_upwards [hcan', hsections'] with ab hab _hrow
    dsimp only [F]
    rw [integral_const_mul, hab, mul_zero]
  have hz : (∫ p, F p ∂((ν.prod ν).prod ν)) = 0 := by
    rw [integral_prod F hFi]
    exact integral_eq_zero_of_ae hinner
  have hm : AEStronglyMeasurable F
      (μ.map (fun ω => ((X i ω, X j ω), X k ω))) := by
    rw [hT.map_eq]
    exact hFm.aestronglyMeasurable
  have ht := integral_map hT.measurable.aemeasurable hm
  rw [hT.map_eq] at ht
  calc
    (∫ ω, r (X i ω, X j ω) * r (X i ω, X k ω) ∂μ) =
        ∫ p, F p ∂((ν.prod ν).prod ν) := by
      simpa only [F] using ht.symm
    _ = 0 := hz

end

end Shao.OQ5.P50
