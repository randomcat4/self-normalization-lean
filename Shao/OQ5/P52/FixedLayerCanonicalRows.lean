import Shao.OQ5.P52.FixedLayerLpLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual L1 layer budget and canonical residual rows

The pair norm budget is obtained from the genuine integrable absolute sum.
Rowwise interchange uses its derived a.e. row budget and the exact source mask.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem integrable_layer_pair (j : ℕ) :
    Integrable (fixedLayerTerm j) (fixedObservationLaw.prod fixedObservationLaw) := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (fixedLayerTerm_memLp_two j)

private theorem integrable_absSum_pair :
    Integrable (fun z : LayerObs × LayerObs => ∑' j : ℕ, |fixedLayerTerm j z|)
      (fixedObservationLaw.prod fixedObservationLaw) := by
  apply memLp_one_iff_integrable.mp
  simpa only [ENNReal.ofReal_one] using fixedLayerAbsSum_memLp 1 (by norm_num)

private theorem integrable_residual_pair :
    Integrable fixedResidualKernel (fixedObservationLaw.prod fixedObservationLaw) := by
  apply memLp_one_iff_integrable.mp
  simpa only [ENNReal.ofReal_one] using fixedResidualKernel_memLp 1 (by norm_num)

theorem summable_integral_abs_fixedLayerTerm :
    Summable (fun j : ℕ =>
      ∫ z : LayerObs × LayerObs, |fixedLayerTerm j z|
        ∂fixedObservationLaw.prod fixedObservationLaw) := by
  let M := fixedObservationLaw.prod fixedObservationLaw
  let S : LayerObs × LayerObs → ℝ := fun z => ∑' j : ℕ, |fixedLayerTerm j z|
  have hS : Integrable S M := integrable_absSum_pair
  have hSnn : 0 ≤ᵐ[M] S :=
    Eventually.of_forall (fun z => tsum_nonneg (fun j => abs_nonneg _))
  have hSfinite : (∫⁻ z, ENNReal.ofReal (S z) ∂M) < ∞ :=
    (hasFiniteIntegral_iff_ofReal hSnn).mp hS.2
  have hm (j : ℕ) : Measurable
      (fun z : LayerObs × LayerObs => ENNReal.ofReal |fixedLayerTerm j z|) := by
    simpa only [Real.norm_eq_abs, Function.comp_def] using
      ENNReal.measurable_ofReal.comp (measurable_fixedLayerTerm j).norm
  have hsum :
      (∫⁻ z, ∑' j : ℕ, ENNReal.ofReal |fixedLayerTerm j z| ∂M) =
        ∫⁻ z, ENNReal.ofReal (S z) ∂M := by
    apply lintegral_congr_ae
    filter_upwards [ae_mem_fixedAbsoluteConvergenceSet] with z hz
    change Summable (fun j : ℕ => |fixedLayerTerm j z|) at hz
    exact (ENNReal.ofReal_tsum_of_nonneg (fun j => abs_nonneg _) hz).symm
  have hb :
      (∑' j : ℕ, ∫⁻ z, ENNReal.ofReal |fixedLayerTerm j z| ∂M) ≠ ∞ := by
    rw [← lintegral_tsum (fun j => (hm j).aemeasurable), hsum]
    exact hSfinite.ne
  have hi (j : ℕ) :
      Integrable (fun z : LayerObs × LayerObs => |fixedLayerTerm j z|) M := by
    simpa only [Real.norm_eq_abs] using (integrable_layer_pair j).norm
  have he (j : ℕ) :
      ENNReal.ofReal (∫ z : LayerObs × LayerObs, |fixedLayerTerm j z| ∂M) =
        ∫⁻ z, ENNReal.ofReal |fixedLayerTerm j z| ∂M :=
    ofReal_integral_eq_lintegral_ofReal (hi j)
      (Eventually.of_forall (fun z => abs_nonneg _))
  have hb' :
      (∑' j : ℕ, ENNReal.ofReal
        (∫ z : LayerObs × LayerObs, |fixedLayerTerm j z| ∂M)) ≠ ∞ := by
    simpa only [he] using hb
  have hs := ENNReal.summable_toReal hb'
  have hreal (j : ℕ) :
      (ENNReal.ofReal (∫ z : LayerObs × LayerObs, |fixedLayerTerm j z| ∂M)).toReal =
        ∫ z : LayerObs × LayerObs, |fixedLayerTerm j z| ∂M :=
    ENNReal.toReal_ofReal (integral_nonneg (fun z => abs_nonneg _))
  simpa only [hreal] using hs

private theorem ae_summable_row_norm_integral :
    ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      Summable (fun j : ℕ =>
        ∫ o' : LayerObs, ‖fixedLayerTerm j (o, o')‖ ∂fixedObservationLaw) := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  let B : ℕ → LayerObs → ℝ := fun j o =>
    ∫ o' : LayerObs, ‖fixedLayerTerm j (o, o')‖ ∂fixedObservationLaw
  have hi (j : ℕ) : Integrable (B j) fixedObservationLaw :=
    (integrable_layer_pair j).integral_norm_prod_left
  have hnn (j : ℕ) (o : LayerObs) : 0 ≤ B j o :=
    integral_nonneg (fun o' => norm_nonneg _)
  have hpair (j : ℕ) :
      (∫ o : LayerObs, B j o ∂fixedObservationLaw) =
        ∫ z : LayerObs × LayerObs, |fixedLayerTerm j z|
          ∂fixedObservationLaw.prod fixedObservationLaw := by
    simpa only [B, Real.norm_eq_abs] using
      (integral_prod (fun z : LayerObs × LayerObs => ‖fixedLayerTerm j z‖)
        (integrable_layer_pair j).norm).symm
  have hs : Summable (fun j : ℕ => ∫ o : LayerObs, B j o ∂fixedObservationLaw) := by
    simpa only [hpair] using summable_integral_abs_fixedLayerTerm
  have he (j : ℕ) :
      (∫⁻ o : LayerObs, ENNReal.ofReal (B j o) ∂fixedObservationLaw) =
        ENNReal.ofReal (∫ o : LayerObs, B j o ∂fixedObservationLaw) :=
    (ofReal_integral_eq_lintegral_ofReal (hi j)
      (Eventually.of_forall (hnn j))).symm
  have hb :
      (∑' j : ℕ, ∫⁻ o : LayerObs, ENNReal.ofReal (B j o) ∂fixedObservationLaw) ≠ ∞ := by
    simpa only [he] using hs.tsum_ofReal_ne_top
  have hm (j : ℕ) : AEMeasurable
      (fun o : LayerObs => ENNReal.ofReal (B j o)) fixedObservationLaw :=
    (hi j).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfinite :
      (∫⁻ o : LayerObs, ∑' j : ℕ, ENNReal.ofReal (B j o) ∂fixedObservationLaw) ≠ ∞ := by
    rw [lintegral_tsum hm]
    exact hb
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfinite] with o ho
  have hreal (j : ℕ) : (ENNReal.ofReal (B j o)).toReal = B j o :=
    ENNReal.toReal_ofReal (hnn j o)
  simpa only [hreal] using ENNReal.summable_toReal ho.ne

theorem integrable_fixedResidualKernel_row_ae :
    ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      Integrable (fun o' : LayerObs => fixedResidualKernel (o, o')) fixedObservationLaw := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  exact integrable_residual_pair.prod_right_ae

theorem integral_fixedResidualKernel_row_eq_zero_ae :
    ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      (∫ o' : LayerObs, fixedResidualKernel (o, o') ∂fixedObservationLaw) = 0 := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  have hmask : ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      (fun o' : LayerObs => fixedResidualKernel (o, o')) =ᵐ[fixedObservationLaw]
        (fun o' : LayerObs => ∑' j : ℕ, fixedLayerTerm j (o, o')) :=
    MeasureTheory.Measure.ae_ae_eq_curry_of_prod fixedResidualKernel_ae_eq_tsum
  filter_upwards [ae_summable_row_norm_integral, hmask,
    integrable_fixedResidualKernel_row_ae] with o hb hm _hir
  have he := integral_tsum_of_summable_integral_norm
    (fun j : ℕ => integrable_fixedLayerTerm_row j o) hb
  calc
    (∫ o' : LayerObs, fixedResidualKernel (o, o') ∂fixedObservationLaw) =
        ∫ o' : LayerObs, (∑' j : ℕ, fixedLayerTerm j (o, o')) ∂fixedObservationLaw :=
      integral_congr_ae hm
    _ = ∑' j : ℕ, ∫ o' : LayerObs, fixedLayerTerm j (o, o') ∂fixedObservationLaw := he.symm
    _ = 0 := by simp only [integral_fixedLayerTerm_row_zero, tsum_zero]

theorem integral_fixedResidualKernel_eq_zero :
    (∫ z : LayerObs × LayerObs, fixedResidualKernel z
      ∂fixedObservationLaw.prod fixedObservationLaw) = 0 := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  rw [integral_prod fixedResidualKernel integrable_residual_pair]
  simpa only [integral_zero] using
    integral_congr_ae integral_fixedResidualKernel_row_eq_zero_ae

end
end Shao.OQ5.P52
