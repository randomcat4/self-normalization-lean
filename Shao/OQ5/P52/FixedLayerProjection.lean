import Shao.OQ5.P52.FixedLayerCanonicalRows
import Shao.OQ5.P52.FixedObservationNoiseMoments

/-!
# The mean and first projection of the actual fixed kernel

The row integral is justified on the actual full-measure row set before it
is identified with the noise coordinate. Centering follows from honest Fubini.
-/

set_option autoImplicit false

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedFirstProjection (o : LayerObs) : ℝ :=
  ∫ o' : LayerObs, fixedKernel (o, o') ∂fixedObservationLaw

private theorem integrable_kernel_pair :
    Integrable fixedKernel (fixedObservationLaw.prod fixedObservationLaw) := by
  apply memLp_one_iff_integrable.mp
  simpa only [ENNReal.ofReal_one] using fixedKernel_memLp 1 (by norm_num)

theorem integrable_fixedKernel_row_ae :
    ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      Integrable (fun o' : LayerObs => fixedKernel (o, o')) fixedObservationLaw := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  filter_upwards [integrable_fixedResidualKernel_row_ae] with o hr
  change Integrable (fun o' : LayerObs =>
    o.1 + o'.1 + fixedResidualKernel (o, o')) fixedObservationLaw
  exact ((integrable_const o.1).add integrable_fixedObservation_first).add hr

theorem fixedFirstProjection_ae_eq_first :
    fixedFirstProjection =ᵐ[fixedObservationLaw] (fun o : LayerObs => o.1) := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  filter_upwards [integrable_fixedResidualKernel_row_ae,
    integral_fixedResidualKernel_row_eq_zero_ae,
    integrable_fixedKernel_row_ae] with o hr hzero _hrow
  change (∫ o' : LayerObs, o.1 + o'.1 + fixedResidualKernel (o, o')
    ∂fixedObservationLaw) = o.1
  have hsum : Integrable (fun o' : LayerObs => o.1 + o'.1) fixedObservationLaw :=
    (integrable_const o.1).add integrable_fixedObservation_first
  rw [integral_add hsum hr,
    integral_add (integrable_const o.1) integrable_fixedObservation_first,
    integral_fixedObservation_first_eq_zero, hzero]
  simp

theorem integral_fixedKernel_eq_zero :
    (∫ z : LayerObs × LayerObs, fixedKernel z
      ∂fixedObservationLaw.prod fixedObservationLaw) = 0 := by
  let _ := fixedObservationLaw_isProbabilityMeasure
  rw [integral_prod fixedKernel integrable_kernel_pair]
  change (∫ o : LayerObs, fixedFirstProjection o ∂fixedObservationLaw) = 0
  exact (integral_congr_ae fixedFirstProjection_ae_eq_first).trans
    integral_fixedObservation_first_eq_zero

theorem fixedFirstProjection_memLp_two :
    MemLp fixedFirstProjection 2 fixedObservationLaw := by
  have hfirst : MemLp (fun o : LayerObs => o.1) 2 fixedObservationLaw :=
    (memLp_two_iff_integrable_sq measurable_fst.aestronglyMeasurable).mpr
      integrable_fixedObservation_first_sq
  exact MemLp.ae_eq fixedFirstProjection_ae_eq_first.symm hfirst

theorem integral_fixedFirstProjection_sq :
    (∫ o : LayerObs, fixedFirstProjection o ^ 2 ∂fixedObservationLaw) = (1 / 3 : ℝ) := by
  have _hgsq : Integrable (fun o : LayerObs => fixedFirstProjection o ^ 2)
      fixedObservationLaw :=
    (memLp_two_iff_integrable_sq
      fixedFirstProjection_memLp_two.aestronglyMeasurable).mp fixedFirstProjection_memLp_two
  calc
    (∫ o : LayerObs, fixedFirstProjection o ^ 2 ∂fixedObservationLaw) =
        ∫ o : LayerObs, o.1 ^ 2 ∂fixedObservationLaw :=
      integral_congr_ae (fixedFirstProjection_ae_eq_first.fun_comp (fun x : ℝ => x ^ 2))
    _ = (1 / 3 : ℝ) := integral_fixedObservation_first_sq

theorem fixedFirstProjection_indep_categories :
    ProbabilityTheory.IndepFun fixedFirstProjection Prod.snd fixedObservationLaw := by
  exact fixedObservation_first_indep_categories.congr
    fixedFirstProjection_ae_eq_first.symm Filter.EventuallyEq.rfl

end
end Shao.OQ5.P52
