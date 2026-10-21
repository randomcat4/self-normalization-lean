import Shao.OQ5.P52.FixedLayerErasureKernel
import Shao.OQ5.P52.FixedLayerCanonicalRows

/-!
# Genuine canonical background under the actual erased observation law

The paired pushforward and exact a.e. deletion give genuine background L2.
Canonical rows are transported through both actual pushforwards, with honest
row integrability before Fubini. No inner law is changed by absolute continuity.
-/

set_option autoImplicit false

open MeasureTheory Filter

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

attribute [local instance] fixedObservationLaw_isProbabilityMeasure
attribute [local instance] fixedErasedLaw_isProbabilityMeasure

theorem map_fixedEraseLayer_pair (j : ℕ) :
    (fixedObservationLaw.prod fixedObservationLaw).map
      (fun z : LayerObs × LayerObs => (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) =
      (fixedErasedLaw j).prod (fixedErasedLaw j) := by
  exact (Measure.map_prod_map fixedObservationLaw fixedObservationLaw
    (measurable_fixedEraseLayer j) (measurable_fixedEraseLayer j)).symm

theorem fixedResidualKernel_memLp_two_fixedErasedLaw (j : ℕ) :
    MemLp fixedResidualKernel 2 ((fixedErasedLaw j).prod (fixedErasedLaw j)) := by
  have hr : MemLp fixedResidualKernel 2 (fixedObservationLaw.prod fixedObservationLaw) := by
    simpa only [ENNReal.ofReal_ofNat] using fixedResidualKernel_memLp 2 (by norm_num)
  have hd := hr.sub (fixedLayerTerm_memLp_two j)
  have hp : MemLp (fun z : LayerObs × LayerObs =>
      fixedResidualKernel (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) 2
      (fixedObservationLaw.prod fixedObservationLaw) :=
    (memLp_congr_ae (fixedResidualKernel_erase_pair_ae_eq_sub j)).mpr hd
  have hT : Measurable (fun z : LayerObs × LayerObs =>
      (fixedEraseLayer j z.1, fixedEraseLayer j z.2)) :=
    ((measurable_fixedEraseLayer j).comp measurable_fst).prodMk
      ((measurable_fixedEraseLayer j).comp measurable_snd)
  rw [← map_fixedEraseLayer_pair j]
  exact (memLp_map_measure_iff measurable_fixedResidualKernel.aestronglyMeasurable
    hT.aemeasurable).mpr hp

private theorem integrable_erased_residual_pair (j : ℕ) :
    Integrable fixedResidualKernel ((fixedErasedLaw j).prod (fixedErasedLaw j)) :=
  MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    (fixedResidualKernel_memLp_two_fixedErasedLaw j)

theorem integrable_fixedResidualKernel_row_fixedErasedLaw_ae (j : ℕ) :
    ∀ᵐ o : LayerObs ∂fixedErasedLaw j,
      Integrable (fun o' : LayerObs => fixedResidualKernel (o, o')) (fixedErasedLaw j) :=
  (integrable_erased_residual_pair j).prod_right_ae

theorem integral_fixedResidualKernel_row_fixedErasedLaw_eq_zero_ae (j : ℕ) :
    ∀ᵐ o : LayerObs ∂fixedErasedLaw j,
      (∫ o' : LayerObs, fixedResidualKernel (o, o') ∂fixedErasedLaw j) = 0 := by
  let F : LayerObs → ℝ := fun o =>
    ∫ o' : LayerObs, fixedResidualKernel (o, o') ∂fixedErasedLaw j
  have hF : Measurable F :=
    measurable_fixedResidualKernel.stronglyMeasurable.integral_prod_right'.measurable
  change ∀ᵐ o ∂fixedObservationLaw.map (fixedEraseLayer j), F o = 0
  apply (ae_map_iff (measurable_fixedEraseLayer j).aemeasurable
    (measurableSet_eq_fun hF measurable_const)).mpr
  have hpair : ∀ᵐ o : LayerObs ∂fixedObservationLaw,
      (fun o' : LayerObs =>
        fixedResidualKernel (fixedEraseLayer j o, fixedEraseLayer j o'))
        =ᵐ[fixedObservationLaw]
          (fun o' : LayerObs => fixedResidualKernel (o, o') - fixedLayerTerm j (o, o')) :=
    MeasureTheory.Measure.ae_ae_eq_curry_of_prod (fixedResidualKernel_erase_pair_ae_eq_sub j)
  filter_upwards [hpair, integrable_fixedResidualKernel_row_ae,
    integral_fixedResidualKernel_row_eq_zero_ae] with o he hi hz
  have hk := integrable_fixedLayerTerm_row j o
  have hI : Integrable (fun o' : LayerObs =>
      fixedResidualKernel (fixedEraseLayer j o, fixedEraseLayer j o')) fixedObservationLaw :=
    (hi.sub hk).congr he.symm
  have hrow : Measurable (fun o' : LayerObs =>
      fixedResidualKernel (fixedEraseLayer j o, o')) :=
    measurable_fixedResidualKernel.comp (measurable_const.prodMk measurable_id)
  have hIb : Integrable (fun o' : LayerObs =>
      fixedResidualKernel (fixedEraseLayer j o, o'))
      (fixedObservationLaw.map (fixedEraseLayer j)) :=
    (integrable_map_measure hrow.aestronglyMeasurable
      (measurable_fixedEraseLayer j).aemeasurable).mpr hI
  calc
    F (fixedEraseLayer j o) = ∫ o' : LayerObs,
        fixedResidualKernel (fixedEraseLayer j o, fixedEraseLayer j o') ∂fixedObservationLaw :=
      integral_map (measurable_fixedEraseLayer j).aemeasurable hIb.aestronglyMeasurable
    _ = ∫ o' : LayerObs,
        (fixedResidualKernel (o, o') - fixedLayerTerm j (o, o')) ∂fixedObservationLaw :=
      integral_congr_ae he
    _ = 0 := by
      rw [integral_sub hi hk, hz, integral_fixedLayerTerm_row_zero]
      simp only [sub_zero]

theorem integral_fixedResidualKernel_fixedErasedLaw_eq_zero (j : ℕ) :
    (∫ z : LayerObs × LayerObs, fixedResidualKernel z
      ∂(fixedErasedLaw j).prod (fixedErasedLaw j)) = 0 := by
  rw [integral_prod fixedResidualKernel (integrable_erased_residual_pair j)]
  simpa only [integral_zero] using
    integral_congr_ae (integral_fixedResidualKernel_row_fixedErasedLaw_eq_zero_ae j)

end
end Shao.OQ5.P52
