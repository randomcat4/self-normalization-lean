import Shao.OQ5.P52.FixedLayerModel
import Shao.OQ5.P35.NoiseMoments

/-!
# Noise moments under the actual fixed p52 observation law

Original p50 and p52 use the same normalized uniform noise on [-1,1].
Only the exact first marginal is transported here; the categorical laws
and the whole observation laws are not identified.
-/

set_option autoImplicit false

open MeasureTheory

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

private theorem fixedFirst_measurePreserving :
    MeasurePreserving (Prod.fst : LayerObs → ℝ)
      fixedObservationLaw Shao.OQ5.P35.noiseLaw := by
  refine ⟨measurable_fst, ?_⟩
  simpa only [Shao.OQ5.P50.layerNoiseLaw, Shao.OQ5.P35.noiseLaw]
    using map_fixedObservation_first

theorem integrable_fixedObservation_first :
    Integrable (fun o : LayerObs => o.1) fixedObservationLaw := by
  simpa only [Function.comp_def] using
    fixedFirst_measurePreserving.integrable_comp_of_integrable
      Shao.OQ5.P35.integrable_noiseLaw_id

theorem integral_fixedObservation_first_eq_zero :
    (∫ o : LayerObs, o.1 ∂fixedObservationLaw) = 0 := by
  calc
    (∫ o : LayerObs, o.1 ∂fixedObservationLaw) =
        ∫ a : ℝ, a ∂(fixedObservationLaw.map Prod.fst) :=
      (integral_map (μ := fixedObservationLaw) (φ := Prod.fst)
        (f := fun a : ℝ => a) measurable_fst.aemeasurable
        continuous_id.aestronglyMeasurable).symm
    _ = ∫ a : ℝ, a ∂Shao.OQ5.P35.noiseLaw := by
      rw [fixedFirst_measurePreserving.map_eq]
    _ = 0 := Shao.OQ5.P35.integral_noiseLaw_id

theorem integrable_fixedObservation_first_sq :
    Integrable (fun o : LayerObs => o.1 ^ 2) fixedObservationLaw := by
  simpa only [Function.comp_def] using
    fixedFirst_measurePreserving.integrable_comp_of_integrable
      Shao.OQ5.P35.integrable_noiseLaw_sq

theorem integral_fixedObservation_first_sq :
    (∫ o : LayerObs, o.1 ^ 2 ∂fixedObservationLaw) = (1 / 3 : ℝ) := by
  calc
    (∫ o : LayerObs, o.1 ^ 2 ∂fixedObservationLaw) =
        ∫ a : ℝ, a ^ 2 ∂(fixedObservationLaw.map Prod.fst) :=
      (integral_map (μ := fixedObservationLaw) (φ := Prod.fst)
        (f := fun a : ℝ => a ^ 2) measurable_fst.aemeasurable
        (continuous_id.pow 2).aestronglyMeasurable).symm
    _ = ∫ a : ℝ, a ^ 2 ∂Shao.OQ5.P35.noiseLaw := by
      rw [fixedFirst_measurePreserving.map_eq]
    _ = (1 / 3 : ℝ) := Shao.OQ5.P35.integral_noiseLaw_sq

end
end Shao.OQ5.P52
