import Shao.OQ5.P35.RealLaw
import Shao.OQ5.P35.FeatureMoments
import Shao.OQ5.P35.PopulationKernel
import Shao.OQ5.P35.NoiseMoments

/-!
# Actual moments of the p35 real observations

Source: current/oq56/inputs02/p35.md §3. Integrability and expectations are
transported along the already proved decoder laws. Neither decoder is assumed
to be an embedding, and the category offset and feature remain dependent.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory

private theorem categoryDecoder_measurePreserving :
    MeasurePreserving decodeCategory realLaw categoryMeasure :=
  ⟨measurable_decodeCategory, map_category_realLaw⟩

private theorem noiseDecoder_measurePreserving :
    MeasurePreserving decodeNoise realLaw noiseLaw :=
  ⟨measurable_decodeNoise, map_noise_realLaw⟩

private theorem category_integrable_comp (f : ℕ → ℝ)
    (hf : Integrable f categoryMeasure) :
    Integrable (fun x => f (decodeCategory x)) realLaw :=
  categoryDecoder_measurePreserving.integrable_comp_of_integrable hf

private theorem noise_integrable_comp (f : ℝ → ℝ)
    (hf : Integrable f noiseLaw) :
    Integrable (fun x => f (decodeNoise x)) realLaw :=
  noiseDecoder_measurePreserving.integrable_comp_of_integrable hf

private theorem category_integral_comp (f : ℕ → ℝ)
    (hf : Integrable f categoryMeasure) :
    (∫ x, f (decodeCategory x) ∂realLaw) = ∫ c, f c ∂categoryMeasure := by
  have hfm : AEStronglyMeasurable f (Measure.map decodeCategory realLaw) := by
    rw [map_category_realLaw]
    exact hf.aestronglyMeasurable
  rw [← map_category_realLaw]
  exact (integral_map measurable_decodeCategory.aemeasurable hfm).symm

private theorem noise_integral_comp (f : ℝ → ℝ)
    (hf : Integrable f noiseLaw) :
    (∫ x, f (decodeNoise x) ∂realLaw) = ∫ a, f a ∂noiseLaw := by
  have hfm : AEStronglyMeasurable f (Measure.map decodeNoise realLaw) := by
    rw [map_noise_realLaw]
    exact hf.aestronglyMeasurable
  rw [← map_noise_realLaw]
  exact (integral_map measurable_decodeNoise.aemeasurable hfm).symm

theorem integrable_decodeNoise_abs_pow (r : ℕ) (hr : r ≤ 3) :
    Integrable (fun x => |decodeNoise x| ^ r) realLaw :=
  noise_integrable_comp (fun a => |a| ^ r) (integrable_noiseLaw_abs_pow r hr)

theorem integrable_decodeNoise : Integrable decodeNoise realLaw :=
  noise_integrable_comp (fun a => a) integrable_noiseLaw_id

theorem integral_decodeNoise : (∫ x, decodeNoise x ∂realLaw) = 0 := by
  exact (noise_integral_comp (fun a => a) integrable_noiseLaw_id).trans integral_noiseLaw_id

theorem integrable_decodeNoise_sq :
    Integrable (fun x => decodeNoise x ^ 2) realLaw :=
  noise_integrable_comp (fun a => a ^ 2) integrable_noiseLaw_sq

theorem integral_decodeNoise_sq :
    (∫ x, decodeNoise x ^ 2 ∂realLaw) = (1 / 3 : ℝ) := by
  exact (noise_integral_comp (fun a => a ^ 2) integrable_noiseLaw_sq).trans integral_noiseLaw_sq

theorem integrable_observationFeature : Integrable observationFeature realLaw :=
  category_integrable_comp categoryFeature integrable_categoryFeature

theorem integral_observationFeature : (∫ x, observationFeature x ∂realLaw) = 0 := by
  exact (category_integral_comp categoryFeature integrable_categoryFeature).trans integral_categoryFeature

theorem integrable_observationFeature_sq :
    Integrable (fun x => observationFeature x ^ 2) realLaw :=
  category_integrable_comp (fun c => categoryFeature c ^ 2) integrable_categoryFeature_sq

theorem integral_observationFeature_sq :
    (∫ x, observationFeature x ^ 2 ∂realLaw) = featureVariance := by
  exact (category_integral_comp (fun c => categoryFeature c ^ 2)
    integrable_categoryFeature_sq).trans integral_categoryFeature_sq

theorem integrable_observationOffset_pow (r : ℕ) (hr : r ≤ 3) :
    Integrable (fun x => observationOffset x ^ r) realLaw :=
  category_integrable_comp (fun c => categoryOffset c ^ r) (integrable_categoryOffset_pow r hr)

theorem integral_observationOffset_pow (r : ℕ) (hr : r ≤ 3) :
    (∫ x, observationOffset x ^ r ∂realLaw) =
      ∫ c, categoryOffset c ^ r ∂categoryMeasure :=
  category_integral_comp (fun c => categoryOffset c ^ r) (integrable_categoryOffset_pow r hr)

end

end Shao.OQ5.P35
