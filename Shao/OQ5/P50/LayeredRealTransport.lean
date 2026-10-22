import Shao.OQ5.P50.LayeredEncoding
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal

namespace Shao.OQ5.P50

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

/-- The actual supplied source law pushed through the single fixed encoder. -/
def layerRealLaw (μ : Measure LayerObs) : Measure ℝ := μ.map layerEncode

/-- The decoded source kernel on the encoded pair image, zero elsewhere. -/
def layerRealKernel (H : LayerObs × LayerObs → ℝ) (z : ℝ × ℝ) : ℝ := by
  classical
  exact if z ∈ layerEncodedSet ×ˢ layerEncodedSet then
    H (layerDecode z.1, layerDecode z.2)
  else 0

theorem layerRealLaw_isProbabilityMeasure (μ : Measure LayerObs)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (layerRealLaw μ) := by
  exact (Measure.isProbabilityMeasure_map_iff measurable_layerEncode.aemeasurable).mpr
    inferInstance

theorem layerRealLaw_ae_image (μ : Measure LayerObs) :
    ∀ᵐ x ∂layerRealLaw μ, x ∈ layerEncodedSet :=
  ae_map_mem_range measurableSet_layerEncodedSet measurable_layerEncode.aemeasurable

theorem layerRealLaw_decode (μ : Measure LayerObs) :
    (layerRealLaw μ).map layerDecode = μ := by
  change (μ.map layerEncode).map layerDecode = μ
  rw [Measure.map_map measurable_layerDecode measurable_layerEncode]
  have hcomp : layerDecode ∘ layerEncode = id := funext layerDecode_encode
  rw [hcomp, Measure.map_id]

theorem layerRealLaw_pair (μ : Measure LayerObs) [SFinite μ] :
    (layerRealLaw μ).prod (layerRealLaw μ) =
      (μ.prod μ).map (Prod.map layerEncode layerEncode) :=
  Measure.map_prod_map μ μ measurable_layerEncode measurable_layerEncode

theorem measurable_layerRealKernel (H : LayerObs × LayerObs → ℝ)
    (hH : Measurable H) : Measurable (layerRealKernel H) := by
  classical
  exact Measurable.ite (measurableSet_layerEncodedSet.prod measurableSet_layerEncodedSet)
    (hH.comp (measurable_layerDecode.prodMap measurable_layerDecode)) measurable_const

theorem layerRealKernel_encode (H : LayerObs × LayerObs → ℝ) (o o' : LayerObs) :
    layerRealKernel H (layerEncode o, layerEncode o') = H (o, o') := by
  have hpair : (layerEncode o, layerEncode o') ∈ layerEncodedSet ×ˢ layerEncodedSet :=
    ⟨⟨o, rfl⟩, ⟨o', rfl⟩⟩
  simp only [layerRealKernel, ite_eq_left hpair, layerDecode_encode]

theorem layerRealKernel_eq_zero (H : LayerObs × LayerObs → ℝ) (z : ℝ × ℝ)
    (hz : z ∉ layerEncodedSet ×ˢ layerEncodedSet) : layerRealKernel H z = 0 := by
  simp only [layerRealKernel, ite_eq_right hz]

theorem layerRealKernel_symmetric (H : LayerObs × LayerObs → ℝ)
    (hH : ∀ o o', H (o, o') = H (o', o)) (x y : ℝ) :
    layerRealKernel H (x, y) = layerRealKernel H (y, x) := by
  by_cases hxy : (x, y) ∈ layerEncodedSet ×ˢ layerEncodedSet
  · have hyx : (y, x) ∈ layerEncodedSet ×ˢ layerEncodedSet := ⟨hxy.2, hxy.1⟩
    simp only [layerRealKernel, ite_eq_left hxy, ite_eq_left hyx]
    exact hH _ _
  · have hyx : (y, x) ∉ layerEncodedSet ×ˢ layerEncodedSet := by
      rintro ⟨hy, hx⟩
      exact hxy ⟨hx, hy⟩
    rw [layerRealKernel_eq_zero H (x, y) hxy, layerRealKernel_eq_zero H (y, x) hyx]

private theorem pairEncode_measurableEmbedding :
    MeasurableEmbedding (Prod.map layerEncode layerEncode) :=
  (measurableEmbedding_embeddingReal LayerObs).prodMap
    (measurableEmbedding_embeddingReal LayerObs)

private theorem layerRealKernel_comp (H : LayerObs × LayerObs → ℝ) :
    layerRealKernel H ∘ Prod.map layerEncode layerEncode = H := by
  funext z
  exact layerRealKernel_encode H z.1 z.2

theorem layerRealKernel_integral (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) :
    (∫ z, layerRealKernel H z ∂(layerRealLaw μ).prod (layerRealLaw μ)) =
      ∫ z, H z ∂μ.prod μ := by
  rw [layerRealLaw_pair, pairEncode_measurableEmbedding.integral_map]
  change (∫ z, (layerRealKernel H ∘ Prod.map layerEncode layerEncode) z ∂μ.prod μ) = _
  rw [layerRealKernel_comp]

theorem layerRealKernel_integrable_iff (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) :
    Integrable (layerRealKernel H) ((layerRealLaw μ).prod (layerRealLaw μ)) ↔
      Integrable H (μ.prod μ) := by
  rw [layerRealLaw_pair, pairEncode_measurableEmbedding.integrable_map_iff,
    layerRealKernel_comp]

theorem layerRealKernel_memLp_iff (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) (p : ℝ≥0∞) :
    MemLp (layerRealKernel H) p ((layerRealLaw μ).prod (layerRealLaw μ)) ↔
      MemLp H p (μ.prod μ) := by
  rw [layerRealLaw_pair, pairEncode_measurableEmbedding.memLp_map_measure_iff,
    layerRealKernel_comp]

theorem layerRealKernel_integral_sq (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) :
    (∫ z, layerRealKernel H z ^ 2 ∂(layerRealLaw μ).prod (layerRealLaw μ)) =
      ∫ z, H z ^ 2 ∂μ.prod μ := by
  rw [layerRealLaw_pair, pairEncode_measurableEmbedding.integral_map]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => congrArg (fun t : ℝ => t ^ 2)
    (layerRealKernel_encode H z.1 z.2)

theorem layerRealKernel_integrable_sq (μ : Measure LayerObs) [SFinite μ]
    (H : LayerObs × LayerObs → ℝ) (hH : MemLp H 2 (μ.prod μ)) :
    Integrable (fun z => H z ^ 2) (μ.prod μ) ∧
      Integrable (fun z => layerRealKernel H z ^ 2)
        ((layerRealLaw μ).prod (layerRealLaw μ)) := by
  exact ⟨hH.integrable_sq, ((layerRealKernel_memLp_iff μ H 2).mpr hH).integrable_sq⟩

end
end Shao.OQ5.P50
