import Shao.OQ5.P35.FixedCategoryLaw
import Shao.OQ5.P35.RealEncoding
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The actual p35 observation law on the real line

Source: current/oq56/inputs02/p35.md §3. The continuous coordinate is
Lebesgue measure restricted and normalized on [-1,1]. The category/noise
product and its real encoding are fixed before every eventual sample size.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory

/-- Continuous uniform noise on the closed interval [-1,1]. -/
def noiseLaw : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)

/-- The category and noise coordinates have the actual independent product law. -/
def observationPairLaw : Measure (ℕ × ℝ) := categoryMeasure.prod noiseLaw

/-- One fixed real observation law, with no sample-size parameter. -/
def realLaw : Measure ℝ :=
  Measure.map (fun ca : ℕ × ℝ => encodeObservation ca.1 ca.2) observationPairLaw

instance noiseLaw_isProbabilityMeasure : IsProbabilityMeasure noiseLaw := by
  unfold noiseLaw
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    norm_num
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

instance observationPairLaw_isProbabilityMeasure :
    IsProbabilityMeasure observationPairLaw := by
  unfold observationPairLaw
  infer_instance

instance realLaw_isProbabilityMeasure : IsProbabilityMeasure realLaw := by
  unfold realLaw
  infer_instance

theorem noiseLaw_ae_mem : ∀ᵐ a ∂noiseLaw, a ∈ Set.Icc (-1 : ℝ) 1 :=
  ProbabilityTheory.ae_cond_mem measurableSet_Icc

theorem noiseLaw_absolutelyContinuous : noiseLaw ≪ volume :=
  ProbabilityTheory.cond_absolutelyContinuous

theorem pairLaw_ae_noise_mem :
    ∀ᵐ ca ∂observationPairLaw, ca.2 ∈ Set.Icc (-1 : ℝ) 1 := by
  apply (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).2
  exact Filter.Eventually.of_forall (fun _ => noiseLaw_ae_mem)

/-- Recovering both coordinates recovers their entire independent product law. -/
theorem map_decode_realLaw :
    Measure.map (fun x => (decodeCategory x, decodeNoise x)) realLaw =
      observationPairLaw := by
  rw [realLaw, Measure.map_map
    (measurable_decodeCategory.prodMk measurable_decodeNoise) measurable_encodeObservation]
  calc
    Measure.map ((fun x => (decodeCategory x, decodeNoise x)) ∘
        (fun ca : ℕ × ℝ => encodeObservation ca.1 ca.2)) observationPairLaw =
        Measure.map id observationPairLaw := by
      apply Measure.map_congr
      filter_upwards [pairLaw_ae_noise_mem] with ca hca
      exact Prod.ext (decodeCategory_encode ca.1 ca.2 hca)
        (decodeNoise_encode ca.1 ca.2 hca)
    _ = observationPairLaw := Measure.map_id

theorem map_category_realLaw :
    Measure.map decodeCategory realLaw = categoryMeasure := by
  calc
    Measure.map decodeCategory realLaw =
        Measure.map Prod.fst
          (Measure.map (fun x => (decodeCategory x, decodeNoise x)) realLaw) := by
      rw [Measure.map_map measurable_fst
        (measurable_decodeCategory.prodMk measurable_decodeNoise)]
      rfl
    _ = Measure.map Prod.fst observationPairLaw := by rw [map_decode_realLaw]
    _ = categoryMeasure := by simp [observationPairLaw]

theorem map_noise_realLaw : Measure.map decodeNoise realLaw = noiseLaw := by
  calc
    Measure.map decodeNoise realLaw =
        Measure.map Prod.snd
          (Measure.map (fun x => (decodeCategory x, decodeNoise x)) realLaw) := by
      rw [Measure.map_map measurable_snd
        (measurable_decodeCategory.prodMk measurable_decodeNoise)]
      rfl
    _ = Measure.map Prod.snd observationPairLaw := by rw [map_decode_realLaw]
    _ = noiseLaw := by simp [observationPairLaw]

end

end Shao.OQ5.P35
