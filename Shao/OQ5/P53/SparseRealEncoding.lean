import Shao.OQ5.P53.SparsePopulation
import Shao.OQ5.P35.RealEncoding
import Mathlib.Logic.Encodable.Basic

/-!
# The actual fixed real law of the p53 population

Source: current/oq56/inputs02/p53.md §3. Encode the paired discrete tags by
a natural category and then use X = 3I + A. Recovery uses the closed noise
interval, including its endpoints. The total decoder has fixed fallback tags
away from valid codes; no global injectivity or surjectivity is asserted.

This module transports the entire actual population law and its independent
pair. Real features, their kernel and moments, iid samples, the studentizer,
balanced events and the original tail conclusions are subsequent obligations.
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

def sparsePopulationEncode (z : (ℝ × (ℕ × Bool)) × (ℕ × Bool)) : ℝ :=
  Shao.OQ5.P35.encodeObservation (Encodable.encode (z.1.2, z.2)) z.1.1

def sparsePopulationDecode (y : ℝ) : (ℝ × (ℕ × Bool)) × (ℕ × Bool) :=
  let labels := (Encodable.decode (Shao.OQ5.P35.decodeCategory y) :
    Option ((ℕ × Bool) × (ℕ × Bool))).getD ((0, false), (0, false))
  ((Shao.OQ5.P35.decodeNoise y, labels.1), labels.2)

def sparseRealMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Measure ℝ :=
  (sparsePopulationMeasure α x N).map sparsePopulationEncode

theorem measurable_sparsePopulationEncode : Measurable sparsePopulationEncode := by
  change Measurable (fun z : (ℝ × (ℕ × Bool)) × (ℕ × Bool) =>
    (3 : ℝ) * (Encodable.encode (z.1.2, z.2) : ℝ) + z.1.1)
  have hcode : Measurable (fun labels : (ℕ × Bool) × (ℕ × Bool) =>
      (Encodable.encode labels : ℝ)) :=
    measurable_of_countable _
  have hlabels : Measurable
      (fun z : (ℝ × (ℕ × Bool)) × (ℕ × Bool) => (z.1.2, z.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  exact (measurable_const.mul (hcode.comp hlabels)).add
    (measurable_fst.comp measurable_fst)

theorem measurable_sparsePopulationDecode : Measurable sparsePopulationDecode := by
  have hlabels : Measurable (fun y : ℝ =>
      (Encodable.decode (Shao.OQ5.P35.decodeCategory y) :
        Option ((ℕ × Bool) × (ℕ × Bool))).getD ((0, false), (0, false))) :=
    (measurable_of_countable (fun n : ℕ =>
      (Encodable.decode n : Option ((ℕ × Bool) × (ℕ × Bool))).getD
        ((0, false), (0, false)))).comp Shao.OQ5.P35.measurable_decodeCategory
  exact (Shao.OQ5.P35.measurable_decodeNoise.prodMk
    (measurable_fst.comp hlabels)).prodMk (measurable_snd.comp hlabels)

theorem sparsePopulationDecode_encode :
  ∀ (z : (ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  z.1.1 ∈ Set.Icc (-1 : ℝ) 1 →
  sparsePopulationDecode (sparsePopulationEncode z) = z := by
  intro z hz
  rcases z with ⟨⟨a, b⟩, c⟩
  simp [sparsePopulationDecode, sparsePopulationEncode,
    Shao.OQ5.P35.decodeCategory_encode _ _ hz,
    Shao.OQ5.P35.decodeNoise_encode _ _ hz]

theorem sparsePopulationEncode_injectiveOn :
  Set.InjOn sparsePopulationEncode
    {z : (ℝ × (ℕ × Bool)) × (ℕ × Bool) | z.1.1 ∈ Set.Icc (-1 : ℝ) 1} := by
  intro z hz w hw hzw
  calc
    z = sparsePopulationDecode (sparsePopulationEncode z) :=
      (sparsePopulationDecode_encode z hz).symm
    _ = sparsePopulationDecode (sparsePopulationEncode w) :=
      congrArg sparsePopulationDecode hzw
    _ = w := sparsePopulationDecode_encode w hw

theorem sparsePopulation_noise_mem_Icc_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ᵐ z ∂sparsePopulationMeasure α x N, z.1.1 ∈ Set.Icc (-1 : ℝ) 1 := by
  intro α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hnoise : ∀ᵐ w : ℝ × (ℕ × Bool)
      ∂(Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)),
      w.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Icc)).2
    filter_upwards [Shao.OQ5.P35.noiseLaw_ae_mem] with a ha
    exact Filter.Eventually.of_forall (fun _ => ha)
  change ∀ᵐ z ∂((Shao.OQ5.P35.noiseLaw.prod (sparseSignedLabelMeasure α x N)).prod
    (sparseSignedLabelMeasure α x N)), z.1.1 ∈ Set.Icc (-1 : ℝ) 1
  apply (Measure.ae_prod_iff_ae_ae
    ((measurable_fst.comp measurable_fst) measurableSet_Icc)).2
  filter_upwards [hnoise] with w hw
  exact Filter.Eventually.of_forall (fun _ => hw)

theorem sparseRealMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseRealMeasure α x N) := by
  intro α x N
  unfold sparseRealMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_sparsePopulationEncode.aemeasurable).2
      (sparsePopulationMeasure_probability α x N)

theorem sparsePopulationDecode_realMeasure_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map sparsePopulationDecode =
    sparsePopulationMeasure α x N := by
  intro α x N
  unfold sparseRealMeasure
  rw [Measure.map_map measurable_sparsePopulationDecode measurable_sparsePopulationEncode]
  calc
    (sparsePopulationMeasure α x N).map
        (sparsePopulationDecode ∘ sparsePopulationEncode) =
        (sparsePopulationMeasure α x N).map id := by
      apply Measure.map_congr
      filter_upwards [sparsePopulation_noise_mem_Icc_ae α x N] with z hz
      exact sparsePopulationDecode_encode z hz
    _ = sparsePopulationMeasure α x N := Measure.map_id

theorem sparsePopulationEncode_decode_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ∀ᵐ y ∂sparseRealMeasure α x N,
    sparsePopulationEncode (sparsePopulationDecode y) = y := by
  intro α x N
  unfold sparseRealMeasure
  apply (ae_map_iff measurable_sparsePopulationEncode.aemeasurable
    (measurableSet_eq_fun
      (measurable_sparsePopulationEncode.comp measurable_sparsePopulationDecode)
      measurable_id)).mpr
  filter_upwards [sparsePopulation_noise_mem_Icc_ae α x N] with z hz
  exact congrArg sparsePopulationEncode (sparsePopulationDecode_encode z hz)

theorem measurePreserving_sparsePopulationEncode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  MeasurePreserving sparsePopulationEncode
    (sparsePopulationMeasure α x N) (sparseRealMeasure α x N) := by
  intro α x N
  exact ⟨measurable_sparsePopulationEncode, rfl⟩

theorem measurePreserving_sparsePopulationDecode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  MeasurePreserving sparsePopulationDecode
    (sparseRealMeasure α x N) (sparsePopulationMeasure α x N) := by
  intro α x N
  exact ⟨measurable_sparsePopulationDecode, sparsePopulationDecode_realMeasure_law α x N⟩

theorem sparsePopulationDecode_realMeasure_prod_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)).map
    (Prod.map sparsePopulationDecode sparsePopulationDecode) =
    (sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseRealMeasure α x N) :=
    sparseRealMeasure_probability α x N
  simpa only [sparsePopulationDecode_realMeasure_law α x N] using
    (Measure.map_prod_map (sparseRealMeasure α x N) (sparseRealMeasure α x N)
      measurable_sparsePopulationDecode measurable_sparsePopulationDecode).symm

end Shao.OQ5.P53
