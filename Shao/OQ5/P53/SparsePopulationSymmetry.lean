import Shao.OQ5.P53.SparsePopulation

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

private theorem noiseLaw_reflection :
    Shao.OQ5.P35.noiseLaw.map (fun t : ℝ => -t) = Shao.OQ5.P35.noiseLaw := by
  have hpreimage :
      (fun t : ℝ => -t) ⁻¹' Set.Icc (-1 : ℝ) 1 = Set.Icc (-1 : ℝ) 1 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith
  have hvolume : (volume : Measure ℝ).map (fun t : ℝ => -t) = volume := by
    simpa using (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  have hrestriction :
      ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)).map (fun t : ℝ => -t) =
        (volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1) := by
    calc
      ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)).map (fun t : ℝ => -t) =
          ((volume : Measure ℝ).map (fun t : ℝ => -t)).restrict
            (Set.Icc (-1 : ℝ) 1) := by
        rw [Measure.restrict_map measurable_neg measurableSet_Icc, hpreimage]
      _ = (volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1) := by
        rw [hvolume]
  unfold Shao.OQ5.P35.noiseLaw ProbabilityTheory.cond
  rw [Measure.map_smul _ measurable_neg.aemeasurable, hrestriction]

private theorem sparseG_reflection (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    (sparseGBaseMeasure α x N).map (fun z => -sparseG α x N z) =
      (sparseGBaseMeasure α x N).map (sparseG α x N) := by
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hpositive :
      (sparseGBaseMeasure α x N).map (Prod.map id (sparseSignedShift α x N)) =
        Shao.OQ5.P35.noiseLaw.prod
          ((sparseSignedLabelMeasure α x N).map (sparseSignedShift α x N)) := by
    unfold sparseGBaseMeasure
    rw [← Measure.map_prod_map _ _ measurable_id
      (measurable_sparseSignedShift α x N), Measure.map_id]
  have hnegative :
      (sparseGBaseMeasure α x N).map
          (Prod.map (fun t : ℝ => -t) (fun z => -sparseSignedShift α x N z)) =
        Shao.OQ5.P35.noiseLaw.prod
          ((sparseSignedLabelMeasure α x N).map (sparseSignedShift α x N)) := by
    unfold sparseGBaseMeasure
    rw [← Measure.map_prod_map
      (f := fun t : ℝ => -t) (g := fun z => -sparseSignedShift α x N z)
      _ _ measurable_neg
      (measurable_sparseSignedShift α x N).neg,
      noiseLaw_reflection, sparseSignedShift_symmetric α x N]
  have hsum : Measurable (fun y : ℝ × ℝ => y.1 + y.2) :=
    measurable_fst.add measurable_snd
  have hnegative_function :
      (fun z : ℝ × (ℕ × Bool) => -sparseG α x N z) =
        (fun y : ℝ × ℝ => y.1 + y.2) ∘
          Prod.map (fun t : ℝ => -t) (fun z => -sparseSignedShift α x N z) := by
    funext z
    change -(z.1 + sparseSignedShift α x N z.2) = -z.1 + -sparseSignedShift α x N z.2
    ring
  calc
    (sparseGBaseMeasure α x N).map (fun z => -sparseG α x N z) =
        ((sparseGBaseMeasure α x N).map
          (Prod.map (fun t : ℝ => -t) (fun z => -sparseSignedShift α x N z))).map
            (fun y : ℝ × ℝ => y.1 + y.2) := by
      rw [Measure.map_map
        (f := Prod.map (fun t : ℝ => -t) (fun z => -sparseSignedShift α x N z)) hsum
        (measurable_neg.prodMap (measurable_sparseSignedShift α x N).neg),
        hnegative_function]
    _ = (Shao.OQ5.P35.noiseLaw.prod
        ((sparseSignedLabelMeasure α x N).map (sparseSignedShift α x N))).map
          (fun y : ℝ × ℝ => y.1 + y.2) := by rw [hnegative]
    _ = ((sparseGBaseMeasure α x N).map
        (Prod.map id (sparseSignedShift α x N))).map
          (fun y : ℝ × ℝ => y.1 + y.2) := by rw [hpositive]
    _ = (sparseGBaseMeasure α x N).map (sparseG α x N) := by
      rw [Measure.map_map hsum
        (measurable_id.prodMap (measurable_sparseSignedShift α x N))]
      rfl

theorem sparsePopulationG_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparsePopulationMeasure α x N).map (fun z => -sparsePopulationG α x N z) =
    (sparsePopulationMeasure α x N).map (sparsePopulationG α x N) := by
  intro α x N
  calc
    (sparsePopulationMeasure α x N).map (fun z => -sparsePopulationG α x N z) =
        ((sparsePopulationMeasure α x N).map (sparsePopulationG α x N)).map
          (fun t : ℝ => -t) :=
      (Measure.map_map measurable_neg (measurable_sparsePopulationG α x N)).symm
    _ = ((sparseGBaseMeasure α x N).map (sparseG α x N)).map
        (fun t : ℝ => -t) := by rw [sparsePopulationG_law α x N]
    _ = (sparseGBaseMeasure α x N).map (fun z => -sparseG α x N z) :=
      Measure.map_map measurable_neg (measurable_sparseG α x N)
    _ = (sparseGBaseMeasure α x N).map (sparseG α x N) := sparseG_reflection α x N
    _ = (sparsePopulationMeasure α x N).map (sparsePopulationG α x N) :=
      (sparsePopulationG_law α x N).symm

theorem sparsePopulationZ_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparsePopulationMeasure α x N).map (fun z => -sparsePopulationZ α x N z) =
    (sparsePopulationMeasure α x N).map (sparsePopulationZ α x N) := by
  intro α x N
  calc
    (sparsePopulationMeasure α x N).map (fun z => -sparsePopulationZ α x N z) =
        ((sparsePopulationMeasure α x N).map (sparsePopulationZ α x N)).map
          (fun t : ℝ => -t) :=
      (Measure.map_map measurable_neg (measurable_sparsePopulationZ α x N)).symm
    _ = ((sparseSignedLabelMeasure α x N).map (sparseSignedAmplitude α x N)).map
        (fun t : ℝ => -t) := by rw [sparsePopulationZ_law α x N]
    _ = (sparseSignedLabelMeasure α x N).map (fun z => -sparseSignedAmplitude α x N z) :=
      Measure.map_map measurable_neg (measurable_sparseSignedAmplitude α x N)
    _ = (sparseSignedLabelMeasure α x N).map (sparseSignedAmplitude α x N) :=
      sparseSignedAmplitude_symmetric α x N
    _ = (sparsePopulationMeasure α x N).map (sparsePopulationZ α x N) :=
      (sparsePopulationZ_law α x N).symm

end Shao.OQ5.P53
