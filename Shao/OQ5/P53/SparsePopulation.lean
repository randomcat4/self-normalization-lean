import Shao.OQ5.P53.SparseProjectionLaw
import Shao.OQ5.P53.SparseSignedAmplitude

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

def sparsePopulationMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    Measure ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) :=
  (sparseGBaseMeasure α x N).prod (sparseSignedLabelMeasure α x N)

def sparsePopulationG (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (z : (ℝ × (ℕ × Bool)) × (ℕ × Bool)) : ℝ :=
  sparseG α x N z.1

def sparsePopulationZ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (z : (ℝ × (ℕ × Bool)) × (ℕ × Bool)) : ℝ :=
  sparseSignedAmplitude α x N z.2

theorem sparsePopulationMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparsePopulationMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  unfold sparsePopulationMeasure
  infer_instance

theorem sparsePopulationG_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparsePopulationMeasure α x N).map (sparsePopulationG α x N) =
    (sparseGBaseMeasure α x N).map (sparseG α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  change ((sparseGBaseMeasure α x N).prod (sparseSignedLabelMeasure α x N)).map
    (sparseG α x N ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_sparseG α x N) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

theorem sparsePopulationZ_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparsePopulationMeasure α x N).map (sparsePopulationZ α x N) =
    (sparseSignedLabelMeasure α x N).map (sparseSignedAmplitude α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  change ((sparseGBaseMeasure α x N).prod (sparseSignedLabelMeasure α x N)).map
    (sparseSignedAmplitude α x N ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_sparseSignedAmplitude α x N) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul]

theorem measurable_sparsePopulationG :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparsePopulationG α x N) := by
  intro α x N
  exact (measurable_sparseG α x N).comp measurable_fst

theorem measurable_sparsePopulationZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparsePopulationZ α x N) := by
  intro α x N
  exact (measurable_sparseSignedAmplitude α x N).comp measurable_snd

theorem sparsePopulationG_indep_Z :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ProbabilityTheory.IndepFun (sparsePopulationG α x N) (sparsePopulationZ α x N)
    (sparsePopulationMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  exact ProbabilityTheory.indepFun_prod
    (μ := sparseGBaseMeasure α x N) (ν := sparseSignedLabelMeasure α x N)
    (X := sparseG α x N) (Y := sparseSignedAmplitude α x N)
    (measurable_sparseG α x N) (measurable_sparseSignedAmplitude α x N)

private theorem population_fst_lift (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (f : ℝ × (ℕ × Bool) → ℝ)
    (hf : Integrable f (sparseGBaseMeasure α x N)) :
    Integrable (fun z : (ℝ × (ℕ × Bool)) × (ℕ × Bool) => f z.1)
        (sparsePopulationMeasure α x N) ∧
      (∫ z, f z.1 ∂(sparsePopulationMeasure α x N)) =
        ∫ w, f w ∂(sparseGBaseMeasure α x N) := by
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  constructor
  · exact hf.comp_fst (sparseSignedLabelMeasure α x N)
  · change (∫ z : (ℝ × (ℕ × Bool)) × (ℕ × Bool), f z.1
        ∂((sparseGBaseMeasure α x N).prod (sparseSignedLabelMeasure α x N))) = _
    rw [integral_fun_fst (μ := sparseGBaseMeasure α x N)
      (ν := sparseSignedLabelMeasure α x N) f]
    simp

private theorem population_snd_lift (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (f : ℕ × Bool → ℝ)
    (hf : Integrable f (sparseSignedLabelMeasure α x N)) :
    Integrable (fun z : (ℝ × (ℕ × Bool)) × (ℕ × Bool) => f z.2)
        (sparsePopulationMeasure α x N) ∧
      (∫ z, f z.2 ∂(sparsePopulationMeasure α x N)) =
        ∫ w, f w ∂(sparseSignedLabelMeasure α x N) := by
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  constructor
  · exact hf.comp_snd (sparseGBaseMeasure α x N)
  · change (∫ z : (ℝ × (ℕ × Bool)) × (ℕ × Bool), f z.2
        ∂((sparseGBaseMeasure α x N).prod (sparseSignedLabelMeasure α x N))) = _
    rw [integral_fun_snd (μ := sparseGBaseMeasure α x N)
      (ν := sparseSignedLabelMeasure α x N) f]
    simp

theorem integrable_sparsePopulationG_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparsePopulationG α x N z| ^ q) (sparsePopulationMeasure α x N) := by
  intro α x N hα hN q hq
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  exact (integrable_sparseG_rpow α x N hα hN q hq).comp_fst
    (sparseSignedLabelMeasure α x N)

theorem integrable_sparsePopulationZ_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparsePopulationZ α x N z| ^ q) (sparsePopulationMeasure α x N) := by
  intro α x N hα q hq
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  exact (integrable_sparseSignedAmplitude_rpow α x N hα q hq).comp_snd
    (sparseGBaseMeasure α x N)

theorem integral_sparsePopulationG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparsePopulationG α x N z ∂(sparsePopulationMeasure α x N)) = 0 := by
  intro α x N hα hN
  obtain ⟨hG, hmean⟩ := population_fst_lift α x N (sparseG α x N)
    (integrable_sparseG α x N hα hN)
  exact hmean.trans (integral_sparseG_zero α x N hα hN)

theorem integral_sparsePopulationZ_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ z, sparsePopulationZ α x N z ∂(sparsePopulationMeasure α x N)) = 0 := by
  intro α x N hα
  obtain ⟨hZ, hmean⟩ := population_snd_lift α x N (sparseSignedAmplitude α x N)
    (integrable_sparseSignedAmplitude α x N hα)
  exact hmean.trans (integral_sparseSignedAmplitude_zero α x N hα)

theorem integral_sparsePopulationG_sq_ge :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (1 / 3 : ℝ) ≤ ∫ z, (sparsePopulationG α x N z) ^ 2 ∂(sparsePopulationMeasure α x N) := by
  intro α x N hα hN
  obtain ⟨hGsq, hsecond⟩ :=
    population_fst_lift α x N (fun w => (sparseG α x N w) ^ 2)
      (integrable_sparseG_sq α x N hα hN)
  calc
    (1 / 3 : ℝ) ≤ ∫ w, (sparseG α x N w) ^ 2 ∂(sparseGBaseMeasure α x N) :=
      integral_sparseG_sq_ge α x N hα hN
    _ = ∫ z, (sparsePopulationG α x N z) ^ 2 ∂(sparsePopulationMeasure α x N) :=
      hsecond.symm

theorem integral_sparsePopulationZ_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ z, (sparsePopulationZ α x N z) ^ 2 ∂(sparsePopulationMeasure α x N) := by
  intro α x N hα hN
  obtain ⟨hZsq, hsecond⟩ :=
    population_snd_lift α x N (fun w => (sparseSignedAmplitude α x N w) ^ 2)
      (integrable_sparseSignedAmplitude_sq α x N hα)
  calc
    0 < ∫ w, (sparseSignedAmplitude α x N w) ^ 2 ∂(sparseSignedLabelMeasure α x N) :=
      integral_sparseSignedAmplitude_sq_pos α x N hα hN
    _ = ∫ z, (sparsePopulationZ α x N z) ^ 2 ∂(sparsePopulationMeasure α x N) :=
      hsecond.symm

theorem integrable_sparsePopulationZ_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  Integrable (fun z => Real.exp (τ * |sparsePopulationZ α x N z| ^ α))
    (sparsePopulationMeasure α x N) := by
  intro α x N hα τ hτ hτ1
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  exact (integrable_sparseSignedAmplitude_exp α x N hα τ hτ hτ1).comp_snd
    (sparseGBaseMeasure α x N)

theorem integral_sparsePopulationZ_exp_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∫ z, Real.exp (τ * |sparsePopulationZ α x N z| ^ α) ∂(sparsePopulationMeasure α x N)) ≤ (5 / 4 : ℝ) := by
  intro α x N hα τ hτ hτ1
  obtain ⟨hExp, hexp⟩ :=
    population_snd_lift α x N
      (fun w => Real.exp (τ * |sparseSignedAmplitude α x N w| ^ α))
      (integrable_sparseSignedAmplitude_exp α x N hα τ hτ hτ1)
  calc
    (∫ z, Real.exp (τ * |sparsePopulationZ α x N z| ^ α)
        ∂(sparsePopulationMeasure α x N)) =
        ∫ w, Real.exp (τ * |sparseSignedAmplitude α x N w| ^ α)
          ∂(sparseSignedLabelMeasure α x N) := hexp
    _ ≤ (5 / 4 : ℝ) := integral_sparseSignedAmplitude_exp_le α x N hα τ hτ hτ1

end Shao.OQ5.P53
