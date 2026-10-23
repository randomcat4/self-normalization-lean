import Shao.OQ5.P53.SparsePopulation

/-!
# Actual p53 sparse population kernel and canonical residual

The law and the full sequences are fixed before the moment exponent. The
residual has the source's positive sign. Products below use two distinct
observation coordinates; their second moments need no fourth moment of Z.
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

def sparsePopulationKernel (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (u v : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))) : ℝ :=
  sparsePopulationG α x N u + sparsePopulationG α x N v +
    sparsePopulationZ α x N u * sparsePopulationZ α x N v

def sparsePopulationResidual (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (u v : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))) : ℝ :=
  sparsePopulationZ α x N u * sparsePopulationZ α x N v

private theorem population_G_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) (hN : SparseSelectionCore α x N) :
    Integrable (sparsePopulationG α x N) (sparsePopulationMeasure α x N) := by
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  exact (integrable_sparseG α x N hα hN).comp_fst (sparseSignedLabelMeasure α x N)

private theorem population_Z_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) :
    Integrable (sparsePopulationZ α x N) (sparsePopulationMeasure α x N) := by
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  exact (integrable_sparseSignedAmplitude α x N hα).comp_snd
    (sparseGBaseMeasure α x N)

private theorem population_Z_sq_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) :
    Integrable (fun u => (sparsePopulationZ α x N u) ^ 2)
      (sparsePopulationMeasure α x N) := by
  simpa only [Real.rpow_two, sq_abs] using
    integrable_sparsePopulationZ_rpow α x N hα 2 (by norm_num)

private theorem abs_add_rpow_bound (a b q : ℝ) (hq : 0 ≤ q) :
    |a + b| ^ q ≤ (2 : ℝ) ^ q * (|a| ^ q + |b| ^ q) := by
  have htwo : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) q
  have haq : 0 ≤ |a| ^ q := Real.rpow_nonneg (abs_nonneg a) q
  have hbq : 0 ≤ |b| ^ q := Real.rpow_nonneg (abs_nonneg b) q
  have htri : |a + b| ≤ |a| + |b| := by
    simpa only [Real.norm_eq_abs] using norm_add_le a b
  rcases le_total |a| |b| with hab | hba
  · have habs : |a + b| ≤ 2 * |b| := htri.trans (by linarith)
    calc
      |a + b| ^ q ≤ (2 * |b|) ^ q :=
        Real.rpow_le_rpow (abs_nonneg _) habs hq
      _ = (2 : ℝ) ^ q * |b| ^ q := Real.mul_rpow (by norm_num) (abs_nonneg b)
      _ ≤ (2 : ℝ) ^ q * (|a| ^ q + |b| ^ q) := by
        nlinarith [mul_nonneg htwo haq]
  · have habs : |a + b| ≤ 2 * |a| := htri.trans (by linarith)
    calc
      |a + b| ^ q ≤ (2 * |a|) ^ q :=
        Real.rpow_le_rpow (abs_nonneg _) habs hq
      _ = (2 : ℝ) ^ q * |a| ^ q := Real.mul_rpow (by norm_num) (abs_nonneg a)
      _ ≤ (2 : ℝ) ^ q * (|a| ^ q + |b| ^ q) := by
        nlinarith [mul_nonneg htwo hbq]

private theorem integrable_abs_add_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (q : ℝ) (hq : 0 < q)
    (hfi : Integrable (fun u => |f u| ^ q) μ)
    (hgi : Integrable (fun u => |g u| ^ q) μ) :
    Integrable (fun u => |f u + g u| ^ q) μ := by
  have hc : Continuous (fun t : ℝ => |t| ^ q) :=
    continuous_abs.rpow_const (fun _ => Or.inr hq.le)
  apply ((hfi.add hgi).const_mul ((2 : ℝ) ^ q)).mono'
    (hc.measurable.comp (hf.add hg)).aestronglyMeasurable
  filter_upwards [] with u
  change ‖|f u + g u| ^ q‖ ≤ (2 : ℝ) ^ q * (|f u| ^ q + |g u| ^ q)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) q)]
  exact abs_add_rpow_bound (f u) (g u) q hq.le

theorem measurable_sparsePopulationKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Measurable (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) => sparsePopulationKernel α x N w.1 w.2) := by
  intro α x N
  exact (((measurable_sparsePopulationG α x N).comp measurable_fst).add
    ((measurable_sparsePopulationG α x N).comp measurable_snd)).add
    (((measurable_sparsePopulationZ α x N).comp measurable_fst).mul
      ((measurable_sparsePopulationZ α x N).comp measurable_snd))

theorem sparsePopulationKernel_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (u v : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))),
  sparsePopulationKernel α x N u v = sparsePopulationKernel α x N v u := by
  intro α x N u v
  unfold sparsePopulationKernel
  ring

theorem integrable_sparsePopulationKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) => sparsePopulationKernel α x N w.1 w.2)
    ((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)) := by
  intro α x N hα hN
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  have hG := population_G_integrable α x N hα hN
  have hZ := population_Z_integrable α x N hα
  exact ((hG.comp_fst _).add (hG.comp_snd _)).add (hZ.mul_prod hZ)

theorem integrable_sparsePopulationKernel_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) => |sparsePopulationKernel α x N w.1 w.2| ^ q)
    ((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)) := by
  intro α x N hα hN q hq
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  have hG := integrable_sparsePopulationG_rpow α x N hα hN q hq
  have hZ := integrable_sparsePopulationZ_rpow α x N hα q hq
  have hGf : Measurable
      (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) =>
        sparsePopulationG α x N w.1) :=
    (measurable_sparsePopulationG α x N).comp measurable_fst
  have hGs : Measurable
      (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) =>
        sparsePopulationG α x N w.2) :=
    (measurable_sparsePopulationG α x N).comp measurable_snd
  have hZf : Measurable
      (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) =>
        sparsePopulationZ α x N w.1) :=
    (measurable_sparsePopulationZ α x N).comp measurable_fst
  have hZs : Measurable
      (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) =>
        sparsePopulationZ α x N w.2) :=
    (measurable_sparsePopulationZ α x N).comp measurable_snd
  have hZprod : Integrable
      (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) =>
        |sparsePopulationZ α x N w.1 * sparsePopulationZ α x N w.2| ^ q)
      ((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)) := by
    simpa only [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)] using
      hZ.mul_prod hZ
  exact integrable_abs_add_rpow _ _ _ (hGf.add hGs) (hZf.mul hZs) q hq
    (integrable_abs_add_rpow _ _ _ hGf hGs q hq (hG.comp_fst _) (hG.comp_snd _))
    hZprod

theorem integrable_sparsePopulationKernel_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  Integrable (sparsePopulationKernel α x N u) (sparsePopulationMeasure α x N) := by
  intro α x N hα hN u
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  exact ((integrable_const (sparsePopulationG α x N u)).add
    (population_G_integrable α x N hα hN)).add
    ((population_Z_integrable α x N hα).const_mul (sparsePopulationZ α x N u))

theorem integral_sparsePopulationKernel_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  (∫ v, sparsePopulationKernel α x N u v ∂(sparsePopulationMeasure α x N)) = sparsePopulationG α x N u := by
  intro α x N hα hN u
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  have hconst : Integrable (fun _ => sparsePopulationG α x N u)
      (sparsePopulationMeasure α x N) := integrable_const _
  have hG := population_G_integrable α x N hα hN
  have hsum : Integrable (fun v => sparsePopulationG α x N u + sparsePopulationG α x N v)
      (sparsePopulationMeasure α x N) := hconst.add hG
  have hZprod := (population_Z_integrable α x N hα).const_mul
    (sparsePopulationZ α x N u)
  unfold sparsePopulationKernel
  rw [integral_add hsum hZprod, integral_add hconst hG,
    integral_const_mul, integral_sparsePopulationG_zero α x N hα hN,
    integral_sparsePopulationZ_zero α x N hα]
  simp

theorem integral_sparsePopulationKernel_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)), sparsePopulationKernel α x N w.1 w.2
    ∂((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N))) = 0 := by
  intro α x N hα hN
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  rw [integral_prod _ (integrable_sparsePopulationKernel α x N hα hN)]
  simp_rw [integral_sparsePopulationKernel_right α x N hα hN]
  exact integral_sparsePopulationG_zero α x N hα hN

theorem sparsePopulationResidual_decomposition :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (u v : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))),
  sparsePopulationKernel α x N u v - sparsePopulationG α x N u - sparsePopulationG α x N v =
    sparsePopulationResidual α x N u v := by
  intro α x N u v
  unfold sparsePopulationKernel sparsePopulationResidual
  ring

theorem integrable_sparsePopulationResidual_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  Integrable (sparsePopulationResidual α x N u) (sparsePopulationMeasure α x N) := by
  intro α x N hα u
  exact (population_Z_integrable α x N hα).const_mul (sparsePopulationZ α x N u)

theorem integral_sparsePopulationResidual_right_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  (∫ v, sparsePopulationResidual α x N u v ∂(sparsePopulationMeasure α x N)) = 0 := by
  intro α x N hα u
  have hrow := integrable_sparsePopulationResidual_right α x N hα u
  unfold sparsePopulationResidual at hrow ⊢
  rw [integral_const_mul, integral_sparsePopulationZ_zero α x N hα, mul_zero]

theorem integrable_sparsePopulationResidual_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  Integrable (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) =>
      (sparsePopulationResidual α x N w.1 w.2) ^ 2)
    ((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)) := by
  intro α x N hα
  have hZsq := population_Z_sq_integrable α x N hα
  simpa only [sparsePopulationResidual, mul_pow] using hZsq.mul_prod hZsq

theorem integral_sparsePopulationResidual_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)), (sparsePopulationResidual α x N w.1 w.2) ^ 2
    ∂((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N))) =
    (∫ u, (sparsePopulationZ α x N u) ^ 2 ∂(sparsePopulationMeasure α x N)) ^ 2 := by
  intro α x N hα
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  rw [integral_prod _ (integrable_sparsePopulationResidual_sq α x N hα)]
  simp only [sparsePopulationResidual, mul_pow]
  simp_rw [integral_const_mul]
  rw [integral_mul_const, pow_two]

theorem integral_sparsePopulationResidual_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)), (sparsePopulationResidual α x N w.1 w.2) ^ 2
    ∂((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)) := by
  intro α x N hα hN
  rw [integral_sparsePopulationResidual_sq α x N hα]
  exact pow_pos (integral_sparsePopulationZ_sq_pos α x N hα hN) 2

end Shao.OQ5.P53
