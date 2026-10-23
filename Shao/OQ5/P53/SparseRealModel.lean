import Shao.OQ5.P53.SparseRealEncoding
import Shao.OQ5.P53.SparsePopulationKernel
import Shao.OQ5.P53.SparsePopulationSymmetry

/-!
# The actual real p53 population model

Source: current/oq56/inputs02/p53.md §3. The real features are literal
compositions with the total decoder. All moment and projection identities
are transported along its actual one-observation or independent-pair law.
Integrability is established before transporting the corresponding integral.
The positive residual uses distinct observation coordinates, so its second
moment uses the second moment of Z and does not require its fourth moment.
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

def sparseRealG (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (y : ℝ) : ℝ :=
  sparsePopulationG α x N (sparsePopulationDecode y)

def sparseRealZ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (y : ℝ) : ℝ :=
  sparsePopulationZ α x N (sparsePopulationDecode y)

def sparseRealKernel (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (u v : ℝ) : ℝ :=
  sparseRealG α x N u + sparseRealG α x N v +
    sparseRealZ α x N u * sparseRealZ α x N v

def sparseRealResidual (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (u v : ℝ) : ℝ :=
  sparseRealZ α x N u * sparseRealZ α x N v

private theorem real_map_decode {E : Type*} [MeasurableSpace E]
    (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (f : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) → E) (hf : Measurable f) :
    (sparseRealMeasure α x N).map (f ∘ sparsePopulationDecode) =
      (sparsePopulationMeasure α x N).map f := by
  rw [← Measure.map_map hf measurable_sparsePopulationDecode,
    sparsePopulationDecode_realMeasure_law α x N]

private theorem real_decode_lift
    (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (f : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) → ℝ)
    (hf : Integrable f (sparsePopulationMeasure α x N)) :
    Integrable (fun y => f (sparsePopulationDecode y)) (sparseRealMeasure α x N) ∧
      (∫ y, f (sparsePopulationDecode y) ∂(sparseRealMeasure α x N)) =
        ∫ z, f z ∂(sparsePopulationMeasure α x N) := by
  have hmp := measurePreserving_sparsePopulationDecode α x N
  have hfm : AEStronglyMeasurable f
      ((sparseRealMeasure α x N).map sparsePopulationDecode) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  constructor
  · exact hmp.integrable_comp_of_integrable hf
  · calc
      (∫ y, f (sparsePopulationDecode y) ∂(sparseRealMeasure α x N)) =
          ∫ z, f z ∂((sparseRealMeasure α x N).map sparsePopulationDecode) :=
        (integral_map hmp.measurable.aemeasurable hfm).symm
      _ = ∫ z, f z ∂(sparsePopulationMeasure α x N) := by rw [hmp.map_eq]

private theorem real_pair_decode_lift
    (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (f : (((ℝ × (ℕ × Bool)) × (ℕ × Bool)) ×
      ((ℝ × (ℕ × Bool)) × (ℕ × Bool))) → ℝ)
    (hf : Integrable f
      ((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N))) :
    Integrable (fun w : ℝ × ℝ =>
        f (Prod.map sparsePopulationDecode sparsePopulationDecode w))
      ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)) ∧
      (∫ w : ℝ × ℝ, f (Prod.map sparsePopulationDecode sparsePopulationDecode w)
        ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))) =
        ∫ z, f z
          ∂((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)) := by
  have hmp : MeasurePreserving (Prod.map sparsePopulationDecode sparsePopulationDecode)
      ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))
      ((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)) :=
    ⟨measurable_sparsePopulationDecode.prodMap measurable_sparsePopulationDecode,
      sparsePopulationDecode_realMeasure_prod_law α x N⟩
  have hfm : AEStronglyMeasurable f
      (((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)).map
        (Prod.map sparsePopulationDecode sparsePopulationDecode)) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  constructor
  · exact hmp.integrable_comp_of_integrable hf
  · calc
      (∫ w : ℝ × ℝ, f (Prod.map sparsePopulationDecode sparsePopulationDecode w)
          ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))) =
          ∫ z, f z
            ∂(((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)).map
              (Prod.map sparsePopulationDecode sparsePopulationDecode)) :=
        (integral_map hmp.measurable.aemeasurable hfm).symm
      _ = ∫ z, f z
          ∂((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)) := by
        rw [hmp.map_eq]

private theorem population_G_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) (hN : SparseSelectionCore α x N) :
    Integrable (sparsePopulationG α x N) (sparsePopulationMeasure α x N) := by
  apply (integrable_norm_iff
    (measurable_sparsePopulationG α x N).aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs, Real.rpow_one] using
    integrable_sparsePopulationG_rpow α x N hα hN 1 (by norm_num)

private theorem population_Z_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) :
    Integrable (sparsePopulationZ α x N) (sparsePopulationMeasure α x N) := by
  apply (integrable_norm_iff
    (measurable_sparsePopulationZ α x N).aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs, Real.rpow_one] using
    integrable_sparsePopulationZ_rpow α x N hα 1 (by norm_num)

private theorem population_G_sq_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) (hN : SparseSelectionCore α x N) :
    Integrable (fun z => (sparsePopulationG α x N z) ^ 2)
      (sparsePopulationMeasure α x N) := by
  simpa only [Real.rpow_two, sq_abs] using
    integrable_sparsePopulationG_rpow α x N hα hN 2 (by norm_num)

private theorem population_Z_sq_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) :
    Integrable (fun z => (sparsePopulationZ α x N z) ^ 2)
      (sparsePopulationMeasure α x N) := by
  simpa only [Real.rpow_two, sq_abs] using
    integrable_sparsePopulationZ_rpow α x N hα 2 (by norm_num)

theorem measurable_sparseRealG :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseRealG α x N) := by
  intro α x N
  exact (measurable_sparsePopulationG α x N).comp measurable_sparsePopulationDecode

theorem measurable_sparseRealZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseRealZ α x N) := by
  intro α x N
  exact (measurable_sparsePopulationZ α x N).comp measurable_sparsePopulationDecode

theorem sparseRealG_indep_Z :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ProbabilityTheory.IndepFun (sparseRealG α x N) (sparseRealZ α x N)
    (sparseRealMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseRealMeasure α x N) :=
    sparseRealMeasure_probability α x N
  let : IsProbabilityMeasure (sparsePopulationMeasure α x N) :=
    sparsePopulationMeasure_probability α x N
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_sparseRealG α x N).aemeasurable
    (measurable_sparseRealZ α x N).aemeasurable).2
  change (sparseRealMeasure α x N).map
      ((fun z => (sparsePopulationG α x N z, sparsePopulationZ α x N z)) ∘
        sparsePopulationDecode) =
    ((sparseRealMeasure α x N).map (sparsePopulationG α x N ∘ sparsePopulationDecode)).prod
      ((sparseRealMeasure α x N).map (sparsePopulationZ α x N ∘ sparsePopulationDecode))
  rw [real_map_decode α x N _
      ((measurable_sparsePopulationG α x N).prodMk (measurable_sparsePopulationZ α x N)),
    real_map_decode α x N _ (measurable_sparsePopulationG α x N),
    real_map_decode α x N _ (measurable_sparsePopulationZ α x N)]
  exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_sparsePopulationG α x N).aemeasurable
    (measurable_sparsePopulationZ α x N).aemeasurable).1
      (sparsePopulationG_indep_Z α x N)

theorem integrable_sparseRealG_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseRealG α x N z| ^ q) (sparseRealMeasure α x N) := by
  intro α x N hα hN q hq
  exact (real_decode_lift α x N (fun z => |sparsePopulationG α x N z| ^ q)
    (integrable_sparsePopulationG_rpow α x N hα hN q hq)).1

theorem integrable_sparseRealZ_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseRealZ α x N z| ^ q) (sparseRealMeasure α x N) := by
  intro α x N hα q hq
  exact (real_decode_lift α x N (fun z => |sparsePopulationZ α x N z| ^ q)
    (integrable_sparsePopulationZ_rpow α x N hα q hq)).1

theorem integral_sparseRealG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparseRealG α x N z ∂(sparseRealMeasure α x N)) = 0 := by
  intro α x N hα hN
  exact (real_decode_lift α x N (sparsePopulationG α x N)
    (population_G_integrable α x N hα hN)).2.trans
      (integral_sparsePopulationG_zero α x N hα hN)

theorem integral_sparseRealZ_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ z, sparseRealZ α x N z ∂(sparseRealMeasure α x N)) = 0 := by
  intro α x N hα
  exact (real_decode_lift α x N (sparsePopulationZ α x N)
    (population_Z_integrable α x N hα)).2.trans
      (integral_sparsePopulationZ_zero α x N hα)

theorem integral_sparseRealG_sq_ge :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (1 / 3 : ℝ) ≤ ∫ z, (sparseRealG α x N z) ^ 2 ∂(sparseRealMeasure α x N) := by
  intro α x N hα hN
  obtain ⟨_, hsecond⟩ := real_decode_lift α x N
    (fun z => (sparsePopulationG α x N z) ^ 2)
    (population_G_sq_integrable α x N hα hN)
  calc
    (1 / 3 : ℝ) ≤ ∫ z, (sparsePopulationG α x N z) ^ 2
        ∂(sparsePopulationMeasure α x N) := integral_sparsePopulationG_sq_ge α x N hα hN
    _ = ∫ z, (sparseRealG α x N z) ^ 2 ∂(sparseRealMeasure α x N) := hsecond.symm

theorem integral_sparseRealZ_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ z, (sparseRealZ α x N z) ^ 2 ∂(sparseRealMeasure α x N) := by
  intro α x N hα hN
  obtain ⟨_, hsecond⟩ := real_decode_lift α x N
    (fun z => (sparsePopulationZ α x N z) ^ 2)
    (population_Z_sq_integrable α x N hα)
  calc
    0 < ∫ z, (sparsePopulationZ α x N z) ^ 2
        ∂(sparsePopulationMeasure α x N) := integral_sparsePopulationZ_sq_pos α x N hα hN
    _ = ∫ z, (sparseRealZ α x N z) ^ 2 ∂(sparseRealMeasure α x N) := hsecond.symm

theorem integrable_sparseRealZ_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  Integrable (fun z => Real.exp (τ * |sparseRealZ α x N z| ^ α))
    (sparseRealMeasure α x N) := by
  intro α x N hα τ hτ hτ1
  exact (real_decode_lift α x N
    (fun z => Real.exp (τ * |sparsePopulationZ α x N z| ^ α))
    (integrable_sparsePopulationZ_exp α x N hα τ hτ hτ1)).1

theorem integral_sparseRealZ_exp_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∫ z, Real.exp (τ * |sparseRealZ α x N z| ^ α) ∂(sparseRealMeasure α x N)) ≤ (5 / 4 : ℝ) := by
  intro α x N hα τ hτ hτ1
  obtain ⟨_, hexp⟩ := real_decode_lift α x N
    (fun z => Real.exp (τ * |sparsePopulationZ α x N z| ^ α))
    (integrable_sparsePopulationZ_exp α x N hα τ hτ hτ1)
  calc
    (∫ z, Real.exp (τ * |sparseRealZ α x N z| ^ α) ∂(sparseRealMeasure α x N)) =
        ∫ z, Real.exp (τ * |sparsePopulationZ α x N z| ^ α)
          ∂(sparsePopulationMeasure α x N) := hexp
    _ ≤ (5 / 4 : ℝ) := integral_sparsePopulationZ_exp_le α x N hα τ hτ hτ1

theorem measurable_sparseRealKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Measurable (fun w : ℝ × ℝ => sparseRealKernel α x N w.1 w.2) := by
  intro α x N
  exact (measurable_sparsePopulationKernel α x N).comp
    (measurable_sparsePopulationDecode.prodMap measurable_sparsePopulationDecode)

theorem sparseRealKernel_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (u v : ℝ),
  sparseRealKernel α x N u v = sparseRealKernel α x N v u := by
  intro α x N u v
  exact sparsePopulationKernel_symmetric α x N
    (sparsePopulationDecode u) (sparsePopulationDecode v)

theorem integrable_sparseRealKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (fun w : ℝ × ℝ => sparseRealKernel α x N w.1 w.2)
    ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)) := by
  intro α x N hα hN
  exact (real_pair_decode_lift α x N
    (fun w => sparsePopulationKernel α x N w.1 w.2)
    (integrable_sparsePopulationKernel α x N hα hN)).1

theorem integrable_sparseRealKernel_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun w : ℝ × ℝ => |sparseRealKernel α x N w.1 w.2| ^ q)
    ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)) := by
  intro α x N hα hN q hq
  exact (real_pair_decode_lift α x N
    (fun w => |sparsePopulationKernel α x N w.1 w.2| ^ q)
    (integrable_sparsePopulationKernel_rpow α x N hα hN q hq)).1

theorem integrable_sparseRealKernel_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ℝ,
  Integrable (sparseRealKernel α x N u) (sparseRealMeasure α x N) := by
  intro α x N hα hN u
  exact (real_decode_lift α x N
    (sparsePopulationKernel α x N (sparsePopulationDecode u))
    (integrable_sparsePopulationKernel_right α x N hα hN (sparsePopulationDecode u))).1

theorem integral_sparseRealKernel_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ℝ,
  (∫ v, sparseRealKernel α x N u v ∂(sparseRealMeasure α x N)) = sparseRealG α x N u := by
  intro α x N hα hN u
  exact (real_decode_lift α x N
    (sparsePopulationKernel α x N (sparsePopulationDecode u))
    (integrable_sparsePopulationKernel_right α x N hα hN (sparsePopulationDecode u))).2.trans
      (integral_sparsePopulationKernel_right α x N hα hN (sparsePopulationDecode u))

theorem integral_sparseRealKernel_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ w : ℝ × ℝ, sparseRealKernel α x N w.1 w.2
    ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))) = 0 := by
  intro α x N hα hN
  exact (real_pair_decode_lift α x N
    (fun w => sparsePopulationKernel α x N w.1 w.2)
    (integrable_sparsePopulationKernel α x N hα hN)).2.trans
      (integral_sparsePopulationKernel_zero α x N hα hN)

theorem sparseRealResidual_decomposition :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (u v : ℝ),
  sparseRealKernel α x N u v - sparseRealG α x N u - sparseRealG α x N v =
    sparseRealResidual α x N u v := by
  intro α x N u v
  exact sparsePopulationResidual_decomposition α x N
    (sparsePopulationDecode u) (sparsePopulationDecode v)

theorem integrable_sparseRealResidual_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ u : ℝ,
  Integrable (sparseRealResidual α x N u) (sparseRealMeasure α x N) := by
  intro α x N hα u
  exact (real_decode_lift α x N
    (sparsePopulationResidual α x N (sparsePopulationDecode u))
    (integrable_sparsePopulationResidual_right α x N hα (sparsePopulationDecode u))).1

theorem integral_sparseRealResidual_right_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ u : ℝ,
  (∫ v, sparseRealResidual α x N u v ∂(sparseRealMeasure α x N)) = 0 := by
  intro α x N hα u
  exact (real_decode_lift α x N
    (sparsePopulationResidual α x N (sparsePopulationDecode u))
    (integrable_sparsePopulationResidual_right α x N hα (sparsePopulationDecode u))).2.trans
      (integral_sparsePopulationResidual_right_zero α x N hα (sparsePopulationDecode u))

theorem integrable_sparseRealResidual_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  Integrable (fun w : ℝ × ℝ =>
      (sparseRealResidual α x N w.1 w.2) ^ 2)
    ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)) := by
  intro α x N hα
  exact (real_pair_decode_lift α x N
    (fun w => (sparsePopulationResidual α x N w.1 w.2) ^ 2)
    (integrable_sparsePopulationResidual_sq α x N hα)).1

theorem integral_sparseRealResidual_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ w : ℝ × ℝ, (sparseRealResidual α x N w.1 w.2) ^ 2
    ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))) =
    (∫ u, (sparseRealZ α x N u) ^ 2 ∂(sparseRealMeasure α x N)) ^ 2 := by
  intro α x N hα
  obtain ⟨_, hpair⟩ := real_pair_decode_lift α x N
    (fun w => (sparsePopulationResidual α x N w.1 w.2) ^ 2)
    (integrable_sparsePopulationResidual_sq α x N hα)
  obtain ⟨_, hsecond⟩ := real_decode_lift α x N
    (fun z => (sparsePopulationZ α x N z) ^ 2)
    (population_Z_sq_integrable α x N hα)
  calc
    (∫ w : ℝ × ℝ, (sparseRealResidual α x N w.1 w.2) ^ 2
        ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))) =
        ∫ w, (sparsePopulationResidual α x N w.1 w.2) ^ 2
          ∂((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N)) := hpair
    _ = (∫ u, (sparsePopulationZ α x N u) ^ 2
        ∂(sparsePopulationMeasure α x N)) ^ 2 :=
      integral_sparsePopulationResidual_sq α x N hα
    _ = (∫ u, (sparseRealZ α x N u) ^ 2 ∂(sparseRealMeasure α x N)) ^ 2 :=
      congrArg (fun t : ℝ => t ^ 2) hsecond.symm

theorem integral_sparseRealResidual_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ w : ℝ × ℝ, (sparseRealResidual α x N w.1 w.2) ^ 2
    ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)) := by
  intro α x N hα hN
  rw [integral_sparseRealResidual_sq α x N hα]
  exact pow_pos (integral_sparseRealZ_sq_pos α x N hα hN) 2

theorem sparseRealG_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map (fun z => -sparseRealG α x N z) =
    (sparseRealMeasure α x N).map (sparseRealG α x N) := by
  intro α x N
  calc
    (sparseRealMeasure α x N).map (fun z => -sparseRealG α x N z) =
        (sparsePopulationMeasure α x N).map (fun z => -sparsePopulationG α x N z) :=
      real_map_decode α x N _ (measurable_sparsePopulationG α x N).neg
    _ = (sparsePopulationMeasure α x N).map (sparsePopulationG α x N) :=
      sparsePopulationG_symmetric α x N
    _ = (sparseRealMeasure α x N).map (sparseRealG α x N) :=
      (real_map_decode α x N _ (measurable_sparsePopulationG α x N)).symm

theorem sparseRealZ_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map (fun z => -sparseRealZ α x N z) =
    (sparseRealMeasure α x N).map (sparseRealZ α x N) := by
  intro α x N
  calc
    (sparseRealMeasure α x N).map (fun z => -sparseRealZ α x N z) =
        (sparsePopulationMeasure α x N).map (fun z => -sparsePopulationZ α x N z) :=
      real_map_decode α x N _ (measurable_sparsePopulationZ α x N).neg
    _ = (sparsePopulationMeasure α x N).map (sparsePopulationZ α x N) :=
      sparsePopulationZ_symmetric α x N
    _ = (sparseRealMeasure α x N).map (sparseRealZ α x N) :=
      (real_map_decode α x N _ (measurable_sparsePopulationZ α x N)).symm

theorem sparseRealG_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map (sparseRealG α x N) =
    (sparsePopulationMeasure α x N).map (sparsePopulationG α x N) := by
  intro α x N
  exact real_map_decode α x N _ (measurable_sparsePopulationG α x N)

theorem sparseRealZ_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map (sparseRealZ α x N) =
    (sparsePopulationMeasure α x N).map (sparsePopulationZ α x N) := by
  intro α x N
  exact real_map_decode α x N _ (measurable_sparsePopulationZ α x N)

end Shao.OQ5.P53
