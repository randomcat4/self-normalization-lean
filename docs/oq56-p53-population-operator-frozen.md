# Frozen actual p53 full-L2 positive rank-one operator contracts (v2)

Two literal definitions and fourteen theorem types frozen before implementation. V1 preserved; before candidate02 only four unused hypothesis binder names hα became _hα. Actual types are alpha-equivalent, all assumptions/conclusions/definitions/proofs unchanged. V2 JSON SHA256 e040e730ab645844f1b135d13866bb84a042c4c65bcdc19c0a1ffda18a9af896; original p53 section3.

```lean
theorem memLp_sparsePopulationZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α),
  MemLp (sparsePopulationZ α x N) 2 (sparsePopulationMeasure α x N)

def sparsePopulationFeatureL2 (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    Lp ℝ 2 (sparsePopulationMeasure α x N) :=
  (memLp_sparsePopulationZ α x N hα).toLp (sparsePopulationZ α x N)

def sparsePopulationResidualOperator (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    (Lp ℝ 2 (sparsePopulationMeasure α x N)) →L[ℝ] (Lp ℝ 2 (sparsePopulationMeasure α x N)) :=
  InnerProductSpace.rankOne ℝ (sparsePopulationFeatureL2 α x N hα) (sparsePopulationFeatureL2 α x N hα)

theorem sparsePopulationFeatureL2_coe :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  (sparsePopulationFeatureL2 α x N hα : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) → ℝ) =ᵐ[(sparsePopulationMeasure α x N)] sparsePopulationZ α x N

theorem integrable_sparsePopulationZ_mul_Lp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  Integrable (fun u => sparsePopulationZ α x N u * f u) (sparsePopulationMeasure α x N)

theorem inner_sparsePopulationFeatureL2 :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  inner ℝ (sparsePopulationFeatureL2 α x N hα) f = ∫ u, sparsePopulationZ α x N u * f u ∂(sparsePopulationMeasure α x N)

theorem inner_sparsePopulationFeatureL2_self :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  inner ℝ (sparsePopulationFeatureL2 α x N hα) (sparsePopulationFeatureL2 α x N hα) = ∫ u, (sparsePopulationZ α x N u) ^ 2 ∂(sparsePopulationMeasure α x N)

theorem sparsePopulationFeatureL2_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparsePopulationFeatureL2 α x N hα ≠ 0

theorem integrable_sparsePopulationResidual_mul_Lp_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ (f : Lp ℝ 2 (sparsePopulationMeasure α x N)) (u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))),
  Integrable (fun v => sparsePopulationResidual α x N u v * f v) (sparsePopulationMeasure α x N)

theorem sparsePopulationResidualOperator_apply_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  (sparsePopulationResidualOperator α x N hα f : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) → ℝ) =ᵐ[(sparsePopulationMeasure α x N)]
    (fun u => ∫ v, sparsePopulationResidual α x N u v * f v ∂(sparsePopulationMeasure α x N))

theorem memLp_sparsePopulationResidualIntegral :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  MemLp (fun u => ∫ v, sparsePopulationResidual α x N u v * f v ∂(sparsePopulationMeasure α x N)) 2 (sparsePopulationMeasure α x N)

theorem sparsePopulationResidualOperator_isSelfAdjoint :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  IsSelfAdjoint (sparsePopulationResidualOperator α x N hα)

theorem sparsePopulationResidualOperator_quadratic :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  inner ℝ f (sparsePopulationResidualOperator α x N hα f) = (inner ℝ (sparsePopulationFeatureL2 α x N hα) f) ^ 2

theorem sparsePopulationResidualOperator_positive :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparsePopulationMeasure α x N),
  0 ≤ inner ℝ f (sparsePopulationResidualOperator α x N hα f)

theorem sparsePopulationResidualOperator_rank :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  (sparsePopulationResidualOperator α x N hα).toLinearMap.rank = 1

theorem sparsePopulationResidualOperator_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparsePopulationResidualOperator α x N hα ≠ 0
```
