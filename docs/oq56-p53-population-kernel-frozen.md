# Frozen actual p53 kernel and positive residual contracts

Two literal definitions and thirteen theorem types were frozen before implementation. Freeze JSON SHA256 6d4caa96f3eb32525113b4f51cff7c9aad196e912a91b86c843b31454fe33839; original p53 SHA256 0bfadbb2021248859f8b15df2ff184c73c879a7203991c27fdc4f5dd6c04f561.

```lean
def sparsePopulationKernel (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (u v : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))) : ℝ :=
  sparsePopulationG α x N u + sparsePopulationG α x N v +
    sparsePopulationZ α x N u * sparsePopulationZ α x N v

def sparsePopulationResidual (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (u v : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))) : ℝ :=
  sparsePopulationZ α x N u * sparsePopulationZ α x N v

theorem measurable_sparsePopulationKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Measurable (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) => sparsePopulationKernel α x N w.1 w.2)

theorem sparsePopulationKernel_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (u v : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))),
  sparsePopulationKernel α x N u v = sparsePopulationKernel α x N v u

theorem integrable_sparsePopulationKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) => sparsePopulationKernel α x N w.1 w.2)
    ((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N))

theorem integrable_sparsePopulationKernel_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) => |sparsePopulationKernel α x N w.1 w.2| ^ q)
    ((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N))

theorem integrable_sparsePopulationKernel_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  Integrable (sparsePopulationKernel α x N u) (sparsePopulationMeasure α x N)

theorem integral_sparsePopulationKernel_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  (∫ v, sparsePopulationKernel α x N u v ∂(sparsePopulationMeasure α x N)) = sparsePopulationG α x N u

theorem integral_sparsePopulationKernel_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)), sparsePopulationKernel α x N w.1 w.2
    ∂((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N))) = 0

theorem sparsePopulationResidual_decomposition :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (u v : ((ℝ × (ℕ × Bool)) × (ℕ × Bool))),
  sparsePopulationKernel α x N u v - sparsePopulationG α x N u - sparsePopulationG α x N v =
    sparsePopulationResidual α x N u v

theorem integrable_sparsePopulationResidual_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  Integrable (sparsePopulationResidual α x N u) (sparsePopulationMeasure α x N)

theorem integral_sparsePopulationResidual_right_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ u : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)),
  (∫ v, sparsePopulationResidual α x N u v ∂(sparsePopulationMeasure α x N)) = 0

theorem integrable_sparsePopulationResidual_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  Integrable (fun w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) =>
      (sparsePopulationResidual α x N w.1 w.2) ^ 2)
    ((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N))

theorem integral_sparsePopulationResidual_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)), (sparsePopulationResidual α x N w.1 w.2) ^ 2
    ∂((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N))) =
    (∫ u, (sparsePopulationZ α x N u) ^ 2 ∂(sparsePopulationMeasure α x N)) ^ 2

theorem integral_sparsePopulationResidual_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ w : ((ℝ × (ℕ × Bool)) × (ℕ × Bool)) × ((ℝ × (ℕ × Bool)) × (ℕ × Bool)), (sparsePopulationResidual α x N w.1 w.2) ^ 2
    ∂((sparsePopulationMeasure α x N).prod (sparsePopulationMeasure α x N))
```
