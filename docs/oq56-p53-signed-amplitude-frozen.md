# Fixed signed amplitude: frozen declarations

This module realizes p53§3 Z=epsilon*t_C on the accepted fixed tagged law. The literal definition and12 public theorem types remain exactly as frozen v1 (f90f11a337fd6e86150e0398b3c0ce4cd613d005882b6cbc1b2ecb3bd5aa7660). The parameters α, the entire supplied x and N are fixed before every q and τ. Only strict square positivity requires the same SparseSelectionCore.

## sparseSignedAmplitude

```lean
def sparseSignedAmplitude (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (z : ℕ × Bool) : ℝ :=
  if z.2 = true then sparseLevelAmplitude α x N z.1
  else -sparseLevelAmplitude α x N z.1
```

## measurable_sparseSignedAmplitude

```lean
theorem measurable_sparseSignedAmplitude :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseSignedAmplitude α x N)
```

## sparseSignedAmplitude_symmetric

```lean
theorem sparseSignedAmplitude_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseSignedLabelMeasure α x N).map (fun z => -sparseSignedAmplitude α x N z) =
    (sparseSignedLabelMeasure α x N).map (sparseSignedAmplitude α x N)
```

## integrable_sparseSignedAmplitude

```lean
theorem integrable_sparseSignedAmplitude :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → Integrable (sparseSignedAmplitude α x N) (sparseSignedLabelMeasure α x N)
```

## integral_sparseSignedAmplitude_zero

```lean
theorem integral_sparseSignedAmplitude_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ z, sparseSignedAmplitude α x N z ∂(sparseSignedLabelMeasure α x N)) = 0
```

## integrable_sparseSignedAmplitude_rpow

```lean
theorem integrable_sparseSignedAmplitude_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseSignedAmplitude α x N z| ^ q) (sparseSignedLabelMeasure α x N)
```

## integral_sparseSignedAmplitude_rpow

```lean
theorem integral_sparseSignedAmplitude_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ q : ℝ, 0 < q →
  (∫ z, |sparseSignedAmplitude α x N z| ^ q ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, |sparseLevelAmplitude α x N j| ^ q ∂(sparseLabelMeasure α x N)
```

## integrable_sparseSignedAmplitude_sq

```lean
theorem integrable_sparseSignedAmplitude_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  Integrable (fun z => (sparseSignedAmplitude α x N z) ^ 2) (sparseSignedLabelMeasure α x N)
```

## integral_sparseSignedAmplitude_sq

```lean
theorem integral_sparseSignedAmplitude_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α →
  (∫ z, (sparseSignedAmplitude α x N z) ^ 2 ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, (sparseLevelAmplitude α x N j) ^ 2 ∂(sparseLabelMeasure α x N)
```

## integral_sparseSignedAmplitude_sq_pos

```lean
theorem integral_sparseSignedAmplitude_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ z, (sparseSignedAmplitude α x N z) ^ 2 ∂(sparseSignedLabelMeasure α x N)
```

## integrable_sparseSignedAmplitude_exp

```lean
theorem integrable_sparseSignedAmplitude_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  Integrable (fun z => Real.exp (τ * |sparseSignedAmplitude α x N z| ^ α))
    (sparseSignedLabelMeasure α x N)
```

## integral_sparseSignedAmplitude_exp

```lean
theorem integral_sparseSignedAmplitude_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∫ z, Real.exp (τ * |sparseSignedAmplitude α x N z| ^ α) ∂(sparseSignedLabelMeasure α x N)) =
    ∫ j, Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α) ∂(sparseLabelMeasure α x N)
```

## integral_sparseSignedAmplitude_exp_le

```lean
theorem integral_sparseSignedAmplitude_exp_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∫ z, Real.exp (τ * |sparseSignedAmplitude α x N z| ^ α) ∂(sparseSignedLabelMeasure α x N)) ≤ (5 / 4 : ℝ)
```
