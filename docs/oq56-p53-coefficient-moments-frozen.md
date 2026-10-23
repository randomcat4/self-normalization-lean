# p53 稀疏标签测度矩：冻结接口

模块 `Shao.OQ5.P53.SparseCoefficientMoments`，命名空间 `Shao.OQ5.P53`。仅导入 `Shao.OQ5.P53.SparseLabelLaw`。以下 10 个完整类型在实现前冻结，正文逐字来自冻结字典；无公开定义。

## summable_sparseLabelMass_amplitude_rpow

```lean
theorem summable_sparseLabelMass_amplitude_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ q : ℝ, 0 < q →
  Summable (fun j : ℕ => sparseLabelMass α x N j * |sparseLevelAmplitude α x N j| ^ q)
```

## summable_sparseLabelMass_shift_rpow

```lean
theorem summable_sparseLabelMass_shift_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N →
  ∀ q : ℝ, 0 < q →
  Summable (fun j : ℕ => sparseLabelMass α x N j * |sparseLevelShift α x N j| ^ q)
```

## summable_sparseLabelMass_amplitude_exp

```lean
theorem summable_sparseLabelMass_amplitude_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  Summable (fun j : ℕ => sparseLabelMass α x N j *
    Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α))
```

## sparseLabelMass_amplitude_exp_tsum_le

```lean
theorem sparseLabelMass_amplitude_exp_tsum_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∑' j : ℕ, sparseLabelMass α x N j *
    Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α)) ≤ (5 / 4 : ℝ)
```

## sparseLabelMass_amplitude_sq_tsum_pos

```lean
theorem sparseLabelMass_amplitude_sq_tsum_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N →
  0 < ∑' j : ℕ, sparseLabelMass α x N j * (sparseLevelAmplitude α x N j) ^ 2
```

## integrable_sparseLabelMeasure_amplitude_rpow

```lean
theorem integrable_sparseLabelMeasure_amplitude_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ q : ℝ, 0 < q →
  Integrable (fun j : ℕ => |sparseLevelAmplitude α x N j| ^ q)
    (sparseLabelMeasure α x N)
```

## integrable_sparseLabelMeasure_shift_rpow

```lean
theorem integrable_sparseLabelMeasure_shift_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N →
  ∀ q : ℝ, 0 < q →
  Integrable (fun j : ℕ => |sparseLevelShift α x N j| ^ q)
    (sparseLabelMeasure α x N)
```

## integrable_sparseLabelMeasure_amplitude_exp

```lean
theorem integrable_sparseLabelMeasure_amplitude_exp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  Integrable (fun j : ℕ => Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α))
    (sparseLabelMeasure α x N)
```

## integral_sparseLabelMeasure_amplitude_exp_le

```lean
theorem integral_sparseLabelMeasure_amplitude_exp_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
  (∫ j, Real.exp (τ * |sparseLevelAmplitude α x N j| ^ α)
    ∂(sparseLabelMeasure α x N)) ≤ (5 / 4 : ℝ)
```

## integral_sparseLabelMeasure_amplitude_sq_pos

```lean
theorem integral_sparseLabelMeasure_amplitude_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N →
  0 < ∫ j, (sparseLevelAmplitude α x N j) ^ 2 ∂(sparseLabelMeasure α x N)
```
