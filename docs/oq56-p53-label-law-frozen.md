# Complete public contract for the sparse label law

One literal definition and thirteen complete theorem types. The direct imports are `Shao.OQ5.P53.SparseMassLimits`, `Mathlib.MeasureTheory.Measure.Dirac.Basic`, and `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`.

```lean
def sparseLabelMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Measure ℕ :=
  Measure.sum fun j : ℕ => ENNReal.ofReal (sparseLabelMass α x N j) • Measure.dirac j
```

```lean
theorem sparseLabelMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseLabelMeasure α x N)
```

```lean
theorem sparseLabelMeasure_singleton :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  sparseLabelMeasure α x N {j} = ENNReal.ofReal (sparseLabelMass α x N j)
```

```lean
theorem sparseLabelMeasure_real_singleton :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  (sparseLabelMeasure α x N).real {j} = sparseLabelMass α x N j
```

```lean
theorem sparseLabelMeasure_Iio :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  sparseLabelMeasure α x N (Set.Iio j) = ENNReal.ofReal (sparsePriorMass α x N j)
```

```lean
theorem sparseLabelMeasure_real_Iio :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  (sparseLabelMeasure α x N).real (Set.Iio j) = sparsePriorMass α x N j
```

```lean
theorem sparseLabelMeasure_Ici :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  1 ≤ j →
  sparseLabelMeasure α x N (Set.Ici j) = ENNReal.ofReal (sparseHighMass α x N j)
```

```lean
theorem sparseLabelMeasure_real_Ici :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  1 ≤ j →
  (sparseLabelMeasure α x N).real (Set.Ici j) = sparseHighMass α x N j
```

```lean
theorem integrable_sparseLabelMeasure_iff :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ → ℝ),
  Integrable f (sparseLabelMeasure α x N) ↔
    Summable (fun j : ℕ => sparseLabelMass α x N j * ‖f j‖)
```

```lean
theorem integral_sparseLabelMeasure :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ → ℝ),
  Integrable f (sparseLabelMeasure α x N) →
  (∫ j, f j ∂(sparseLabelMeasure α x N)) =
    ∑' j : ℕ, sparseLabelMass α x N j * f j
```

```lean
theorem tendsto_sparseLabelMeasure_high_mass_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => (sparseLabelMeasure α x N).real (Set.Ici j))
    atTop (nhds 0)
```

```lean
theorem tendsto_sparseLabelMeasure_high_mass_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  SparseSelectionCore α x N →
  Tendsto (fun j : ℕ => (N j : ℝ) *
    (sparseLabelMeasure α x N).real (Set.Ici j))
    atTop (nhds 0)
```

```lean
theorem tendsto_sparseLabelMeasure_low_mass_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => (sparseLabelMeasure α x N).real (Set.Iio j))
    atTop (nhds 1)
```

```lean
theorem tendsto_sparseLabelMeasure_background_power_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  SparseSelectionCore α x N →
  Tendsto (fun j : ℕ => ((sparseLabelMeasure α x N).real (Set.Iio j)) ^ (2 * (N j - 2)))
    atTop (nhds 1)
```
