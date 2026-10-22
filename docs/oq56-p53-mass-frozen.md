# P53 稀疏标签质量与极限：冻结公开声明

两个模块，21条公开定理与3个公开定义。以下保留完整量词和字面定义；内部辅助声明和审计例子不计入公开目标。

```lean
def sparseLabelMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j = 0 then 1 - ∑' k : ℕ, sparsePositiveMass α x N k
  else sparsePositiveMass α x N j
```

```lean
def sparseHighMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑' k : ℕ, sparsePositiveMass α x N (j + k)
```

```lean
def sparsePriorMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j, sparseLabelMass α x N k
```

```lean
theorem sparsePositiveMass_nonneg (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparsePositiveMass α x N j
```

```lean
theorem sparsePositiveMass_pos (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) : 0 < sparsePositiveMass α x N j
```

```lean
theorem sparsePositiveMass_le_dyadic (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    sparsePositiveMass α x N j ≤ sparseDyadic (j + 2)
```

```lean
theorem summable_sparsePositiveMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    Summable (sparsePositiveMass α x N)
```

```lean
theorem sparsePositiveMass_tsum_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    0 ≤ (∑' j : ℕ, sparsePositiveMass α x N j) ∧
    (∑' j : ℕ, sparsePositiveMass α x N j) ≤ 1 / 4
```

```lean
theorem sparseLabelMass_nonneg (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparseLabelMass α x N j
```

```lean
theorem hasSum_sparseLabelMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    HasSum (sparseLabelMass α x N) 1
```

```lean
theorem sparseLabelMass_zero_ge (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    (3 / 4 : ℝ) ≤ sparseLabelMass α x N 0
```

```lean
theorem sparseLabelMass_eq_positiveMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    sparseLabelMass α x N j = sparsePositiveMass α x N j
```

```lean
theorem summable_sparsePositiveMass_tail (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : Summable (fun k : ℕ => sparsePositiveMass α x N (j + k))
```

```lean
theorem sparseHighMass_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparseHighMass α x N j ∧ sparseHighMass α x N j ≤ 1 / 4
```

```lean
theorem sparseHighMass_succ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) :
    sparseHighMass α x N j = sparsePositiveMass α x N j + sparseHighMass α x N (j + 1)
```

```lean
theorem sparsePriorMass_zero (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : sparsePriorMass α x N 0 = 0
```

```lean
theorem sparsePriorMass_eq_one_sub_highMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) : sparsePriorMass α x N j = 1 - sparseHighMass α x N j
```

```lean
theorem sparsePriorMass_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    (3 / 4 : ℝ) ≤ sparsePriorMass α x N j ∧ sparsePriorMass α x N j < 1
```

```lean
theorem sparseHighMass_future_cost (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N)
    (j : ℕ) (hj : 1 ≤ j) :
    (N j : ℝ) * sparseHighMass α x N (j + 1) ≤ sparseDyadic j / (N j : ℝ)
```

```lean
theorem sparseHighMass_total_cost (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N)
    (j : ℕ) (hj : 1 ≤ j) :
    (N j : ℝ) * sparseHighMass α x N j ≤
      sparseDyadic j + sparseDyadic j / (N j : ℝ)
```

```lean
theorem tendsto_sparseHighMass_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => sparseHighMass α x N j) atTop (nhds 0)
```

```lean
theorem tendsto_sparsePriorMass_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => sparsePriorMass α x N j) atTop (nhds 1)
```

```lean
theorem tendsto_sparseHighMass_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_ : SparseSelectionCore α x N),
  Tendsto (fun j : ℕ => (N j : ℝ) * sparseHighMass α x N j)
    atTop (nhds 0)
```

```lean
theorem tendsto_sparsePriorMass_background_power_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_ : SparseSelectionCore α x N),
  Tendsto (fun j : ℕ => (sparsePriorMass α x N j) ^ (2 * (N j - 2)))
    atTop (nhds 1)
```

P53 的实际标签概率测度、独立取样、矩、算子、条件统计量及最终尾结论另行构造。
