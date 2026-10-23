# Actual sparse conditional statistics and balanced concentration

These exact interfaces are the finite conditional-statistic consumer in original p53 section4 equation(9) and the concentration/all-pattern step in section5. They use the given selection Core, actual two-target/opposite-sign event and actual centered-row jackknife. Both modules have complete independent source-to-statement and actual-owned-object review, with exact server receipts bound in the publication manifest and review document.

## Unit122

Module Shao.OQ5.P53.SparseConditionalStatisticBounds. Source SHA256 7e456f765734ce7ea19d75e8f3bf76cff44319f6434e3de84ed5edd98fe5a134; object SHA256 27ee7cd3e26632a8a3b5febee1705c6b157565cb3c532cb9d09345b63451bd7c. Four public definitions and nine public theorem types.

```lean
def sparseSampleNumerator (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (ω : Fin n → SparseObs) : ℝ :=
  Real.sqrt (n : ℝ) * sparseSampleU α x N ω
```

```lean
def sparseBalancedNumeratorMean (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  2 * Real.sqrt (N j : ℝ) * sparseLevelShift α x N j / ((N j : ℝ) - 1)
```

```lean
def sparseNumeratorMomentBound (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : ℝ :=
  4 + 24 * (∫ z, sparsePopulationG α x N z ^ 2 ∂sparsePopulationMeasure α x N) +
    12 * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N) ^ 2
```

```lean
def sparseStudentizerMomentBound (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : ℝ :=
  4 + 16 * (∫ z, sparsePopulationG α x N z ^ 2 ∂sparsePopulationMeasure α x N) +
    16 * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N) ^ 2 + 72 * (∫ z, sparsePopulationZ α x N z ^ 2 ∂sparsePopulationMeasure α x N)
```

```lean
theorem sparseNumeratorMomentBound_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < sparseNumeratorMomentBound α x N
```

```lean
theorem sparseStudentizerMomentBound_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < sparseStudentizerMomentBound α x N
```

```lean
theorem memLp_sparseSampleNumerator_cond_balanced_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  MemLp (fun ω : Fin (N j) → SparseObs => sparseSampleNumerator α x N ω) 2
    (sparseBalancedPatternMeasure α x N (N j) j i k b)
```

```lean
theorem integral_sparseSampleNumerator_cond_balanced :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  (∫ ω : Fin (N j) → SparseObs, sparseSampleNumerator α x N ω
    ∂sparseBalancedPatternMeasure α x N (N j) j i k b) = sparseBalancedNumeratorMean α x N j
```

```lean
theorem integral_sparseSampleNumerator_centered_sq_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  (∫ ω : Fin (N j) → SparseObs,
    (sparseSampleNumerator α x N ω - sparseBalancedNumeratorMean α x N j) ^ 2
    ∂sparseBalancedPatternMeasure α x N (N j) j i k b) ≤ sparseNumeratorMomentBound α x N
```

```lean
theorem variance_sparseSampleNumerator_cond_balanced_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  ProbabilityTheory.variance (fun ω : Fin (N j) → SparseObs => sparseSampleNumerator α x N ω)
    (sparseBalancedPatternMeasure α x N (N j) j i k b) ≤ sparseNumeratorMomentBound α x N
```

```lean
theorem integrable_sparseSampleStudentizerSq_cond_balanced :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  Integrable (fun ω : Fin (N j) → SparseObs => sparseSampleStudentizerSq α x N ω)
    (sparseBalancedPatternMeasure α x N (N j) j i k b)
```

```lean
theorem integral_sparseSampleStudentizerSq_cond_balanced_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  (∫ ω : Fin (N j) → SparseObs, sparseSampleStudentizerSq α x N ω
    ∂sparseBalancedPatternMeasure α x N (N j) j i k b) ≤
    sparseStudentizerMomentBound α x N *
      (1 + 2 * sparseLevelAmplitude α x N j ^ 2 / (N j : ℝ) ^ 2)
```

```lean
theorem integral_sparseSampleStudentizerSq_cond_balanced_uniform_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
  (∫ ω : Fin (N j) → SparseObs, sparseSampleStudentizerSq α x N ω
    ∂sparseBalancedPatternMeasure α x N (N j) j i k b) ≤ 3 * sparseStudentizerMomentBound α x N
```

## Unit123

Module Shao.OQ5.P53.SparseBalancedConcentration. Source SHA256 6673006d7d82722c22464be43fea8ab873a353a1dcb21622706ac5024f3a7207; object SHA256 a8bee44a7ae06446fd696ba99c1535880395728ed7d67e9867cd9d70e57b0ef1. One public definition and five public theorem types.

```lean
def sparseBalancedFailureBound (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  sparseNumeratorMomentBound α x N /
    (sparseSlow α x (N j) ^ 2 * x (N j) ^ 2) +
  3 * sparseStudentizerMomentBound α x N / sparseSlow α x (N j)
```

```lean
theorem sparseBalancedFailureBound_nonneg :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  0 ≤ sparseBalancedFailureBound α x N j
```

```lean
theorem sparseBalancedPairPattern_cond_tail_ge :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  1 ≤ sparseSlow α x (N j) →
  ∀ (i k : Fin (N j)) (b : Bool), i < k →
    1 - sparseBalancedFailureBound α x N j ≤
      (sparseBalancedPatternMeasure α x N (N j) j i k b).real
        {ω : Fin (N j) → SparseObs | x (N j) ≤ sparseSampleStudentized α x N ω}
```

```lean
theorem tendsto_sparseBalancedFailureBound_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (sparseBalancedFailureBound α x N) atTop (nhds 0)
```

```lean
theorem eventually_sparseBalancedPairPattern_cond_tail_half :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop, ∀ (i k : Fin (N j)) (b : Bool), i < k →
    (1 : ℝ) / 2 ≤
      (sparseBalancedPatternMeasure α x N (N j) j i k b).real
        {ω : Fin (N j) → SparseObs | x (N j) ≤ sparseSampleStudentized α x N ω}
```

```lean
theorem eventually_sparseBalancedEvent_tail_half :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∀ᶠ j : ℕ in atTop,
    (Measure.pi (fun _ : Fin (N j) => sparsePopulationMeasure α x N)).real
        (sparseBalancedEvent (N j) j) / 2 ≤
      (Measure.pi (fun _ : Fin (N j) => sparsePopulationMeasure α x N)).real
        {ω : Fin (N j) → SparseObs | x (N j) ≤ sparseSampleStudentized α x N ω}
```
