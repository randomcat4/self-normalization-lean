# Fixed sparse signed-label law: frozen declarations

This module supplies the actual Nat × Bool law for p53 §3: the accepted sparse category law times an independent fair sign. It proves probability, exact tagged masses, both marginals, coordinate independence, the atomic expansion, and an honest weighted L1/integral bridge.

All α, x and N are arbitrary and fixed. No positivity, SparseSelectionCore, monotonicity or subsequence reselection is added. Equal later real amplitudes do not merge distinct tags. The only project dependency is SparseLabelLaw (Unit100); Unit101 is not imported.

The one definition body and eight public theorem types below are unchanged from frozen v1 (235a43f170e3c63183f4ec6944e1a985b654d4fdca8aa6c207a016523ff6b3d4).

## sparseSignedLabelMeasure

```lean
def sparseSignedLabelMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Measure (ℕ × Bool) :=
  (sparseLabelMeasure α x N).prod
    (Measure.sum (fun b : Bool => (1 / 2 : ℝ≥0∞) • Measure.dirac b))
```

## sparseSignedLabelMeasure_probability

```lean
theorem sparseSignedLabelMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseSignedLabelMeasure α x N)
```

## sparseSignedLabelMeasure_singleton

```lean
theorem sparseSignedLabelMeasure_singleton :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool),
  sparseSignedLabelMeasure α x N {(j, b)} = ENNReal.ofReal (sparseLabelMass α x N j / 2)
```

## sparseSignedLabelMeasure_first

```lean
theorem sparseSignedLabelMeasure_first :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseSignedLabelMeasure α x N).map Prod.fst = sparseLabelMeasure α x N
```

## sparseSignedLabelMeasure_sign

```lean
theorem sparseSignedLabelMeasure_sign :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseSignedLabelMeasure α x N).map Prod.snd =
    (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true
```

## sparseSignedLabelMeasure_eq_sum

```lean
theorem sparseSignedLabelMeasure_eq_sum :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  sparseSignedLabelMeasure α x N =
    Measure.sum (fun j : ℕ => Measure.sum (fun b : Bool =>
      ENNReal.ofReal (sparseLabelMass α x N j / 2) • Measure.dirac (j, b)))
```

## sparseSignedLabelMeasure_indep_coordinates

```lean
theorem sparseSignedLabelMeasure_indep_coordinates :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ProbabilityTheory.IndepFun (Prod.fst : ℕ × Bool → ℕ) (Prod.snd : ℕ × Bool → Bool)
    (sparseSignedLabelMeasure α x N)
```

## integrable_sparseSignedLabelMeasure_iff

```lean
theorem integrable_sparseSignedLabelMeasure_iff :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ × Bool → ℝ),
  Integrable f (sparseSignedLabelMeasure α x N) ↔
    Summable (fun j : ℕ => (sparseLabelMass α x N j / 2) *
      (‖f (j, false)‖ + ‖f (j, true)‖))
```

## integral_sparseSignedLabelMeasure

```lean
theorem integral_sparseSignedLabelMeasure :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ × Bool → ℝ),
  Integrable f (sparseSignedLabelMeasure α x N) →
  (∫ z, f z ∂(sparseSignedLabelMeasure α x N)) =
    ∑' j : ℕ, (sparseLabelMass α x N j / 2) * (f (j, false) + f (j, true))
```
