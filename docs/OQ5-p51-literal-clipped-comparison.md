# LiteralClippedComparison — exact qualified interface

Literal S10/S12 fixed512 comparison with rho>=0 and explicit symmetry/n>=4/y>=1/window; external hDom discharged, pointwise hLower and true lowerbad/V0 guard retained.

Source SHA256: 8d601a1496ca1a330fb7f96a2ff5cdab6f0d3b37c125a710735d9123c5be1f14; bytes: 2614.

Complete source heads:

```lean
theorem literal_clippedCentered_comparison_on_projectionGood (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (rho y : ℝ)
    (x : Fin n → Ω) (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hsym : ∀ a b : Ω, r a b = r b a) (hrho : 0 ≤ rho)
    (hwindow : (1 + rho) * y ≤ Real.sqrt (n : ℝ))
    (hGood : x ∈ projectionGood n g y)
    (hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x) :
    clippedCenteredDelta n g r 512 rho y x = centeredDelta n g r x ∧
    0 < projectionV n g x *
      Real.sqrt (1 + clippedCenteredDelta n g r 512 rho y x) ∧
    0 < Real.sqrt (centeredSq n g r x) ∧
    projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho y x) =
      Real.sqrt (centeredSq n g r x) ∧
    clippedCenteredStatistic n g r 512 rho y x =
      (if Real.sqrt (centeredSq n g r x) = 0 then 0 else
        (projectionW n g x + residualStatisticD n r x) /
          Real.sqrt (centeredSq n g r x))

theorem literal_clippedCentered_comparison_exception_subset (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (rho y : ℝ)
    (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hsym : ∀ a b : Ω, r a b = r b a) (hrho : 0 ≤ rho)
    (hwindow : (1 + rho) * y ≤ Real.sqrt (n : ℝ))
    :
    {x : Fin n → Ω |
      clippedCenteredStatistic n g r 512 rho y x ≠
        (if Real.sqrt (centeredSq n g r x) = 0 then 0 else
          (projectionW n g x + residualStatisticD n r x) /
            Real.sqrt (centeredSq n g r x))} ⊆
      (projectionGood n g y)ᶜ ∪ lowerStudentizerBad n g r y
```

Validation: qualified complete independent source/proof review, complete actual all-module TYPE/required non-theorem FULLVALUE and transitive axiom audit on the first original object. Old source/check evidence is reused exactly. No merge or root completion is claimed.
