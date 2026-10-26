# OriginalClippedComparisonPayments — exact qualified interface

Literal S12 comparison exception plus two actual S15 remainder probabilities in the bounded-product/polylog class. Fixedrho window derived internally; same original window and all model assumptions, c before n/r/w/y, full lowerbad payment and 4exp+9exp retained. No S14/DC/generalS15/fullOQ56 claim.

Source SHA256: d9d59c78c868072303fcce4716a7c3f57e0b7228ce2626a3dea37612644ab35c; bytes: 10155.

Complete source heads:

```lean
theorem eventually_original_boundedPolylog_clipped_comparison_payments
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1)
    (C a t0 M rho : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (ht0 : 0 < t0) (hM0 : 0 ≤ M) (hrho : 0 ≤ rho) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (r : Ω → Ω → ℝ) (w : Ω → ℝ),
      Measurable (Function.uncurry r) →
      Integrable (Function.uncurry r) (μ.prod μ) →
      (∀ᵐ a ∂μ, (∫ b : Ω, r a b ∂μ) = 0) →
      (∀ᵐ b ∂μ, (∫ a : Ω, r a b ∂μ) = 0) →
      (∀ᵐ o ∂μ, 0 ≤ w o) →
      (∀ᵐ o ∂μ, w o ≤ Shao.OQ5.P51.boundedPolylogHeight C a n) →
      Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ →
      (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M →
      (∀ᵐ z ∂μ.prod μ, |r z.1 z.2| ≤ w z.1 * w z.2) →
      (∀ a b : Ω, r a b = r b a) →
      ∀ y : ℝ, (1 : ℝ) ≤ y →
      y ≤ Shao.OQ5.P51.remainderWindowScale
        (Shao.OQ6.BoundedProductEnvelopeTails.tailScale M) t0 *
          Real.rpow (n : ℝ) ((1 : ℝ) / 6) →
      (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real
        {x : Fin n → Ω |
          Shao.OQ5.P51.clippedCenteredStatistic n g r 512 rho y x ≠
            (if Real.sqrt (Shao.OQ5.P51.centeredSq n g r x) = 0 then 0 else
              (Shao.OQ5.P51.projectionW n g x + Shao.OQ5.P51.residualStatisticD n r x) /
                Real.sqrt (Shao.OQ5.P51.centeredSq n g r x))} +
        (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real (Shao.OQ5.P51.numeratorRemainderBad n g r y) +
        (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real (Shao.OQ5.P51.denominatorRemainderBad n g r y) ≤
        Real.exp (-c * (n : ℝ)) +
          (4 : ℝ) * Real.exp (-(y * Real.sqrt (n : ℝ)) / (2 : ℝ)) +
          (9 : ℝ) * Real.exp (-Shao.OQ5.P51.boundedPolylogMomentOrder t0 n)
```

Validation: qualified complete independent source/proof review, complete actual all-module TYPE/required non-theorem FULLVALUE and transitive axiom audit on the first original object. Old source/check evidence is reused exactly. No merge or root completion is claimed.
