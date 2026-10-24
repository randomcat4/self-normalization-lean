# U22DB187 complete exact declaration freeze

Freeze before implementation. Honest finite-frequency integration bridge for an ACTUAL pair probability characteristicfunction on ANYmeasurablefrequencyset contained in the literalEuclideanKball, K>=0. A supplied actualCF supremumbound epsilon>=0 yields genuineweightedIntegrableOn/nonnegativeLebesgueintegral <=4*K^(k+2)*epsilon forEVERYnaturalk. True finite rectangle volume/probability CF continuity, no assumed integrability/finite integral or replacement of Euclideanradius by Prodmaxnorm. The modularpointwisepremise must be DERIVED by canonical far/middle caller from alreadyqualified actualCG/CP, neverassumed fororiginalB/D. CGcompleteconsumedinterface confirms originalstrictbeta<2/5 and actualcubic smoothingwindow radius<=n^3 alreadyproved; no repeat of its analytic bound needed. Nextcanonicalcaller retains SAMEE and derives equality of any qualified producer E only from their full literalmatrixaction, neverasassumption. ONEcomplete statementletf frozen. ALLheavyserverONLY CPU14-17 max1 native-M8192 -j4; nooldPASSgatereplay.

```lean
theorem pair_characteristic_bounded_frequency_weighted_integral_bound
    (rho : Measure (ℝ × ℝ)) [IsProbabilityMeasure rho]
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (K epsilon : ℝ) (hK : 0 ≤ K) (hepsilon : 0 ≤ epsilon)
    (hrad : ∀ z ∈ D, Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ K)
    (hCF : ∀ z ∈ D,
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤ epsilon)
    (k : ℕ) :
    let f : (ℝ × ℝ) → ℝ := fun z =>
      (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
        ‖(∫ w : ℝ × ℝ,
          Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖
    IntegrableOn f D ∧ 0 ≤ (∫ z in D, f z) ∧
      (∫ z in D, f z) ≤ 4 * K ^ (k + 2) * epsilon
```
