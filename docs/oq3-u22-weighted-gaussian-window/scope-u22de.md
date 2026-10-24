# U22DE190 exact complete declaration freeze

Freeze BEFORE implementation. Two source-bound Gaussian-frequency tail bridges: genuinewholeplaneEuclideanGaussianpolynomial integrability givestrueoutsideR weightedGaussianIntegrableOn/nonnegativeACTUALLebesgueintegral boundedbyexp(-aR^2/2) timesACTUALfinitehalf-exponentenvelopeintegral; then fordelta>0 theactualstandardGaussian weightedtailoutside delta*sqrt(n) is superpolynomial forANYnaturalweight/ANYrealpower withONE N beforeALLn>=N. ALL5statementletvalues frozen. No tail/integrability/error estimate assumed. CYwholeplaneintegrability andCFqualifiedarbitraryrealpowerstretchedexpconvergence reused withcompleteconsumedinterfaces, no oldproof/review/gatereplay. ExplicitEuclideanradius andtruefrequencyvolume, origin/R0/k0/negativeq covered. These are standardGaussiananalysis helpers, not higherEdgeworth/inversion/fullfrequency/exterior/newrhoLaplace/originalB/Dclosure ornovelty. Rootv63pinsandidentitydistinctions unchanged; ALLheavyserverONLY CPU14-17 max1 M8192j4.

```lean
theorem euclidean_gaussian_weighted_tail_bound
    (k : ℕ) (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) :
    let tail : Set (ℝ × ℝ) := {z | R ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
    let f : (ℝ × ℝ) → ℝ := fun z =>
      (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
        Real.exp (-a * (z.1 ^ 2 + z.2 ^ 2))
    let envelope : (ℝ × ℝ) → ℝ := fun z =>
      (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
        Real.exp (-(a / 2) * (z.1 ^ 2 + z.2 ^ 2))
    Integrable f ∧ Integrable envelope ∧ IntegrableOn f tail ∧
      0 ≤ (∫ z in tail, f z) ∧
      (∫ z in tail, f z) ≤
        Real.exp (-a * R ^ 2 / 2) * (∫ z : ℝ × ℝ, envelope z)

theorem eventually_scaled_euclidean_gaussian_weighted_tail
    (k : ℕ) (delta q epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let tail : Set (ℝ × ℝ) := {z |
        delta * Real.sqrt (n : ℝ) ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
      let f : (ℝ × ℝ) → ℝ := fun z =>
        (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
      IntegrableOn f tail ∧ 0 ≤ (∫ z in tail, f z) ∧
        Real.rpow (n : ℝ) q * (∫ z in tail, f z) < epsilon
```
