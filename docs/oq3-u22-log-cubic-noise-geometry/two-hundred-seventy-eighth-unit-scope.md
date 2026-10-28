# GO278: actual log-cubic Gaussian noise and unweighted original-law set sandwich

Frozen before implementation 2026-10-27T22:56:48.754294+00:00. Module Shao.OQ3.CubicGaussianNoiseSandwich. Three complete theorems, 13 statement lets. Direct dependencies GG270 (machinepassed; solefinalreview pending behindGM), qualifiedGH271 andGI272. Do not run native untilGG exact independent qualification.

Actual Gaussian product variance2b, b=1/(2n^6), eps=log(n)/n^3; first true noise tail probability <=4exp(-log²(n)/2). Ultimate threshold depends onlya>=0, before alln/baseprobabilitylaws/measurablesets; actual same rho=mapadd(nu.prodgamma), closed metric thickening and complement of complement thickening sandwich with n^-a additive error. No density ofnu, no asymptotic-error/coherence premise. This is an actual unweighted independent-noise sandwich, not the remaining weighted test-function estimate, boundary Gaussian expansion, cell summation, fullfrequencyerror, exterior, B-D or originalpositiveOQ3 completion. Original strictbeta<2/5, p54corr, Songuniform/s8 attribution retained. Repaired epsilon is log² larger than originalh; explicitgeometryobligation remains.

## Complete frozen declarations

```lean
theorem cubic_pair_gaussian_noise_tail_bound
    (n : ℕ) (hn : 1 ≤ n) :
    let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
    let eps : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    gamma.real {y : ℝ × ℝ | eps < ‖y‖} ≤
      4 * Real.exp (-(Real.log (n : ℝ)) ^ 2 / 2)

theorem eventually_cubic_pair_gaussian_noise_tail
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
      let eps : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
      let v : ℝ≥0 := Real.toNNReal (2 * b)
      let gamma : Measure (ℝ × ℝ) :=
        (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
      gamma.real {y : ℝ × ℝ | eps < ‖y‖} ≤ Real.rpow (n : ℝ) (-a)

theorem eventually_cubic_gaussian_smoothed_set_sandwich
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
        (s : Set (ℝ × ℝ)), MeasurableSet s →
      let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
      let eps : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
      let v : ℝ≥0 := Real.toNNReal (2 * b)
      let gamma : Measure (ℝ × ℝ) :=
        (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
      let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
      rho.real ((Metric.cthickening eps sᶜ)ᶜ) - Real.rpow (n : ℝ) (-a) ≤ nu.real s ∧
        nu.real s ≤ rho.real (Metric.cthickening eps s) + Real.rpow (n : ℝ) (-a)
```
