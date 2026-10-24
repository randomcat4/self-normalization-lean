# Unit202 / U22DQ: actual directional moments and degree-four characteristic moment polynomial

Freeze COMPLETE declarations BEFORE implementation. Genuine pair probability/L2/zero means/identity covariance -> actual directional L2/integrability/mean0/second moment u²+v². True radial third/fourth integrability -> genuine signed directional third/fourth coefficient integrability and the exact complex-phase/factorial degree-four moment polynomial. QualifiedDJ fulltype/allfletvalue source/object/receipt/full93qualifiedreview metadata plus pinnedprimaryCovariance/L2/Bochner APIs reused; nooldproof/report/gatereplay. This is a necessary coefficient identification step, not a cumulant or higherEdgeworth/root theorem. OriginalB/D/highercumulants/normalizedIID/fullfrequency/inversion/exterior/newrhoLaplaceOPEN; assumptions only explicitactualmodel inputs, rootconditions unchanged.

```lean
theorem pair_probability_directional_first_two_moments
    (law : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure law]
    (hL2 : ∀ j : Fin 2, MemLp (fun y : Fin 2 → ℝ => y j) 2 law)
    (hmean : ∀ j : Fin 2, (∫ y : Fin 2 → ℝ, y j ∂law) = 0)
    (hcov : ∀ j k : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y j) (fun y : Fin 2 → ℝ => y k) law =
        if j = k then 1 else 0) (u v : ℝ) :
    let L : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
    MemLp L 2 law ∧ Integrable L law ∧
      Integrable (fun y => L y ^ 2) law ∧
      (∫ y, L y ∂law) = 0 ∧
      (∫ y, L y ^ 2 ∂law) = u ^ 2 + v ^ 2

theorem pair_probability_degree_four_moment_polynomial
    (law : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure law]
    (hL2 : ∀ j : Fin 2, MemLp (fun y : Fin 2 → ℝ => y j) 2 law)
    (hmean : ∀ j : Fin 2, (∫ y : Fin 2 → ℝ, y j ∂law) = 0)
    (hcov : ∀ j k : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y j) (fun y : Fin 2 → ℝ => y k) law =
        if j = k then 1 else 0)
    (hI3 : Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) law)
    (hI4 : Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 4) law) (u v : ℝ) :
    let L : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
    Integrable (fun y => L y ^ 3) law ∧ Integrable (fun y => L y ^ 4) law ∧
      (∑ j ∈ Finset.range 5, (Complex.I ^ j / (j.factorial : ℂ)) *
        ((∫ y, L y ^ j ∂law : ℝ) : ℂ)) =
      1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
        Complex.I * ((∫ y, L y ^ 3 ∂law : ℝ) : ℂ) / 6 +
          ((∫ y, L y ^ 4 ∂law : ℝ) : ℂ) / 24
```
