# U22CV181 exact complete declaration freeze

Freeze before implementation. Actual one-observation Gaussian comparison from genuine covariance identity and radial third integrability. First declaration bounds the literal real Gaussian minus its quadratic polynomial on the unit Euclidean ball using unconditional complex-exponential series remainder. Second combines independently qualified CR177 actual pair CF quadratic remainder with this Gaussian remainder. No Gaussian/CF/error bound is assumed, no exponential moment or bounded support, no root theorem/Edgeworth claim. A next actual iid comparison will use this local cubic error and already derived Gaussian damping; weighted Fourier error integrals and original B-D remain OPEN. ALL heavy server-only CPU14-17 max1 -M8192 -j4; no PASS gate replay.

```lean
theorem real_gaussian_quadratic_remainder_bound (u v : ℝ)
    (hr : Real.sqrt (u ^ 2 + v ^ 2) ≤ 1) :
    ‖((Real.exp (-(u ^ 2 + v ^ 2) / 2) : ℝ) : ℂ) -
      (1 - ((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2)‖ ≤
        Real.exp 1 * (Real.sqrt (u ^ 2 + v ^ 2)) ^ 3

theorem pair_probability_characteristic_gaussian_remainder_bound
    (law : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure law]
    (hL2 : ∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 law)
    (hmean : ∀ i : Fin 2, (∫ y : Fin 2 → ℝ, y i ∂law) = 0)
    (hcov : ∀ i j : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) law =
        if i = j then 1 else 0)
    (hthird : Integrable (fun y : Fin 2 → ℝ =>
      (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3) law)
    (u v : ℝ) (hr : Real.sqrt (u ^ 2 + v ^ 2) ≤ 1) :
    ‖(∫ y : Fin 2 → ℝ,
      Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law) -
        ((Real.exp (-(u ^ 2 + v ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      ((Real.exp 1 + 4) *
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂law) +
          Real.exp 1) * (Real.sqrt (u ^ 2 + v ^ 2)) ^ 3
```
