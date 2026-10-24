# Unit 197 / U22DL — actual Fin2 characteristic directional moment expansion

Frozen before implementation. Both complete declarations, zero statement lets. Actual Fin2 probability law, genuine literal Euclidean radial m-th absolute moment, every natural order including0, every real frequency pair including0. Actual CF and exact factorial coefficients multiply genuine signed directional raw moments over the SAME law and SAME (u,v). Uniform family uses only common actual radial moment bound, not a target error/coherence hypothesis. Plan: genuine scalar projection pushforward, qualified DJ directional moment derivation and actual moment bound, qualified DK actual scalar CF/moment remainder at t=1, exact probability/integrability/integral map identities. Wait for complete independent DJ and DK qualification before author implementation; retain their full consumed types/values/bindings without entire old proof/report/gate replay. Original OQ3 B/D, higher Edgeworth, full-frequency inversion/exterior, new-rho Laplace remainOPEN. Source/p54/originalstrictbeta/external attribution unchanged; finite Taylor dependency is not root completion or novelty.

```lean
theorem pair_probability_characteristic_moment_remainder_bound
    (law : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure law] (m : ℕ)
    (hM : Integrable (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) law)
    (u v : ℝ) :
    ‖(∫ y : Fin 2 → ℝ, Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law) -
        (∑ j ∈ Finset.range m, (Complex.I ^ j / (j.factorial : ℂ)) *
          ((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ j ∂law : ℝ) : ℂ))‖ ≤
      (Real.exp 1 + (m : ℝ) + 1) * Real.sqrt (u ^ 2 + v ^ 2) ^ m *
        (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂law)

theorem uniform_pair_characteristic_moment_remainder_bound
    {ι : Type*} (law : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ i, IsProbabilityMeasure (law i)) (m : ℕ) (M : ℝ)
    (hI : ∀ i, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) (law i))
    (hM : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂(law i)) ≤ M) :
    ∀ (i : ι) (u v : ℝ),
      ‖(∫ y : Fin 2 → ℝ,
          Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂(law i)) -
          (∑ j ∈ Finset.range m, (Complex.I ^ j / (j.factorial : ℂ)) *
            ((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ j ∂(law i) : ℝ) : ℂ))‖ ≤
        (Real.exp 1 + (m : ℝ) + 1) * M * Real.sqrt (u ^ 2 + v ^ 2) ^ m
```

