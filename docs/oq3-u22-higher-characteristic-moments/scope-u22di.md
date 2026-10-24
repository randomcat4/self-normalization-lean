# Unit 194 / U22DI — actual scalar finite moment coefficient coherence

Frozen before implementation. Two complete declarations with the exact single P let-value. From actual probability and the genuine finite m-th absolute moment, derive every lower absolute and signed moment and identify the actual integral of the literal imaginary-exponential Taylor polynomial with the polynomial of genuine signed raw moments. Every natural m including 0 and every real t including 0; no moment/coefficient/integrability coherence premise. Mathlib-only enabler for later assembly with qualified DG and independently pending DH; does not consume an unreviewed DH theorem. OQ3 B/D, higher Edgeworth, full-frequency inversion/exterior and new-rho Laplace remain OPEN. Source scope, p54 repairs, original strict beta scope, and external-result attribution unchanged.

```lean
theorem integrable_scalar_power_of_absolute_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℕ)
    (hM : Integrable (fun x : ℝ => |x| ^ m) ν) (j : ℕ) (hjm : j ≤ m) :
    Integrable (fun x : ℝ => |x| ^ j) ν ∧ Integrable (fun x : ℝ => x ^ j) ν

theorem scalar_integral_taylor_polynomial_eq_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℕ)
    (hM : Integrable (fun x : ℝ => |x| ^ m) ν) (t : ℝ) :
    let P : ℝ → ℂ := fun x =>
      ∑ j ∈ Finset.range m, (((t * x : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)
    Integrable P ν ∧
      (∫ x, P x ∂ν) =
        ∑ j ∈ Finset.range m,
          (((t : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)) *
            ((∫ x : ℝ, x ^ j ∂ν : ℝ) : ℂ)
```

