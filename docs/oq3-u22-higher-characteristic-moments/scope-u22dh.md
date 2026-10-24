# Unit 193 / U22DH — actual scalar characteristic integrated Taylor remainder

Frozen before implementation. Source-bound next dependency for actual characteristic-function higher moment/cumulant expansion. Only genuine probability and the stated actual finite m-th absolute moment; all natural m including 0 and all real t including 0. Exact two let-values retained. Derive actual phase, Taylor-polynomial, and remainder integrability and an actual integral error. No assumed target integrability, remainder, exponential moment, or coefficient bound. Consumes qualified DG192 exact source fa560d715fe1ee72ab65aadbc4825db4b3183339609a8b50a83f4dcb9cab7e27 / complete report 3f32285182604348c468e02d13e9a16492796a4295154e802d3d2aa0239eea66 by full consumed interface, not old proof replay. Does not close original OQ3 B/D, higher Edgeworth, full-frequency inversion/exterior, or new-rho Laplace. Source scope, p54 repairs, strict original beta scope and external attribution unchanged.

```lean
theorem scalar_characteristic_integrated_taylor_remainder
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℕ)
    (hM : Integrable (fun x : ℝ => |x| ^ m) ν) (t : ℝ) :
    let e : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
    let P : ℝ → ℂ := fun x =>
      ∑ j ∈ Finset.range m, (((t * x : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)
    Integrable e ν ∧ Integrable P ν ∧ Integrable (fun x => e x - P x) ν ∧
      ‖(∫ x, e x ∂ν) - (∫ x, P x ∂ν)‖ ≤
        (Real.exp 1 + (m : ℝ) + 1) * |t| ^ m * (∫ x, |x| ^ m ∂ν)
```

