# Candidate declarations v1

Proposed production module: `Shao/Probability/CenteredQuadraticCharacteristic.lean`.
Imports: `Shao.Probability.QuadraticCharacteristic` and existing mathlib variance/Cauchy–Schwarz support. Namespace `Shao.Probability`, `open MeasureTheory ProbabilityTheory`, `set_option autoImplicit false`.

These are complete proposed public declarations; mathematical assumptions and actual definition values are frozen together by root approval. Private implementation helpers may be added without changing these interfaces.

```lean
noncomputable def centeredQuadraticChar (ν : Measure ℝ) (u v : ℝ) : ℂ :=
  Complex.exp (-(((u * ∫ a : ℝ, a ∂ν : ℝ) : ℂ) * Complex.I)) *
    quadraticChar ν u v

theorem centeredQuadraticChar_eq_integral (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (u v : ℝ) :
    centeredQuadraticChar ν u v =
      ∫ a : ℝ, Complex.exp
        (((u * (a - ∫ b : ℝ, b ∂ν) + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν

theorem norm_centeredQuadraticChar (ν : Measure ℝ) (u v : ℝ) :
    ‖centeredQuadraticChar ν u v‖ = ‖quadraticChar ν u v‖

theorem centeredQuadraticChar_hasDerivAt (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => centeredQuadraticChar ν r v)
      (Complex.I * ∫ a : ℝ, ((a - ∫ b : ℝ, b ∂ν : ℝ) : ℂ) *
        Complex.exp
          (((u * (a - ∫ b : ℝ, b ∂ν) + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν) u

theorem centeredQuadraticChar_deriv_hasDerivAt (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => deriv (fun s : ℝ => centeredQuadraticChar ν s v) r)
      (-(∫ a : ℝ, (((a - ∫ b : ℝ, b ∂ν) ^ 2 : ℝ) : ℂ) *
        Complex.exp
          (((u * (a - ∫ b : ℝ, b ∂ν) + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν)) u

theorem quadraticChar_centered_second_moment (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) :
    (∫ a : ℝ, (a - ∫ b : ℝ, b ∂ν) ^ 2 ∂ν) = variance (id : ℝ → ℝ) ν

theorem quadraticChar_phase_variance (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (u v : ℝ) :
    (∫ a : ℝ, ‖Complex.exp
      (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) - quadraticChar ν u v‖ ^ 2 ∂ν) =
      1 - ‖quadraticChar ν u v‖ ^ 2

theorem centeredQuadraticChar_derivative_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    ‖deriv (fun r : ℝ => centeredQuadraticChar ν r v) u‖ ≤
        Real.sqrt (variance (id : ℝ → ℝ) ν) *
          Real.sqrt (1 - ‖quadraticChar ν u v‖ ^ 2) ∧
      ‖deriv (fun r : ℝ => deriv (fun s : ℝ => centeredQuadraticChar ν s v) r) u‖ ≤
        variance (id : ℝ → ℝ) ν
```
