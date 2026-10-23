# Candidate declarations v1 — awaiting root freeze

Target module: `Shao/Probability/SourceScalarFourierDerivatives.lean`.
Namespace: `Shao.Probability`; exact source objects from `SourceScalarNoise.lean`.
No production declaration has been implemented.

```lean
theorem sourceScalarChar_scaled_derivatives (gamma u0 : ℝ) :
    let d1 : ℂ := ∫ r : ℝ,
      Complex.I * ((gamma * r : ℝ) : ℂ) *
        Complex.exp ((((gamma * u0 * r : ℝ) : ℂ)) * Complex.I) ∂sourceScalarLaw
    let d2 : ℂ := ∫ r : ℝ,
      -(((gamma * r) ^ 2 : ℝ) : ℂ) *
        Complex.exp ((((gamma * u0 * r : ℝ) : ℂ)) * Complex.I) ∂sourceScalarLaw
    HasDerivAt (fun u : ℝ => sourceScalarChar (gamma * u)) d1 u0 ∧
    HasDerivAt
      (fun u : ℝ => deriv (fun t : ℝ => sourceScalarChar (gamma * t)) u) d2 u0 ∧
    deriv (fun u : ℝ => sourceScalarChar (gamma * u)) u0 = d1 ∧
    deriv
      (fun u : ℝ => deriv (fun t : ℝ => sourceScalarChar (gamma * t)) u) u0 = d2

theorem sourceScalarChar_scaled_derivative_bounds :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ gamma u : ℝ, u ≠ 0 →
        ‖deriv (fun t : ℝ => sourceScalarChar (gamma * t)) u‖ ≤ C1 / |u| ∧
        ‖deriv
          (fun t : ℝ => deriv (fun r : ℝ => sourceScalarChar (gamma * r)) t) u‖ ≤
            C2 / u ^ 2
```

The statements are byte-for-byte copied from the first two candidates in `drafts/c12-cone-derivatives/next-scalar-xi-candidates.md`, except surrounding document text. All real scale values are included. No additional hypotheses may be added by the author. Auxiliary private lemmas may expose weighted Lebesgue amplitudes, measure conversion and normalized Fourier identities, but cannot replace the actual public source objects with a free function.
