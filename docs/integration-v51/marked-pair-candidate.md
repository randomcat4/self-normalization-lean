# Actual marked pair inverse identities after twice-u integration by parts

Status: CANDIDATE_PENDING_ROOT_FREEZE. Proposed module Shao/Probability/SourceOddEvenMarkedIBP.lean. Exactly two public theorems, no new public definitions.

```lean
namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem sourceFutureNoiseKernel_odd_derivative_markedIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 < y) (w q : ℝ) (hw : |w| ≤ y / 16) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let o : ℝ → ℝ := fun r => (f r - f (-r)) / 2
    let D : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let Aplus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2
    let Aminus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r - w / y) ^ 2
    let Gplus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aplus y ξ.1 w ξ.2 *
          deriv (fun t : ℝ => deriv (D ξ.2) t) ξ.1
    let Gminus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aminus y ξ.1 (-w) ξ.2 *
          deriv (fun t : ℝ => deriv (D ξ.2) t) ξ.1
    DifferentiableAt ℝ o w ∧
      Integrable Gplus (volume : Measure (ℝ × ℝ)) ∧
      Integrable Gminus (volume : Measure (ℝ × ℝ)) ∧
      ((deriv o w : ℝ) : ℂ) =
        (-Complex.I / (((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)) *
          ((∫ ξ : ℝ × ℝ, Gplus ξ) + ∫ ξ : ℝ × ℝ, Gminus ξ)

theorem sourceFutureNoiseKernel_even_second_markedIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 < y) (w q : ℝ) (hw : |w| ≤ y / 16) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let e : ℝ → ℝ := fun r => (f r + f (-r)) / 2
    let E : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let W : ℝ → ℝ → ℂ := fun v u => (u : ℂ) * E v u
    let Aplus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2
    let Aminus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r - w / y) ^ 2
    let Gplus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aplus y ξ.1 w ξ.2 *
          deriv (fun t : ℝ => deriv (W ξ.2) t) ξ.1
    let Gminus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aminus y ξ.1 (-w) ξ.2 *
          deriv (fun t : ℝ => deriv (W ξ.2) t) ξ.1
    DifferentiableAt ℝ e w ∧ DifferentiableAt ℝ (fun r : ℝ => deriv e r) w ∧
      Integrable Gplus (volume : Measure (ℝ × ℝ)) ∧
      Integrable Gminus (volume : Measure (ℝ × ℝ)) ∧
      ((deriv (fun r : ℝ => deriv e r) w : ℝ) : ℂ) =
        ((((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)⁻¹) *
          ((∫ ξ : ℝ × ℝ, Gplus ξ) + ∫ ξ : ℝ × ℝ, Gminus ξ)

end Shao.Probability
```

The actual shifts of the inner sine mark are w and-w; the modified amplitudes contain theta=w/y and-theta. The positive v phase is retained. The coefficients are exactly-i/((2pi)^2*y^2) and+1/((2pi)^2*y^2). The outputs are actual standard spatial derivatives of the real odd/even kernels, and both post-IBP pair integrands are explicitly absolutely integrable.
