# Candidate complete Lean signatures

Status: unelaborated declaration proposal, no proof bodies. These are complete candidate types, not a compile-ready Lean file and not an assertion of proved theorems. The coordinator must freeze them before implementation. Proposed module: `Shao.Probability.QuadraticChordConeDerivatives`.

```lean
import Shao.Probability.QuadraticChordNoise

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem quadraticChordChar_cone_derivatives
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (u0 v0 : ℝ) (hu : u0 ≠ 0)
    (hv : |v0| ≤ |u0| / (4 * h)) :
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let D : ℝ × ℝ → ℝ := fun p => p.1 - p.2
    let theta : ℝ × ℝ → ℝ := fun p => u0 + v0 * (p.1 + p.2)
    let Q1 : ℝ × ℝ → ℝ := fun p =>
      D p * Real.sin (D p * theta p) / theta p ^ 2 -
        2 * (1 - Real.cos (D p * theta p)) / theta p ^ 3
    let Q2 : ℝ × ℝ → ℝ := fun p =>
      D p ^ 2 * Real.cos (D p * theta p) / theta p ^ 2 -
        4 * D p * Real.sin (D p * theta p) / theta p ^ 3 +
        6 * (1 - Real.cos (D p * theta p)) / theta p ^ 4
    let d1 : ℂ := (((∫ p : ℝ × ℝ, Q1 p ∂ν.prod ν) / V : ℝ) : ℂ)
    let d2 : ℂ := (((∫ p : ℝ × ℝ, Q2 p ∂ν.prod ν) / V : ℝ) : ℂ)
    Integrable Q1 (ν.prod ν) ∧
    Integrable Q2 (ν.prod ν) ∧
    HasDerivAt (fun u : ℝ => quadraticChordChar ν u v0) d1 u0 ∧
    HasDerivAt
      (fun u : ℝ => deriv (fun r : ℝ => quadraticChordChar ν r v0) u)
      d2 u0 ∧
    deriv (fun u : ℝ => quadraticChordChar ν u v0) u0 = d1 ∧
    deriv
      (fun u : ℝ => deriv (fun r : ℝ => quadraticChordChar ν r v0) u) u0 = d2

theorem quadraticChordChar_cone_derivative_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (u0 v0 : ℝ) (hu : u0 ≠ 0)
    (hv : |v0| ≤ |u0| / (4 * h)) :
    ‖deriv (fun u : ℝ => quadraticChordChar ν u v0) u0‖ ≤ 8 / |u0| ∧
    ‖deriv
      (fun u : ℝ => deriv (fun r : ℝ => quadraticChordChar ν r v0) u) u0‖ ≤
        64 / u0 ^ 2

end Shao.Probability
```
