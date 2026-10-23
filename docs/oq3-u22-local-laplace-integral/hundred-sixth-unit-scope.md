# U22y — integrable quantitative boundary Laplace envelope

Complete declarations frozen before implementation. Module Shao.OQ3.BoundaryLaplaceEnvelope, two public theorems and zero definitions. Source repair01.md183–210 equation14. Prove every nonnegative-integer monomial |u|^m*v^n against exp(-d*(v+u²)) integrable on Lebesgue R times Lebesgue [0,infinity), using actual Gaussian/Gamma integrability and product measure. Then prove X's complete explicit error envelope integrable by a finite sum of these monomials. No desired integrability is a premise. This supplies the quantitative integrating majorant, not yet the original integral/Jacobian, leading constant, actual probability/Edgeworth/far-field or root conclusion.

```lean
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem boundary_laplace_monomial_integrable
    (d : ℝ) (hd : 0 < d) (m n : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      |p.1| ^ m * p.2 ^ n * Real.exp (-d * (p.2 + p.1 ^ 2)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0)))

theorem boundary_laplace_error_envelope_integrable
    (d CA CF a0 rho : ℝ) (hd : 0 < d) :
    Integrable (fun p : ℝ × ℝ =>
      (CA * (|p.1| + p.2) + |a0| * CF * (|p.1| ^ 3 + |p.1| * p.2 + p.2 ^ 2) +
        |a0| / rho * (|p.1| + p.2)) * Real.exp (-d * (p.2 + p.1 ^ 2)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0)))

end
end Shao.OQ3
```

All coefficients may be arbitrary real constants for the integrability assertion; positivity needed by X's inequality remains explicit there. The given d is strictly positive. No finite-support, reference-law or unproved uniform-spectrum shortcut is involved.
