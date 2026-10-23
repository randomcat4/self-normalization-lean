# U22w — quantitative scaled boundary kernel error

Complete declarations frozen before implementation. Module Shao.OQ3.BoundaryLaplaceScaledError, two public theorems, zero definitions. Source repair01.md lines183–210 equation(14), with scale t=1/sqrt(n), r=t*u, z=t^2*v. This module consumes explicitly proved local Taylor/coercivity/amplitude bounds (R/T/U) and produces the pointwise order-t kernel error on the expanding coordinate rectangle, using V's exponential comparison. It does not assume the desired scaled kernel error, and does not yet prove the integrated estimate, cutoff complement, change of variables or original probability/root conclusion.

```lean
import Shao.OQ3.BoundaryLaplaceExponential

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem boundary_taylor_scaled_error
    (F : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho CF : ℝ) (hCF : 0 ≤ CF)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2))
    (t u v : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hv : 0 ≤ v)
    (hru : |t * u| ≤ rho) (hzv : t ^ 2 * v ≤ rho) :
    |(F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2 -
      (lambda * v + Lambda1 / 2 * u ^ 2)| ≤
      CF * t * (|u| ^ 3 + |u| * v + v ^ 2)

theorem boundary_weighted_scaled_kernel_error
    (F A : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho CF CA c d : ℝ)
    (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hd : 0 < d)
    (hdc : d ≤ c) (hdl : d ≤ lambda) (hdq : d ≤ Lambda1 / 2)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2))
    (hmargin : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0))
    (hamplitude : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |A (r, z) - A (0, 0)| ≤ CA * (|r| + z))
    (t u v : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hv : 0 ≤ v)
    (hru : |t * u| ≤ rho) (hzv : t ^ 2 * v ≤ rho) :
    |A (t * u, t ^ 2 * v) *
        Real.exp (-((F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2)) -
      A (0, 0) * Real.exp (-(lambda * v + Lambda1 / 2 * u ^ 2))| ≤
      t * (CA * (|u| + v) + |A (0, 0)| * CF * (|u| ^ 3 + |u| * v + v ^ 2)) *
        Real.exp (-d * (v + u ^ 2))

end
end Shao.OQ3
```

Both statements include u of either sign, v=0 and closed rectangle boundaries. Coercivity and leading exponent share the positive d envelope. The polynomial times exp(-d*(v+u^2)) is independent of t; integrability and cutoff-error integration remain the next source dependencies. No odd-term cancellation is used, in agreement with the repair's explicit relative-error scope.
