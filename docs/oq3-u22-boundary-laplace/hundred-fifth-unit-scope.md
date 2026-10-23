# U22x — global expanding-rectangle cutoff envelope

Exact complete declaration frozen before implementation. Module Shao.OQ3.BoundaryLaplaceCutoff, one public theorem, zero definitions. Source repair01.md183–210 equation14. Consumes W's genuine local producer bounds and extends the scaled kernel by zero outside the expanding coordinate rectangle; proves an explicit order-t pointwise error envelope for ALL u real/v>=0. Outside cutoff, rho<=t*(|u|+v) follows from the failed rectangle test and 0<t<=1, so the missing leading mass is controlled by t*|A0|/rho*(|u|+v)*exp(-d*(v+u²)). This replaces a merely qualitative dominated-convergence claim with a quantitative global pointwise bound. Integrability, integration, original-coordinate Jacobian/scaling and actual probability/far-layer errors remain open. No desired global-envelope conclusion is assumed.

```lean
import Shao.OQ3.BoundaryLaplaceScaledError

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem boundary_weighted_scaled_cutoff_error
    (F A : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho CF CA c d : ℝ)
    (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hrho : 0 < rho) (hd : 0 < d)
    (hdc : d ≤ c) (hdl : d ≤ lambda) (hdq : d ≤ Lambda1 / 2)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2))
    (hmargin : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0))
    (hamplitude : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |A (r, z) - A (0, 0)| ≤ CA * (|r| + z))
    (t u v : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hv : 0 ≤ v) :
    |(if |t * u| ≤ rho ∧ t ^ 2 * v ≤ rho then
        A (t * u, t ^ 2 * v) *
          Real.exp (-((F (t * u, t ^ 2 * v) - F (0, 0)) / t ^ 2)) else 0) -
      A (0, 0) * Real.exp (-(lambda * v + Lambda1 / 2 * u ^ 2))| ≤
      t * (CA * (|u| + v) + |A (0, 0)| * CF * (|u| ^ 3 + |u| * v + v ^ 2) +
        |A (0, 0)| / rho * (|u| + v)) *
        Real.exp (-d * (v + u ^ 2))


end
end Shao.OQ3
```
