# U22s — positive lower bound from the proved boundary Taylor producer

Declarations frozen before implementation. Module Shao.OQ3.LocalBoundaryLowerBound; two public theorems, zero definitions. Source binding: read-only original repair01.md equations (11) and (13), lines154–179. The algebra helper states its supplied uniform Taylor bound openly; the C3 producer consumer proves that bound with Q rather than assuming it. The actual rate consumer will use R's already proved same-chart bound, retaining original genuine source Lambda1 positivity. No claim that covariance invertibility alone proves positive tangential curvature, no amplitude/Jacobian/Laplace/root closure. All source spectral/WC/moment/global saddle/far probability assumptions remain in force.

```lean
import Shao.OQ3.LocalBoundaryTaylor

namespace Shao.OQ3
open scoped Topology ContDiff
noncomputable section

theorem exists_positive_boundary_lower_bound_of_taylor
    (F : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho C : ℝ)
    (hlambda : 0 < lambda) (hLambda1 : 0 < Lambda1)
    (hrho : 0 < rho) (hC : 0 < C)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        C * (|r| ^ 3 + |r| * z + z ^ 2)) :
    ∃ delta c : ℝ, 0 < delta ∧ delta ≤ rho ∧ 0 < c ∧ ∀ r z : ℝ,
      |r| ≤ delta → 0 ≤ z → z ≤ delta →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0)

theorem exists_positive_boundary_lower_bound_of_contDiffAt
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 3 F (0, 0))
    (htangent : deriv (fun t : ℝ => F (t, 0)) 0 = 0)
    (hnormal : 0 < fderiv ℝ F (0, 0) (0, 1))
    (hcurvature : 0 < deriv (deriv (fun t : ℝ => F (t, 0))) 0) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ r z : ℝ,
      |r| ≤ delta → 0 ≤ z → z ≤ delta →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0)

end
end Shao.OQ3
```

Proof intent: shrink the already positive rectangle radius below both lambda/(4*C) and Lambda1/(4*C). Bound |r|^3 by delta*r^2, |r|*z by delta*z, and z^2 by delta*z. The remaining coefficients dominate lambda/2 for z and Lambda1/4 for r^2; choose c=min(lambda/2,Lambda1/4)>0. Zero and closed endpoints are included. The second theorem invokes Q with actual derivatives and htangent, so the target lower bound is not present in its premises.
