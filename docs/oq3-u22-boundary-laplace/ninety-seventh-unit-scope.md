# U22p — a genuine uniform cubic Taylor remainder at a center

FROZEN before implementation, 2026-10-23, OQ3 lane. Repaired B equation11 needs a uniform cubic tangent remainder, rather than a pointwise second-derivative identity or an assumed remainder inequality. This scalar analytic producer is the tangent component of the subsequent two-variable actual-rate estimate.

Module `Shao.OQ3.LocalCubicTaylor`, zero public definitions and one public theorem. Exact imports and TYPE:

```lean
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Shao.OQ3
open MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem exists_uniform_cubic_taylor_bound_at_zero
    (g : ℝ → ℝ) (hg : ContDiffAt ℝ 3 g 0) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r : ℝ, |r| ≤ rho →
      |g r - g 0 - (deriv g 0) * r - (deriv (deriv g) 0) / 2 * r ^ 2| ≤
        C * |r| ^ 3
```

The only analytic premise is genuine finite-order C3 at zero. The conclusion constructs positive radius and constant before the varying r, includes both signs and closed-radius endpoints, and uses actual first and second derivatives. No desired remainder bound, a third-derivative bound, or differentiability of a fabricated polynomial surrogate is a premise. At zero the assertion must give an exact zero remainder.

A suitable route is a finite C3 neighborhood and the proved third-order Peano Taylor theorem, then absorb its finite cubic coefficient into an O(|r|^3) bound and shrink to a closed half-radius. A Lagrange remainder with a genuinely produced local third-derivative bound is also valid. Neither C-infinity openness nor a merely o(r^2) remainder suffices for the claimed cubic order. The theorem is a standard calculus helper, with the actual rate consumer and the normal/mixed-term control still separate. No original B/D root, Laplace asymptotic, Edgeworth/cell/far-probability claim or external-result axiom.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy command; accepted package/source view only. Exact declaration frozen before implementation. Fresh independent complete source-to-statement/proof review and every actual module owner/private/generated transitive axiom required; whitelist propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/weak settings. Preserve failures and reuse successful source-bound gates; no new execution wrapper.
