# U22q — uniform boundary-coordinate Taylor remainder

Source binding: original read-only `C:/game/shao/current/oq3/proofs/r2/repair01.md`, equations (8)–(11), lines 124–159. This is the analytic producer for the fixed-rectangle remainder, after O's actual two-variable jet and P's scalar cubic producer. It does not identify an arbitrary function with the actual rate, or import a desired remainder estimate as a hypothesis.

Before implementation the complete imports and public declarations are frozen below. Module `Shao.OQ3.LocalBoundaryTaylor`; two public theorems, zero public definitions. All newly written source is UTF-8 with LF. The first theorem requires genuine center C2, obtains a fixed positive rectangle and controls the normal increment by the actual center normal derivative. The second requires genuine center C3 and controls the full remainder using actual tangent first/second derivatives and actual normal derivative. Both include z=0 and all signs of r; the tail side is explicitly 0<=z. Constants and radii are uniform over the whole closed rectangle.

```lean
import Shao.OQ3.LocalCubicTaylor
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue

namespace Shao.OQ3
open scoped Topology ContDiff
noncomputable section

theorem exists_uniform_normal_increment_bound_at_zero
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 2 F (0, 0)) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
      |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (r, 0) - (fderiv ℝ F (0, 0) (0, 1)) * z| ≤
        C * (|r| * z + z ^ 2)

theorem exists_uniform_boundary_taylor_bound_at_zero
    (F : (ℝ × ℝ) → ℝ) (hF : ContDiffAt ℝ 3 F (0, 0)) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
      |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - (deriv (fun t : ℝ => F (t, 0)) 0) * r -
        (fderiv ℝ F (0, 0) (0, 1)) * z -
        (deriv (deriv (fun t : ℝ => F (t, 0))) 0) / 2 * r ^ 2| ≤
        C * (|r| ^ 3 + |r| * z + z ^ 2)

end
end Shao.OQ3
```

Planned proof: actual normal derivative H(w)=DF(w)(0,1) is differentiable at zero by center C2; its genuine anchored big-O supplies a local linear variation bound. Center finite C2 also gives a genuine neighborhood of differentiability of F. On each normal segment, the mean-value inequality gives the first result with a single common radius and constant. For the second result, restrict F to the tangent line, use P's scalar C3 theorem, shrink the two radii to their positive minimum and add the two controlled errors.

Scope remaining open: applying these theorems to the same actual O chart, identifying the source Lambda1 coefficient, retaining its original positivity, local positive lower bound, amplitude/Jacobian/tail-coordinate equivalence, quantitative Laplace, Edgeworth/cells/far probability and original B/D closure. The source's actual uniform spectral/WC, moment, saddle and far-probability assumptions remain unchanged. One complete fresh independent final review plus exact-source server kernel/all-owned-transitive-axiom evidence is required for acceptance. No duplicate SOURCE or environment-inventory workflow is introduced.
