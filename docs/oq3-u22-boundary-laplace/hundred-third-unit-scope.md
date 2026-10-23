# U22v — quantitative exponential comparison for boundary Laplace

Exact declarations frozen before implementation. Module Shao.OQ3.BoundaryLaplaceExponential; two public theorems, zero definitions. Source binding: repair01.md lines183–210, equation(14), retaining the required relative O(n^(-1/2)) rather than only a qualitative limit. This is the proved pointwise exponential-comparison producer used after the actual Taylor/lower-bound/amplitude inputs. It is not yet the scaled-integral or Laplace theorem, and takes its numerical exponent/amplitude error estimates explicitly. No probability/Edgeworth/far-field/root closure claim.

```lean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Shao.OQ3
open scoped Topology
noncomputable section

theorem abs_exp_neg_sub_exp_neg_le
    (a b d : ℝ) (ha : d ≤ a) (hb : d ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ Real.exp (-d) * |a - b|

theorem abs_weighted_exp_neg_sub_le
    (a b w w0 d E Q : ℝ) (ha : d ≤ a) (hb : d ≤ b)
    (hexponent : |a - b| ≤ E) (hamplitude : |w - w0| ≤ Q) :
    |w * Real.exp (-a) - w0 * Real.exp (-b)| ≤
      (Q + |w0| * E) * Real.exp (-d)

end
end Shao.OQ3
```

The first bound follows from the real mean-value inequality on the full closed interval [min(a,b),max(a,b)], where the absolute derivative of exp(-t) is at most exp(-d). The second is the exact two-term decomposition plus positive exponential bounds. No smallness condition on a-b, sign condition on d, cancellation of odd terms or desired integral estimate is assumed. These estimates permit a Gaussian/exponential envelope once both genuine scaled exponents have the same positive quadratic/normal lower bound.
