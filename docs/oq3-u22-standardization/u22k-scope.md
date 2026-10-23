# U22k — actual local mean inverse with compact parameter control

FROZEN before implementation, 2026-10-23, OQ3 lane. Source R2report50–60: the moment neighborhood is covered by the inverse mean map and its parameter image stays in a compact subset of the true exponential-integrability interior. This unit obtains that local compactness from the actual U22e mean chart, with actual tilted covariance determinant nonzero at the center. It is a local analytic producer, not a global injectivity or rate-minimization theorem.

Module `Shao.OQ3.OpenDomainCompactMeanChart`, zero public definitions and one public theorem. Exact imports and TYPE:

```lean
import Shao.OQ3.OpenDomainMeanInverse
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_compact_mean_chart
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ≠ 0) :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ), ∃ epsilon : ℝ,
      0 < epsilon ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ e.source ⊆ Omega ∧
      Metric.closedBall (means theta) epsilon ⊆ e.target ∧
      ContDiffAt ℝ ∞ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) (means theta) ∧
      let U : Set (ℝ × ℝ) := Metric.ball (means theta) epsilon
      let Theta : Set (ℝ × ℝ) := e.symm '' Metric.closedBall (means theta) epsilon
      IsOpen U ∧ means theta ∈ U ∧ IsCompact Theta ∧ theta ∈ Theta ∧
        Theta ⊆ Omega ∧
        ContinuousOn (e.symm : (ℝ × ℝ) → (ℝ × ℝ))
          (Metric.closedBall (means theta) epsilon) ∧
        (∀ m ∈ Metric.closedBall (means theta) epsilon,
          e.symm m ∈ Theta ∧ means (e.symm m) = m) ∧
        (∀ p ∈ Theta, e.symm (means p) = p) ∧
        means '' Theta = Metric.closedBall (means theta) epsilon ∧
        e.symm '' U ⊆ Theta
```

The moment neighborhood is the literal positive-radius open ball U about the actual tilted mean. Its closed ball lies inside the chart target. Theta is the literal continuous inverse image of that compact closed ball, not an assumed arbitrary compact set; both inverse identities and exact mean image are stated. Theta lies in the true open integrability interior Omega, so all previously proved genuine tilt/smoothness/moment interfaces apply there. The inverse's center C-infinity conclusion is inherited from U22e; uniform C-infinity on the entire chart is not asserted without further justification. The theorem permits arbitrary unbounded mu subject to the explicit actual-domain and covariance nondegeneracy gates.

No global inverse, extended-real Legendre equality, strict/global rate minimum, uniform spectral constants, weak-Cramer propagation, Song Edgeworth, Lindeberg, cells, boundary Laplace, far-probability bound, or B/D root closure is claimed. In particular, compactness alone is not a proof that the covariance is nondegenerate at every image point. Original B retains its actual uniform spectral/weak-Cramer and other conditions. The bounded C result remains unchanged, and no external result is introduced as an axiom.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy command; accepted package/source view only. Full fresh independent complete source-to-statement/proof review and all actual owner/private/generated transitive axioms required, whitelist propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/weak settings. Keep frozen declarations and failed evidence; reuse successful source-bound gates, no new execution wrapper.
