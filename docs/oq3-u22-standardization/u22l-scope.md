# U22l — actual global Legendre value on the local mean chart

FROZEN before implementation, 2026-10-23, OQ3 lane. Source R2report38–55 and root-contract2/4 require a true extended-real global Legendre transform and agreement with the finite local expression, rather than a domain-free real log integral or a merely formal dual formula. This unit proves the global bound by Jensen under the actual normalized tilt, then binds attainment to the compact local mean chart from U22k.

Module `Shao.OQ3.OpenDomainLegendre`, zero public definitions and two public theorems. Exact imports and declarations:

```lean
import Shao.OQ3.OpenDomainCompactMeanChart
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_legendre_attained
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let m : ℝ × ℝ := (∫ x : ℝ, x ∂nu, ∫ x : ℝ, x ^ 2 ∂nu)
    let Ktheta : ℝ := Real.log
      (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)
    let I : ℝ := theta.1 * m.1 + theta.2 * m.2 - Ktheta
    (∀ p : Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)),
      (p : ℝ × ℝ).1 * m.1 + (p : ℝ × ℝ).2 * m.2 -
        Shao.Probability.bivariateLogMGF mu (fun x : ℝ => (x, x ^ 2)) p ≤ I) ∧
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) m = (I : EReal)

theorem open_domain_quadratic_tilt_compact_legendre_chart
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
      0 < epsilon ∧ (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ e.source ⊆ Omega ∧
      Metric.closedBall (means theta) epsilon ⊆ e.target ∧
      let Theta : Set (ℝ × ℝ) := e.symm '' Metric.closedBall (means theta) epsilon
      IsCompact Theta ∧ theta ∈ Theta ∧ Theta ⊆ Omega ∧
        ∀ z ∈ Metric.closedBall (means theta) epsilon,
          e.symm z ∈ Theta ∧ means (e.symm z) = z ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z =
            (((e.symm z).1 * z.1 + (e.symm z).2 * z.2 - Real.log
              (∫ x : ℝ, Real.exp ((e.symm z).1 * x + (e.symm z).2 * x ^ 2) ∂mu) : ℝ) : EReal)
```

The supporting inequality is quantified over the entire true exponential-integrability domain, including its boundary. Only the attaining center theta must be interior, so its tilted first/two-coordinate moments are genuinely integrable. For p in that domain, F=(p-theta) dot W has a genuine tilted first moment, exp(F) is genuinely tilted-integrable, and its expectation is Z(p)/Z(theta). Jensen gives E_theta F <= log Z(p)-log Z(theta), hence every global dual test is bounded by the actual center value. The center itself is an admissible test, proving equality with the EReal supremum and therefore finiteness. No global convexity/attainment conclusion is assumed by the caller.

The second theorem obtains its actual chart and compact parameter set from U22k, proves mean(e.symm z)=z for every point of the closed moment ball, and applies the first result at that actual inverse parameter in Omega. It does not assume a desired global Legendre equality or replace the EReal supremum by a locally defined real function. Zero-covariance cases are allowed by the first theorem; the second retains actual center determinant nonzero solely for the inverse-chart producer.

No uniqueness of the maximizing parameter, global inverse, global tail-domain minimizing saddle, local rate derivative/Hessian, uniform covariance spectral constants, weak-Cramer propagation, Edgeworth/cells/Laplace/far-probability bound, or root B/D closure is claimed. Original B conditions and p54 repairs remain intact. Jensen is a proved pinned Mathlib theorem, not an external axiom; external Song attribution and unproved obligations remain separate.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy command; accepted package/source view only. Freeze exact declarations before implementation. Full fresh independent complete source-to-statement/proof review and all actual owner/private/generated transitive axioms required, whitelist propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/weak settings. Preserve failures and reuse unchanged successful gates; no new execution wrapper.
