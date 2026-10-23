# U22m — genuine local Legendre gradient and inverse-covariance Hessian

FROZEN before implementation, 2026-10-23, OQ3 lane. Source R2report38–55, root-contract2/4 and the local boundary-rate setup require derivatives of the actual finite Legendre expression. This unit binds the local inverse from U22e to the true global value proved in U22l, and derives its first and second Frechet derivatives at the actual center. No formal inverse-Hessian or dual-gradient identity is a caller assumption.

Module `Shao.OQ3.OpenDomainRateDerivatives`, zero public definitions and one public theorem. Exact imports and TYPE:

```lean
import Shao.OQ3.OpenDomainLegendre

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_local_rate_derivatives
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
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    let covector : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
      pr0.smulRight pr0 + pr1.smulRight pr1
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ means theta ∈ e.target ∧ e.source ⊆ Omega ∧
      let J : (ℝ × ℝ) → ℝ := fun z =>
        (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
      ContDiffAt ℝ ∞ J (means theta) ∧
        HasFDerivAt J (theta.1 • pr0 + theta.2 • pr1) (means theta) ∧
        HasFDerivAt (fun z => fderiv ℝ J z)
          (covector.comp (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (means theta) ∧
        ∀ z ∈ e.target,
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z = (J z : EReal)
```

L is the literal continuous linear equivalence whose derivative matrix is the actual tilted covariance at theta; its inverse is therefore the actual inverse covariance operator. The covector map identifies a real pair with the corresponding linear functional, so the displayed derivative of fderiv J is the inverse-covariance Hessian as a continuous bilinear form. J uses the same actual mean inverse and actual log partition; its global EReal Legendre equality is asserted only on that chart's target, where the actual inverse parameter stays in Omega.

The proof must obtain the genuine local identity fderiv J(z)=covector(e.symm z) in a neighborhood of means(theta), not infer a second derivative from a single-point first-derivative equality. Finite C1 regularity on some neighborhood follows from the inverse's center C-infinity regularity; no common C-infinity neighborhood is assumed from that fact alone. Differentiating the eventual gradient identity uses the actual inverse derivative from U22e. The local rate's own center C-infinity regularity follows by composition with K inside the true domain. Totalized values outside the chart are not certified as a global real rate.

No global inverse, globally unique maximizing parameter, global tail-domain minimizing saddle, uniform covariance spectra, weak-Cramer propagation, boundary Laplace estimate, Edgeworth/cell/far-probability statement, or root B/D closure is claimed. The center determinant premise and every original B condition remain explicit. Standard proved calculus and Jensen results introduce no external-result axiom; Song attribution and its unproved obligations remain separate.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy command; accepted package/source view only. Exact declaration frozen before implementation. Fresh independent complete source-to-statement/proof review and every actual owner/private/generated transitive axiom required, whitelist propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/weak settings. Preserve failures and reuse unchanged successful gates; no new execution wrapper.
