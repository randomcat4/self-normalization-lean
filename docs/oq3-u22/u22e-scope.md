# U22e — actual nondegenerate quadratic-tilt local mean inverse

FROZEN before implementation, 2026-10-23, OQ3 lane. Source: R2report38–60 and root-contract section4. This unit consumes the genuine open-domain smooth/strict producer to establish an actual local inverse, not a free caller-supplied inverse or a statement assuming the target identity.

Module `Shao.OQ3.OpenDomainMeanInverse`, zero public definitions, one public theorem. Exact imports and declaration:

```lean
import Shao.OQ3.OpenDomainSmoothMean
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_local_mean_inverse
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
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ means theta ∈ e.target ∧ e.source ⊆ Omega ∧
      ContDiffAt ℝ ∞ (e.symm : (ℝ × ℝ) → (ℝ × ℝ)) (means theta) ∧
      HasStrictFDerivAt (e.symm : (ℝ × ℝ) → (ℝ × ℝ))
        (L.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (means theta)
```

The determinant hypothesis is explicitly the actual covariance's determinant at the given interior point. It is the exact nondegeneracy gate for this helper, weaker than the original B positive-definite covariance/spectral hypotheses; this helper does not silently replace those root hypotheses, and a root consumer must establish this gate from its retained conditions. No boundedness, arbitrary mean function, caller derivative, selector, inverse or surrogate covariance is assumed.

The open partial homeomorphism itself supplies honest open source/target neighborhoods, two-sided inverse identities, maps into the source, and continuity there. Its literal forward function must equal the actual tilted mean pair everywhere; its source must stay in the true domain's interior. Smoothness and exact strict inverse derivative are asserted at the actual center mean. No global inverse, global Legendre optimum, uniform Hessian spectra/moments on a compact inverse-image family, expansion engine, cell/Laplace/far-tail bound or B/D root closure is claimed.

Proof route: use the actual covariance symmetry and determinant to construct a genuine continuous linear equivalence for its two-row derivative, use U22d smoothness and U22c full derivative, apply the genuine inverse function theorem, and restrict its open source to Omega. Preserve exact frozen declarations, author/reviewer separation, full actual-owner/private/generated transitive-axiom audit and a fresh complete independent semantic/proof review. Only propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by or proof-setting weakening. All Lean server CPU14–17/native8192/j4/autoImplicit=false/one heavy; pinned environment and necessary existing view only; root alone shared/cache/imports/pins/integration. Retain failures; do not repeat unchanged success.
