# U22o — actual two-variable boundary coordinate jet

FROZEN before implementation, 2026-10-23, OQ3 lane. Source repair01 equations8–11 use G(r,z)=(a0+r,(a0+r)^2/x^2-z). This next producer binds a single actual local rate chart to its complete two-variable first/second derivative jet, including the normal sign and curvature. This is preparatory to, not a proof of, the uniform Taylor/lower-bound or Laplace estimate.

Module `Shao.OQ3.OpenDomainBoundaryJet`, zero public definitions and one public theorem. Exact imports and TYPE:

```lean
import Shao.OQ3.OpenDomainRateDerivatives
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_boundary_coordinate_jet
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ≠ 0)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0) (hnegative : theta.2 < 0)
    (hmean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (hsaddle : theta.1 = -2 * a0 * theta.2 / level ^ 2) :
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
    let B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
      pr0.prod ((2 * a0 / level ^ 2) • pr0 - pr1)
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ means theta ∈ e.target ∧ e.source ⊆ Omega ∧
      let J : (ℝ × ℝ) → ℝ := fun z =>
        (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
      let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
        (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
      let F : (ℝ × ℝ) → ℝ := fun w => J (G w)
      0 < -theta.2 ∧ ContDiffAt ℝ ∞ F (0, 0) ∧
        HasFDerivAt F ((-theta.2) • pr1) (0, 0) ∧
        (∀ u v : ℝ × ℝ,
          (fderiv ℝ (fun w => fderiv ℝ F w) (0, 0) u) v =
            (L.symm (B u)).1 * (B v).1 + (L.symm (B u)).2 * (B v).2 +
              (2 * theta.2 / level ^ 2) * u.1 * v.1) ∧
        ∀ᶠ w in 𝓝 (0, 0),
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) (G w) = (F w : EReal)
```

F is the actual rate composed with the exact source coordinate map using one chart witness, not a separately assumed smooth function. B is the literal derivative of G at zero. The second derivative is the inverse actual covariance pulled back through B, plus the curvature term; evaluating both directions at (1,0) recovers the source Lambda1 expression. Genuine center C-infinity justifies the actual fderiv/fderiv values. The proof must establish the chain-rule identity for fderiv F on a genuine neighborhood before differentiating it, using finite C1 of J near the center. Its eventual global-rate identity uses actual target membership supplied by continuity of G.

No uniform Taylor constant, local rate lower bound, covariance-amplitude estimate, tail-domain coordinate equivalence/Jacobian theorem, Laplace remainder, Edgeworth/cells/far-probability bound, or B/D closure is claimed. These remain the next source-bound obligations. Original root conditions are retained, and no external axiom is introduced.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy command; accepted package/source view only. Fresh independent complete source-to-statement/proof review and every actual module owner/private/generated transitive axiom required; whitelist propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/weak settings. Preserve failures and reuse unchanged successful gates; no new execution wrapper.
