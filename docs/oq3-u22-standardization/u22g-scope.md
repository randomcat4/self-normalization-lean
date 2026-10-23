# U22g — compact actual tilted affine-parabola Euclidean moments

FROZEN before implementation, 2026-10-23, OQ3 lane. This is the next source-bound moment transfer after U22f, independent of the blocked inverse-function cache. R2report57–60 and83–92 require uniform actual Euclidean moments of a centered transformed parabola family. This unit transfers true compact raw tilted moments through an arbitrary uniformly entry-bounded matrix family; a later actual whitening consumer must produce that bound from its retained spectral hypotheses.

Module `Shao.OQ3.OpenDomainAffineMoments`, zero public definitions, one public theorem. Exact imports and TYPE:

```lean
import Shao.OQ3.OpenDomainCompactMoments
import Shao.OQ3.CovarianceWhitening

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem compact_open_domain_affine_parabola_moments
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hA : ∀ theta ∈ Theta, ∀ i j : Fin 2, |A theta i j| ≤ U) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
      ![∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p]
    let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x =>
      A p *ᵥ (![x, x ^ 2] - means p)
    let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (tilt p).map (Y p)
    (∀ theta ∈ Theta, IsProbabilityMeasure (laws theta)) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ theta ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k)
          (laws theta) ∧
        0 ≤ (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws theta) ∧
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws theta) ≤ C
```

The source law, true open domain, tilts, actual mean pair, centered parabola, matrices and pushforward laws are all literal. A need not be continuous in theta; for each fixed theta the sample map is continuous. No joint-parameter measurability is claimed. Theta may be empty and U may vanish. Positive constants can depend on mu/Theta/U/k, not theta. Natural k includes0, and the radius is the exact Euclidean square-root expression, not the product/sup norm.

The uniform entry bound is an explicit matrix-family hypothesis, not an assumption that the output moment theorem holds. This helper does not call arbitrary A the covariance inverse square root. The subsequent actual whitening theorem must bind A to its genuine actual covariance construction and establish this bound from the retained uniform spectral hypotheses. No such binding, standardized covariance, weak-Cramer transfer, general local inverse, 8+delta real exponent conclusion or B/D root closure follows automatically here.

Proof route: U22f supplies true raw absolute moments and uniform first/second moment bounds, hence bounds on actual tilted means. The matrix entry bound and Euclidean-radius triangle bound yield radius(Y_theta(x)) ≤ Q(1+x²). Powers are bounded by (2Q)^k(1+|x|^(2k)), whose integrability and uniform expectation follow from U22f. Transfer through the actual continuous sample map uses genuine measurable pushforward/integral identities. No bounded-support argument or totalized-divergent integral is allowed.

All Lean server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy command; root alone shared/cache/pins/imports/integration. Reuse pinned artifacts and necessary accepted-source-view, no execution wrapper or repeated unchanged successful checks. Preserve author/reviewer separation and full source-to-statement/proof review of every actual owner/private/generated declaration plus transitive standard-three axiom audit. No sorry/admit/new axiom/unsafe/native_decide/implemented_by or weakened settings.
