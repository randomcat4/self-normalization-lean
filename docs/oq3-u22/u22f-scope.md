# U22f — actual compact open-domain tilted moments

FROZEN before implementation, 2026-10-23, OQ3 lane. Independent useful work while U22e awaits root's missing shared inverse-function cache object. Source R2report38–60 requires compact parameter control and true uniform moments; neither directional derivatives nor arbitrary caller moment functions establish this. This unit gives every actual signed tilted moment smooth on the true open domain, and every natural absolute raw tilted moment uniformly bounded on an arbitrary compact subset of that domain.

Module `Shao.OQ3.OpenDomainCompactMoments`, zero public definitions, two public theorems. Exact imports and TYPEs:

```lean
import Shao.OQ3.OpenDomainSmoothMean

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_tilted_moment_contDiffOn
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (k : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => ∫ x : ℝ, x ^ k
        ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
      (interior (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))

theorem compact_open_domain_uniform_tilted_moments
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    (∀ theta ∈ Theta, IsProbabilityMeasure (nu theta)) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ theta ∈ Theta,
        Integrable (fun x : ℝ => |x| ^ k) (nu theta) ∧
          0 ≤ (∫ x : ℝ, |x| ^ k ∂nu theta) ∧
          (∫ x : ℝ, |x| ^ k ∂nu theta) ≤ C
```

Mu is any real probability law; Theta may be empty. No boundedness, caller moment/domination/regularity assumptions, sign restriction on the second parameter, source-atomic law or surrogate integrals. Constants can depend on mu/Theta/k, never on theta within Theta. Genuine integrability is explicit, not inferred from a finite totalized integral. Smoothness is C∞, not analytic omega, and only on the true open domain.

Proof: true positive partition and U22d weighted smoothness give actual normalized tilted moment smoothness through the literal tilt integral formula. The even signed moment of order 2k is continuous on compact Theta and bounded above. The scalar inequality |x|^k ≤ 1+x^(2k), actual tilted probability and genuine integrability give a positive uniform bound for the kth absolute moment, including k=0. Empty compact sets need no nonempty/maximizer hypothesis.

This unit does not yet standardize/whiten these variables, prove the 8+delta moment bound for the standardized vector, supply uniform covariance spectra, a local inverse, compact inverse-image family, Edgeworth/cell/Laplace/far-tail estimates, or B/D root closure. Original root assumptions remain unchanged. C is closed only in rootv44's bounded stability scope.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy lane command; reuse pinned imports and necessary existing accepted-source-view, no shared cache/pins/root-import writes or new execution wrapper. Root owns missing-cache repair. Preserve failed attempts and never repeat passed unchanged checks. Full actual-owner/private/generated transitive axiom gate (only propext, Classical.choice, Quot.sound) and fresh complete independent proof/source semantic review required. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/proof-setting weakening.
