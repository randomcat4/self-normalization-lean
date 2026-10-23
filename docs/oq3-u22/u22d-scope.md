# U22d — genuine open-domain smoothness and strict mean derivative

FROZEN before implementation, 2026-10-23, OQ3 lane. Same source-bound U22 batch. Source: read-only R2 report.md38–60 and root-contract section4. The actual tilted mean map must admit a true local inverse; full Fréchet derivative existence alone is not a strict differentiability argument. This unit supplies C∞ on the actual open domain and the exact strict mean derivative needed by the subsequent inverse-function consumer.

Module `Shao.OQ3.OpenDomainSmoothMean`, zero public definitions, two public theorems, exact imports and TYPEs:

```lean
import Shao.OQ3.OpenDomainFrechetCumulants
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_weighted_moment_contDiffOn
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (k : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => ∫ x : ℝ, x ^ k * Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
      (interior (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))

theorem open_domain_quadratic_tilt_smooth_and_strict
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let Z : (ℝ × ℝ) → ℝ := fun p =>
      ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
    let K : (ℝ × ℝ) → ℝ := fun p => Real.log (Z p)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    ContDiffOn ℝ ∞ Z Omega ∧ ContDiffOn ℝ ∞ K Omega ∧
      ContDiffOn ℝ ∞ means Omega ∧
      ∀ theta ∈ Omega,
        let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
        let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
        let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
        let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
        let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
        HasStrictFDerivAt means (row0.prod row1) theta
```

All laws, integrals and domain are actual. No boundedness, nondegeneracy, caller smoothness, arbitrary surrogate functions, or target-derivative assumptions. Theta is quantified only inside the true open exponential-integrability domain, which may be empty. Smoothness does not assert finiteness or differentiability outside that domain. Strict derivative uses the actual covariance rows and remains valid for singular covariance; invertibility will need a separately frozen nondegeneracy hypothesis and theorem.

Use U22b at every interior point, finite-order induction for actual weighted moments, actual positive partition and tilt integral identities, log/division/product rules, U22c full mean derivative, and the genuine C¹-to-strict derivative theorem. No fresh bounded-support argument or directional-to-Fréchet shortcut. Subsequent local inverse, compact inverse-image parameter control, root B Edgeworth/cell/Laplace/far-tail analysis and D remain OPEN; C has only the bounded stability scope accepted by rootv44.

Server-only CPU14–17, one heavy lane command, `-M8192 -j4 -DautoImplicit=false`; reuse pinned environment and necessary accepted-source-view. Root alone shared/cache/pins/imports/integration. Full failures retained; first unchanged success never rerun. Qualified fresh independent complete proof/source semantic review and actual-owner/private/generated transitive-axiom audit mandatory; only propext, Classical.choice, Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by or weakened proof settings. No per-unit execution/control wrapper.

Syntax correction before successful elaboration: full attempt01 reported `expected token` on the scoped infinity symbol. Added `ContDiff` to the notation scopes, preserving every mathematical quantifier, assumption and conclusion. Original frozen scope SHA fec3286ce83dce97759333b2fbb03da075d545a40935b93f10b800dbc849ed73 and failed source e0a8e2b0 remain in server evidence; no successful evidence is invalidated or rerun.
