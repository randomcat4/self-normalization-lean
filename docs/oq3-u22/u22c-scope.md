# U22c — actual open-domain full Fréchet cumulants, frozen before implementation

Status: FROZEN, 2026-10-23. Lane OQ3 only. This is the next mathematical consumer in the same substantive U22 batch; U22a independently accepted, U22b full source and first actual-owner audit pass with fresh independent review in progress. No root acceptance follows merely from these producer states.

Source: read-only `current/oq3/proofs/r2/report.md` 38–60, 83–92 and `drafts/oq3/root-contract.md` sections 2/4. The real tilt is the exponential tilt of the actual original law, its first moment pair is the gradient of the actual log partition, and its covariance is the full Fréchet Hessian. This unit supplies that analytic bridge for arbitrary real probability laws on the interior of the actual two-dimensional exponential-integrability domain. It makes no bounded-support or caller derivative/domination assumption. The source-specific bounded APIs are proof patterns only and cannot replace this scope.

Proposed module `Shao.OQ3.OpenDomainFrechetCumulants`, zero public definitions and one public theorem. Exact imports and public declaration:

```lean
import Shao.OQ3.OpenDomainWeightedMoments
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology
noncomputable section

theorem open_domain_quadratic_tilt_frechet_cumulants
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂nu p, ∫ x : ℝ, x ^ 2 ∂nu p)
    let K : (ℝ × ℝ) → ℝ := fun p =>
      Real.log (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    let gradient : (ℝ × ℝ) →L[ℝ] ℝ :=
      (means theta).1 • pr0 + (means theta).2 • pr1
    let hessian : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
      row0.smulRight pr0 + row1.smulRight pr1
    IsProbabilityMeasure (nu theta) ∧
      MemLp (fun x : ℝ => x) 2 (nu theta) ∧
      MemLp (fun x : ℝ => x ^ 2) 2 (nu theta) ∧
      HasFDerivAt means (row0.prod row1) theta ∧
      HasFDerivAt K gradient theta ∧
      HasFDerivAt (fun p => fderiv ℝ K p) hessian theta
```

All objects in the conclusion are literal actual integrals/tilts/covariance; none is a caller-supplied matrix or arbitrary moment function. The derivative is on all of ℝ×ℝ, at the interior point, and the second derivative is of the actual `fderiv ℝ K` using a genuine neighborhood identity on the true open domain. No inference from directional derivatives alone is allowed. Covariance degeneracy is permitted; positive definiteness is not needed for these derivative identities.

Proof boundary: use U22b full weighted-moment Fréchet derivatives, positive actual partition, genuine log/quotient rules, actual tilted moment integral identities, and actual covariance identities. This proves no local inverse, strict differentiability, compact-uniform moment theorem, Edgeworth engine, cell/Laplace/far-tail result or B/D root. PR173/C root acceptance remains root-owned. Preserve p54 repair and external attributions; no novelty/optimality claim.

Execution: server CPU14–17 only, one heavy command including children, native `-M8192 -j4 -DautoImplicit=false`; no local Lean, cache/pin/root-import/shared implementation edits. Reuse the existing necessary accepted-source-view; no per-unit control wrapper. Record complete failures, never repeat passed unchanged source/audit. Fresh independent complete source-to-statement/proof review plus actual-owner/private/generated transitive axiom audit required. Whitelist only propext, Classical.choice, Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by or proof-setting weakening.
