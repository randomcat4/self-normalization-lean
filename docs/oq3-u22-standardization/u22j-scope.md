# U22j — genuine real moments and the actual whitened 8+delta moment

FROZEN before implementation, 2026-10-23, OQ3 lane. Source R2report38–61/83–92 and the original B moment condition. Natural-power integrability does not by itself state the required real 8+delta integrability. This unit supplies the real-power domination and binds its specialization to the same actual covariance whitening as U22i. It introduces no bounded-support premise, reference-law weak-Cramer stability, or caller-supplied moment conclusion.

Module `Shao.OQ3.OpenDomainRealMoments`, zero public definitions and two public theorems. Exact imports and declarations:

```lean
import Shao.OQ3.OpenDomainAffineMoments
import Shao.OQ3.QuadraticWhiteningSpectralData

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem compact_open_domain_affine_parabola_real_moments
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
      ∀ r : ℝ, 0 ≤ r → ∃ C : ℝ, 0 < C ∧ ∀ theta ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ => Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) r)
          (laws theta) ∧
        0 ≤ (∫ y : Fin 2 → ℝ, Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) r ∂laws theta) ∧
        (∫ y : Fin 2 → ℝ, Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) r ∂laws theta) ≤ C

theorem compact_open_domain_whitened_eight_add_delta_moment
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (lo hi delta : ℝ) (hlo : 0 < lo) (hhi : 0 < hi) (hdelta : 0 < delta)
    (hspec : ∀ p ∈ Theta,
      let D : Matrix (Fin 2) (Fin 2) ℝ :=
        parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
      ∀ xi eta : ℝ,
        lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2)) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
    let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
    let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
      ![∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p]
    let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - means p)
    let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (tilt p).map (Y p)
    (∀ p ∈ Theta, (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
      IsProbabilityMeasure (laws p)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ =>
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta)) (laws p) ∧
        0 ≤ (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ∧
        (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ≤ C
```

The first result transfers actual natural Euclidean moments to every real r>=0 by choosing an integer n>r and proving x^r<=1+x^n for x>=0, split at x=1. Both measurability and genuine integrability precede the integral bound. Its arbitrary matrix field has an explicit uniform entry bound; it is not declared to be whitening. Constants are chosen before theta. Zero radius, r=0, U=0 and empty Theta are allowed, with real-power conventions respected.

The second result uses the literal positive symmetric inverse square root of the actual tilted parabola covariance, retaining the explicit original actual uniform covariance spectra. Its whitening matrix agrees definitionally with U22i. It produces genuine uniform real 8+delta moment integrability, not just a totalized integral inequality or an assumed moment conclusion. Weak-Cramer is unnecessary for this moment-only consequence; no hypothesis of the eventual original B root is removed by this fact. The original beta<2/5 and actual family weak-Cramer conditions remain obligations of the B root, as do the other original conditions.

No Lindeberg/tail-rate statement, compact inverse-image neighborhood, global Legendre geometry, Song Edgeworth theorem, cell reconstruction/summation, boundary Laplace or far-probability result is claimed. B/D remain OPEN; the accepted bounded C result is unchanged. No additional external-result assumption or axiom.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy command; accepted package/source view only. Full fresh independent complete source-to-statement/proof review and every actual module owner/private/generated transitive axiom are mandatory, whitelist propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/weaker settings. Freeze before authoring; preserve failures and reuse unchanged successful gates. No new execution wrapper.
