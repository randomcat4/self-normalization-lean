# U22n — actual boundary rate and the source Lambda1 coefficient

FROZEN before implementation, 2026-10-23, OQ3 lane. Source R2's fixed saddle boundary q=a^2/x^2 and root-contract2/4 define Lambda1 as 2*t0/x^2+(1,2*a0/x^2)*Delta^(-1)*(1,2*a0/x^2)^T. This unit computes the two derivatives of the actual local/global Legendre rate along that curve using U22m, including a genuine neighborhood derivative identity before differentiating again.

Module `Shao.OQ3.OpenDomainBoundaryRate`, zero public definitions and one public theorem. Exact imports and TYPE:

```lean
import Shao.OQ3.OpenDomainRateDerivatives

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_tilt_boundary_rate_derivatives
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det ≠ 0)
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0)
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
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧
      theta ∈ e.source ∧ means theta ∈ e.target ∧ e.source ⊆ Omega ∧
      let J : (ℝ × ℝ) → ℝ := fun z =>
        (e.symm z).1 * z.1 + (e.symm z).2 * z.2 - K (e.symm z)
      let f : ℝ → ℝ := fun a => J (a, a ^ 2 / level ^ 2)
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      ContDiffAt ℝ ∞ f a0 ∧ HasDerivAt f 0 a0 ∧
        HasDerivAt (deriv f) Lambda1 a0 ∧
        ∀ᶠ a in 𝓝 a0,
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
            (a, a ^ 2 / level ^ 2) = (f a : EReal)
```

The mean point, parabola boundary, saddle stationarity relation and inverse covariance all refer to the same actual tilted law. Lambda1 is the source quadratic form expressed through the continuous inverse of the actual covariance derivative; its leading vector is (1,2*a0/level^2). The second derivative must include the curvature term 2*theta.2/level^2. Neither this coefficient nor its positivity is assumed or manufactured as a second-derivative hypothesis. The first derivative vanishes by the actual saddle relation. The real boundary function is C-infinity at a0 and agrees with the genuine global EReal Legendre transform for all sufficiently nearby a, with that neighborhood supplied by the actual chart.

The positive level/a0 premises retain source geometry, although the calculus identity itself may admit a wider domain. Original B additionally retains theta.2<0, level<1, Lambda1>0, its global saddle/localization, uniform spectra, real moments, WC with beta<2/5, and explicit far-probability conditions; none is removed from the root by this helper. No positive Lambda1, Laplace asymptotic, global minimum, Edgeworth, cell estimate, far-probability bound or B/D root closure follows from this statement alone. No external-result axiom.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy command; accepted package/source view only. Exact declaration frozen before implementation. Fresh independent complete source-to-statement/proof review and all actual module owner/private/generated transitive axioms required, whitelist propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/weak settings. Preserve failures and reuse unchanged successful gates; no new execution wrapper.
