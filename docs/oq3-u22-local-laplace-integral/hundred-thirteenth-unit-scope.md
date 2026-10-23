# OQ3 U22af — actual original-coordinate normalized local Laplace theorem

DECLARATION_FROZEN_BEFORE_IMPLEMENTATION. Source repair01.md135-210 (SHA2569d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd), especially equation14 actual tilted covariance amplitude and source Legendre density. Assemble qualified AB with AC/AD/AE: same actual L/e, actual J and B in original mean coordinates, exact fixed parabolic strip, true global EReal rate identity and positive actual covariance there, genuine original-strip uncentered integrability, external1/(2pi*t²), positive exact t*exp(-J0/t²)*C0/(2pi) main and relative order-t error. Actual center determinant and actual chosen tangential curvature positivity remain EXPLICIT, as in AB. No assumed Taylor/coercivity/amplitude/measurability/scaled integral/error premise.

Module Shao.OQ3.OpenDomainBoundaryLaplaceNormalization; imports OpenDomainBoundaryLaplaceIntegral and BoundaryLaplaceNormalization. Namespace Shao.OQ3; MeasureTheory open; Matrix Topology ContDiff scoped.

```lean
theorem open_domain_boundary_laplace_original_strip
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)
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
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance (nu theta)
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    let row0 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 0 • pr0 + D 0 1 • pr1
    let row1 : (ℝ × ℝ) →L[ℝ] ℝ := D 0 1 • pr0 + D 1 1 • pr1
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = row0.prod row1 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = means ∧ theta ∈ e.source ∧ e.source ⊆ Omega ∧
      let K : (ℝ × ℝ) → ℝ := fun p => Real.log
        (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
      let J : (ℝ × ℝ) → ℝ := fun w =>
        (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - K (e.symm w)
      let B : (ℝ × ℝ) → ℝ := fun w =>
        (Real.sqrt (parabolaCovariance (nu (e.symm w))).det)⁻¹
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      let C0 : ℝ := (Real.sqrt D.det)⁻¹ * (Real.sqrt (2 * Real.pi / Lambda1) / (-theta.2))
      let J0 : ℝ := J (a0, a0 ^ 2 / level ^ 2)
      let m0 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
      0 < -theta.2 ∧ (0 < Lambda1 → 0 < C0 ∧ ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧
        let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
          w.1 ^ 2 / level ^ 2 - rho ≤ w.2 ∧ w.2 ≤ w.1 ^ 2 / level ^ 2}
        (∀ w ∈ V, w ∈ e.target ∧ e.symm w ∈ e.source ∧ e.symm w ∈ Omega ∧
          means (e.symm w) = w ∧ 0 < (parabolaCovariance (nu (e.symm w))).det ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w = (J w : EReal)) ∧
        ∀ t : ℝ, 0 < t → t ≤ 1 →
          let W : (ℝ × ℝ) → ℝ := fun w => B w * Real.exp (-J w / t ^ 2)
          let Ln : ℝ := (1 / (2 * Real.pi * t ^ 2)) * ∫ w : ℝ × ℝ in V, W w ∂m0
          let main : ℝ := t * Real.exp (-J0 / t ^ 2) * (C0 / (2 * Real.pi))
          IntegrableOn W V m0 ∧ 0 < main ∧ |Ln / main - 1| ≤ C * t)
```

Proof plan: call AB once, retain exact same chart and inverse covariance L, use its actual center amplitude equality to identify literal C0. Transfer the already produced scaled relative integral bound via AE with J and true inverse-chart covariance amplitude B. AC's exact image equality lifts AB's entire pointwise window to the original strip. No theorem assertion for actual random-sample probability, exterior mass, physical a/q event positivity/equivalence, n/sqrt constant algebra, Edgeworth/cells or original B/D closure.

One publicTHM/0defs; actual allowner source/type/value and transitiveAX audited, fresh independent full review before acceptance. All checks server CPU14-17,M8192,j4,autoImplicit=false,maxone heavy. No replay accepted gates, UTF8LF before first gate.
