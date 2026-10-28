# GN277: compact actual open-MGF log-cubic parabola oscillation

Frozen before implementation at 2026-10-27T22:55:09.219270+00:00. Module Shao.OQ3.CompactOpenDomainLogCubicOscillation.

One complete theorem / 15 statement lets. Base probability mu; same compact Theta inside true quadratic-MGF interior; actual pointwise tilted covariance determinant positive. Uniform lo/hi spectrum is a conclusion, never an added premise. Same explicit A/covariance and returned E with exact action/inverse bounds, same M and explicit positive Cstar before p/n/cell. Actual half-open grid intersect closed physical parabola window; closed rectangle anchor retained; all n>=2, h=log(n)/n^3; genuine averaged Gaussian oscillation Integrable and <= Cstar*log(n)/(n^3*sqrt(n)). EmptyTheta/degenerate cells/rho0/totallevel0 remain legal pure geometry.

Dependencies: qualified BR151 actual covariance spectrum and exact GM276 log-cubic family (machine passed, sole independent finalreview currently RUNNING; must qualify before first native consumption). BS152 qualified89LF source is proof-composition template only, not new direct dependency. Source-bound original repair01 small-cell passage; strict beta<2/5, p54 correction and Song s=8 external attribution retained. Original h=n^-3/log(n) differs from repaired epsilon=log(n)/n^3 by log²; new conclusion is explicit. No desired-error/coherence premise, canonical full-frequency error, sample-law comparison, weighted desmoothing, reconstruction, exterior, B-D or positiveOQ3 root completion.

## Complete frozen declaration

```lean
theorem compact_open_domain_parabola_log_cubic_gaussian_oscillation
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : ∀ p ∈ Theta, 0 < (parabolaCovariance
      (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det)
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
    let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      (∀ p ∈ Theta, ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ∧
        xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2)) ∧
    ∃ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
      (∀ p : Theta, A p * D p * A p = 1 ∧
        (∀ w : ℝ × ℝ, E p w =
          (A p 0 0 * w.1 + A p 0 1 * w.2, A p 1 0 * w.1 + A p 1 1 * w.2)) ∧
        ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
        ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 4 * hi * (1 / Real.sqrt lo)) ∧
      ∃ M : ℝ, 0 < M ∧ (∀ p : Theta, ‖(p : ℝ × ℝ)‖ ≤ M) ∧
        let U : ℝ := 1 / Real.sqrt lo
        let R0 : ℝ := 2 * U
        let kappa0 : ℝ := (2 * M) * (4 * hi * U)
        let G0 : ℝ := R0 * (1 + 2 * (|a0| + rho) / level ^ 2)
        let Cstar : ℝ := Real.exp (kappa0 * R0) *
          (8 * kappa0 * (R0 + 1) ^ 2 + 768 * (G0 + 1))
        0 < Cstar ∧
        ∀ (p : Theta) (n : ℕ), 2 ≤ n → ∀ (y : ℝ × ℝ) (aL aR qL qR : ℝ),
          y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR →
          aR - aL ≤ 1 / (n : ℝ) → qR - qL ≤ 1 / (n : ℝ) →
          let h : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
          let cellA : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
            {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
              0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
          let stdCell : Set (ℝ × ℝ) :=
            (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E p (w - y)) '' cellA
          let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
            ((p : ℝ × ℝ).1 * ((E p).symm v).1 +
              (p : ℝ × ℝ).2 * ((E p).symm v).2))
          let Φ : Measure (ℝ × ℝ) :=
            (gaussianReal 0 1).prod (gaussianReal 0 1)
          Integrable (openBallOscillation (stdCell.indicator g) h) Φ ∧
            (∫ z, openBallOscillation (stdCell.indicator g) h z ∂Φ) ≤
              Cstar * Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))
```
