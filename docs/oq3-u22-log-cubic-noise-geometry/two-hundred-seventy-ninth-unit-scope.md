# GP279: same physical window/chart/anchors with log-cubic Gaussian cells

Frozen before implementation at 2026-10-27T23:00:47.589413+00:00. Module Shao.OQ3.PhysicalWindowLogCubicGaussianCells. One full theorem / 33 statement lets. Reuse qualified BT153 actual L/e/rho physical witnesses, preserving every original source/domain/actualmean/rate/globalLegendre/closureminimizer/closed-anchor field. Retain original positivelevel/a0/negative secondtilt/actualmean/saddle assumptions and explicit Lambda1>0 implication, no implicit Lambda1positivity proof. Replace only old Gaussian ncube packet with GN277 complete new log-cubic packet on SAME Theta=e.symm image V. New E is bound by the exact same covariance A row action; no coherence input or free whitening substitution. Same allphysicalcells/closedanchors. Explicit n>=2/h=log(n)/n^3/Cstar*log(n)/(n^3sqrt n). Uniform spectrum in conclusion, actual openMGF/pointwisedet producers used.

BT153 full111LF combinedBSBT qualifiedreview and actual140LFsource/154LFTYPE ENTIRE parentread. GN277 firstnative/sameO machinePASS; complete independentreview pending, no GP native untilGNqualified. No full samplelaw approximation, weighteddesmoothing, reconstruction/summation, exterior/B-D/root claim; strictbeta<2/5/p54corr/Songuniforms8 attribution retained. Originalwidth differslog², not silent protocol replacement.

## Complete frozen declaration

```lean
theorem open_domain_physical_window_log_cubic_gaussian_cells
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
      let v : ℝ × ℝ := (1, 2 * a0 / level ^ 2)
      let Lambda1 : ℝ := 2 * theta.2 / level ^ 2 +
        (L.symm v).1 + (2 * a0 / level ^ 2) * (L.symm v).2
      0 < -theta.2 ∧ (0 < Lambda1 → ∃ rho : ℝ, 0 < rho ∧
        let U : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
          |w.1 ^ 2 / level ^ 2 - w.2| ≤ rho}
        let Tail : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ level * Real.sqrt w.2 ≤ w.1}
        let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
          0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
        let Theta : Set (ℝ × ℝ) := e.symm '' V
        (
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
        ) ∧
        IsCompact Theta ∧ theta ∈ Theta ∧ Theta ⊆ Omega ∧
        (∀ p ∈ Theta, p ∈ e.source ∧ means p ∈ V ∧
          0 < (parabolaCovariance (nu p)).det) ∧
        (∀ w ∈ V, e.symm w ∈ Theta) ∧
        V = U ∩ Tail ∧ IsCompact V ∧
        (∀ w ∈ V, 0 < w.1 ∧ 0 < w.2 ∧ w ∈ e.target ∧ e.symm w ∈ e.source ∧
          e.symm w ∈ Omega ∧ means (e.symm w) = w ∧
          0 < (parabolaCovariance (nu (e.symm w))).det ∧
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
            (J w : EReal)) ∧
        ∀ aL aR qL qR : ℝ,
          let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
          let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
          A.Nonempty →
          ∃ y ∈ closure A, y ∈ Q ∩ V ∧
            0 < y.1 ∧ 0 < y.2 ∧ y ∈ e.target ∧ e.symm y ∈ e.source ∧
            e.symm y ∈ Omega ∧ means (e.symm y) = y ∧
            0 < (parabolaCovariance (nu (e.symm y))).det ∧
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y =
              (J y : EReal) ∧
            ∀ w ∈ closure A,
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
                Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w ∧
              J y ≤ J w)
```
