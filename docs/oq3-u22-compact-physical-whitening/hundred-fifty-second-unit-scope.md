# OQ3 unit152 BS — actual compact-open Gaussian cell oscillation
Exact full declaration/all statement values frozen BEFORE implementation. Module Shao.OQ3.CompactOpenDomainGaussianOscillation; imports Shao.OQ3.CompactOpenDomainCovarianceSpectrum and Shao.OQ3.CompactParabolaGaussianOscillation. Namespace Shao.OQ3; open MeasureTheory ProbabilityTheory; scoped Matrix Topology; noncomputable section. One public theorem, zero definitions.

Source role: original repair01.md compact tilted cell oscillation bound. Discharge BP149's explicit uniform covariance spectrum premise with BR151 ACTUALcompact TRUEopen covariance producer. Preserve ALL literal half-open physical cells, original CLOSED rectangle anchors, actualcanonical whitening family, TRUE productGaussian, actual weights/integrability and common positive Cstar independentp/n/cell/y. New inputs only compactTheta subsettrueMGFinterior plus pointwise actualcovdetpositive. No boundedsupport or samplelaw/Edgeworth premise. Pure geometrylevel0permitted as BP; actualphysical producer suppliespositivelevelseparately.

```lean
theorem compact_open_domain_parabola_ncube_gaussian_oscillation
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
        ∀ (p : Theta) (n : ℕ), 1 ≤ n → ∀ (y : ℝ × ℝ) (aL aR qL qR : ℝ),
          y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR →
          aR - aL ≤ 1 / (n : ℝ) → qR - qL ≤ 1 / (n : ℝ) →
          let h : ℝ := 1 / (n : ℝ) ^ 3
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
              Cstar / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))
```

All let-values tilt,D,s,t,A,U,R0,kappa0,G0,Cstar,h,cellA,stdCell,g,Phi are literal BP values. lo/hi>0 and actualall-direction spectralbounds are CONCLUSIONS. BRsourcec54c920af77b529a30f737b22232cadafa221cee708f11d1e19d118a1ba313a4 (116lines2actual, firstkernel+AXPASS independentfreshfullreviewRUNNING; qualificationmustfinishbeforeBSacceptance), actualcovariancequantityorderconverted by commutativerealalgebra ONLY; no silent premise change. QualifiedBP source dcd06857e360cab10992139afe5a68b335f66eeeb47f9c4db6f004a42e653472, report18485d507e8cf9f36b2be5f5d2e0ddaa93144bc937ba7dec72bc24f63b6bcf79 full91linesalreadyparentread; consumedcomplete59line actualtype37696fafa2ce3490b3598c1bf11541fce15a353885b7913c6ded4567011350ca andALL statement let-values nowreread. Reuse old qualified proofs/checks without replay.

Only designatedserver CPU14–17/native-M8192-j4/autoImplicitfalse/oneheavy lane; no localLean/cache/package/root/sharedwrites. No sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakensettings. Fresh independentNONAUTHOR allNEWsource/fulltypes/ALLvalues/fullproof/allactualownertransitiveAX whiteliststd3 mandatory; waitsolechildBRfinishedbeforenewBSreview. Preserve firstfailures/warnings and exactfirstPASSsource. No passedgate replay. PR2100b64fc frozen rootintaking; activefeat/oq3-covariance-cell-family; no merge/rebase. ActualBQsamephysicalwitnesscoupling, sampleEdgeworth/reconstruction/exterior and originalB/D OPEN; AandboundedCscopeunchanged.
