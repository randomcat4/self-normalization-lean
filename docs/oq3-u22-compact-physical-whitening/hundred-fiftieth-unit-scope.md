# OQ3 U22BQ / unit150 — frozen actual compact inverse-mean tilt parameter window

FROZEN before implementation. math-theorem/no math-ultra. One public theorem, zero global definitions. Fresh full review of ALLNEWproof/types/statement and proofvalues+recursiveactualowner white3AX required. AllLean/heavyserverCPU14–17/max1/native8192MiB/j4/autoImplicitfalse, pins/read-onlycache unchanged.

Source-bound purpose: BL145 supplies finite true analytic rate closureanchors in one actual physical window/chart, but actual-family Gaussian BP149 needs a compact tilt parameter set. A separately selected old closed-ball chart need not be the SAME chart/window. This unit must construct Theta=e.symm''V from the SAME actual BL L/e/rho/V, prove it compact, contained in the true MGF-domain interior, containing the actual center theta, and carrying the inherited positive actual covariance. It retains EVERY BL window and cell-anchor conclusion for the SAME witnesses; no arbitrary compactchart or spectrum premise is introduced.

Exact import: Shao.OQ3.PhysicalWindowCellRateAnchors. BL source dcc7e3c5d2b881403791abfe37c952b08eee3eda071f1818382c33cd33051b09, qualifiedreport9817b85d0c069cbf595409b4c2be3abaf1a3523d1cf2888c5b97f880b44e3c7d full114linesparentread; entire actualtype76lines incl17letvalues/fullchart/window/anchor scope is the consumed interface. Existing PR210 frozen0b64fc contains this exactsource; oldproof/kernel/AX reused. EveryNEWproof/value reviewed.
Intrinsic inverse-chart continuity is OpenPartialHomeomorph.continuousOn_symm restricted to actual V⊆e.target. IsCompact.image_of_continuousOn gives actualimage compactness. These pinned API calls were observed in qualified OpenDomainCompactMeanChart lines55–57 solely as API spelling, not another oldproof review or reuse of its separate existential chart.

Exact complete declaration including ALL statement local values:
```lean
theorem open_domain_physical_window_compact_tilt_parameters
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

All actual theta/open-MGF/center determinant/positive level,a0/negative theta2/actualmoment/saddle hypotheses and conditional actualLambda1>0 remain unchanged. The new Theta is EXACT image of literal closed physical V under the SAME e.symm. It is not supplied, replaced by a larger arbitrary set, or taken from a different existing chart. Both positivecenter/thetacompactmembership and everypoint covariance positivity are actualproduced facts. Its positive determinant claim is not yet a uniform lower eigenvalue bound.

Proof route: consume BL with exactunchangedpremises and preserve L/e and conditional branch. Take its rho>0, Vcompact, Vsubsete.target and pointwise inverse/source/Omega/mean/covariance/rate facts. Restrict intrinsic inversecontinuity to V and take compactimage. Image witnesses prove Theta⊆Omega and each p∈Theta lies in e.source, has means(p)∈V and positive actualcovariance determinant. Actualcenter w0=(a0,a0²/level²) lies in literalV; he+hmean identify e(theta)=w0 and chartleftinverse gives e.symm(w0)=theta, hence theta∈Theta. EveryVpoint inverse lies inTheta by definition. Pass ALL original Vphysicalidentity/compactness/pointwisefiniteRate and EVERYcell closureanchor/trueI+realJ minima through unchanged for SAMErho/e.

OPEN: deriving actual uniform covariance spectral bounds on this produced compactTheta from open-domain momentcontinuity/positive covariance; coupling BP149 to these actualwitnesses, actualsampleEdgeworth, weighted probabilityreconstruction/cellsummation, full exterior/originalB-D. Existing fixedlawA/boundedcompacttiltC/p54/strictWC/externalattribution unchanged. No fullrootclosure or novelty claim.
