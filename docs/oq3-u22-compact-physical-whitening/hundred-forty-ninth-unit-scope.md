# OQ3 U22BP / unit149 — frozen actual canonical-family uniform Gaussian ncube bound

FROZEN before source. math-theorem/no math-ultra. One public theorem/zero globaldefinitions; all NEW source/proof/fullactualownedtypes/allvalues freshfullreview+recursive actualowner whitelist3AX mandatory. Serveronly CPU14–17/max1/native8192MiB/j4/autoImplicitfalse/pins/read-onlycache unchanged.

Source-bound purpose: actual closedcell Gaussian meanoscillation at h=n^-3 is qualified percell (BH141), but its coefficient contains theta and E norms. BN/BO construct the actual canonical covariance pair family with explicit uniform forward/inverse maxnorm bounds under the retained actual uniform covariance spectral premise. This unit must derive ONE explicit positive Gaussian coefficient for ALL actual family members, n>=1 and literal width<=1/n cells, using compactness to bound actual tilt coordinates. It may not assume the desired Gaussian expectation, coefficient or actual E norms.

Exact imports: Shao.OQ3.ParabolaPairWhiteningFamily; Shao.OQ3.ParabolaCellNcubeOscillation; Mathlib.Analysis.Normed.Group.Bounded. Last primary object observedcached; primary Bornology.IsBounded.exists_pos_norm_le at Bounded:76–78 read (positive common normbound from actual compactness).
BO source9c48fd8a9434a7c28cb9761358f93255fb0dcf0d836093fc2a0c10afd8d65fdc/66lines1actual kernel/AXPASS, freshfullreviewactive; mustqualify before accepted BP. BH sourcef09f00ce6cc6a0e357b0a039022fb3e3148985e57f7bdaad18c7af2c3013f16f/56lines1actual, qualifiedBGBHreport e6330b315e50ebd562a300fa48d0b91be95541ea5d4262fcaf212840f5cdfbab all202parentread and frozenPR210. Its ENTIRE consumed declaration including h/A/B/g/kappa/R/C/G/Phi and exactdenominator was fully read before this freeze. Oldproof/checkreused; allNEWproof/types/values fully reviewed.

Full exact declaration and ALL statement local values:
```lean
theorem compact_parabola_pair_ncube_gaussian_oscillation
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hspec : ∀ p ∈ Theta,
      let D : Matrix (Fin 2) (Fin 2) ℝ :=
        parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
      ∀ xi eta : ℝ,
        lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2))
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
    let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
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

The actual mu/tilt/D/s/t/A values and universal actual covariance hspec premise are preserved. hcompact is actual compactness of Theta, including emptyTheta. lo,hi>0 explicit. This unit does not derive hspec or identify a compact analytic chart. It chooses genuine BO E for each subtype p, proves exact canonical row action and A D A=I and uniform maxnorm bounds; no continuity/measurability of p↦E asserted. M>0 bounds actual maxnorm theta over Theta from compactness, not a supplied arbitrary envelope.

U=1/sqrtlo, R0=2U, kappa0=(2M)*(4hiU), G0=R0*(1+2(|a0|+rho)/level²) and Cstar=exp(kappa0*R0)*(8kappa0*(R0+1)²+768*(G0+1)) are exact explicitvalues. Cstar depends only on fixed Theta/lo/hi/physicalwindow parameters and is independent of p,n,cell endpoints,y. Its strict positivity must be proved.

Every physical cell remains literal Ioc×Ioc intersect CLOSEDwindow with both weak parabolic walls. Allreal level/a0/rho, with rho>=0, n>=1; level0 totaldivision allowed pureGaussiangeometry, not positivephysicaltail identification. Anchor y belongs to original CLOSED rectangle, no desiredminimum/support/tubebound assumed. h is literally1/n³; standardizedimage uses sqrt(n)*actualE(p)*(w-y); g uses actual inverseE(p) and actualtiltcoordinatep; Phi is actualproductstandardGaussian. Integrability and expectation bound are proved for the actual openBallOscillation of the literal indicator, not an essential/a.e. envelope or samplelaw assumption. No boundaryatom is dropped. ActualGaussianresult only.

Proof route: BO supplies actual E and uniform normbounds. Actual compactness supplies M>0 forallp normp<=M; productmaxnorm bounds each |pcoordinate|<=M. Thus actualkappa<=kappa0, actualR<=R0 and actualG<=G0 using nonnegative common physical factor. Monotonicity of squaring on nonnegative R+1, realexp and nonnegative products gives the entire actual BH coefficient<=Cstar; prove Cstar>0. Apply BH unchanged at eachp/n/y/rectangle and compare over positive actualn³sqrt(n). No desiredmeanbound/integrability/coefficient assumption or oldgate replay.

OPEN: deriving actual uniform spectrum and compact true analytic anchorchart in the original unbounded-law scope; actual sample Edgeworth, exact weighted probabilityreconstruction/cell summation, full exterior and original B/D. FixedlawA/boundedcompacttiltC, p54/strictWC/externalSong-AngstPoly attribution unchanged. No sampleprobability or rootclosure/novelty claim.
