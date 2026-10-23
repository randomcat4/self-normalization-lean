# OQ3 unit153 BT — SAME physical-window uniform Gaussian cell family
Exact declaration/all statement local values frozen BEFORE implementation. Module Shao.OQ3.PhysicalWindowUniformGaussianCells; imports Shao.OQ3.PhysicalWindowCompactTiltParameters and Shao.OQ3.CompactOpenDomainGaussianOscillation; namespace Shao.OQ3; open MeasureTheory ProbabilityTheory; scoped Matrix Topology ContDiff; noncomputable section. One public theorem, zero definitions.

This is the actual source producer coupling, not an arbitrary supplied compactfamily. From the SAME original actualtheta/MGFinterior/actualcenterpositivecovdet/physicallevel,a0/negativequadratictilt/exactactualmean/saddle inputs as BQ, construct the SAME L/e and conditional SAME rho/V/Theta=e.symm''V. Add the COMPLETE actualGaussian packet from BS on exactly this Theta. Retain EVERY BQ physicalwindow/chart/trueglobalERealI=J/allclosureanchors/minI+minJ conclusion verbatim with samewitnesses. Lambda1>0 remains explicit. No samplelawEdgeworth/reconstruction/exterior closure or boundedsupport addition.

```lean
theorem open_domain_physical_window_uniform_gaussian_cells
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

Added parenthesized packet is EXACT BS fullconclusion including all nested lets tilt/D/s/t/A/U/R0/kappa0/G0/Cstar/h/cellA/stdCell/g/Phi. Shadowing names D/U/A is localinsideparentheses and never changes outer covariance/chart/window/cellanchor objects. Spectral lo/hi, canonicalEfamily and commonM/Cstar are actual CONCLUSIONS, with independentp/n/anycell/anyoriginalclosedrectangleanchor quantifiers. Existing BQ Theta compact/subsettrueOmega/pointwiseactualdetpositive directly discharge BS premises. Exactsame V as BS literalcell ensures originalanchors allowed.

Qualified BQ source1d654378f3d71e5c1ac01e082361b11edb689732cb299a73653f6c4b7e045fcc, independentu22bq-proof-review.md SHA5c11e7c36176ca5ab2010493ead9afe111bfa74f664a84a29604520e6801b787 all116source/88actualtype/allvalues, full83linesparentread; completeconsumedpublicdeclaration/all18statementletvaluesnowreadagain. BSsourcea80f3e07d8c35bf5e31195f035970229cc7c798214c627bb949d82ac1c9ab076/89lines1actual firstkernel/AXPASS, fullactualtype/allvaluesread; BRfreshreviewactive andBSfreshreviewQUEUED, neitherclaimedqualifiedbeforeindependentfinal. MustqualifyBRthenBSbeforeBTacceptance. Oldqualifiedproofs/checks reused, no replay.

OnlyserverCPU14–17/native-M8192-j4/autoImplicitfalse/oneheavy; solechildlease1 serialfreshNONAUTHOR fullnewsource/types/ALLvalues/allownedrecursiveAX review std3 whitelist. No localLean/cache/package/sharededit, no math-ultra/newsidebar/crossmessages. No sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings; preservefirstfailures/warnings andexactfirstPASS. No passedchecksreplay/cosmeticPASSedits. PR2100b64fc frozen rootintake and branchfeat/oq3-covariance-cell-family; no merge/rebase. OriginalB/D actualsampleEdgeworth/reconstruction/exterior remainOPEN; correctedfixedlawA/boundedcompactC,p54andexternalattribution unchanged.
