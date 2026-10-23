# OQ3 unit160 CA — same new floor window with freshly applied Gaussian oscillation

Exact complete declaration and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.PhysicalWindowRateFloorGaussianCells. Imports ONLY Shao.OQ3.PhysicalWindowRateFloorAnchors and Shao.OQ3.CompactOpenDomainGaussianOscillation. Namespace Shao.OQ3; open MeasureTheory ProbabilityTheory; scoped Matrix Topology ContDiff; noncomputable section. One public theorem, zero definitions.

Source critical integration: apply qualified BS directly to NEW BZ compact Theta=e.symm''V and SAME NEW rho returned by explicit cap/rho<=cap shrink; never transfer old BT Gaussian cell estimate on old cap. Retain the entire actual BZ L/e/Lambda, explicit radius shrink, pointwise true rate and common J floor, rebuilt closure anchors. Common actual spectra, canonical E family, positive common M/Cstar and actual product-Gaussian integrable oscillation at h=n^-3 are rederived conclusions for that SAME Theta/rho. No additional spectrum, bounded-support or desired-error premise. Uniform actual tilt weak-Cramer/actual Edgeworth NOT provided by Gaussian geometry and not silently inferred.

```lean
theorem open_domain_physical_window_rate_floor_gaussian_cells
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
      0 < -theta.2 ∧ (0 < Lambda1 → ∃ cap rho : ℝ, 0 < cap ∧ 0 < rho ∧ rho ≤ cap ∧
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
        (∀ w ∈ V, J (a0, a0 ^ 2 / level ^ 2) ≤ J w) ∧
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

All full actual let values are above: Omega/nu/means/D/pr0/pr1/row0/row1/K/J/v/Lambda1/U/Tail/V/Theta; inside parenthesized Gaussian packet actualtilt/parameterizedD/s/t/canonicalA plus U=1/sqrtlo/R0/kappa0/G0/Cstar/h/literalcellA/stdCell/g/Phi. Parentheses keep local D/U/A shadowing confined to Gaussian packet. Rate/anchor A is original literal physical halfopen-cell intersection. E is an actual continuous-linear equivalence over newTheta, canonical action and forward/inverse norm bounds included. No assertion of family continuity not supplied by source.

BZ159 source ecf1a792e3e0b6bd224067c9ebb48079c16691f1be11f1a1a98194a2b5308b6d receipt957d9172161177acd3b265f2cd409ba16474c06800c017cdb3895b671c1f36ae firstcompletekernelattempt2/oneactualstd3; fresh NONAUTHOR full review ACTIVE at freeze; CA cannot qualify until BZ review is qualified. Old qualified BS sourcea80f3e07d8c35bf5e31195f035970229cc7c798214c627bb949d82ac1c9ab076; reportu22bsbt-proof-review.md SHA5d058db40c45f1602fd019c4387b1487ee60700db64b6575f9916654604c4591 complete229newsource/2actualtype/allvalues CORRECT111lines parentread. Complete consumed BS interface and ALL values read, old proofs/checks reused not reread/replayed. BT interface source80ceee23b74a9faa1e693faed41f82e047337fd6b196d13f0e6f9727a36b9806 only declaration template; no BT theorem invoked/no oldphysicalradius packet transfer. BS is a qualified frozen PR217 parent dependency, source bound by its own complete review/publication receipt and exact server bytes before first kernel; rootv59 does NOT yet contain BS, so no rootv59 membership or library snapshot presence is asserted.

Rootv59 mainb6bdf7333a514f9f908c838ddd0161b5617e422e receipt30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc checkedcode29c9804c552f0cc494355e6556c112aa3c36c908/tree3105ddcd9ee08c67da77f150f9392e140061a98c; no acceptedhead supplied. Active continuation feat/oq3-weighted-grid-reconstruction PR217fd718003 frozen rootintake no merge/rebase/oldchecks. Serveronly CPU14–17/max1heavy native-M8192-j4 autoImplicitfalse. Solefreshchildlease1. No localLean/sharedcache/packagewrite/math-ultra/newsidebar/crossmessages/sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings. Preserve all firstPASS bytes, original failures/warnings; no cosmetic PASS edit or check replay. Full all-new-source/complete actual types/allvalues/actualownerincludinggenerated recursiveAX standard3 and fresh independent NONAUTHOR full review mandatory.

No newwindow Laplace bound claimed. Quantitative weighted error/actual Song Edgeworth proof/exterior and original B/D OPEN. Corrected fixed-law A/bounded compact-tilt C/p54 repairs/strict WC threshold/external-result attribution remain unchanged.

Freeze provenance repair BEFORE implementation: v1 retained as hundred-sixtieth-unit-scope-v1.md. Rootv59 source map has no BS because PR217 is still in intake; a local metadata lookup raised KeyError before any build/source implementation. Correct binding is exact qualified PR217 parent source/report/publication; declaration and ALL mathematical let values unchanged.
