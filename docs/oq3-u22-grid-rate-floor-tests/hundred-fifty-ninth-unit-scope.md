# OQ3 unit159 BZ — actual same-chart rate-floor physical window and rebuilt anchors

Exact complete declaration and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.PhysicalWindowRateFloorAnchors. Imports ONLY Shao.OQ3.PhysicalWindowCellRateAnchors and Shao.OQ3.PhysicalWindowRateFloor. Namespace Shao.OQ3, open MeasureTheory, scoped Matrix Topology ContDiff, noncomputable section. One public theorem, zero definitions.

Source-bound target: original probability mu/theta in TRUE open MGF domain, positive actual covariance determinant, level/a0 positive, negative theta2, exact actual tilted mean and saddle equality. No bounded-support or assumed rate-floor premise. Select actual BL L/e and original cap window. Independently invoke qualified T actual boundary producer; its L equals the SAME actual BL L because both have the complete actual covariance-row continuous-linear-map value. This transports the EXACT Lambda1 positivity; no arbitrary derivative or replacement assumption. T's inverse chart need not equal BL's inverse chart: compare both through the TRUE global EReal Legendre rate using BY.

For conditional actual Lambda1>0, expose cap>0 and explicit new rho>0<=cap. The returned literal closed physical V, U, compact Theta=e.symm''V, pointwise inverse/domain/actualmeans/covdet/finite I=J, ALL original closed-cell closure minima, and added J(center)<=J(w) are ALL about this NEW rho and SAME chosen BL e. Rebuild compact V/Theta and new closure anchors from BI, not old cap-cell minimizers. V=U∩Tail is proved at new rho using subset cap and actual positivity. Gaussian or Laplace integral estimates on new rho NOT claimed or silently transferred. They require proper later application.

```lean
theorem open_domain_physical_window_rate_floor_anchors
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

Every statement let value appears in full above, including actual Omega/nu/means/covariance rows/K/J/v/Lambda1/U/Tail/V/Theta/A/Q. cap is the original BL radius in proof; rho is the explicit shrink delivered by BY's actual rate identity+growth bridge. No conditional hLambda removed. T eventual identity and genuine positive c growth are derived outputs, not new assumptions.

Qualified consumed old interfaces/all values/source bindings: BL PhysicalWindowCellRateAnchors source dcc7e3c5d2b881403791abfe37c952b08eee3eda071f1818382c33cd33051b09 report9817b85d0c069cbf595409b4c2be3abaf1a3523d1cf2888c5b97f880b44e3c7d; T OpenDomainBoundaryLowerBound426d3b0713595bea5fbb4205b550f2e20e6a7f9f4aea1c555bd847cdb060dcc4 report9dd3afba4c9d742aea2c2772c014a679c7caa022179e2df3c50ff27ec006b205; BI ParabolaCellRateAnchora6c6546788a6069c38bdc7545cc670252734236f67aa7c9e0892f0924de5842e report615f58cc598db96cfc2408971b046219bb493e1c39d75acf29f1aac50ae2b50e; BK ParabolaFiniteGridCoverb9303194ada7248223e0b98947d71db21a66117c0ee07cba563e31c2d8b87178 report00ea72556d773f38448f49c169f2c8c20251a4c08d7b796ba91b8eaa99871a99. Old proofs/checks reused, no replay. BY158 source7e76ddd24536a713098341d2829077ff312296fac37da25bca41a7a573d98c7e receipt8e38643d98d17e162a276c589435cb9452b4676a724fe314a94f7dc6e09e6454 firstPASS all3actual standard3; fresh NONAUTHOR full review ACTIVE at freeze; BZ cannot qualify unless dependency review qualifies.

Rootv59 mainb6bdf7333a514f9f908c838ddd0161b5617e422e receipt30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc checkedcode29c9804c552f0cc494355e6556c112aa3c36c908/tree3105ddcd9ee08c67da77f150f9392e140061a98c; notice427library sources; acceptedhead not supplied. Active continuation feat/oq3-weighted-grid-reconstruction headfd718003; PR217 frozen root intake, no merge/rebase/old check replay. Server CPU14–17/max1heavy/native -M8192 -j4 autoImplicit=false; no local Lean/shared caches or packages write. Sole independent child lease1. All actual module-owned declarations INCLUDING generated/external-namespace owners and values require fresh full semantic/proof review and recursive standard3 axiom audit. No sorry/admit/new axiom/unsafe/native_decide/implemented_by or weakened settings. No math-ultra/new sidebar/cross-thread message.

Partial actual window-floor/anchor producer not root proof: weighted quantitative error, actual Song Edgeworth formal proof/exterior, original B/D OPEN. Corrected fixed-law A/bounded compact-tilt C, p54 repairs/strict WC threshold/external attribution unchanged. Keep first PASS exact; preserve failures/warnings.
