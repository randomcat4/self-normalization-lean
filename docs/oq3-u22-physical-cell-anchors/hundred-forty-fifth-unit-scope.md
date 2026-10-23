# OQ3 U22BL / unit145 — frozen actual finite analytic-rate closure anchors

FROZEN before source. math-theorem/no math-ultra; one public theorem, zero global definitions. Mandatory fresh independent all-new source/proofs/each actual-owned complete type/everylocalvalue review, actualowner recursive standard3 AX. Server-only CPU14–17/max1/native8192MiB/j4/autoImplicitfalse and pinned read-only package rules unchanged.

Source-bound purpose: r2/report section3 chooses rate-minimizing half-open cell anchors; the explicit anchor note repairs nonattainment by closure. BI142 proved generic compact-closure attainment for the true global EReal rate, but that alone allowed infinite rates/unidentified parameter charts. This unit must obtain its SAME actual chart/window directly from the qualified AL119 physical-window producer, and then prove EVERY nonempty actual half-open rectangle intersected with that actual window has a finite-rate closure anchor in the genuine inverse-mean chart. No assumed desired rate identity, supplied minimizing point or proxy-rate premise.

Exact imports: Shao.OQ3.OpenDomainBoundaryLaplacePhysicalWindow; Shao.OQ3.ParabolaCellRateAnchor; Shao.OQ3.ParabolaFiniteGridCover.
Qualified AL source454756d46f915ab48e6967573696582eedc4239ff22504f015ca036a1ea26629, allowned type u22al-actual-types.txt fully read, exact local/rootv54 mapping verified; qualified AK/AL reporte1a5e43dfcf786636658c0a8e0e654666c8dfbda821e70d0944281e618d4f411 scope/status checked, oldproof reused.
BI sourcea6c6546788a6069c38bdc7545cc670252734236f67aa7c9e0892f0924de5842e; report615f58cc598db96cfc2408971b046219bb493e1c39d75acf29f1aac50ae2b50e all105lines parentread qualified.
BK sourceb9303194ada7248223e0b98947d71db21a66117c0ee07cba563e31c2d8b87178 firstkernel/AXPASS; independent review active, final qualification must precede accepted BL. Only consumed old full declarations/definitionvalues+hash/qualification/scope checked; no oldproof/gate replay. Every NEW proof/type/value here fully reviewed. Primary EReal.coe_le_coe_iff at Data/EReal/Basic:55 preserves real order on finite casts.

Complete exact declaration and all statement local values:
```lean
theorem open_domain_physical_window_cell_rate_anchors
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

All original actual theta/interior-MGF, actual center determinant, positive level/a0, negative theta2, exact physical mean and saddle relation hypotheses remain explicit. L is the genuine derivative row-map and e the genuine mean-map chart, rather than a supplied arbitrary rate/whitening map. The conditional actual tangential positivity 0<Lambda1 is retained exactly; it is not proved or removed. Lambda1 uses this same L and physical tangent v. No C0/Laplace-asymptotic conclusion is asserted by this helper.

The selected rho is produced by AL with a genuine two-sided U and actual physical Tail; the literal V is proved equal to U∩Tail via AL's exact strip equation and elementary inequality rearrangement. V compactness comes from BK. Every point of V has positive first/second coordinates and lies on the SAME inverse-mean chart with positive actual covariance determinant and finite real J equal to the TRUE GLOBAL EReal Legendre rate. All quantification over cells is inside the selected rho/chart, for arbitrary real rectangle endpoints, no width or nonemptywindow premise. Actual A is literal Ioc×Ioc∩V; Q is original closed rectangle. Empty A makes only its implication vacuous.

Proof route: consume actual AL producer, preserve L/e equalities and source interior facts, and apply its conditional Lambda1 branch to select rho. Convert its exact closed physical strip to the literal nonnegative-gap V. Transfer positivity/chart/true-rate identity pointwise. For each nonempty actual A, apply qualified BI to produce y in closure A∩Q∩V minimizing actual EReal rate. BK compact V is closed and contains A, hence contains closure A; apply the pointwise finite-rate identity to y and every w in closure A. EReal.coe_le_coe_iff converts the already established true-rate minimum to the finite real analytic J minimum. Anchor need not be a member of the half-open A. All proof-local window/function values must repeat the frozen ones exactly; unused AL Laplace output is simply not claimed.

OPEN: quantitative O(n²) cell cardinality, uniform true covariance whitening and parameter-family constants, actual-sample Edgeworth, weighted exact probability reconstruction/cell summation and full exterior control. This finite analytic-anchor producer alone does not prove original B or D. Corrected fixed-law A and bounded compact-tilt C, all p54/strictWC/external attribution scopes preserved. No silent premise/value changes.
