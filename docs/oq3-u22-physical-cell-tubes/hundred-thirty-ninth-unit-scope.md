# OQ3 U22BF / unit139 — frozen actual standardized physical-cell frontier tube

FROZEN before implementation. math-theorem/no math-ultra. OQ3 lead author, independent complete source-to-statement/proof/every actual owned full type/every global-local value and actual module-owner recursive standard3 axiom audit mandatory. One public theorem, no global definitions.

Source-bound integration: original repair01's normalized-cell Gaussian boundary tube estimate, for the ACTUAL AL physical closed window intersected with exact disjoint-grid Ioc rectangle. AZ/BA construct its actual six-arc geometry; BB derives finite-arc Gaussian tubes; BC/BD prove actual uniform scaled arc Lipschitz constants; BE transports frontier using the actual normalization homeomorphism. This unit must consume these producers and derive a true Gaussian bound, not assume the boundary-probability estimate or cover.

Exact imports planned: Shao.OQ3.ParabolaCellArcs; Shao.OQ3.GaussianFiniteArcTube; Shao.OQ3.StandardizedParabolaArcs; Shao.OQ3.StandardizedFrontierTransport. Existing source/object hashes and independent qualification reused. BA source0dc6e551015bdf4390d1fcd456340728e11870af59cfb6313c968d17c2b3a14b and reportc10a8a6ba2878f4f8e4729b7783f1228f1a1cfc7548ecc7164702cb0f433c8dd; BB sourcedf527270c1099d5fe7176d0295a0cc703bf3c4f81d706af58012d00c7109dcd4/report101b20bea6e727678dfab495fd4b4c54696742efa9474efaec64a2f946de47d7 qualified. BC/BD sources073096f20f40f6a605ce1da8ca9559de9a324abe2ed6ae8273da2553d3275cf0/ac1ef1f8204eb80fcf27cfabcc83fe51ad5164ae9d1035cdf7bb03aadf34959e author kernel/AXPASS and combined fresh full reviewrunning. BE source7f685dcdca14e32e6aa051f7bf1764b54351cfbbdbf9ba1a2ecbde40dafe7383 authorfirstPASS andreviewpending. No BF qualification until every direct dependency has independent complete qualification; no accepted gate replay.

Exact complete declaration, including ALL statement local values:
```lean
theorem actual_standardized_parabola_cell_frontier_tube_bound
    (n : ℕ) (hn : 1 ≤ n) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (hawidth : aR - aL ≤ 1 / (n : ℝ)) (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    (h : ℝ) (hh : 0 < h) :
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let B : Set (ℝ × ℝ) :=
      (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A
    let C : ℝ := ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ *
      (1 + 2 * (|a0| + rho) / level ^ 2)
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real (Metric.cthickening h (frontier B)) ≤
        384 * (C * h / Real.sqrt (n : ℝ) + h ^ 2)
```

Universally quantify all displayed arguments. n>=1, rho>=0, two grid width upper bounds and h>0 are the ONLY scalar hypotheses. E a genuine continuous linear equivalence, y arbitrary; E is not claimed actual covariance whitening. NO assumption A nonempty, clipped interval ordered, qL<=qR, frontier covered, curves Lipschitz, or desired Gaussian tube probability. Handle empty/reversed cells separately. For nonempty A, derive the orderings from an actual witness in the original Ioc cell and closed physical window. Exact half-open rectangle and BOTH weak parabolic inequalities retained; no Ioc L R replacement or boundary-atom deletion. Pure geometry permits all real level with total division; original physical probability consumers retain positive-level/domain premises.

Actual proof-local curve values are frozen here (same exact BA and BD curves):
```lean
let L : ℝ := max aL (a0 - rho)
let R : ℝ := min aR (a0 + rho)
let curve : Fin 6 → ℝ → ℝ × ℝ := ![
  (fun t => (L + t * (R - L), qL)),
  (fun t => (L + t * (R - L), qR)),
  (fun t => (L, qL + t * (qR - qL))),
  (fun t => (R, qL + t * (qR - qL))),
  (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2)),
  (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - rho))]
```

Further permitted local abbreviations: Φ is exactly the displayed Gaussian product; K=Real.toNNReal(C/Real.sqrt(n:Real)); scaled_i(t)=Real.sqrt(n:Real)•E(curve_i(t)-y). No renamed probability hypothesis. Prove compact geometric cover using BA, transport frontier with BE, feed actual scaled Lipschitz constants from BD and BB, simplify all6 equal constants to 384. At A=empty derive B=empty/frontier empty/tube empty and show explicit nonnegative right side. Arbitrary y allowed; no minimizing anchor property used. Norm on ℝ×ℝ remains the existing maximum norm.

The coefficient normE*(1+2*(abs(a0)+rho)/level²) is explicit. Family-uniform whitening/level/window control remains a separate obligation; this is not silently a covariance-normalization result. h=n^-3 substitution, combination with actual Gaussian oscillation, actual Edgeworth/sample-law comparison, exact partition/valid rate-anchor/exterior and originalB/D remain OPEN. Accepted fixed-lawA and boundedcompacttiltC scopes retained, all p54/strictWC/external-attribution conditions unchanged. No silent assumption/declaration/value edits.

