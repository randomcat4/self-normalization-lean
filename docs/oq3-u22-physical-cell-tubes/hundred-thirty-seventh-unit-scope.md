# OQ3 U22BD / unit137 — frozen actual six standardized arc constants

FROZEN before implementation. OQ3 lead author, math-theorem/no math-ultra, exact fresh independent full semantic/proof/owned-type/all-values and recursive standard3 audit before qualification. One public theorem, zero global definitions. All Lean server only, CPU14–17, max1heavy, -M8192/-j4/-DautoImplicit=false, pinned Lean/mathlib/read-only packages unchanged.

This source-bound geometry unit consumes BC136 primitives and uses exactly BA134's six local curve formulas and clipping max/min endpoints. It derives a common explicit O(1/sqrt(n)) Lipschitz constant from actual grid side width bounds. It does not claim the full probability theorem, covariance normalization or a family-uniform operator bound.

Exact imports planned: Shao.OQ3.ParabolaArcLipschitz; Mathlib.Data.Fin.VecNotation; Mathlib.Tactic.FinCases. BC136 final source SHA073096f20f40f6a605ce1da8ca9559de9a324abe2ed6ae8273da2553d3275cf0 currently author kernel/recursiveAXPASS, independent qualification pending. Any consumer qualification waits for complete independent BC report. BA geometry full report c10a8a6ba2878f4f8e4729b7783f1228f1a1cfc7548ecc7164702cb0f433c8dd already qualified; no old gate replay.

Exact complete declaration and ALL local statement values:
```lean
theorem actual_six_standardized_arcs_lipschitz
    (n : ℕ) (hn : 1 ≤ n) (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (hclip : max aL (a0 - rho) ≤ min aR (a0 + rho)) (hqorder : qL ≤ qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ)) (hqwidth : qR - qL ≤ 1 / (n : ℝ)) :
    let L : ℝ := max aL (a0 - rho)
    let R : ℝ := min aR (a0 + rho)
    let M : ℝ := |a0| + rho
    let C : ℝ := 1 + 2 * M / level ^ 2
    let curve : Fin 6 → ℝ → ℝ × ℝ := ![
      (fun t => (L + t * (R - L), qL)),
      (fun t => (L + t * (R - L), qR)),
      (fun t => (L, qL + t * (qR - qL))),
      (fun t => (R, qL + t * (qR - qL))),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2)),
      (fun t => (L + t * (R - L), (L + t * (R - L)) ^ 2 / level ^ 2 - rho))]
    ∀ i : Fin 6,
      LipschitzOnWith (Real.toNNReal (‖E‖ * C / Real.sqrt (n : ℝ)))
        (fun t : ℝ => Real.sqrt (n : ℝ) • E (curve i t - y))
        (Set.Icc (0 : ℝ) 1)
```

Universally quantify every displayed argument. n>=1 is explicit for the 1/sqrt(n) conversion. E is an arbitrary continuous linear map, y arbitrary, not assumed true whitening/invertible. hrho and hclip are explicit: the clipped first-coordinate interval must be ordered, and so must the vertical grid interval; these follow from actual nonempty cells in the later source consumer, while empty cells will be handled separately. No cell nonemptiness, desired Lipschitz constant, tube/probability estimate, boundary-null condition or covariance matrix is assumed. The grid width upper bounds are explicit geometric premises. level is an arbitrary real for this pure total-division geometry statement, not a change to original physical positive-level assumptions. The existing maximum norm on real pairs is used.

M=|a0|+rho>=0 and C=1+2M/level²>=1. All6 exact parameter values agree with BA; two parabolas remain present. Proof derives 0<=R-L<=1/n, 0<=qR-qL<=1/n, and |L+t(R-L)|<=M for t∈Icc01. The straight bounds and parabola range bound feed BC primitives, weaken their constants to C/n, and then use BC actual scaling with exact sqrt(n)/n=1/sqrt(n). Local proof helper functions may only abbreviate these actual curves, constants and quantified intermediate bounds. No omitted global definition.

OPEN afterward: derive source family uniform bounds on ‖E‖ and geometry; actual cell nonempty/empty source consumer; exact affine/homeomorphic frontier transport; actual sixarc Gaussian tube and h=n^-3; anchors/disjointpartition/Edgeworth/full exterior and originalB/D. Accepted corrected fixed-lawA and bounded compact-tiltC retained. Original p54 repairs, strictWC and external attribution preserved. No silent premise/declaration change.

