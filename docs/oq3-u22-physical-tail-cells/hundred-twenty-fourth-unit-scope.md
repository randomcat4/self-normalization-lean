# OQ3 unit124 (U22aq): boundary-indicator pointwise oscillation
Frozen before implementation. Source repair01.md section2 equations4–6, report.md small-cell boundary oscillation. This is the deterministic boundary split, not the unrelated historical unified mechanism. Direct consumer: actual AO/AP cell test plus Gaussian average oscillation/tube bounds.
A may be any set; g bounded and Lipschitz only ON A, so no unnecessary outside-support assumptions. On a closed ball disjoint from the frontier, connectedness forces constant membership. The second theorem bounds every pair in the ball by the interior Lipschitz contribution supported near A, plus the jump contribution supported near frontierA. Constants and closed-ball boundary inclusions frozen below. No Gaussian integration/tube/Edgeworth conclusion is assumed.
Two public theorems/0globaldefinitions:
```lean
theorem closed_ball_membership_iff_of_frontier_disjoint
    (A : Set (ℝ × ℝ)) (z : ℝ × ℝ) (h : ℝ)
    (havoid : Disjoint (Metric.closedBall z h) (frontier A)) :
    ∀ u ∈ Metric.closedBall z h, ∀ v ∈ Metric.closedBall z h, (u ∈ A ↔ v ∈ A)

theorem indicator_cell_pair_oscillation_bound
    (A : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ)
    (C L h : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hbound : ∀ u ∈ A, |g u| ≤ C)
    (hLip : ∀ u ∈ A, ∀ v ∈ A, |g u - g v| ≤ L * dist u v)
    (z : ℝ × ℝ) :
    let Near : Prop := (Metric.closedBall z h ∩ A).Nonempty
    let Edge : Prop := (Metric.closedBall z h ∩ frontier A).Nonempty
    ∀ u ∈ Metric.closedBall z h, ∀ v ∈ Metric.closedBall z h,
      |A.indicator g u - A.indicator g v| ≤
        (if Near then 2 * L * h else 0) + (if Edge then 2 * C else 0)
```
For h=0 the ball is a singleton and left oscillation is0. EmptyA/frontier and thin truncated cells allowed. This pairwise bound is not yet a measurability or integral claim for the supremum oscillation. No actual sample probability approximation/rootB-D closure. Full independent final semantics/proof/alltypes/localvalues and exactserverkernel/allowner recursiveAX required.
