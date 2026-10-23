# OQ3 unit130 / U22aw — actual planar Gaussian neighborhood mass

Original target B: repair01.md section2 eq(4)–(6), specifically the near-cell Gaussian probability needed by the first oscillation term. Direct consumer: AV actual averaged cell oscillation and the actual AR/AP small support. This is the genuine product of two standard Gaussian laws on real coordinates, not an arbitrary dominated measure or assumed probability estimate.

Freeze before implementation. The existing product-real norm is max norm; its closed ball is the square [-r,r]^2. The selected actual standard Gaussian CDF/interval bound from already accepted Shao.OQ4.IntervalConcentration is consumed without editing that lane. Current source SHA256491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875; actual source/object identity must be verified and prior complete acceptance reused. No local Lean or rebuilt dependency.

Both exact declarations follow. No definition is added. The radius r will be R/sqrt(n) only after a legitimate support producer; no n-dependent or boundary-tube conclusion is assumed. Arbitrary A, including empty/nonclosed/nonmeasurable A, is allowed because the closed thickening is closed and containment is all that is used. The bound at r=0 is an actual nonatomic Gaussian fact derived from the accepted CDF/closed interval theorem, not a presumed sample-law boundary property. Actual sample atoms remain unrestricted. Do not change assumptions silently.

```lean
theorem standard_gaussian_plane_closed_ball_bound
    (r : ℝ) (hr : 0 ≤ r) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real
        (Metric.closedBall (0 : ℝ × ℝ) r) ≤ 4 * r ^ 2

theorem standard_gaussian_plane_cell_thickening_bound
    (A : Set (ℝ × ℝ)) (r h : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hA : A ⊆ Metric.closedBall (0 : ℝ × ℝ) r) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real
        (Metric.cthickening h A) ≤ 4 * (r + h) ^ 2
```

The sharper boundary tube O(h/sqrt(n)+h²), exact cell partition/anchors, whitening family, actual Edgeworth comparison and original B/D remain OPEN; a whole ball bound must not be presented as the required thin boundary tube bound.
