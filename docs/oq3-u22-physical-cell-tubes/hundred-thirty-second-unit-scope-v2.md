# OQ3 unit132 / U22ay — actual Gaussian tube of a Lipschitz arc

Original B target: repair01.md section2 eq(5), thin boundary tube. Direct consumer: source frontier as at most5 actual standardized Lipschitz arcs with K=O(n^-1/2), then AX and h=n^-3. Freeze before implementation. This module must derive an actual Gaussian tube bound from real curve geometry rather than assume a desired tube probability estimate.

Proof route: actual translated Gaussian rectangle/ball mass from the accepted actual CDF bound; compact finite ball-cover tube containment and probability union bound; construct a uniform mesh with N=ceil(K/h)+1 on [0,1], ≤N+1 image centers, and prove the mesh approximation from the ACTUAL LipschitzOnWith premise. Then16*(N+1)*h²≤64(Kh+h²). Finite covers alone are auxiliary; the third theorem must actually construct one from the arc. No measurability/probability estimate is assumed for the curve image. Compactness derives from the supplied on-interval Lipschitz condition. The finite cover lemma uses compact F so closed-neighborhood witnesses are attained legitimately.

Exact declarations:

```lean
theorem standard_gaussian_plane_translated_ball_bound
    (z : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real (Metric.closedBall z r) ≤ 4 * r ^ 2

theorem standard_gaussian_plane_finite_ball_cover_tube_bound
    (F : Set (ℝ × ℝ)) (hF : IsCompact F) (S : Finset (ℝ × ℝ))
    (h : ℝ) (hh : 0 ≤ h)
    (hcover : ∀ x ∈ F, ∃ c ∈ S, dist x c ≤ h) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real (Metric.cthickening h F) ≤
        16 * (S.card : ℝ) * h ^ 2

theorem standard_gaussian_plane_lipschitz_arc_tube_bound
    (f : ℝ → ℝ × ℝ) (K : NNReal)
    (hf : LipschitzOnWith K f (Set.Icc (0 : ℝ) 1))
    (h : ℝ) (hh : 0 < h) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real
        (Metric.cthickening h (f '' Set.Icc (0 : ℝ) 1)) ≤
          64 * ((K : ℝ) * h + h ^ 2)
```

No new global definitions. Three public theorems. The norm is the existing max norm on real pairs, and the actual product Gaussian uses standard real coordinates. Bounds do not presume actual sample laws have zero boundary mass. Applying the third theorem to the at-most5 actual transformed cell edges/parabolic boundary piece, and obtaining uniform K and exact frontier containment, remain separate OPEN producers. The source covariance-whitening family/anchors/partition/Edgeworth comparison and original B/D stay OPEN. Assumptions and frozen full declarations must not be changed silently.

## Representation correction before second kernel attempt
V1 used the ill-typed notation token ℝ≥0, parsed as a comparison on Type in this context. V2 writes the intended NNReal parameter type explicitly. This changes no mathematical domain, assumption, conclusion, constant or proof route; the original V1 and failed source01 are preserved. All exact declarations above replace only that representation before the next source change/check.
