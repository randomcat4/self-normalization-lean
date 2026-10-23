# OQ3 U22BB / unit 135 — frozen finite-arc Gaussian tube interface

State: FROZEN before implementation. Author: OQ3 lead. Fresh independent source/statement/proof/full-owned-type/value and recursive axiom review required before qualification. math-theorem, never math-ultra.

Source-bound dependency: read-only original repair01 needs a Gaussian boundary-neighborhood estimate for actual normalized physical cells. AY132 constructs a single Lipschitz arc cover and proves actual standard product-Gaussian tube mass <=64(Kh+h²). AZ133/BA134 derive the literal closed-window intersected half-open-grid frontier and its six explicit compact arcs. This unit sums the actual single-arc estimate under an explicit geometric cover; it does not assume the desired probability estimate. It is a generic consumer, not by itself the original B/D theorem or the actual six-arc scaled bound.

Exact imports planned: Shao.OQ3.GaussianCurveTube. The existing accepted/qualified AY source SHA256 d4d1da20940cbb53f74bbfe4f6b65391faa19d7b1e2b9a6a13d393cceb85ce49 and independent full report bf1941655e52f442256e67c76b37affea14d1767aff5e62563a4119520116a30 are reused without replay. Lean/mathlib pins, CPU14–17/max1heavy/-M8192/-j4 remain fixed.

Exact complete declaration (one public theorem, no global definitions):
```lean
theorem standard_gaussian_plane_finite_arc_cover_tube_bound
    (m : ℕ) (f : Fin m → ℝ → ℝ × ℝ) (K : Fin m → NNReal)
    (hf : ∀ i, LipschitzOnWith (K i) (f i) (Set.Icc (0 : ℝ) 1))
    (F : Set (ℝ × ℝ))
    (hcover : F ⊆ ⋃ i : Fin m, f i '' Set.Icc (0 : ℝ) 1)
    (h : ℝ) (hh : 0 < h) :
    ((ProbabilityTheory.gaussianReal 0 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).real (Metric.cthickening h F) ≤
        64 * (h * (∑ i : Fin m, (K i : ℝ)) + (m : ℝ) * h ^ 2)
```

All parameters universally quantified. Fin m can be empty (m=0). F can be empty, nonclosed, nonmeasurable or disconnected; no hidden compactness or nonemptiness. Each K is an actual finite nonnegative NNReal. h>0, matching the qualified single-arc theorem. The norm on ℝ×ℝ is the existing maximum norm. The measure is the actual gaussianReal0,1 product, not a new assumed law/density.

Proof route: derive compactness/closedness of the finite union of actual Lipschitz arc images; infer closure F lies in that closed union; represent the closed thickening using closure F and nearest closed balls; each such ball lies in the thickening of some arc. Apply finite Gaussian real-measure union subadditivity and the already constructed single-arc bound, then exact finite-sum algebra. This also covers m=0 and arbitrary F without discarding boundary atoms.

Local proof lets may abbreviate exactly Φ=(gaussianReal0,1).prod(gaussianReal0,1), U=⋃i,f i''Icc01, and H i=cthickening h (f i''Icc01). No auxiliary assumption can assert the desired Gaussian tube mass. No declaration/assumption edits silently; any representation correction requires explicit version freeze before corrected source/check.

OPEN after this unit: actual scaled affine/quadratic arc Lipschitz constants uniform in the source cell family, exact affine/homeomorphic frontier transport, actual six-arc consumer, h=n^-3 order, whitening, valid anchors/disjoint partition, actual Edgeworth and full exterior. Original B/D OPEN, previously qualified fixed-law A and bounded compact-tilt C scopes retained. Source p54 repairs, strict WC threshold and external-result attribution unchanged.

