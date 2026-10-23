# OQ3 unit129 / U22av — genuine integrated cell oscillation

Original target B: repair01.md section2 equation(4), an actual averaged oscillation rather than a per-pair inequality. Direct consumers: actual standardized cell AR followed by source Gaussian tube bounds and Edgeworth remainder. The measure is any finite Borel measure, hence includes Phi2 when properly instantiated; no claimed density/tube/Edgeworth conclusion is assumed.

Exact declaration below is frozen before implementation. The oscillation is the actual AU real open-ball supremum, not a renamed majorant. No measurability of A or g is assumed: AU gives measurability from the derived global boundedness of A.indicator g. The genuine integrability is part of the conclusion. Closed metric thickenings are closed/measurable even for arbitrary A, safely dominate actual closed-ball hits and include closure points without assuming boundary mass zero. Finite mass prevents Measure.real infinity-to-zero effects. The source uses Euclidean coordinates whereas the formal product-real metric is the existing max norm; later uniform norm comparison/tube geometry is still required. Assumptions and exact conclusion may not be silently changed.

```lean
theorem indicator_cell_averaged_oscillation_bound
    (μ : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsFiniteMeasure μ]
    (A : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ)
    (C L h : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hbound : ∀ u ∈ A, |g u| ≤ C)
    (hLip : ∀ u ∈ A, ∀ v ∈ A, |g u - g v| ≤ L * dist u v) :
    MeasureTheory.Integrable (openBallOscillation (A.indicator g) h) μ ∧
    (∀ z, openBallOscillation (A.indicator g) h z ≤
      (Metric.cthickening h A).indicator (fun _ => 2 * L * h) z +
      (Metric.cthickening h (frontier A)).indicator (fun _ => 2 * C) z) ∧
    (∫ z, openBallOscillation (A.indicator g) h z ∂μ) ≤
      2 * L * h * μ.real (Metric.cthickening h A) +
      2 * C * μ.real (Metric.cthickening h (frontier A))
```

No new global definitions. One public theorem. This closes only the measure integration step of equation(4), not source eq(5)/(6), actual covariance whitening, Edgeworth or original B/D. AU must complete independent qualification before this consumer is accepted; author server gates may proceed on exact source/object identities while its full review runs.
