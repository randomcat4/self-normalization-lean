# OQ3 unit131 / U22ax — actual standardized Gaussian averaged oscillation

Original B target: repair01.md section2 eq(4)–(6). Direct consumer: the remaining thin boundary-tube producer and then h=n^(-3) source remainder. Freeze exact declaration before implementation. This consumes AP geometric-cell support and actual exponential bounds, AU real measurable supremum, AV genuine integral inequality, and AW actual product-Gaussian neighborhood probability. Parent gates may run at exact author-PASS identities while fresh complete reviews finish; acceptance waits for each dependency qualification.

The conclusion uses the SAME affine-image B and inverse-map weight g as AR/AO and the genuine product standard Gaussian Phi. All bounds on g/Lipschitz behavior and its actual finite-measure integrability must be derived from hcell; no desired probability/integrability/oscillation premise appears. The near-cell contribution is explicit in n,h,R,kappa,C. The boundary probability stays literal and must still be bounded by a legitimate tube estimate. Do not infer covariance whitening or uniformity over varying theta/E/d. Product-real norm is max norm; any Euclidean interpretation still needs legitimate comparison. Original B/D remains OPEN; no silent assumption changes.

```lean
theorem standardized_gaussian_cell_averaged_oscillation_bound
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (d : ℝ) (hd : 0 ≤ d) (A : Set (ℝ × ℝ))
    (hcell : ∀ w ∈ A, ‖w - y‖ ≤ d / (n : ℝ))
    (h : ℝ) (hh : 0 ≤ h) :
    let B : Set (ℝ × ℝ) := (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    let kappa : ℝ := (|theta.1| + |theta.2|) * ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let R : ℝ := d * ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let C : ℝ := Real.exp (kappa * R)
    let Φ : MeasureTheory.Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)
    MeasureTheory.Integrable (openBallOscillation (B.indicator g) h) Φ ∧
    (∫ z, openBallOscillation (B.indicator g) h z ∂Φ) ≤
      8 * Real.sqrt (n : ℝ) * kappa * C * h *
        (R / Real.sqrt (n : ℝ) + h) ^ 2 +
      2 * C * Φ.real (Metric.cthickening h (frontier B))
```

No global definitions. One public theorem. In particular this theorem must not be advertised as the final O(n^-7/2) oscillation result because the boundary term is not yet given the thin-tube rate.
