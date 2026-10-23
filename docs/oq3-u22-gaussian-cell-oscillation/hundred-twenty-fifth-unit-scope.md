# OQ3 unit125 (U22ar): actual standardized-cell indicator oscillation
Frozen before implementation. Source repair01.md section2 equations3–4 and report.md equation9; directconsumer averageGaussianoscillation and sourcepercellEdgeworth. AO has precisely this g/B, AP givesactualsupport/weight/Lip, AQ suppliesboundarysplit. This theorem must DERIVE both uniformbounds from the geometriccellpremise; it cannot assume the desiredoscillation or Gaussianerror.
One public theorem,0globaldefs, exact declaration:
```lean
theorem standardized_cell_pair_oscillation_bound
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
    ∀ z : ℝ × ℝ, ∀ u ∈ Metric.closedBall z h, ∀ v ∈ Metric.closedBall z h,
      |B.indicator g u - B.indicator g v| ≤
        (if (Metric.closedBall z h ∩ B).Nonempty then
          2 * Real.sqrt (n : ℝ) * kappa * C * h else 0) +
        (if (Metric.closedBall z h ∩ frontier B).Nonempty then 2 * C else 0)
```
C/kappa/R are independent of n for fixed cellgeometry/tilt/normalizingmap data. h may be anynonnegative number because g/Lipschitz are needed only ON exactB; later h=n^-3 is a specialization. Empty/thin/nonclosedcells allowed. No measurability/supremum/integral/tube/Edgeworth/far/rootB-D conclusion. ActualE covariancewhitening anduniformfamily bounds stillmustbe supplied by legitimateproducers. Exactserverkernel/allownerAX + freshcompleteindependent proof/source/types/values required.
