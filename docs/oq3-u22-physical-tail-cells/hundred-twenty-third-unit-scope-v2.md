# OQ3 unit123 (U22ap), declaration v2: source small-cell support and exponential/Lipschitz bounds
Frozen before implementation. Source repair01.md section2 equations2–3 and report.md section3 equations7–8. Direct consumer small-cell average oscillation; actual standardized-cell change-of-measure AO supplies precisely the displayed g and affineimage. The cell-size premise is a literal geometric bound, not a probability/Edgeworth/error conclusion. E explicit invertible normalization map, covariancewhitening still needs actual separate instantiation.
Three public theorems/0globaldefinitions. Full declarations:
```lean
theorem normalizing_dual_linear_bound
    (theta : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (v : ℝ × ℝ) :
    |theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2| ≤
      ((|theta.1| + |theta.2|) * ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖) * ‖v‖

theorem standardized_cell_support_bound
    (n : ℕ) (hn : 1 ≤ n) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (y : ℝ × ℝ) (d : ℝ) (hd : 0 ≤ d) (A : Set (ℝ × ℝ))
    (hcell : ∀ w ∈ A, ‖w - y‖ ≤ d / (n : ℝ)) :
    ∀ v ∈ (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A,
      ‖v‖ ≤ d * ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ / Real.sqrt (n : ℝ)

theorem standardized_cell_exponential_bounds
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (R : ℝ) (hR : 0 ≤ R) :
    let B : ℝ := (|theta.1| + |theta.2|) * ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    (∀ v : ℝ × ℝ, ‖v‖ ≤ R / Real.sqrt (n : ℝ) →
      0 < g v ∧ |g v| ≤ Real.exp (B * R)) ∧
    (∀ v w : ℝ × ℝ, ‖v‖ ≤ R / Real.sqrt (n : ℝ) →
      ‖w‖ ≤ R / Real.sqrt (n : ℝ) →
      |g v - g w| ≤ Real.sqrt (n : ℝ) * B * Real.exp (B * R) * ‖v - w‖)
```
The constants B and exp(BR) depend on theta,E,R, not n. Support is O(n^-1/2), weight bounded and Lipschitz factor O(sqrt(n)) on the displayed ball. A can be arbitrarily thin/truncated; no lower area or probabilitymass premise. No tube/oscillation/Edgeworth/actualdensity or rootB-D claim. Full independent final source/proof/types/localvalues review and exactserver kernel/allowner recursiveAX required.


Representation correction before implementation v2: v1 frozen scope SHA f5028b614d67b0be7da18aca1e11c9444c4fb6e5688431411ca505496ef28ade used norm notation directly on ContinuousLinearEquiv, which has no Norm instance. v2 explicitly coerces E and E.symm to their continuous linear maps before taking the intended operator norms. Objects, mathematical assumptions, constants and conclusions are unchanged in meaning. Preserve v1 scope and failed source01; no successful source/check was changed or replayed.
