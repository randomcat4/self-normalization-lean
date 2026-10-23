# OQ3 unit122 (U22ao): actual affine-standardized cell expectation
Frozen before implementation. Source report.md section3 equations6–8, repair01.md section2 exact B_Q/f_Q. Direct consumer is the bounded small-cell oscillation/Edgeworth function input. This exports the actual transformed tilted SAMPLE LAW, not an assumed density or Gaussian law.
The invertible continuous linear map E is explicit geometric input. The identity is valid for any such E; a later actual whitening producer must instantiate E=Delta^(-1/2) before claiming identity covariance. No whitening, mean, weakCramer, Edgeworth or probabilistic error condition is silently inferred from invertibility.
One public theorem, no globaldefinitions, exact declaration:
```lean
theorem iid_quadratic_standardized_cell_change_of_measure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) (hn : 1 ≤ n) (y : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
    let K : ℝ := Real.log (∫ x : ℝ, Real.exp (f x) ∂mu)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu.tilted f)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let F : (ℝ × ℝ) → (ℝ × ℝ) := fun w => Real.sqrt (n : ℝ) • E (w - y)
    let T : Shao.Path n → (ℝ × ℝ) := fun z => F (M z)
    let rho : Measure (ℝ × ℝ) := Measure.map T Q
    let B : Set (ℝ × ℝ) := {v | y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v ∈ A}
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    MeasurableSet B ∧ B = F '' A ∧ Integrable g rho ∧
      P.real (M ⁻¹' A) = Real.exp (-(n : ℝ) * (theta.1 * y.1 + theta.2 * y.2 - K)) *
        ∫ v : ℝ × ℝ in B, g v ∂rho
```
B is simultaneously the exact affine image of A and inverse-affine preimage, hence includes actual arbitrarily thin truncated cells. rho is exactly the pushforward of actual iid tilted product, and g is exactly the source centered inverse likelihood. Integrability must be proved from AM, not assumed. n>=1 explicit. Anchor y arbitrary for the exact identity; later y=m(theta) plus Legendre equality required to interpret the exponent as the actual rate. No Gaussian/Edgeworth approximation/exterior/B-D closure claimed. Full independent final source/proof/alltypes/localvalues review plus server kernel/recursive axiom audit required.
