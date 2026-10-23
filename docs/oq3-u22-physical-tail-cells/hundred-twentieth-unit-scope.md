# OQ3 unit120 (U22am): actual iid quadratic-tilt and exact cell probability
Frozen before implementation; source report.md section3 equations6–7 and repair01.md cell retilting. This is actual iid quadratic tilt for W=(X,X²), with its true MGF domain; no fixed bounded-X assumption. First helper removes finite-product tilt/normalizer obligation. Second is actual path-sample probability vs centered inverse-likelihood expectation for each measurable cell A and anchor y. Direct consumer is the source Gaussian/Edgeworth cell comparison; it does not posit that approximation.
All n including0 are allowed: totalized sample mean division at0 affects only the selected event, and the change-of-measure equality remains valid. Future positive sample-size/tail geometry will require n>=1 explicitly.
Two public theorems, zero globaldefinitions. Exact declarations:
```lean
theorem iid_quadratic_sample_tilt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) :
    let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
    let S : Shao.Path n → ℝ := fun z => ∑ i : Fin n, f (z i)
    let Z : ℝ := ∫ x : ℝ, Real.exp (f x) ∂mu
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    Integrable (fun z => Real.exp (S z)) P ∧
      (∫ z : Shao.Path n, Real.exp (S z) ∂P) = Z ^ n ∧
      P.tilted S = Measure.pi (fun _ : Fin n => mu.tilted f)

theorem iid_quadratic_cell_change_of_measure
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) (y : ℝ × ℝ) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
    let K : ℝ := Real.log (∫ x : ℝ, Real.exp (f x) ∂mu)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu.tilted f)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let E : Set (Shao.Path n) := M ⁻¹' A
    let G : Shao.Path n → ℝ := fun z => Real.exp (-(theta.1 *
      ((∑ i : Fin n, z i) - (n : ℝ) * y.1) +
      theta.2 * (Shao.energy z - (n : ℝ) * y.2)))
    Integrable G Q ∧
      P.real E = Real.exp (-(n : ℝ) * (theta.1 * y.1 + theta.2 * y.2 - K)) *
        ∫ z : Shao.Path n in E, G z ∂Q
```
No weak-Cramer/Edgeworth black box, no desired probability error premise, no root B/D closure. Anchor need not be the mean for this exact identity; the later cell consumer must specialize to the true tilt mean. The claimed integral is genuinely Integrable, including the unbounded-X case under the exact exponential-integrability premise. No extra moments silently introduced. Full independent proof/source/types/values and server kernel/allowner axioms required.
