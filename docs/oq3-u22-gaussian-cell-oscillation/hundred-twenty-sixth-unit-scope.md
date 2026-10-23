# OQ3 unit126 (U22as): actual iid exponential separator probability
Frozen before implementation. Source report.md section4 equation18 finiteexponentialcover and repair01.md section4 far-field scope. Direct consumer compact actual rate-gap finite cover.
This is actual iid mu, truequadratic exponential domain, actual raw samplemean. hsep is a pointwise lower bound for a genuine normalized log-MGF exponential TEST on the geometric target A, not an assumed probability bound or the target rate theorem.
Onepublictheorem0globaldefs:
```lean
theorem iid_quadratic_exponential_separator_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) (hn : 1 ≤ n) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) (c : ℝ)
    (hsep : ∀ w ∈ A, c ≤ theta.1 * w.1 + theta.2 * w.2 -
      Real.log (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    P.real (M ⁻¹' A) ≤ Real.exp (-(n : ℝ) * c)
```
Derive through AM exact changeofmeasure and genuineIntegrable, with actual tilted product probability <=1. No boundedX or unproved distribution-density assumption. c arbitrary real; n>=1 explicit. Does not yet derive separators/finitecover from actualLegendre rate, nor unbounded far-field exponentialtightness/globalB-D closure. Exactserver kernel/allowner recursiveAX + freshcomplete independent source/proof/types/values review required.
