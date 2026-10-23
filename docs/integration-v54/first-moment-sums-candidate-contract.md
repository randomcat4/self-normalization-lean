# Next source-bound dependency

This author has completed and frozen the exact first-moment unit and releases its writer/execution slot. No next source module is implemented without root freezing its declarations. The second-moment candidate is separately owned by the root's new author in `drafts/c12-regulator-second-moment-candidate`; this author does not enter that scope.

## Available independent first-moment continuation: actual prefix marginal

The first-moment theorem above handles a terminal increment in a sample whose length equals its original time. The next direct interface is the exact prefix-marginal statement for each actual increment of a longer canonical sample. Complete candidate declaration, not yet frozen or implemented:

```lean
theorem iid_lindleyRegulator_prefix_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (N : ℕ) (i : Fin N) :
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    Integrable (fun a : Shao.Path N => lindleyRegulator a i) P ∧
      ((i.val + 1 : ℕ) : ℝ) *
        (∫ a : Shao.Path N, lindleyRegulator a i ∂P) =
          ∫ a : Shao.Path N, max (-(Shao.prefixSum a (i.val + 1))) 0 ∂P ∧
      (∫ a : Shao.Path N, lindleyRegulator a i ∂P) ≤
        Real.sqrt V / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + |μ|

theorem iid_lindleyRegulator_sum_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (N : ℕ) :
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    Integrable (fun a : Shao.Path N => ∑ i : Fin N, lindleyRegulator a i) P ∧
      (∫ a : Shao.Path N, ∑ i : Fin N, lindleyRegulator a i ∂P) ≤
        2 * Real.sqrt V * Real.sqrt (N : ℝ) + (N : ℝ) * |μ|
```

The producer is the frozen actual first moment. The eliminated obligations would be the true iid prefix marginal, agreement of the actual recursion on prefixes, finite expectation exchange, and the deterministic sum `∑_(i=1)^N i^(-1/2)≤2√N`. The second declaration includes `N=0`. It states the general actual-law sum bound, without promoting it to the source's uniform constant; that specialization still needs the source-law `N V` and `N|μ|` payments from conditionalmoments. No positive-variance premise belongs in these first-moment candidates.

## Precise remaining second-moment obstacle

Supplement LF2184–2215 needs the true reversal law for `W_(i-1)` and the genuine uniform one-sided survival estimate under the same iid source law:

`P(W_(i-1) ≤ a) ≤ C min(1, (a+γ)/(sqrt(V)*sqrt(i)))` for `a≥0`, with the original third centered moment, variance comparability, smallness and drift-budget payments from conditionalmoments. Integrating against the independent actual last increment then pays `E[(A^-)²(A^-+γ)]`, and the source proves `γ m₂≤2m₃` from `V≥m₂/2`. The existing OQ4 ReflectedSurvival results are adapters with genuine CDF/Spitzer inputs; they cannot serve as a closed source-law survival theorem. The present first-moment proof does not supply or assume that theorem.

Supplement LF2240 onward additionally requires the actual energy-tilted measure proportional to `exp(-s A²) dν`, its normalization, iid product identity, and the altered moments/drift. None of these weighted payments is established by the first-moment result.
