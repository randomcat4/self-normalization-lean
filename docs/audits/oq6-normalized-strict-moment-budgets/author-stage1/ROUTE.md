# Unit229 source-bound route and exact generic-API argument map

Status: `ROUTE_ONLY_NO_PROOF_IMPLEMENTATION`. The mathematical route is complete at the interface level; it still requires lead freeze, implementation, independent review and new exact-source server evidence before acceptance.

## Sole bearing producer

Use the already qualified theorem
`Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits`
from exact source SHA256 `c414aeb98cec27146d30f38e3c869f34a7b81e4a45101497a99db29a4d37b92d`, full declaration lines173–241. The exact application expression is:

```lean
Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits
  ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr z
```

| Producer input | Candidate input |
|---|---|
| implicit carrier and measurable instance | the same `Ω`, `[MeasurableSpace Ω]` |
| `ν`, probability instance | the same `ν`, `[IsProbabilityMeasure ν]` |
| `n`, `hn`, `ξ`, `hξ`, `hξ2` | identical values and proofs |
| `hξmean`, `hξenergy` | identical original mean-zero and total-energy proofs |
| `Y`, `hY` | identical sequence and coordinate measurability |
| `ε`, `hε`, `hεsmall`, `hεlim`, `herr` | identical positive/small/error/limit assumptions |
| `x : ℝ` | exactly `z`, not `1 + z` |

The producer's eta is definitionally the candidate eta. Its delta/deltaEta/L/LEta become the candidate δ0/δη/L0/Lη by unfolding `Fz` and the six displayed lets. No law change, independent-variable factorization, integration transport, normalization theorem reproving, or product-integrability premise occurs.

Under the producer's right-associated conjunction, counting its top-level components with `Integrable exp(S)` and `0 < I` separately, original integrability is component12 (line221), normalized integrability13 (line222), coordinate limits18 (line228), and finite-sum limit19 (line229). These four fields are the only fields needed. This is a statement-field map, not a fresh audit or replay of the old proof/object/axioms.

## Finite strict-budget transfer

After the candidate lets, introduce the two conditional proof variables with the exact types:

```lean
hδ0 : ∀ i : Fin n, δ0 i < (1 / 2 : ℝ)
hL0 : L0 < cBudget * z ^ 2
```

The only planned new local fact interfaces are:

```lean
hδ0int : ∀ i : Fin n, Integrable (fun (ω : Ω) => Fz (ξ i ω)) ν
hδηint : ∀ (k : ℕ) (i : Fin n),
  Integrable (fun (ω : Ω) => Fz (η k i ω)) ν
hδlim : ∀ i : Fin n,
  Filter.Tendsto (fun (k : ℕ) => δη k i) Filter.atTop (nhds (δ0 i))
hLlim : Filter.Tendsto Lη Filter.atTop (nhds L0)
hδevent : ∀ i : Fin n,
  ∀ᶠ k : ℕ in Filter.atTop, δη k i < (1 / 2 : ℝ)
hAllevent : ∀ᶠ k : ℕ in Filter.atTop,
  ∀ i : Fin n, δη k i < (1 / 2 : ℝ)
hLevent : ∀ᶠ k : ℕ in Filter.atTop, Lη k < cBudget * z ^ 2
htail : ∀ᶠ k : ℕ in Filter.atTop,
  (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2
k0 : ℕ
hk0 : ∀ k : ℕ, k0 ≤ k →
  (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2
```

These are proposed `have`/witness types, not proof terms, new assumptions, extra theorem parameters, local definitions or a proof implementation. The first four facts come only from the four producer fields just identified. Each coordinate limit maps the open real interval `(-∞,1/2)` containing δ0 i to an eventual condition. The sum limit maps the open interval `(-∞,cBudget*z²)` containing L0 likewise. Finiteness of `Fin n` combines all coordinate conditions in the same filter; intersect with the sum condition. The Nat-atTop characterization of this one eventual conjunction supplies k0 and hk0. Thus one index works for all k≥k0 and all i, with the exact two strict conclusions.

The standard neighborhood/finite-filter/Nat-tail interfaces intended for that step are `Filter.Tendsto.eventually`, `eventually_lt_nhds`, `Filter.eventually_all`, conjunction of eventual facts, and `Filter.eventually_atTop`. Exact elaboration has not been run. No extra helper theorem is proposed and no new per-unit runner/preflight wrapper is needed.

## Exact captures and choices

All deterministic value lets and their exact RHSs are in CANDIDATE.md; there are no other planned value lets. The only integral callbacks are `fun (ω : Ω) => Fz (ξ i ω)` and `fun (ω : Ω) => Fz (η k i ω)`, capturing exactly Fz/ξ/i or Fz/η/k/i. The only convergence callback is `fun (k : ℕ) => δη k i`, capturing δη and i. Eventual predicates capture the already fixed δη/Lη/z/cBudget and the corresponding fixed threshold. None receives sample-dependent, future or external information.

There is no chosen measurable function, encoding, measurable inverse, dependent instance, arbitrary regular conditional law, auxiliary-Prop binder, public callback premise or new axiom. The only witness k0 is existentially obtained after the fixed model/sequence/scalars and both conditional margin proofs. Its type is ℕ; hk0 is exactly the displayed tail property. No deterministic RHS for k0 is promised by the theorem, and no `Classical.choose` value let is planned. This is an existence theorem, not a computable-rate theorem.

The only user-supplied typeclass instances remain `[MeasurableSpace Ω]` and `[IsProbabilityMeasure ν]`. Standard finite-index, real-field, real topology/Borel, and Nat-atTop structures are imported canonical instances; `Fin n` is finite for the already fixed n. No topology, StandardBorel, Nonempty or countably-generated assumption on Ω is needed. The witness selection and all captures remain inside the candidate's fixed parameter scope.

## Boundary and non-circularity checks

* The function matches the continuous source truncation exactly: for s=z*t, `s² min(|s|,1)` equals |s|³ when |s|≤1 and s² when |s|≥1, agreeing at |s|=1. In particular it is continuous at t=±1/z in the z≥1 regime and bounded by z²t². Higher or mixed moments are not silently used.
* Every finite k has normalized-integrand integrability, while the strict budgets hold only on the eventual tail. The statement does not promote an eventual budget to an all-k budget.
* n=1 and z=1 are included exactly as conditionally stated. The theorem does not assert that any fixed model admits the requested strict original margins; infeasible margins for a particular model do not become an existence claim.
* The proof cannot start from normalized strict bounds as a premise: its only added premises are strict bounds on the displayed original integrals. Neither conclusion is hidden in a callback or auxiliary proposition.
* `hz` and `hcBudget` are source-regime restrictions, not evidence that a published source constant has been identified. No source constant is imported or applied.
* The candidate is a standard strict-limit bridge extracted from an existing qualified generic limit API. It claims no research novelty. Related strict-limit reasoning appears in the much larger canonical/tail assembly interfaces; those modules are not dependencies of this candidate and their proofs are not rerun or re-reviewed here.
