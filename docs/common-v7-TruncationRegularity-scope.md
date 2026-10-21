# Truncation budget: regularity and normalized asymptotic proposal

Status: the coordinator froze the five regularity signatures on 2026-10-21
and authorized implementation. The frozen proposal SHA256 was
`f7c95db32fb6a0590f10bd5b07ce099af4995af5faa75ead8f90588d995ad257`.

## Source contract rechecked

Read `C:/game/shao/current/c12/main.tex` at the common notation and Lemma
`h:lem:truncatedbudget` (Lemma 3.1), and the corresponding proof
`h:supp:truncatedbudgetproof` in `supplement.tex`.

The source starts from iid real observations with `EX=0` and
`0<σ²=EX²<∞`, and an integer `n≥1`. For this lemma it sets

```text
ξ = X/(σ√n),     ν = the actual probability law of ξ,
n ∫ z² dν = 1,   n ∫ |z|^p dν = β_(n,p),
R_n(t) = n ∫ F((1+t)z) dν,     F(z)=z² min(|z|,1).
```

Crucially, the normalized law has second moment `1/n`, not second moment `1`.
Replacing `ν` by a unit-second-moment law without this `n` scaling would make
the normalized limit below equal to `n`, rather than the source's `1`.
The iid and mean-zero hypotheses are not used for the scalar budget's
regularity, so they will not be introduced into its interface.

The exact new source assertions are:

1. `R_n` is continuous on `[0,∞)`.
2. It is strictly increasing on `[0,∞)`.
3. **The ratio** `R_n(t)/(1+t)²` tends to `1` as `t→∞`.

The source does not assert that the unnormalized `R_n(t)` tends to `1`.
The normalized ratio limit, not a guessed alternative limit, is the target.
Each limit fixes both `ν` and `n`; it is not a joint limit in sample size or
an assertion uniform over changing normalized laws.
The real-power upper bound and the local `1/8`/`8` comparison were handled in
the preceding integral component and are not redefined here.

## Proposed regularity module and exact declarations

Use a new `Shao/Probability/TruncationRegularity.lean` importing the frozen
`TruncationIntegrals` module. Keep the existing `truncationBudget` definition
unchanged. Namespace `Shao`; `open MeasureTheory Filter`; `open scoped Topology`;
`autoImplicit false`.

The following five declarations form the proposed independently closable unit:

```lean
theorem continuousOn_truncationBudget (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    ContinuousOn (truncationBudget ν n) (Set.Ici 0)

theorem truncationBudget_pos (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (hn : 0 < n)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂ν) (t : ℝ) (ht : 0 ≤ t) :
    0 < truncationBudget ν n t

theorem strictMonoOn_truncationBudget (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (hn : 0 < n)
    (hsecond : 0 < ∫ z : ℝ, z ^ 2 ∂ν) :
    StrictMonoOn (truncationBudget ν n) (Set.Ici 0)

theorem tendsto_truncationBudget_div_sq (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Tendsto (fun t : ℝ => truncationBudget ν n t / (1 + t) ^ 2) atTop
      (𝓝 ((n : ℝ) * ∫ z : ℝ, z ^ 2 ∂ν))

theorem tendsto_truncationBudget_div_sq_of_normalized_second
    (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1) :
    Tendsto (fun t : ℝ => truncationBudget ν n t / (1 + t) ^ 2) atTop (𝓝 1)
```

The `hnorm` condition itself implies `n>0` and a strictly positive second
moment. Thus the general positivity and strict-monotonicity interfaces recover
the source's assertions under its actual normalization; no extra source
hypothesis is needed. A normalized strict-monotonicity wrapper would be a
direct corollary, not another measure-theoretic input.

## Minimal assumptions and proof obligations

| Assertion | Assumptions beyond an arbitrary real measure |
|---|---|
| Continuity on `[0,∞)` | Integrable square only; arbitrary natural `n`, including zero |
| General ratio limit | Integrable square only; arbitrary natural `n`, including zero |
| Positive budget | Integrable square, `n>0`, positive square integral |
| Strict increase | Integrable square, `n>0`, positive square integral |
| Ratio limit equal to `1` | Integrable square and `n∫z²=1` |

No finite-measure, probability-measure, sigma-finite, positive-density,
non-atomicity, global third-moment, or mean-zero assumption is required for
these five regularity statements. If `n=0`, the budget is identically zero;
if the square integral is zero, its integrable nonnegative integrand forces
the budget to vanish. These cases correctly remain in the continuity/general
limit assertions and are excluded from strict increase by its stated premises.

Proof routes, without changing these declarations:

- Continuity: on `0≤t≤T`, dominate the actual integrand by
  `(1+T)² z²`, and use scalar continuity plus dominated convergence locally.
- Positivity: positive square integral gives positive measure to nonzero `z`;
  at `1+t>0`, `F((1+t)z)>0` exactly there. Integrability is already proved.
- Strict increase: for `0≤s<t`, take `c=(1+t)/(1+s)>1`. The proved quadratic
  scaling lower bound gives `R_n(t)≥c²R_n(s)>R_n(s)` using positive budget.
- Ratio limit: eventually `t≥0`, so the exact integrand after division is
  `z² min((1+t)|z|,1)`. It tends pointwise to `z²` (including `z=0`) and is
  dominated by the integrable `z²`. Multiplying the limit by `n` gives the
  general target; `hnorm` gives the source target `1`.

## Sample-size lower bound: next, separate unit

The remaining source assertion is the exact chain

```text
if t≥0 and R_n(t)≤ρ≤1/16, then
(1+t)^6 ≤ (1-ρ)^3 (1+t)^6 / R_n(t)^2 ≤ n.
```

It requires an additional integral moment comparison. The preceding five
regularity results and the frozen integral decomposition alone do not prove
it. It should be a separately frozen `TruncationSampleSize` unit, rather than
silently adding a Lyapunov inequality as a hypothesis to this unit.

A source-faithful eventual API for that next unit is:

```lean
theorem truncationBudget_sample_size_lower
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (t ρ : ℝ) (ht : 0 ≤ t)
    (hR : truncationBudget ν n t ≤ ρ) (hρ : ρ ≤ 1 / 16) :
    (1 + t) ^ 6 ≤
        (1 - ρ) ^ 3 * (1 + t) ^ 6 / truncationBudget ν n t ^ 2 ∧
      (1 - ρ) ^ 3 * (1 + t) ^ 6 / truncationBudget ν n t ^ 2 ≤ (n : ℝ)
```

This next-unit signature is proposed only, not included among the five
regularity declarations for implementation. No global third moment is needed:
the random variable in Lyapunov's inequality is the bounded-cutoff variable
`g(z)=z 1_{|z|≤1/(1+t)}`, whose third absolute moment is integrable by the
previous component.

The next unit must actually prove the probability-space comparison
`(∫g²)^3 ≤ (∫|g|³)^2` (for example from established Holder/Lp machinery), then
combine it with retained square integral `n∫g²≥1-ρ`, the budget decomposition,
and the positive denominators. `R_n(t)>0` and `n>0` follow from normalization
and the proposed regularity result, rather than being silently assumed.

The mass condition matters for this numeric constant. General finite measures
with only `h2` and `hnorm` do **not** suffice: take

```text
n=1, t=0, ν=1024 δ_(1/32), ρ=1/32.
```

Then `n∫z²=1`, `R_n(0)=1/32≤ρ≤1/16`, but the displayed middle term is
`31³/32>1=n`, contradicting the claimed upper bound by `n`. A subprobability
mass bound would also suffice for Lyapunov, but the original law is a
probability measure; no unnecessary probability condition is imposed on the
regularity unit above.

All proposed implementation checks remain server-only. Existing frozen source
files, their definitions, and their hashes remain untouched.

## Implementation and designated-server receipt

The five frozen regularity declarations are implemented, without additional
premises, in `drafts/c12/TruncationRegularity.lean` and the remote counterpart
`workspaces/lead-c12/Shao/Probability/TruncationRegularity.lean`.

The actual targeted command, after the pinned activation script and changing
to `lead-c12`, was:

```text
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/Probability/TruncationRegularity.olean Shao/Probability/TruncationRegularity.lean
```

The final check exited 0 with no compiler diagnostics. The new dominated
convergence import was already cached; no package cache writes were needed.
The designated-server source SHA256 is:

```text
1d2fb3de5a6e1cb15ccbf083d483cfca5d7c42768ce19e845d590ef52c2a87ad
```

A separate import through `lake env lean --stdin` printed the transitive axioms
of all five declarations. It exited 0; each list is exactly
`[propext, Classical.choice, Quot.sound]`. The pinned versions remain Lean
`leanprover/lean4:v4.36.0-rc1` and mathlib
`807d3836b165983210ee2ecf3cd28f239436949c`.

Proof coverage matches the proposal: the continuity proof uses the local
integrable dominator `(2+t₀)² z²` on `[0,∞)`; positivity reduces a zero budget
integral to a zero square integral; strict increase uses the existing quadratic
scaling lower bound and positive budget. The asymptotic proof applies dominated
convergence to `z² min((1+t)|z|,1)`, with dominator `z²` and pointwise limit
`z²`, including `z=0`.

Current status: all five frozen regularity assertions are mechanically checked;
independent blind semantic/proof review is pending. The sample-size lower-bound
unit above remains unimplemented here and belongs to the separately assigned
author. No complete Lemma 3.1 certificate is claimed solely by this file.
