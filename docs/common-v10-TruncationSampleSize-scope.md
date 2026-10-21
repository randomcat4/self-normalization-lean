# Frozen genuine truncation-budget sample-size lower bound

Status: the root coordinator froze the sole public signature and actual
polynomial-integral Lyapunov route at proposal SHA256
`5d6361c6b066de65c9e226132102871ed7361a0c0f81832d0bdfd5b1bfbf6c3e`
before implementation. `TruncationSampleSize.lean` in this directory now passes
the targeted server check and transitive axiom audit; see its review receipt.
This unit does not modify TruncationIntegrals or the separate Regularity source.

## Exact source contract

Read-only `current/c12/main.tex`, Lemma 3.1 (`h:lem:truncatedbudget`), lines
320-329, states the chain

```text
n >= (1-rho)^3 (1+t)^6 / R_n(t)^2 >= (1+t)^6
```

under `t>=0` and `R_n(t)<=rho<=1/16`, for the actual normalized observation law.
Read-only `supplement.tex`, `h:supp:truncatedbudgetproof`, lines 994-1020,
uses `a=1+t`, the retained event `D={abs z<=1/a}`, actual retained moments,
normalization `n integral z^2 = 1`, Lyapunov, and positivity of the budget.
The normalized law has second moment `1/n`, not `1`.

Source hashes:

- main: `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`.
- supplement: `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

The last section of `TruncationRegularity-scope.md` was read as a proposal for
this separate unit, not as an already accepted theorem. Its target signature
is retained exactly below. Regularity's already frozen positivity interface
can supply a proved positive denominator once that independent module is ready.

## Frozen sole public theorem

New module `Shao/Probability/TruncationSampleSize.lean`, namespace `Shao`,
`open MeasureTheory`, `autoImplicit false`:

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

The definition of `truncationBudget` is unchanged. There is no Lyapunov,
global-third-moment, positive-budget, positive-second-moment, positive-`rho`,
or positive-`n` input. The last four positivity properties that are needed
are derived from the displayed hypotheses. There is no iid, centering, density,
or atomlessness assumption for this scalar-law statement.

Probability of the true law is essential to the numerical assertion and will
not be omitted. As noted in the source-bound regularity proposal, arbitrary
finite measures do not suffice: `ν=1024 delta_(1/32)`, `n=1`, `t=0`,
`rho=1/32` satisfy square normalization and the budget premise, but make the
middle expression `31^3/32 > 1`. No general-measure version with the same
constant will be silently substituted.

## Lyapunov must be proved, using a direct polynomial route

The following internal lemma is to be actually proved, not added as a premise
of the public theorem. It can remain private because only its application to
the genuine cutoff variable is required here:

```lean
private theorem integral_sq_cube_le_abs_cube_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ)
    (hg2 : Integrable (fun ω => (g ω) ^ 2) μ)
    (hg3 : Integrable (fun ω => |g ω| ^ 3) μ) :
    (∫ ω, (g ω) ^ 2 ∂μ) ^ 3 ≤ (∫ ω, |g ω| ^ 3 ∂μ) ^ 2
```

This lemma needs no explicit measurability premise on `g`: the two supplied
integrabilities provide the measurability of exactly the functions integrated.
It will not be assumed from its name, from a numerical check, or from an
unresolved Holder/Lp theorem.

A short proof avoids all fractional-power integrability obligations. Set
`A=integral g^2`, `C=integral abs(g)^3`, and `b=sqrt A>=0`, so `b^2=A`.
For every real `u>=0` the polynomial identity

```text
2 u^3 + b^3 - 3 b u^2 = (u-b)^2 (2u+b) >= 0
```

holds. Substitute `u=abs(g omega)` and use `abs(g omega)^2=g omega^2`.
The left comparison function `3b g^2` is integrable by `hg2`; the right
`2 abs(g)^3 + b^3` is integrable by `hg3` and the probability-space constant
function. Therefore an actual two-sided `integral_mono`, followed by linearity
and `μ(univ)=1`, gives

```text
3 b A <= 2 C + b^3.
```

Using `A=b^2` gives `b^3<=C`. Both sides are nonnegative, so squaring gives
`A^3=b^6<=C^2`. This proof also handles `A=0` and never divides by an unknown
moment. All algebraic facts are polynomial equalities/inequalities plus the
standard nonnegative square-root identity. It is an explicit proof of the
needed probability-space Lyapunov comparison.

## Instantiate the true cutoff variable without a full third moment

Inside the public proof, write only local abbreviations

```text
N = (n : R),   a = 1+t >= 1,
D = {z | abs z <= 1/a},
g(z) = if z in D then z else 0,
A = integral g(z)^2 dν,
C = integral abs(g(z))^3 dν,
T = integral (z^2 1_(D.compl)) dν,
R = truncationBudget ν n t.
```

The marked square of `g` is the indicator of `z^2` on the Borel set `D`.
Its integrability follows from `h2.indicator` (or the direct norm bound by
`z^2`), without dividing or using finite moments of another variable.
The third absolute power of `g` is exactly the marked small-third kernel
already proved integrable by `integrable_truncation_small_three ν h2 a ha`.
The tail square is integrable by the corresponding checked tail-square lemma.
Thus the internal Lyapunov lemma's two premises are proved for this actual
bounded-cutoff variable; they are not new public assumptions on `z`.

Finite cutoff-boundary atoms lie in `D`, exactly as in the checked integrals.
The exact square split and budget decomposition give

```text
N(A+T) = 1,
R = a^3 N C + a^2 N T,
A>=0, C>=0, T>=0, N>=0.
```

The first equality uses actual integrability on both pieces of the square
integral; the second is `truncationBudget_decomposition` at `t>=0`.

## Proof of the upper bound by n

Since `a>=1`, the decomposition implies `N T <= R <= rho`. Hence
`N A >= 1-rho >= 15/16 > 0`. Apply the proved cutoff Lyapunov inequality
`A^3<=C^2`. From `R>=a^3 N C>=0`, square and multiply by nonnegative `N`:

```text
N R^2 >= a^6 N^3 C^2
      >= a^6 N^3 A^3
       = a^6 (N A)^3
      >= a^6 (1-rho)^3.
```

This is exactly the rearranged upper sample-size inequality and does not
replace retained moments by variances or assumed unit-second-moment variables.
It avoids unnecessary division by `A`, `C`, or `n`.

Normalization gives `n>0` (the zero case contradicts `hnorm`) and a positive
full square integral. Once the frozen Regularity dependency is available,
`truncationBudget_pos ν n h2 hn hsecond t ht` gives the actual `R>0`.
Only then divide the displayed polynomial inequality by the strictly positive
`R^2` to obtain the public theorem's second conjunct.

## Proof of the lower bound by a^6

The already derived `R>0`, `R<=rho<=1/16` give `0<R<=1/16` and
`1-rho>=15/16`. Thus

```text
R^2 <= (1/16)^2 <= (15/16)^3 <= (1-rho)^3.
```

Multiply by the nonnegative `a^6` and divide only by the proved positive
`R^2`. This proves the public theorem's first conjunct. The final statement
is the exact weak chain in the source; no stronger inequality is substituted
for the frozen assertion.

## Dependency and implementation boundary

- Reuse the checked TruncationIntegrals definition, marked integrability, and
  exact decomposition at source hash
  `d7432b7c579c6e6e0d9980af322437941f59f8f670bebd2dd4770f6cfcf1e234`.
- Reuse Regularity's frozen positivity declaration after that independent
  author produces the dependency. Do not edit or duplicate its generic
  positivity/strict-monotonicity/limit implementation.
- After this scope freezes, the private polynomial Lyapunov proof and local
  cutoff-moment calculations are independent work that can be implemented
  without waiting for Regularity. The final public theorem can consume its
  positivity theorem when ready. No open premise or placeholder will be left
  in an accepted proof.
- The natural type `n` is unrestricted in the signature; `hnorm` itself makes
  `n=0` impossible. Zero/negative `rho` is not silently excluded by an extra
  hypothesis: actual budget positivity and `hR` exclude it.
- This unit proves the sample-size part of Lemma 3.1, not a complete C12 root
  theorem or any subsequent moment/tail estimate.

Only `drafts/c12/TruncationSampleSize.lean`, this scope, its author check
receipt, and remote `Shao/Probability/TruncationSampleSize.lean` are in this
author's lane. The coordinator froze the sole public signature and the
requirement that the internal Lyapunov lemma be proved, not assumed, before
implementation. The polynomial proof above is the route actually used. All
Lean execution was server-only and targeted, with no source changes to other
modules, shared cache writes, root-import changes, or dependency rebuilds by
this author. Independent blind review remains required for acceptance.
