# Actual probability Spitzer: author completion

Status: all five root-frozen heads implemented, server kernel and all-owned
transitive-axiom gates PASS; independent complete review is pending. This is
classic Spitzer identity formalization, with no novelty claim. The workflow is
math-theorem, not math-ultra. No child agents were created.

Exact source: `Shao/Probability/SpitzerLaplace.lean`, 316 LF-only UTF-8 lines,
15267 bytes, SHA256
`2faaf41caf7b0025e7171b764b468803688802f0177f02bfa0d4645a7c4890fb`.
It remains uncommitted so root can publish its coordinated common-source batch.
No other owner's implementation, root imports, curated snapshot, or OQ4 adapter
was edited. The source and installed object of accepted SpitzerFinite retain
their original qualified hashes.

## Probability argument and boundary coverage

1. `spitzer_integral_reorder` uses the inverse of the actual measure-preserving
   coordinate equivalence for a fixed permutation. It proves the integral
   equality for every real observable, so it also applies to the cut observable.
   The first frozen theorem specializes it to the actual maximum integrand.
2. The exact coordinate equivalence `Fin k ⊕ Fin (n-k) ≃ Fin n` identifies the
   actual head/tail map with a composition of two measure-preserving measurable
   equivalences. `spitzer_head_tail_integral` then uses `integral_map` and
   `integral_prod_mul`, and the accepted literal `head_prefixSum` identity.
   The proof includes `n=0`, `k=0`, and `k=n` through these finite equivalences;
   no nonempty-index restriction occurs.
3. `spitzer_integrable_cut` supplies true measurable bounded integrability. In
   the recurrence proof, both maximum and cut observables are integrable after
   every fixed permutation. The independently qualified all-real finite cut
   identity is integrated, finite sums are interchanged with the integral,
   permutation invariance and head/tail factorization compute each term, and
   the positive real cardinality of the permutation type is cancelled. Its
   cardinality is not assumed to equal a factorial. A final finite-index
   conversion gives the exact frozen recurrence. The `j=n` empty tail survives.

## Analytic argument

The helper `spitzer_summable_norm_coeff` proves actual absolute convergence
for bounded coefficients at every `|x|<1`, including negative `x`. Each of the
two derivative helpers works on `(-r,r)` with `r=(|x|+1)/2`. The derivative
majorants are `(n+1)r^n` and `r^n`, proved summable from the pinned geometric
APIs. The series converge at zero, and the full open-set termwise-derivative
theorem establishes their derivatives throughout that interval.

The bounded-recurrence theorem uses proof-local actual real functions
`A(x)=a(0)+Σ x^(n+1)a(n+1)` and
`W(x)=Σ x^(n+1)b(n+1)/(n+1)`. The summable shift identity identifies `A` with
the existing actual `laplaceG`. The norm-summable Cauchy-product theorem and
the supplied recurrence prove `W'(x)A(x)=A'(x)`. The product
`A(x)exp(-W(x))` therefore has derivative zero on `(-1,1)`, and the mean-value
constant-function theorem identifies its values at `s` and zero. Its zero
value is exactly one. Exponential multiplication gives `A(s)=exp(W(s))`,
where `W` is literally the existing `laplaceW`.

The final theorem supplies the actual integral bounds, actual length-zero
identity, and the newly proved actual recurrence. Its only mathematical
inputs are a real probability law, `L>0`, and `0<s<1`. It has no SP, CDF,
centering, moment, symmetry, atomlessness, or recurrence assumption.

## Exact evidence and review handoff

The successful full source-bound check is `step-010`; its first whole-source
success emitted object SHA256
`86fd91edc877ed88c94de93f109bb92ee01a5b74e36f8eb946714f98766d2f9b`.
The identical object is installed in the author's own build path and archived
in `final-010`. Earlier failures remain in separate immutable step directories;
each direct exit was captured before displaying diagnostics. No accepted
predecessor was rebuilt. All Lean commands used the shared root-heavy lock,
CPU10–13, `-M8192 -j4 -DautoImplicit=false`.

The reused existing owned-audit implementation selects by actual target module
ownership. It reports 22 actual owned constants, all 22 theorems including
private/generated declarations, zero definitions, and the five frozen public
heads. All actual types are printed in the server audit output; there are no
definition values. Every owned declaration's transitive axioms are contained
in `propext`, `Classical.choice`, `Quot.sound`. Audit direct Lean exit is zero.

Remote evidence root:
`/root/rivermind-data/shao-lean-20261021/artifacts/common-spitzer-laplace/`.
The exact successful source, object, commands, stdout/stderr and direct exits
are in `step-010` and `final-010`; actual types and all-owned map are
`final-010/owned-audit.stdout` and `final-010/owned-audit.json`.
See the compact `final-author-receipt.json` for all exact hashes.

Source write authority is released for root's one fresh, qualified complete
source-to-statement/proof/type/axiom review. A repeat compilation of unchanged
accepted sources is unnecessary. Root must preserve the final independent
review boundary; author kernel success is not independent acceptance.

This production closes only its frozen Spitzer interface after acceptance.
Original C1/C2, survival/CDF, and all other original root groups remain OPEN.
No next source-bound dependency is authorized to this author beyond its five
frozen heads. The next required dependency is root's independent final review.
