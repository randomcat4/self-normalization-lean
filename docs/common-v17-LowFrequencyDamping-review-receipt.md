# LowFrequencyDamping author implementation receipt

Status: AUTHOR IMPLEMENTATION COMPLETE; awaiting fresh independent final proof
review. This is an implementation-author receipt, not an independent verdict.
Author: `/root/deletion_inequality` (authorized GPT-6.1-sol, xhigh).
Date: 2026-10-21.

## Frozen interface and exact source identity

The original frozen scope remains byte-for-byte unchanged:

```text
drafts/c12/LowFrequencyDamping-next-scope.md
SHA256 4e65222b68f8d3e75065b9f0064bdc0ac90dc6545289c60ab05f6e9fff78cb8a
```

The independent declaration review was CORRECT with no signature revisions:

```text
drafts/c12/LowFrequencyDamping-declaration-review.md
SHA256 e05746a95f83393ae5304bf91e97b9b9f1d6808a5ac1e7c0dd94a9569d6b994c
```

Local and server implementation source bytes agree:

```text
SHA256 ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65

C:/game/shao lean/drafts/c12/LowFrequencyDamping.lean
/root/rivermind-data/shao-lean-20261021/workspaces/lead-c12/Shao/Probability/LowFrequencyDamping.lean
```

Only the new owned Lean source and this separate author receipt were written.
No frozen scope, old mathematical source, cache, lock or common interface was
modified. All Lean compilation and API checks ran on the designated server.

## Public delivery: zero public definitions, six frozen theorems

| Declaration | Source line | Result |
|---|---:|---|
| `quadratic_pair_square_moment` | 58 | Genuine product-law pair square is integrable and has integral `2 Var(id;ν)`, retaining the actual squared mean. |
| `quadratic_pair_tail_square_bound` | 137 | Actual strict bad-pair mask is integrable and its integral is at most `8m3/d`. |
| `quadratic_pair_retained_square_lower` | 158 | Actual weak retained-pair mask is integrable and retains at least the actual variance under the stated cutoff moment budget. |
| `quadraticChar_gap_identity` | 233 | True norm-square gap equals the actual paired cosine-gap integral; it needs no moment assumption. |
| `quadraticChar_local_gap` | 322 | Genuine spectral gap `V u²/16`, derived from actual pair truncation and the frozen local frequency inequalities. |
| `quadraticChar_lowFrequency_damping` | 375 | Actual simultaneous `±u` bound with `κ=1/128` and `c=1/32`. |

All six public signatures are unchanged. The law `ν` is fixed and real;
it is not replaced by a law chosen to be centered. Analytic moment input
is the actual raw `Integrable (fun a => |a|^3) ν`. Positive variance is
required exactly where frozen. No support, centering, symmetry, fourth
moment, nonzero-frequency, variance-retention or target-damping premise
was added. Private helpers and the literal private exponential phase are
implementation details, not a new public law or characteristic function.

## Actual integrability and pair moment proof

The probability-space dominator `1+|a|³` supplies genuine first/square
integrability from `h3`. On the real product measure `ν.prod ν`, the pair
square is dominated by `2a²+2b²`. The actual cross product is integrable
by `Integrable.mul_prod` on the two actual L1 coordinates before its
integral is factored.

Expanding the true pair square and integrating gives

```text
E(A-A')² = 2 E A² - 2(E A)² = 2 Var(A).
```

The actual raw/centered variance bridge comes from `variance_eq_sub`
with the derived L2 input. No equality of raw second moment and variance,
or zero mean of the conditional increment, is used.

The strict bad event is `d<|a| or d<|b|`; the weak good event is
`|a|≤d and |b|≤d`. Each integrand is the actual indicator of the pair
square on a proved measurable set, hence actually integrable. Equality
atoms remain in the good event. The exact good/bad integral split is
proved pointwise and uses both established integrabilities.

For `d>0`, the pointwise tail proof is

```text
d(a-b)² ≤ (|a|+|b|)³ ≤ 4(|a|³+|b|³)    on the strict bad event.
```

The marginal cube sum is genuinely integrable. Its product-law integral
is `2m3`, so the tail integral is at most `8m3/d`. The frozen moment budget
then bounds that tail by `V`, and the full pair moment `2V` leaves at
least `V` on the good event. The retained theorem uses its positive `V`
premise only through valid positive-denominator comparisons; it never
divides by an unknown sign.

## Actual characteristic gap, spectral gap and exponential conversion

Every real phase `exp(i(ua+va²))` has norm one and is actually integrable.
The product with its full complex conjugate is also genuinely integrable
on the actual product measure. Product integration, `integral_conj` and
`integral_re` identify its real part with the squared norm of the original
`quadraticChar`.

The exact paired phase is

```text
(a-b)(u+v(a+b)).
```

The proof conjugates the entire phase, not merely the linear frequency;
it never asserts `φ(-u,v)=conj(φ(u,v))`. The cosine-gap integrand is
bounded between zero and two and actually integrable, so subtracting its
integral from one is justified even without moments.

The private small-angle proof derives `t²/4≤1-cos t` for `|t|≤1` from the
existing actual sine remainder and half-angle identity. It uses no
division by `t`. On the actual retained pair event, the local frequency
inequalities imply

```text
|u+v(a+b)| ≥ |u|/2,
|(a-b)(u+v(a+b))| ≤ 3d|u| ≤ 1.
```

Thus the pointwise retained cosine gap is at least `u²(a-b)²/16`.
Outside the retained event it is still nonnegative. Both comparison
functions are integrable before monotonicity is applied. Combining the
proved retention result with the exact norm-square identity yields the
actual spectral gap, rather than taking it as input.

For the final ratio domain, `m3>0` is derived from positive variance:
if the actual nonnegative integrable cube had zero integral, the cube
would vanish almost everywhere, hence `id=0` almost everywhere and the
actual variance would be zero. This establishes `γ=m3/V>0` and
`d=16γ>0` before division or multiplication of frequency inequalities.
The fixed final domain then proves, rather than assumes,

```text
8m3 ≤ dV,
|u|d ≤ 1/8 ≤ 1/3,
4|v|d ≤ |u|/2 ≤ |u|.
```

After the genuine gap `δ=Vu²/16`, the scalar inequality
`1-δ≤exp(-δ)` and nonnegative squares give the actual norm bound
`exp(-δ/2)=exp(-Vu²/32)`. Negative `u` satisfies the same absolute
frequency inequalities and has the same square. No step divides by `u`
or `v`; the origin and both signs are included in the same actual proof.

## Exact server verification

After sourcing `/root/rivermind-data/shao-lean-20261021/activate.sh` and
then changing to the assigned `workspaces/lead-c12`, the final exact-source
targeted check was:

```text
taskset -c 0-3 lake env lean \
  -o .lake/build/lib/lean/Shao/Probability/LowFrequencyDamping.olean \
  Shao/Probability/LowFrequencyDamping.lean
```

Result: **exit 0, stdout empty, stderr empty**. No warning was suppressed.
Only this target's own build artifact was produced. There was no broad
library build, dependency rebuild, cache acquisition or cache mutation.

A separate server `lake env lean --stdin` import checked all six public
signatures and printed each one's transitive axioms. Every public theorem
reported only

```text
[propext, Classical.choice, Quot.sound]
```

The audit also enumerated all six public name prefixes/exact names and
the new module's private prefix, including generated internal declarations,
and ran `Lean.collectAxioms` with a failing whitelist check:

```text
AUDITED_NEW_DECLARATIONS 30
```

It separately audited these actual semantic dependencies:

```text
Shao.Probability.quadraticChar
ProbabilityTheory.variance
ProbabilityTheory.variance_eq_sub
ProbabilityTheory.variance_congr
MeasureTheory.integral_prod_mul
integral_conj
integral_re
Complex.exp_conj
Complex.mul_conj
Complex.normSq_eq_norm_sq
Real.abs_sub_sin_le
Real.sin_sq_eq_half_sub
Real.one_sub_le_exp_neg
MeasureTheory.integral_eq_zero_iff_of_nonneg_ae

AUDITED_SEMANTIC_DEPENDENCIES 14
```

All fourteen had only the accepted three axioms. Audit result: **exit 0,
empty stderr**. The server prohibited-token scan for `sorry`, `admit`,
`axiom`, `unsafe` and `native_decide` found no matches in the new source.
The source sets `autoImplicit false` and has no custom axioms.

An intermediate transport request failed before dispatch with
`operation_may_have_started=false`; its safe retry performed the check.
The final targeted compilation and separate audit above both actually ran
and succeeded. No failed relay response is being counted as a proof check.

## Preserved frozen inputs and source provenance

The server rechecked these protected source hashes, unchanged:

```text
QuadraticCharacteristic.lean
8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5

QuadraticCharacteristicPower.lean
5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8

FiniteIIDMoments.lean
d2417f73424ea90a13edb10bdad267d638d66fec432c3107362a2d0246fe2bfa
```

Only `QuadraticCharacteristic` is a project import of this new module;
the other protected sources were not edited, imported as surrogate
premises, rebuilt or copied. The actual pair calculation uses cached
Mathlib product/variance interfaces.

The source-bound assertion is `h:supp:lowfreq` at
`supplement.tex:2371–2377`, with its true proof at `3155–3192`.
Original source SHA256s remain those in the frozen scope:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

## Scope boundary and next action

This is a genuine fixed-law real low-frequency damping input. It can be
instantiated with the actual conditional increment law once its true
probability, raw third integrability and positive variance are supplied.
The explicit `h_x=ε/(1+x)` law transport/rescaling bridge described in the
frozen proposal has not been implemented here. In particular the earlier
`1/x` retained law has not been silently substituted for the source law,
and a global third moment of the original untruncated variable was not
added. The conditional mean was never set to zero.

Still open: that source-specific `h_x` bridge, the combined low-frequency
odd-power derivative table, law-adapted high-frequency noise/damping,
clock probabilities, complex tilting, Fourier inversion/oscillatory
integration, and smoothing/defect payment back to the strict CDF test
`1_{q>0, |w|<t sqrt q}`. This module does not change its boundary or the
zero-energy convention and does not close the full C1/C2 comparison.

Minimum next action: fresh independent final proof review of the exact
source hash above, then coordinator integration if accepted.
