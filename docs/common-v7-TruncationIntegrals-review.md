# Independent blind review: TruncationIntegrals

STATUS: CORRECT

JUSTIFICATION: the actual definition and all seventeen theorem statements
match the frozen mathematical interface; their proofs use genuine integrable
dominators and both-sided integral comparisons. The exact reviewed source also
passed the reviewer's independent targeted server check and all-declaration
transitive axiom audit described below. No critical gap or extra premise was
found. This verdict covers this integral-comparison component, not a full root
theorem or the deferred continuity/strict-increase/asymptotic results.

Review target SHA256:
`d7432b7c579c6e6e0d9980af322437941f59f8f670bebd2dd4770f6cfcf1e234`.
The local target matches this hash. Its previously independently accepted
pointwise dependency TruncationBudget matches
`70cf7e33d458b847ea94cfa5bd8dce59a9dc3cb0ef632140a0f55fca8ded71bd`.
The reviewer did not author either module, does not edit either proof, and
does not use the author's check receipt as evidence.

## Statement reconstruction before reading the scope document

From the actual declarations, set `F(z)=z^2 min(abs z,1)`. The single new
definition is `R(n,t)=n * integral F((1+t)z) dnu`, for any real `t`, natural
`n`, and arbitrary `nu : Measure R`. The measure need not be a probability,
finite, or sigma-finite measure. Every theorem below explicitly assumes
`Integrable (z |-> z^2) nu`; the three marked-kernel integrability theorems
and their integral comparisons additionally assume a positive scale.

For `a>0` write `L1_a(z)=abs z * 1_{abs z>1/a}`,
`L2_a(z)=z^2 * 1_{abs z>1/a}`, and
`S3_a(z)=(abs z)^3 * 1_{abs z<=1/a}`. These symbols abbreviate the actual
conditional expressions in the file; they are not replacement Lean definitions.

| # | Actual public theorem | Reconstructed assertion |
|---|---|---|
| 1 | `integrable_truncationF_mul` | For every real `a`, `F(a z)` is integrable under `nu`. |
| 2 | `integrable_truncation_tail_one` | For `a>0`, `L1_a` is integrable; no global first moment is assumed. |
| 3 | `integrable_truncation_tail_two` | For `a>0`, `L2_a` is integrable. |
| 4 | `integrable_truncation_small_three` | For `a>0`, `S3_a` is integrable; no global third moment is assumed. |
| 5 | `integral_truncation_tail_one_le` | For `a>0`, `a integral L1_a <= integral F(a z)`. |
| 6 | `integral_truncation_tail_two_le` | For `a>0`, `a^2 integral L2_a <= integral F(a z)`. |
| 7 | `integral_truncation_small_three_le` | For `a>0`, `a^3 integral S3_a <= integral F(a z)`. |
| 8 | `truncationBudget_nonneg` | `0 <= R(n,t)` for every real `t` and every natural `n`. |
| 9 | `truncationBudget_mono` | If `-1<=s<=t`, then `R(n,s)<=R(n,t)`. No monotonicity below `-1` is claimed. |
| 10 | `truncationBudget_scale_le_one` | For any real `t` and `0<=c<=1`, `c^3 R(n,t)<=R(n,c(1+t)-1)<=c^2 R(n,t)`. |
| 11 | `truncationBudget_scale_one_le` | For any real `t` and `1<=c`, `c^2 R(n,t)<=R(n,c(1+t)-1)<=c^3 R(n,t)`. |
| 12 | `truncationBudget_local_comparison` | If `x,t>=0` and `abs(t-x)<=(1+x)^(-1)`, then `R(n,x)/8<=R(n,t)<=8 R(n,x)`. |
| 13 | `truncationBudget_decomposition` | For `t>-1`, `R(n,t)=(1+t)^3 n integral S3_(1+t)+(1+t)^2 n integral L2_(1+t)`. |
| 14 | `truncationBudget_le_rpow_moment` | For `t>=0`, real `2<=p<=3`, and the additional actual integrability of `Real.rpow (abs z) p`, `R(n,t)<=(1+t)^p n integral Real.rpow(abs z,p)`, with real powers on both factors. |
| 15 | `truncationBudget_cutoff_tail_one` | For `x>0`, `x n integral L1_x <= R(n,x)`. The cutoff here is `1/x`, while the budget kernel uses `1+x`. |
| 16 | `truncationBudget_cutoff_tail_two` | For `x>0`, `x^2 n integral L2_x <= R(n,x)`, with the same distinction of scales. |
| 17 | `truncationBudget_cutoff_small_three` | For `x>0`, `x^3 n integral S3_x <= R(n,x)`, including the cutoff boundary on the small side. |

No theorem assumes `n>0`, a normalized second moment, or a global third moment
except the explicitly parameterized real-moment hypothesis when `p=3` in #14.
No continuity, strict increase, asymptotic divergence, normalization, or lower
sample-size theorem appears among these actual declarations.

## Scope comparison and proof review

The statement reconstruction above was written before opening the scope
document. It matches the frozen mathematical section of
`TruncationIntegrals-scope.md` for the definition and each of the seventeen
theorems: same domains, quantifiers, hypotheses, marked-event boundaries,
scales, real-power type, and constants. The scope document's author receipt
portion is excluded from the evidence for this verdict.

### Integrability under an arbitrary real measure

The four actual dominators are `a^2 z^2`, `a z^2`, `z^2`, and `a^(-1) z^2`.
Their integrability follows from the given `h2` by multiplication by a finite
real constant. There is no use of probability, finite total measure, or
sigma-finiteness. The dominated functions are Borel measurable: continuity for
`F(a z)`, and measurable strict/weak threshold indicators times continuous
absolute powers for the marked kernels. Consequently their actual
`AEStronglyMeasurable` obligations hold for the arbitrary supplied measure.

Direct checks of the pointwise domination steps:

- Lines 29-39: nonnegativity of `F` removes its norm, and
  `F(a z)<=(a z)^2=a^2 z^2` works even when `a` is negative or zero.
- Lines 41-56: on the tail, `abs z > 1/a` and `a>0` give
  `a abs z >= 1`, hence `abs z <= a z^2`; off the tail the kernel is zero.
  This proves marked first-moment integrability without a global first moment.
- Lines 58-69: the marked square is bounded in norm by `z^2` independently of
  the cutoff. The positive `ha` parameter is harmless and unnecessary for this
  one theorem; preserving it preserves the frozen interface.
- Lines 71-86: on the small region, `(abs z)^3 <= a^(-1)(abs z)^2`, with
  `a^(-1)>=0`; off it the kernel is zero. This proves the actual marked third
  moment is integrable without assuming the full third moment.

Thus the theorem statements and proofs do not exploit the zero value assigned
to a nonintegrable Bochner integral. Although the standalone definition of
`truncationBudget` is total, each accepted comparison is explicitly in the
integrable regime established from `h2` (and additionally `hp` only in #14).

### Both sides of every integral comparison

All thirteen `integral_mono` calls were inspected directly:

- Lines 92, 101, and 110 supply the appropriate marked-kernel integrability
  multiplied by its scale, and the independently proved integrability of `F`.
- Line 121 supplies both the zero function and `F`; the zero function's
  integrability is itself obtained from a known integrable function.
- Line 130 supplies both scaled `F` functions for monotonicity.
- Lines 142, 146, 164, and 168 supply the scaled `F` function on both sides,
  including its appropriate constant powers. Nonnegative `n` is multiplied
  only after the valid integral comparison.
- Line 271 supplies integrable `F` and the genuinely integrable scaled
  real-power kernel `hpmul`.
- Lines 287, 298, and 309 supply both `F(x z)` and `F((1+x)z)`.

The decomposition's separate `integral_add` at line 252 supplies integrability
of both weighted marked kernels. Its pointwise identity comes from the
previously accepted dependency at the permitted positive scale `1+t`; it
does not conceal the integral decomposition in an unproved new hypothesis.

### Local constants, scale sign, and the real exponent

For local comparison, the proof first obtains `1+x>0` and
`abs(t-x)<=1`. Writing `c=(1+t)/(1+x)`, nonnegativity of `t` and the bound
`x<=t+1` give `1+x<=2(1+t)`, hence `c>=1/2`. Nonnegativity of `x` and
`t<=x+1` give `1+t<=2(1+x)`, hence `c<=2`. These are the actual ratio bounds
proved at lines 192-197; no inference from the reciprocal bound alone is
missing. The identity `c(1+x)-1=t` uses the explicitly nonzero denominator.
The two scale cases then give `c^3>=1/8` or `c^3<=8`, with their complementary
square bounds. Every coefficient comparison uses the already proved
nonnegativity of `R(n,x)`. The proof never divides by the budget, so zero
budget is covered.

The global scale theorems allow arbitrary real `t`, as frozen. This is valid:
the accepted pointwise scale lemmas apply to the arbitrary real argument
`(1+t)z`, and their external scale `c` is nonnegative. Neither proof assumes
that `1+t` is positive where none is stated.

The moment theorem at lines 258-281 quantifies `p : R`, uses `Real.rpow` in
its hypothesis and conclusion, and applies the accepted real-exponent bound
`F(w)<=abs(w).rpow p`. Its product identity uses nonnegative bases and
`Real.mul_rpow`. The scaled moment is shown integrable from the actual `hp`
before integration. The endpoint values `p=2` and `p=3` remain included, with
their stated integrability obligations; there is no replacement by natural
powers or a hidden global third-moment premise for the other theorems.

### Boundary attacks

- `n=0`: all budget expressions and weighted bounds are zero; no proof divides
  by `n`, cancels it, or assumes it is positive.
- `t=-1`: the kernel is `F(0)=0`, so the budget is zero. Nonnegativity and the
  two scale laws cover this directly. Monotonicity permits its left endpoint
  `s=-1`. The decomposition explicitly requires `t>-1`, so it does not use
  the singular cutoff `1/(1+t)` there.
- `c=0` in the small-scale theorem gives transformed time `-1`; `c=1` in both
  scale theorems preserves time. There is no forbidden scale division.
- The marked small region is `abs z<=1/a`; the tail is the strict complement
  `1/a<abs z`. The decomposition counts a joining-boundary atom once, on the
  small side. No atomlessness is assumed.
- In the final three bounds the marked cutoff is truly `1/x`, not `1/(1+x)`.
  They first use the accepted pointwise bound at scale `x>0`, then compare
  `F(x z)` with `F((1+x)z)`. This is exactly the frozen source connection.

## Independent designated-server evidence

The reviewer independently ran the following command after checking source
hashes on the server; it checks only this target source and does not emit an
output `.olean` or rebuild the already accepted pointwise dependency:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-c12
sha256sum Shao/Basic/TruncationBudget.lean Shao/Probability/TruncationIntegrals.lean
taskset -c 0-3 lake env lean Shao/Probability/TruncationIntegrals.lean
```

The remote hashes exactly matched the two reviewed hashes at the top of this
report. Exit code: 0. The sole diagnostic was the unused `ha` binding in the
marked-square integrability theorem at line 59, for the mathematical reason
explained above. It is not a proof gap or a requested frozen-signature change.

In the same server request, a separate `lake env lean --stdin` environment
audit imported the target and Lean, applied `Lean.collectAxioms` to all eighteen
owned public declaration-name prefixes and the module-private prefix, and
rejected any axiom outside the standard whitelist. Result: exit 0,
`AUDITED_DECLARATIONS 19` (definition, seventeen theorems, generated defining
equation). Every declaration uses only
`[propext, Classical.choice, Quot.sound]`.
Independent `#check @...` outputs for local comparison and the moment theorem
confirmed the arbitrary measure, real `p`, explicit integrability, exact
constants, and absence of positive sample-size assumptions.
The reviewer's source-token scan found no `sorry`, `admit`, new `axiom`,
`unsafe`, or `native_decide` occurrence.

No proof source, shared import, lock, audit script, or cache was edited during
this review. All Lean execution occurred on the designated server. This
acceptance does not certify that `nu` has already been constructed as the
source normalized probability law, nor does it close the deferred analytical
components or any complete C12 root group.
