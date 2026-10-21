# GaussianTail author receipt

Status: IMPLEMENTED, SERVER CHECKED, TRANSITIVE AXIOM AUDIT PASSED;
PENDING FRESH INDEPENDENT PROOF REVIEW. This is the author's execution
receipt, not an independent correctness verdict.

## Frozen objects and ownership

- Frozen proposal: `drafts/c12/GaussianTail-next-scope.md`, SHA256
  `26a01989f5b8169ac37f44f543b3f0312a7e668bd26562e221f64d5c60a6dbef`.
  Its bytes and original status text remain unchanged. The coordinator
  froze it after `GaussianTail-statement-review.md` returned CORRECT.
- Local source: `drafts/c12/GaussianTail.lean`.
- Server source: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-c12/Shao/Probability/GaussianTail.lean`.
- Frozen source SHA256, independently read locally and on the server:
  `f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922`.
- The author wrote only this new source and receipt. No old source,
  shared import, scope, pin, audit program or package/cache was changed.

## Exact public interface

The two definitions and seven theorems have exactly the frozen names in
namespace `Shao`; there are no substitute aliases:

```text
standardNormalDensity
standardNormalTail
standardNormalTail_representation
standardNormalTail_basic
standardNormal_derivatives
standardNormal_mills_bounds
standardNormalTail_ratio_bound
standardNormalTail_local_comparison
standardNormalTail_deletion_comparison
```

In particular the derivative and Mills names intentionally use the frozen
`standardNormal_...` spelling; the other tail theorem names use
`standardNormalTail_...`. The server `#check @...` outputs match every
frozen public signature. There are 10 private proof lemmas and 10 generated
declarations, giving 29 new audited declarations in total.

## Actual mathematical construction

The definitions use `gaussianPDFReal 0 1` and the real mass of the strict
tail of `gaussianReal 0 1`. Actual Gaussian singleton-nullity proves the
weak-tail bridge; finite probability complement and `cdf_eq_real` prove
the CDF bridge. Actual nonnegative density integration supplies the third
representation. Positive density has full support; the nonempty Lebesgue
half-line and true density integrability prove strict positive tails.
The actual Gaussian negation-map law supplies reflection, hence the half
tail at zero and the upper range bound one.

The density derivative is computed from its genuine exponential formula.
Global density integrability and `integral_Ioi_sub_Ioi'` give the oriented
interval formula for the tail, including negative endpoints. FTC-1 proves
the true tail derivative at every real threshold.

For nonnegative `x`, the proof-local functions are
`f(t)=phi(t)/(1+t)` and
`g(t)=phi(t)*(t^2+t+1)/(1+t)^2`. Their weight is between `3/4` and one
on the required half-line. `Integrable.mono'` proves `g` genuinely
integrable there using its measurable formula and pointwise norm bound by
the integrable density. Its negative is genuinely integrable as required
by `integral_Ioi_of_hasDerivAt_of_tendsto'`. The derivative is established
on all of `Ici x`. The density tends to zero from the explicit quadratic
exponential and `f` tends to zero by a nonnegative squeeze. Half-line FTC
therefore gives the exact weighted integral identity. Both subsequent
integral comparisons use real integrability proofs for both sides.

This proves the frozen Mills constants `1` and `4/3`, including `x=0`;
strict positive tails justify the hazard bound. The ratio theorem uses the
exact exponential density ratio. The local comparison applies a genuine
derivative bound to `log` of the positive tail on a nonnegative convex
interval and exponentiates a log-difference bound of two. The deletion
comparison uses `y^2=x^2-j`, `y>=x/2` and the ratio bound, relaxing `8/3`
to three. No division by `x`, `j` or `y` occurs. The hypotheses remain
closed at zero and at `j=x^2/2`.

These functions are source `PhiBar=1-Phi` at main.tex:169–171. The Mills
domain matches supplement.tex:1027–1029; local comparison covers
main.tex:457–465 and 807–812, and the deletion comparison matches
supplement.tex:205–211. The source hashes remain those in the frozen
proposal. This module does not close Berry--Esseen, a sample Gaussian
comparison, Brownian maximum, clock concentration or full C1/C2.

## Server execution evidence

All Lean execution used only the designated server and worktree, with
four-core affinity. No local Lean installation or execution was used.

Pinned versions reported on the server:

```text
Lean 4.36.0-rc1, c9afcddf514a6772bd4d649f7cfc04eff0b9f15e
Mathlib 807d3836b165983210ee2ecf3cd28f239436949c
```

Final source-target check:

```sh
source /root/rivermind-data/shao-lean-20261021/activate.sh &&
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-c12 &&
taskset -c 0-3 lake env lean \
  -o .lake/build/lib/lean/Shao/Probability/GaussianTail.olean \
  Shao/Probability/GaussianTail.lean
```

Actual remote result: `exit_code=0`, `stdout=""`, `stderr=""`.

A separate fresh `lake env lean --stdin` imported the produced module,
ran `#check @...` for both definitions and all seven public theorems,
ran `#print axioms` on all seven public theorems, and traversed the entire
environment for every name beginning with either
`Shao.standardNormal` or `_private.Shao.Probability.GaussianTail.`.
The traversal used `Lean.collectAxioms` and threw an error for any axiom
outside `propext`, `Classical.choice`, `Quot.sound`.

Actual remote result: `exit_code=0`, empty stderr;
`AUDITED_DECLARATIONS 29`. Every public theorem depends only on the three
whitelisted axioms. Every private, definition-equation and generated
simplification declaration was included and also passed.

Final remote source hash and forbidden-token scan were a separate command:

```sh
sha256sum Shao/Probability/GaussianTail.lean
if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|unsafe|native_decide)([^[:alnum:]_]|$)' \
  Shao/Probability/GaussianTail.lean; then exit 41; else
  echo FORBIDDEN_SCAN_CLEAN
fi
```

Actual remote result: `exit_code=0`, empty stderr, the frozen source hash
above, and `FORBIDDEN_SCAN_CLEAN`. Local SHA256 recheck also confirmed the
proposal's original frozen bytes.

The shared broker had transient pre-start `operation_failed` responses
during early read-only probes; all reported
`operation_may_have_started=false`. A permitted native SSH/SCP fallback
was used briefly, and no started command was replayed blindly. The final
upload, target check, complete audit and hash/scan all succeeded through
the configured `tools/server.py` broker. There was no cache fetch/build or
full-library build.
