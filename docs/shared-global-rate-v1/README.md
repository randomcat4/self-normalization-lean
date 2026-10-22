# BivariateLegendre v1 — author handoff

Status: author target compilation and full module-owner type/axiom gates PASS.
Independent complete-proof review remains required. This is not a root-closure
claim, an independent review, or publication approval.

The exact three definitions and four theorem signatures are frozen at SHA256
`0b2bafc5965881e4ada01f8ebbeafc8d705ffc78980db711a29fd93dc10d8b81`.
`source-declarations-v1.txt` is reconstructed from the final production source
and checked byte-for-byte against that snapshot. The only scope repair to the
proposal is the required anonymous `end` before `end Shao.Probability`.
No definition body, theorem binder, assumption or conclusion was changed.

The source is `Shao/Probability/BivariateLegendre.lean`. Its imports contain no
OQ3 module. The domain consists of the actual integrable exponential tests,
the logarithm accepts only that domain subtype under `NeZero`, and each finite
real test is embedded into `EReal` before the complete supremum is formed.

## Proof structure

1. `bivariateLogMGF_spec`: the subtype property supplies exponential
   integrability; `MeasureTheory.integral_exp_pos` supplies strictly positive
   finite partition integral; `Real.exp_log` gives exact recovery.
2. `bivariateLegendreRate_test_le`: the test at the supplied domain element is
   below its defining indexed supremum by `le_iSup`.
3. `bivariateLegendreRate_eq_of_attained_bound`: `iSup_le` and the real-to-EReal
   order equivalence give the global upper bound. The attained domain element
   and theorem 2 give the reverse bound; antisymmetry gives equality.
4. `bivariateLegendreRate_unique_minimizer_of_tests`: theorem 3 gives the
   candidate value. For every distinct point in D, its separating finite real
   test embeds strictly above that value and is at most the same global rate
   by theorem 2. Thus the candidate is minimal and the only point with equal
   rate. The equal-point branch is reflexive.

The membership binder `hz₀` is preserved exactly despite an unused-variable
linter warning: the frozen public contract explicitly records candidate
membership. An empty exponential domain cannot supply `θ₀`; points with rate
`EReal.top` cause no subtraction, conversion to real, or finiteness assumption.
The proof does not require probability, finite measure, an open domain,
continuity, differentiability, compactness, or a uniform separation gap.

## Mechanical evidence

All Lean execution took place on the designated server after sourcing
`activate.sh` and then changing to this worktree. Every Lean command used
CPU10–13, `-M8192 -j4 -DautoImplicit=false`; heavy commands were sequential.
Lean actual version is 4.36.0-rc1, commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`, with the pinned mathlib commit
`807d3836b165983210ee2ecf3cd28f239436949c`.

`target-03` compiled the full final module to its own olean and returned 0.
`audit-02` imports that object and enumerates constants by the exact module
owner, rather than a public-name prefix. It therefore covers any private or
generated constants as well. It found 3 definitions, 4 public theorems,
4 total theorems and 7 total module-owned constants: no additional hidden
constants. For every owner it exports the complete actual type and universe
parameters, rejects any owned axiom and traverses all axiom dependencies.
Only `propext`, `Classical.choice`, and `Quot.sound` occur.

`actual-declarations.txt` contains these actual exported types and axiom lists;
`author-receipt.json` and `MANIFEST.sha256` bind source, frozen declarations,
audit source, checked object, all attempts and raw server logs. The binding
script is a lightweight byte/hash/status check and runs no Lean.

## All attempts, including failures

| Attempt | Exit | Result |
|---|---:|---|
| target-01 | 127 | `/usr/bin/time` was unavailable; Lean did not start. |
| target-02 | 1 | Anonymous `noncomputable section` needed its closing `end`; four proof bodies were already elaborated and remained unchanged. |
| target-03 | 0 | Final complete production module accepted. |
| audit-01 | 1 | Unsupported `pp.maxDepth` output option; enumeration completed but this attempt is not counted as a passed gate. |
| audit-02 | 0 | Corrected audit configuration accepted; complete module-owner gate passed. |

Each attempt has the complete input source, command, start/end time, exit code,
stdout and stderr under `attempts/` on the server. Raw stdout/stderr logs and
copied background proposal/review inputs are server-only; their absolute paths
and SHA256 values appear in the receipt. Git retains the module, frozen
declarations, concise receipt, actual-type export, audit source and full attempt
source snapshots. No successful unchanged check was repeated.
The frozen `hz₀` linter warning and inherited mathlib local-change warning are
retained. No cache, package source, version pin, root import, global manifest,
integration-v37 working file or external process was changed by this author.

The author has handed CPU10–13 back to root and will run no further Lean checks.
Root must arrange a fresh independent complete-proof review before integration.
No KL, derivative, Hessian, far-region probability bound or original OQ3 root
closure follows from this module alone.
