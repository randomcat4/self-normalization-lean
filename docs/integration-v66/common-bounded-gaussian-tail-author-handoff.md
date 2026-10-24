# Bounded Gaussian tail producer handoff

Author unit complete. Server kernel and actual all-owned-type/transitive-axiom audit PASS; independent complete review remains pending. Author source write authority is released, with no in-flight command or target Lean/audit process.

## Exact bytes and Git

- Branch: `feat/common-bounded-gaussian-tail`.
- Parent: `bf22cc907e5c494a5c7e81899689e3e83093606d`; parent tree: `4986c07b8491c28a101d6610f647e71007c2fe2e`.
- Source-only commit: `d32ac06685132eeae5534cf3603ac5bcc6bc73a5`; tree: `aa6ad1430c5a92fe7bbbcb300fb339b57e336212`.
- Sole committed path: `Shao/Probability/BoundedGaussianTail.lean`. Unrelated untracked BerryEsseen, BoundedQuadraticTilt and SourceFourierTestKernel source references were untouched and not staged. No push, PR or merge.
- Source SHA256: `876559b2921ffe0e23c8c3a2c55d00c458985ace6036de4b8bc7f6a6aa24f4bd`; 126651 bytes, 2509 lines, UTF-8 without BOM, LF only.
- First whole-source two-public PASS: `check031`, direct rc 0. Same-invocation object SHA256: `8b618278b77c7dd6dc43be42a207aebd18f6a5fb3092ab9fe217e1bdd736d098` (7141352 bytes). Both `check031-source.lean` and `check031.olean` remain immutable on the server. Zero producer reruns after that first full PASS.
- Freeze SHA256 `9b6cdb76bf53bdf5ce82889dc91bdb959cd1fd72d09e63e0ccce47023206b8e0`; frozen complete-header file SHA256 `616bdf54381c4a7f6e7a181b50d5bdea82a67cad0402d94ae235b9ed7296cfe7`. The two complete public heads match the frozen candidates after whitespace normalization.

## Mathematical scope

Exactly two public theorems are introduced, with the existential positive constant chosen after D and before every law, k, u or b. All explicit large constants are proof-local lets. There are no global or private definitions.

1. `bounded_deterministic_wall_gaussian_upper` (line 1426): actual iid finite-path upper-maximum event, raw total second moment v in [1/4,4], support bounded by 1/u, controlled possibly nonzero mean and absolute third moment, all 0<=b<=3u; upper bound C times the genuine normal tail at b/sqrt(v).
2. `bounded_random_denominator_gaussian_upper` (line 2319): actual `Shao.upperCrossing hk u`, raw total second moment in [1/2,2], the same support/mean/third-moment controls; upper bound C times the genuine normal tail at u. All atoms and the entire zero-energy set Q=0 are included. No mean-zero, atomless, or positive-energy assumption was added.

The source follows Section 3 of the original proof candidate (SHA256 `409a6fc57a53802acae9ce50a3d3c035972dfc12fa099a48c742bfcc2696abce`). Review must cover the full source, frozen public statements and all actual types, including private/generated declarations:

- Lines 15-249: bounded integrability, raw/centered moment budgets, small-u probability bound, real BE interval estimate.
- Lines 250-720: finite first-crossing event partition, actual prefix/suffix independence, empty suffix, Chebyshev/BE completion and correction a. Positive variance is proved in the large-u branch, not inserted into either public head.
- Lines 721-1425: exponential Taylor/log normalizer, real finite-product inverse tilted density, weighted half-open-bin geometric tail, linear-tilted centered moments and BE, endpoint estimate, Mills/prefactor comparison and scalar bounds. The reciprocal-square-root variance form of the interval constant is used; it is mathematically the same bounded-total-variance estimate.
- Lines 1426-1601: deterministic-wall assembly.
- Lines 1602-2075: genuine square-tilt covariance/weight/moment bounds, raw-second monotonicity, total fourth moment, tilted-law parameter budgets. The tilted raw total second moment is proved in [1/4,v], and the enlarged moment budget is `(1+16*exp 8)*D`.
- Lines 2076-2318: actual energy-layer Radon-Nikodym comparison, Gaussian layer comparison and finite geometric sum, explicit finite floor-energy cover, and separate lowest layer. The geometric proof uses a stronger convenient exp(-3) series, then pays the originally selected larger constant.
- Lines 2319-2509: random-denominator assembly from high, finite middle and lowest energy sets. The lowest set includes all Q=0 samples.

The original coarse CDF pullback, single-deletion transport, weighted contraction, original-law CDF tail, and the C1/C2 roots remain OPEN. This unit proves only the two bounded auxiliary-law Gaussian producers.

## Kernel and actual-owner evidence

`check031-exit.json` binds the first full source/object/log/rc, pinned Lean/mathlib versions and server resource flags. All checks ran only on the designated server after activation, CPU 10-13, shared root-heavy lock, -M8192, -j4, autoImplicit false and source Elab.async false. No heartbeat/resource increase or old dependency recompile was used. Failed snapshots/logs/direct rc for checks 001-030 remain on the server; check030 was the first complete two-public attempt and failed, before the final correction and successful check031.

`bounded-gaussian-tail-owned-audit.json` selects constants using the actual native module owner, including private/generated declarations. `actual-owned-types.json` contains all 76 complete actual types. There are 76 owned theorems: 2 public, 48 explicitly private source helpers, and 26 generated theorems. There are zero definitions and hence zero definition values to dump. Recursive `Lean.collectAxioms` for every owned constant uses only `propext`, `Classical.choice`, `Quot.sound`. Actual `⋯`, `…` and literal `...` scans are all zero. Pretty-print flags include pp.all, pp.deepTerms, pp.proofs and pp.maxSteps 10000000.

Audit native attempts = 2; pre-owner import failures = 1; successful owner enumerations = 1. The first attempt `audit.log`/`audit.rc=1` failed during import because the private top-level Shao execution view lacked dependency references; it audited no declaration. The root then explicitly authorized mirroring the 10 activation-provided exact read-only object symlinks in that private output view. `audit-reference-view.json` binds every referenced object hash. No object was copied, no cache/shared dependency was written and no producer was rerun. The second attempt `audit002.log`/`audit002.rc=0` produced the sole successful owner enumeration. `audit-exit.json` retains both outcomes and binds the successful full types, report and log.

Full logs, binaries and immutable source snapshots stay under `/root/rivermind-data/shao-lean-20261021/outputs/common-bounded-gaussian-tail` on the server. Only compact receipts, the new complete source/types and audit source were retrieved locally.

## Release and next action

`writer-release.json` records no target Lean/audit process and no in-flight command. Author makes no further source edits. Parent should assign the fresh qualified complete source-to-statement/proof/type/value review for exact source SHA256 above. Author scans and kernel receipts do not substitute for that review. Integration and downstream consumers are outside this author unit.

Actual prescribed author model/effort: gpt-6.1-sol / xhigh. Per-agent input, cached-input, output and reasoning-subset token counters are unavailable; no exact usage or subscription-percentage allocation is asserted. `handoff.json` binds all local evidence hashes.
