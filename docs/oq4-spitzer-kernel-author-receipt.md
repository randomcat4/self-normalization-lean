# SpitzerKernelBounds author receipt

Author implementation and the required mechanical checks passed. Independent mathematical/source-to-statement/formal review is pending; this receipt does not self-certify independent review.

## Frozen artifact

- Frozen interface: `drafts/oq4/frozen-spitzer-kernel-bounds-v1.md`, previously statement-translated CORRECT by an independent context.
- Server source: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/SpitzerKernelBounds.lean`.
- Final source SHA256: `e9d956ed03c634f5214c4fd85905d86fa51f6b1e5663a43ed9d3f143fcf5e014` (6621 bytes).
- Author-only emitted olean SHA256: `7c083c1a95a780553eb83e4bbc1c60f7c73e1d9d518fe40b60d356d35874ea3f`.
- Local source and anonymous derivation: `drafts/oq4/spitzer-kernel/SpitzerKernelBounds.lean` and `proof.md`.
- UTF-8 without BOM, LF only, exactly one final LF; source frozen after successful checks.

## Exact scope and dependencies

There are three new explicit theorems. `spitzer_kernel_probability_inputs` derives the actual third absolute moment β ≥ 1 from square/cube integrability and unit second moment, then supplies both existing actual probability predicates using ReflectedSurvival. Their accepted argument order is ν β C. `spitzer_kernel_block_bounds` retains full integrability/centering/second-moment/M premises and internally supplies actual S/AC, actual Borel residual measurability, genuine absolute-residual integrability under the true killed-kernel row, and actual R3/R4 for m=floor(h²), h≥3, |z|≤h. `spitzer_kernel_finite_absorption` supplies these inputs to the accepted finite D8 theorem.

The final theorem explicitly retains id/square/cube integrability, mean zero, second moment one, M≥0 and actual β≤M, C_BE≥0, the sole all-t/x ordinary-sum BE CDF premise for ν, and the two separate all-L/s original SP identities for ν and reflectedLaw ν. It also retains h≥3, π(1+M)≤h, N≥floor(h²), and the original noncircular smallness condition. No reflected-law BE, S/AC/O0/R3/R4, antitone, summability, survival-conditioned independence, B1, or sought normalized-mass bound is assumed.

Cq=1+2 C_BE, Cs=√2 exp(6+3 C_BE), Clayer=12 Cq Cs M(1+M), E=π³M/48+2π Clayer(1+2M), R=exp(π²), H=2(1+(2Cs)R)R are explicit let bindings in the relevant signatures. They match the accepted killed block/absorption constants exactly. The smallness expression is ((2Cs)R)(E R/h³)N+(2CsM)R/h≤1/2. The conclusions retain every k≤N including k=0 for mass, and floor(h²)≤k≤N including equality for the cosine difference; subtraction is natural before coercion. Source endpoints remain closed, with no extra moment, support, density, nonlattice, or symmetry assumption.

Only the finite conditional chain BE/two original SP → actual S/AC → actual R3/R4 → finite D8 is supplied. BE, SP, B1, long-time limits, 4/π, K/Kv, E1–E6 and all complete roots remain OPEN.

## Server execution

Every Lean invocation ran only on the designated server, after activation and changing back to the assigned OQ4 worktree. Each used one process with `taskset -c 0-3`. No old module target/olean was rebuilt. There was no Git, common/root/manifest/lock/shared-cache edit or cache download.

Parent-confirmed baseline: branch `feat/oq4-be-sp-blocks`, HEAD `884e67692280a4049d4c52aeb4fa0573a0be2cf7`. Parent reported its accepted PR29 head tree is identical to accepted main59844ce; the author performed no Git operation. All prior mathematical modules remain fixed.

Toolchain: `leanprover/lean4:v4.36.0-rc1`.
Mathlib revision: `807d3836b165983210ee2ecf3cd28f239436949c`.

| Check | Exit | Full server record |
|---|---:|---|
| 22 prior OQ4 imports followed by exact new source body | 0 | `repro_outputs/oq4-spitzer-kernel/coexist03.log`, `.exit` |
| Canonical new source target | 0 | `repro_outputs/oq4-spitzer-kernel/target01.log`, `.exit` |
| Author-only olean emission | 0 | `repro_outputs/oq4-spitzer-kernel/olean.log`, `.exit` |
| Actual 23-module import and owner-module all-constant transitive axiom audit | 0 | `repro_outputs/oq4-spitzer-kernel/audit.log`, `.exit` |

The successful coexistence/target/olean logs contain 0 bytes and no diagnostics. Raw logs/binaries stay only on the server. Initial coexist01/coexist02 failures are retained there: the sole issue was an unavailable field/name for measurability of absolute value. The final proof uses continuous_abs.measurable.comp with the accepted principalResidual_measurable. Mathematical hypotheses, constants, conclusions and proof route were unchanged. Two local curated historical source snapshots retain the failed API spellings; the initial source hash was c0aceadb970c1b55d010e779198f987272133f0ce68661be1620df435b4aec95. Neither historical source is an accepted artifact.

## Complete axiom audit

The dynamic audit uses `env.getModuleIdxFor?` and exact owner module name `Shao.OQ4.SpitzerKernelBounds`, with no constant-name/namespace prefix filter. It found **7 actual new constants = 3 explicit theorems + 4 generated helpers**. All 7 actual transitive axiom records are exactly {propext, Classical.choice, Quot.sound}; there are no unexpected axioms. The four generated helpers belong to imported definitions' names: killedLayerConstant.eq_1, killedResidualConstant.eq_1, normalizedKernelCosine.congr_simp, normalizedKernelMass.congr_simp. These were included despite their different roots. A source banned-token scan was empty. See `declarations.md` and curated `summary.json`.

## Reproduction

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean repro_outputs/oq4-spitzer-kernel/CoexistSource.lean
taskset -c 0-3 lake env lean Shao/OQ4/SpitzerKernelBounds.lean
# Author emission already completed once. Reviewers use source/no-o and import checks.
# taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/SpitzerKernelBounds.olean Shao/OQ4/SpitzerKernelBounds.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-spitzer-kernel/Audit.lean
python3 repro_outputs/oq4-spitzer-kernel/summarize.py
```

The local helpers `check.ps1`, `CoexistSource.lean`, `Audit.lean`, and `summarize.py` reproduce this new-module workflow. `Audit.lean` imports all23 modules. Source/proof/receipt/declarations/summary/checkpoint and helper source are curated locally; full audit/compile logs and binary artifacts are server-only.
