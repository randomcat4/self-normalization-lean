# Frozen finite CDF / nonzero-drift survival production handoff

Author: `/root/common_survival_cdf_candidate`, `gpt-6.1-sol/xhigh`.
Status: all eight frozen declarations have original server kernel and all-owned
transitive-axiom PASS. **Independent complete review and root acceptance remain
pending.** No author self-review is represented as independent evidence.

The exact declaration/value freeze is
`coordination/public-survival-cdf-declaration-freeze.md`, SHA256
`674a688c637cc88eb5d3e1f5c43486725e8f1f64510a248ca9742b423a8db2fa`.
The original candidate/contract/route files are preserved as frozen historical
inputs; their original “uncompiled” status describes the candidate stage.

## Source-only Git objects

Worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/common-cone-derivatives-v44`.
Branch: `feat/common-chord-cone-derivatives`.

| Commit | Parent | Scope |
|---|---|---|
| `ba7ef8674924248e6eb6fb78d8c59aaf848a6627` | `2044113b88476b1d3b3c47f3da8b5388b15b6c9a` | Only `Shao/Probability/BerryEsseen.lean` |
| `3993099d893ada6b91d53f6bbbadfdfaff96c123` | `ba7ef8674924248e6eb6fb78d8c59aaf848a6627` | Only `Shao/Probability/FiniteSurvival.lean` and `SourceLindleySurvival.lean` |

Trees are respectively `84a40189b9c876fd23f8b6d9a51af84f073ea2d6` and
`620a2d3cdf9d6c8833edbd86607983b103f6487e`. No draft, review claim, other owner's
source, or PR was included. Each source was compared against its immutable
successful artifact before committing. Root publishes and integrates.

## Original source-bound results

Artifact root is
`/root/rivermind-data/shao-lean-20261021/artifacts/common-survival-cdf`.
All three local review sources are in this draft directory, UTF-8 with LF.

| Module / artifact | Source SHA256 | Original emitted object SHA256 | Kernel / audit exit |
|---|---|---|---|
| `BerryEsseen` / `step-043` | `8bf02df1210d69a2934746987d0022a85166d17c9850fa4fd27656eb88bb2af9` | `d67df1b97eddcde16ee7d9fedc6e6e7e4af11e22e04732a69dbd0b5883b76b57` | `0 / 0` |
| `FiniteSurvival` / `finite-007` | `155b8865c55e392f27b07a65caad1ea3aac542a70fea4ae491251ee1b3a3d816` | `b0037ea1068ddd216c6cea03781efae10b06bfeb967e95a5207f9a4fe248935a` | `0 / 0` |
| `SourceLindleySurvival` / `source-002` | `433313fd12cfacfae54bb0ec1366d05aa47844b12fc18585fd326aae81590178` | `5eb0dd2b431314562b2ff0866addd250ae940a83fbcfedb8c8e1fe28ae8f2f48` | `0 / 0` |

Original commands, requests and responses remain in `step-043-*`, `finite-007-*`,
`source-002-*`, and the corresponding `*-owned-audit-*` files. Full original
stdout/stderr/exit/source/object remain on the server. The audit imports the
original successful object installed in this worktree; it does not recompile the
producer. All actual Lean/audit checks used root-heavy.lock, CPU10–13,
`-M8192 -j4 -DautoImplicit=false`. Accepted older dependencies were not replayed.

The first FiniteSurvival audit transport response timed out after its original
command began. The saved original terminal `owned-audit.exit = 0`, JSON and log
were recovered read-only; the audit was **not rerun**. The evidence summary binds
the original terminal files. The complete type JSON was transferred by SFTP and
its hash verified after a short stdout fetch was detected and replaced; no Lean
check was repeated for that transfer repair.

## Complete review exports

Every actual module-owned declaration was selected by the environment owner map,
including private/generated declarations. Printing explicitly sets
`pp.all=true`, `pp.maxSteps=10000000`, `pp.deepTerms=true`, `pp.proofs=true`.
Every actual type was machine-scanned for literal `⋯`: zero occurrences.

| Module | Owned / theorem / definition / public counts | Complete type/value JSON SHA256 | All-owned axiom JSON SHA256 |
|---|---|---|---|
| BerryEsseen | `119 / 118 / 1 / 5` | `01287fa1419ff72d337e27d786e74e79cc1d86458a74af14ac325d87f5003244` | `4d0a0675617535831e11e85473908b8533c3619c211b45df65f73fb578ac2bb3` |
| FiniteSurvival | `37 / 37 / 0 / 1` | `74baa94a9473d24bfb75f1c238f07e37b1ee494647f401b3abe41ccd4eecb5eb` | `287239ddec1032ad68e99c3509eb0bb1cf571028a614fd142d0e15d553d7faf9` |
| SourceLindleySurvival | `5 / 5 / 0 / 2` | `fe414751442e8843cdf661649725bf74681675a8723b724b85912240048ef86a` | `480ff90ebf7835658a4e873415addcc7ee6e6b41af4e48e8586c1abd4b082f09` |

The local filenames are `berry/finite/source-owned-actual-declarations.json` and
`berry/finite/source-owned-axioms.json`. Evidence summaries are
`berry-first-five-evidence.json`, `finite-head6-evidence.json`, and
`source-heads7-8-evidence.json`. Total actual ownership is 161 declarations:
160 theorems and the sole frozen definition `cdfFourierError`, with its full
literal value exported. All transitive axiom lists are within `propext`,
`Classical.choice`, `Quot.sound`.

## Mathematical scope and review points

1. `cdf_error_le_fourier_smoothing` constructs the actual sinc-fourth density,
   its normalization, first moment and compact Fourier support. Atomic CDF
   differences are proved L1 by explicit indicator intervals and Fubini, then
   transformed and unsmoothed by monotonicity and supremum absorption. Neither
   probability law is silently assumed atomless.
2. `iid_unitVariance_charFun_error` and `iid_unitVariance_berryEsseen` produce the
   actual finite product pushforward bound, all `k >= 1`, with literal 1024.
   The final proof uses the pinned Taylor remainder `beta*|u|^3/2`, a single-step
   comparison coefficient `5/8`, and the extra exponential factor to cover `k=1`.
   This proof refinement preserves every frozen head/value/constant; it does not
   use an assumed quantitative CLT or final C1/C2 theorem.
3. `iid_centered_berryEsseen` pays actual affine moments and the finite product
   pullback. `iid_uncentered_berryEsseen` retains exactly
   `|mu|*sqrt(k)/sqrt(V)`.
4. `iid_closed_survival_nonzero_drift` uses the accepted actual Spitzer producer.
   Correcting the endpoint payment by `delta*sqrt(k)` pays the series loss at
   `s=exp(-1/m)`, bounded by `4*delta*sqrt(m)`. Coefficient extraction is proved
   at that single parameter; no false uniform-in-parameter drift estimate is
   supplied to the old all-parameter coefficient consumer. The closed event,
   minimum, `m=0`, `r=0`, and literal `2*exp(6+3*1024)` are retained.
5. `sourceTruncation_lindleyPrefixSurvivalBound` uses the original raw finite2,
   normalization, raw mean-zero, cutoff and budget assumptions unchanged. The
   fixed conditional law may have nonzero mean. Accepted payments give
   `N*|mu| <= 1/8`, `N*V >= 1/2`, hence drift `<=1/4` for `k<N`, and centered
   cube `<=8` times raw cube. Its constant is exactly `16*exp(7+3*1024)`.
6. `sourceTruncation_lindleyRegulator_second_moment` consumes the already accepted
   square-moment consumer at that actual survival predicate. It retains
   `m3/(sqrt(V)*sqrt(j+1))` with literal `48*exp(7+3*1024)`, without a survival
   premise. The existing predicate is not redeclared.

The Fourier/Spitzer/Berry–Esseen method is classical; no novelty claim is made.
Original source ranges and attribution remain in `source-contract.md` and
`proof-route.md`. Weighted source square sums, further source deletion/tilt
steps, complete C1/C2, and all original root groups remain OPEN unless separately
accepted by root. These three modules do not assert those larger conclusions.

Next required action: a fresh qualified independent complete source-to-statement,
proof, generated/private scope and full-value review of these exact versions,
then root acceptance using the existing source-bound receipts. No review or
integration check is requested merely to replay an unchanged successful proof.
