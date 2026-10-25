# Nonnegative stretched-exponential sum moments

This module proves the exact auxiliary statement from original p44 §2(6). Fix `0 < β ≤ 1`, `τ > 0`, and `M0 ≥ 1`. For arbitrary measurable `Ω`, every `n : ℕ` including zero, coordinate probability measures `μ i` and measurable functions `Y i` that are respectively almost everywhere nonnegative, assume the actual functions `exp (τ * (Y i)^β)` are integrable and their actual integrals are at most `M0`. The joint law is the actual independent product `Measure.pi μ`; coordinate laws need not be identical.

Let `K = M0 * (τ * β)^(-(1/β))` and `C = 2 * 2^(1/β) * K`. The public theorem fixes this positive `C` before `Ω`, `n`, `μ`, `Y`, and the real moment order `q`. It proves integrability of the actual sum to the power `q` and, for every real `q ≥ 1`,

`(∫ x, (coordinateSum Y x)^q ∂Measure.pi μ)^(1/q) ≤ C * (n + q^(1/β))`.

The source contains three definitions, thirteen private helpers and three public theorems. The proof pays coordinate moment domination, monomial integrability and actual finite-product integration, a finite multinomial expansion, positive-composition and support counting, factorial weights, and the real-order comparison with `ceil q`. Empty sums and products are retained; no positivity of n, identical distributions, standard Borel or atomless assumptions are added.

## Exact qualification

Source: `Shao/OQ6/StretchedExponentialSumMoments.lean`, SHA256 `9ffdbe105b2cbdc5552acdc11d8942dd08372e8d55574bd65dcad8c186344470`, 67573 bytes / 1262 LF. Object: SHA256 `65cf3bd6489e09be794ffa6b8686b0ab15df5cf56d27baf192691dfff0b7d6d3`, 1607696 bytes.

The original complete independent source review is reused at its exact hash for fourteen unchanged declarations. The same independent reviewer completely reviewed the five changed helper proofs and all affected types/scopes, then all actual imported-module-index declarations. The final independent report and complete coverage accompany this change; author and reviewer are separate.

Server kernel03: native RC0 / 7.049260888248682s, all 4984 protected records preserved. The same-object all-owner audit01: native RC0 / 5.460864732041955s, all 4993 protected records preserved. Actual inventory: 62 owners = 59 theorems + 3 definitions, complete 1488 TYPE lines and 24 FULLVALUE lines. Per-owner recursive axioms are exclusively `propext`, `Classical.choice`, `Quot.sound`; occurrences are 62 / 42 / 53. The independent reviewer reconstructed all 133500 bytes of audit output exactly.

Forty source style/deprecation/unused warnings and the 134-byte Lake repository warning remain in the kernel record; the audit retains that Lake warning. Both strict wrappers report false because of diagnostics; the native kernel and audit passed. No clean-wrapper claim or warning-only recompile is made. The original source's RC1/16 errors and a later pre-Lean configuration KeyError/zero Lean calls are preserved separately. Final source was normalized to UTF-8 without BOM and LF before its first source-bound gate.

Kernel receipt SHA256: `1ff093805d4702176e860f7240737c27f550dcec0866d0059efbedc7bf08bc9f`. Audit receipt SHA256: `cbd9ee6513e2fad5ba7ade8d6cce89ca22a4c5e50a7add988b221ee6a9d11701`. Independent qualification SHA256: `e81c3d47330b8fd69661c43170dffe1e00c26c377a0f477eb81c1fc0f583f8e3`.

This pays only p44 §2(6). Hilbert/Rademacher comparison, conditional ghost consumers, second chaos, row concentration, DC/SZ engines and original root closure remain separate. It does not restore the p54 moment-rate claim refuted by retained counterexample evidence. No novelty or OQ56/C2/C12 root completion is claimed. OQ3 remains paused by the human.
