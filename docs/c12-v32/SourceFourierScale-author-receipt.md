# SourceFourierScale author receipt

STATUS: AUTHOR_GATES_PASS / INDEPENDENT_FULL_PROOF_REVIEW_PENDING. This is an author delivery, not an independent CORRECT verdict or root closure.

Frozen scope: `SourceFourierScale-next-scope.md`, SHA256 `5d0afce4726be7a211e934a6bc3ff72e68fc2e622bc091b1e67ad4abff1773ef`. Independent declaration review: `SourceFourierScale-declaration-review.md`, SHA256 `cf3a3a7b298d19ab7549d93f0d9f823c3e4c577987c74859da2a3ee3cb9e41c9`, CORRECT with no revision. The two public signatures match those exact frozen blocks after whitespace normalization; there are zero definitions, two public theorems and two explicitly private theorem helpers. No premise, cutoff, law, variance or sample normalization was changed.

## Immutable delivery

- Local mathematical source: `C:/game/shao lean/drafts/c12/SourceFourierScale.lean`.
- Server module: `/root/rivermind-data/shao-lean-20261021/workspaces/source-fourier-scale/Shao/Probability/SourceFourierScale.lean`.
- Source SHA256: `5f31eb92eff8ded33b91f55a59a16de4e58cdd7a9e0514d082a2c4932f5feff0`, identical locally and remotely, 10,314 UTF-8 bytes, 221 LF lines, no BOM/CR.
- Isolated branch `author/source-fourier-scale`, commit `3fb0ba0ede60a785bc7ad448756140df868c20f1`; sole committed file is the new module. Base is accepted v28 integration ancestor `dfd521e6ed80b37c7e0b4280395daf1f7c1ec881`.
- All nine imported project source files equal their accepted base bytes. SourceTruncationBridge remains `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1`; SourceClockBridge remains `ced48edd68d62919d066dd1bd964374a166bd5ccb47c309849ccbe6009f1fe65` (not imported by the new module). Root imports, expected-public-theorem manifest, pins and shared packages remain unchanged.
- New module's sole direct import is `Shao.Probability.SourceTruncationBridge`; no new cache module or shared write was needed. The isolated worktree reused v28 project build artifacts and the existing shared read-only package symlink. No local Lean, lake update, cache get, whole Mathlib build or child agent was used.

The mathematical source has not been edited since the successful target. No self-review or merge was performed. Untracked server `work/` contains only this unit's receipts/audit; it was not committed or copied into the local workspace as raw logs.

## Complete proof route

`sf_raw_lyapunov` is the only new analytic helper. For the actual probability rho with true raw second/absolute-third integrability, it sets b=sqrt(m2), uses b²=m2, and integrates the pointwise nonnegative factorization `(abs z-b)^2*(2*abs z+b)`. Both sides `3b*z²` and `2*abs z³+b³` are explicitly integrable. Probability integrates the constant as b³, yielding `sqrt(m2)*m2<=m3`. The source uses no original global third moment or silently centered conditional law.

`sf_variance_ratio` is an elementary scalar helper. From positive N, N*mu²<=1/4, N*V>=1/2 and V=m2-mu², it proves V<=m2<=2V; its scaled variance identity is written before positive-N cancellation. Its input facts are supplied by accepted SourceTruncationBridge at exactly the same rho in both public proofs.

`sourceTruncation_gamma_bounds` obtains n>=64, rho probability, the actual a.e. cutoff and true raw h2/h3 from the accepted bridge, then its true positive V, variance identity and nV bounds. The raw Lyapunov lower side proves m3>0, hence gamma=m3/V>0; comparison of sqrt(m2)*V with m3 then proves m2<=gamma². Integrating the actual a.e. support bound gives m3<=h*m2<=2hV and gamma<=2h. The exact identity gamma*(nV)=n*m3 with nV in [1/2,4/3] yields `(3/4)n*m3<=gamma<=2n*m3`. Accepted raw cube payment and `truncationBudget_scale_one_le` at t=0,c=1+x prove n*m3<=2R_n(0), then gamma<=4R_n(0). The scale direction is the actual upper inequality R_n(x)<=(1+x)^3 R_n(0).

`sourceTruncation_oddPower_scale_inputs` preserves ell=n-i as natural subtraction. From the literal hT region, m2<=gamma² and gamma>0, it obtains L2<=ell by legitimate positive-gamma² cancellation. L2>=20 gives Nat6<=ell, and natural subtraction gives ell<=n. It separately reuses accepted drift payment with the same weak source budget and epsilon<=1/2 to obtain n|mu|<=1/8<=1. The accepted variance data give m2<=2V<=4V. Thus n>=64 never substitutes for a future-length assumption, and no desired OddPower conclusion is used as a premise.

Original source anchors and hashes are frozen in the scope and checked by the independent declaration review. This source proves those exact scalar gamma/length/bias/ratio statements only. No noise K/Xi estimate, Fourier derivative bound, full-frequency inversion, desmoothing or C1/C2 root closes here.

## Actual designated-server checks

Every invocation first sourced `activate.sh`, then changed to the isolated worktree. At most one author Lean process ran, always with CPU affinity0–3. Actual version is Lean4.36.0-rc1, compiler commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`; Mathlib manifest/actual Git HEAD is `807d3836b165983210ee2ecf3cd28f239436949c`, with no tracked Mathlib diff. Manifest SHA256 is `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`.

Final target:

```text
taskset -c 0,1,2,3 lake env lean -o .lake/build/lib/lean/Shao/Probability/SourceFourierScale.olean Shao/Probability/SourceFourierScale.lean
```

`check02.json`: exit0 in5.363012172281742s; stdout/stderr empty; source SHA unchanged before/after. Actual olean SHA256 `181f3e96c2cde028a900a0d7c167ca7e521e1a19b28ac97427b9530e6433ab8b`. Earlier check01 failed during elementary rewrite/order-API elaboration and retained its complete raw output; the frozen public signatures never changed. No accepted predecessor check was repeated.

Actual all-module-owned audit:

```text
taskset -c 0,1,2,3 lake env lean work/source-fourier-scale/Audit.lean
```

`audit01.json`: exit0 in5.366872431710362s, stderr empty, source SHA unchanged. The audit enumerates the actual environment ownership of every imported Shao constant, applies `Lean.collectAxioms` transitively to each, and rejects any axiom outside `propext`, `Classical.choice`, `Quot.sound`. It finds **7 target-module constants**, all theorem constants:2 public+2 explicit private+3 generated proofs. The three generated names are `sourceTruncation_gamma_bounds._proof_1_1`, `sourceTruncation_oddPower_scale_inputs._proof_1_1` and `sourceTruncation_oddPower_scale_inputs._proof_1_2`. The explicit private helpers are `sf_raw_lyapunov` and `sf_variance_ratio` under the target module's private names. All169 imported Shao constants (including the target7;162 predecessors) pass the whitelist. Both actual public types are printed with `pp.all` and both public transitive axiom queries are retained. No actual target-owned/private/generated declaration was omitted merely because it is not public.

Raw server evidence remains in `work/source-fourier-scale/` in the isolated worktree:

| Artifact | SHA256 |
| --- | --- |
| `check02.json` | `3436086967d69e50103190a19f05545640be153e53126e3946d27ed65f1adeb5` |
| `check02.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Audit.lean` | `073123c1bc5a16e7178a7e74aab52aee7f2d3b4b482d249ffbe3432b339f03b2` |
| `audit01.json` | `fe749a9d0baf82786417cf2567f24502e6be8ea8366ceefd1862e1006678b317` |
| `audit01.stdout` | `77c2287af5f61d1ef6373b9e1a9804ae32cc0f780e8ba3cb7cd5c2ea03d4f797` |
| `metadata.json` | `b4eb2813ead973061106da267316d3d84c9ec7f4cb9f95ceff8b3b7a9dc25e9b` |
| `final.json` | `54b7ff9ac6518bbaecf4cbb159912fd5c7925a15a69dee57c68855046212ff0e` |

The full ten-file project-source closure and its source hashes/imports are recorded in metadata. All nine predecessor source bytes were additionally compared directly with the accepted base Git blobs before committing the sole new source file. Both old source bridges, root imports/manifest and pins were explicitly rehashed and compared to base.

Local read-only contract/prohibited-code check: `SourceFourierScale-source-check.py`; saved result `SourceFourierScale-source-check.json`, SHA256 `cff7aff05dfebf5eb6c1d4dc8b928e422beaa23bdee4e4b3a4df3442934cb402`. It validates frozen scope/review hashes, both exact headers, declaration inventory, UTF8/LF/noBOM and nested-comment/string-aware absence of sorry/admit/axiom/unsafe/native_decide. It does not invoke Lean and does not assert independent proof correctness. Local audit source `SourceFourierScale-audit.lean` equals the actual server audit bytes.

Required next gate: a never-author independent complete source/proof/type/receipt review, then root's imports/manifest/whole-library integrated gate. Source bytes are frozen for that review; parent alone coordinates any justified change.
