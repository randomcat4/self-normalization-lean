# SourceClockBridge author receipt

Status: AUTHOR TARGET AND AXIOM GATES PASS; independent final proof/source review PENDING. This is an author verification receipt, not a self-issued CORRECT verdict or root completion claim.

## Frozen identity and isolated delivery

- Frozen scope: `drafts/c12/SourceClockBridge-next-scope.md`, SHA256 `673ad95d64459843af58dd563696a600f3820c662cd038bf5baff7b419b6877c`.
- Independent declaration/source review: `SourceClockBridge-declaration-review.md`, CORRECT, SHA256 `9ffbaf9313a71907db6dcad6411b4d986b289ef6489aa2543aab614db04fdcad`.
- Local implementation: `C:/game/shao lean/drafts/c12/SourceClockBridge.lean`.
- Server module: `/root/rivermind-data/shao-lean-20261021/workspaces/takeover-source-clock-bridge/Shao/Probability/SourceClockBridge.lean`.
- Final implementation SHA256: `ced48edd68d62919d066dd1bd964374a166bd5ccb47c309849ccbe6009f1fe65`.
- Source-only author commit: `bf6ba73b36aacc572a8d26cbf8af87ee3d680442`.
- Worktree/branch: `takeover-source-clock-bridge` / `author/takeover-source-clock-bridge`.
- Base: accepted SourceTruncationBridge author commit `d472d38f39f7a68025a9409a47c2a11a55e0e8c1`, itself based on origin/main `c7f54caf9d43d6ee149c9d11aa0cb88d552d0b1b`.
- Exactly one source file committed, 360 lines. No push, merge, root import/manifest/shared source edit. Only untracked private author audit/log artifacts remain in the worktree.
- Recorded completion: `2026-10-21T16:39:16Z` (2026-10-22 Asia/Singapore).

All three public signatures were extracted from the actual source and independently compared with the three frozen Lean blocks after whitespace normalization only. Exact equality, exactly three public theorems, zero definitions, and no sorry/admit/axiom/unsafe/native_decide tokens. One handwritten private theorem, `sc_final_clock_chebyshev`, supplies actual squared-coordinate L2/variance/Chebyshev; no extra public declaration or premise was introduced.

Public targets:

```text
Shao.Probability.sourceTruncation_conditioned_sample
Shao.Probability.sourceTruncation_clock_bad_probability_le
Shao.Probability.sourceTruncation_final_clock_probability_le
```

## Actual mathematical implementation supplied for independent review

The first theorem starts with the original iid sample and marginal law. The actual all-coordinate closed cutoff event A is fixed at x. Its complement is the finite union of the strict tail events. Original marginal equality plus the real finite-union bound and accepted source tail budget give mu.real(A^c)<=R/epsilon^3<=1/8. Only after mu.real(A)>=7/8 and actual mu(A)!=0 does the proof install probability for cond mu A and consume the accepted generic conditional vector-law theorem.

The full true product law is then mapped through coordinate evaluations, yielding the actual conditioned marginal laws. The existing joint-map criterion reconstructs actual independence. The n=0 case is handled uniformly rather than by a separate Nat split: scalar rho probability is installed only inside a proof with an actual i:Fin n, via positive A and its inclusion in that coordinate's cutoff event. There is no global scalar probability claim for an empty sample and no added n>0 assumption. The empty vector law itself is supplied by the generic true conditional law.

The second theorem uses the same fixed A, cond mu A, rho and unchanged original coordinates for every y. It consumes accepted scalar support, raw second-moment bounds and all three clock numeric hypotheses. The actual generic ClockControl conclusion retains the conditional cube factor; accepted nearby payment then supplies 16R, giving 32768 sqrt(2 pi) R Tail(y), followed by the actual exp(2) Gaussian local-tail comparison. The original normalization and original mean zero remain explicit, and no conditional mean-zero or desired clock hypothesis is inserted.

The private final-clock helper transports true square-coordinate L2 from the actual scalar fourth moment, obtains actual means and variances via IdentDistrib, and applies independent finite-sum variance to Y_i=X_i^2. Thus E Q=n*m2 and Var(Q)=n Var_rho(z^2)<=n*m4. The complement of the closed good interval lies inside {|Q-EQ|>=1/2}; actual positive-threshold Chebyshev gives bad<=4n*m4.

The third theorem obtains bad<=8 epsilon R/(1+x)^4<=R from the accepted paid raw moments. For x<2 it uses real Tail(x)>=Tail(2)>0. For x>=2 it calls the second theorem at y=x and drops the other nonnegative bad-clock term. This proves the displayed uniform coefficient 32768 sqrt(2 pi)+1/Tail(2), with no low-y use of the y>=2 clock theorem, no division by R/n/m3, and no replacement of raw Q by centered-A energy.

## Server/toolchain and resource context

All Lean execution occurred on the designated server after sourcing `/root/rivermind-data/shao-lean-20261021/activate.sh` and then entering this new worktree. Commands were sequential, one Lean process at a time, with CPU affinity 0-3.

Actual versions:

```text
Lean 4.36.0-rc1, commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e
Lake 5.0.0-src+c9afcdd
Mathlib 807d3836b165983210ee2ecf3cd28f239436949c
```

The prescribed shared package symlink is read-only. Existing project build outputs were copied from the preceding owned source-bridge worktree; only the new module's own output and private author artifacts were written. No local Lean, package update, cache download or full Mathlib build occurred. Root retains cache/import/manifest/integration authority.

Unchanged accepted dependency/control hashes were checked:

```text
SourceTruncationBridge 05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1
ClockControl c7782d17c1b6dec827cde84d1d44f9b6cb7a7d8dd166bee2183cac4d2dd5cdba
ConditionalIID 855c2eb0e560ac9372505f8b41551a9895b9eb753be3ce2b3f3752be845af787
lean-toolchain d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4
lake-manifest.json 40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e
```

## Final actual checks and immutable receipts

Full artifacts remain on server in the new worktree's `.author-source-clock/`; no raw logs or compiled outputs were copied into the local shared workspace.

1. `git diff --cached --check` before the source-only commit: exit 0, empty `diff-check.log`.
2. Final actual target and object:

```sh
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/Probability/SourceClockBridge.olean Shao/Probability/SourceClockBridge.lean
```

`check-06.log`: Lean exit 0, no diagnostics. SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
New own olean SHA256 `7a7eceb94c1293f94beb6739a7a9ef01d0741007696f9a1ec17f00693d3f0aeb`.

3. Full module/dependency axiom audit:

```sh
taskset -c 0-3 lake env lean .author-source-clock/OwnedAudit.lean
```

`audit-02.log`: Lean exit 0. Audit source SHA256 `d0a0442f1474210d94dfa268f46db21424272e4958ba753fdbb8deba9f48e6fe`; log SHA256 `3174771a735419c7fa66125b6f18c1c44c583e8f635f6684070849c1e3aa018f`.

The audit imports the actual new module, selects all imported Shao constants by true `env.getModuleIdxFor?` ownership, then calls transitive `Lean.collectAxioms` on every one and throws on anything outside propext, Classical.choice and Quot.sound. Exact target module equality identifies every new public/private/generated constant. Each frozen public target is separately checked for theorem kind and exact module ownership; actual elaborated types are logged. Separate #print axioms commands for all three public targets also return only the whitelist.

Actual summary:

```text
COVERED_FROZEN_PUBLIC_TARGETS 3
AUDITED_TARGET_CONSTANTS 21
AUDITED_TARGET_THEOREMS 21
AUDITED_DEPENDENCY_CONSTANTS 321
WHITELIST_ONLY propext Classical.choice Quot.sound
```

The 21 target constants are all theorems: 3 public, 1 handwritten private and 17 generated proof declarations. The 321 count is the full imported project constant set including these 21; no private/generated declarations were omitted by name filtering. A read of the final audit records found no errors and axiom union exactly the whitelist.

## Failure/normalization ledger and remaining gate

`check-01`/`check-02` exposed library naming, probability-instance placement and real-complement-expression normalization. `check-03` exposed explicit squared-coordinate composition/L2-integrability arguments, variance positivity and simple algebra normal forms. These were repaired without signature or premise changes. `check-04` passed the complete target with one unused private hX parameter warning. Removing that unnecessary private parameter gave clean `check-05` plus successful `audit-01`.

The first commit hygiene check rejected Windows CRLF as trailing whitespace. The new module alone was normalized to LF; no Lean text/proof/signature changed. The pre-normalization source hash 9f00b17703aa2580d826eb281dee48dff053f2a937acc36dfb97514d7f44594f is superseded by the final hash ced48edd68d62919d066dd1bd964374a166bd5ccb47c309849ccbe6009f1fe65. The coordinator was informed before final delivery. Final target `check-06`, audit `audit-02` and staged hygiene were rerun to bind the final bytes; the olean and audit-log hashes remained identical. The accepted SourceTruncationBridge bytes were never normalized or edited.

Next gate is integration_review's independent full source/proof review at the final hash. No self-review, merge, noise construction, Fourier comparison, full desmoothing argument or C1/C2 root completion is claimed.
