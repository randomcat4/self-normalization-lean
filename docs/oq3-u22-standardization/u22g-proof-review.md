# OQ3 U22g independent complete proof review

## Immutable blind actual-statement prefix

This prefix was written before reading the U22g scope, Lean source, source-attribution records, author proof records, or mechanical-check receipts. It is frozen and will not be revised by the later review. Reviewer: fresh independent delegated context, prescribed gpt-6.1-sol / xhigh; no proof authorship, no children, no Lean/audit/gate execution, sole write ownership of this report.

First and complete input: `drafts/oq3/u22g-actual-types.txt`, SHA256 `ccd6cd9bbf1c6e592b6ac105d3b19f970216b594c20b84072f86c560494edc28`, 1706 bytes, 26 LF-terminated lines, read in full. Its inventory has exactly three owner declarations (two private and one public), each listing only `propext`, `Classical.choice`, and `Quot.sound`.

### Independent translation of all actual declarations

1. For every real x and natural k, `(1+x²)^k ≤ 2^k (1+|x|^(2k))`.
2. For all real a,b, `sqrt(a²+b²) ≤ |a|+|b|`.
3. Let mu be any probability measure on the real line, and let Theta be any compact subset of the interior of the true bivariate moment-generating-function integrability domain of `x ↦ (x,x²)`. Let A be any family of real 2×2 matrices indexed by all real parameter pairs. Given U≥0 and a bound `|A(theta)[i,j]|≤U` for every theta in Theta and both finite indices, form the actual normalized exponential tilt of mu by `theta₁x+theta₂x²`; form its actual first and second scalar integral means; center `(x,x²)` by those means; apply A(theta); and push the tilted measure forward along that map. Every resulting law for theta in Theta is a probability measure. For each natural k there is a strictly positive real C, uniform in theta in Theta, such that the kth power of the actual Euclidean radius `sqrt(y₀²+y₁²)` is integrable under the corresponding pushforward law, its actual integral is nonnegative, and that integral is at most C.

### Blind acceptance requirements and exclusions

The proof must cover all three declarations, all real x (not a bounded surrogate), all k including zero, U=0, empty Theta, arbitrary probability mu, actual means and actual normalized tilted laws. It must supply genuine integrability, not exploit totalized integrals; justify probability preservation, map measurability and integral transfer; derive uniformly bounded first/second actual tilted means from the stated domain/compactness hypotheses; and control Euclidean radius rather than silently substituting the product norm. The matrix assumption is the explicit uniform entry bound, not continuity or joint parameter measurability. No joint theta measurability is asserted. A has not been identified with a covariance whitening matrix, and no covariance identity, standardized 8+delta result, weak-Cramer claim, or root closure is part of this actual theorem. A later whitening application must produce its own actual A and uniform entry bound. A valid proof of these three types may be accepted only for this scope, after complete source-to-statement review and exact source-bound kernel/transitive-axiom evidence.

--- END IMMUTABLE BLIND PREFIX ---

## Prefix binding and mathematical review

The report consisting only of the preceding immutable prefix (through its terminal LF) was SHA256 `b9b85aa230f004956beb0ec335db65f8aa229e9e8308cdb59b3026e871921f19`, 3151 bytes, 19 LF-terminated lines. All subsequent text is an appended review. The full 26-line actual-type inventory was read before the prefix was written. The complete scope, then the entire final Lean source and consumed U22f source, were read only after that write.

Mathematical verdict: **CORRECT**, for all three actual owner declarations in this module. This is an independent complete source-to-statement/proof review, not a declaration-only review and not reliance on another review vote.

### Exact objects reviewed

- Frozen scope `eighty-eighth-unit-scope.md`: SHA256 `1dbc69a2da2a782a1ea8a05d196c61b68f32aeea3f9ce79a053ad1ceb6a63e4d`, 4145 bytes, all 44 lines.
- Final author source `OpenDomainAffineMoments.lean`: SHA256 `110a16cab72d655905659b30a496625f98aa70e188b004a8713006225ab9a8e3`, 8875 bytes, all 166 lines, both private proofs and the complete public proof.
- Consumed `OpenDomainCompactMoments.lean`: SHA256 `19946ecf589a2012df33b34ad740b4ff30190bd84fe42662bdaa194c5c545093`, 4170 bytes, all 85 lines read for interface validation. The consumed theorem at lines 37–48 gives probability of each actual tilt and, for each natural j, a positive theta-uniform constant with true integrability, nonnegative integral, and upper bound for `|x|^j`. Its measure, domain, compact set and quantifiers exactly unify with G line 67; no bounded-support, spectral, WC or pre-standardized moment premise is being imported. Its existing independent acceptance is dependency evidence, not a vote proving G.
- Original read-only R2 `C:/game/shao/current/oq3/proofs/r2/report.md`: SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`, 20102 bytes; actual lines 47–67 and 83–92 read, including the requested 57–60 and 83–92.
- `root-contract.md` was read, particularly sections 2 and 4. The true-domain definition `Shao.Probability.bivariateMGFDomain` was inspected at `library/Shao/Probability/BivariateLegendre.lean:20–22`: it is precisely exponential integrability, not finiteness of a totalized log/integral. The imported accepted-v43 `CovarianceWhitening.lean` source hash is `d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8`. G does not invoke its private radius helper or any of its whitening conclusions; G supplies its own complete private proof.

### Complete proof coverage

**Lines 1–7, imports and setting.** The real, finite matrix, measurable and topological structures are the standard ones. The scope matches the actual public type at lines 33–52 literally. There are zero public definitions; the `tilt`, `means`, `Y`, `laws` and `radius` in the proof are local abbreviations for exactly the objects in the statement. In particular the radius is `sqrt(y 0 ^ 2 + y 1 ^ 2)`, never the norm of the product/function space.

**Private `affine_radius_le_abs`, lines 9–12.** Both sides are nonnegative, so comparison of their squares is legitimate. `a²+b²≥0` permits the exact square-root square identity, and the nonnegative cross term `2|a||b|` proves the squared inequality using `|a|²=a²` and `|b|²=b²`. This proves the full real two-coordinate Euclidean inequality, including zeros and either sign.

**Private `quadratic_power_growth`, lines 14–31.** The even power is nonnegative because `x^(2k)=(x²)^k`, so `|x|^(2k)=x^(2k)`. When `x²≤1`, `1+x²≤2` and monotonicity of natural powers, followed by multiplication by `1+x^(2k)≥1`, gives the result. In the complementary case, `1+x²≤2x²`, and `(2x²)^k=2^k x^(2k)≤2^k(1+x^(2k))`. The proof has no bounded-x premise. For k=0 the usual zero-power identity is used and both branches remain valid.

**Lines 53–75, actual laws, measurability and constants.** For each fixed p, Y is a continuous finite linear combination of x and x² with real constant coefficients and real constant means (lines 61–66). No property of the function p↦A(p), or joint measurability in p, is required. Radius is continuous (line 60). The consumed raw-moment interface supplies true probability of the actual normalized tilt, and `Measure.isProbabilityMeasure_map_iff` applies to the measurable Y to obtain probability of the actual map measure (lines 68–70). Positive raw bounds C1,C2 are chosen once for all p∈Theta. Thus B=C1+C2+2 is positive and Q=2UB is nonnegative, also when U=0.

**Lines 76–121, actual mean and global sample growth bound.** For each actual tilted measure, the norm-of-integral inequality yields `|m0|≤∫|x|≤C1` and `|m1|≤∫|x|²≤C2`. These are not bounds on invented centering constants. U22f also provides integrability of `|x|` and `|x|²`; hence x and x² are genuinely integrable (by the norm criterion and `|x|²=x²`), so the actual means do not depend on divergent-integral totalization even though the norm-integral API itself is stated without an integrability argument. The coordinate centered bounds follow from the absolute-value triangle inequality. Each matrix row has two terms, bounded using the explicit `|A(p)[i,j]|≤U`, hU and nonnegative absolute values. Consequently `|Y_i|≤U(|x|+x²+C1+C2)`. The elementary inequality `|x|≤1+x²` and nonnegative `(C1+C2)x²` imply `|x|+x²+C1+C2≤B(1+x²)`. The privately proved Euclidean bound applied to both coordinates then yields `radius(Y(p,x))≤2UB(1+x²)=Q(1+x²)` for **every** real x, not only almost every bounded sample.

**Lines 122–143, uniform kth-power domination.** For any natural k, the raw interface is used at j=2k. With W=(2Q)^k≥0, monotonicity of powers, the private quadratic-power bound, and the power product identity give `radius(Y(p,x))^k≤W(1+|x|^(2k))` for all real x. The proposed final bound `C=W(1+Ck)+1` is strictly positive and depends on no p. The right-hand function is genuinely integrable under each actual probability tilt by integrability of 1 and the raw 2k moment.

**Lines 144–163, genuine integrability and actual pushforward integral.** The composed radius power is continuous and hence strongly measurable. Since it is nonnegative, its real norm equals itself; the global bound therefore meets `Integrable.mono'` exactly. This proves actual sample integrability before using any integral comparison. `integrable_map_measure` then transfers it to the exact map measure using a.e. measurability of Y and strong measurability of the radius power under that map measure. `integral_map` identifies the actual law integral with the actual sample integral. Both sides of `integral_mono` are integrable; no use is made of a zero value for an undefined integral. Integration of the dominating function gives `W(1+∫|x|^(2k))` because the tilt has mass 1; the raw bound gives `≤W(1+Ck)<C`. Radius-power nonnegativity supplies the separately stated nonnegative integral. Lines 165–166 close only the section/namespace.

### Boundary and semantic checks

- k=0 is covered by natural powers, including `0^0=1`; W=1 and the pushforward probability makes the zeroth moment 1. No positive-k division is present.
- U=0 gives Q=0 and, for positive k, W=0; the same proof forces zero radius and zero positive moments. The `+1` still makes C positive.
- Empty Theta requires no member or nonempty choice. The consumed existence of the raw constants and the universally quantified construction give a valid positive C; all law/moment assertions over Theta are vacuous.
- Arbitrary real probability measures are allowed. No finite support, bounded support, density, covariance invertibility, sample independence, parameter continuity, or theta measurability has been smuggled in.
- The theorem is source-faithful as a **moment-transfer dependency** of R2 lines 57–60 and 83–92: it has the actual tilt and centering and gives every natural Euclidean moment under an explicit uniform matrix-entry bound. The original standardized variable uses the actual inverse covariance square root. This theorem deliberately leaves that binding and its entry bound to a later actual whitening producer. It does not by itself prove the source's real-exponent 8+delta condition, covariance identity, WC transfer, inverse mean map, saddle expansion or root B/D closure. The root-contract true-domain restriction is respected.

### Pinned API inspection (read-only server source, no execution gates)

The designated OQ3 server worktree reports toolchain `leanprover/lean4:v4.36.0-rc1` and mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`. These were obtained with source reads and `git rev-parse`, not a Lean invocation or a broad cache/status audit. The following exact signatures were inspected at that pin:

- `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:139`, `Measure.isProbabilityMeasure_map_iff (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) ↔ IsProbabilityMeasure μ`. File SHA256 `00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b`.
- `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:105`, `Integrable.mono'` takes an integrable real dominator, a.e. strong measurability, and an a.e. bound on the norm; `:355`, `integrable_map_measure` is an iff for the exact composition with a.e. measurable map. File SHA256 `d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759`.
- `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:970`, `norm_integral_le_integral_norm`; `:1076`, `integral_map` requires the same a.e. measurable map and a.e. strongly measurable integrand on the map measure. File SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`.
- `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:513`, `pow_le_pow_left₀` requires a nonnegative lower base and an ordered-base bound and applies for every natural exponent. File SHA256 `28c0432242f3766a643689abd852cbf92fee391d314f76815e6977e64854103c`.
- `Mathlib/MeasureTheory/Measure/Tilted.lean:42–43` defines the actual normalized measure by density `ofReal(exp(f x)/(∫exp(f) dμ))`, with zero-measure behavior for nonintegrable exponentials stated immediately below. Its `integral_tilted` at :230–232 agrees with the consumed raw-moment source. File SHA256 `355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f`. The true-domain hypotheses and consumed probability result exclude that degenerate nonintegrable case here.

Mechanical receipts were intentionally not inspected until completion of all preceding mathematical/source checks.

## Mechanical and environment evidence binding

**Evidence verdict: CORRECT / existing server receipts sufficient for this exact source.** I ran no Lean command, owner audit, build, test gate, cache hydration, or cache mutation. All successful gates below were reused once, then checked by read-only record/log/source/hash inspection.

The full `u22g-receipt.json` was read only after the mathematical review: SHA256 `1f164bfedac0bd032ab52c1eac7c12f09d739aa97c35f3df8aa48d6981304f37`, 4126 bytes. Its scope/source/inventory hashes, byte counts and line counts match the independently read files. The remote run is `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22g-20261023`; the worktree is `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`.

| Existing evidence | Exact binding and result |
|---|---|
| Archived final source `source-02.lean` and current worktree source | Both SHA256 `110a16cab72d655905659b30a496625f98aa70e188b004a8713006225ab9a8e3`, 8875 bytes / 166 lines, identical to local reviewed source. |
| Full-source check attempt 02 | Exit 0, 6.305335840210319 seconds; `build-02.log` SHA256 `bd80eb82994bfd4ab23c8983ab965659facf56c8fcbca8d8f9dbe88d0cdf2948`, 850 bytes; the entire log was read. |
| First complete owner audit | Exit 0, 5.784404607489705 seconds; `audit.log` SHA256 `8e90106306ee1247c9af534815ac88b017b5195ef96ac693d8ccb6864fa09809`, 1953 bytes; the entire log was read. |
| Exact audit program | `u22g-Audit.lean` / remote `Audit.lean` SHA256 `d54f7f8da5eeea0d11b4e264b35fa2ce22ccff18ec51442be7644d04c9e09ebd`, 1891 bytes, read in full. |
| Audit record | Local and remote SHA256 `a78519cf6d1bee08a468fb0e0568e5406d844d3116bf5cfece462177f40baf82`, 498 bytes. |
| Build history | Local and remote SHA256 `e530f6eddce2f3edb0b8f290a120fd3640ad5a3bb5be61fbc357e3a3b7d0c5d7`, 1567 bytes. |
| Environment manifest | Local and remote SHA256 `4750d91c9e2065166c3198a457f60869deca606bc67c0ecb0a5498d543e23fe6`, 526 bytes; actual parent F source hash equals the reviewed F hash. |
| Actual inventory | Remote `actual-types.txt` is the same SHA256/1706 bytes as the blind inventory. The full audit log lists exactly these same three types and concludes 0 frozen definitions, 1 frozen public theorem, 3 all theorems, 3 all declarations, `U22G_AXIOM_GATE PASS`. |

Both source-check attempts and the owner audit record CPU14–17, Lean native memory limit 8192 MiB, j4, and `autoImplicit=false`. The current worktree `lakefile.toml` explicitly retains `autoImplicit=false` and pins mathlib to `807d3836b165983210ee2ecf3cd28f239436949c`; its SHA256 is `444f3a3a01fd8ff99f219cff08a99b20459c0d177c4e2c884af9eead481daf44`. The project toolchain file has SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4` and contains the recorded v4.36.0-rc1 pin. No proof settings were weakened.

The all-owner audit uses `env.getModuleIdxFor?` to identify actual ownership, not a namespace prefix. For every module-owned constant it rejects a new axiom and invokes transitive `Lean.collectAxioms`, accepting only `propext`, `Classical.choice`, and `Quot.sound`. Each of the two private lemmas and the public theorem is printed with exactly that standard-three list. No generated owner declaration is omitted: counts are three owner constants, all three theorems, zero generated theorems and zero definitions. The complete 166-line source has no `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, `implemented_by`, or proof-bypass option. This is full source-to-statement/proof review plus a transitive kernel axiom receipt, not merely a public theorem count.

### Preserved failure and warnings

Attempt 01 is retained, exit 1 after 6.624954408034682 seconds, archived source SHA256 `deb69f34fd8fb8bf062fab57f5b2056dba3269b7ad5a2ff576c4b78ceb2e29e6`, 8389 bytes / 155 lines, log SHA256 `ae1009f3b85632480117559a0c43fe5faa1be5cb05c3b688dd39e88396d22ea6`, 10860 bytes. Its five error locations concern simplification/type mismatches, an unsuccessful rewrite, and unresolved proof expressions. Read-only comparison of all three entire archived theorem statement texts through `:= by` found them byte-text identical to the final three statement texts; only proofs changed. The failed source receives no acceptance. Attempt 02 is the first complete successful check, and the recorded audit is the first owner audit. No passed gate was rerun by this reviewer.

The complete successful log has two `letI` style suggestions at source lines 69 and 129, plus Lake's local-changes warning for the accepted thin package view. These are not proof failures; no suggested linter-disabling option was added. I did not run broad `git status`, assert a clean whole cache, inspect unrelated overlay metadata, or modify the root cache.

### Focused dependency/package inspection

The current packages symlink resolves to `/root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages`, as authorized by SERVER.md and the root cache receipt. The five inspected API source files in the preceding section were each compared read-only against `git show 807d3836b165983210ee2ecf3cd28f239436949c:<path>` and are byte-identical to their pinned Git versions.

The environment-change record `u22e-environment-change.json` has SHA256 `1cd5b6af8a400bd18f3cb0b1d4d0fa3daf7dac276a49ef163e644370b8423ff4`, 751 bytes. It names the root-authorized shared-v34 package switch and no shared/binary write by the lane. The corresponding `coordination/inverse-contdiff-cache-receipt.json`, SHA256 `7b86a9666b67ef78e2beb5226707309a7e4b06ff72d7b03315ed122a83e68627`, 915 bytes, records `PASS_TARGETED_PINNED_CACHE_READY`. A targeted read of only its named `Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.olean` confirms SHA256 `1643895d9546fb472b54a89e29d500b023358851556be7750145ea3bfb6a10ac`, matching both records. This is no new cache audit or download.

The necessary accepted-source-view objects were inspected only at the three directly relevant paths. G and F are symlinks to their own lane-built objects; CovarianceWhitening is a symlink to the accepted `integration-bearing-v43` object. G object SHA256 is `4db6e4828491ef0f086d259e03125128d286d95ed5a35ddf387a4729549cf95a`; F object SHA256 is `a91518aceb2c3e577f8342b4c2c159ba02654953f70d3d16c7967e963814d367`; CovarianceWhitening object SHA256 is `1afba1a21692a5519c553d2713510818c372b67446f37e347e776741da39ff44`. Current direct-dependency sources match the local reviewed F and the unchanged accepted CovarianceWhitening hashes. The build-history field `provisional_dependency_source=ea105db471a073ac5eca67b4f94ff986766fd3fe3685790fb4859497da49289a` is the actual current `QuadraticTiltCumulants.lean` hash (verified by targeted server source hashing), not a claim that F has that hash; the explicit actual F dependency is correctly `19946...` in both receipt and environment manifest. The consumed F actual-type inventory was also read in full and agrees with its source signature; SHA256 `ca8efe662783a7821fc3d7ea1f22c4978b03a492240386468d2b5c7e918ce9ad`.

## Acceptance and remaining boundaries

**STATUS: CORRECT.** All 166 final source lines, all three owner statements/proofs, the complete frozen scope, the actual consumed interface, the original source obligations and root-contract restrictions have been reviewed. The exact source version has a successful complete server kernel check and all-owner transitive standard-three-axiom receipt. No critical gap or uncovered G scope remains. This report independently accepts U22g as the stated helper only.

The proof eliminates the all-natural Euclidean-moment transfer obligation **once** an actual parameter family of matrices with the stated uniform entry bound is supplied. Actual covariance-whitening construction/bounds for the unbounded compact tilt family, its covariance/WC consumers, the original real-exponent 8+delta step and B/D root work remain separate dependencies. Previously accepted corrected A and bounded C scope are unaffected. The report does not accept another module, certify A–F publication/integration, or close an OQ3 root group. No implementation, source assumption, shared cache, branch, status file or coordination record was edited; this report is the sole output owned by this reviewer.
