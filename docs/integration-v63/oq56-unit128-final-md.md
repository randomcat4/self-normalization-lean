# Unit128 independent final review

STATUS: **CORRECT — LEAN_FULLY_CHECKED for the exact frozen Unit128 scope**

The repaired source faithfully implements the frozen normalized original U-statistic, row means, centered-row jackknife, population-centered Studentized statistic, actual tail probabilities, a.e. denominator positivity and the two tail-limit transfers. Its exact server kernel check succeeded. One subsequent independent, sole-import, no-`-o` audit of that exact object succeeded; every actual owned type, all actual non-theorem values and every transitive axiom list were completely read. No critical gap remains in this unit.

This accepts an auxiliary source-bound unit. P53, OQ6 and RS2 remain **OPEN**. It does not establish an existential/root assembly, positive PE, whole-kernel PSD or a new historical-priority claim.

## Independence, source and freeze

Reviewer `/root/oq56_final128_r2_fresh` is permanently `NEVER_AUTHOR128`. The OQ56 lead is `AUTHOR128`, permanently `NEVER_FINAL128`. The author and reviewer are separate contexts. This review uses math-theorem; math-ultra and subagents were not used. Model/effort: gpt-6.1-sol/xhigh. Token usage and subscription allocation are unavailable; no counters or allocation estimates are invented.

The exact current source is `drafts/oq56/unit128/lead-author-repair-02/SparseNormalizedRealStatistics.lean`, 12091 bytes, 225 lines, UTF-8 without BOM, LF endings:

`5b811028a95afa915b0c70ba8d7c4da371bf8672d243dc16a3421dee54c553fa`

Its compiled object is 249792 bytes:

`76a96c16ad5ec6798f78e4b3b58aa67bd181f4271f1e4bc85449e6c614c84f32`

The server source/object mtime_ns values are respectively `1792791074467442564` and `1792791115143329987`. Freeze JSON SHA256 is `c296cca19807ab025f06cbf6745ddff3491222f515627dc46fc89dbbb2adeabf`; freeze Markdown SHA256 is `e736efa1c29d18239122df8ecf6449dffbc3c3dcfb7dab9ca6825ed8744c1501`.

I reuse my own complete static reading of this exact source, all proof bodies and both complete frozen contracts, recorded in `current-static-source-review.md` SHA256 `cba29f708c6bda73e83ef8ec1e14d4ad2ee9b9f68fe8b044f14e0a6300ce1dab` and JSON SHA256 `ee03df597b9a7e1bbb627f8d92a48aa55dad2e077c4301fe516d0a84c61c744a`. The current local source, author input, installed source, accepted object and final server descriptors were re-bound to those exact bytes. All six full public definitions/values and fifteen full public theorem contracts match the freeze literally, and both imports match. No assumptions changed. That complete source/proof review is incorporated here; it was not replayed after the successful check.

The source-only count is 25 declarations: six definitions, fifteen public theorems and four private helpers. It was used only as an inventory floor. The final coverage count is derived from actual imported module ownership, not that lexical count.

## Mathematical and source-fidelity findings

Original p53 and p45, and the complete scope01 definitions, were read in the static review. The same fixed real probability law is retained, with the same α, given sequence x and selected N. Normalization scales the actual real kernel by the positive fixed scalar c obtained from its actual projection second moment. There is no replacement with a model constant and no sample-size-dependent change of law.

The actual imported FiniteRows definitions were checked. U averages every unordered off-diagonal pair exactly once using the inverse binomial coefficient. Row i excludes its diagonal and divides by n−1. R² is exactly `4(n−1)/(n−2)^2` times the sum of `(rowMean−U)^2`. R is the real square root of that square. Neither an uncentered row square nor a redesigned denominator is substituted.

The four private proofs distribute an arbitrary real scalar through the actual pair sum, U and erased rows, then through each centered difference and its square. Every original coefficient remains intact. These are polynomial/ring rearrangements and finite-sum identities, with no cancellation by n, n−1 or n−2. They therefore apply to all n, including 0, 1 and 2 under total real division. The public U/row/R² scaling results instantiate these exact helpers with the actual kernel: U and row means scale by c, while R² scales by c².

The R identity uses nonnegativity of c² for square-root multiplication and c>0 for `sqrt(c²)=c`; it does not impose an extra sign premise on the original square. The normalized T definition first subtracts the actual integral of the normalized kernel against the same product population measure. Its proof then uses the accepted theorem that this true population mean is zero. After substituting the U and R identities, it cancels only the nonzero fixed c. Thus Tnorm=T holds pointwise for every finite observation vector and every n, including R=0. No bound c≤1, monotonicity of x or nonzero sample-denominator premise is used.

Measurability covers U, every erased row, R², R, the actual population-centered T and its composition with the actual infinite-sample prefix. In the repaired row proof, `hpair` explicitly has domain `Fin n → ℝ`; it is formed from the same two measurable coordinate evaluations before composing with the jointly measurable actual kernel. The new kernel receipt resolves the former elaboration failure for this exact source.

Equality of the actual tail sets gives equality of their actual probabilities for every n and real y under the same whole infinite iid real law. Genuine a.e. R>0 for each fixed n≥3 transfers separately by c>0; the pointwise T identity does not use that probability result. Both tail limits retain all frozen hypotheses, the given x, the selected N, thresholds `x (N j)`, the literal logarithmic normalization `−x²/2`, and the actual standard-normal upper tail.

The consumed accepted interfaces were checked against their exact source/object evidence, without recompiling or commissioning another complete review of old proofs:

| Dependency | Source SHA256 | Object SHA256 |
|---|---|---|
| Unit127 SparseRealNormalization | `d02519beb7b06b9f0a7d0d8ae09681550dd6559005f59c0429155abec2ca4424` | `5c93902a5c9d395772bc6a6adac1daf708401a16bda01adaac993bca065bdd16` |
| Unit124 SparseBalancedTailLimits | `0865f412c97cf2798eb7e8a7061fabd40f8384c54d0f038d13fc2004639fb4ab` | `f6c69598849d6f250328421f53612d8e6d73d7172fe8db5575e2411642cfe2d5` |
| Unit116 SparseRealStatistics | `f6ea65cb8c923e4911f51abeaeaf0a2a697061f1dd2241a8e54e41ae627c5aeb` | `be391f18c2e3d4c413d161bc70adc59ebbb54c08b7b82999fa72d01b658dcf97` |

## Successful exact-source and exact-object evidence

The preserved author-01 failure applies to old source `6aad0528…864236`. The only repaired body is `measurable_sparseNormalizedRealSampleRowMean`; the other 24 complete declaration segments, all 25 headers, six definition values and both imports are byte-exact. The old failure receipt remains immutable and was not replayed.

Author-02 is the first clean check of the repaired current source. It succeeded in `5.29770328104496` seconds, with exit code 0, empty stdout/stderr, no warnings/errors, no timeout, no cleanup, no ownership issue, no post-check error and an ended owned process group. Receipt SHA256: `adc935be92b01c4df86204ef892e105e3f337ab2da5574bf4502a1c6c20f4543`. Author config SHA256: `81c9677a9d2f80799150eca76d8219fda3420bf45db17894e4480c4c4c610e82`. AUTHOR-STOP, RUN-ENDED, author handoff, author DONE and lead evidence acceptance were hash-validated; the author source/object/check authority was permanently released before this audit.

I ran exactly one reviewer Lean invocation, `owned-object-audit-02`, importing only `Shao.OQ5.P53.SparseNormalizedRealStatistics`. It used the accepted object, without `-o`, source-prefix re-elaboration, extra imports or another source build. It succeeded in `4.507107572630048` seconds. Audit receipt SHA256: `d6d65398893cb0f802dc9245c268533e63ba826da632d860c4d33c9407aaf7fc`; audit config SHA256: `4d99bdeafbbddafbf081f26502036b73bc45f1450798354e583672cbbbe105bf`; audit input SHA256: `62a5dadaffa4bce3d83e563e097f8ded520e652062af656c95b41e064dfd4116`. RUN-ENDED SHA256 is `b15e6f5a9a1072f33264a4cf9350aec5ff890c71af009b036a761b42f5c12357`. This successful reviewer Lean invocation is permanently stopped; no second Lean invocation is authorized or needed by this verdict.

The mature runner and audit template hashes were checked: runner `196f00b955983a076a23638630598993943dc95d902856efb4fdcf1a170e7807`; template `3dfd30bde5a70fed91965aac1e7cc75f3c9fed21da4aea16e3051c18a35cb8ac`. Resource enforcement was CPU22–25, native `-M8192 -j4`, one lane-heavy lock, at least 28 GiB headroom and 20 GiB reserve, without RLIMIT_AS. The external CPU0–9/80 GiB workload was untouched. All Lean ran on the designated server; local Lean calls, cache writes and Git mutations were zero.

## Complete actual-owned type/value/axiom reading

The audit traversed the entire imported environment and selected constants by actual module index obtained from the owned anchor. It did not select by a public name prefix. It found **28** owned constants: 6 source definitions, 15 public source theorems, 4 private source helpers and 3 generated simplifier helpers. All 28 types, all 6 non-theorem definition values, and every one of the 28 transitive axiom lists were read literally and completely in three consecutive batches, indices 0–9, 10–19 and 20–27. There was no factoring, elision, pretty-print truncation or count/hash-only acceptance. The raw 33906-byte stdout and extracted literal expression corpus stay on the server.

The six actual definition values were checked against the source meanings of U, erased row, original jackknife square, its square root, T with the true population integral, and the actual infinite-sample tail event. The fifteen actual public theorem types retain exactly the frozen quantifiers, hypotheses, functions and conclusions. The four actual private helper types match the arbitrary n/a/H finite-sum and square-scaling statements reviewed in source.

All three generated declarations were individually read and mapped:

| Actual inventory index / private suffix | Actual mathematical type and source meaning | Transitive axioms |
|---|---|---|
| 2 — `normalized_square_scale._simp_1_2` | `sum (a*f i) = a*sum f` over a nonunital nonassociative semiring; factors c² out of the centered-row square sum in source lines 76–81. | propext, Quot.sound |
| 5 — `normalized_square_scale._simp_1_1` | `a*b−a*c = a*(b−c)` over a nonunital nonassociative ring; factors the scaled centered row difference before squaring in lines 76–81. | empty |
| 17 — `normalized_row_scale._simp_1_1` | The same reverse finite-sum distribution, used in the erased-diagonal row identity at lines 69–74. | propext, Quot.sound |

The remaining 25 axiom lists are each exactly `[propext, Classical.choice, Quot.sound]`. This gives 79 axiom occurrences across 28 complete lists. No new axiom, sorryAx, unsafe/native bypass or opaque constant occurs. All actual types, names, definition values and axiom lists are individually bound in `owned-expression-coverage.json`, SHA256 `4039dbb689fe5abef744a35cfea890aa07e33d5d085b321794cdf395fcddf626`.

The plain marker parser round-tripped the entire raw output, verified unique names, all present bodies, exact TYPE/VALUE ownership alignment and the final actual count, and rejected ellipses and pretty-printer failures. The complete actual module inventory equals the 21 frozen public declarations, the four private helpers and precisely the three generated helpers above.

## Final preservation and release

The metadata config inherits the entire 804-record author after-map, then protects the new own object and author receipts/seals/outputs, canonical map, audit input and static reports. All 819 configured records use FULL_SHA_BYTES_NS; the actual audit before/after maps each contain 820 records including the audit config itself, and are exactly equal. The first-created own object was correctly taken from author.object_after/STOP.object; it is not incorrectly required to have existed in the author before-map.

All 44 canonical source/object pairs (88 descriptors) were matched by module, with their exact key-to-physical-path associations retained, including the two accepted symlink-backed records. The entire prior Unit129 factor corpus and its metadata remain protected and unchanged. The sole historical rebinding is the explicitly authorized old failed Unit128 source to this repaired source, after Unit129 reviewer DONE and lead qualification; no successful prior source or object was changed.

Final server validation rehashed every one of the 820 actual guard records, checked all post-audit expressions/summary/coverage bindings, the current source and object, both author/audit ended states, all canonical descriptors, current tracked-clean Git state and all 73 own refs. HEAD remains `344ee3b7f346e14a3a02e4d6b29ae16f4ad19e35`, tree `7fc28991a9dada56317c602fc78e6c8f7a4c0b52`, branch `refs/heads/feat/oq56-p53-normalization-v41`; pinned mathlib remains `807d3836b165983210ee2ecf3cd28f239436949c`. The final observed lane-live Lean/lake list was empty. Validation SHA256: `c8192a1abc751b5604e893b5539f102d8a36a3e54343bd83da5ba13472d6ad0c`.

I release this reviewer’s write/check authority on completion of the accompanying DONE seal. No further Lean, source/object edit or evidence replay follows from this verdict. The next mathematical work belongs to the lead’s remaining source-bound dependencies; this review closes only the exact Unit128 auxiliary obligations above.
