# Final independent machine supplement

Verdict: **CORRECT_FORMALLY_QUALIFIED** for the exact new uniform Gaussian-tail theorem. `formalQualified=true`. The unchanged, previously complete independent source/proof review is combined with the exact-source kernel receipt, complete actual-owned type review, and transitive all-owned axiom audit. No uncovered declaration, value, assumption, or mathematical gap remains within this one-module scope.

This supplement was completed by the same independent reviewer, `/root/uniform_gaussian_tail_formal_review001`, separate from parent author `01a174b9-5b2e-7611-ba13-02580d678eb3`. Its parent activation SHA256 is `0dfe20b5bdf80e4aba64836643e950a8648dd6a546eeb89ee5fd30290802eaf0`. All 18 input records were verified by SHA256 and exact byte length before review and reverified at sealing. No machine command was rerun by this reviewer.

## Reused complete source/proof coverage

The exact source remains SHA256 `7294125186fa502c7c89b0c19a345c93c9fa902ab1584825e7777fcb717fc888`, 2025 bytes, 41 LF. The frozen head remains SHA256 `fcc23bb992d2cb32b83246d4c2cc0b1d2065f73dd4d9e15808a7025c36b27671`. The immutable 7917-byte complete source report, SHA256 `9af78312172693581e0bc1b515c1a51da01efdf9bbcdfd6cfec0b1819dad9e76`, already covers every source line and the complete sole proof, including unit220 section 2 correspondence, the public Gaussian interfaces, positivity and cancellation, polynomial/exponential estimates, and coefficient. It is reused exactly, without another complete proof review.

The prior payload seal SHA256 `317b7cc17750d8220aacbf64955d8e7daf55e0fcee824345ee8c216385e9e8df` and natural release SHA256 `4578f43497d433df72ba97cadb2641b3ddc0488ac491152bd9a7c4e663ef4b32` are unchanged. All five old payload records and the release-to-seal reference were reverified; the canonical old payload hash is `b0b6d3e17d0a384e6c9acff1c43072722dcb1a2fda697cec927ac1756cf9c560`, also matching the parent source-stage acceptance. The old source-stage verdict remains an accurate historical pending-native record; this supplement supplies the missing final evidence.

## Original kernel object and dependency chain

`kernel001` started at 2026-10-25T22:00:03.961278+00:00 and ended naturally at 22:00:09.511031+00:00 with RC 0 and zero error headers. Its before/after source hashes both equal the exact reviewed source. It produced the original 268896-byte object SHA256 `9df4c5074c0eccad81d30911c35aa2d4dbb41f895b5cac8220a2406f80928349`.

The alias-binding receipt records that the own-output import alias was previously absent and points to that same original object, with identical hash and size; its setup performed zero Lean/AX commands and zero shared-package cache writes, and found no uncertain prior audit effects. `audit001` subsequently imported that original object, ended naturally with RC 0 and zero error headers, and reports the same source before/after hash and original object hash/size. There is no substituted source or second independently compiled proof object in this chain.

The source-only import setup binds the accepted public `GaussianTail.lean` source SHA256 `f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922` and both canonical/own dependency objects to SHA256 `37aa119d788f35dd21146e35116823ae689204c91553c3f5f43a386d2234013d`. That setup had zero heavy commands, zero Lean/AX, zero old-producer checks and zero cache writes. Its phase18 preparation is distinct from the phase19 native execution; no old producer proof or check was replayed for this supplement.

## Complete actual type and owner review

I read the entire untruncated 2145-byte, 31-line `actual-types-values.txt`, SHA256 `034a124c00581f25b244989b4f78474d0cd779cbb7e94fc2b19092afc0bfb7a9`. The index binds it to the exact source and original object and covers lines 1-31. There is one `TARGET_DECL`, one `ACTUAL_TYPE`, zero full-value blocks and zero truncation markers. The extractor's nine file rows were checked against the local compact receipts, and its raw-log hash equals the audit result's log hash.

The sole actual declaration is `Shao.C2.UniformGaussianTailPolynomial.standardNormalTail_cubic_uniform_bound`. Its complete expanded type has exactly two binders: `x : Real` and `hx : 0 <= x`, with the order supplied by `Real.instLE`. Its conclusion is real order between:

- `(1+x)^3 * Shao.standardNormalTail x`, using real addition and multiplication and natural power 3;
- `(16/3) * (Real.sqrt (2*Real.pi))^-1`, using real division, multiplication and inversion.

Every explicit numeric cast and typeclass instance in the expanded type was read. The natural exponent 3, real numerator 16, real denominator 3, square-root argument 2*pi, and inverse normalization all match the frozen head and reviewed mathematical statement. There are no additional binders, hidden local lets, extra typeclass hypotheses, law assumptions, restricted positive-x domain, or altered coefficient.

The actual owner inventory selects every target-module-owned constant, including private/generated declarations. It contains exactly **1 owner, 1 theorem, 0 definitions/non-theorem values including private/generated, and 1 public theorem**. Its sole name/kind matches the complete actual-type index. Thus all actual owned types are covered, and the zero non-theorem-value obligation follows from the machine owner inventory rather than source syntax. No generated or private value is left unreviewed.

## Transitive axioms and resource evidence

The audit reports `PASS_ALL_ACTUAL_OWNERS_TRANSITIVE`. The complete owner report has status PASS and gives the sole theorem's recursive `collectAxioms` result as exactly `[propext, Classical.choice, Quot.sound]`, equal to the allowed whitelist. The target-module ownership selection is not a theorem-name prefix filter. The owner-report hash in the audit result matches the supplied owner report; the exact source/object/type/extraction chain is consistent throughout.

Both native starts bind phase19 SHA256 `ea083f6a6392b08d62320ba9440b935a231b95cc37970be0db24723efc138c9d`, native flags `-M8192 -j4`, CPU44-47 and `c12-heavy.lock` held for the actual target. The kernel stage finished before the audit stage began. Complete thread-record checks find all 5 observed kernel-stage user threads and all 4 observed audit-stage user threads restricted to exactly CPU44-47. Each stage separately records one `iou-sqp-*` kernel I/O helper with first/last CPU ticks zero and the known OS affinity 0-255; it is correctly classified separately from user computation, with no helper affinity change. Recorded aggregate-memory peaks are 164.3592 GiB and 164.4504 GiB, both below the 180 GiB watchdog threshold. The extraction receipt observes the C12 lock free after audit. These are observed receipt facts, not a new live server probe by this reviewer.

## Final scope and release

The combined coverage qualifies only the frozen uniform-tail theorem in this exact module/source/object. It does not qualify all of unit220, a publication or integration snapshot, or the C2/C12 root. C2/C12 remain OPEN; OQ3 remains PAUSED_BY_USER.

No source edits, local/remote Lean or AX, server access, uploads, Git/API publication, or child delegation were performed during this supplement. All earlier source-review artifacts remain immutable. The new supplement outputs are sealed and the reviewer releases naturally with every writer/execution/inflight counter zero.

Configured model/effort: `gpt-6.1-sol` / `xhigh`. Actual backend/model/effort and input, cached-input, output, reasoning-subset token counts are unobservable and recorded as null; no backend or usage telemetry is inferred.
