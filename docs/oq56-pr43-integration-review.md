# PR43 independent integration evidence review

Verdict: **CORRECT / INTEGRATION_EVIDENCE_ACCEPTED for the frozen two-module payload. ROOT_INTEGRATED_GATE_PENDING.** No mathematical or evidence-binding blocker was found. This is a read-only acceptance of the existing independent source/proof checks, not a new Lean run or a certificate for the complete p52/p53/OQ6/RS2 roots.

Reviewer: root-assigned `source_bridge_author`, who did not author either module. Review date: 2026-10-22. Only this report was written; no lane/source/state/import/manifest/cache/Git changes and no contact with the lane lead. The math-theorem review protocol and workspace AGENTS/SERVER/TEAM constraints apply.

## Exact publication and byte binding

PR: https://github.com/randomcat4/shao-lean/pull/43, branch `feat/oq56-balanced-block`, head `4732ef50729c0a6f39a5a7210dd3e2ad9fefe8f0`. The read-only GitHub response and the actual server Git object agree on that head. Its sole parent is the independently integrated v23 main `661318d074b04eb8ff8fa4e6b20c92f4f01982ef`. The commit adds exactly the following five files, with no modifications to existing tracked sources:

| PR path | SHA256 at the actual head |
| --- | --- |
| `Shao/OQ5/P45/BalancedBlock.lean` | `5aa37b415a44f18294bb8b9eec57685d0277a27747249bbe1d72279786c8e125` |
| `Shao/OQ5/P50/CanonicalEdges.lean` | `f81b3297213af8b8a6714e9c413d277e6aa5f023781f9619f7265925d1c79c6c` |
| `docs/oq56-balanced-canonical-scope.md` | `773020a7979549bf662e324fee9c8a90c22419dbbc87aa484099b9f6cee70fa3` |
| `docs/oq56-balanced-canonical-frozen.md` | `aedf3f0d57ff679a8c204cdc03ed261265b3dacd97063b98ffb14def08dbcba7` |
| `docs/oq56-balanced-canonical-review.md` | `2864424ec5401ca60a3fe2a171288a22402dc7b12ed3b9e1d4099cd17b436420` |

Both source blobs equal the local unit33/unit34 drafts and the exact source prefixes in the independent audits, byte for byte: 10,316 bytes/261 LF lines and 8,062 bytes/186 LF lines respectively. The three PR documents equal the local package07 documents. These hashes were recomputed, rather than inferred from the PR description. The implementation is bound to the independently reviewed frozen source bytes; the frozen contract documents have their own distinct hashes, below.

The actual head also preserves the complete three-file Shao import closure of BalancedBlock:

| Dependency | SHA256 |
| --- | --- |
| `Shao/OQ6/FiniteRows.lean` | `bb4dc865f5ab96ce57814f0721fbd31a2885d6fce7a9facd150941c4c2f91930` |
| `Shao/OQ5/P35/TargetCancellation.lean` | `b5b5f4b1bc5a3f0815253063a61fec83c0a9d677122b2db10535f4e2f933549c` |
| `Shao/OQ5/P35/RowIdentity.lean` | `73bb0809bc6d323b31775327e468677d6320b38f8fe87363936860164f17f975` |

CanonicalEdges has no Shao imports, only five pinned official Mathlib imports. The package receipt `work/oq56/pr07-packaging.json` was read on the server and rehashed as `89fcc5256121ff219ed8192404827f6dc5a862b18a020d96f1b203c435cdf6bd`; it records the same five additions, hashes, counts, unchanged existing sources and unchanged independent reports. Its mutating packaging script was not rerun.

## Frozen contracts and independent proof review

I read the unit author handoffs, package07 scope/frozen/review documents, both complete source modules, their semantic and proof reviews, and the cited original source passages. The following local hashes were independently recomputed:

| Unit | Frozen contract | Preimplementation source review | Complete never-author proof review |
| --- | --- | --- | --- |
| 33 | `unit33/frozen-v1.md`: `7b6de979a5ded92483d679a6c8c3fb98377cec90d22041aab423c7de624e8559` | `unit33/semantic-review.md`: `4fdf78b19d650ee6f05ae1162a6c9a3aef0babe9284faf65007b811fdf59c973` | `unit33/proof-review.md`: `234470a83e00bea3f7107201e6c84adcd254fcbe0e0d3e99ab17a33b42889a69` |
| 34 | `unit34/frozen-v1.md`: `61d6d0d1de93b795da25ab2506cfd2a42ebaee22864941b67e3e3eef504b94c8` | `unit34/semantic-review.md`: `ad6f83ed2044e8f93cbb94f70f46dcb5e942b198057f520b4f758f283cc7f4c9` | `unit34/proof-review.md`: `86dde00dcef0f4521954eca6145312bd79261923e4b5ff3d6094f0ba003aa90a` |

Paths in this table are under `C:/game/shao lean/drafts/oq56/`. Reviewers `oq56_verify33` and `oq56_verify34` are never-authors of the respective implementations. Their verdicts are CORRECT / LEAN_FULLY_CHECKED for these exact units. No author receipt is being substituted for independent proof review.

The precise public surface is three definitions plus eleven theorems, fourteen declarations:

- P45 definitions: `positiveKernel`, `adjustedRow`, `BalancedTarget`.
- P45 theorems: `positiveKernel_symmetric`, `centered_rowMean`, `jackknifeSq_eq_centeredRow`, `adjustedRow_eq_target`, `adjustedRow_eq_background`, `uStatistic_eq_balancedBlock`.
- P50 theorems: `pairKernel_memLp_two`, `integral_pairKernel_sq`, `integral_pairKernel_eq_zero`, `sharedEdgeProduct_integrable`, `integral_sharedEdgeProduct_eq_zero`.

Unit33 has thirteen explicitly private theorem helpers. Its existing independent exact-prefix audit matches all three definition bodies and six full frozen theorem types, with eighteen loaded-definition `rfl` checks and five additional loaded dependency type checks. Unit34 has three explicitly private law helpers and no definitions; its five complete frozen polymorphic types are independently restated as compiled assignments, also recorded with fully explicit type printing. The source inventories and freezes contain no extra public interface or changed premise.

## Source semantics and proof risks

Original source binding, all under `C:/game/shao/current/oq56/inputs02/`: p45 SHA `0b799637356615cfb18a9fef016c11d682aeefde314106e0b56eb46a853c09ca`; p53 SHA `0bfadbb2021248859f8b15df2ff184c73c879a7203991c27fdc4f5dd6c04f561`; p50 SHA `de553dc827eeadbc1e863c1778caa9bdeb00bca84110b4666b06cab053d7b768`; p52 SHA `615209f8501e14a6bfaee220899c30891510fef5987c9abf7f74ac52b6538b45`. These local hashes were independently recomputed. Historical approval labels are not premises.

**Finite positive balanced block.** P45 lines10–49 and p53 lines72,90–103 use the positive residual sign `h_ij=G_i+G_j+Z_i Z_j`. The source really defines this sign and proves its global-negation connection to `P35.kernel (-G) 0 Z`, separately checking row, once-counted U, adjusted row and centering. It does not reuse the old same-sign target cancellation with its different tuning. `U` counts each unordered pair once and divides by choose(n,2); `q_i` excludes the diagonal and divides by real `n−1`; the original centered jackknife is `4(n−1)/(n−2)^2 * sum(q_i−U)^2`. All subtractions occur after casting n to the reals, with statistical identities requiring n≥3.

The adjusted row is `b_i=G_i+Z_i(sum Z−Z_i)/(n−2)`, and the proof gets `q_i−U=(n−2)/(n−1)*(b_i−mean b)` and hence the original `R²=4/(n−1)*sum(center b)^2`. BalancedTarget requires target `G_i=A_i+d`, target squares `Z_i²=t²`, target feature sum zero, and `d=t²/(n−2)`. It yields target row `A_i+Z_i S_B/(n−2)` and background row `G_i+Z_i(S_B−Z_i)/(n−2)`. With K=|J|, the exact numerator is

`U = K*d/(n−1) + (2/n)*sum_target A + (2/n)*sum_background G + (S_B²−Q_B)/(n*(n−1))`.

The target-only A and every background term are preserved. The empty/full target, t=0 and deterministic odd-cardinality cases do not create a false probability claim; no positivity of R, rank statement, iid law or tail limit is asserted by this finite unit.

**Actual canonical L2 edges.** P50 section6, especially lines169–208, and p52 lines88–108 require a general canonical residual kernel, not merely the scalar rank-one product formula available in FiniteIIDMoments. The new code keeps the actual measurable family X under the actual probability μ and common law ν. Its private helpers derive the marginal pushforward from IdentDistrib, the distinct-coordinate pair law from actual iIndepFun, and the distinct-coordinate triple law on `(ν.prod ν).prod ν`. No joint-law or desired moment conclusion is assumed.

Pair-edge L2 is pulled back through the proved pair measure-preserving map. The square identity uses the same population second integral and genuine square integrability. Zero mean first gets genuine population L1 from L2 on a probability space, then uses integrable product Fubini with the a.e. canonical right-row condition, then transports to the sample pair. No everywhere-integrable-row premise or unnecessary globally measurable representative is inserted in that theorem.

For a shared-first-vertex product `r(X_i,X_j)*r(X_i,X_k)`, L1 is proved from two actual L2 edges before any cross integral is evaluated; adjacent edges are not assumed independent, and no fourth moment is required. The final proof transfers that L1 to the actual triple-law integrand, derives a.e. integrable sections from population L2/L1, pulls canonicality along the first projection, and supplies explicit triple L1 to Fubini before transporting the zero integral back. Thus totalized nonintegrable Bochner integrals cannot explain the cancellation. All three indices are distinct. No symmetry is silently used to change edge orientation or to control the diagonal. The frozen `Measurable r` premise in the shared-product results comes from the source's Borel version; the index and observation types retain their full frozen generality.

## Actual receipts, reused without rerunning Lean

Raw artifacts were read directly under `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/work/oq56/`. I independently verified all seven artifact hashes referenced by unit33 final-clean and all ten referenced by unit34 final, with zero mismatches, and checked both complete source-prefix equalities against the actual PR blobs.

| Evidence | Recomputed SHA256 | Existing actual result |
| --- | --- | --- |
| `fresh-review33/target.json` | `6be49eda6f5917107dac433691fc4d3d0ce2f3c3a21601429160924586491141` | exit0,3.172s, empty stdout/stderr |
| `fresh-review33/final-clean.json` | `f3859c03b30cb40b6cc3022cae7d4740af411c5fd9dac7f260d5e343b1b968ac` | PASS, exact frozen/body checks, stable four-file closure |
| `fresh-review33/ExactPrefixClean.lean` | `9816995d50883599cb821f61013273a0fc6b7ded0481e4c51a3f1b37f6bfe6c8` | exact10,316-byte implementation prefix |
| `fresh-review33/exact-prefix-clean.json` | `82d32ba455d681eeecabee823138aacce17266f41954e17cd67cd39a8fc27a02` | exit0,3.429s, no diagnostics |
| `fresh-review34/target.json` | `d41df2bda0c3601ad07ffed77e56029258846b5e273b57d094ab5a6814815748` | exit0,4.102347809821367s, empty stdout/stderr |
| `fresh-review34/final.json` | `d3bd6a4d3c73a41bae66ea7ce88de927e32f3ee9170bd13c0372044dfd519220` | CORRECT, five full types, stable source |
| `fresh-review34/ExactSourceAudit.lean` | `a0ba079826c8369d7dbf17b5fe5d9924bb28134ba0b223c3cd8df133ba2acd16` | exact8,062-byte implementation prefix |
| `fresh-review34/prefix.json` | `d28afb062771190612dd251e7bf5af18ab0e55b91e0ef879f3ce29798ee55f80` | exit0,4.216019472107291s, empty stderr |
| `fresh-review34/frozen-type-comparison.json` | `34f4e90a8ec7d863aa7c260fb79198b2c0c796f488ba0ff673d479ad532fbec2` | all five headers match the freeze |

The independent audits freshly elaborate the entire implementation prefixes, rather than import an own-module olean. Unit34 retains33 unused-binder warnings solely in the later frozen-type example appendix, after source line186; the actual target and implementation prefix have none. Unit33's earlier appendix-only warnings have a clean later receipt; no source change is involved.

I parsed the raw saved axiom output as well as its JSON summaries: unit33 has29 queries (9 new public+20 dependencies), unit34 has24 (5 public+3 private+16 official dependencies), every entry restricted to `propext`, `Classical.choice`, `Quot.sound`, with no sorryAx. All13 unit33 private helpers were included in fresh complete-source elaboration. Existing independent comment/string-aware scans of the complete source closures contain no prohibited code tokens. The recorded compiler is Lean4.36.0-rc1 commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`, Mathlib actual HEAD/manifest `807d3836b165983210ee2ecf3cd28f239436949c`, manifest SHA `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`; commands were server-only with CPU affinity0–3. No Lean, predecessor target, full build or cache operation was repeated for this acceptance.

## Required root gate and still-open roots

The lane evidence is sufficient to accept this payload for root integration, but **does not itself close the root all-module-owned gate**. Public transitive queries, selected private queries and fresh private-helper elaboration do not enumerate every private/generated declaration attributed to the actual imported modules. Root must retain the frozen bytes while adding the two imports and the eleven exact theorem names, audit all fourteen public declarations and every module-owned public/private/generated constant with the transitive whitelist, run the whole-library integrated gate, and bind its exact source set, pins, final head and merged main tree to the resulting receipt. The current main `7103c4020b4be4f25f6d1528c6c42ab087f82b68` was supplied by the coordinator; that newer merge object is not present in this read-only lane Git object store. No fetch or branch mutation was done to manufacture an integration claim. Compatibility and the final all-owned counts on current main remain root's actual gate.

The complete original p52 and p53 counterexamples, OQ6 and RS2 remain OPEN. In particular, these units do not establish the fixed iid infinite-layer construction/Borel encoding, same-law simultaneous exponential moments, actual layer-conditioned background law, sparse sequence selection and rare-event probabilities, positive residual operator/rank and full Studentizer positivity, or either actual tail failure. Within the canonical-background chain, arbitrary edge orientations/symmetry, disjoint-edge classification, finite counting, row covariance, centered row energy and G/background cross terms remain later dependencies. Within the positive-block chain, the finite identities still need source-law specialization and its conditional moment/event estimates. None may be treated as a supplied target bound or hidden premise. C1/C2, OQ3 A/B/C/D and OQ4 are also unaffected and remain open under their separate lane contracts. The separately integrated original OQ5 p35 sections1–7 remains CLOSED/LEAN_FULLY_CHECKED at v18; the earlier PR33 finite foundations are already integrated and are not this Unit33.

Acceptance is therefore exactly the immutable eleven-theorem/three-definition prerequisite payload at PR43 head4732ef50729c0a6f39a5a7210dd3e2ad9fefe8f0, subject to root's complete integrated gate. No unresolved source/proof/receipt defect was found in this payload.
