# Unit118 independent final review

STATUS: CORRECT

The exact frozen Unit118 scope is fully reviewed and server checked. The actual balanced-event probability is `choose(n,2) * labelMass_j^4 * q_j^(2*(n-2)) / 8`; at positive levels this specializes to p53 section 4 equation (8). Strict positive event mass is proved before either conditional probability measure is normalized. P53/OQ6/RS2 remain OPEN.

Reviewer: `/root/oq56_final118_fresh`, fresh gpt-6.1-sol / xhigh, permanent NEVERAUTHOR118. I authored no mathematical source or proof. Ownership was confined to this review directory and new remote review artifacts. Accepted old proof/kernel/axiom evidence was reused at exact hashes; no old proof or unchanged old module was rechecked.

## Exact reviewed source and original scope

- Module: `Shao.OQ5.P53.SparseBalancedMass`.
- Final source: SHA256 `0aceb5f9fa55332c619a779bb764f5eef8ce1e6b509994f131a3c12756ebd075`, 14429 bytes, 317 lines, UTF-8 without BOM, LF only, one final LF.
- First successful reusable object: SHA256 `741dbe41c37a8f96674e4dc239d4f01170877faeff0766ef031bc6df320fab3c`, 599208 bytes.
- Frozen JSON: `6f9f7a4b19d0ff4cfe9c68aad19786dbc0129b05bccdd3aecbdac2655212a545`; frozen Markdown: `3354375bb2b4c9b4d59c2287096d2349dd4f642d4f647a4fa1e51fa124e5888a`. All 13 public theorem types, both imports and the observation notation are exact. There are zero public mathematical definitions.
- Original `C:/game/shao/current/oq56/inputs02/p53.md`: all five sections read completely, SHA256 `0bfadbb2021248859f8b15df2ff184c73c879a7203991c27fdc4f5dd6c04f561`.
- Actual `p45.md` section 1 read completely, source SHA256 `0b799637356615cfb18a9fef016c11d682aeefde314106e0b56eb46a853c09ca`.

Every proof and private helper in the strict 316-line source `0600dad2605c94052852b814d299cce1d22cc823073f5bcd8d957a8863f3e33d` was read. I then read the complete exact repair02 diff and all eight changed declaration bodies. A separate deterministic comparison regenerated the diff exactly, confirmed the other eight declaration spans byte-identical, and confirmed every header, import, option and mathematical premise unchanged. This gives complete final-source proof coverage without repeating unchanged reading. `static-review.md/json` and `repair02-review.json` retain the detailed reading record.

## Mathematical and source-to-statement review

The observation type is literally `((Real × (Nat × Bool)) × (Nat × Bool))`, with the actual law `((noise × signed B) × signed C)`. The consumed definition values and declarations are those of accepted units98/100/102repair01/105/106/112/117. In particular, unit117's exact six event definitions and rectangle/disjointness interfaces were read at source `508223229fdf89bd576f1f72c7520844430d28d0793c1e3f394a2f3a86ca11ff`, qualification `9d5559797234e1399066b969f683c5106a9dcb3fb70f634a795cd1495949e5fe`. Unit112's complete actual population-prefix law was read at source `a6836b75d1c7ad3713124bbe45f9fd6903519b7460bb247bb3987f28d7e011bc`. Old dependency proofs were not reread. All dependency source and qualification hashes, and accepted scopes, were verified; their bindings are retained in the static record and final JSON. P35 counting/noise interfaces and the positive-mass definition match the root-v53 source map, receipt `6c4c3ff622f79210bcef2c86aadd90f9b2f9095afd5d45ba4da412629b5956d2`.

The low observation requires both `B<j` and `C<j`; neither sign nor noise is restricted. Each label restriction has mass `q_j`, so the exact observation mass is `q_j²`. A target fixes `(B,eta)=(j,true)` and `(C,epsilon)=(j,b)`. Each actual signed atom has mass `labelMass_j/2`, giving target mass `labelMass_j²/4`. These equalities are established in ENNReal and then in real measure using nonnegativity.

For a fixed `i<k`, the actual finite product rectangle contains precisely those two opposite-sign targets and `n-2` low observations. Its mass is `labelMass_j^4 * q_j^(2*(n-2)) / 16`. The two orientations are disjoint and have equal mass, producing `/8`. Different sorted target pairs are disjoint because every other observation is low. The private counting helper uses the accepted symmetric off-diagonal identity and exact binomial pair-count identity; it yields `choose(n,2)`. The finite disjoint union therefore gives the whole-event formula.

The prefix event is the literal inverse image of the finite event under the whole population-prefix projection. Unit112's full infinite iid population law gives exactly the finite product law, transferring this actual event probability. No feature marginal, finite proxy, abstract probability formula or conditioning premise replaces the population construction.

All structural formulas quantify unrestricted `alpha,x,N,n,j` and retain the actual residual mass at `j=0`. Only the separate positive-level formula uses `1≤j` to substitute `sparsePositiveMass`. At `n=0,1` there is no sorted pair and the binomial coefficient is zero; at `j=0`, the actual prior mass is zero and the `n=2` zero exponent correctly leaves the all-target case. The fixed-pattern order itself supplies two distinct indices and hence `n≥2`. No boundary is silently dropped.

For `j≥1`, accepted positivity of the label mass and `q_j≥3/4` make the actual oriented pattern mass positive. With `n≥2`, the binomial coefficient also makes the actual prefix-event mass positive. Only afterward are the two normalized conditional measures shown to be probability measures, by contradicting a hypothetical zero event measure. No alpha/core assumption, moment assumption, positive-mass premise or hidden normalization assumption is added.

This closes the equation-(8) event-mass/positive-conditioning interface. It does not establish conditional second moments, logarithmic asymptotics, tail failure, limits, novelty, or any root theorem.

## Same-object complete ownership and axiom review

After author first-clean STOP/ENDED, I ran the unchanged mature audit template with data substitutions only: one sole import of `Shao.OQ5.P53.SparseBalancedMass`, no `-o`, no canonical proof re-elaboration. The audit anchor is the actual imported theorem owner. It enumerates that module's actual constants, prints every type and every definition/opaque value, and computes each constant's full transitive axiom list. No extra Lean call was needed.

Actual ownership is **25**, derived from the actual names/kinds and source/freeze maps; the lexical theorem floor16 was not used as a declaration count:

- 13 frozen public theorems and 3 private source helper theorems.
- 3 generated tactic theorems: the two conditional-probability `_simp_1_1` declarations and private `balanced_sorted_pair_count._proof_1_1`.
- 4 lazily materialized parent equations: `sparseTargetObservation.eq_1`, `sparseLowObservation.eq_1`, `sparsePopulationMeasure.eq_1`, `sparseGBaseMeasure.eq_1`.
- 2 generated notation definitions: the `SparseObs` macro and parser descriptor; both complete values were read and expand to the literal nested observation type. There are no opaque values or new axioms.

I fully read all 25 types, both definition values and all 25 axiom lists, including each private/generated/parent equation. Every proof/definition body is present. The actual 64 axiom occurrences use only `propext`, `Classical.choice`, and `Quot.sound`. The two simplifier auxiliaries use `propext`; the arithmetic auxiliary uses `propext` and `Quot.sound`; both notation definitions have no axioms. Every other owned theorem uses the permitted three. There is no `sorry`, `admit`, added axiom, `unsafe`, `native_decide`, `extern`, `implemented_by`, or proof/linter weakening.

The plain-marker curator exactly roundtrips the server output, verifies unique names, type/value alignment and body presence, and rejects ellipses/pretty-printer failures. All expressions were complete; no expression gap remains. The per-declaration reading coverage is in `owned-expression-coverage.json`, SHA256 `b5a298982e1e82f4955d1d4428613f40c5814e10314e4eadc5825c11466e342c`. Curated expressions SHA256 `227d28dec6d38fb5ec505cd3ec77b278d57c2f38d545afdae9cb7d626bedf5d7`; summary SHA256 `4950ccb903eb70a00eba341962c7fd073c42f8efbef48a92c4c14706e5191f8e`; raw output stays on the server, SHA256 `68eb44856124f64e5be931d1b8d42f2631b71ddb20ea59fed0175415f650a18a`.

## Server receipts and preservation

Author gate02 checked the complete final source and created the exact reusable object with exit0, empty stdout/stderr and no diagnostics. Receipt: `e966bf238d8b062dc6343ffd09a910d834de2681aef8cda6534b3fb7adab9f35`; author STOP: `01da228439dc977873ff386883d8ca9ab5b480eaf596659fbd2fd40ccd2ad5ec`; ENDED: `8ec16b68dbae1185928636c7b1f88969e271531ae22088c8835570a33d50b63c`.

The one reviewer metadata call passed with exit0, empty stderr, no diagnostics and all owned processes ended. Receipt: `a445d60fff81d03eb4d09e26ea515ab99e6e92094ac2e4a4166aac876b59d1d1`; ENDED: `119bbe3254e638258c969a3021afc5237b6a6595c0c7e616ea23eb2045602c01`. The unchanged mature runner is SHA256 `196f00b955983a076a23638630598993943dc95d902856efb4fdcf1a170e7807`; audit source `cfecef519b6933d6e953479e8fa4f0272d4921d0d749515f81a97f27b56edcb0`; audit config `5d6c0d6ebe0cb897e9a5b08246e6d679fc97b60888f46620fa7fa4a685b20459`.

Final read-only validation rehashed the current source, exact first-clean object and all bound evidence; before/after maps are equal. Counts derived from physical owner maps are 290 author records, 295 metadata-listed records and 296 actual metadata-protected records; the canonical source/object union has 27 complete pairs. All 69 lane refs and HEAD `8ec0a3a7d3b3c4617ebd8430999ad4656ed804e7`, tree `6d08916c9e5608ae8f6d1d66ceb74d2371685acf`, branch `feat/oq56-p53-balanced-event-v41` remained unchanged. Final lane live Lean list is empty. Exact final evidence: `owned-object-evidence.json`, SHA256 `c46a0aedc0e7d6ae3a2184063011984f0cd035cd192b6ca082b45bc7edc6f762`.

Checks used the pinned Lean `leanprover/lean4:v4.36.0-rc1` environment and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. The single lane-heavy lock, CPU22–25, native M8192/j4, at least28GiB headroom and20GiB reserve were enforced. No RLIMIT_AS was used. External CPU0–9/80GiB work was untouched. Local Lean calls0; reviewer Lean calls1; extra Lean calls0; canonical proof recompilations after first-clean0.

Failed source0600, receipt `4042c270702d35697b072fa254ea39a8faa88ce4df0d3da54d4df7d9916dd664`, failed ENDED `89f668849b50d758380b4fa504296a077027288e01e0ee9650d1e6a1b4daa5ab`, proof-only diff `3dd22ba7a2a55a36e5354638ea657e315dd4911233a4860cc2d3dce1c57a0a73` and complete changed bodies `b80b82743b62717af9bba03f683b9f30dec88a4364e88bed8f1a5ccfe1f35ae0` are preserved. The successful correction changes only seven local instance spellings and the explicit finite-constant-sum closure; no frozen assumption or proof setting changed.

All Unit118 reviewer Lean, remote artifact work and writes are released after the DONE seal. Usage input, cached input, output and reasoning subset are separately null because unavailable. Next lane dependency is Unit119's actual conditional joint law and second moments; no work on that mathematical source is owned by this reviewer.
