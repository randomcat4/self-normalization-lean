# Unit111 final independent complete review

STATUS: CORRECT. The exact frozen Unit111 source is fully checked for source-to-statement fidelity, all proofs, server kernel acceptance, actual imported owned types/definition values/body presence, and complete transitive axioms. This is Unit111 acceptance only; original P53/OQ6/RS2 roots remain OPEN.

Reviewer: `/root/oq56_final111_fresh`, fresh `gpt-6.1-sol` / `xhigh`, permanent `NEVERAUTHOR111`. The reviewer has authored no mathematical source, dependency, shared instruction, cache or canonical implementation. No additional context was spawned. `math-theorem` is used; `math-ultra` is not used.

## Exact version and full reading

The complete original `C:/game/shao/current/oq56/inputs02/p53.md` was read, all five sections, SHA256 `0bfadbb2021248859f8b15df2ff184c73c879a7203991c27fdc4f5dd6c04f561`, 5686 bytes. Section 3 is the present obligation; sections 1, 4 and 5 establish why actual iid sampling, the original centered-row denominator, balanced-event and conditional/tail conclusions must remain separate OPEN obligations.

Both complete pre-implementation freezes were read: `frozen-contracts.json` SHA256 `231c8a1f6a5618601c5bf90d7f5da3ecf43d07775e815c497ad791a4784b2b4a`, and `frozen-v1.md` SHA256 `63a73970a113040aa6fec76563a4949df726c381bc15502e0d42b948bfb1d4e6`. All four literal definitions and 28 raw public theorem types match exactly, independently checked in `raw-contract-checks.json`.

The entire candidate `successor-author-01/SparseRealModel.lean` was read, all 410 lines / 20640 bytes, SHA256 `bc935dcd55b7e3bd29000c28382c9c4538ac23fdb30bfa546df9103bf5d63746`. All four definitions and all 35 theorem proofs, including seven private helpers, receive the review below. UTF-8 without BOM, LF-only, final LF; no prohibited proof token. Three imports are the frozen imports.

## Actual source-to-statement dictionary

The exact qualified Unit106/107/109/110 sources were fully read at their actual `successor-author-01` paths. Their source and qualification hashes were independently checked; accepted old checks are reused rather than rerun. Unit110 source is `8c2fdfc80273c52a1ae645c17c2b87141e72fcbd11e63748a6a9119a50926909`, qualified by `7d65fbc137022a796e5f4b3239339c36939f457b1bfca4089572147991dd2ddb`. Unit109 source is `c002b4c0170d2641d774a5ed58588139f2f343d04f5917a3a231fb380c48bfa6`, qualified by `788e46d58c8547879e49cb6e5f4e9abae87f4ca9edd48ca9953964b8d37a6a84`. Unit107 source is `b11eeda079b43800ef836b9b932bebd2e8f5447d2b2bb520ebd6ce9a7978e829`, qualified by `fe7efa45c7ce3d1d81ff02ddaeb3b45813e535803e17246bbdf6ba440df17836`. Unit106 source is `e8783d2b2a7d75f60cb1ef1fe8e4c805a4c524f519a4292ff4e5dc084da6401d`, qualified by `0edf4d8e24d771f488a106c5a2c9f2cd2901fc3caf67a9bc31b40b71206e7995`.

Relevant actual earlier definition values were also read from the curated snapshot: `SparseScales`, `SparseSelection`, `SparseMass`, `SparseLabelLaw`, `SparseSignedLabelLaw`, `SparseSignedShift`, `SparseSignedAmplitude`, `SparseProjectionLaw`, `P35.RealLaw`, `P35.RealEncoding` and `P35.NoiseMoments`. No old acceptance is enlarged or replaced by this reading.

| Original object | Actual consumed formal meaning | Unit111 connection |
|---|---|---|
| Fixed full sequences before sampling or moment order | Parameters `α`, complete `x : ℕ → ℝ`, complete `N : ℕ → ℕ`; `sparseLevelAmplitude` and `sparseLevelShift` are zero at level 0 and source `t(N j)`, `t(N j)^2/(N j-2)` otherwise | The same `α,x,N` occur in every definition and measure. `q` is quantified afterwards; it cannot change the population. |
| Category probabilities `π_j=2^{-j-2} exp(-t_j^α)`, remainder at 0 | `sparsePositiveMass` is the dyadic source mass for positive levels; `sparseLabelMass` subtracts the full convergent mass sum at 0; `sparseLabelMeasure` is its Dirac sum | The transported law is the actual normalized law, not a finite truncation or a renamed abstract measure. |
| Independent uniform `A`, signed shift `(B,η)`, signed amplitude `(C,ε)` | `noiseLaw` is normalized Lebesgue on `[-1,1]`; `sparseSignedLabelMeasure` is category law times fair Boolean sign; `sparseGBaseMeasure=noiseLaw.prod signedLabelMeasure`; population law is `GBase.prod signedLabelMeasure` | Actual full tuple is `((A,(B,η)),(C,ε))`; Unit106 gives `G=A+ηd_B`, `Z=εt_C`, independence and moments. |
| Real observation `X=3I+A` and Borel fallback | Unit110 `sparsePopulationEncode` encodes both complete signed labels, `sparseRealMeasure=population.map encode`; total measurable decoder recovers the tuple on closed-noise support and only has AE inverse assertions | Unit111 definitions compose with this total decoder. No global inverse, bijectivity, or embedding is assumed. |
| `G`, `Z` on real observations | `sparseRealG=populationG ∘ decode`, `sparseRealZ=populationZ ∘ decode` literally | No abstract proxy is substituted. One-observation decoder map law transports the actual complete functions. |
| `h=G+G′+ZZ′`, positive canonical remainder | `sparseRealKernel` and `sparseRealResidual` are the exact frozen positive-sign formulas | Global Borel measurability and symmetry hold on all `ℝ×ℝ`, including outside valid encoding intervals. This does not assert PSD of the whole kernel. |
| Independent pair and moment factorization | Unit110 maps the genuine `realMeasure.prod realMeasure` by `Prod.map decode decode` to `populationMeasure.prod populationMeasure` | Pair moment/integral transport uses the entire genuine pair law, not separate marginals or a diagonal identity. |
| First projection `g=G`, `θ=0` | Accepted Unit107 row integral holds for every tuple argument, not just support points | It can be evaluated at `decode u` for every real `u`, including off-image points. The centered residual is exactly `ZZ′`. |

## Complete proof coverage

All entries in the following table are CORRECT for the exact accepted source. The server kernel and the complete imported actual expressions independently bind this same version.

| Candidate lines | Declaration | Independent proof check |
|---|---|---|
| 24–35 | Four public definitions | All literal values are exact. `h` and residual have the source's positive product sign; no auxiliary measure replaces the fixed actual real measure. |
| 37–43 | private `real_map_decode` | `map_map` uses measurable outer `f` and measurable total decoder, then the exact Unit110 decoder pushforward law. This transfers joint maps as well as scalar maps. |
| 45–63 | private `real_decode_lift` | The actual measure-preserving decoder supplies integrable composition from `hf`; target AE strong measurability is rewritten along `map_eq`; `integral_map` is used in the correct reverse direction and then rewritten to the true population measure. No embedding premise is used. |
| 65–99 | private `real_pair_decode_lift` | Same construction on `Prod.map decode decode`, with the actual accepted pair map law and global measurability. It transports pair integrability before the integral. |
| 101–107 | private `population_G_integrable` | Positive moment order 1, with `hα` and exact selection core; `integrable_norm_iff` uses the previously proved measurability. |
| 109–115 | private `population_Z_integrable` | Positive moment order 1; only `hα` is needed. Norm and real power 1 simplify correctly. |
| 117–122 | private `population_G_sq_integrable` | Moment order 2 converts `|G|^2` into `G^2`; preserves both `hα` and selection core. |
| 124–129 | private `population_Z_sq_integrable` | Moment order 2 converts `|Z|^2` into `Z^2`; no selection core is added. |
| 131–134 | `measurable_sparseRealG` | Composition of actual measurable population feature with global measurable decoder. |
| 136–139 | `measurable_sparseRealZ` | Same global composition for actual `Z`. |
| 141–165 | `sparseRealG_indep_Z` | Finite/probability instances exist for both actual measures. The independence characterization transfers the complete joint map and both marginal maps through one common decoder, then uses actual Unit106 independence. Marginal-law equality alone is not used as a substitute for independence. |
| 167–172 | `integrable_sparseRealG_rpow` | Actual single-law lift of the qualified full `q>0` moment, with the same complete `N`, `hα`, and core. Includes `0<q<1`. |
| 174–179 | `integrable_sparseRealZ_rpow` | Exact qualified full `q>0` moment transported with only `hα`; no `α<1` or core added. |
| 181–187 | `integral_sparseRealG_zero` | Honest `G` integrability is established by the private order-1 helper before integral transport; inherited actual zero mean closes the chain. |
| 189–195 | `integral_sparseRealZ_zero` | Same honest transport using order-1 `Z`, only `hα`. |
| 197–207 | `integral_sparseRealG_sq_ge` | The actual finite second moment is transported as an equality; the accepted bound `1/3` is used in the proper direction. With zero mean this is the required projection variance bound. |
| 209–219 | `integral_sparseRealZ_sq_pos` | Honest second-moment transport followed by exact accepted positivity under the selection core. |
| 221–228 | `integrable_sparseRealZ_exp` | Actual integrable source exponential transported; only `0<α`, `0<τ`, `τ≤1`; endpoint `τ=1` is included. |
| 230–241 | `integral_sparseRealZ_exp_le` | Finite source exponential established first, then exact integral equality and bound `5/4`; no claim about exponential moments of `G`. |
| 243–248 | `measurable_sparseRealKernel` | Global pair composition with the exact literal population kernel, definitionally equal to the real kernel. |
| 250–255 | `sparseRealKernel_symmetric` | Global population symmetry evaluated at both decoded arguments; does not require support membership. |
| 257–264 | `integrable_sparseRealKernel` | Genuine pair-law lift of the actual integrable kernel, with exact inherited core. |
| 266–273 | `integrable_sparseRealKernel_rpow` | Genuine pair-law lift of all positive real moment orders, including subunit orders; no new moment theorem or finite surrogate. |
| 275–281 | `integrable_sparseRealKernel_right` | Accepted row integrability is universal in the tuple first argument, so it applies to every `decode u`. Single-law transport proves the real row integrable for every real `u`. |
| 283–290 | `integral_sparseRealKernel_right` | Uses that same honest row integrability before transport; accepted universal tuple row identity gives `G(decode u)`, literally real `G(u)`. |
| 292–300 | `integral_sparseRealKernel_zero` | Honest whole pair integrability before exact pair integral transport and accepted population `θ=0`; no unsupported Fubini invocation is introduced here. |
| 302–308 | `sparseRealResidual_decomposition` | Exact global algebraic decomposition evaluated at decoded arguments; positive sign preserved. |
| 310–316 | `integrable_sparseRealResidual_right` | Accepted universal tuple row integrability uses only `hα`; transported for every real row argument. |
| 318–325 | `integral_sparseRealResidual_right_zero` | Honest universal row integrability and accepted zero row integral transport; actual canonical degeneracy, with no extra core. |
| 327–335 | `integrable_sparseRealResidual_sq` | Genuine independent-pair lift of accepted `(Z(u)Z(v))^2` integrability. The underlying accepted proof uses separate coordinate second moments, not `Z^4`. |
| 337–358 | `integral_sparseRealResidual_sq` | Independently transports the pair residual-square integral and the one-coordinate `Z^2` integral, inserts the exact population factorization, then squares the one-coordinate equality. No diagonal substitution occurs. |
| 360–366 | `integral_sparseRealResidual_sq_pos` | Exact factorization plus accepted positive one-coordinate second moment; positivity of its square is valid. Core is retained exactly where positivity requires it. |
| 368–380 | `sparseRealG_symmetric` | Transfers the full reflected marginal and the ordinary marginal through the same actual decoder law, with measurable negated feature; uses true Unit109 symmetry rather than zero mean. |
| 382–394 | `sparseRealZ_symmetric` | Same full reflected-law transfer for `Z`; structural symmetry needs no `hα` or core. |
| 396–401 | `sparseRealG_law` | Exact measurable feature map composition and actual Unit110 decoder law. |
| 403–408 | `sparseRealZ_law` | Exact measurable `Z` feature map composition and actual decoder law. |

## Pinned API verification and limits

Author `api-evidence-01.md` was read completely. Independently, a single bounded server read-only query retrieved the exact pinned official source signatures and relevant proof bodies for `MeasurePreserving.integrable_comp_of_integrable`, `integrable_norm_iff`, `integral_map`, `MeasurePreserving.integral_comp`, and `indepFun_iff_map_prod_eq_prod_map_map`. Its request and full bounded result are `official-api-01.request.json` and `official-api-01.transport.json`; remote exit code 0, stderr empty. These source queries execute no Lean. In particular, `integral_comp` requires `MeasurableEmbedding`, while the actually used `integral_map` needs the AE strong measurability explicitly constructed in both lift helpers. The candidate meets the latter exact signature.

No mathematical gap was found in the exact frozen scope. The mature audit template hash `3dfd30bde5a70fed91965aac1e7cc75f3c9fed21da4aea16e3051c18a35cb8ac` was reused with only module `Shao.OQ5.P53.SparseRealModel`, owner anchor `Shao.OQ5.P53.sparseRealG`, and lexical floor 39 substituted. Its sole metadata Lean invocation was explicitly authorized after independently verifying the first clean object, author STOP and RUN-ENDED. The actual owned inventory was derived from the imported module index; floor 39 was only a lower-bound guard.

Actual real L2 operator/rank-one/PSD result, iid samples, true jackknife `R` positivity, actual balanced events, conditional moments and tail ratios remain OPEN, as do P53/OQ6/RS2. No original-root closure or historical novelty claim is made.

Usage: actual model `gpt-6.1-sol`, effort `xhigh`; separate input, cached input, output and reasoning-subset counts are unavailable and must remain null. No subscription allocation is inferred.


## Exact source-bound server kernel and metadata evidence

Author FIRSTCLEAN `author-01` used the pinned Lean `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. It targeted only canonical `Shao/OQ5/P53/SparseRealModel.lean`, CPU22–25, native `-M8192 -j4`, no RLIMIT_AS, and produced the canonical object with exit 0, both outputs empty, zero diagnostics, all owned processes ended, and preservation equality. Elapsed 4.53203715197742 seconds. All 92 author protected records and all 67 own refs were preserved.

- Canonical source: `bc935dcd55b7e3bd29000c28382c9c4538ac23fdb30bfa546df9103bf5d63746`, 20640 bytes, mtime_ns `1792755187254766455`.
- Accepted object: `a1e897c495c6dccb3d273f94dd43682e0cb7c5b97b8ab7d508eed8a0f0ce8a21`, 161304 bytes, mtime_ns `1792755212430696777`.
- First-clean author receipt: `6925f525e896a92199198ec2ea2063d92416012361793f3511258ae12e130519`.
- Author STOP: `95b61aef8cc6b5ee85a341eed48cd95d649c47a190e4c6dab0491698ee133071`.
- Author RUN-ENDED: `9be1bfa18a34a06ec37acd989864eb21434d26b2f028c274a0746345daf8a4ca`.

The reviewer reused mature runner `work/oq56/runtime-20261023/lane-bounded-v2.py`, SHA256 `196f00b955983a076a23638630598993943dc95d902856efb4fdcf1a170e7807`. Metadata invocation only imported the accepted `Shao.OQ5.P53.SparseRealModel` object; it did not pass `-o`, compile a proof prefix, recompile the canonical proof, or replay old accepted checks. It succeeded with exit 0, empty stderr, zero diagnostics, all owned processes ended, and before/after preservation equality in 4.755648139864206 seconds.

- Metadata receipt: `abbcce9b0220b29376774320dc09fb0d76f93674709a1fd0bf4f4870937d401b`.
- Metadata RUN-ENDED: `2a6e350ce427236ca22980b80f7522165c552dda5443133cc84421c116343c65`.
- Mature substituted metadata source: `4e10bab7763020caa32e6d38f8df782bc533ddf608c65d731d097c114f8fe240`, 2602 bytes / 60 lines.
- Audit config: `2627c9615b9ce0bb4ed1e4cb7e55cd6c7c1d9b22967ce0f99c8862e3b0cab982`.
- Server-curated complete actual expression evidence: `1de69b868095f83d615a0fa84c28ea3bcf2429d7eedc3c09f0e03a82389e3979`, 90008 bytes, stored locally as `owned-object-evidence.json`. Raw logs remain on the server.

Actual imported owner inventory contains exactly 39 constants: four definitions, 28 public theorem declarations and seven private theorem declarations. There are no extra materialized generated constants, opaque values, axioms or unsafe bodies in this owned set. All 39 actual complete types (49180 characters), all four actual definition values (928 characters), all body-presence records and all 117 transitive-axiom occurrences were completely read. Each actual axiom list is exactly `propext`, `Classical.choice`, `Quot.sound`. There is no pretty-print failure, ellipsis or truncated coverage. The inventory is the actual module-index-derived inventory, not an inferred lexical count.

Actual values remain the literal frozen decoder compositions and positive-sign kernel/residual formulas. All actual public type domains, measures, argument order, quantifiers, moment orders, constants and assumptions match the frozen raw types. All private actual types match the source helpers: arbitrary measurable outer maps and genuinely population-integrable single/pair functions; none contains an extra decoder embedding/inverse, stronger positivity/core, boundedness, or fourth-moment assumption. Per-constant exact type/value hashes, semantic interpretation and complete review coverage are in `actual-evidence-check.json`.

All 98 metadata-protected records, including exact source/object/receipts and accepted dependencies, remained current and unchanged; all 67 own refs were preserved. Metadata CPU affinity is 22–25, native memory limit 8192 MiB, jobs 4, no RLIMIT_AS; observed cgroup headroom was 114868301824 bytes, above 28 GiB, with 20 GiB system reserve and external CPU0–9/80 GiB untouched. No local Lean was used. Author calls 1; reviewer metadata calls 1; extra Lean after complete coverage 0. All Unit111 canonical source/object/EOF and author/reviewer Lean are permanently STOP after this accepted version.

Kernel classification: LEAN_FULLY_CHECKED_FOR_UNIT111_ONLY. Semantic classification: CORRECT_FOR_EXACT_FROZEN_ORIGINAL_SECTION3_SCOPE. Correctness is distinct from novelty; this transported auxiliary model is not presented as a new standalone theorem or an original root closure. Remaining source dependencies are actual real iid sampling and the actual real L2 residual operator, followed by true R positivity, events, conditional moments and tails. No future work is claimed by the existence of this final answer; the reviewer child slot is released on final handoff. Future corrections must be append-only; the final report and JSON become immutable after DONE.
