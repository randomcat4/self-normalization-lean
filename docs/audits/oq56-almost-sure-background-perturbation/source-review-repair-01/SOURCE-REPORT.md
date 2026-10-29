# unit280 repair01 independent affected SOURCE review

STATUS: CORRECT

The complete new T03 proof is mathematically correct under the unchanged frozen statement. Its union with the exact prior complete SOURCE evidence covers the entire new 170-LF source. sourceAccepted=true, kernelChecked=false, qualified=false. This review is not a new native or axiom receipt.

## Activation, scope and exact version

The SAME independent reviewer /root/oq56_unit280_review was explicitly reactivated by source-review-repair01-ACTIVATION.json, SHA256 0b173cc01783b36dd34aa27b29647c6e8f402ad0e4f18b2e597c10a95cb8fdfc /40082B. All 173 immutable activated input SHA/byte bindings passed before any new report write, and actual runtime ACK 173/173 was sent promptly. The sole new writable scope is source-review-repair-01. All source, freeze, author directories, prior reviews, library, shared files and other owners remain read-only.

The new source is author-repair-01/AlmostSureBackgroundPerturbation.lean, SHA256 879eddc9a21eb422412cb70ec99ee34524ec821e67e4aac2c3fc074b758c5572, 7679B/170LF. The frozen declaration record remains bcd298af759372f157cf955d255c4eb967c45e206a069073e1922e0058c14f5e /6889B. I literally read the complete new 24-LF T03 proof, its actual surrounding source context, the full repair AUTHOR-REPORT and MFT addendum, exact affected diff and byte map, and the complete pinned public API heads and enclosing contexts used by this repair. The prior literal primary p41/p51, all eight frozen HEADs/two RHS/PRE/CLOSE and five unchanged proof bodies are reused by exact source hashes; they were not commissioned or presented as another blanket proof review.

The requested SAME model/effort is gpt-6.1-sol/xhigh. Actual backend/model/effort telemetry and input/cachedInput/output/reasoningSubset counters are unavailable and are null, separately from requested configuration.

## Preserved machine failure and the repair boundary

The original 7371B/162LF source remains SHA653589d66e7eabc454f6476509d4029c5772fd31483e6ce49bafb2328bc2246c. Its native01 actual exit code is 1, not a pass; it ended naturally, was not timed out, left no original object, and preservation was exact. The complete local diagnostic is 545686b8351b5d215bc3ad6bfc3e7e2788803793c81eb6775c1c3431a10735c6 /4229B and binds original server receipt bb0fc3f0555a3ff1dac81335e0f67461a70aa617fb413dafe2e548489cf877ea /39685668B. The sole normalized error was old source line106 column20: Measurable.comp hr could not unify the supplied pair measurability proof with Measurable ?m.115.

This old failure does not become a Lean pass through a SOURCE decision. The original complete SOURCE report remains a mathematical/fidelity review with no machine acceptance. This repair only changes the complete T03 proof body; it must await a genuinely new authorized native02 and later actual-owner audit.

Independently substituting new proof bytes [4270,5291) for old proof bytes [4270,4983) reproduces the entire new source exactly. The unchanged prefix has 4270B and the unchanged suffix 2388B. All eight HEADs, two fixed RHS, PRE/CLOSE, imports/settings/order and other five proof bodies remain byte exact. The five reused proof bodies total 60LF. New T03 is 1021B/24LF, SHA256 bbc020b5891bd21de5d8d60c90b6f9464ef4683bca9070b0b649efc2777c4033. The source delta is exactly +308B/+8LF. The complete proof-component total is now 84LF, and aggregate ALLPROOF is 89LF with five blank separator LF. There are still eight top-level declarations, two definitions, six theorems (five public, one private); no new top-level helper or premise was added.

## Complete affected proof review, new source lines92-115

Lines92-93 retain the proof start and classical context. No new instance about Omega or any probability measure is introduced.

Lines94-96 introduce hpair(i,j) with the explicit complete target Measurable(fun x:Fin n->Omega => (x i,x j)). The two measurable_pi_apply proofs have domain the actual finite sample function type and codomain Omega. Measurable.prodMk forms their pair into the canonical product measurable space. The annotation fixes both the sample domain and product-valued function; it needs neither an equality relation on Omega nor a hypothesis i!=j.

Lines97-100 introduce hrx(i,j) with complete target Measurable(fun x:Fin n->Omega => r(x i)(x j)). The repair uses the exact public API Measurable.comp and explicitly chooses g=Function.uncurry r and f=(fun x:Fin n->Omega => (x i,x j)). Thus its types instantiate alpha=Fin n->Omega, beta=Omega x Omega, gamma=Real, with the canonical Pi, product and real measurable spaces. The original hr proves measurability of g, and hpair i j proves measurability of f using those same spaces. The API yields Measurable(g compose f); beta/delta reduction of uncurry and composition is exactly the declared real-valued target. No measurable-space transport, equality of observations, residual diagonal condition or further function-measurability premise is used.

Lines101-103 introduce hwx(i) with complete target Measurable(fun x:Fin n->Omega => w(x i)), from the original frozen hw and measurable evaluation. The expected function and intermediate space are explicit, and the output is the same coordinate weight as in D01. It does not replace an AE hypothesis by a pointwise nonnegativity assumption; this is the separate T03 measurability statement.

Lines104-108 rewrite E as the same two predicate sets and take their intersection. Lines109-111 prove the finite intersection of coordinate nonnegativity conditions using measurableSet_le for constant zero and hwx i. Lines112-115 prove the pair envelope condition: Set.ofPred_forall gives intersections over i,j:Fin n and a proof of i!=j, then measurableSet_le compares (hrx i j).abs with (hwx i).mul(hwx j). The outer indices are finite; the proof index is subsingleton and hence countable. When i=j this implication is vacuous; no measurable diagonal in Omega is required. All bounds and all real expressions are unchanged from D01.

This is the entire proof. It proves exactly MeasurableSet(sampleEnvelopeEvent n r w) using exactly the two frozen premises Measurable(uncurry r) and Measurable w, for arbitrary measurable Omega. No unproved mathematical intermediate is introduced. The typed local facts address the observed inference ambiguity at the source level; whether this exact candidate elaborates successfully remains a native02 question.

## Exact pinned API evidence

The pin remains mathlib807d3836b165983210ee2ecf3cd28f239436949c.

The bound coordinate source packet a7c4324ce1bc6bfdd4efb1008b5ff9de5dc9f56b9133809a19ea2615f80d3ff9 /51775B embeds the complete MeasurableSpace/Constructions.lean file, whose raw source is independently hash/byte checked against 03bdd1fd16c69f61acf8ae50d684f54c9b565d03c6fa880fc338fcbd3bbebadb /49519B. Its global type variables, Prod section, canonical product measurable-space instance and local measurable-space variables were read; the full prodMk head is lines409-410. Its Pi section lines570-585 supplies the Pi measurable space, all component measurable spaces and complete measurable_pi_apply head. No finite-domain or regularity condition is hidden in these APIs.

The supplied existing query parent-native01-affected-primary-api02 binds the exact Measurable.comp head at Defs523-524, sourceSHA bbb025056bb49e962516e9d495bbda6356251a19fde31544d820ecbe50894ecf. To read its full enclosing measurable-space context rather than trust only a short head, I used the already local pinned source query11: C:/game/shao lean/drafts/oq56/unit218/parent-pinned-interfaces01/pinned-mathlib-source-query11.json, SHA256 bd87d8456ff087986fdab013f2e8c2eaaba444f3e09660d0f5062686f13b83d3 /25947B. Its literal Defs40-67 and492-522 excerpts have the same exact Defs sourceSHA; they show global type variables, the defining preimage predicate for Measurable, the closed notation namespace, the MeasurableFunctions section and all three measurable-space variables mAlpha/mBeta/mGamma. Together with the adjacent exact comp head this gives the full relevant context. The excerpt hashes were independently checked. This was local read-only evidence reuse, with no network, probe, compiler or server action.

The two other local context-search packets were only used to locate this existing pinned context, not as mathematical suppliers. Additional context provenance is explicit in READ_ACK/coverage and does not change the activated 173-input denominator.

## Coverage union, unchanged boundaries and conclusion

The original complete report/source-coverage/manifest/unique LAST remain immutable and hash bound. Their complete p41/p51 reading, mathematical source-to-statement review, frozen definitions and five unchanged proofs cover the exact retained bytes. This new complete affected review replaces only the original T03 proof coverage. T03's unchanged HEAD remains exactly the frozen measurable-event statement. T04/T05/T06 merely shift by eight source lines; their proof bytes and interfaces are unchanged, so there is no new interaction requiring another whole-proof review.

All previous boundaries therefore remain: one actual common AE sample event, then pointwise forall v/forall B; separate explicit measurability for probability-one; anomaly half coefficient, norm coefficient one, original n-2 and n4/cardB3 restrictions; small n, empty/full B, repeated observations, arbitrary residual diagonal and zero-energy cases. A sample-dependent selector may be substituted pointwise but gains no measurability or conditional-law claim. Unit279 remains unqualified/not consumed. Qualified278 TYPE/VALUE and original independent/native/axiom evidence are reused without re-reading its old theorem proofs or replaying checks.

The new source is independently rebuilt from exact frozen components plus complete proofs, matches ALLHEAD/FIXED-RHS/ALLPROOF, is UTF-8 without BOM, LF only with one terminal LF, and has no forbidden proof escape tokens. These deterministic checks are not Lean parsing, elaboration or axiom acceptance. Old failed receipts and original post-LAST six-file append incident remain intact; no old claim is rewritten.

No critical mathematical gap was found. The precise SOURCE evidence union is complete for the new source, so sourceAccepted=true; kernelChecked=false and qualified=false remain mandatory. Conditional projection, means/variance, canonical residual re-centering, geometry/interaction/rareblock and original unconditional PE/root obligations remain OPEN, with the original alpha restriction unchanged. The next gate is authorized new native02 and actual-owner TYPE/VALUE/transitive-axiom evidence for this exact candidate, not a replay of accepted old proof checks.

All active reviewer/report authority is released at the unique LASTFINALWRITE. No active wait, pending external command, uncertain operation, child or queued work remains. Possible SAME FINAL identity retention is dormant metadata only, without writer permission until explicit reactivation.
