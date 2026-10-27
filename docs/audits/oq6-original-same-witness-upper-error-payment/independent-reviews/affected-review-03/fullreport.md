# Unit238 same-original-never-author affected03 review

Verdict: CORRECT_AFFECTED_SOURCE_REVIEWED_KERNEL_PENDING. The single hCm repair is correct at SOURCE level. This affected review, combined with complete prior SOURCE01 and affected01/02 coverage on exact unchanged bytes, covers source004. Qualified=false, kernelPending=true, new native and same-first-original-object allactual TYPE/non-theorem VALUE/recursive AX final join remain pending. No machine qualification is claimed.

## Authority, objects and input verification

Reviewer is the same original never-author context /root/oq56_same_witness_upper_payment238_source_review for OQ56 owner01a17665-2e41-7ed1-9911-57f16fe889fa. Activation isfc5b948a552d64ada8d6ae20c6448df0b267d285a4b51b117f2d7b4b9d9fdd96/5924B. All19 direct inputs and embedded local input/manifest references were verified before actual RUNTIME-ACK:363 matched occurrences/193 distinct local paths. The author had released writer/execution authority. Only affected-review-03 is written; all source/freeze/author/prior-review/shared/other-owner files remain read-only.

Source003:2d9f90190751d15cd9f53c81681b5f3182843ee65490ac9cc499d935168d72da/43455B748LF. Source004:c1d52289bd4bb7d971feb933d13fcd3e347020117767572e5c7210913e46e2dd/43577B750LF. The complete frozen head,131 ordinary result definitions and138 optional ordinary approvals are unchanged.

Requested model/effort isgpt-6.1-sol/xhigh. Actual backend/model/effort and input,cached-input,output,reasoning-subset usage counters are unavailable and null. Math-theorem continues under the more specific project constraints; no math-ultra or child context was used.

## Native003, coded error and preserved counter correction

The bound corrected-counts record, original narrow diagnostic-result record and the entire bounded failure diagnostic were read. Actual native003 ended naturally RC1 after59.73149485886097s, with no object, no timeout, all owned processes ended and preservation/beforeAfterEqual true. The receipt fingerprint is290c32ac2a33f9c81b60fbd31831cf72e4ab70374124691411cc2e32132aeeac. No remote receipt, invocation or server check was replayed.

The original narrow counter searched the literal ': error:' and recorded errors0/diagnostics[] despite actualRC1/no object. Its exact bytes remain preserved. The supplied49 diagnostic lines show six existing local-instance style warnings and one line547:8 coded error:
error(lean.unknownIdentifier): Unknown identifier borel_pi.
That syntax is outside the narrow literal search. The separately sealed corrected-counts record therefore states errors1/warnings6 and explicitly preserves the older result. Neither the narrow zero nor the absence of an older-style diagnostic is a proof pass.

The existing Mathlib-local-changes stderr warning is retained in the bounded failure evidence; this local proposition repair does not mutate packages or claim to resolve environment warnings. A failed native and the listed diagnostic set do not certify source003 or source004. A fresh exact-source native004 and subsequent original-object audit remain required.

## Independent exact-byte delta

The only old source text removed is line547:
rw[borel_pi].

The replacement is new547-549:
have hB : (inferInstance : MeasurableSpace(Fin n→ℝ)) = borel(Fin n→ℝ) := BorelSpace.measurable_eq;
rw[←hB].
The actual source uses the full three-line Lean formatting recorded losslessly in COVERAGE.json and EXACT-DIFF.patch.

Independent reconstruction, without relying solely on the author compatibility claim, proves:
- old/new1-546 are the same34002B prefix;
- old547 is an18B block replaced by a140B block;
- old548-748/new550-750 are the same9435B suffix;
- prefix+oldblock+suffix is exactly source003 and prefix+newblock+suffix exactly source004.

COVERAGE.json records all segment and block hashes, complete replacement text and affected types. No other proof byte, declaration, assumption, result or ordinary RHS changed. No full unchanged proof review or accepted producer/check replay was performed.

The full original review manifest1bf311015a1af4e0b39658da34558f3301e6f3065bfe753154f20e01aad7b3b6, affected01 manifestab5ff7e51ac592c0e8d028498698bd84ba056b8de977cffdf5674caaa8f676c5 and affected02 manifest414271b78443ff4eda07b4c071f5d2e2e798829555c1b77d149894691dabb6fe remain immutable. Their complete source-to-statement/proof/interface coverage applies only to the unchanged byte ranges and scope. This review supplies the new hCm coverage.

## Complete affected proposition and surrounding context

The target remains exactly
hCm : Measurable[mAug,borel(Fin n→ℝ)](C 0).

The already-approved ordinary map is
C : ℕ→(Fin n→Ω×ℝ)→(Fin n→ℝ) := fun k x i=>η k i x,
where η is the same actualNormalizedFamily ν(Y k) from the sole retained model. The entire surrounding hFactor0/G1/G2/hFactors/hCm and immediate downstream compositions were read for affected context. Those factors are still the exact qualified234 output at k=0. The domain is the unchanged augmented measurable space mAug; the finite real-vector codomain is Borel(Fin n→ℝ).

The retained coordinate fact is
∀i:Fin n,Measurable[mAug,borelℝ](η 0 i),
selected by (((hηpacket 0).2.2.2.1)i).1. The explicit C definition makes its ith coordinate exactly this η0i. These full types, the relevant frozen mAug/ν/Y/η/C RHS and their branch scope were checked against the previously reviewed complete declaration context. No different tuple, normalization family, probability law, coordinate function or model is substituted.

The new local fact has complete type and RHS:
hB : (inferInstance : MeasurableSpace(Fin n→ℝ)) = borel(Fin n→ℝ)
:= BorelSpace.measurable_eq.
This is an equality proposition proved from an existing typeclass instance. It is not an ordinary data definition, new callback, fresh model witness, local instance declaration, new assumption or import.

The left structure is the already-installed finite Pi measurable structure from standard real-coordinate measurable spaces. Rewriting backwards replaces the target's Borel real-vector codomain with that existing Pi structure. It does not change mAug or C0. The unchanged measurable_pi_iff.2 then asks for the same measurable coordinates, and the unchanged retained η packet supplies each one. The new proof therefore establishes precisely the original target hCm.

Downstream, hDη0m and hD2aug still compose the same Borel G1/G2 factors with hCm. They still feed the same D1 descent, safe set and transport. There is no probability-space transport performed by hB; its role is solely measurable-space equality on the real-vector codomain.

## Bounded primary API and accepted API example

The complete supplied pinned primary API capture was read locally. Its relevant Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean context is bound by SHA2565eede22bbb9d69e270ae3123180ab7cfecaf77f6c40aceedd39799b46a3fdb6f/34545B at Mathlib807d3836b165983210ee2ecf3cd28f239436949c. The supplied631-654 context includes pi_le_borel_pi and the existing Pi.borelSpace instance. No claim is made to have read the entire remote Mathlib file or to have independently reobserved it over the network.

Pi.borelSpace requires Countable index, coordinate topological/measurable structures, coordinate second-countable topology and BorelSpace coordinates. Here the index is Fin n, hence countable from its existing finite structure, and every coordinate is ℝ with its standard second-countable topology and Borel measurable structure. All conditions are already available. The instance gives BorelSpace(Fin n→ℝ), whose measurable_eq projection has exactly hB's full equality type.

These requirements are only on the finite real-vector codomain. They impose no BorelSpace, standard Borel, second-countable topology or new measurable structure on original Ω or the augmented domain. The arbitrary original observation-space scope is preserved.

The actual curated CoordinateBorelFactorization.lean bindingd245e4f1495972f54a1a823ca075afa526a3f82759fd2030141c0badab780c5c/7334B was checked. Its imports1-3 provide the relevant constructions/BorelSpace context; its finite index type39-44 and explicit equality55-56 were read as a bounded API use. Lines137-138 give exactly the Fin n→ℝ equality used here, and145-148 show backwards rewriting from Borel structures to the existing measurable instances. This is a compatibility check of the exact API bridge, not a re-review of that accepted theorem's complete proof or a replay of its checks.

## Unchanged mathematics, ordinary data and instances

All131 scoped result definitions and their complete RHS, all138 approved optional ordinary entries, the39 dependent introductions,48 optional result mirrors and9 explicit ordinary lets remain exact. The new hB is Prop-valued, so it adds no ordinary inventory item. The six existing local instances are unchanged; this source does not install a new Pi/BorelSpace instance. Imports, theorem header, sole m₀ choice, cg choice and all prior repaired proposition bridges remain byte-identical.

The same original/reduced/augmented spaces, trim law and product measures remain. The same actual η and epsilon sequence, public factors and signed identity are retained. The fixed section remains measurability-only. Hsource remains an original-space concentration event; Ssafe/Jsafe and exact ν→P₀→P transport are unchanged. Actual E/E2/Z, pointwise convergence, eventual safety, payments and numeric limsup are unchanged.

The statement still retains the complete universal234 packet for every n≥4,C0≥0,z≥0 and adds only the genuine bounded-polylog p54 F4-F6 payment branch with its original envelope/window/quantifier scope. No new moment condition, atom premise, global Measurable w, conditional p-rate assumption, second coding model or η-identification hypothesis is added. It claims no235/236 assembly, all-real-epsilon theorem, physical=clipped blanket equality, source CDF/external-engine application or OQ56/root closure.

## Final decision and release

No affected mathematical, full-type/RHS, instance, scope or source-fidelity gap was found. Exact source004 has complete combined SOURCE coverage through unchanged evidence reuse and this affected proof review. It remains qualified=false/kernelPending=true, with no first successful original object. The reviewer does not infer kernel success from fixing one unknown identifier or from the corrected diagnostic count.

The next dependency is the lead's exact source004 designated-server native004. Only after first success, audit that same first original object for every actual module-index-owned full TYPE, required non-theorem full VALUE and transitive axioms. This same original never-author context must then join those exact machine artifacts to the source coverage. The accepted axiom whitelist remains propext,Classical.choice,Quot.sound. A subsequent source change requires only its affected rebinding/review, never silent evidence reuse across changed bytes.

No Lean/server/network/upload/Git/API/children operation, old accepted proof/check replay, source/freeze/author/prior-review/shared/other-owner write occurred. All six final counters writer/heavy/inflight/pendingExternal/children/uncertain are0 in lastzeroRELEASE, which is the final artifact write. Actual backend/model/effort and the four usage counters remain null because they are unexposed.
