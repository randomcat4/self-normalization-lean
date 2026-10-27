# Unit228 repair01 independent affected-proof review

STATUS: CORRECT

**Verdict: SOURCE_ACCEPTED_FOR_NEW_NATIVE.** The narrow hIntEq repair has no identified mathematical or frozen-interface gap. This is an affected source/proof review only: `sourceAcceptedForNewNative=true`, `kernelPending=true`, `qualified=false`. The repaired source has not been elaborated, kernel checked or axiom audited by this context.

The same fresh NEVER-AUTHOR reviewer retains the previously completed whole-source review of b348. Requested model/effort remain gpt-6.1-sol/xhigh; unobservable actual model/effort and input/cachedInput/output/reasoningSubset fields are null. All writes are confined to `source-review-01/repair-01/**`. Prior complete review, source, receipts and author/freeze/other-owner files remain unchanged. Lean/server/network/transfer/Git/API/children/source-edits are zero.

## Exact binding and affected coverage

New source: SHA256 `df16a04be1a36ccef76eedc4872e7f1dd911d5be2da7117e307bcf24662b1155`,41664 bytes/658LF/zeroCR/UTF-8 without BOM. Baseline b348: SHA256 `b348d6ee5c0eca3a29b36c515e03125336e098b94c43c65a9f42defcb2aba7cb`,41340 bytes/652LF. Activation SHA256 `89a8a705b986301ff352d833b07eba67f946076427fa3fe4626c1dec61b088f2`,2175 bytes. Prior full-review release `b73f410f7e9f1beb30eb8404eaf3fcacacfbae2fa3e84a0fdb8729f92efaa851` and its seven payloads remain exact.

The complete literal replacement is old484–491 -> new484–497. Independent byte comparisons show old/new lines1–483 equal and old492–652 equal new498–658. Replacing just that old block reconstructs the entire new file exactly. The frozen preamble/full head and closing are identical, so all76 ordinary typed data/RHS scopes and46 target clauses retain their earlier complete review. The previous full652LF review is reused outside this actual change, without a duplicate complete old proof review. All new changed lines were read in full, with new472–507 context and new529–622 direct downstream interactions. `COVERAGE.json` records the exact current658LF coverage composition.

The author manifest's six payloads and15 inputs, parent repair intake, prior review chain and pinned API references match expected SHA256/length identities. The complete binding list and derived counts are in `INPUT-BINDINGS.json`; no hash check is substituted for semantic reading.

## Pinned integral_map interface and exact argument order

The Root-curated pinned Bochner Basic source SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`,72547 bytes, equals its provenance-bound second copy. The existing manifest records pinnedGitBlobExact. I read its full required declaration1076–1078, namespace/variable context139–155 and179–184, and intervening variable/section scopes through1079. The relevant declaration is:

```
theorem integral_map {β} [MeasurableSpace β] {φ : α → β}
    (hφ : AEMeasurable φ μ) {f : β → G}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ
```

For the explicit `@integral_map` application, the dependency order is alpha,G,the NormedAddCommGroup G and NormedSpace Real G instances,m,mu,beta,the target measurable-space instance,phi,hphi,f,hfm. The unrelated E/F/kappa structures, CompleteSpace E, auxiliary X/H and separate nu variables do not occur in this declaration's type and introduce no new premise. The code's two typed real inferInstance arguments select the existing canonical real structures; no local instance or caller premise is added.

The q call at new485–489 correctly supplies alpha=`Fin n -> Omega x Real`, G=Real, m=mAug, mu=nu, beta=`Fin n -> Omega`, target space=mN0, phi=q, hphi=hq.aemeasurable, and exactly the callback's f. Its last argument is AE strong measurability of that same f under `@Measure.map ... mAug mN0 q nu`. The retained hq was explicitly typed with those two measurable structures. The source law has not become P/P0, and the target has not become the original mN.

The identity call at new491–495 correctly supplies alpha=`Fin n -> Omega`, G=Real, m=mN, mu=P, beta=`Fin n -> Omega`, target space=mN0, phi=id, hphi=hId.aemeasurable, and the same f. Its last argument is AE strong measurability under `@Measure.map ... mN mN0 id P`. This explicit source mN is precisely what must be preserved when the carrier has both original mN and reduced mN0 structures. The unchanged hId is itself typed `@MeasurePreserving ... mN mN0 id P P0` and constructed from measurable identity and the exact retained map equality. No target integrability or new measurability hypothesis is needed: hf is reduced-target measurability, sufficient for the declared AE-strong-measurability condition.

## Law rewriting and callback equality

New496 rewrites the q target law using hq.map_eq. New497 rewrites the identity target law using the already retained `hP0map.symm`, exactly `@Measure.map ... mN mN0 id P = P0`. This is the same proof used in hId's constructor at480–481; it has the proper source and target measurable structures and does not choose a new probability law or witness.

After these rewrites, h1 states `integral_P0 f = integral_nu (f o q)` and h2 states `integral_P0 f = integral_P (f o id)`. Therefore unchanged `h1.symm.trans h2` is correctly oriented from the augmented integral to the original-P integral. The unchanged final simplification only unfolds Function.comp_def and id_eq. The callback's full signature at482–483 remains exactly the frozen derived statement, capturing the same q/nu/P0/originalP and reduced f. It is proved locally and supplies no caller callback or hidden mathematical assumption.

This is a type-explicit repair of the existing mathematical argument. It does not strengthen or weaken the statement, silently identify two independently chosen witnesses, change a measure, or replace genuine integrability with the totalized Bochner integral.

## Complete downstream interaction check

I checked all seven original-target function families against the unchanged hIntEq interface:

| New source use | Target and consequence preserved |
| --- | --- |
| 529–530 | exp(S0): same integral equality to original I0, hence later original-I0 positivity and Ieta limit. |
| 531–533 | fullTest0 exp(S0): same original-P full signed-integral and ratio RHS. |
| 534–537 | each deletedTest0_i exp(S0minus_i): same original-P partial signed-integral and ratio RHS. |
| 538–539 | each compactDeletedTest0_i: same original-P compact deleted integral. |
| 540 | A0 integral for the compact one-term cost. |
| 541 | B0 integral with the retained z coefficient. |
| 542–548 | every continuous truncated Lcompact summand and its exact finite sum. |

All receive the same reduced-target measurability proofs already completely reviewed. The callback's required target does not acquire mN measurability or target L1 as a new premise. Its output continues to use original P on mN. The separately derived hIntFromnu at499–502 is outside the replacement and byte-identical; the original-P full/deleted/compact product integrability at549–559 still comes from genuine227 integrability transported through the same q and id. It is not inferred merely from equality of totalized integrals.

The positivity and all signed-integral/ratio limits at560–605 keep their exact original-P RHS. Full and deleted ratios retain full Ieta/full I0. Both finite assemblies606–622 retain the full-plus-deleted numerator, full normalizer, continuous truncated Lcompact, integral A, z integral B and every compact deleted term. No two-sided deletion envelope, n-dependent coefficient, normalization or witness scope changes. All other source mathematics is exact old reviewed bytes.

## Diagnostics, verdict limit and zero release

The bound native02 diagnostics concern only OLD b348: natural RC1 after96.0434305910021 seconds, two mN0-versus-mN inference errors, six warnings and no object. The previous90-second interrupted attempt is separately preserved. These failures do not certify either the original proof text or repaired source. This review does not replay a native attempt or reinterpret an interruption as a proof result.

No critical affected-proof/interface gap remains. The explicit arguments target the recorded inference mismatch at the correct source/target boundary, but actual elaboration remains a new server gate. The reported shared source-version execution-interface gap currently blocks dispatch administratively; it is not a mathematical verdict and this reviewer does not alter shared execution infrastructure.

Next: lead may dispatch a new exact-source native only after that actual execution interface is ready. A successful new first object must then be joined by this same never-author reviewer to all actual module-index TYPE/required VALUE/transitive-axiom evidence before final qualification. The whitelist remains propext/Classical.choice/Quot.sound. Accepted226/227/source/AX evidence and original scopes remain unchanged; no whole OQ56/SZ/CDF/atom/zero-event/root closure is claimed. The final RELEASE0 records zero writers/heavy/inflight/pendingExternal/children/uncertain operations. A final answer itself is not a persistent continuation mechanism.
