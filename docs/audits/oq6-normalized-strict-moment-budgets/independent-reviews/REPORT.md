# Unit229 independent complete SOURCE/proof review

STATUS: CORRECT

Stage: SOURCE_ACCEPTED_FOR_NATIVE. qualified=false; kernelPending=true. This is a complete independent review of the new exact source and its restricted source-to-statement meaning. No parsing, elaboration, native/kernel or transitive-axiom result is claimed.

Reviewed source: C:/game/shao lean/drafts/oq56/unit229/author-01/NormalizedStrictMomentBudgets.lean
SHA256: 52e0f905cb5d68d3c213faa2078cc1bb885a24834dac1cd1e61a96d4437b8ad0
Bytes: 4109. UTF-8 without BOM; 86 LF, no CR; final LF.
Public theorem: Shao.OQ6.NormalizedStrictMomentBudgets.actual_source_z_strict_truncated_moment_budgets
Frozen declaration JSON: d79ac1f0107343ad0a5768e5b11584e27c52e7abe2b811ef0cebb0cff469086e.

Reviewer: fresh independent never-author context /root/oq56_normalized_strict_budgets229_source_review. Lead: OQ56 successor 01a17665-2e41-7ed1-9911-57f16fe889fa. Requested model/effort: gpt-6.1-sol/xhigh. Actual model, actual effort, input, cached-input, output and reasoning-subset usage are unexposed and recorded as null. No author-source repair or implementation was performed.

## Read coverage and binding verification

I read the complete new module, lines1-86, including every binder, typed let, conclusion, proof step and closing. I read the exact complete frozen preamble/head/closing (11/33/3 lines), complete frozen-declaration JSON, complete typed interface inventory (353 lines), Stage1 CANDIDATE (69), ROUTE (79), SOURCE-MAP (17), author REPORT (29), INTERFACE-COMPATIBILITY (75), input bindings, manifest, author zero release, both parent intakes, and this review activation/brief.

Primary source C:/game/shao/current/oq56/inputs02/p51.md was independently read completely, lines1-355, SHA256 96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359, 17326 bytes. The first combined tool output was truncated globally; the missing ending lines345-355 was separately read. The full candidate/route and producer declaration were also separately displayed in untruncated follow-up reads.

For the reused producer, I independently read the COMPLETE exact public declaration, not just a frozen summary: C:/game/shao lean/library/Shao/OQ6/NormalizedAnalyticCostLimits.lean lines173-241, source SHA256 c414aeb98cec27146d30f38e3c869f34a7b81e4a45101497a99db29a4d37b92d, 56155 bytes. Its existing qualified proof/object/AX evidence is reused; no complete old-proof re-review, old proof build, or leaf-AX replay was conducted.

For eta semantics, I read C:/game/shao lean/library/Shao/OQ6/ActualMomentNormalization.lean lines1-41, particularly complete definitions actualCoordinateMean20-23, actualCenteredFamily25-29, actualNormalizationScale31-34, actualNormalizedFamily36-41. Exact file SHA256 7e781dc929166b43c69dd6ffe463c62e2d1508fa5283451852ea50afed18c237, 22137 bytes. I read the defining deterministicAffineObservation interface/body at QuantizedObservationCoding.lean17-19: (Y x-a)/s. No proof audit of these old definitions/producers was requested or repeated.

INPUT-BINDINGS.json records all exact mathematical/authority/support inputs. Twenty-five inputs carrying expected hashes/lengths were independently matched, with zero mismatches; nine policy/skill/definition-support files carry observed hashes. These are binding counts, not proof or receipt counts. The local AGENTS current tail, SERVER/TEAM instructions and required math-theorem references were consulted; no historical workflow or resource authority was activated.

## Frozen bytes, interface, and deterministic values

STATIC-COMPATIBILITY.json independently verifies exact frozen preamble+head prefix, exact closing suffix at byte4061, strict UTF-8/LF bytes, the sole permitted import, one public theorem, no other ordinary declaration, twelve displayed lets (six statement plus six repeated proof-local lets), and no sorry/admit/axiom/unsafe/native_decide token. Both copies of all six typed let bodies agree modulo indentation. These are text/byte findings, not actual generated-owner or axiom findings.

The implicit carrier is the same arbitrary Ω:Type*, with supplied MeasurableSpace Ω. ν:Measure Ω and supplied IsProbabilityMeasure ν are unchanged throughout. No Ω topology, StandardBorel, countably-generated, explicit Nonempty, independence, atomlessness, higher-moment or target-integrability premise is added. Fin n carries its canonical finite structures; real topology/Borel structures and Nat-atTop are canonical imported structures. The declaration has exactly the frozen19 explicit parameters:
ν,n,hn,ξ,hξ,hξ2,hξmean,hξenergy,Y,hY,ε,hε,hεsmall,hεlim,herr,z,hz,cBudget,hcBudget.

The exact deterministic values at statement28-35 and proof48-55 are:

| Value/type | Exact RHS | Direct value captures and type captures |
|---|---|---|
| η : ℕ→Fin n→Ω→ℝ | fun (k:ℕ) => ActualMomentNormalization.actualNormalizedFamily ν (Y k), with the full frozen namespace | ν,Y; Ω,n,MeasurableSpace Ω |
| Fz : ℝ→ℝ | fun (t:ℝ) => (z*t)^2 * min \|z*t\| 1 | z; canonical real structures |
| δ0 : Fin n→ℝ | fun (i:Fin n) => ∫ ω:Ω, Fz (ξ i ω) ∂ν | ν,Fz,ξ; Ω,n,MeasurableSpace Ω |
| δη : ℕ→Fin n→ℝ | fun (k:ℕ) (i:Fin n) => ∫ ω:Ω, Fz (η k i ω) ∂ν | ν,Fz,η; Ω,n,MeasurableSpace Ω |
| L0 : ℝ | ∑ i:Fin n, δ0 i | δ0; n |
| Lη : ℕ→ℝ | fun (k:ℕ) => ∑ i:Fin n, δη k i | δη; n |

The table uses mathematical spacing only; the byte-exact expressions are in the reviewed frozen head/new source and the verified inventory. Eta is precisely centering each Y k coordinate by its ν-mean and dividing by the square root of the sum of its centered ν-second moments. The helper uses the qualified generic normalization/limits API and does not introduce an unrelated normalized family. That API handles its normalization obligations under the displayed hypotheses; the new proof does not assume an undeclared denominator fact.

The integral callbacks capture only Fz/ξ/i or Fz/η/k/i and are Ω→ℝ. The convergence callback is k↦δη k i. The eventual predicates capture only the fixed δη,Lη,z,cBudget and finite-index type. There is no public callback premise, auxiliary-Prop binder, new typeclass instance, extra deterministic value, measurable selector or original-law transport.

## Exact producer application and conjunction audit

At new59-60 the applied theorem has16 explicit arguments, in order:
ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr z.
They agree respectively with producer175-187. The implicit Ω/measurable structure and probability instance are inferred from the same ν and function types. Producer x is exactly z. hz and hcBudget stay displayed in the frozen theorem but are not needed by this broader producer or by the strict-neighborhood transfer; cBudget is used only in the fixed aggregate threshold. This does not delete or weaken a frozen assumption.

I counted the actual right-associated conjunction at producer211-241. A parenthesized quantified conjunction is one field; the unparenthesized Integrable exp(S) and 0<I at213 are separate fields. The fields before the retained remainder are:

1 original individual tilt integrability/positivity211;
2 normalized individual tilt integrability/positivity212;
3 full original exponential integrability213;
4 positivity of I213;
5 normalized full exponential integrability/positivity214;
6 original deleted exponential integrability/positivity215;
7 normalized deleted exponential integrability/positivity216;
8 original full exponential bound217;
9 normalized full exponential bound218;
10 original deleted exponential bound219;
11 normalized deleted exponential bound220;
12 original truncated integrability221;
13 normalized truncated integrability222;
14 truncated domination223-224;
15 individual tilt-mean limits225;
16 full exponential-mean limit226;
17 deleted exponential-mean limits227;
18 coordinate truncated limits228;
19 sum truncated limit229.
The final pattern "_" retains/discards the entire residual right-associated packet starting with Integrable q at230. It is not an assertion that the complete producer has only20 atomic conjuncts.

Thus the eleven initial skips in new61, hδ0int/hδηint at positions12/13, four further skips14-17, hδlim/hLlim at18/19, and final remainder pattern in new62 match the actual declaration. No positivity or convergence field was misindexed. Producer η agrees definitionally with local η. With x=z and the displayed Fz, producer δ/δη/L/Lη are definitionally local δ0/δη/L0/Lη. The changes at63-68 expose these equalities without a law change or an integral identity that would need new assumptions.

Both actual integrability families are returned at38-39 for every displayed coordinate and every finite k. This avoids treating Lean's total integral convention as an integrability proof. They are direct producer conclusions under exactly its measurable/MemLp/mean/energy/approximation premises, not assumed target integrability or a new dominated-convergence claim.

## Complete new proof audit and five conclusions

New46-58: classical enables the ordinary finite-index/filter use. dsimp only exposes the statement-level value lets. The six identical proof-local typed values are introduced; intro introduces exactly hδ0 and hL0; change57-58 expresses the same original strict bounds in that notation. No new premise is introduced.

New59-68: the correctly applied producer supplies output1 original truncated integrability, output2 normalized truncated integrability, output3 coordinate Tendsto to δ0, and output4 finite-sum Tendsto to L0. This is direct reuse of the exact qualified API, with no new limiting interchange.

New69-72: fix an arbitrary i:Fin n. Since hδ0 i proves δ0 i<1/2, the open upper neighborhood below1/2 belongs to nhds(δ0 i). The coordinate Tendsto sends it to an eventual δη k i<1/2. The use of eventually_lt_nhds has the correct strict direction. This would not follow from a non-strict original bound; the actual premise is strict.

New73-75: Filter.eventually_all.2 combines the coordinate event for every i of the fixed finite type Fin n. Finiteness is available for every fixed n and is the precise reason this exchange is valid. No exchange over an infinite family, n, model or z occurs.

New76-77: hL0 puts L0 in the open upper neighborhood below the fixed real cBudget*z^2. hLlim gives eventual Lη k<cBudget*z^2, again with the correct strict direction. No equality between cBudget and any external constant is used.

New78-80: the filter intersection hAllevent.and hLevent retains both strict conditions for the same k. New81 uses Nat-atTop eventuality to obtain k0:ℕ and hk0:∀ k, k0≤k→((∀ i,δη k i<1/2)∧Lη k<cBudget*z^2). New82 returns the four analytic outputs plus this existential witness. Its nested conjunction/existential constructor structure agrees with the five frozen conclusions at38-44.

The output5 quantifier order is exactly ∃k0 ∀k≥k0 ∀i for the coordinate part, conjoined with the sum bound. k0 is chosen after all fixed model/sequence/error/scalar data and both margin hypotheses. It may depend on them. It is common over coordinates only; no uniform n/z/cBudget/model/sequence rate or computable threshold is asserted. The statement does not claim strict budgets at early k. n=1,z=1 and arbitrary finite n remain under the conditional premises; no existence of models meeting those margins is asserted. Fin n is finite even without hn, but hn is retained and supplied to the producer unchanged.

## Independent primary-source fidelity and scope attack

p51 is explicitly UNCERTIFIED_REPAIR_CANDIDATE at3, and5 says it is supplemental candidate repair material, not the original manuscript. This review certifies only the new conditional helper; it does not certify all p51 mathematical assertions.

The relevant bearing claim is p51 S19 at223-232 and S4 at234-296, particularly294: normalized coordinate and sum truncated budgets converge, and strict original reserves persist for sufficiently small approximation error at a fixed model/threshold. The source hypotheses supplying S19 margins and its p-moment/window estimates are outside this helper. Source241-243 defines the centered common-variance normalization consistent with actualNormalizedFamily. Its specific coding construction and error bound247 are not constructed here; the new theorem asks explicitly for any measurable uniformly approximating sequence with the stronger displayed small-error control needed by the qualified API. It is a conditional sequence form of the strict-budget preservation step.

For s=z*t, Fz(t)=s^2 min(|s|,1). If |s|≤1 this is |s|^3, because s^2=|s|^2; if |s|>1 it is s^2; at |s|=1 both expressions are1, and at0 both are0. Thus it is exactly the continuous source truncated function F(z*t), bounded by z^2*t^2. There is no boundary jump, need for atomlessness, higher/mixed moment, or compact-cost substitution. The p51 compact estimate at311 instead uses L_(n,1+z) in0≤z≤1. Neither 1+z nor a compact weighted cost enters the new module or producer application.

The two strict original conditions new36-37 are EXPLICIT hypotheses:
∀i,δ0 i<1/2 and L0<cBudget*z^2.
They are not deduced from L2 normalization, measurability, approximation, hz, or positivity of cBudget. Source S19 has non-strict displayed bounds followed by the strict-reserve instruction232; the helper consumes already strict reserves, and does not promote ≤ to <.

cBudget is an arbitrary explicitly positive generic real. The theorem does not identify it with published c_SZ, derive any source-small constant, or invoke Shao–Zhou Theorems2.1/2.2, Remark2.2, (92) or DC Lemma6.1. p51 external attribution7/349 and the preserved p54 repairs are not changed or absorbed into new originality claims. p54 is outside this source unit and was not newly audited.

Unit228 is neither an import, input, premise nor theorem application. Its unqualified source/check is not used, renamed, retried or qualified by this review. The sole new import is NormalizedAnalyticCostLimits. No original m0/q/P transport, same-witness coding/consumer construction, Qepsilon or weighted/deleted source-R convergence, external scalar theorem application, CDF/atom/zero-event statement, full S11/OQ56 or root closure is proved. All such obligations remain outside this exact conditional helper. The mathematics here is a standard finite strict-limit bridge and carries no new research-novelty claim.

## Findings, limits, and handoff

Critical gaps: NONE in the frozen conditional statement, complete new proof, exact producer argument/field map, or restricted primary-source fidelity.

Material limitations: original strict reserves and an actual same-model approximation sequence must still be supplied by a future consumer; cBudget is not a qualified external constant. This SOURCE verdict is not a native/kernel/AX qualification.

Static-check incident: an initial local command used a JavaScript string that consumed regex backslashes, so its declaration/let counts were zero. The initial JSON is preserved as STATIC-COMPATIBILITY-INITIAL-PATTERN-ESCAPING.json. Only the affected text guard was corrected using a raw command string; corrected results show one theorem/twelve lets/no prohibited tokens. Source/freeze bytes never changed. This was no Lean/server request, uncertain write, mathematical failure or proof replay.

All review writes are confined to unit229/source-review-01/**. Proof-source writes=0; source/freeze/other-owner edits=0; Lean/server/network/transfer/Git/API/children=0. There are no pending or asynchronous external operations. The final manifest/release seals this review and binds the exact inputs. This same independent complete review may be reused after exact-source native success, adding only the actual generated TYPE/required VALUE/transitive AX/frozen-machine join and any genuinely new uncovered risk. No automatic second full new-proof review or old-producer audit is requested.
