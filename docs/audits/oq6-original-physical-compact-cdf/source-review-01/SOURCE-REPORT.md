# Unit264 complete independent SOURCE review

STATUS: CORRECT — COMPLETE SOURCE REVIEW, MACHINE PENDING.

The entire exact 171-line source and all 115 new proof lines have been independently read and accepted against the frozen statement. No critical mathematical gap or silently added hypothesis was identified. This is `sourceAccepted=true`, `qualified=false`, `kernelChecked=false`, `machinePending=true`. No new-source elaboration/kernel pass, compiled owner count, first original object, actual compiled TYPE/VALUE or transitive-axiom result is inferred from this review.

Reviewer `/root/oq56_unit264_review` is the SAME retained independent statement/theory reviewer. Sole output scope remains `drafts/oq56/unit264/source-review-01`. No mathematical source or author file was edited. This review accepts the new consumer proof only, reusing exact unchanged qualified221/170 proof/TYPE/kernel/AX evidence and the prior statement/theory verdict. It issues no FINALWRITE and retains independent authority for later complete final machine review.

## Binding, read acknowledgment and source coverage

Activation: SHA256 `e2c400f3ae71ea52ce2445b8e796d7928c2654c7efb4fcafa508c2debfaace36`, 4134B. All thirteen activation input streams were read, decoded and size/hash verified; SOURCE-READ_ACK was written before substantive SOURCE review. Its initial byte-reading claim is explicitly distinguished from the subsequent mathematical reading recorded here.

Source: `author-01/OriginalPhysicalCompactCDF.lean`, SHA256 `2273f619b4cc4a3cf7d9fd8141392ba7839352052db2b858e2995f3681545de2`, 7821B/171LF. New proof: `PROOF.txt`, SHA256 `d31dd7570b104fc5f3a5cecc1e1777171e5908806432791aa978ba3417384c25`, 5437B/115LF. Literal assembly independently recomputed:

    frozen preamble (source1–13)
    + frozen head (14–53)
    + PROOF.txt (54–168)
    + frozen closing (169–171).

There is no altered frozen byte. The head remains SHA256 `8f2442fc18632aabd158ee56473abe6b53efe9ddbba5e08b3c6d7140f9b44056`, 2082B/40LF, under freeze `35fd1a442e1803430b43fe016df40f4ad8081a44db95007c6d958e79d91be774`.

The complete 12932B implementation report was read. The implementation manifest and LASTFINALWRITE references were deterministically walked: 27 unique exact local path/hash/size bindings matched. This is a byte-binding check, not duplicate mathematical adjudication of the old reports contained in those references. The author release is SHA256 `ff7d815803bf4818cdd4e8c5aa022d6a98dd08ee9cade8bac2a47cb989aac692`, 3476B. ALL authority-release fields are true in that record's TOP LEVEL; writers/heavy/inflight/pendingExternal/uncertain/children are each zero and top-level sixZero=true. There is no nested release object. Parent intake `42d36f92bc06d6022943c05e5a0ab55b90b16c21beb3de0571e258254942888d` is consistent with those derived bindings and assembly.

SOURCE-COVERAGE records disjoint exhaustive spans and one row per actual source line, with exact line SHA256 and its semantic review group. All 171 lines, including the preamble, complete unchanged head and closing, are accounted for. All 115 newly written proof lines54–168 were semantically reviewed. No source line or proof branch was omitted. The source currently has one public theorem, no new public definition/instance/helper, and no sorry/admit/new axiom/unsafe/native_decide text. That static source fact is not a compiled-owner or axiom audit.

## Preamble, head and original goal captures: lines1–56

The two frozen imports expose only the required qualified producer interfaces. autoImplicit remains false; namespace/noncomputable section/open scopes/universe are exact frozen text. No new heartbeat option, local axiom or public helper appears.

Lines14–53 preserve all already accepted frozen semantics: arbitrary original measurable Ω, probability μ, actual jointly measurable symmetric centered L² h, actual projection second moment one, real 2<p≤3 and genuine original hgp; actual g/r/v, s=1+sqrt(v), β; a single positive K before all n≥3 and x∈[0,1]; the original pi law, literal physical finiteRows U/jackknife square T with zero else branch; and all four strict/closed CDF/tail inequalities with the unchanged rate. The broader ordinary CDF-input hSZC is still distinct from the tail hSZ input and remains conditional.

Line55 selects classical reasoning, which does not itself assert an axiom audit result. At line56 `intro g r v s β` introduces the let-values from the already elaborated ORIGINAL goal. These local definitions capture μ/mΩ before the coarse instance is installed later. They are not recomputed under a new sigma algebra. Likewise the fixed model s is not the sample Studentizer.

## One221 call and all conjunction positions: lines57–64

The single221 call instantiates its universes at `{u,0,0}` and passes exactly μ,h,hh,hh2,hhsymm,hcenter,hprojectionsecond. Ω remains in u; the future finite index and real target need only universe0. The call occurs once before K,n,x.

`dsimp only at hmodel` removes the producer's let-bindings while preserving their elaborated measure/space arguments. The first obtain selects m₀, hm₀:m₀≤mΩ, countable generation at m₀, coarse h measurability and the reduced coarse model. Its zero-observable measurability field is discarded.

The 22 fields of hmodel₀, read from the qualified public statement, are:

| Position | Exact field | Consumer action |
| --- | --- | --- |
| 1 | μ₀ probability | hprob₀ |
| 2 | μ₀ as identity pushforward | discarded |
| 3 | total g₀=g | hgeq |
| 4 | total r₀=r | discarded |
| 5 | separate v₀=v | hv |
| 6 | rho₀=rho | discarded |
| 7 | row-integrability equivalence | discarded |
| 8 | h coarse L² | hh₂₀ |
| 9 | coarse h mean zero | hcenter₀ |
| 10 | g₀ measurable | hg₀ |
| 11 | g₀ L² | discarded |
| 12 | g₀ mean zero | discarded |
| 13 | g₀ second moment one | hgsecond₀ |
| 14 | r₀ measurable | discarded |
| 15 | r₀ L² | discarded |
| 16 | r₀ symmetric | discarded |
| 17 | r₀ canonical | discarded |
| 18 | projection-law equality | hglaw |
| 19 | ENNReal-p MemLp equivalences | discarded |
| 20 | pair-law identity | discarded |
| 21 | generic finite-J/all-target clause | hfinite |
| 22 | specialized n≥4 centered/clipped clause | discarded |

The rcases pattern at63–64 selects exactly those positions. In particular hfinite is position21, not the n≥4 clause22. No factorization premise, countable-generation hypothesis about mΩ, or specialized statistic has replaced the generic law.

## Internal typed values and instance captures: lines65–81

At65 μ₀ is explicitly `@Measure Ω m₀` with the literal value μ.trim hm₀, while the original μ is still captured. Line66's identity has explicit source mΩ and target m₀; `measurable_id'' hm₀` has the mathematically correct monotonicity direction. The structure installed at67 is m₀, the countable-generation instance at68 refers to that structure alone, and69 gives probability only to μ₀.

Lines70–72 define g₀,r₀,v₀ with the coarse measure and its product. Line73 explicitly fixes the original real projection law ν with `@Measure.map ... mΩ ... g μ`, despite the surrounding coarse default. Lines74–78 convert the extracted statements to exactly g₀=g, v₀=v, measurable g₀, coarse second moment one and μ₀.map g₀=ν. No equality of integrals is inferred merely from r₀=r across different measures: hv is the producer's separate exact v equality.

Lines79–81 prove original g measurability by total g equality and composition of the coarse g₀ with the original-to-coarse identity. The resulting type explicitly names mΩ. This supplies the genuine original measurable-map witness without a new public hypothesis.

The nine new internal typed let-values were all checked: μ₀, g₀, r₀, v₀, ν, F, mN, mN₀, Pc. Their captures match the manifest. All six letI scopes were checked: coarse Ω at67, its CG at68, its probability at69, temporary original Ω at89, temporary original Ω at104, and temporary original sample space at145. None transports a coarse CountablyGenerated instance to the original mΩ.

## Genuine real-p moment and beta: lines82–107

F(z)=Real.rpow |z| p uses the SAME real exponent p. Lines83–87 prove continuity using p≥0 from 2<p; hence the a.e.-strong-measurability requirements on real projection laws are available even if Ω has no topological structure. This is the actual rpow continuity interface already inspected in170.

The hFν block88–92 restores original mΩ locally. After unfolding ν, the equivalence integrable_map_measure has type

    Integrable F (μ.map g) ↔ Integrable (F ∘ g) μ.

Direction .2 is correctly applied to the original genuine hgp, whose integrand is definitionally F(g(o)). Thus Integrable F ν is established from integrability, not from a finite-looking value of a totalized integral.

Lines93–95 rewrite the exact projection-law equality to obtain Integrable F (μ₀.map g₀). Lines96–97 use direction .1 of the same equivalence with hg₀.aemeasurable, obtaining the genuine coarse real-p moment required by170. The ENNReal-p MemLp equivalence from221 is not used or confused with this statement.

Lines98–107 then prove the exact beta equality. The first integral_map is used backwards with coarse g₀ and the already established integrable F under its map law. hglaw replaces that law by ν. The final block restores mΩ locally and applies integral_map to original g and hFν; rfl identifies the captured β. Both coarse and original p-integrability have already been established. There is no nonintegrable-integral shortcut, moment bound, exponent conversion, beta inflation or limit argument. p=3 is covered; no p=2 extension occurs.

## Explicit170 call and common K: lines108–115

The fully explicit @170 call supplies C,hSZC,Ω,m₀,hcg₀,μ₀,hprob₀,h,hh₀,hh₂₀,hhsymm,hcenter₀,hgsecond₀,p,hp2,hp3,hgp₀ in the correct declaration order. The coarse row-integral expressions in hgsecond₀/hgp₀ are definitionally the exact normalized projection required by170. Symmetry remains pointwise symmetry of the original h; no new model is substituted.

The same hSZC applies at universe u to the internal probability model. Its external existence/proof is not asserted, and it is not replaced by any tail-only input. `dsimp only` exposes170's let-bound rate values; rewriting hβ₀ and hv changes its true coarse moment/residual values to the frozen originals. The separate equality hv is used, not an unjustified change of measure.

Line114 takes exactly170's K and positivity proof;115 inserts this SAME witness into the original goal. No new factor, additive exceptional payer, or n/x-dependent constant appears. Coarsening and the170 invocation precede the introduction of n and x, as required by the frozen quantifier order.

## Original sample law and same physical function: lines116–126

`intro n hn N q P U R2 T` at116 introduces values from the ORIGINAL already elaborated goal. The fact that a coarse Ω instance is currently in scope does not re-elaborate those let definitions: P carries the original pi structure and μ; N,q,U,R2,T retain their original expressions.

Lines117–120 make both sample structures explicit: mN uses mΩ and mN₀ uses m₀. Lines121–123 type Pc as a measure on mN₀ and construct it with the explicit coarse coordinate structures and μ₀. These definitions cannot silently capture the original law into Pc or vice versa.

After hphysical n hn, the coarse T-measurability is definitionally changed at126 to `Measurable[mN₀,borel ℝ] T`. This is valid mathematically because both total functions use only n,h,ξ and the literal same finiteRows definitions; no measure, g,r or clipping parameter occurs in T. The exact positive-R2 guard and zero else branch are unchanged. There is no agreement only off a zero set and no hidden identification of projection-energy zero with physical jackknife zero. For n≥3 the row coefficient remains nonnegative, with n−2 nonzero; n=3 is included by170 itself.

## Generic finite-J transfer and original measurability: lines127–135

The finite index is Fin n with its Fintype instance. hfinite has no n lower bound. `dsimp only` and the four-field rcases select its measurable identity and arbitrary-target map law; its probability/product-law fields are unused. Line130 explicitly identifies the original-to-coarse SAMPLE identity.

At131 hT₀.comp hidN is original-space T measurability: composition with id is definitionally T. This is the actual measurability conclusion in the original goal, not merely the coarse one. At132 the generic target law is specialized at ℝ,borel ℝ,T with coarse measurability. Lines133–135 explicitly identify its two domain structures and measures as mN₀/Pc and mN/P. There is no n≥4 clause, desired-event hypothesis, atomlessness or replacement statistic.

## All Borel events and real probabilities: lines136–150

The local hEvent takes an arbitrary Borel real set B. Its two preimages are sets of the same underlying sample type. Lines139–141 use map_apply backwards on the coarse side with hT₀. Lines142–143 apply the exact measure-law equality to B by congrArg. Lines144–146 use map_apply forward on the original side, explicitly restoring mN for that subproof. Each map_apply has the corresponding measurable T and measurable target set. The required product measure/structure captures are visible in the terms.

Lines147–150 apply ENNReal.toReal to the exact ENNReal equality and unfold Measure.real_def. Equality is simply preserved by toReal; no complement subtraction or conversion of an inequality across infinity is involved. Both pi measures are probability laws, but even additional finiteness is unnecessary for this equality operation. hEvent and hrealEvent are proved internal facts, not public assumptions.

## Four endpoints, unchanged error and final conjunction: lines151–171

Line151 provides the original hT. Line152 introduces x,hx,hx1 and the already elaborated ORIGINAL error let-value. Lines153–160 invoke hrealEvent separately on Iic x, Iio x, Ioi x and Ici x. Their Borel proofs and preimage meanings match, respectively, T≤x, T<x, x<T and x≤T. All four exact identities are kept, including equality atoms. No event is reconstructed from a continuity argument or a different open/closed convention.

Line161 obtains170's four bounds at the same x with the SAME closed range hypotheses. Lines162–166 state exactly the coarse probabilities with the frozen original error; the earlier beta/v rewriting supplies that rate. Line167 rewrites all four probabilities to the original P, and168 returns the complete conjunction. Both x=0 and x=1 are retained; zero-physical-denominator atoms and ties are not removed. No extra coefficient or exceptional payment is introduced. Lines169–171 close precisely the frozen section/namespace.

## Source-fidelity and evidence boundary

The prior complete statement/theory review `0cba30d8d6cad2de3a9b7e088a9405ad7d6e844b2be2205de1e6fd7647e6d7ad` is reused for its original p51/p54 and CDF-input semantic adjudication. This actual implementation follows that route. Original arbitrary measurable Ω, actual μ/h, normalized real projection, finiteRows statistic, zero convention, n≥3, all four endpoints and exact rpow rate remain intact. There is no public countable-generation/standard-Borel, atomless, n≥4, extra moment, beta bound, event-law or window premise.

Qualified221/170 source hashes still match their source-bound accepted evidence. Their unchanged proofs, compiled TYPEs, native and recursive-AX judgments are reused, not independently repeated here. This new source introduces no mathematical scope change from any separate unit263 tool/elaboration diagnosis. Such a diagnosis is neither a264 proof result nor authorization to alter264's statement.

Source correctness does not establish Lean elaboration. In particular the source's `change`, `rw`, local-instance and dependent-let conversions still require the designated-server kernel attempt on these exact bytes. If an attempt fails, retain the failure and use a new authorized affected repair; do not weaken the frozen declaration. After success, the SAME FIRST original object needs complete all-actual-owner TYPE/required VALUE and transitive-axiom evidence, followed by this retained reviewer's final exact binding/coverage review. Compiled generated owners and actual axiom dependencies remain unknown at this stage; no count is fabricated and no old accepted producer/leaf audit is requested again.

The conditional broader scalar CDF input's existence/proof, unbounded/growing or relative tails, p54 conditional-family uniformity and strict upper-event margins, DC, full OQ56 and root remain OPEN. p54's rejection of arbitrary polynomial conditional p-moment rates is respected: no changing conditional family appears in this proof. External-result attribution and novelty/priority limitations are unchanged.

Only local deterministic reading/hashing/reconstruction and review-file writing occurred. No source edits, Lean/build/axiom command, server/network/Git/API/publication or child operation occurred. No Goal or schedule was created. All new reviewer files are UTF-8 without BOM, LF only, exactly one final LF. CHECKPOINT-SOURCE-01 is written last with writers/heavy/inflight/pendingExternal/uncertain/children zero; reviewer authority is retained for final review and no FINALWRITE is issued. An idle checkpoint is not an assertion of persistent runtime activity.

Requested model/effort remain gpt-6.1-sol/xhigh. Actual model/backend/effort are unexposed/null; input, cachedInput, output and reasoningSubset telemetry are separately null. No token or subscription allocation is invented.
