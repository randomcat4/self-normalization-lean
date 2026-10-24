# Unit171 independent complete source review — original archived source

STATUS: STATIC_CORRECT_NOT_QUALIFIED

The complete mathematical source-to-statement/proof review finds no critical mathematical gap in the exact 6,670-byte, 155-LF-line source `835fd74807aefa3d6cf165a942fb8de38f935eaf83a867e676d18026eb8646bc`. The actual first server check failed at source line 133: `` `dsimp` made no progress ``. Therefore this report does **not** qualify this source, certify successful elaboration, or claim a kernel/all-owned-axiom pass. The original source remains immutable. A later same-context supplement must bind the authorized proof repair, review its actual delta and unchanged-byte correspondence, and literally read every actual owned TYPE, metadata field, required non-theorem VALUE and recursive axiom payload before final qualification.

I am a fresh independent final reviewer, separate from the Stage1/Stage2 author and the parent server executor. Prescribed model/effort are gpt-6.1-sol/xhigh; actual model and effort telemetry are unavailable, and input, cached-input, output and reasoning-subset counts are all null. I used math-theorem, not math-ultra. My write ownership is exclusively `drafts/oq56/unit171/final-review-01/`. No Lean, server, network, Git, cache, API elaboration, toolchain discovery, source/library/original/shared edit, child, chat, Goal or automation operation was performed. All mathematical sources were read only.

## Complete reading and immutable inputs

Before writing this report I read the entire new Lean source, both frozen exact headers and all seventeen full typed values, the complete author proof note, author DONE and both parent intakes. I sent the parent an actual read/hash acknowledgement before report writing. Exact principal bindings are:

| Input | SHA256 | Bytes |
| --- | --- | ---: |
| ActualPhysicalCompactRelative.lean | 835fd74807aefa3d6cf165a942fb8de38f935eaf83a867e676d18026eb8646bc | 6670 |
| Frozen declarations and values | df8db8225661424d84b4dac703b7e9cb36db16ae7fd07c17c9306d1e7099c4e1 | 14493 |
| Stage2 proof-note.md | 28926d3d993f6140430bd6628ede59490836177d4cab494007421eb850468f5c | 6676 |
| Stage1 mathematical-derivation.md | f44c933a8b87d56d396315033210cb6aa161103cfbe9560c4f90d83424988b42 | 13567 |
| Stage1 consumed-interfaces.json | 66fe244424a74729fbc263485178ff146c9053f9a256e3efd32fcc039cc7ea5f | 84186 |

I read all five mandatory original inputs in full: scope01.md (8682 B, 5c8653d5...), p37.md (16161 B, dff4a1c5...), p38.md (9383 B, 4ba79f1a...), p39.md (19898 B, 25124983...), and p54.md (6045 B, e03649e1...). Full exact hashes are in input-bindings.json. This is a review against their genuine statistical objects and stated repaired scope, not a name/hash-only reading. I also read applicable AGENTS.md, SERVER.md, streamlined acceptance, and selected current TEAM/REGISTRY ownership/model/resource fields. OQ56's activated owner is 01a16c48-9017-7d50-8123-83c72763be0f; coordinator authority remains with 01a16be2-3e35-7e13-97d3-7b11b603dead.

The entire consumed interface packet was read by fields, including the literal complete 230-line, 16,069-byte actual TYPE of exact170, its raw full consumed header, all six project defining bodies, all eight pinned Gaussian/CDF/measure/arithmetic API records with full raw namespace/section/variable contexts, the full positive-density packet, and the full support/positive-integral packet. I read the actual to_additive primary annotation generating Function.support, together with its defining body and mem_support header. Input/coverage files distinguish those mathematical readings from administrative fields selected for deterministic binding verification.

## Source-to-statement fidelity

The public theorem keeps C and the ordinary supplied scalar Shao-Zhou finite-cost CDF Prop before the original law, n and x. I read that Prop's entire higher-order body: it concerns arbitrary scalar measurable independent centered finite-second-moment coordinates, normalized total energy, measurable scalar remainder/envelope/deleted-coordinate functions and the specified finite compact cost, under positive V and correction. It is not the desired physical tail assertion recast as an input. Its existence/proof remains UNPROVED; this consumer supplies neither one.

The observation space remains countably generated. The single original probability law mu determines the actual iid product P0. The kernel h is jointly measurable, joint L2, pointwise symmetric and centered under mu product mu. The projection is the actual integral g(o)=integral h(o,y) dmu(y), with its actual second moment equal to one; beta is the actual integrable projection p-moment for fixed 2<p<=3. No free projection or synthetic law is substituted.

I verified the direct library definitions against the packet and current local source bytes. unorderedPairSum sums only i<j; uStatistic divides that sum by n choose2; rowMean omits i and divides by n-1; jackknifeSq is precisely 4(n-1)/(n-2)^2 times the sum of squared centered row means. Thus U and R2 are the original centered-row jackknife objects of scope01/p39. T is sqrt(n) U/sqrt(R2) when R2>0 and is exactly zero otherwise. It has the same branch and same zero-event payment already included in170's qualified absolute error; the consumer does not remove or identify physical-zero and projection-zero events.

There is one positive Krel for every n>=3 and every x in the entire closed interval [0,1]. The genuine displayed error is Krel times beta/n^((p-2)/2)+s/sqrt(n), with s=1+sqrt(integral r^2). Both actual upper events x<T and x<=T are retained separately. There is no atomlessness, density, nonlattice, extra joint/diagonal moment, beta>=1, concentration, desired probability, or conditional standardized p-moment-rate assumption. No eventual-n or growing-window conclusion is inserted.

The source therefore expresses the frozen limited compact relative-tail consequence. It does not prove original OQ56/RS2 closure, the full moderate-deviation window or a new external probability engine. It preserves the p54 correction: no arbitrary polynomial convergence rate of conditional standardized p-moments is used or claimed. The published Shao-Zhou engine remains externally attributed. Novelty and historical priority are unverified.

## Private helper: full proof review, lines 14–51

At lines 16–22, f is the actual standard Gaussian real density. Its full primary formula is the inverse square-root normalizer times exp of the negative centered square over twice the variance. The pinned positivity lemma applies at nonzero NNReal variance one and gives f(x)>0 for every real x. Global Gaussian integrability restricts to real volume on Ioc(1,2); no finite-integral assumption is silently introduced.

At lines 23–30, the actual support definition is {x | f(x) != 0}; positivity therefore makes it univ. Restricted volume evaluates that support as volume(Ioc(1,2))=ENNReal.ofReal(1)>0. The measure here is the restricted Lebesgue measure, so this step assumes no Gaussian tail probability.

At lines 31–37, integral_pos_iff_support_of_nonneg applies with the proved pointwise nonnegativity, actual restricted integrability and positive support mass. It yields a strictly positive real density integral. gaussianReal_apply_eq_integral at variance one identifies the actual Gaussian interval measure with ofReal of that integral. Its integral is nonnegative, so toReal(ofReal(...)) is the same real integral. Thus the real Gaussian mass of Ioc(1,2) is strictly positive.

At lines 38–42, Ioc(1,2) is a subset of Ioi(1), and Gaussian probability finiteness meets real-measure monotonicity's finite-upper-mass condition. The real upper-ray mass is positive. At lines 43–49, Ioi(1) is exactly the complement of measurable Iic(1), so finite probability complement and real total mass one give its mass as 1-Phi(1), using the actual project CDF identity. Lines 50–51 conclude the exact private statement. No reflection, numerical tail approximation or Gaussian positivity premise is imported into the header.

Every private proof step has the correct mathematical object and hypotheses. The explicit Gaussian measure arguments at lines 42 and 48 are appropriate. The compiler reported no failure in this helper; that observation does not replace the still-missing successful complete module gate.

## Public theorem: full proof review, lines 53–151

Lines 93–97 reintroduce precisely the frozen actual g/r/v/s/beta. Lines 98–100 consume170's qualified theorem with the unchanged complete hypothesis application, yielding Kabs>0 and its all-n/all-x absolute bounds. Kabs is an existential theorem witness, not a newly supplied assumption. Lines 101–105 set a=1-Phi(1)>0 and Krel=Kabs/a>0 before introducing n or x.

Lines 106–120 fix arbitrary n>=3, reproduce exactly the same product law/U/R2/T and retain measurable T from170. Lines 121–125 fix any 0<=x<=1 and introduce exactly Psi=1-Phi(x) and the inherited rate E. Lines 126–131 apply the actual monotone Gaussian CDF to x<=1, obtaining Phi(x)<=Phi(1), hence a<=Psi and Psi>0. This includes x=0 and x=1 without any special continuity or atom premise.

Lines 132–137 specialize the absolute bound and extract its strict and weak upper inequalities individually. The redundant dsimp at line 133 is the single actual compiler failure; mathematically the subsequent conjunction decomposition is the same absolute theorem specialization. Nonnegativity of Kabs*E is correctly obtained from the strict absolute inequality and abs_nonneg. This is a consequence of an already-proved absolute bound, not circular use of the desired relative conclusion and not a missing beta-nonnegativity assumption.

The proof-only local hrelative at lines 138–150 has exactly the frozen header. It treats arbitrary real P with its own absolute bound. Since Psi>0, field algebra gives P/Psi-1=(P-Psi)/Psi, and absolute division gives |P/Psi-1|=|P-Psi|/Psi. Dividing the supplied inequality preserves direction. Because a<=Psi, a>0, Psi>0 and Kabs*E>=0, the next comparison (Kabs*E)/Psi <= (Kabs*E)/a is valid: the displayed cross multiplication is exactly (Kabs*E)*a <= (Kabs*E)*Psi. Final ring factorization is (Kabs/a)*E=Krel*E. Line 151 instantiates that proof independently for P0.real{x<T} and P0.real{x<=T}. No event is exchanged at equality, including the physical T=0 convention at x=0.

There is no critical mathematical gap in either proof. The formal script as archived fails elaboration; a proof-only compiler repair and its subsequent exact-source evidence remain required.

## Freeze and complete coverage

My independent static checks confirm the exact raw prefix, suffix and both raw headers, the single import, autoImplicit=false and unchanged default heartbeat. All twelve header values and five constructive proof-local values were read in full, checked against their frozen expression byte bindings, and matched to all twenty-eight source let occurrences. Eleven header values are reintroduced; error is unfolded instead. Expression-only indentation/newlines are normalized explicitly where a multiline source expression is compared with the single-line freeze value. Raw source-expression hashes and byte lengths are retained separately; this is not claimed as raw-byte identity across whitespace changes.

The witness application and proof-only hrelative header were checked in full. There is no extra mathematical data let, global definition, helper, import, option or hidden ambient variable. source-per-line-coverage.json covers each of all 155 source lines with its LF-inclusive UTF8 byte count, line hash and specific semantic/proof assessment; the line byte counts sum to6670. frozen-source-values-coverage.json contains all seventeen full typed values and all twenty-eight independently parsed spans. consumed-interfaces-values-coverage.json records the complete consumed mathematical review and actual170 type binding. This evidence is bound to the original archived source, not to a future repaired version.

## Exact170 reuse and interaction

I read the source-bound qualified-evidence.json cce1dc7e... (5737 B), its complete independent final qualification 963d3e2a... (6532 B), and parent-final-intake2922668b... (698 B). Their local linked evidence was rehashed. Exact170 source is d264ae1c1f04cee3b43ec5e44829a5986574d70f30615f7bdeb1f1bfab2a14ae (26260 B); its object hash is c907a0e8730cae485e8e6614f4fb3aa5f839687cb748b71f2706b9cb7c7a0dfb. Its consumed actual type is 2ee2c1d3b302cce3257e8581eaf0ca9b79fac30c46d0f6c9f55d6b4f62cbd377 (16069 B/230 lines) and was read literally and compared exactly with the qualified actual metadata entry.

The old independent complete proof review, kernel and all-owner audit are reused, not rerun or recertified by me. I have not claimed a second complete old-proof reading. The new theorem's interaction is exactly specialization of the same physical absolute rate followed by genuine Gaussian denominator algebra. There is no changed old mathematical interface, assumption or statistic and no uncovered interaction requiring another old-proof review. Accepted147/169 dependencies remain transitive through170. No168 reflection dependency is introduced.

## Actual compiler evidence and remaining qualification

I read the entire local parent diagnostic projection8f8d1153633ef3c11413d8fc97e7ec80bdc48b2807ba76d9d32fdb394462de74 (4197 B). It binds the archived source and input copy to835fd748..., the actual remote receipt eedfe3c63688520c74b88ee618ce57e750fcb056c5ce2fa89a7cbc38b75a697f (3173952 B), and the complete83-byte sole error: source133:2, `` `dsimp` made no progress ``. Direct Lean exit is1, no output object exists, no timeout or ownership issue occurred, and all owned execution ended. The retained134-byte stderr is the known Lake local-changes notice. The projection records all3435 protected records exact with full mode, equal preservation and unchanged Git, the pinned mathlib807d3836..., CPU22–25, -M8192 and -j4. I did not fetch or independently rerun the remote raw receipt, command, binary or environment.

I also read the exact prepared actual-owner audit source e1538984... (2770 B). It selects every constant by the actual imported module index, not by namespace or a guessed count; includes private/generated/out-of-namespace ownership; records kind, full name components, universe parameters and body-present flags; emits full TYPE and every actual defn/opaque VALUE; and recursively collects axioms against only propext, Classical.choice, Quot.sound. This is an inspected future audit program, not an executed receipt. No171 actual-owned count, TYPE coverage, non-theorem VALUE count, axiom count or successful object is inferred from the two source declarations or17 frozen values.

Required next: the parent may reactivate the same released author for the actual compiler-directed proof repair within its lease; preserve this original source and failure. After the affected server source gate and actual-owner audit succeed, the same independent reviewer context can reuse this unchanged full review, inspect the exact mathematical/proof delta and unchanged-byte correspondence, then literally read every new actual owned payload and bind all evidence. No duplicate complete original-source or old170 review/check is automatically required.

OQ56 and C12 remain OPEN; OQ3 remains PAUSED_BY_USER; OQ4's separate limited acceptance is preserved. This review provides no root closure or novelty claim. At release my writer, execution and in-flight counts are zero; the ordinary review turn ends, with the precise next dependency above.
