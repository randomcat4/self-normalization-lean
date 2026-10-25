STATUS: CRITICAL_GAPS

Complete independent STATIC source-to-statement/proof review of unit 193, exact candidate SHA256 c7eb34c3587f69da035af24be9dbc02a576d860b1268f0117cd64d492adc4564 (98,380 bytes, 1,738 LF lines). The mathematical argument and frozen statement are sound on this review. The submitted Lean text has concrete native-source closure gaps identified below. This does not assert that the theorem is false, and is not a compiler-observed failure: no Lean command was run.

Reviewer: /root/actual_bad_interval_negative_complete_source_review, independent of the source author. Requested model/effort gpt-6.1-sol / xhigh; actual backend/model/effort and separate input, cached-input, output, and reasoning-subset counts are unobservable and recorded null. No substitution was requested. Exclusive write scope is this review folder. The author release independently hashes to 60826ba305ffbcfcb36cdb38f83adc239d9ddb05afa045899ad16407d3b33cfa, with sourceWriter/executionWriter/inflight all zero.

Only local reading, hashing, text comparison, and review-artifact writing occurred. No server contact, Lean/lake/kernel/axiom command, upload, Git/API publication, further delegation, owner wake, or source modification occurred. Later observed project resource-phase metadata does not expand this reviewer's explicitly static assignment. C2/C12 remain OPEN.

## Concrete native-source gaps

**N1: unresolved namespace at line 758.** The type annotation is HalflineReflectionIdentities Q. Its defining declaration is Shao.Probability.SourceActualLocalProfileBudget.HalflineReflectionIdentities (source lines 35–39). The candidate opens SourcePermutationReveal, SourceSeparatedOvershoot, and ActualSignedDoubleTelescope, but neither opens SourceActualLocalProfileBudget nor qualifies this name. The open command inside the imported ActualSignedDoubleTelescope module is its lexical name-resolution context, not an exported declaration in its namespace. The inspected source has no export/alias for this name. The submitted proof therefore lacks a resolved reference at this annotation. Full qualification would preserve all frozen declarations/premises. This is an implementation defect, not a missing reflection theorem or mathematical assumption.

**N2: missing propositional wall transport at lines 1401–1404.** The rewrite at 1401 changes the left side of hneg to use wall v. The following hAv explicitly retains actualWall a x. Its proof only simplifies A, D, and if_pos hT; it omits hwall. These walls are propositionally equal by hwall but are not definitionally equal: one contains energy (Fin.append v u), whereas the other contains T + energy v. The append-energy identity is required. The stated estimate is mathematically correct, but this use site does not carry the already-proved wall equality.

**N3: the corresponding lower-sign gap at lines 1416–1419.** The rewrite at 1416 likewise replaces actualWall a x by wall v in hneg, while hAv keeps actualWall a x and its listed simplifications again omit hwall. This is a second occurrence of N2.

These are static source findings, not invented compiler diagnostics. There may be additional native syntax, namespace, API, tactic, dependent-index or simplification failures when the designated server elaborates the source. In particular, the normalization/product transports, variance_sum_pi call, dependent append/rank identities, block split and grid rewrites have only been inspected statically. I do not claim those applications have passed.

Overall STATUS is CRITICAL_GAPS for the exact native source. The mathematical disposition is CORRECT: no missing mathematical premise or counterexample was found. N1–N3 identify missing native-source connections, rather than merely a missing check. Accepted theory evidence remains valid. After authorized repair, this same reviewer can review only the affected source delta and subsequent actual machine artifacts; unchanged mathematical proofs and qualified old producer proofs do not automatically require another complete review.

Actual elaborated types, generated/private owner inventory, elaborated non-theorem values, kernel object, and recursive all-owned axiom report are UNKNOWN/NOT_RUN. The 21 count below is a SOURCE top-level declaration count only, never an actual-owned/generated count. The permitted axiom whitelist remains propext, Classical.choice, Quot.sound; no dependency set was computed here.

## Frozen bytes, values and original scope

The complete public context/local instance/bill prefix is byte-for-byte equal to frozen-public.lean.txt, SHA256 7f0960fc2b7b64371bf1c38b1e9cebf98bd4519e6836435c023468f4c14fa398. The full public theorem head is exact. All 18 private heads match frozen-private-heads.lean.txt, SHA256 21aecfec04487b7f48e051f939b0ad84a1423e7dfcc8f70ecd3df76d3179c444. These comparisons were independently recomputed. Imports, options, opens, namespace, instance/bill values, binders, hypotheses, theorem-local lets in the frozen heads, and targets are preserved. No global helper definition, assumption, import or oracle was added. There are 18 private theorem bodies, 1 public body, 1 local instance and 1 bill definition: 21 SOURCE declarations.

The source is valid UTF-8 without BOM, has 1,738 LF bytes and zero CR bytes, and matches the assigned hash and byte count. A lexical token scan finds no sorry, admit, axiom, unsafe or native_decide. This scan is not elaboration or axiom certification.

Line 18's local measurable-space instance has the exact value top on LabelPerm n, consistent with the discrete space used by the actual permutation/reveal definitions. The bill at 20–28 sums all r in range n. Its weak bad mask is 3*x*sqrt(T)/2 <= abs(d), and its value is the OWN negative part of the actual interval separated overshoot with cap nu p.1. No full-amplitude or one-wall domination has been substituted.

The universal positive C precedes every law, bound, n, x, Brownian space/representation and cap. The probability law has EX=0, EX²=1 and a.e. abs(X)<=B with B>0. Boundedness supplies the moments used. The support factor remains 1/100, x>=16, and delta*(1+x)^3<=exp(-3*x²). Beta/delta are the actual integral/normalization. The cap is only section-measurable for each finite permutation and pointwise <= energyCutoff at 4*beta². It is never given an extra stopping premise. The conclusion covers the exact bill's measurability, genuine L1, nonnegative integral and C*delta*standardNormalTail x numerical bound.

I read the complete frozen theory subject, all 269 proof lines, complete accepted independent mathematical report, parent theory acceptance, occupancy/attribution note and original-source excerpts. The proof hash independently matches 9a2567b45875f70addbcf0e3e522d137fccf635f35ade760f312b73679c2c8b4; the report hash matches 9c96cf8903a8b9be04e38ab134265c5b2f84c62b7aa40d7137a2a0ed59ec82a1. This accepted mathematical evidence is reused; every final Lean proof body and encoding was independently inspected here.

The immutable original C:/game/shao/current/c12/supplement.tex independently matches SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd. Its specified ranges 4323–4341, 4867–4903, 4978–4999, 5046–5065 and 5564–5588 reproduce the supplied excerpt exactly after only line-ending normalization for that comparison. The excerpt byte hash is 9f0df75032e6b0619ee39f86dc3fb2ded37fe84adb36084124147e6fadb61e51.

Those ranges supply the own-negative projection, bounded actual-energy strip, actual cutoff, rare grids and retained negative interval term at a bad first exit. This source pays that bounded residual negative bill only. It does not pay all double/second-wall/retained/terminal bills or general unbounded finite-second-law truncation/assembly. Original C1's separately accepted immutable completion is unchanged; C2/C12 remain OPEN. This is source reproduction/proof closure, not a novelty claim. Attribution to prior RootB cubic proxy work is retained; no unqualified proxy conclusion is assumed.

## Full 1,738-line coverage

All exact source lines were read in order with line numbers. This contiguous partition covers 1–1,738 without a gap; blank separators belong to the preceding unit. Every new head, local let/value and all 19 proof bodies are included.

| Lines | Unit | Coverage |
| --- | --- | --- |
| 1–29 | Imports/context, local instance, bill | Complete context and both non-theorem values |
| 30–82 | H01 bounded_moment_data | Entire head/body |
| 83–102 | H02 clipped_square_lipschitz | Entire head/body |
| 103–190 | H03 floored_statistic_strong | Entire head/body and clip/F/H/update-sum lets |
| 191–254 | H04 normalized_iid_data | Entire head/body and beta/scale/eta/budget |
| 255–322 | H05 iid_low_energy | Entire head/body and L2/variance/indicator |
| 323–422 | H06 actual_wall_interval_concentration | Entire head/body and floor/normalization sets |
| 423–478 | H07 reverse_closed_survival | Entire head/body and normalized reversal |
| 479–743 | H08 large_x_true_energy_closed_strip | Entire head/body, both signs and product split |
| 744–773 | H09 actual_interval_kernel_data | Entire head/body; N1 |
| 774–867 | H10 local_actual_negative_cubic | Entire head/body and all signed/guard cases |
| 868–892 | H11 capped_source_negative_domination | Entire head/body and cutoff cases |
| 893–958 | H12 bill_measurable_integrable | Entire head/body and genuine finite L1 |
| 959–1069 | H13 cap_reorder_reduction | Entire head/body and iid transport |
| 1070–1155 | H14 iid_rank_negative_disintegration | Entire head/body and complete append/Fubini |
| 1156–1258 | H15 fixed_suffix_cubic_bound | Entire head/body and actual first suffix label |
| 1259–1480 | H16 fixed_suffix_late_marked1_bound | Entire head/body, both strips/gain; N2/N3 |
| 1481–1520 | H17 rank_grid_reindex | Entire head/body and parity/injectivity |
| 1521–1576 | H18 early_gaussian_factor_comparison | Entire head/body and native tail comparison |
| 1577–1737 | Public theorem | Entire head/body and all rare/rank/grid/constant assembly |
| 1738 | Namespace close | Read, consistent |

All helper names in this table have the source prefix anib_. The next section analyzes each proof separately.

## Per-proof analysis

**H01 (30–82).** For every natural p, a.e. support bounds both z^p and abs(z)^p by the integrable constant B^p, with explicit measurability. This supplies the genuine first/second/third/fourth moments. Integrating z²<=B² gives B>=1 because EX²=1 and B>0. The pointwise inequality 3z²<=2abs(z)^3+1 follows from (abs(z)-1)^2*(2abs(z)+1)>=0 and gives beta>=1. Finally z^4=abs(z)*abs(z)^3<=B*abs(z)^3 gives EX⁴<=B beta. No moment premise or undefined integral is hidden.

**H02 (83–102).** The min/max clip lies in [-B,B] on the whole real line and is 1-Lipschitz by the native min/max difference inequalities. Factoring the difference of squares and bounding the sum of clipped moduli by 2B gives the exact global 2B square-Lipschitz estimate. The B=0 case is included. No differentiation at clip joins is assumed.

**H03 (103–190).** F retains the original linear sum, clips only squared coordinates, and floors the root at k/2. H=2F(sqrt(k)*v)/sqrt(k) is measurable globally. Both root arguments exceed k/2; rationalization plus H02 bounds a root-coordinate change by B*sqrt(2/k)*abs(t-s). The update algebra explicitly removes the changed coordinate from the finite sum. The exact slope condition x*B*sqrt(2/k)<=1/2 then makes H gain at least t-s. Hence H(update a i t)-t is monotone on the entire line, including clip/floor joins. Positive k supplies all nonzero root denominators. This proves the unrestricted native concentration premise, not a support-only derivative statement.

**H04 (191–254).** Eta is the actual scalar pushforward under division by sqrt(k); probability, square integrability, zero mean and k*EY²=1 transport through that measurable map. The cubic moment transports genuinely as well. The actual truncation integrand z²*min(abs(z),1)<=abs(z)^3 gives R_k(0)<=beta/sqrt(k). The path normalization map has the product eta law. These are precisely the moments and genuine budget later consumed, with no artificial budget assumption.

**H05 (255–322).** X² is L2 by the genuine fourth moment. Product evaluation preserves coordinate laws; energy has mean k and variance k*Var(X²)<=k*B*beta. On energy<k/2, its squared centered value is at least k²/4. Integration of the measurable constant indicator against the genuine centered L2 square yields 4B beta/k. This pays the entire floor exception and establishes all needed L1/L2 facts before integration.

**H06 (323–422).** Native unrestricted strong-monotonicity concentration is applied to H under eta at closed endpoints 2a/sqrt(k),2b/sqrt(k). Its exact 2*(length)+80R bound gives (4(b-a)+80beta)/sqrt(k). On the common a.e. support set the clip is identity; outside energy<k/2, q>=0 makes the floor identity too. Thus the actual event is a.e. contained in the floored event union the low-energy exception. H05 and B<=sqrt(k) pay that exception by 4beta/sqrt(k), yielding 84*(b-a+beta)/sqrt(k). Uniformity is for every q>=0 and every interval location; endpoints/atoms are retained. There is no x<=1 call or random-wall stopping premise.

**H07 (423–478).** The survival constant is selected before rho/k/v. Normalize by sqrt(k), use positive homogeneity of the maximum including zero, and apply original_closed_survival_uniform at sign -1 and level v/sqrt(k). H04's genuine budget gives Cs*(v+beta)/sqrt(k). Reversal is an iid measure-preserving coordinate permutation. This yields the exact sign-negated reversed survival event without assuming symmetric rho or discarding a closed endpoint.

**H08 (479–743).** This is the all-energy large-x strip derivation. B>=1, x>=16 and 100*x*B<=sqrt(n) imply 10000*x²*B²<=n, excluding r<2 when n<=2r. With k=floor(r/2), ell=r-k, both are positive and at least r/3; n<=6k yields B<=sqrt(k) and the actual H06 slope condition. The original support factor 1/100 is retained.

The upper event includes every zero-through-r prefix sum below the actual wall x*sqrt(q+energy a), with terminal gap in [0,v]. Split into independent blocks k and ell. The complete reverse terminal-sum identity covers j=0 through ell. Survival and terminal gap force every negated reversed last-block prefix sum <=v. Fixing that entire block leaves the first block's actual energy statistic in [-lastSum-v,-lastSum], with external energy q+lastEnergy>=0. H06 is uniform in both location and energy; ordinary indicator L1 and Fubini therefore multiply it by the last-block survival bound H07. The source's safe estimate r<=4sqrt(k)sqrt(ell) gives Cstrip=336Cs, a harmless enlargement of the accepted theory's possible 252Cs.

For the lower sign, reflect the entire law under z↦-z. Mean, variance, support and beta are preserved and the product pushforward matches the sign-negated path. Thus the same constant applies without symmetry assumptions. q=0 and v=0 are included. Random prefix energy stays inside the wall throughout. The local set named G is a product survival/terminal-interval event, not RootB's high-energy-only set G.

**H09 (744–773).** Actual Brownian upper/lower reflection formulas and the resolved interval spatial derivative supply the reflection/regularity hypotheses of actual_interval_kernel_data. The mathematical result is measurability of the guarded actual interval derivative, KernelBounds constant 4 and the genuine interior HasDerivAt. No x restriction is needed. N1 concerns only the unresolved type-name annotation, not the availability or assumptions of those producers.

**H10 (774–867).** C0=2*compensatedProfileConstant is nonnegative and numerical; C0+1 is positive before every Brownian representation. The actual positive-T completion/derivative identity is explicit. At either projected boundary step p, p²<=T/2 and abs(y+p)<=w. The resolved Taylor producer allows this CLOSED boundary. Its interval increment profile is <=2, giving K*abs(p)^3. The upper own-negative producer bounds the actual upper negative overshoot by K*abs(b)^3; the lower producer and the explicit ring identity give the corresponding actual lower sign. Both current and terminal interiority are preserved when applying these estimates.

If the small-energy guard fails or neither wall is crossed, the separated value is literally zero. Exact crossing equality has zero excess and remains covered. This bounds the interval term's own negative part, never its full amplitude through a one-wall proxy.

**H11 (868–892).** A nonzero capped term requires r<n and r<nu sigma. Nu<=energyCutoff and exact cutoff data give h<=remainingEnergy and r<n. Replacing cap by constant n then leaves its source value unchanged. All other capped branches have zero negative part and nonnegative proposed dominator; r>=n is explicitly zero. This removes cap dependence by pointwise domination and uses no stopping property.

**H12 (893–958).** Actual kernel data and native section measurability/L1 give each fixed-permutation source section. The finite discrete permutation seed permits joint measurability. Remaining sum/energy are measurable finite observables, so the weak Bad set is measurable. Each negative masked term is bounded in absolute value by 4*4*(1+n)=16*(1+n) on every path/cap. The reveal probability law makes this a genuine integrable bound; finite sums give measurability, L1 and pointwise nonnegativity. This works for every section-measurable cap before any cutoff assumption.

**H13 (959–1069).** The canonical deterministic term has both h-energy and weak-Bad masks and genuine L1. Total energy/sum are permutation invariant. Evaluating it on the random reordered WHOLE path gives the constant-cap-n source at that permutation, with actual wall, live prefix, remaining energy/sum and crossing coordinate unchanged. H11 dominates the arbitrary-cap bill before any iid pushforward is used. The iid evaluation laws/independence then supply the actual random-reorder map to rho^n and its integral transport. No arbitrary cap or random wall is reinterpreted as an iid stopping object.

**H14 (1070–1155).** R is measurable and globally bounded, hence integrable. Fin.append carries independent prefix/suffix product law to the full iid path law. Literal append sums/squares give remainingEnergy=energy(suffix) and remainingSum=the entire suffix sum. Thus F is exactly R after append and has genuine product L1. Ordinary Fubini gives the suffix-outer/prefix-inner equality. The crossing label has not been removed from the suffix; no stopping claim is needed. The dependent-index/product API elaboration is still untested.

**H15 (1156–1258).** The fixed suffix has T from ALL its squares, d from ALL its coordinates, and b its first coordinate for t>0. The source proves this is exactly the full path's rank-r coordinate. Fixed-prefix L1 uses the old global source bound, not a false pointwise consequence of an a.e. Fubini result. On T>=h>0, H10 with z-y=d gives the cubic envelope. Dropping nonnegative crossing/activity supports afterward yields the exact marked3 denominator sqrt(T)^3 and drift power 3. Other branches are zero/nonnegative. It includes r=0 and is used for early ranks.

**H16 (1259–1480).** Conditioning fixes the COMPLETE suffix, hence b,T,d,D and Bad. The prefix wall remains x*sqrt(T+energy v), identified with the full actualWall through append energy. Live interval prefixes imply either signed closed survival. Upper crossing gives wall-S_r<=abs(b); lower crossing gives wall+S_r<=abs(b); current interiority supplies the other gap endpoint. Therefore the cubic source envelope is supported on the union of two actual-wall strips of width abs(b). H08 pays each by Cs*(abs(b)+beta)^2/r under support 1/100. Terminal interiority is dropped only after establishing the own-negative envelope.

On the retained branch, b²<=T/2 and T>=4beta² imply (abs(b)+beta)^2<=2b²+2beta²<=3T/2. Since r+t<=2r, (abs(b)+beta)^2/r<=3T/(r+t). Multiplying the cubic envelope reduces T^(-3/2) to T^(-1/2)/(r+t), with the SAME cubic mark and coefficient 6CsC0. Failed small-step and failed outer-mask branches are literally zero. N2/N3 are the missing propositional wall transports in the two tactic subproofs; the signed inequalities and numerical gain are mathematically sound.

**H17 (1481–1520).** r↦n-r is injective on range n. Early 2r<n maps into Icc((n+1)/2,n); nonnegative f permits the spare endpoint for even n. For n=2m its image is m+1,…,2m, a subset of m,…,2m; for n=2m+1 it is m+1,…,2m+1. Late n<=2r maps exactly to Icc(1,n/2) in both parities. r=0 is early when n>0, r=n is excluded, and no rank/n factor is introduced. Image inclusion/equality and injective finite-sum transport are written explicitly.

**H18 (1521–1576).** The public Gaussian ratio head has direction Psi(y)<=(4/3)*(1+x)/(1+y)*exp((x²-y²)/2)*Psi(x). At y=0 it gives a lower tail bound. For x>=16, 1+x<=exp(x²/8) yields exp(-5x²/8)<=(8/3)Psi(x). At y=3x/2 the ratio is <=1 and exponent is -5x²/8, so Psi(3x/2)<=(32/9)Psi(x)^2<=(2Psi(x))². Positivity permits sqrt(Psi(3x/2))<=2Psi(x), and exp(-x²)<=(8/3)Psi(x). Constant 8 safely pays the sum. No inaccessible rare-producer Gaussian lemma is used.

**Public proof (1577–1737).** CE,CL,CG and CR at fixed p=3 are chosen before all data; C=(CE*CG+CL)*CR+1 is positive/universal. The complete native rare head/all lets match actual beta,delta,h0, products, energy/sum, first-coordinate cubic M, D^3, positive-energy guard and weak Bad. Its marked q=3/q=1 L1 and two summed grids are exactly consumed; other outputs are merely destructured.

For each r<n, t=n-r>0 and r+t=n. H14 supplies true product disintegration and inner-integral L1. Early ranks apply H15; late ranks apply H16 (forcing r>0), and H17 performs the exact reindexing. H12 retains genuine bill L1/nonnegativity. H13 removes cap then reorders, the existing rare grids pay the two sums, H18 converts the early Gaussian factor, and nonnegative multiplication gives C delta Psi(x). No new theory-194 result, stopping condition, moment/support change or shared Probability edit is used.

## Consumed interfaces, transparent values and reuse

All 13 frozen input hashes/byte counts were independently recomputed and match. INPUT-SEAL.json binds whole-file bytes and reviewed ranges. This is consumed-interface/value inspection; unchanged qualified producer proofs are reused rather than re-reviewed or rerun.

| Frozen input | Complete consumed source coverage |
| --- | --- |
| SourceTrueEnergyStrip | 190–200 closed survival head; 463–475 unrestricted concentration head; 1237–1254 restricted strip head checked to exclude invalid large-x use |
| SourceResidualRareSuffix | 1213–1270 full exported head and every beta/delta/u/h0/H/m/vx/Ax/P/T/d/M/D/marked/unmarked/future let/output; exact q=3/q=1,p=3 |
| SourceSeparatedOvershoot | 19–64 instance and projection/local/source values; 363–369 uniform-bound head; 463–481 full measurable/L1 head |
| SourcePermutationReveal | 29–170 complete consumed domain/cutoff/live/wall/kernel/law/reorder context and values; 352–357 cutoff; 616–624 iid map; 781–788 event-kernel data |
| SourceActualIntervalProfileBudget | 19–37 instance, full intervalDerivative value and kernel head; 235–310 exact derivative and both local-negative source identifications |
| ActualIntervalProjection | 10–20 sourceRemainder/signed overshoot values; 69–76,106–113 full own-negative heads; adjacent source context through 126 for assumptions/signs |
| ProjectionOvershoot | 6–11 all four scalar values; 82–88 full own-negative head |
| BridgeIntervalImageResolved | Entire 1–51, especially 22–39 actual spatial/closed-boundary Taylor heads; old proof qualification reused |
| IntervalGaussianLocal | 11–24 complete profile/retained/negative values; 26–41 full profile bound; 54–65 projected-budget head |
| IntervalImageRevealBounds | 13–42 complete numerical scalar values and nonnegativity; no strict-interior-only Taylor substitution |
| TruncationBudget | 24 actual truncationF value and surrounding nonnegative/continuous/closed-small-region facts through 40 |
| TruncationIntegrals | 26–39 full truncationBudget value and genuine integrability head |
| ActualSignedDoubleTelescope | 27–31 complete actualDerivativeFamily/context; 303–339 unrestricted actual Brownian kernel construction; no stopped-telescope result consumed |

I also read actual interface/value slices in FinitePath, SpitzerFinite, GaussianTail, SourceIntervalCompletion, BrownianBridgeLaw, SourceActualLocalProfileBudget, BridgeDomination, BridgeUpperAffineIdentification, BridgeLowerIdentification, IntervalImageGlobalProfiles, HalfLineTaylorSegment, IntervalImageMixedTerms and IntervalSineHighTimeProfiles. Their hashes/ranges are sealed too. They fix prefix/energy/max meanings, actual physical bridge/completion law, reflection-data namespace, tail-ratio direction and law-independent numerical profile constants. This is not a new full proof qualification of those old modules.

Both complete RootB weighted-prefix frozen public heads were read solely for comparison. Even theta=0 in its CDF head retains G={r/2<=energy} and support 1/200. It cannot replace the all-q/all-energy support-1/100 H08. The related opposite-hit profile head is not consumed either. The candidate neither imports nor applies that unqualified module or its circularly weighted proofs. Its local proof G is unrelated to RootB's restricted G.

## Continuation and release

N1–N3 require authorized source-author repairs with new exact bytes; frozen statements need not change. Further compiler-discovered failures must be preserved and repaired only where affected. The designated pinned server must later run the normal target and whole-owned recursive-axiom/full-type/non-theorem-value gates. Lean's pin was read as leanprover/lean4:v4.36.0-rc1; no toolchain command was run.

This review covers every new mathematical/source unit but is not final formal qualification. Subsequent actual type/value/owner/axiom coverage and repaired source deltas remain outstanding. Do not infer actual owner counts from 21 SOURCE declarations or accept only public-name axiom coverage. No original C2/C12 closure is claimed.

The reviewer releases source/execution/inflight authority, all zero, at completion. VERDICT.json, INPUT-SEAL.json, PAYLOAD-SEAL.json and RELEASE.json record the exact payload and byte provenance. Source, freezes, old qualified inputs, accepted theory and other owners' files remain unchanged.
