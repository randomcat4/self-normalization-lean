STATUS: CORRECT

Independent mathematical source-to-statement/proof review of the exact frozen theory subject, unit 193. This verdict is mathematical only. No Lean execution, kernel receipt, axiom qualification, upload, Git operation, API publication, server execution, or delegation was performed.

Reviewer: /root/bad_interval_negative_budget_theory_review.
Requested model/effort: gpt-6.1-sol / xhigh, fresh context.
Actual model/effort: unobservable from available runtime metadata; no model substitution was requested or performed. Input, cached-input, output, and reasoning-subset token counts are unobservable and recorded as null in VERDICT.json.
Proof author: C12 parent. The reviewer did not edit the proof, subject, original sources, library, or another owner's files. The assigned review directory is the only write scope.

The frozen subject is SHA256 9079374a50b47f280348733ef51d2a6d9fd0775eb68050076debac8aa69b3d82 (6522 bytes). The complete proof reviewed is SHA256 9a2567b45875f70addbcf0e3e522d137fccf635f35ade760f312b73679c2c8b4 (12764 bytes, 269 lines). All 13 frozen consumed-source inputs match their recorded SHA256 and byte counts. The immutable original supplement has SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd. Its five specified ranges, 123 source lines in total, reproduce the supplied complete excerpt text exactly, with only line-ending normalization for that textual comparison. The excerpt's own byte hash is 9f0df75032e6b0619ee39f86dc3fb2ded37fe84adb36084124147e6fadb61e51.

The result proved is exactly a bounded residual iid, actual Brownian interval, bad-displacement negative separated-overshoot bill with an arbitrary measurable cap dominated by the actual h0 cutoff. It includes a newly derived large-x actual-energy strip. It does not close C2/C12, any second-wall or full separated bill, all retained terms, the terminal corridor, or unbounded-law truncation/assembly.

1. Frozen statement and original-source fidelity

The assumptions rho probability, EX=0, EX²=1, |X|<=B a.e., x>=16, B<=sqrt(n)/(100x), and delta(1+x)^3<=exp(-3x²) are preserved. The proof neither strengthens the moment assumptions nor imposes a stopping-time property on the arbitrary cap. Boundedness supplies the third and fourth moments actually used. The inequalities beta>=1 and B>=1 in proof lines 9-11 follow from the probability-law Lp comparison and EX²<=B²; these are consequences, not new assumptions.

The original source's projection identity/budget (supplement 4323-4341), actual-wall strip construction (4867-4903), actual cutoff event (4978-4999), marked rare grids (5046-5065), and difficult negative interval term (5564-5588) agree with the frozen target and the candidate's uses. In particular, original lines 5569-5579 explicitly retain the negative interval term and use early marked3 and late strip-weighted marked1/n estimates. The candidate supplies this particular numerical bill. It does not misidentify a finite algebraic identity as a root theorem.

The selected strip support factor is eta=1/100, within the original bound; the selected x>=16 and weak residual inequality are exactly within the consumed rare producer's actual exported head. The frozen weak Bad is 3x sqrt(T)/2<=|d|. No strict-event estimate is substituted for this weak event.

2. New large-x strip: proof lines 16-107

The clipped quadratic coordinate c_B(t)^2 is globally 2B-Lipschitz: projection onto [-B,B] is 1-Lipschitz and both projected values have modulus at most B. Taking a maximum with k/2 is 1-Lipschitz, and square-root rationalization on [k/2,infinity) gives the stated B sqrt(2/k) coordinate Lipschitz bound. Therefore F_q increases by at least half the coordinate increase when xB sqrt(2/k)<=1/2. The argument applies across both clipping endpoints and the floor, without differentiability assumptions. F_q and H are Borel measurable by continuity.

The normalization in lines 32-44 is exact. For Y=X/sqrt(k), k EY²=1, EY=0, and
R_k(0)=k E[Y² min(|Y|,1)]<=beta/sqrt(k).
For H(y)=2 F_q(sqrt(k)y)/sqrt(k), the map t -> H(update(v,i,t))-t is monotone on the entire real line. The closed interval has length 2v/sqrt(k). The exported iid_strong_monotonicity_concentration head (SourceTrueEnergyStrip lines 463-475) has no x restriction or small-budget requirement and gives 2 times that length plus 80R, exactly (4v+80beta)/sqrt(k). Closed interval endpoints and atoms are covered.

On the a.e. support set, clipping is the identity. If Q_k>=k/2 then q+Q_k>=k/2, so the floor is also the identity. Independence and EX²=1 give Var(Q_k)=k Var(X²)<=k EX⁴<=k B beta. Chebyshev bounds P(Q_k<k/2) by 4B beta/k. Under B<=sqrt(k), the combined bound is (4v+84beta)/sqrt(k)<=84(v+beta)/sqrt(k). It is uniform over every q>=0 and every real interval location. The exceptional probability does not depend on the conditioned second block.

For late ranks, B>=1 and the support restriction imply n>=10000x². Thus r>=n/2>=2, and k=floor(r/2), ell=r-k satisfy k,ell>=r/3>=n/6. Both slope and B<=sqrt(k) requirements hold with the constants stated in lines 69-70. There is no unhandled small-integer case.

On the upper strip event, every reversed partial sum within the final ell prefix coordinates is S_r-S_(r-j)>=-v. Upon fixing that entire block, the first block has its original independent product law, q+q_2 is nonnegative and fixed, and the terminal gap indeed places
S_k-x sqrt(q+q_2+Q_k) in [-s-v,-s].
The uniformly bounded conditional first-block probability may therefore be multiplied by the second-block survival probability. This is a valid Fubini/product argument even though the original wall is random.

The survival call in lines 93-96 uses -X/sqrt(ell), the level v/sqrt(ell), and its genuine budget <=beta/sqrt(ell). The exact exported original_closed_survival_uniform head (SourceTrueEnergyStrip lines 190-200) gives C_OS(v+beta)/sqrt(ell). Reversal preserves the iid law, and sqrt(k ell)>=r/3 gives C_strip=252 C_OS. Sign reversal gives the lower strip without symmetry of rho. Uniformity in deterministic q justifies q=T after a complete independent suffix is fixed.

The public iid_true_energy_closed_strip head really requires x<=1 (SourceTrueEnergyStrip lines 1237-1254); the candidate does not apply it at x>=16. Only the unrestricted monotonicity concentration and closed survival heads are used. This was specifically checked.

3. Actual cubic negative envelope: proof lines 109-146

The source's live branch has w>0, T>0, |y|<w and |z|<w. Its small-energy guard is exactly b²<=T/2. If that guard fails, or neither wall is crossed, localSeparatedOvershoot is literally zero (SourceSeparatedOvershoot lines 22-42); all outer inactive cases are zero by lines 55-64.

At an upper crossing, u=w-y satisfies 0<u<=b, u²<=T/2 and y+u=w. The exact sourceRemainder_small_bound head (BridgeIntervalImageResolved lines 31-39) admits the closed new-position condition |y+u|<=w, so projection onto the boundary is in range. intervalIncrementProfile_bounds (IntervalGaussianLocal lines 26-41) gives profile<=2. With the numerical nonnegative compensatedProfileConstant this yields the stated projected cubic bound. At a lower crossing, the same image theorem applies directly to the actual projected increment -u=-w-y; its absolute value is u=w+y and y-u=-w. The sign and drift reversal in the lower projection theorem is therefore valid.

The own-negative theorem is the correct producer: ActualIntervalProjection lines 69-76 and 106-113 bound the projected remainder's absolute value plus the negative part of the actual corresponding projected overshoot by K u b²<=K|b|³. Its hypotheses include terminal interiority, which supplies z-y<u above and y-z<u below; those hypotheses have not been discarded before applying it. Nonnegativity of actual completion and actual differentiability hold for the Brownian bridge law. The image theorem's spatial derivative head is BridgeIntervalImageResolved lines 22-29.

The source and derivative identification is literal. actualDerivativeFamily Q .interval is intervalDerivative Q (ActualSignedDoubleTelescope lines 27-31). The latter is the guarded derivative of eventCompletionKernel .interval Q (SourceActualIntervalProfileBudget lines 21-25). On positive T, sourceIntervalCompletion is that same actual completion. The transparent hDer/hNeg construction in that module, lines 253-310, identifies the upper/lower localSeparatedOvershoot formulas with upperOvershoot/lowerOvershoot including the lower sign. These identities have no x<=1 dependency; the containing old consumer's restricted probability estimate is not used. The actual Brownian kernel data and measurability with constant 4 are realized in ActualSignedDoubleTelescope lines 303-339 without an x<=1 assumption.

Thus (4) is valid with a numerical C_0>0, chosen larger than 2 compensatedProfileConstant if needed. Its support includes strict prefix survival and one positive wall gap <=|b|. At equality y+b=+/-w the projection increment is b, so the separated overshoot is zero. If b=0 there is no crossing from an interior live point. Exterior endpoints, dead prefixes, zero total energy, T<=0, r>=n, a reached cap, and large-energy steps all have literal zero source separated term. Dropping terminal interiority only after obtaining a nonnegative upper bound is sound.

4. Cap removal and genuine L1: proof lines 148-173

energy_cutoff_data (SourcePermutationReveal lines 352-357) gives r<energyCutoff(a,h0,sigma) => r<n and h0<=T. As beta>=1, h0=4beta²>0. On r<nu, the constant-cap-n term is exactly the same local source value. On r>=nu, the capped value is zero. Hence its negative part is pointwise bounded by the constant-cap-n negative part times 1_(T>=h0). This removes all arbitrary cap dependence before invoking the iid reorder law. No cap stopping-rank property is needed.

The dominating source value, actual wall, remaining sum/energy, live predicate and marked label all depend only on the reordered complete path at a fixed rank. Total sum and total energy are permutation invariant. The actual iid_randomPermutation_map_eq_pi head (SourcePermutationReveal lines 616-624) therefore permits the pushforward used in lines 158-163. This is not an assertion about independence of a random wall or an iid stopping boundary.

The kernel bound is 4, so source_parts_uniform_bound (SourceSeparatedOvershoot lines 363-369) gives the exact global absolute bound 16(1+n), for every cap and every path when x>0. The source_parts_measurable_integrable head, lines 463-481, needs only per-permutation cap measurability and kernel data, not a stopping property. The finite discrete permutation space makes that sufficient for joint measurability. Bad is Borel because d and T are finite polynomial/continuous observables (and the real square root is Borel). Each masked negative part and their finite sum is genuinely integrable under the probability reveal law.

The cubic conditional bounds are used only on T>=h0>0. On the a.e. support set, |b|<=B, |d|<=nB and T<=nB², so their magnitudes have finite deterministic bounds for fixed n,B,h0. Define them as zero off the displayed positive-energy guard. Thus the subsequent Fubini and expectation comparisons have genuine finite L1 justification, rather than relying on an arbitrary value of a divergent integral.

5. Early marked grid and rank mapping: proof lines 175-199

At deterministic rank r, t=n-r and the complete suffix is (X_(r+1),...,X_n), including b=X_(r+1). Its T and d are precisely the source remainingEnergy and remainingSum. In particular, the mark |b|³ is the first-coordinate cubic mark and the bad event uses that same complete suffix. Removing nonnegative prefix activity/crossing support from the upper bound is legitimate.

The exact exported rare producer (SourceResidualRareSuffix lines 1213-1270) chooses K=2^64, has x>=16 and the weak residual inequality <=exp(-3x²), and for p=3 exports an integrable marked function with q=3 and the sum over Icc((n+1)/2,n). Its definitions at lines 1230-1242 agree with the displayed early integrand: h0=4beta², denominator sqrt(T)^3 and drift power 3. All its law assumptions are frozen assumptions; no support-vs-x restriction is additionally demanded by this grid.

For n=2m, early ranks r=0,...,m-1 map injectively to t=2m,...,m+1, a subset of [m,2m]. For n=2m+1, early r=0,...,m map to t=2m+1,...,m+1, exactly the relevant upper range. The use of a subset of ceil(n/2),...,n is sound in both cases, since all integrands are nonnegative. There is no duplicated or missing actual rank and no extra n multiplier. The bound C_early delta A_x follows.

6. Late conditional grid: proof lines 201-235

For 2r>=n and r<n, fixing the complete suffix fixes b,T,d,D and Bad. The prefix remains a product of r rho coordinates. Its actual wall is w=x sqrt(Q_r+T), with true random prefix energy still present. Source interval survival implies each signed closed survival used by the derived strip; the crossing condition implies one positive gap <=|b|. Terminal endpoint interiority is safely dropped for the upper bound. The conditional crossing probability is thus at most 2 C_strip (|b|+beta)^2/r; no label is resampled or deleted.

The conditional cubic envelope retains both T>=h0 and b²<=T/2. On this set beta²<=T/4, so
(|b|+beta)^2<=2b²+2beta²<=3T/2
and r>=n/2 implies (|b|+beta)^2/r<=3T/n.
This explains exactly the inverse-power gain from T^(-3/2) to T^(-1/2)/n, and yields the factor 6 C_strip C_0/n. Removing the small-energy indicator afterward enlarges a nonnegative integrand.

The same exact rare producer exports (1/n) times the sum of marked q=1,p=3 over Icc(1,n/2), with the same complete-suffix first-coordinate mark. For n=2m, late r=m,...,2m-1 map to t=m,...,1. For n=2m+1, late r=m+1,...,2m map to t=m,...,1. This covers precisely the late rank range. The retained h0 guard implies T>0, matching the producer's extra explicit positivity guard. Thus the late bound C_late delta Psi(x) is justified.

7. Gaussian comparison, constants and scope: proof lines 237-269

For x>=16, integrate the normal density on [x,x+1/x] to obtain
Psi(x)>=exp(-3/2) exp(-x²/2)/(sqrt(2pi)x),
since (x+1/x)²<=x²+3. The elementary upper tail integral bound at 3x/2 gives Psi(3x/2)<=exp(-9x²/8). Consequently
A_x/Psi(x)<=sqrt(2pi)exp(3/2)x(exp(-x²/16)+exp(-x²/2)).
The inequality exp(x²/16)>=x²/16>=x and monotonicity of the exponential show each final x-weighted exponential is <=1. Equation (8) is valid and supplies a numerical comparison without an inaccessible private lemma.

C_OS is universal, compensatedProfileConstant is a numerical scalar (IntervalImageRevealBounds lines 13-22 and its nonnegativity lines 24-42), and the rare constant is selected for the fixed natural drift power p=3 before the law/n/x. Therefore C_strip and C_negative can be chosen strictly positive and universal before all data, as the frozen quantifier order requires. Brownian representation, cap and terminal endpoint do not enter these constants.

The integrand is nonnegative by its definition; the proven upper bounds supply the frozen finite numerical bill. Weak Bad includes the strict Bad used by unit 192. The explicit exclusions at proof lines 267-269 are correct.

Consumed-input coverage (all exact hash bindings are in INPUT-SEAL.json)

- SourceTrueEnergyStrip: full consumed exported heads at 190-200, 463-475; explicit non-use of restricted public consumer at 1237-1254. Unchanged producer proofs are reused, not re-reviewed or rerun.
- SourceResidualRareSuffix: complete consumed exported head and all marked/T/d/M/D transparent lets at 1213-1270; fixed p=3, q=3/q=1 summed grids. Unchanged producer proof reused.
- SourceSeparatedOvershoot: projection/local/source transparent definitions at 22-64; full uniform bound at 363-369 and full measurability/integrability head at 463-481.
- SourcePermutationReveal: remaining sum/energy, cutoff, domains, actual wall/alive, kernels, reveal law and reorder definitions at 29-170; cutoff head at 352-357; reorder-law head at 616-624.
- SourceActualIntervalProfileBudget: intervalDerivative at 21-25; full actual kernel-data head at 27-37; source-completion/derivative and signed local-negative identification at 235-310. The restricted x<=1 old expectation consumer at 79-115 is not applied.
- ActualIntervalProjection: actual sourceRemainder and signed overshoot definitions at 10-20; complete signed own-negative heads at 69-76, 106-113, with hypothesis use checked.
- ProjectionOvershoot: projected factors/overshoot at 6-11; complete own-negative head at 82-88, including F>=0, K>=0 and e<u.
- BridgeIntervalImageResolved: complete actual spatial derivative and projected small-step heads at 22-39, including the closed boundary condition.
- IntervalGaussianLocal: increment profile and negative overshoot definitions at 11-24; complete profile bounds at 26-41 and projected cubic head at 54-65.
- IntervalImageRevealBounds: universal scalar definitions and nonnegativity at 13-42; the candidate consumes the resolved actual Taylor theorem, not the strict interior-only small-step head at 152-158.
- TruncationBudget: actual truncationF value at 24, evenness and its small-region formula at 29-40.
- TruncationIntegrals: actual truncationBudget value at 26-27 and integrability head at 29-39; these justify the normalized genuine budget calculation.
- ActualSignedDoubleTelescope: actualDerivativeFamily value at 27-31 and the unrestricted actual Brownian kernel-data construction at 303-339. No stopped-telescope conclusion requiring a stopping cap is used here.

Critical gaps: none found in the complete exact candidate.

Attribution supplement, received after the mathematical pass: the parent-provided occupancy-and-attribution.md was read completely, together with the complete 167-line prior RootB draft record-endpoint-and-overshoot-proxies-next-proof.md, SHA256 766582010822e936715649b72eea55dd709261e78888360f51fb341081fbbb7e. Its Section 7 already sketches early q3 / late q1 numerical payment for a cubic wall-gap proxy, and its lines 157-158 explicitly leave physical source-value/endpoint/status domination unpaid; lines 166-167 disclaim independent/formal qualification. That prior draft is attribution/provenance only, not an assumed theorem or an additional mathematical premise here. This verdict independently covers the present exact actual own-negative projection mapping and all-Q large-x conditional strip. No novelty or original-C2-completion credit is claimed, and no prior proxy proof pass is inherited. The subject and proof hashes remain unchanged.

Evidence boundary: this is a complete independent mathematical review of the newly frozen theory candidate with exact consumed-interface/source-value coverage. Previously qualified unchanged producer proofs are taken as the established project inputs authorized for reuse. This review does not create or replace any server kernel/owned-transitive-axiom receipt, does not formally implement the new candidate, and does not certify an original root theorem. Existing accepted source/proof/check evidence remains unchanged.

