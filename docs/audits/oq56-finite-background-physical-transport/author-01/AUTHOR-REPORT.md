# Unit279 complete author implementation

STATUS: COMPLETE_IMPLEMENTATION_CANDIDATE_AWAITING_INDEPENDENT_REVIEW_AND_SERVER. The exact frozen module is Shao/OQ5/P41/FiniteBackgroundPhysicalTransport.lean. Source SHA256 is 91784857cbbb5930bfaae3973bb884eb1115c9a38d9ec5509b0f69fcb8f07d57, 18315 bytes/413 LF. All twenty-two theorem proof bodies are present. This author has not run Lean, a compiler, AX, any server command, environment probe, transfer, network or publication operation. sourceAccepted=false, kernelChecked=false, qualified=false.

## Exact authority and immutable data

The parent explicitly reactivated the SAME canonical author role /root/oq56_unit279_author for implementation only. Activation a21d7adbabf18ad00c580227238b4528a92d862c8db8de331f33fb695d7db9a5/14301B and all 56 input SHA/byte bindings were verified before the first author-01 write. The original proposal remains sealed and read-only. All writes are confined to drafts/oq56/unit279/author-01. No other owner, shared implementation, library snapshot, freeze or primary source was edited.

The exact parent freeze is 836a6ab88185d97129cabe68955f4b55c3dbf9dc9a6755582efb9754fbd20325/14831B. Its 25 HEADs, three fixed RHS, PRE and CLOSE are assembled without changes. The PRE's mandatory set_option autoImplicit false is retained byte for byte. No other option, new declared helper, assumption, parameter, public/private change or definition change was added. T01/T02 remain the only private source theorems.

This source contains three definitions, two private theorems and twenty public theorems. This is a count of written declarations, not a prediction of actual compiled/generated owner counts. PRE15 + HEAD159 + fixedRHS7 + PROOF229 + CLOSE3 = source413 LF. ALLHEAD, ALLPROOF and FIXED-DEFINITION-BODIES contain the exact ordered component streams. DECLARATION-ASSEMBLY.json gives every UTF-8 byte range and one-based source line range, component SHA/bytes/LF and full declaration SHA. The source reconstruction is deterministic concatenation of the frozen components and each complete proof.

## Qualified suppliers and actual interfaces

278 is now qualified at exact evidence a5f3c16017165189da76dd7691b9ff10c3200eba203541dce25fe21a017054c1/18854B, exact source 8481562684fc7a3c5455e8ab99d6f85b15f4778860fa414da93099b83b4adcb8/30148B. Its native03 and same FIRST original object audit01 returned actual0/0 and complete independent final coverage is accepted by the parent. The first original object is fbd3913b99528f0e63e8301180570ff9c7c0b95af37a4eff6509e9e52003149c. These original receipts/qualification are reused; this author neither rechecked nor recertified an old supplier proof/object.

Before implementation this role read the complete raw actual TYPE blocks for blockPairSum, backgroundRow, blockMean, blockCenteredEnergy, backgroundScale, backgroundNumerator, backgroundStudentizer, block_offDiagonal_sum and background_denominators_and_scale. The complete actual non-theorem VALUE blocks for the seven used definitions were also read, with all explicit cast/instance/let details retained. The latter denominator theorem is used in T07/T13 to obtain actual positive cardinal/ambient denominators directly from n>=4 and cardB>=3, derived from the physical cardB>=4. No unused positive-energy theorem is assumed. SUPPLIER-READ-COVERAGE.json records those exact unelided blocks by hash and source.

The same context's complete readings of accepted P51 BoundedStudentizerGeometry, P35 RowIdentity and FiniteRows sources, their used full public source TYPEs/definitions and actual originalUpper/originalRows RHS are retained. No old complete proof review or accepted producer/kernel/AX check was repeated. The P51 source file's historical candidate comment is not a new claim about its accepted qualification.

Bearing accepted types are used exactly:
P51.residualU_eq_erased_row has no size/symmetry premise; sampled_uStatistic_formula and centeredSq_eq_center_sum require global symmetry and sample size>=4; FiniteRows.jackknifeSq_nonneg requires sample size>=3; P35.offDiagonalSum_eq_two_unordered accepts every symmetric finite real matrix, including empty/singleton sizes and arbitrary diagonal. OriginalUpper is the strict-index sum, originalRows excludes equal sample indices, P51 W=sum g/sqrt n, D=originalUpper/[sqrt n*(n-1)], and centeredSq=jackknifeSq/4.

## Complete proof narrative: actual finite transport

D01 is the exact sample x_B(j)=x((e j).val), for the actual e:Fin(cardB)≃{i//i∈B}. D02 is the exact lambda*r residual, lambda=(cardB-2)/(n-2), with the original ambient n. D03 is defined from the original finite unordered-pair U and original jackknife root R, as 0 when R=0 and sqrt(n)*U/R otherwise. It is not defined by the conclusion NB/sB.

T01 uses (e j).property for membership. T02 applies Subtype.ext to equality of the original indices and then e.injective. No assertion about order or observation inequality is introduced.

T03 uses Finset.sum_bij from the Fin m univ to the actual finite B. Membership is T01; injectivity is T02; for i∈B, e.surjective applied to the actual subtype element yields a preimage j and equality of values by congrArg Subtype.val. The summand equality is reflexive. The finite bijection covers empty B automatically.

T04 applies the same sum_bij to univ.erase j and B.erase(Ej). A source member k has k≠j. If E(k)=E(j), T02 contradicts that inequality, proving target erased membership. Conversely for i∈B.erase(Ej), e.surjective supplies k with E(k)=i. If k=j then i=E(j), contradicting the actual erase hypothesis. This transports the SAME row and excludes only the SAME sample index. Equal observation values at distinct indices remain included.

T05 pulls symmetry back through e and obtains the actual erased-row double sum by T04. T03 transports the outer sum. Accepted P35 double counting identifies the pulled-back double sum with twice the pulled-back unordered sum; qualified278 block_offDiagonal_sum identifies the transported double sum with twice blockPairSum B H. Linear arithmetic cancels the real constant2. The proof does not rewrite j<k into E(j)<E(k) and never assumes e is order preserving. Arbitrary sample-index diagonals are not used.

T06 unfolds the strict-index actual originalUpper of the actual x_B/lambda*r. T05 rewrites the original unscaled unordered sum to blockPairSum B R, and finite multiplication/distribution through each strict-pair conditional factors out lambda. Conditional zeros remain zero. This identity is finite and valid for any B; symmetry is its only mathematical premise beyond data.

## Complete proof narrative: rows, mean and energy

T07 applies accepted residualU_eq_erased_row to the actual background sample/kernel. It factors lambda out of the finite erased row, transports the row by T04 and unfolds lambda. Qualified278 background_denominators_and_scale supplies n-2>0 and m-2>0 from the explicit size bounds. Field algebra cancels m-2 and leaves the ORIGINAL n-2:
residualU_m(lambda*r,x_B,j)=sum_(i∈B.erase Ej)r(x_Ej)(x_i)/(n-2).
Neither symmetry nor any law-level canonicality is needed.

T08 adds unchanged g(x_Bj) and reduces the exact backgroundRow RHS, identifying the per-coordinate adjusted row with b0(Ej). T09 unfolds the actual P35 mean and exact278 blockMean, applies T03 and commutes inverse-times-sum into total real division. T10 unfolds center and substitutes T09. T11 squares this per-coordinate centering identity and applies T03 to the squared centered function. It returns the literal exact278 blockCenteredEnergy without dividing by it.

T12 unfolds actual P51 W on x_B and applies T03, giving sum_B g/sqrt m. T13 unfolds actual D, uses T06 and T12, and unfolds exact278 backgroundNumerator/backgroundScale. Qualified278 denominator/cardinal positivity supplies nonzero n-2, m-1 and sqrt m, so field algebra proves exactly
W_B+D_B=[sum_B g+(m-2)F_B/((n-2)(m-1))]/sqrt m=NB.
The ambient n and coefficient lambda are preserved.

T14 first proves global symmetry of lambda*r by multiplying the actual r symmetry by the fixed scalar. Accepted P51.centeredSq_eq_center_sum is then applied with sample size m>=4. T08 gives an equality of the ENTIRE adjusted-row functions, so the actual center function is rewritten, then T11 transports its literal centered sum of squares. The result is actual centeredSq=Q0/(m-1), Q0 the exact backgroundRow centered energy. No empirical mean0 or positive energy is assumed. T15 unfolds exact278 backgroundStudentizer and substitutes T14 under sqrt. This immediately includes Q0=0.

## Complete proof narrative: original root and zero convention

T16 derives nonnegativity of actual jackknifeSq from accepted FiniteRows at n>=3, obtained from n>=4. Since centeredSq=jackknifeSq/4, centeredSq is nonnegative. The squares of sqrt(jackknifeSq) and 2sqrt(centeredSq) agree exactly. Both sides are nonnegative, so two applications of accepted sq_le_sq₀, one in each direction, establish equality by antisymmetry. This proof includes zero and requires no symmetry. It does not rely on a sign-ambiguous cancellation.

T17 proves the actual numerator identity sqrt(n)*U=2(W+D) from accepted P51.sampled_uStatistic_formula. In its explicit field calculation a factor sqrt(n)²/n is inserted, the rational expression is normalized with n,n-1,sqrt(n) all nonzero, and the factor becomes1 by sqrt(n)²=n. Thus no incorrect cancellation of sqrt(n) as n is used. T16 identifies the original R as 2sqrt(centeredSq). Split on sqrt(centeredSq)=0: in that branch the ORIGINAL D03 guard and total RHS quotient both give0. In the nonzero branch R≠0 follows by multiplying the nonzero root by2, then field algebra cancels the actual constant2. The full sample-space identity T=(W+D)/sqrt(centeredSq) is proved, including zero.

T18 applies T16 at the actual m/background kernel and substitutes T15, yielding original R_h=2s_B. T19 applies T17 with the derived symmetry of the SAME lambda*r, then substitutes T13/T15. Splitting on the actual s_B=0 produces the exact frozen guarded NB/s_B statement. T20 uses T19 and the same zero split to identify the total real quotient; a/0=0, not an assertion a=0. T21 specializes the advertised s_B=0 branch to physical statistic0. In particular N_B may be nonzero when s_B=0; the proof never infers N_B=0.

T22 proves the explicit half-sample size boundary by contradiction: cardB<4 implies cardB<=3, whence 2cardB<=6. Combined with n>=8 and n<=2cardB this gives the impossible natural inequality8<=6. This does not silently presume a half-sample property of an arbitrary B.

## Full source fidelity, quantifiers and boundaries

All 25 HEADs and three RHS are byte-identical to the parent freeze. All finite data are universally quantified. The observation type Ω is arbitrary Type u, with no hidden measurable-space, standard-Borel, nonempty, projection or distribution class. B is the literal Finset(Fin n), m is literally B.card, e is an actual arbitrary equivalence, and x is the given complete sample. Every physical result uses the same x_B/g/lambda*r. Global pointwise r symmetry is stated wherever the accepted physical interface needs it; row identities do not add it unnecessarily.

For the physical wrappers T07,T08,T13,T14,T15,T18,T19,T20,T21, n>=4 and cardB>=4 remain explicit. Generic T16/T17 require their explicit n>=4. Finite T03/T04/T05/T06/T09/T10/T11/T12 are valid at their unrestricted finite domains; their empty cases do not extend the physical m=4 contract to m=3. T22 requires explicit n>=8 and n<=2cardB before deriving cardB>=4.

Only the sample-index diagonal is deleted. If x_i=x_j but i≠j, the term r(x_i)(x_j)=r(a,a) remains in the erased sums and unordered pair. r(a,a) is unrestricted; no diagonal-zero or distinct-observations premise appears. Full B/empty anomaly, empty/singleton B for the algebraic helpers, zero residuals, constant adjusted rows, Q0=0, s_B=0 and NB nonzero at s_B=0 all remain covered. Empty B means no j exists in T01/T04; T09/T11 use total division/empty sums. Physical wrappers never assert their hypotheses for such B.

Exact constants and quantities are retained: lambda=(m-2)/(n-2), original residual-row n-2, D's sqrt m*(m-1), centeredSq=Q0/(m-1), actual R_h=2s_B, and sqrt m*U=2(W+D). Desired row/pair/energy/ratio identities are outputs, not caller assumptions. The only zero premise is the expressly advertised branch in T21.

Primary p41 §2 gives h_B=g+g'+lambda*r, b0, NB and s_B before formula(4); this source gives their missing actual physical Fin m realization. p41(3)'s finite optimization, (4)'s full Delta and (5)'s envelope/norm perturbation are separate qualified/supplier scope, not assumed 279 conclusions. Primary p51 S1 supplies actual W,D,s,R,T and the zero convention; its S6 warns that under truncation P_R the projection/kernel mean/variance change. These changes are not removed by deterministic relabeling.

The full source probability claims retain their original scope outside this packet. Under the initial iid symmetric measurable h=g+g'+r model, Eg=0, Eg²=1, canonical residual and product-a.e. envelope w>=1, p41 PE-R sets 2<p<=3, beta_p=E|g|^p<infinity, alpha_p=2(p-2)/(2p-1), delta_p=(p-2)/(2p), assumes E exp(tau*w^alpha_p)<infinity for tau>0, and claims error C[beta_p(1+x)^p n^(-(p-2)/2)+(1+x)^3/sqrt n] uniformly at sufficiently large n for 0<=x<=c beta_p^(-1/p)n^delta_p. Fixed-model constants may depend on p, residual second moment, tau and exponential moment, with no uniform p down to2 claim. PE-L uses only the projection second moment, the initial decomposition/canonicality/envelope and E exp(tau*w^alpha)<infinity,0<alpha<=1, with x_n→infinity and x_n=o(n^(3alpha/(8-2alpha))), to claim log P(T_n>=x_n)/(-x_n²/2)→1. Neither probabilistic claim is proved by this source.

## Open dependencies and certification limits

Product-a.e. envelope lifting to one simultaneous all-distinct-index-pairs full-measure event remains separate, including sample-selected B and repeated observations. Actual conditional law/projection g_R=g-E_Rg+lambda(a_R-theta_R), residual lambda(r-a_R-a_R'+theta_R), kernel mean2E_Rg+lambda theta_R, variance normalization and quantitative mean transfer remain separate. No Eg_R=0/variance1/canonicality assumption is silently assigned to the unmodified g/r here.

Conditional tail/CDF/closed-threshold/atoms/SZ interfaces, clipping1-to-physical comparison, small zero-denominator-event payment, interaction concentration conditioned on complete anomalous observations, lower bounds for s_B, rare-block exponential integration and large K/Q payments remain open. This source consumes no theorem body or conclusion from276 or277. PE-R/PE-L, complete OQ56 and root completion remain OPEN.

A fresh independent complete source-to-statement/proof review and parent server native/same FIRST original object all-owned TYPE/non-theorem full VALUE/transitive AX qualification are still required. The whitelist remains propext, Classical.choice, Quot.sound; this author has not measured the new compiled dependencies or actual generated-owner counts. Static text checks can establish exact assembly and forbidden-token absence, not kernel acceptance.

All 56 input bindings and all component/payload bytes are reverified at seal. LASTFINALWRITE is the unique last write and releases the author with six zero counters, no queued work and no active wait. Requested model/effort are gpt-6.1-sol/xhigh; actual backend/model/effort and input/cached-input/output/reasoning-subset counts remain null because they are not exposed. No persistent continuation is claimed after release.
