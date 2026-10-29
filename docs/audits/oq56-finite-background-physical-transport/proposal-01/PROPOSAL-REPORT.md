# Unit279 proposal: actual background physical transport

STATUS: PROPOSAL_ONLY_NOT_FROZEN_NOT_IMPLEMENTED. No theorem in this packet is marked proved, independently accepted, kernel checked or qualified. The exact proposed module is `Shao/OQ5/P41/FiniteBackgroundPhysicalTransport.lean`. The deliverable is 25 complete declaration interfaces: three fixed definition RHS, twenty public theorem heads and two private theorem heads. No Lean source/proof body is supplied and no compiler, environment, server, AX or toolchain command was run.

This role was dispatched by the sole OQ56 parent after its recorded natural child release. The ACT's historical PREPARED field is superseded only by that dispatch, not by this proposal. All eleven ACT input SHA256/byte records passed before the first write, and all forty-nine indirect 278 HEAD/RHS/PRE/CLOSE records were verified before reading. They are reverified at sealing. Actual backend/model/effort/token counts are not exposed by this role's tools and remain null; the prescribed/requested model and effort are gpt-6.1-sol/xhigh.

## 1. Exact source question and scope

Primary p41 was read in full, including its original candidate status, PE-R/PE-L quantifiers, sections 2–7 and examples/exclusions. Primary p51 was read in full, S1–S8, including the actual R_h=2s, T=(W+D)/s, s=0 => T=0 convention and the conditional-background recentering warning. The scope of this proposal is the deterministic seam between p41 §2's h_B, b0, N_B, s_B and the already accepted P51/FiniteRows physical definitions. It neither certifies all mathematical arguments in those candidate notes nor supplies any probability estimate.

Fix an arbitrary natural n, an arbitrary observation type Ω, an actual finite set B ⊆ Fin n, and an arbitrary equivalence

    e : Fin B.card ≃ {i : Fin n // i ∈ B}.

Write m=card B, E(j)=(e j).val, x_B(j)=x(E(j)), G_i=g(x_i), and R_ij=r(x_i)(x_j). There is no separate caller-supplied m or equality m=card B to rewrite incorrectly. B itself remains the actual finite set. Every later function is formed from this SAME B/e/x/g/r; no surrogate observation family or newly normalized projection is introduced.

The residual factor is exactly lambda=(m-2)/(n-2), implemented by the exact frozen 278 backgroundScale definition, and r_B(a,b)=lambda*r(a,b). Thus the actual sampled background kernel is g(x_Bj)+g(x_Bk)+lambda*r(x_Bj)(x_Bk). No shift of g, scale change of g, or conditional recentering occurs in this packet.

The full physical wrappers require explicit n>=4 and m>=4 and pointwise symmetry r(a,b)=r(b,a). The residual-row identities do not need symmetry but retain those physical size hypotheses. The generic sum/index/mean/energy helpers have their own unrestricted finite scope. The 278 m=3 algebraic endpoint is retained as a supplier property only; no P51 physical conclusion at m=3 is proposed. T22 makes the future half-sample implication explicit: n>=8 and n<=2*card B imply card B>=4. It does not infer a half-sample property from an arbitrary B.

The full parent source claims are recorded here to fix the excluded probability scope. p41's initial model is iid observations, symmetric measurable h=g+g'+r with Eg=0, Eg²=1 and E[r(o,O)]=0 almost everywhere, together with a measurable w>=1 and |r(o,o')|<=w(o)w(o') for μ⊗μ-almost every pair. For 2<p<=3 it sets beta_p=E|g|^p<infinity, alpha_p=2(p-2)/(2p-1), and delta_p=(p-2)/(2p). Its PE-R candidate assumes E exp(tau*w^alpha_p)<infinity for some positive tau and claims, for sufficiently large n and uniformly over 0<=x<=c*beta_p^(-1/p)*n^delta_p,

    |P(T_n>=x)/Psi(x)-1|
      <= C*[beta_p*(1+x)^p*n^(-(p-2)/2)+(1+x)^3/sqrt n].

The constants may depend on the fixed model, residual second moment, tau, exponential moment and p; there is no uniform p down to2 claim. The same source's PE-L candidate retains the initial decomposition/canonicality/product envelope, requires only the projection second moment instead of a p>2 projection moment, and assumes E exp(tau*w^alpha)<infinity with 0<alpha<=1. For every x_n going to infinity with x_n=o(n^(3alpha/(8-2alpha))) it claims log P(T_n>=x_n)/(-x_n²/2) tends to1. These are source candidate statements, not certified consequences of279. The present packet proves none of their probabilistic premises or conclusions.

The immediate source seam in p41 §2 is the exact h_B, b0, N_B and s_B displayed before formula(4). Formula(3) additionally requires Q_b>0 and belongs to the separate finite optimization dependency; formula(4) is the complete numerator perturbation with Delta; formula(5) uses the original envelope to bound F_A and the norm perturbation. This proposal transports the finite background objects to the original physical sample. It does not take formula(3), (4) or (5) as an assumed conclusion. p51 S1 supplies the physical W/D/s/R/T definitions; S6 warns that the true conditional projection and kernel mean change and must later be paid quantitatively.

## 2. Fixed definitions and original physical convention

D01 backgroundSample has RHS x_B(j)=x((e j).val), with the actual equivalence as an explicit parameter.

D02 scaledResidual has RHS lambda*r, where lambda is backgroundScale B with the original ambient n. Its value on the observation diagonal is whatever lambda*r(a,a) is. It is not modified to zero.

D03 physicalStatistic is defined from the ORIGINAL FiniteRows objects:

    R = sqrt(FiniteRows.jackknifeSq (P51.sampledKernel n g r x));
    T = if R=0 then 0 else sqrt(n)*FiniteRows.uStatistic(P51.sampledKernel n g r x)/R.

The fixed RHS uses explicit Classical.propDecidable for the equality guard, not a new assumption or an inferred decidability parameter. The complete RHS is in PROPOSED-HEADS.json. At all valid physical sizes, T17 will identify this exact object with (P51.projectionW+P51.residualStatisticD)/sqrt(P51.centeredSq), including the zero case. This is a definition by the actual unordered-pair U and actual centered-row jackknife, not a definition by the desired background N_B/s_B conclusion.

No extra studentizer, normalized sample, structure carrying a desired equality, conclusion-as-input field, or probabilistic event is introduced. The total-real-division version in T20 is a theorem following from the explicit guard, since a/0=0 in ℝ. It does not assert that the numerator vanishes when the denominator does.

## 3. Full accepted bearing interfaces read

The entire exact accepted BoundedStudentizerGeometry.lean, RowIdentity.lean and FiniteRows.lean sources were read. Their existing qualification is reused; this role does not issue another supplier proof review or any old Lean/AX check. The complete relevant public types and definitions are:

* P51.sampledKernel n g r x i j = g(x_i)+g(x_j)+r(x_i)(x_j).
* P51.residualU n r x i = originalRows n r x i/(n-2); residualU_eq_erased_row gives the actual sum over univ.erase i without size or symmetry premises.
* P51.projectionW n g x = sum_i g(x_i)/sqrt n.
* P51.residualStatisticD n r x = originalUpper n r x/[sqrt n*(n-1)].
* P51.centeredSq n g r x = FiniteRows.jackknifeSq(sampledKernel n g r x)/4.
* P51.sampled_uStatistic_formula requires global pointwise symmetry and n>=4 and gives U=2 sum g/n + 2 originalUpper/[n(n-1)].
* P51.centeredSq_eq_center_sum has the same symmetry/size premises and gives sum_i center(g+residualU)_i²/(n-1).
* P35.mean f=(n:ℝ)^(-1)*sum f; center f i=f_i-mean f.
* P35.unorderedPairSum H=sum_i sum_j (if i<j then H_ij else 0). Its public offDiagonalSum_eq_two_unordered is for EVERY symmetric Fin n real matrix, including n=0 and 1, and has no diagonal-zero premise.
* FiniteRows.uStatistic H=(n.choose 2:ℝ)^(-1)*P35.unorderedPairSum H; rowMean H i=(n-1)^(-1)*sum_(univ.erase i) H_ij.
* FiniteRows.jackknifeSq H=[4(n-1)/(n-2)²]*sum_i(rowMean H i-uStatistic H)²; jackknifeSq_nonneg requires n>=3, no symmetry.
* The actual accepted originalUpper definition is the strict-index unordered sum; actual originalRows inserts zero for i=j by INDEX and otherwise uses r(x_i)(x_j). Their RHS were read directly as well.

Names and binder conventions in the proposed complete HEAD strings match those interfaces. No private P35 lemma is invoked. Full elaboration remains unperformed because this is proposal-only.

## 4. Exact transport route, without an ordering premise

T01 is a private membership helper from the subtype property. T02 is a private injectivity helper: subtype value equality implies subtype equality, then equivalence injectivity implies index equality. These facts never imply different observations at distinct indices.

T03 transports sum_(j:Fin m) f(Ej) to sum_(i in B) f_i. One direct proof reindexes the Fintype sum through e to the subtype B, then identifies the subtype sum with the Finset B sum. Empty B is covered; no division, symmetry, positivity, observation law or e-order property is used.

T04 transports each actual erased row. For fixed j, k≠j iff E(k)≠E(j), by T02. Membership T01 and surjectivity of e then give the exact finite bijection between univ.erase j and B.erase(Ej). A second direct route applies T03 to the indicator of i≠Ej and identifies the erased sums. Both routes exclude the same sample index ONLY.

T05 transports a symmetric unordered pair sum. It deliberately does not rewrite a predicate j<k into Ej<Ek. Let L denote the pulled-back unordered pair sum and F_B the frozen blockPairSum. Accepted P35 double counting yields

    2 L = sum_j sum_(k != j) H(Ej)(Ek).

Apply T04 to the inner sum and T03 to the outer sum. The result is sum_(i in B) sum_(l in B.erase i) H_i,l. Future qualified exact 278 block_offDiagonal_sum gives this as 2 F_B. Cancellation of the NONZERO REAL CONSTANT 2 yields L=F_B. No division by an energy or cardinality is involved. The symmetry of the pulled-back matrix follows pointwise from the supplied hsym. This proof covers arbitrary e, including non-monotone permutations, empty/singleton B, arbitrary H_ii, and repeated observation values.

T06 unfolds originalUpper and D01/D02, pulls the constant lambda through finite sums (the zero term of each strict-index conditional stays zero), and uses T05 with H_ij=r(x_i)(x_j). It concludes the exact ORIGINAL background unordered sum is lambda*blockPairSum B R. No minimum cardinality is needed for this finite identity.

This is the sole proposed use of a new 278 theorem body: block_offDiagonal_sum. The other 278 dependencies are the exact fixed definitions. This role does not cite that unqualified theorem as accepted; it records the precise supplier that a future implementation must first qualify. An alternative independent reproof of the block double count would need a separately approved/frozen helper and is not silently included.

## 5. Exact original denominator and centered energy route

T07 applies accepted P51.residualU_eq_erased_row on the SAME x_B/r_B, pulls out lambda, then applies T04. Algebra cancels m-2 from

    [(m-2)/(n-2)] * sum_(B.erase Ej) R_Ej,i / (m-2).

Both m-2 and n-2 are positive from the explicit m>=4,n>=4. The result retains the ORIGINAL n-2 denominator. No relation between g and r and no residual mean hypothesis is used.

T08 adds the unchanged g(x_Bj) and unfolds exactly 278.backgroundRow, yielding the per-coordinate actual adjusted-row identity. It is not inferred merely from similar notation.

T09 transports the finite mean by T03. P35.mean's inverse-times-sum equals 278.blockMean's sum/card via real division. This equality holds also at card B=0 under total division. T10 subtracts that same mean at the same coordinate. T11 squares and sums T10 and uses T03, obtaining the literal blockCenteredEnergy. No positive centered energy or distinct values is assumed.

T14 applies accepted P51.centeredSq_eq_center_sum at m>=4 to the actual globally symmetric scaledResidual (its symmetry is derived by multiplying hsym by the fixed lambda). Every coordinate g(x_Bj)+residualU is rewritten by T08, then T11 transports the centered energy. The conclusion is exactly

    actual P51.centeredSq = Q0/(m-1),
    Q0 = blockCenteredEnergy B (backgroundRow B G R).

The factor 4 has already been accounted for by the accepted definition centeredSq=jackknifeSq/4. T15 applies sqrt to T14 and unfolds the exact fixed 278 backgroundStudentizer: sqrt(actual centeredSq)=s_B. There is no square-root cancellation through a possibly zero Q0, and no requirement s_B>0.

T16 is a genuinely 278-independent generic physical helper. Accepted jackknifeSq_nonneg at n>=4 gives J>=0. Since centeredSq=J/4, both sqrt J and 2 sqrt(centeredSq) are nonnegative and their squares equal J. Hence sqrt J=2 sqrt(centeredSq), INCLUDING J=0. T18 combines this generic identity with T15 for the same background kernel, obtaining the ORIGINAL R_h=2s_B, rather than redefining R_h as 2s_B.

## 6. Exact numerator and ratio route

T12 unfolds the original P51 W and applies T03:

    W_B = (sum_(i in B) g(x_i))/sqrt m.

T13 unfolds the original D and uses T06, so

    W_B+D_B
      = [G_B + lambda*F_B/(m-1)]/sqrt m
      = [G_B+(m-2)*F_B/((n-2)(m-1))]/sqrt m
      = exact 278.backgroundNumerator B G R.

The last line is the FROZEN 278 RHS, not an input equality. The proposed physical wrapper states n>=4,m>=4 explicitly, so sqrt m>0, m-1>0 and n-2>0 are available if field normalization divides by them. The coefficient is lambda, not 1 and not a replacement of the ambient n by m.

T17 first applies the accepted actual U formula at n>=4. Multiplying it by sqrt n and using (sqrt n)²=n yields sqrt n*U=2*(W+D). T16 identifies the actual R_h as 2 sqrt(centeredSq). Split on this nonnegative square root being zero. In the zero branch both D03's original guard and total quotient give 0; in the nonzero branch cancel the constant 2 and the nonzero root. Thus the ratio identity is valid on the entire sample space, without assuming a small probability for zero R.

T19 substitutes T13/T15 into T17 and supplies the explicit 278 s_B=0 guard. T20 removes that guard only by total-real-division algebra. T21 specializes the exact guarded identity to s_B=0 and concludes physicalStatistic=0. It does not require, derive or pretend that N_B=0. All three endpoints refer to the same fixed B/e/x/g/lambda*r. A physical n>=4,m>=4 wrapper never consumes the m=3 278 endpoint as an unsupported physical theorem.

The final public interface therefore identifies three separately defined quantities: actual unordered-pair U, actual centered-row R_h, and p41 N_B/s_B. It does not assume the identity that it is intended to prove.

## 7. Quantifiers, boundary attacks and source fidelity

Every HEAD is complete relative only to the PRE's explicit universe u, namespaces and opened qualified supplier constants. There are no hidden section variables or typeclass assumptions. Every Ω has type Type u; no measurable-space, standard-Borel, nonempty, distribution, independence, integrability or projection class is required. Existence of x is simply part of a universally quantified function input.

The statement inputs are literal finite data, symmetry where the accepted physical interface needs it, the explicit sample size bounds, and for T21 only the advertised zero-scale branch. No desired row identity, pair identity, mean identity, nonzero energy, canonicality or probability inequality is supplied as a hypothesis.

Repeated observations are allowed. If x_i=x_j while i≠j, r(x_i)(x_j)=r(a,a) still participates in the offdiagonal sums. Only i=j is omitted. Nothing sets r(a,a)=0 or removes all equal-valued observations. All sample-index diagonal values of the finite matrix can be arbitrary because strict pair and erased-row definitions never use them.

The algebraic helpers cover empty B and singleton B. T04 with a j input is vacuous when B is empty; mean and energy use total real division and zero sums. These facts do not extend the physical theorem below m=4. Full B and empty anomaly block are included. Constant g/residual configurations, centered energy Q0=0, s_B=0, residual upper sum F_B=0 and numerator N_B nonzero with s_B=0 all remain legitimate; the physical guard gives 0 in the last case. No later probability limit is invoked to remove these samples.

The physical coefficients are exact: lambda=(m-2)/(n-2), residualU retains n-2, D_B has sqrt m*(m-1), centeredSq=Q0/(m-1), R_h=2s_B, and sqrt m*U=2(W_B+D_B). p41 formula (4)'s Delta and formula (5)'s product-envelope perturbation are not re-proved or assumed here; those belong to 278. This packet supplies the missing actual-sample identification of its NB/sB only.

The proposed names, visibility, exact order and all fixed RHS are in the two JSON artifacts. MFT.md gives a per-declaration source/fidelity ledger. There are no extra silently anticipated declarations. The acyclic order has the two private index helpers before their public consumers. A prospective implementation that needs a different helper, RHS or HEAD must return to the parent for an exact freeze change.

## 8. Supplier qualification and independent subset

The current exact 278 freeze has 33 declarations and its two bound MFT files provide SOURCE-layer independent review evidence only. Their own kernelChecked/qualified fields are false. Neither current parent metadata nor this role's reading promotes them to accepted kernel theorems. Complete implementation of D02 and all 278-consuming heads remains dependent on the parent obtaining the exact source, independent full SOURCE/final coverage, successful server native, same FIRST original object all actual TYPE/non-theorem full VALUE/transitive AX qualification, and parent freeze/activation of 279.

A genuinely independent finite/physical subset exists in principle: D01,D03,T01,T02,T03,T04,T12,T16,T17,T22. Its statements and proof outlines only use accepted P51/P35/FiniteRows plus the actual e; no 278 object appears. If the parent elects to split it, each declaration's listed local dependencies still apply. No such split, freeze or implementation is performed here. It is not a reason to assume the rest of 278, and no special prefix compilation is proposed.

All existing accepted supplier proof/kernel/AX evidence should be reused at the exact hashes. A future native/AX receipt for new 279 source cannot be issued from this proposal and must not replay old accepted producers merely to acknowledge it. No theorem or proof body from 276 or 277 is consumed in this packet.

## 9. Precise future obligations left open

1. Product-a.e. envelope lifting: from the actual original μ⊗μ almost-everywhere envelope and iid coordinate maps, derive one common full-measure event covering EVERY finite distinct INDEX pair. Pairwise sample observations need not differ in value. This event must support arbitrary sample-selected B. Neither an everywhere-on-Ω envelope nor observation-value inequality may be substituted. This is a separate probability interface, absent from all proposed heads.

2. Conditional law and genuine projection: under P_R=P(·|w<=R), lambda*r is generally not canonical, and g generally has nonzero mean and variance different from 1. p41(9)–(12)/p51 S6 require actual a_R, theta_R, g_R=g-E_Rg+lambda(a_R-theta_R), canonical residual lambda*(r-a_R-a_R'+theta_R), kernel mean 2E_Rg+lambda theta_R, and variance/standardization/mean-shift estimates. This packet neither assumes nor proves any of them.

3. Actual tail engine: apply an independently qualified conditional-background bound to the SAME actual h_B after the correct recentering/standardization and small-mean transfer. The current finite equalities do not supply an SZ/CDF theorem, atom/closed-threshold transfer, small zero-denominator probability, clipping1-to-physical process estimate or a probability law for the reindexed background.

4. Interaction and norm concentration: p41(14) requires conditioning on all actual anomalous observations, not only their envelope values, followed by canonical/bias and Bernstein estimates. p41(13)/(25) concentration and actual s_B lower bounds remain separate.

5. Original rare-block integration: p41(15)–(23) require exact event implication, threshold losses, exponential-weight integration of nonempty retained blocks, large K/Q payment and the original measure's failed-background/zero events. Unit277 finite optimization or a conditional unit276 theorem cannot supply these by naming similarity.

6. Full PE-R/PE-L and original OQ56/root completion remain OPEN. The original PE-R exponent remains alpha_p=2(p-2)/(2p-1), with 2<p<=3, finite beta_p and the stated small window; it is not replaced by arbitrary alpha>0 from a conditional engine. PE-L has its separate level-dependent truncation and log-window obligations. No result here changes those quantifiers, constants, source candidate status, attribution or open scope.

## 10. Delivery and static limit

This report supplies full mathematical routes and exact HEAD/RHS text, not completed Lean proofs. Static checks cover declaration inventory/order, forbidden implementation tokens in HEAD/RHS, no source implementation, all eleven direct and forty-nine indirect input bindings, JSON parse, and strict UTF-8/no-BOM/LF/single-final-LF bytes. They do not establish elaboration, theorem correctness or qualification.

One first local READ_ACK construction hit a PowerShell parser error due to case-insensitive duplicate JSON field keys; it failed before any writes and was corrected by distinct names. A subsequent apply_patch construction attempted duplicate delete/add operations for the same proposal JSON paths and was rejected atomically before any edits; a direct exact text rewrite corrected the proposed documents. Both were administrative text-generation failures only. No Lean/check/server request, source proof change, uncertain execution or external write occurred.

The sealed MANIFEST binds every payload. LASTFINALWRITE.json is the unique final write and releases all assigned active authority with six zero counters, no queued work and no active wait. The next action belongs to the parent: review this exact proposal, obtain qualified 278 as required, freeze exact 279 interfaces/RHS, and explicitly reactivate an author for implementation plus an independent reviewer. This role does not retain a writer or a persistent continuation.
