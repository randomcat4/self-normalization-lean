# Unit278 independent complete SOURCE review

STATUS: CORRECT

The complete frozen source is accepted at the independent mathematical SOURCE-review layer. I found no concrete mathematical gap, source-to-statement mismatch, hidden hypothesis, circular input conclusion, or misuse of the bearing accepted public interface. This is not a Lean elaboration/kernel result. `sourceAccepted=true`, `kernelChecked=false`, `qualified=false`; actual-owner full TYPEs, all definition/generated non-theorem VALUEs, recursive axioms and the machine-evidence FINAL review remain pending.

## Exact object and independence

The authoritative candidate is `C:/game/shao lean/drafts/oq56/unit278/author-01/FiniteBackgroundPerturbation.lean`, SHA256 `29285b2347c5fcf61af5703d6d6756caf56f3364471dc376a690812ac69e0d43`, 30091 bytes, 693 LF. The declaration freeze is SHA256 `4b9a16afde8d790fa7fc13a87c0758719f0248d03c5927b2bdb33fa2e5a3ace2`. The review activation is SHA256 `ba38d44bbdfa8dc02d15c74e7b45ab92bc77ae6cb0fd95a5d9fdea03e3e05a95`, 36041 bytes, with 152 bound inputs. All 152 input SHA256/byte pairs were independently verified before the first report write. They are reverified for the final seal.

I am the fresh independent reviewer `/root/oq56_unit278_review`, separate from `/root/oq56_unit278_author`. No mathematical source, fixed component, proposal, freeze, supplier, prior report, shared implementation or owner file was edited. My only write scope is this new `source-review-01` directory. Requested model/effort are gpt-6.1-sol/xhigh; actual backend/model/effort and token-category counters are not exposed and are recorded null, without inferring subscription use.

The full 693-line candidate was read, including every complete definition and proof. This includes all 33 exact frozen heads (118 LF), all 19 complete proof components (522 LF), all 14 fixed definition bodies (36 LF), PRE (14 LF) and CLOSE (3 LF). This is complete reading, not proof sampling or reliance on the author's MFT. Full p41 (SHA256 `8c1a8a2fb9273716002fbd9c6745c54ca4a41e5b94d8db748f68bd8405fe774a`) and p51 (SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`) were read, as were the full proposal report, declaration order, parent dependency note and author MFT/implementation account. The exact heads/RHS were additionally compared to the proposal and freeze.

Existing supplier proof qualification is reused at its exact bound bytes. I read the relevant supplier definitions and complete public theorem types, especially P35 `unorderedPairSum` and `offDiagonalSum_eq_two_unordered`, without commissioning or claiming a new proof review of the old suppliers. ConditionalNumerator/ConditionalStudentizer are contextual interfaces, not imported or invoked by the new module. The P51 physical interfaces retain their actual sample-size-at-least-four hypotheses.

## Independent source and byte integrity

I independently reconstructed `PRE + each HEAD/body in frozen order + CLOSE` in memory and compared it byte-for-byte with the authoritative source. Every recorded component byte offset, length and line interval agrees with the source. All 33 author HEADs match the freeze and normalized proposal strings; all 14 RHS components match the fixed frozen bodies and proposal expressions. `ALLHEAD.txt`, `ALLPROOF.txt` and `FIXED-DEFINITION-BODIES.txt` exactly equal their reconstructed streams. Counts above were derived from the actual bytes and declaration map, not copied into claims about compiled owners.

The source contains exactly 14 top-level definitions and 19 top-level theorems, the frozen PRE imports, and only the frozen `set_option autoImplicit false`. There is no extra helper declaration, new premise, option or import. Strict UTF-8 decoding succeeds; there is no BOM or CR and exactly one final LF. Static inspection finds no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide` token. These are text-integrity observations, not kernel evidence.

The archived static001 incident is preserved and not promoted into a Lean result. Its unsealed 690-LF/29913-byte candidate SHA256 `5877e357e07b4dc95d442f9860cc206c8da0ea7488455647e63d4b6b1bd41a39` is not this review target. The original broad text guard rejected two solved refine metavariable tokens in T02; the authoritative final proof uses explicit named facts. Neither old nor final candidate has a kernel pass in this review.

## Source fidelity and exact intended objects

Write N=n cast to real, M=card B cast to real, A=univ\\B and K=card A cast to real; put d=N-2 and e=N-1. These are explanatory abbreviations, not additional assumptions. D01 is the actual complement, D02 is a strict-upper index-pair sum, and D03 is the oriented sum over A then B. D04 and D05 both retain the original d denominator. D06/D07 are the literal B mean and centered square sum. D08 is (M-2)/d. D09 is the p41 anchor mean_B(b)-F/(ed), with the original accepted unordered-pair F. D10 is exactly `[G+(M-2)F_B/(d(M-1))]/sqrt M`. D11 retains all three original Delta terms and the literal real expression K-1. D12/D13 are ell and Qw. D14 is sqrt(Q0/(M-1)). All are concrete fixed expressions, not structures whose fields assume desired conclusions.

These definitions faithfully encode only the finite part of p41 section 2, formulas (4)-(5), with p51 S1/S6 clarifying physical and conditional-model boundaries. General real g and arbitrary real r are allowed; symmetry is supplied exactly where the numerator double counting needs it. The norm estimates use only nonnegative finite weights and the offdiagonal-index envelope. Neither positive-semidefinite/bilinear structure nor a probability law, moment, canonicality, measurability or a law-level everywhere envelope is inserted.

## Complete proof review: pair algebra and numerator

T01, lines 75-81: `card_sdiff_add_card_eq_card` applies to the actual inclusion B subset univ. The cast-free conclusion is card A+card B=n. No partition identity is assumed from the caller.

T02, lines 82-103: casts of n>=4 and card B>=3 establish d>0, M-2>0, M-1>0 and M>0. Casting T01 with K>=0 gives M<=N. Dividing M-2<=N-2 by the positive d proves lambda<=1; its nonnegativity follows from the same positive denominators. The nested conjunction projections used later select precisely d, M-2, M-1 and M. N-1 positivity is derived separately from d>0 in T10.

T03, lines 104-153: for i in S, the erased row becomes the S sum with the equality case set to zero. Order trichotomy partitions each unequal pair into i<j and j<i. Swapping the two finite sums and applying symmetry identifies the lower triangle with the upper triangle. Diagonal values are excluded; there is no r_ii=0 premise. The proof is direct, differing harmlessly from the earlier masked-matrix proof plan without changing the declaration.

T04, lines 154-220: A and B are shown disjoint with union univ. The full row at an A index splits into A.erase i plus B, and the full row at a B index splits into A plus B.erase i. The `sum_erase_eq_sub` steps subtract each actual diagonal term from both sides; they do not silently set it to zero. The B-to-A cross sum equals the declared A-to-B cross sum by symmetry and sum interchange. T03 supplies 2F_A and 2F_B, and the accepted public P35 theorem supplies 2F for the same symmetric r and same full erased rows. Cancelling the scalar 2 yields F=F_A+F_B+C_AB, with no nonemptiness or denominator assumption.

T05, lines 221-262: the same B-row split yields sum_B psi=2F_B+C_AB. The internal sum is T03 and the remaining orientation is converted by symmetry. This is a proved intermediate conclusion rather than a supplied hypothesis.

T06, lines 263-289: for i in B, the same complement split gives b_i-b0_i=sum_A r_ia/d after cancellation of g_i. It needs no symmetry. Its ring manipulations distribute multiplication by d inverse, so they remain valid under total division even if d=0; no field cancellation occurs in this helper.

T07, lines 290-302: T02 supplies nonzero M-2 and d. Pulling lambda outside the sum and cancelling these denominators proves b0_i=g_i+sum_(B.erase i)(lambda*r_ij)/(M-2), for every ambient i. For physical background use one still restricts to i in B and constructs the relabeling. Crucially this result retains lambda; it never replaces d by M-2 alone.

T08, lines 303-322: expansion of the actual B sum of D04, finite sum/division distributivity and T05 give

    a0 = G/M + (2F_B+C_AB)/(M*d) - F/(e*d).

Rewriting inverse products and ring identities is valid for total real division as well, including empty B. The helper has not secretly used the endpoint positivity premises.

T09, lines 323-366: M>0 and N>0 are obtained explicitly from T02. The proof first establishes `(sqrt(N/M)*sqrt M)^2=(sqrt N)^2` and nonnegativity of both sides, then deduces equality of the square roots. Nonzero sqrt M is justified by M>0. The subsequent cancellation gives `sqrt(N/M)*(v/sqrt M)=(sqrt N/M)*v` for arbitrary v; applying it to D10 is the exact scaling required. This is not an unjustified square-root or zero-factor cancellation.

T10, lines 367-389: all four necessary field denominators d,e,M-1,M are proved nonzero. T01 supplies the real identity K=N-M. T08, T09 and T04 expose the original G,F_A,F_B,C_AB terms; field simplification and ring normalization establish the stated equality. Independently subtracting the background numerator gives these coefficients inside the outer sqrt N:

    F_B: 2/(M*d)-1/(e*d)-(M-2)/(M*d*(M-1))
         = 1/(d*(M-1))-1/(e*d) = K/(d*e*(M-1));
    C_AB: 1/(M*d)-1/(e*d) = (e-M)/(M*e*d)
           = (K-1)/(M*e*d);
    F_A: -1/(e*d).

These are precisely D11 and p41(4), with no lost factor 2 or sqrt factor. K-1 is real subtraction, not a natural predecessor. No coefficient identity, background conclusion, unit276 or unit277 theorem is assumed.

## Complete proof review: envelope and centered norm

T11, lines 390-415: expanding the full square of a finite sum gives the S-by-S product sum. Each row is split into its genuine diagonal square and erased row. The product matrix is symmetric by commutativity, so T03 gives the exact identity ell_S^2=sum_S w_i^2+2 sum_(i<j in S)w_i w_j. No sign hypothesis is needed for this algebra.

T12, lines 416-455: two finite-sum absolute-value inequalities bound the anomaly strict-pair sum by its product-weight pair sum. Every use of the envelope follows from a strict index inequality, hence from distinct indices. T11 leaves the diagonal square sum nonnegative, giving |F_A|<=ell^2/2. The original coefficient one half is retained. The weight nonnegativity premise is compatible with the intended envelope; the final diagonal-square discard itself requires only square nonnegativity. No r diagonal value enters.

T13, lines 456-491: T06 exposes the actual row difference. If a is in A and i in B, disjointness proves a!=i. The finite triangle inequality and the envelope give the numerator bound sum_A w_i*w_a=ell*w_i. Division is by the original positive d from n>=4. No symmetry or unmentioned independence is used.

T14, lines 492-509: with M>0, expanding `(f_i-mean_B f)^2` gives sum f_i^2-2 mean_B(f) sum f_i+M mean_B(f)^2. Substitution of mean_B(f)=sum f_i/M and justified cancellation proves sum f_i^2-(sum f_i)^2/M. The finite constant-sum cast has the correct cardinal coefficient M.

T15, lines 510-516: the removed square divided by positive M is nonnegative, so T14 proves centering contraction. It does not require a positive energy.

T16, lines 517-587: all local vectors, energies and scalar products are explicitly typed. Let a=P_B f, b=P_B h, A2=sum a_i^2, B2=sum b_i^2 and C=sum a_i b_i. The proof expands the complete nonnegative double sum

    sum_(i,j in B)(a_i*b_j-a_j*b_i)^2 = 2*A2*B2-2*C^2,

giving C^2<=A2*B2. A2,B2>=0 and comparisons of nonnegative squares yield |C|<=sqrt A2*sqrt B2, hence C<=that product. There is no division by A2, B2, C or either square root. Linearity of the actual mean gives P_B(f-h)=a-b and its energy A2+B2-2C. Thus `(sqrt A2-sqrt B2)^2` is at most that energy; T15 bounds it by sum_B(f_i-h_i)^2. Comparing the squares of nonnegative absolute value and nonnegative target square root proves the required coefficient-one bound. The conclusion is reverse triangle followed by centering contraction, not a coarser pair of triangle inequalities.

T17, lines 588-616: ell>=0, w_i>=0 and d>0 justify squaring T13's absolute-value comparison. Summing the resulting inequalities and taking the constant `(ell/d)^2` outside gives exactly `(ell/d)^2*Qw`. No division by ell or Qw occurs, and Qw may be zero.

T18, lines 617-641: M-1>0 and Q0>=0 justify the square-root quotient. The two products whose squares are compared are nonnegative; cancellation uses only the nonzero M-1. This proves sqrt(M-1)*sB=sqrt Q0, including Q0=sB=0.

T19, lines 642-690: card B>0 follows from card B>=3. T18 rewrites the background norm; T16 bounds the absolute difference by the raw row-difference norm. T17 and square-root monotonicity bound it by sqrt[(ell/d)^2*Qw]. ell/d>=0 and Qw>=0 permit a nonnegative-square comparison with ell*sqrt(Qw)/d. This is exactly the second inequality of p41(5), with coefficient 1 and the original n-2 denominator. Desired conclusions are outputs, not premises.

## Boundary and hypothesis audit

All following boundary conclusions are by inspection of the complete general arguments, not numerical testing or extra checked theorems.

* Empty A and K=0: B=univ, cross and anomaly pair sums and ell vanish; real K-1=-1 multiplies the zero cross sum. Delta vanishes, lambda=1 and b=b0. No natural truncated subtraction is present.
* K=1: the anomaly strict-pair sum is empty, and real K-1=0 removes the cross coefficient. The same endpoint proof applies.
* Empty B: total definitions and T01/T03-T06/T08/T11 remain meaningful. Endpoint T10/T19 explicitly require M>=3 and do not claim an empty physical background.
* m=3: M-2=1 and M-1=2 are positive, so the finite endpoints genuinely include this case. Existing P51 physical wrappers still require m>=4; the present module neither invokes them at m=3 nor establishes their extension.
* Zero ell, Qw, Qb, Q0 or sB: no proof divides by any of these quantities. T16 uses a square-identity CS proof that includes zero centered energies. T17/T19 obtain any forced zero row difference from the envelope and sum inequalities themselves. No positive-energy hypothesis is smuggled in from p41(3), which is a different result.
* Arbitrary r_ii: erasures and strict pairs exclude it; row-split subtraction cancels the actual diagonal. Symmetry is a general symmetric-matrix hypothesis and does not impose diagonal zero.
* Repeated observation values: all distinctness is of finite sample indices i!=j. No step assumes different indices give different observations or removes the observation-space diagonal.
* General g and signed residuals: no projection mean/variance or residual positivity is used. The finite statements are valid before any probabilistic centering.

## Remaining scope and parent gate

The accepted SOURCE scope is the complete deterministic p41(4)-(5) packet and its stated helpers. It is not a probability theorem, a physical-background wrapper, the p41(3) extremal bound, or original OQ56/root closure.

An actual equivalence from Fin(card B) to B's index subtype, transport of symmetric unordered pair sums, means and centered squares, and identification of the actual original background numerator/studentizer remain separate work. An arbitrary reindexing does not preserve the strict-order pair expression without symmetry/double counting or a proved ordered enumeration. Physical zero-denominator statistic identification also remains separate.

The original envelope is product-a.e.; it still needs a simultaneous finite full-measure lift for each pair of distinct coordinate projections under the actual product law, including coincident observed values. The present pointwise finite envelope is the correct deterministic input to that future lift, not a proof of it. The raw conditional background must retain its actual first projection, canonical residual, variance and kernel mean, with the p41(9)-(12)/p51 S6 mean and variance payments. Conditional interaction concentration, actual lower denominator events, p41(15) threshold loss, p41(16)-(21) rareblock integration/large-K/large-Q payments, compact levels and paid zero-denominator transfer remain open. Arbitrary conditional alpha does not replace the original unconditional PE-R alpha_p.

No unit276/277 proof body or unqualified probability engine is imported. No old accepted producer, proof check or leaf axiom check was replayed. This role ran no Lean, Lake, AX, compiler, toolchain probe, prefix, SSH/network, upload, Git/API publication, child, Goal, schedule or resource command. Only local read/hash/byte-integrity operations and this report writing were performed.

The parent may now perform the first complete exact-source server native gate. Only a successful original object followed by all actual-owned full TYPEs, all non-theorem/definition VALUEs and recursive axiom coverage can support machine qualification. Definition VALUE auditing is mandatory for all fourteen fixed definitions and any actual generated non-theorem owner. This review does not infer those counts from source declarations. FINAL review is retained under the same dormant reviewer identity and requires explicit reactivation with actual machine evidence. Until then qualified/kernelChecked remain false.
