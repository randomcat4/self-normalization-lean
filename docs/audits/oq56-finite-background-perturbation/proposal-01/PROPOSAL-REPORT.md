# unit278 finite background perturbation: declaration and proof-design proposal

Status: PROPOSED_ONLY_NOT_FROZEN. This packet proposes 14 concrete definitions and 19 theorem heads in one cohesive deterministic module, `Shao/OQ5/P41/FiniteBackgroundPerturbation.lean`. No Lean module or theorem proof body is implemented. Parent review and exact declaration freeze must precede implementation by this same author. This is a checkable mathematical design, not an independent review, kernel receipt, qualified proof, probability theorem, or root completion.

## Authority and source intake

The exact activation is `drafts/oq56/unit278/proposal-ACTIVATION.json`, SHA256 `0d98a0d0dbfcedbc9c9609b979799e62d5501557cac52c5f8f1b14ec98e21a8b`, 5340 bytes. All nine activation input SHA256/length bindings matched before first write. Full p41 and p51 and the complete parent278 dependency note/binding were read. Supplier intake was confined to the relevant public definitions/types and finite-algebra design context recorded in READ_ACK; old proof qualification is not reopened.

The selected math-theorem role is a source-to-statement proposal author. Its general local toolchain-discovery instruction is superseded here by the explicit server-parent-only/no-probe activation. No network, SSH, Lean, Lake, toolchain discovery, compiler, AX command, upload, publication, child, Goal, schedule, or shared-file change has been performed. Only this proposal directory is writable.

The exact PRE, ordered fully typed HEAD strings, concrete definition RHS expressions, and CLOSE are in PROPOSED-HEADS.json. RHS expressions specify definitions only; there are no theorem proof bodies. Every binder is typed and every name is scoped. `autoImplicit false` is the only proposed option. Imports use accepted RowIdentity finite algebra plus Mathlib square-root and tactic support. Neither 276 nor 277, nor the probability-specific ConditionalNumerator/ConditionalStudentizer modules, is imported. The only bearing old proof API needed beyond the accepted unordered-pair definition is the public `Shao.OQ5.P35.offDiagonalSum_eq_two_unordered`; its exact public type was read. The private center-energy and pair-square lemmas are not callable dependencies. Full proposed Lean elaboration and all source/axiom gates remain for the parent server after freeze.

## Intended mathematical contract and notation

Take any natural n, finite B contained in Fin n, A=univ\\B, and real vectors g,w and a real matrix r. The definitions are total, using Lean's total real division. The main p41(4) and centered-norm conclusions require n>=4 and m=card B>=3. There is no law, moment, canonicality, measurability, rank, positivity of r, or distributional hypothesis.

For exposition put N=(n:real), M=(card B:real), K=(card A:real), d=N-2, e=N-1. T01 proves K+M=N, with casts derived from the natural cardinal identity. K-1 in numeratorShift is explicitly real subtraction `(((anomaly B).card : ℝ) - 1)`; no natural predecessor or truncated subtraction appears.

Definitions correspond exactly to source notation:

| IDs | Proposed objects | Source meaning |
|---|---|---|
| D01-D03 | anomaly, blockPairSum, crossPairSum | A, unordered F_S with i<j, C_AB=sum_A sum_B r_ai |
| D04-D05 | adjustedRow, backgroundRow | b_i=g_i+sum_{j!=i}r_ij/(N-2), b0_i=g_i+sum_{j in B,j!=i}r_ij/(N-2) |
| D06-D07 | blockMean, blockCenteredEnergy | mean on B and sum_B(f_i-mean_B f)^2 |
| D08 | backgroundScale | lambda=(M-2)/(N-2) |
| D09 | backgroundAnchor | a0=mean_B b-F/[(N-1)(N-2)], with F the accepted original unorderedPairSum |
| D10 | backgroundNumerator | NB=[sum_B g+(M-2)FB/((N-2)(M-1))]/sqrt M |
| D11 | numeratorShift | the entire exact p41(4) Delta, retaining K, K-1, C_AB, F_A and all original n-coefficients |
| D12-D13 | anomalyWeight, backgroundWeightEnergy | ell=sum_A w, Qw=sum_B w_i^2 |
| D14 | backgroundStudentizer | sB=sqrt[Q0/(M-1)], Q0=blockCenteredEnergy B b0 |

No separate structure with desired conclusions as fields or hypotheses is introduced. T10, T12 and T19 are outputs to be proved from the primitive finite definitions and explicit hypotheses. T07 is the exact scaling identity needed before any physical background wrapper is built.

## Topological proof design: exact pair and numerator group

All D01-D14 precede the theorems. The dependency graph in PROPOSED-DECLARATION-ORDER.json is acyclic and records only earlier IDs. These plans describe derivations to be implemented after freeze, not proofs already accepted.

T01, partition_card. A and B are disjoint and their union is univ by the definition of A. Finite cardinal additivity and card(Fin n)=n give card A+card B=n. In particular card B<=n. No nonempty assumption is needed.

T02, background_denominators_and_scale. Cast hn and hm into the reals. Derive N-2>0, N-1>0, M-2>0, M-1>0 and M>0; the head explicitly returns all except N-1, which follows at once from N-2>0. T01 yields M<=N. Dividing 0<=M-2<=N-2 by positive N-2 gives lambda in [0,1]. All field-simplification side conditions later come from these facts. No presumed denominator or norm lower bound is supplied by the caller.

T03, block_offDiagonal_sum. Apply the accepted public double-counting theorem to the masked symmetric ambient matrix H_ij=if (i in S and j in S) then r_ij else 0. The full offdiagonal sum of H is the stated S-row sum; its unordered upper sum is blockPairSum S r. Membership rewriting removes every term outside S. Diagonal r_ii is excluded by erase/i<j, and no condition on its value is used.

T04, unorderedPairSum_partition. For i in B, split univ.erase i as the disjoint union of B.erase i and A. For a in A, split univ.erase a as A.erase a and B. Therefore the total offdiagonal row sum is the sum of the two within-block offdiagonal sums and both oriented cross sums. T03 gives 2FA+2FB. Symmetry and finite sum interchange identify the B-to-A cross sum with C_AB, while the A-to-B cross sum is C_AB by definition. The accepted total double-counting API gives 2F. Cancel the nonzero scalar 2 to conclude F=FA+FB+C_AB. This does not require any denominator bound or a nonempty A.

T05, background_original_row_sum. Use only the B-row split just described. The B-internal contribution is 2FB by T03. The remaining sum_B sum_A r_ia is C_AB by symmetry and sum interchange. Thus sum_B psi=2FB+C_AB. This exact identity is proved as its own helper rather than treated as an input assumption.

T06, adjustedRow_sub_backgroundRow. For i in B the same disjoint split of univ.erase i shows that the difference of row sums is sum_A r_ia. Cancelling g_i and using division distributivity proves b_i-b0_i=sum_A r_ia/(N-2), without symmetry or any nonzero denominator requirement. Its head is valid even in total-division degenerate dimensions; main applications use n>=4.

T07, scaled_background_row_identity. Pull lambda outside sum over B.erase i and substitute D08. Since M-2 and N-2 are nonzero by T02,
  [lambda sum_{j in B,j!=i}r_ij]/(M-2) = sum_{j in B,j!=i}r_ij/(N-2).
Add g_i. This proves that b0 is precisely the adjusted row for the scaled residual lambda*r when the background is viewed on its own indices. It never replaces 1/(N-2) by 1/(M-2) without lambda. The head is stated ambiently for every i; only its i in B instances are used as background coordinates.

T08, backgroundAnchor_formula. Expand D09, D06 and D04; distribute the B-sum over g and residual rows, pull out division by N-2 and M, and apply T05. This gives
  a0=G/M+(2FB+C_AB)/(M*d)-F/(e*d), G=sum_B g.
Only field identities valid for total division are needed here, so no artificial positivity premises appear in this head.

T09, backgroundNumerator_sqrt_scaling. From M>0 and N>=0, sqrt(N/M)=sqrt N/sqrt M, sqrt M>0 and (sqrt M)^2=M. Hence
  sqrt(N/M) NB = (sqrt N/M)[G+(M-2)FB/(d(M-1))].
This handles the two square-root factors explicitly; it is not a merely formal cancellation of sqrt M. No arbitrary branch choice is introduced.

T10, background_numerator_perturbation. Substitute T08 and T04 into sqrt N*a0, and T09 for the proposed background term. The G coefficient cancels. Derive K+M=N from T01. The remaining three exact coefficients are
  FB: 2/(M*d)-1/(e*d)-(M-2)/(M*d*(M-1))
      =1/(d*(M-1))-1/(e*d)=K/(d*e*(M-1));
  C_AB: 1/(M*d)-1/(e*d)=(e-M)/(M*e*d)=(K-1)/(M*e*d);
  FA: -1/(e*d).
Field simplification using M,d,e,M-1 nonzero followed by ring normalization proves the exact equality in the HEAD. This derivation exposes all terms; no desired coefficient identity is a hypothesis. Multiplying the displayed residual combination by sqrt N is exactly D11, with no factor 2 added or discarded.

## Topological proof design: finite envelope and coefficient-one norm group

The finite envelope premise is exactly
  for every i,j:Fin n with i!=j, abs(r_ij)<=w_i*w_j,
and hw is w_i>=0 at those finite coordinates. It is not an observation-space pointwise envelope. Symmetry is used in the numerator group but is unnecessary in T12, T13, T17 or T19.

T11, block_pair_product_identity. Expand (sum_S w)^2 as the full S-by-S product sum. Split each inner sum into its diagonal term and S.erase i. The diagonal contribution is sum_S w_i^2. Apply T03 to the symmetric product matrix w_i*w_j to identify the offdiagonal contribution with twice its unordered sum. No sign hypothesis is needed.

T12, anomaly_pair_envelope_bound. The absolute value of the finite upper-triangular sum is at most the sum of the absolute values of its terms. For each strict pair i<j in A, use i!=j and henv. Summing gives abs FA<=blockPairSum A (w_i*w_j). T11 rewrites twice the latter as ell^2-sum_A w_i^2. The discarded diagonal-square sum is nonnegative, so abs FA<=ell^2/2. This retains the original sharp half and proves it without assuming r_ii=0. Empty A is covered by empty sums.

T13, adjustedRow_sub_backgroundRow_bound. Apply T06. For i in B and a in A, disjointness gives i!=a. The triangle inequality and henv give abs(sum_A r_ia)<=sum_A w_i*w_a=w_i*ell. Since N-2>0, divide by the same original N-2 and use commutativity to obtain the exact HEAD. This is an uncentered row-difference estimate with coefficient one.

T14, blockCenteredEnergy_variance. With M>0 from hB, expand every (f_i-mean_B f)^2. The sum of f is M*mean_B f, so the expansion is sum_B f_i^2-(sum_B f_i)^2/M. All uses of division by M are justified by hB. No positivity assumption on f or on its energy is present.

T15, block_centering_contraction. In T14 the subtracted term is nonnegative, because M>0 and a square is nonnegative. Therefore energy of the centered vector is at most its uncentered squared norm. This is the contraction of the orthogonal centering projection in finite real coordinates.

T16, block_centered_norm_lipschitz. This is proved from finite algebra, not assumed as a norm axiom or imported from a private supplier lemma. Put a_i=f_i-mean_B f, b_i=h_i-mean_B h, A2=sum_B a_i^2, B2=sum_B b_i^2, C=sum_B a_i*b_i. Finite Cauchy-Schwarz follows by expanding the nonnegative double sum
  sum_{i,j in B}(a_i*b_j-a_j*b_i)^2=2(A2*B2-C^2).
Consequently C<=sqrt(A2)*sqrt(B2): both energies are nonnegative; square the nonnegative quantities abs C and sqrt(A2)*sqrt(B2), use sqrt-square identities, and apply the real squared-order comparison. This route includes A2=0 or B2=0 with no division.

Linearity of blockMean, by finite sum and division distributivity, implies that centering f-h has coordinates a_i-b_i. Its energy is A2+B2-2C. Therefore
  (sqrt A2-sqrt B2)^2
    =A2+B2-2sqrt(A2)*sqrt(B2)
    <=A2+B2-2C
    =blockCenteredEnergy B (f-h).
T15 bounds the last quantity by sum_B(f_i-h_i)^2. Use nonnegativity of the target square root and abs of the difference, and its square identity, to deduce the stated absolute-value bound. This is reverse triangle followed by centering contraction, with coefficient one. It is not the coarser two-triangle bound.

T17, row_difference_energy_bound. T13 gives abs delta_i<=(ell/d)*w_i for each i in B, with ell>=0, d>0 and w_i>=0. Squaring this nonnegative comparison, summing over B and pulling out (ell/d)^2 gives exactly (ell/d)^2 Qw. Qw is a sum of squares and may be zero.

T18, backgroundStudentizer_sqrt_identity. M-1>0 from hm. Q0 is a finite sum of squares, hence nonnegative. Square-root division gives sB=sqrt Q0/sqrt(M-1). Multiply by the positive sqrt(M-1) to obtain the HEAD. Q0=0 is included; no division by Q0 or sB occurs.

T19, background_centered_norm_perturbation. Rewrite sqrt(M-1)*sB as sqrt Q0 using T18. Apply T16 to f=adjustedRow g r and h=backgroundRow B g r, with card B>0 derived from hm. Apply monotonicity of sqrt to T17. Since ell/d>=0 and Qw>=0,
  sqrt[(ell/d)^2 Qw]=(ell/d)*sqrt Qw=ell*sqrt Qw/d.
Combining these statements is precisely the p41(5) norm inequality in the HEAD. It assumes no positive Qb, Q0, Qw, ell, or sB and introduces no extra factor 2.

## Boundary and fidelity audit before parent freeze

1. A empty / k=0. Then B=univ, ell=C_AB=FA=0 and K=0. D11 still contains real K-1=-1, multiplied by zero cross sum. Delta=0, lambda=1, b=b0, and both sides of the norm bound are zero. No natural predecessor is used.
2. k=1. FA is zero by an empty strict-pair set and the C_AB coefficient K-1 is exactly zero. The remaining FB coefficient is K/[d*e*(M-1)]. This cancellation is real algebra, not a special-case hypothesis.
3. m=3. Every finite theorem requiring hm is valid at M=3: M-2=1 and M-1=2. The existing P51 physical wrapper requires sample size at least 4, so this proposal does not invoke or extend it at m=3.
4. ell=0, Qw=0, Qb=0, Q0=0 and sB=0. The proof route uses square roots of nonnegative sums and never divides by these quantities. Any forced zero row-difference consequences follow from the envelope and T17, without an extra branch assumption.
5. B empty. Definitions remain total and denominator-free identities T01/T03-T06/T08/T11 remain meaningful. The p41 numerator and centered norm theorems require m>=3, so no theorem about a physical empty background is asserted.
6. Diagonal data. All pair/row residual sums are offdiagonal in the sample indices. r_ii can be arbitrary. Distinct indices may carry equal observations, so the condition is never weakened to unequal observation values or an assumption r(o,o)=0.
7. General g. The numerator equality is finite algebra for any real g_i; Eg=0 and Eg^2=1 play no role here. They cannot be silently inferred or used to invoke a tail engine.
8. Finite restrictions. There is no global everywhere product envelope premise on an observation space, no Hilbert/bilinear residual representation, and no independence hypothesis in the deterministic group.
9. No supplied conclusion. Pair decomposition, sum_B psi, numerator coefficients, sharp pair bound, contraction, reverse triangle and final norm bound are all proposed theorem outputs with explicit proof designs. None is required as an input premise.
10. Static versus kernel. Exact textual HEAD checks and mathematical design do not establish Lean elaboration, proof success, transitive axioms or original-source acceptance. All such statuses remain false/not run.

## Unimplemented next obligations and exact consumer boundary

A. Finite background relabeling remains a separate source-bound result. Construct an actual equivalence between Fin m and the subtype of indices in B. Transport g, the scaled residual lambda*r, within-B unordered pair sums, B means and centered square sums. For an arbitrary equivalence, unordered i<j sums need symmetry/double-counting or an order-preserving enumeration; they cannot be reindexed as ordered sums without justification. Identify the actual relabeled original rows with b0 using T07, and prove physical projectionW+residualStatisticD=NB and physical sqrt(centeredSq)=sB. Existing P51 formulas may be consumed at m>=4 only. In the later n>=8, m>=n/2 regime, m>=4 is derived. The m=3 finite output here does not automatically extend the old physical wrapper.

B. Product-a.e. envelope to actual samples remains separate. Starting only from abs r(o,o')<=w(o)w(o') for mu.prod mu-a.e. pair, use that the two distinct coordinate projections under the finite iid product law have joint law mu.prod mu. Pull the pair event back for each i!=j and intersect the finitely many full-measure events. On this common event the deterministic henv holds simultaneously for all pairs and hence for any sample-selected B. If symmetry is only product-a.e., lift it as well; diagonal index symmetry is reflexive. Observations may coincide and the observation-space diagonal must not be removed. This proposal does not add an everywhere envelope to bypass that obligation.

C. The raw background kernel g+g'+lambda*r under the conditional law must retain its actual first projection, canonical residual, variance and nonzero kernel mean from p41(9)-(12) / p51 S6. Relabeling alone does not center the model or pay its mean/variance shifts. No unqualified 276/277 body is used and no conditional tail conclusion is presumed.

D. Source p41(3) extremal finite geometry and p41(4)-(5) are distinct ingredients. This packet targets (4)-(5) only and has no dependency on unfinished 277 proof bodies. It does not claim that the finite background numerator alone is a physical Fin m statistic until A is proved.

E. Source p41(14) conditional C_AB concentration remains necessary, conditioning on full abnormal observations rather than their weights alone. Background F_B/Qw/row energy and actual sB lower-bound events must be combined with this finite perturbation to derive the quantitative implication (15), with all k,m,n factors and threshold signs. None of those probability/concentration conclusions is claimed here.

F. Source p41(16)-(21) still requires conditional tails, Mills ratio transfer, nonempty abnormal-block exponential-weight integration, large K and Q payments, and comparison of background failure probabilities to the normal tail. K=0 and zero-denominator/compact-level transfers must be kept with their actual paid events. A finite numerator identity does not pay any of these terms.

G. The unconditional PE-R branch uses exactly alpha_p=2(p-2)/(2p-1), with its identities in p41(19). A conditional background statement allowing arbitrary alpha>0, including proposed/unfinished unit276, does not imply an unconditional relative tail for arbitrary alpha. No original mu-tail, PE-R, PE-L, NR, DC, full S11, OQ56 or root completion is asserted.

## Freeze recommendation and next authorized action

The entire 33-declaration bundle is mathematically cohesive and proposal-ready for parent interface/source review. T10, T12 and T19 are the source endpoints, with noncircular helpers proving the needed algebra and coefficient-one norm bound. The parent should inspect these exact HEADs, proof plans and remaining obligations, then decide the precise freeze; this author does not freeze them. If the parent chooses a smaller implementation milestone, T01-T10 form a substantive numerator group and T11-T19 the exact next finite-norm group, without changing definitions or silently claiming the other half complete.

After seal all active authority of this proposal author is released; there is no active wait, queued check or uncertain operation. Any same-author implementation requires a parent follow-up carrying the exact frozen bundle. Actual backend/model/effort and input/cached-input/output/reasoning-subset usage are unexposed and recorded null, separately from the requested gpt-6.1-sol/xhigh configuration.


