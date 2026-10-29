# unit278 whole-source mathematical fidelity table

Status: AUTHOR_SOURCE_FIDELITY_CANDIDATE. This is the implementation author's semantic account of the complete frozen 33-declaration source. It is not the required independent complete SOURCE/proof review and does not report Lean elaboration or axioms. Parent-only server checks have not been run by this role.

Authoritative freeze: 4b9a16afde8d790fa7fc13a87c0758719f0248d03c5927b2bdb33fa2e5a3ace2, 19339 bytes. Candidate and exact source/proof line/byte mappings are bound by DECLARATION-ASSEMBLY.json. The module contains precisely 14 frozen definitions and 19 frozen theorems in the frozen order. No additional top-level declaration, hypothesis, import, or option was introduced.

## Definitions D01-D14

D01 identifies A with the actual complement univ\\B of the actual finite B. D02 sums strict index pairs once, with no diagonal value convention. D03 is sum_A sum_B r_ai, with its original orientation. D04 is the original full adjusted row g_i+psi_i/(N-2). D05 retains that same N-2 denominator for the within-B adjusted row. D06 is the B mean divided by M, and D07 is the literal sum of B-centered squares. D08 is lambda=(M-2)/(N-2). D09 is the original a0=mean_B b-F/[(N-1)(N-2)], using the accepted original upper-pair F. D10 is the literal source NB, including (M-2)FB/[(N-2)(M-1)] and sqrt M. D11 contains all three source Delta terms, especially real K-1 and the unmodified n-denominators. D12 and D13 are the actual finite ell and Qw. D14 is sqrt[Q0/(M-1)], with Q0 the actual B-centered b0 energy.

All fourteen frozen RHS files are copied byte-for-byte. Their candidate values require the future complete VALUE audit, not merely a TYPE check. No result is hidden in a definition field or supplied as a structure assumption.

## Theorems T01-T10: p41(4)

| ID | Original meaning and implementation |
|---|---|
| T01 | Finite complement cardinality K+M=N. The proof uses finite difference cardinality, not an asserted real cardinal relation. |
| T02 | n>=4/m>=3 imply positive d=N-2, M-2, M-1 and M; the real cast of T01 and K>=0 imply M<=N, hence lambda in [0,1]. N-1 positivity is derived in the numerator proof. |
| T03 | Restricted offdiagonal double counting gives twice the upper-triangular block sum. The implementation proves this directly with erase/indicator splitting, order trichotomy, transpose/symmetry and finite sum interchange. It introduces no new helper declaration. |
| T04 | Full pair decomposition F=FA+FB+C_AB. The proof splits full rows between the disjoint complement blocks, applies T03 to both diagonal blocks, identifies both cross orientations by symmetry, and cancels 2 from the accepted full double-counting identity. No r_ii=0 premise is needed: diagonal terms cancel via sum_erase_eq_sub. |
| T05 | Sum_B psi=2FB+C_AB from the actual full n-row sums. This is derived using the finite complement split, not assumed as an input conclusion. |
| T06 | For i in B, b_i-b0_i=sum_A r_ia/(N-2), including all zero and total-division cases. No symmetry is necessary for this identity. |
| T07 | b0_i equals g_i+sum_{B\\i}(lambda*r_ij)/(M-2), proving the exact background scaling. It never changes 1/(N-2) to 1/(M-2) without lambda. |
| T08 | Expands a0=G/M+(2FB+C_AB)/(M*(N-2))-F/[(N-1)(N-2)] using the original full rows and T05. Total-division distributive algebra is used, so this helper has no unstated denominator assumptions. |
| T09 | Proves sqrt(N/M)*NB=(sqrt N/M)[G+(M-2)FB/((N-2)(M-1))]. The proof compares nonnegative squares to establish sqrt(N/M)*sqrt M=sqrt N, using M>0, and then cancels the nonzero sqrt M. |
| T10 | Proves the complete original p41(4) identity. T01 supplies the real K=N-M; T04/T08/T09 expose all terms, and justified field simplification/ring normalization gives the frozen Delta. |

The three coefficients in T10 are exactly:
  FB: K/[(N-2)(N-1)(M-1)];
  C_AB: (K-1)/[M(N-1)(N-2)];
  FA: -1/[(N-1)(N-2)].
K-1 is the literal real expression (((anomaly B).card:real)-1). The full equality includes sqrt N outside this combination. No factor 2 is added or dropped.

## Theorems T11-T19: p41(5)

| ID | Original meaning and implementation |
|---|---|
| T11 | The square of a finite weight sum equals the diagonal square sum plus twice the strict-pair product sum. This is proved by a literal diagonal/offdiagonal split, with T03 applied only to the symmetric product matrix. |
| T12 | The source bound abs FA<=ell^2/2. Two finite triangle bounds and the envelope on strict index pairs yield abs FA<=sum_{a<b}w_aw_b. T11 retains the nonnegative diagonal squares, giving the exact half. |
| T13 | The actual uncentered row difference is at most ell*w_i/(N-2). Membership in disjoint A/B ensures distinct sample indices, so only the finite offdiagonal envelope is used. |
| T14 | Exact centered-energy identity sum(f-mean_B f)^2=sum f^2-(sum f)^2/M, derived by expanding the squares with M>0. |
| T15 | Centering contraction follows by discarding the nonnegative square divided by M in T14. |
| T16 | Coefficient-one Lipschitz bound for the two centered finite norms. Finite Cauchy-Schwarz is proved from the nonnegative double sum of (a_i b_j-a_j b_i)^2. It bounds C by sqrt A2*sqrt B2, then expands the centered-difference energy and uses T15. Comparing nonnegative squares completes reverse triangle. |
| T17 | Squares and sums the exact T13 estimate, deriving uncentered row-difference energy <=(ell/(N-2))^2*Qw. The sign conditions needed to square the estimate are established explicitly. |
| T18 | Proves sqrt(M-1)*sB=sqrt Q0 by comparing nonnegative squares with M-1>0. It never divides by Q0 or sB. |
| T19 | Combines T16, T17 and T18, then compares nonnegative squares to prove sqrt[(ell/(N-2))^2 Qw]=ell*sqrt Qw/(N-2). This is exactly the original p41(5) norm bound with coefficient 1. |

The T16 proof has local typed vectors a,b and real energies A2,B2,C; these are ordinary local proof objects, not new global declarations or stronger imported assumptions. All uses of Cauchy-Schwarz, centering and reverse triangle are proved inside the frozen proof chain.

## Quantifiers, hypotheses and degenerate data

The main numerator result uses symmetry and n>=4/card B>=3. The norm result uses only finite nonnegative weights and the finite offdiagonal envelope, in addition to n>=4/card B>=3; it does not add symmetry where unnecessary. There is no probability law or hidden measurability/canonicality/moment assumption.

When A is empty, K=0, FA=C_AB=ell=0, and K-1=-1 remains a real coefficient multiplying the zero cross sum. The same proofs apply. At K=1 the cross coefficient vanishes exactly, and the strict-pair anomaly sum is zero. No case split changes a frozen statement.

Every energy is a sum of squares. The implementation never divides by ell,Qw,Qb,Q0,sB or a centered norm. Its nonnegative-square comparisons include all zero values. B empty remains a total definitional case, but the source endpoint theorems explicitly require card B>=3.

The m=3 algebra has positive M-2=1 and M-1=2 and remains within all frozen endpoint statements. It is separate from existing P51 physical wrapper theorems whose published Lean types require sample size at least 4; no such wrapper is invoked at m=3.

The finite envelope is indexed by i!=j, not by unequal observed values. r_ii is unrestricted. Distinct sample indices may carry equal observations; no observation-space diagonal is removed.

## Actual physical and probability work still open

This source proves only finite deterministic p41(4)-(5), subject to independent SOURCE/proof acceptance and the first original parent server gate. The following work is not implemented:

1. Construct B-to-Fin m relabeling, transport symmetric unordered pair sums and means/centered squares, and identify the actual background original rows/numerator/studentizer/zero-convention statistic. T07 supplies only the finite scaled-row algebra. Existing m>=4 physical wrappers must retain that premise; later n>=8,m>=n/2 can derive it.
2. Lift the original product-a.e. envelope to the simultaneous full-measure event for finitely many distinct coordinate pairs under the actual product law. An everywhere observation-space envelope must not be substituted. If symmetry is only product-a.e., its finite lift must also be made explicit.
3. Retain the actual conditional first projection, canonical residual, variance and kernel mean for g+g'+lambda*r, including all small-mean/variance transfers.
4. Prove or consume independently qualified finite geometry for source p41(3), conditional C_AB concentration, background actual denominator lower bounds and the quantitative threshold shift p41(15).
5. Pay nonempty abnormal-block exponential weights, large K/Q blocks, background failure probabilities divided by the normal tail, K=0, compact-level and zero-denominator events.

There are no imports or dependencies on unfinished 276/277 proof bodies. Conditional freedom in an alpha parameter does not change the original unconditional PE-R requirement alpha_p=2(p-2)/(2p-1). No original-mu relative probability, PE-R, PE-L, NR, DC, full S11, OQ56 or root completion is claimed.

## Verification and handoff boundary

All body API spelling and elaboration remain unverified by this author because the activation explicitly prohibits author Lean/AX/toolchain execution or probes. Static exact-byte assembly and escape-token checks are not Lean checks. The parent must commission the required independent complete source-to-statement/proof review and then run the original complete server gate; all actual owners and all fourteen definition VALUEs must be audited using the original successful object if one is produced. No prior accepted producer or AX evidence was replayed.

No new top-level helper or interface change was needed. The author has not changed the frozen HEAD/RHS/PRE/CLOSE, any source input, proposal, accepted supplier, shared file, resource limit, option or execution wrapper. After sealing the candidate, all assigned active authority is released with sixzero and no active wait. Future corrections require an explicit same-author parent reactivation bound to exact diagnostics and source bytes.
