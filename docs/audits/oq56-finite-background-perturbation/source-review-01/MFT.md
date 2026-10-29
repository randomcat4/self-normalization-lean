# Unit278 independent source-to-statement fidelity table

STATUS: CORRECT at the independent mathematical SOURCE layer only. The complete reviewed source is SHA256 `29285b2347c5fcf61af5703d6d6756caf56f3364471dc376a690812ac69e0d43`, 30091 bytes/693 LF. `sourceAccepted=true`, `kernelChecked=false`, `qualified=false`. This table is the independent reviewer's mapping; the author's MFT is an input rather than its authority.

Here N=n cast to real, M=card B cast to real, A=univ\\B, K=card A cast to real, d=N-2, e=N-1, F_S=sum_(i<j in S)r_ij and C_AB=sum_A sum_B r_ai. The source itself contains all exact fully typed heads and fixed bodies; these abbreviations add no assumptions.

## Every fixed definition

| ID / source lines | Object and original meaning | Independent fidelity judgment |
|---|---|---|
| D01 / 15-17 | `anomaly B = univ \\ B` | Actual finite complement, not a caller-supplied partition. |
| D02 / 18-21 | `blockPairSum S r` | Each strict index pair i<j counted once; no diagonal convention. |
| D03 / 22-25 | `crossPairSum B r` | Exact A-to-B orientation of C_AB; no factor 2. |
| D04 / 26-29 | `adjustedRow g r i` | Full original b_i=g_i+psi_i/(N-2). |
| D05 / 30-33 | `backgroundRow B g r i` | Within-B b0_i with the same original N-2 denominator. |
| D06 / 34-36 | `blockMean B f` | Literal B mean sum_B f/M, with total real division. |
| D07 / 37-40 | `blockCenteredEnergy B f` | Literal sum_B(f_i-mean_B f)^2, not a replacement energy. |
| D08 / 41-43 | `backgroundScale B` | lambda=(M-2)/(N-2), the p41 scaled residual factor. |
| D09 / 44-48 | `backgroundAnchor B g r` | a0=mean_B b-F/[(N-1)(N-2)]; F is the accepted full unorderedPairSum. |
| D10 / 49-54 | `backgroundNumerator B g r` | Exactly [sum_B g+(M-2)F_B/((N-2)(M-1))]/sqrt M. |
| D11 / 55-63 | `numeratorShift B r` | Entire p41(4) Delta: outer sqrt N, FB coefficient K/[d e(M-1)], cross coefficient real (K-1)/[M e d], and -FA/[e d]. |
| D12 / 64-66 | `anomalyWeight B w` | ell=sum_A w. |
| D13 / 67-70 | `backgroundWeightEnergy B w` | Qw=sum_B w_i^2. |
| D14 / 71-74 | `backgroundStudentizer B g r` | sB=sqrt(Q0/(M-1)) for the actual centered b0 energy. |

Every one of these 14 RHS byte strings matches its freeze and proposal expression; exact future compiled VALUE auditing remains mandatory. There is no structure or definition that assumes T10, T12 or T19 as data.

## Every complete proof

| ID / head and proof span | Claim matched to source or exact helper | Independent proof/fidelity judgment |
|---|---|---|
| T01 / 75-81 | card A+card B=n | Uses actual finite difference cardinality; casts later are justified. |
| T02 / 82-103 | d>0, M-2>0, M-1>0, M>0 and 0<=lambda<=1 from n>=4,M>=3 | Actual cardinal bound M<=N follows from T01, not an extra assumption. |
| T03 / 104-153 | Sum of within-S erased rows =2F_S | Erase indicator, order trichotomy, transposition and symmetry prove exact double counting. No diagonal-zero premise. |
| T04 / 154-220 | F=FA+FB+C_AB | Disjoint complement split, both cross orientations and accepted full double counting match the same r and n. |
| T05 / 221-262 | sum_B psi=2FB+C_AB | Actual full n-row sums, with the retained oriented interaction. |
| T06 / 263-289 | For i in B, b_i-b0_i=sum_A r_ia/d | Exact row split; no symmetry/nonzero-denominator premise, only total-division distributivity. |
| T07 / 290-302 | b0_i=g_i+sum_(B.erase i)(lambda*r_ij)/(M-2) | Cancels only proved nonzero M-2,d. Ambient finite algebra; physical relabeling still absent. |
| T08 / 303-322 | a0=G/M+(2FB+C_AB)/(M*d)-F/(e*d) | Correct mean expansion with total division; no stronger hypothesis used. |
| T09 / 323-366 | sqrt(N/M) NB=(sqrt N/M)[G+(M-2)FB/(d(M-1))] | Nonnegative-square proof and M>0 justify actual square-root cancellation. |
| T10 / 367-389 | Complete p41(4) numerator equality | Real K=N-M, correct three coefficients and outer sqrt N; all field denominators justified. |
| T11 / 390-415 | (sum_S w)^2=sum_S w_i^2+2F_S(w_i w_j) | Exact diagonal/offdiagonal split; product symmetry established locally. |
| T12 / 416-455 | p41(5): abs FA<=ell^2/2 | Finite triangle bound and strict-pair envelope; retains nonnegative diagonal squares and exact half. |
| T13 / 456-491 | For i in B, abs(b_i-b0_i)<=ell*w_i/d | A/B disjointness gives index inequality, then triangle/envelope and positive original d. |
| T14 / 492-509 | Q_B(f)=sum_B f_i^2-(sum_B f_i)^2/M | Expanded mean with actual positive M; correct cast of the constant sum. |
| T15 / 510-516 | Q_B(f)<=sum_B f_i^2 | Drops only the nonnegative squared sum divided by M. |
| T16 / 517-587 | abs(sqrt Q_B(f)-sqrt Q_B(h))<=sqrt(sum_B(f_i-h_i)^2) | Complete finite-CS square identity, nonnegative comparisons, mean linearity and centering contraction; coefficient 1, no energy division. |
| T17 / 588-616 | sum_B(b_i-b0_i)^2<=(ell/d)^2 Qw | Sign-justified squaring of T13 and exact finite summation. |
| T18 / 617-641 | sqrt(M-1)*sB=sqrt Q0 | Compares nonnegative squares, divides only by M-1>0, includes Q0=sB=0. |
| T19 / 642-690 | p41(5): abs(sqrt Qb-sqrt(M-1)*sB)<=ell*sqrt Qw/d | T16, T17, T18 plus monotonicity/nonnegative-square factorization; exact coefficient 1. |

All 19 bodies were read completely. No private P35 contraction/pair-square proof is called. The only bearing old theorem call is the actual public P35 `offDiagonalSum_eq_two_unordered` in T04; its unrestricted symmetric-matrix type exactly matches the use. T03 has a direct new proof despite a different earlier proposal route. No frozen mathematical interface changed.

## Quantifiers, boundary coverage and scope

The numerator endpoint quantifies arbitrary finite real g and symmetric real r with n>=4 and card B>=3. The envelope endpoints quantify nonnegative finite w and abs r_ij<=w_i w_j only for i!=j. Desired identities/bounds are theorem outputs. There are no law-level measurability/moment/canonicality premises and no hidden positive-energy assumptions.

K=0/empty A, K=1, real K-1, arbitrary r_ii, repeated observation values and all zero ell/Qw/Qb/Q0/sB cases are covered by the unchanged general proofs. Empty B remains a total definitional case for the unrestricted helpers, not an asserted physical endpoint. Finite m=3 is valid; physical P51 sample-size-at-least-four requirements stay intact. No old supplier proof, kernel or AX check was rerun.

The physical Fin(card B) relabeling and pair/mean/energy transport, actual background-statistic and zero-convention identification, product-a.e.-to-finite-pair full-measure lift, conditional recentering/variance/mean transfer, interaction concentration and rareblock payments remain separate obligations. This SOURCE review does not validate all probability arguments in the p41/p51 candidate notes merely because they were read. It covers this precise deterministic packet, with no unqualified unit276/277 dependency, AE-to-pointwise shortcut, unconditional PE-R/PE-L, full OQ56 or root-completion claim.

The full report gives independently checked coefficient calculations and complete proof reasoning. SOURCE-COVERAGE.json gives the lossless component SHA/byte/line map for every declaration. Machine-evidence qualification is deferred to the parent server and the explicitly reactivated same FINAL reviewer identity.
