# Unit279 source-to-statement proposal fidelity ledger

STATUS: PROPOSAL_ONLY. This is the author's complete proposed-statement mapping, not an independent correctness review or a kernel receipt. The exact 25 HEADs and three fixed RHS reside in PROPOSED-HEADS.json; all quantifiers there are binding. Full primary p41 and p51 have been read. Existing accepted supplier proof qualification is reused, while frozen278 remains unqualified.

| ID | Exact mathematical role | Source/supplier anchor and proposed proof route | Range and retained boundary |
|---|---|---|---|
| D01 | Actual x_B(j)=x((e j).val) | p41 §2 actual retained observations; fixed RHS directly applies the actual e | Any n/B/Ω/x/e, empty B allowed |
| D02 | r_B=lambda*r with lambda=(cardB-2)/(n-2) | p41 §2 h_B and exact278 D08 backgroundScale | Arbitrary diagonal; original ambient n retained |
| D03 | Original sqrt(n)*unordered U/original jackknife root, root=0 =>0 | p51 S1, accepted FiniteRows U and jackknife definitions | Total definition; physical claims below use n>=4 |
| T01 private | E(j)∈B | Actual subtype property | No observation equality inference |
| T02 private | j↦E(j) injective | Subtype value injectivity then Equiv injectivity | No ordering requirement |
| T03 | Fin(cardB) sum transports to true Finset B sum | Reindex through actual e and subtype sum | Empty/singleton B included |
| T04 | Erased Fin row transports to B.erase E(j) | T03 plus E(k)≠E(j) iff k≠j | Index diagonal only; repeated observations included |
| T05 | Pulled-back symmetric unordered pair = blockPairSum B H | Accepted P35 2F, T04/T03, future qualified278 T03 2F; cancel2 | Any B, arbitrary e, no order preservation, arbitrary H_ii |
| T06 | Actual scaled originalUpper=lambda*F_B | OriginalUpper strict-index definition, D01/D02, T05 | Symmetric r; any cardB |
| T07 | Actual residualU on x_B/lambda*r has original n-2 row denominator | Accepted P51 erased-row type, T04 and exact lambda cancellation | Explicit n>=4/cardB>=4, no symmetry needed |
| T08 | Actual g(x_B)+residualU=278.backgroundRow at E(j) | T07, D01, exact278 D05 RHS | Same x/g/r and original denominator |
| T09 | Actual P35 mean of pullback=278.blockMean | T03, accepted mean and exact278 D06 RHS | Empty B uses real total division |
| T10 | Each actual centered coordinate transports | T09 and accepted center RHS | No mean-zero hypothesis |
| T11 | Actual centered sum of squares=278.blockCenteredEnergy | T10, T03, exact278 D07 RHS | All zero and empty energies allowed |
| T12 | Actual background projectionW=sum_B g/sqrt(cardB) | Accepted P51 W RHS, D01, T03 | Any B, total real division |
| T13 | Actual W_B+D_B=exact278 NB | T12/T06, accepted D RHS, exact278 D10 RHS | Symmetric r, n>=4/cardB>=4, exact lambda |
| T14 | Actual centeredSq=Q0/(cardB-1) | Accepted P51 center-sum theorem, derived scaled symmetry, T08/T11 | Symmetric r, physical size>=4, Q0 may0 |
| T15 | sqrt(actual centeredSq)=exact278 s_B | T14 and exact278 D14 RHS | No s_B>0 assumption |
| T16 | Actual sqrt jackknifeSq=2 sqrt centeredSq | Accepted jackknifeSq_nonneg and P51 centeredSq RHS; compare nonnegative squares | n>=4, no symmetry, zero included; independent of278 |
| T17 | Original guarded physical statistic=(actual W+D)/sqrt centeredSq | Accepted actual U formula, sqrt(n)^2=n, T16 and zero/nonzero split | Symmetric r,n>=4; ratio theorem covers denominator0 |
| T18 | Actual background R_h=2s_B | T16/T15 on SAME x_B/g/lambda*r | Symmetric r, n>=4/cardB>=4; s_B may0 |
| T19 | Actual background physical statistic=guarded NB/s_B | T17/T13/T15; explicit ite equality decider | The ORIGINAL zero guard is preserved |
| T20 | Same actual statistic=total real quotient NB/s_B | T19 and a/0=0 | No N_B=0 inference when s_B=0 |
| T21 | If s_B=0, same actual statistic=0 | T19's exact zero branch | Only advertised branch premise, no conclusion-as-assumption |
| T22 | n>=8,n<=2cardB imply cardB>=4 | Direct natural-number arithmetic | Half-sample property is explicit input, not hidden |

All twenty-two theorem conclusions are proposed outputs. There are no proof or desired-equality fields supplied as assumptions. All Ω quantifiers are explicit Type u; finite wrappers do not introduce conditional mean0, variance1, canonicality, measurability, independence or positivity of centered energy.

The exact local order is acyclic. Only T01/T02 are private. Proposed independently freezable heads D01,D03,T01,T02,T03,T04,T12,T16,T17,T22 do not mention278; no split or implementation is authorized by this ledger. Full consumer qualification depends on exact278 definitions and block_offDiagonal_sum becoming independently reviewed/server qualified, and on a parent freeze of279.

Primary scope stays finite deterministic. p41(4)-(5) Delta/envelope perturbation are supplier scope, not a new279 result. Product-a.e.-to-all-distinct-pairs lifting, true conditional projection/recentering/variance/kernel-mean correction, tail/CDF/atoms/zero-event payments, interaction concentration, rare-block integration and unconditional PE-R/PE-L/OQ56/root conclusions remain open as detailed in the full report. No276/277 theorem body is consumed.
