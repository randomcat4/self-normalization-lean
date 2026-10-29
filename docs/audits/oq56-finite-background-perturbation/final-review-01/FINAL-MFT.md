# Unit278 actual TYPE/VALUE semantic fidelity

STATUS: CORRECT_AND_QUALIFIED for source8481562684fc7a3c5455e8ab99d6f85b15f4778860fa414da93099b83b4adcb8 and first objectfbd3913b99528f0e63e8301180570ff9c7c0b95af37a4eff6509e9e52003149c. All63 full TYPEs/756LF and14 full VALUEs/165LF were literally read and semantically reviewed.

## Every concrete definition VALUE

| Frozen ID / actual VALUE lines | Literal compiled value compared to fixed source RHS | Result |
|---|---|---|
| D01 anomaly /26-28 | Finset univ difference B using actual Fin n equality decision; no caller partition or modified universe. | MATCH |
| D02 blockPairSum /160-165 | Nested S sums with ite(i<j,r_ij,0). Each strict index pair counted once. | MATCH |
| D03 crossPairSum /109-112 | Sum over actual anomaly A, then B, of r_a,i in that orientation. | MATCH |
| D04 adjustedRow /135-145 | g_i plus sum_(univ.erase i)r_ij divided by real n-2. The numeric support theorem elaborates numeral2 only. | MATCH |
| D05 backgroundRow /85-94 | g_i plus sum_(B.erase i)r_ij divided by the same real n-2. | MATCH |
| D06 blockMean /21-25 | sum_B f divided by real card B, total real division. | MATCH |
| D07 blockCenteredEnergy /146-153 | Sum_B(f_i-blockMean B f)^2, exponent the natural numeral2. | MATCH |
| D08 backgroundScale /10-20 | (real card B-2)/(real n-2); no natural truncated subtraction. | MATCH |
| D09 backgroundAnchor /95-108 | Actual blockMean B of full adjustedRow minus accepted full unorderedPairSum r/[(real n-1)(real n-2)]. | MATCH |
| D10 backgroundNumerator /113-134 | [sum_B g+(M-2)blockPairSum B r/((N-2)(M-1))]/sqrt M, retaining all parentheses, casts and coefficients. | MATCH |
| D11 numeratorShift /29-80 | Outer sqrt N times KFB/[(N-2)(N-1)(M-1)]+(K-1)C_AB/[M(N-1)(N-2)]-FA/[(N-1)(N-2)]. K and M are cardinal casts; K-1 is explicit real subtraction. | MATCH |
| D12 anomalyWeight /81-84 | Sum_A w over the actual complement. | MATCH |
| D13 backgroundWeightEnergy /154-159 | Sum_B w_i^2. | MATCH |
| D14 backgroundStudentizer /1-9 | sqrt(blockCenteredEnergy B(backgroundRow B g r)/(real card B-1)). | MATCH |

Every definition's complete compiled TYPE has the same implicit n and explicit finite-data binders as its frozen HEAD. No desired conclusion is stored as a field or supplied as a hypothesis. Full VALUE reading, rather than type compatibility or name membership alone, establishes these object matches.

## Every source theorem actual full TYPE

| ID | Complete actual TYPE compared with freeze/source | Result |
|---|---|---|
| T01 partition_card | Actual complement cardinality plus B cardinality equals n, in Nat. | MATCH |
| T02 background_denominators_and_scale | Only n>=4/cardB>=3; real n-2,M-2,M-1,M positive and0<=lambda<=1 in the frozen conjunction order. | MATCH |
| T03 block_offDiagonal_sum | Arbitrary symmetric r; exact S erased-row sum=2 strict-pair sum. | MATCH |
| T04 unorderedPairSum_partition | Arbitrary symmetric r; original full F=FA+FB+C_AB. | MATCH |
| T05 background_original_row_sum | Arbitrary symmetric r; actual B full-row sum=2FB+C_AB. | MATCH |
| T06 adjustedRow_sub_backgroundRow | Only i in B; full row minus background row=sum_A r_i,a/(N-2), without symmetry or extra denominator premise. | MATCH |
| T07 scaled_background_row_identity | n>=4/cardB>=3, every ambient i; b0 equals g plus within-B lambda*r sum/(M-2). | MATCH |
| T08 backgroundAnchor_formula | Only symmetric r; exact original anchor expansion with G/M,(2FB+C)/(M(N-2)),F/[(N-1)(N-2)]. | MATCH |
| T09 backgroundNumerator_sqrt_scaling | n>=4/cardB>=3; exact sqrt(N/M) NB=(sqrt N/M)[G+(M-2)FB/((N-2)(M-1))]. | MATCH |
| T10 background_numerator_perturbation | Symmetry,n>=4/cardB>=3 only; sqrt N*a0=sqrt(N/M)*NB+actual Delta. | MATCH |
| T11 block_pair_product_identity | Any finite real w; square of sum equals square sum plus twice the strict-pair product sum. | MATCH |
| T12 anomaly_pair_envelope_bound | Nonnegative w and envelope only for index i!=j; exact abs FA<=ell^2/2, without symmetry. | MATCH |
| T13 adjustedRow_sub_backgroundRow_bound | n>=4, nonnegative finite w, offdiagonal envelope, i in B; bound ell*w_i/(N-2), without cardB or symmetry premise. | MATCH |
| T14 blockCenteredEnergy_variance | Only cardB>0; centered energy=sum squares-(sum f)^2/M. | MATCH |
| T15 block_centering_contraction | Only cardB>0; centered energy<=raw square sum. | MATCH |
| T16 block_centered_norm_lipschitz | Only cardB>0; absolute difference of centered square roots<=sqrt(sum(f-h)^2), exact coefficient1. | MATCH |
| T17 row_difference_energy_bound | n>=4/nonnegative w/offdiagonal envelope; raw row-difference square sum<=(ell/(N-2))^2 Qw. | MATCH |
| T18 backgroundStudentizer_sqrt_identity | Only cardB>=3; sqrt(M-1)sB=sqrt actual Q0, no positive-energy premise. | MATCH |
| T19 background_centered_norm_perturbation | n>=4/cardB>=3/nonnegative w/offdiagonal envelope; exact abs(sqrt Qb-sqrt(M-1)sB)<=ell sqrt Qw/(N-2). | MATCH |

All30 generated theorem full TYPEs were also literally read:25 generic simplifier support types,4 exact definition equation types and1 numeral-instance proof. They are part of actual63-owner coverage and recursive AX auditing, not new source mathematical claims. FINAL-COVERAGE provides all names, exact per-owner TYPE/VALUE indices and source/generated classification.

Actual statement/value fidelity preserves realKminus1 at empty A, same-n denominators/lambda, unrestricted diagonals, repeated observation values, sharp half, coefficient1 and all zero-energy cases without division by an energy. Finite m=3 algebra remains separate from physical m>=4 interfaces. These facts do not supply any missing physical transport, product-AE lift, conditional model payment, concentration, rareblock or unconditional probability result.
