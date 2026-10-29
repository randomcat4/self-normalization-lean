# Unit279 author source-to-statement fidelity ledger

STATUS: COMPLETE_AUTHOR_IMPLEMENTATION_CANDIDATE; NOT an independent review or kernel receipt. Exact source 
91784857cbbb5930bfaae3973bb884eb1115c9a38d9ec5509b0f69fcb8f07d57
, 
18315
 bytes/
413
 LF. All25 HEAD/3fixedRHS/PRE/CLOSE are frozen byte-identical. All22 proof bodies are written, not compiler checked.

Primary p41 and p51 full readings are retained from the same author context; complete mathematical derivations and original probability-scope statements appear in AUTHOR-REPORT.md. The table below maps every written declaration, with current line ranges derived mechanically from the exact byte assembly.

| ID and declaration | Current HEAD / body lines | Full source and bearing interface | Complete implementation route | Preserved quantifiers and boundary |
|---|---|---|---|---|
| D01 backgroundSample | 16-18 / 19-19 | p41 §2 actual retained sample | Exact actual equivalence pullback x(Ej); fixed RHS unchanged. | Any B/Ω/e/x, empty B included. |
| D02 scaledResidual | 20-21 / 22-22 | p41 §2 h_B; qualified278 backgroundScale actual VALUE | Exact lambda*r with lambda=(m-2)/(n-2); original ambient n. | Arbitrary residual diagonal, no law/projection premise. |
| D03 physicalStatistic | 23-24 / 25-29 | p51 S1; accepted FiniteRows original U/jackknife VALUEs | Original guarded sqrt(n)*U/sqrt(jackknifeSq), using explicit equality decider. | Total definition; physical claims separately n>=4. |
| T01 background_index_mem | 30-32 / 33-34 | Actual subtype in frozen e | Use (e j).property. | Membership only, no observation-value inference. |
| T02 background_index_injective | 35-37 / 38-40 | Actual equivalence in frozen e | Subtype.ext followed by e.injective. | No order or distinct-observation premise. |
| T03 sum_background_equiv | 41-44 / 45-56 | Finite sum seam for p41 background; accepted sum_bij API | Explicit e-value bijection univ→B; membership/injectivity/surjectivity/summand all proved. | Empty/singleton B allowed. |
| T04 erased_row_background_equiv | 57-61 / 62-79 | Actual erased-row seam; accepted P51 erased index convention | Explicit e-value bijection univ.erase j→B.erase(Ej); index inequality proved in both directions. | Excludes equal indices only; equal observations remain. |
| T05 unorderedPairSum_background_equiv | 80-86 / 87-104 | P35 public 2F TYPE; qualified278 block_offDiagonal_sum actual TYPE | Transport both erased row sums, obtain equality of two double counts, cancel constant2. | Symmetric arbitrary matrix; any e/B; arbitrary diagonal; no order preservation. |
| T06 originalUpper_scaled_background | 105-112 / 113-123 | Actual originalUpper RHS; p41 F_B | Unfold strict-pair sum on same x_B/lambda*r, pull lambda through finite sums and conditionals, use T05. | Global r symmetry; any cardB. |
| T07 residualU_background_original_denominator | 124-131 / 132-146 | Accepted P51 residualU_eq_erased_row; qualified278 denominator TYPE | Apply actual erased-row formula, T04, pull lambda, prove n-2/m-2 nonzero, exact field cancellation. | Explicit n>=4/cardB>=4; no symmetry assumption. |
| T08 adjusted_row_background | 147-155 / 156-158 | p41 b0; qualified278 backgroundRow actual VALUE | Add unchanged g to T07, reduce fixed sample/row RHS. | Same g/r/x_B, original n-2. |
| T09 mean_background_equiv | 159-163 / 164-168 | Accepted P35 mean; qualified278 blockMean actual VALUE | T03 plus inverse-times-sum and total division ring identity. | No mean0; empty B allowed. |
| T10 center_background_equiv | 169-173 / 174-176 | Accepted P35 center; p41 centered background row | Unfold center and rewrite literal mean by T09. | All finite data; no positive energy. |
| T11 centered_energy_background_equiv | 177-182 / 183-186 | Qualified278 blockCenteredEnergy actual VALUE | Square exact transported center from T10, apply T03. | Includes empty/zero centered energy. |
| T12 projectionW_background | 187-191 / 192-195 | p51 actual W; p41 N_B projection term | Unfold actual projectionW on same sample; T03. | Any B with total division. |
| T13 numerator_background | 196-205 / 206-217 | p41 N_B RHS; p51 actual W+D; qualified278 actual denominator/VALUEs | T06/T12 rewrite actual numerator; derive denominator/card/sqrt positivity and normalize exact lambda coefficient. | Symmetric r, n>=4/cardB>=4, no conditional canonicality. |
| T14 centeredSq_background | 218-228 / 229-247 | p51 centeredSq_eq_center_sum full public TYPE; p41 Q0/(m-1) | Derive scaled-kernel symmetry; apply accepted center-sum formula; rewrite whole adjusted-row function by T08; T11. | Physical n>=4/cardB>=4, arbitrary zero Q0. |
| T15 sqrt_centeredSq_background | 248-256 / 257-259 | Qualified278 backgroundStudentizer actual VALUE | Unfold exact s_B, substitute T14 under sqrt. | No s_B>0, includes zero. |
| T16 jackknife_root_eq_two_sqrt_centeredSq | 260-264 / 265-286 | Accepted FiniteRows jackknifeSq_nonneg and P51 centeredSq VALUE | Both roots nonnegative; exact equality of their squares; sq_le_sq₀ in both directions. | n>=4; symmetry unnecessary; zero included. |
| T17 physicalStatistic_eq_projection_ratio | 287-293 / 294-331 | p51 S1 original T/W/D/R; accepted actual U formula TYPE | Prove sqrt(n)U=2(W+D) via sqrt(n)^2/n=1; T16; split zero root and cancel only when nonzero. | Symmetric r,n>=4; original zero guard preserved. |
| T18 jackknife_root_background | 332-341 / 342-345 | p51 original R_h=2s; p41 s_B | Apply generic T16 to SAME background sample/kernel and substitute T15. | Symmetric r,n>=4/cardB>=4; zero included. |
| T19 physicalStatistic_background_guarded | 346-356 / 357-371 | p41 T_B=N_B/s_B; p51 zero convention | T17 with derived scaled symmetry then T13/T15; explicit s_B zero/nonzero split. | Same x_B/g/lambda*r; original guarded ratio. |
| T20 physicalStatistic_background_total_ratio | 372-381 / 382-389 | Total-real-division identity for source convention | T19 plus cases on s_B=0 and a/0=0. | Never infers N_B=0 from s_B=0. |
| T21 physicalStatistic_background_zero | 390-397 / 398-401 | p51 physical zero-denominator convention | Specialize exact T19 guard under its advertised s_B=0 premise. | Only advertised branch assumption; output physical T=0. |
| T22 card_ge_four_of_half_sample | 402-404 / 405-410 | p41 later m>=n/2 physical use boundary | If cardB<=3 then n<=2cardB<=6 contradicts n>=8. | Half-sample n<=2cardB is explicit premise; no hidden property of arbitrary B. |

All finite Ω/g/r/x/B/e are universally quantified exactly as frozen. There is no extra typeclass, nonempty, mean0, variance1, canonicality, integrability, measurability, independence, positive-energy or desired-equality premise. Actual B.card replaces any separate caller-supplied m. All physical wrappers keep explicit n>=4/cardB>=4; unrestricted finite helper cases do not extend physical P51 to m=3. T22 alone derives the physical size from explicit n>=8 and n<=2cardB.

Both sample-index diagonal and repeated observation cases are retained faithfully: only i=j is omitted. Distinct indices may have equal values and then r(a,a) participates in offdiagonal sums. r(a,a) itself is unrestricted. Empty/full B, empty anomaly blocks, zero residuals, constant adjusted rows, Q0=0/s_B=0, and nonzero N_B at zero s_B are correctly preserved at the applicable statement domains.

Source constants remain lambda=(m-2)/(n-2), actual residual n-2, D denominator sqrt(m)*(m-1), centeredSq=Q0/(m-1), original R_h=2s_B and sqrt(m)*U=2(W+D). Symmetric pair transport uses actual two-sided 2F double counting, never e-order preservation.

The qualified278 source/first-object evidence is reused exactly. Actual unelided TYPEs for all nine used/bearing278 constants and full VALUEs for seven definitions were read and are bound in SUPPLIER-READ-COVERAGE.json. Existing full P51/P35/FiniteRows public source HEAD/definition coverage is reused. No old supplier full proof/producer/kernel/AX check was replayed. Current source counts are25 declarations (3defs/2private/20public); actual compiled generated-owner counts are not predicted.

This ledger covers deterministic physical transport only. Product-a.e. simultaneous finite-pair lifting, actual conditional law/projection/variance/kernel-mean correction, interaction concentration, lower s_B control, tail/CDF/atoms/zero-event payments, clipping1-to-physical process transfer, rare-block integration, unconditional PE-R/PE-L, complete OQ56 and root closure remain OPEN. No276/277 proof conclusion is consumed.

Independent complete SOURCE review and parent server native/same FIRST original object actual TYPE/VALUE/transitive AX remain mandatory. This author issues no qualification. Requested sol/xhigh; actual backend/model/effort and usage remain null when not exposed.
