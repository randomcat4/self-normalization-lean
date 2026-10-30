# Unit281 mathematical fidelity trace

STATUS: PROPOSAL_ONLY; no declaration frozen by this author; no proof or kernel result.

## Fixed meaning

The mask is a fixed set of good positions in the original n-coordinate product law, and its complement contains the anomalous positions. The background enumeration is the actual arbitrary equivalence e. The law is the genuine normalized restriction cond P E_B only when P E_B≠0. The unnormalized restricted pushforward covers all masks. The physical statistic is the actual U/jackknife statistic of the λ-scaled residual and the original background row numerator/Studentizer with zero guard, not a renamed projection surrogate.

## Declaration-by-declaration contract

| ID | Complete proposed object or result | Inputs and scope retained | Direct bearing |
|---|---|---|---|
| D01 | fixedMaskEvent | Any Ω,n,C,B; true mixed coordinate membership | p41 actual good/anomaly mask |
| D02 | backgroundClosedTail | Actual279 physicalStatistic on Fin B.card, scaledResidual B r, closed z≤T | Background h_B=g+g′+λr physical upper event |
| D03 | originalBackgroundClosedTail | Original n-row backgroundNumerator/Studentizer; explicit zero guard | Original p41 N_B/s_B event |
| T01 | measurableSet_fixedMaskEvent | Measurable C; all cardinalities | Genuine conditioning event |
| T02 | fixedMask_measure | Probability μ; measurable C; all B | Exact product mask mass, no combinatorial multiplicity |
| T03 | fixedMask_real | Same; d=μ.real C | Exact d^m(1-d)^K weight |
| T04 | fixedMask_real_boundary | All n/B; d=0/1 and B empty/univ | K=0, m=0, n=0 and 0^0 not discarded |
| T05 | measurable_backgroundSample | Arbitrary Ω and e | Actual retained Ω-valued sample |
| T06 | fixedMask_backgroundSample_cond_map | Actual P E_B≠0; generic C; arbitrary e; no m>0 premise | Public full-n generic conditional joint producer then actual retained projection |
| T07 | fixedMask_backgroundSample_restrict_map | Every mask, including P E_B=0 | Original unnormalized mask-weight law; zero branch without normalization |
| T08 | measurable_scaledResidual | Only measurable uncurry r | Constant λ scaling measurable |
| T09 | measurable_physicalStatistic | Measurable g/r; pointwise r symmetry; dimension≥4 | Public global physical measurability plus exact279 projection bridge |
| T10 | measurableSet_backgroundClosedTail | Same physical assumptions, m≥4; every real z | Closed physical event measurable |
| T11 | originalBackgroundClosedTail_eq_preimage | Pointwise symmetry and m≥4; arbitrary e | Exact279 guarded bridge; derive n≥4 from m≤n |
| T12 | measurableSet_originalBackgroundClosedTail | Measurable g/r, same physical assumptions | Measurable actual original-row tail |
| T13 | fixedMask_physical_closed_tail_cond | Positive actual full mask; same original physical assumptions; every z | Actual conditional tail probability equals product-background physical tail |
| T14 | fixedMask_physical_closed_tail_intersection | Every actual mask; same physical assumptions; every z | Original P intersection equals exact mask weight times background tail |
| T15 | cutoff_fixedMask_physical_closed_tail_transport | C={w≤R}, measurable w; same physical assumptions; every R,z | Original cutoff specialization with exact law and conditional/weighted event transport |

All objects and conclusions above are written literally in the individual HEAD/RHS files. This table abbreviates only explanations, never the frozen-file candidates.

## Supplier fidelity

1. ConditionalIID.lean was read in full. indep_cond_joint_map_eq_pi has arbitrary measurable observation type, finite independent coordinate family and a nonzero joint event. T06 first instantiates it on the full Fin n evaluation family. No ℝ-only retained corollary supplies the new generic law.
2. The full six279 actual TYPEs and full three definition VALUEs were read and matched exact metadata; frozen public HEAD/RHS bindings were verified. backgroundSample uses e and the actual source coordinates; scaledResidual fixes λ=(m-2)/(n-2); physicalStatistic uses the actual U and jackknife square.
3. physicalStatistic_eq_projection_ratio has explicit pointwise r symmetry and dimension≥4. physicalStatistic_background_guarded has both n≥4 and m≥4. T09/T11 retain these requirements, deriving only the redundant n bound from cardinality. The generic mask law has no symmetry.
4. physical_clipped_globally_measurable supplies only measurability here. Its guarded physical first component agrees with the exact279 total projection ratio at denominator0. Its arbitrary auxiliary C0,rho,y are instantiated by0 without introducing any estimate.
5. The bound Pi.lean source supplies exact finite-product rectangles and measure-preserving evaluations. Generic independence/precomposition methods are supported by exact accepted local call-site contexts, with the absence of a newly printed full imported TYPE explicitly recorded. Nothing was fetched or probed.
6. The original activation's pending279 FINAL state is preserved as history. Two later exact read-only bindings establish qualified279 without changing source/FIRSTO. The later qualification does not activate281 implementation.
7. Qualified276 is a future quantitative consumer, not imported or invoked by proposed281. Its true conditional model/projection/variance is not reconstructed. No unqualified280 proof is consumed.

## Degenerate and atomic cases

| Case | Proposed contract | Why no extra premise is introduced |
|---|---|---|
| n=0 | E_B is univ; B=empty=univ; mask weight1; map law on the empty path | Generic T02-T07 retain n=0 |
| m=0, possibly μ C=0 | Empty retained product has mass1; T06 still applies whenever full mask is nonzero | Do not infer μ C≠0 from a positive full mask with no retained coordinate |
| K=0 | B=univ and mask mass d^n | The anomaly factor is (1-d)^0=1, including d=1 |
| d=0 | Only B=empty has nonzero weight1 | Positive m masks handled by T07 zero branch |
| d=1 | Only B=univ has nonzero weight1 | Masks containing an anomalous coordinate have weight0 |
| 0^0 | Both zeroth-power factors evaluate to1 | No manual 0^0=0 convention |
| P E_B=0 | T07 and T14 remain valid and have weight0 | Split zero restriction before any conditional normalization |
| Repeated observed values | Allowed | e distinguishes positions, not observed values |
| Atoms at z | Closed event z≤T preserved exactly | No strict-tail substitution or continuity assumption |
| s_B=0 | T_B=0 on both actual events | For z≤0 such points are included; for z>0 they are excluded |
| Arbitrary nonordered e | Every equivalence is admitted | Only injectivity and retained membership are used |
| Asymmetric r | Generic mask law still admitted; ratio-based physical corollaries do not apply | Exact279 symmetry premise is explicit |
| m=3 | Generic laws valid; no physical corollary asserted | Current279 interface and task require m≥4 |

These are scope/semantic checks of proposed statements, not separately executed tests or proofs.

## Assumption ledger

Required for the generic probability layer: measurable Ω, probability μ, measurable C, a finite fixed B, and a fixed arbitrary e. Nonzero full-mask mass is required exactly in T06/T13 and the corresponding implications in T15. T07/T14 retain zero masks.

Required in addition for the physical transport: measurable g, product-measurable r, pointwise r symmetry, m≥4. These are carried in the literal physical HEADs. No canonicality/moment/envelope premise is smuggled into the generic law; no physical symmetry premise is removed from a ratio conversion.

Not assumed anywhere in281: StandardBorel Ω, nonatomic μ, unique observed values, positivity of every mask, existence of a regular conditional law given a full anomalous value, external ShaoZhou contracts, or the desired quantitative tail bound. The last two remain in the qualified276 quantitative theorem and its future application.

## Dependency order and implementation obligations

Definitions D01,D02,D03 precede all theorems. The generic chain T01-T07 and physical measurable/pointwise chain T08-T12 are independent until T13/T14 join them. T15 is the final original-cutoff consumer. ORDER.txt lists every local edge. No cyclic reference or future theorem is used by a HEAD.

Future implementation must preserve exact HEAD/RHS bytes, derive every product-coordinate conditional probability instance only where justified, handle the zero restriction before dividing, and transport the measurable closed event using the actual map equality. It must use the public measurable producer plus exact279 bridge rather than copy an old proof tree. A new frozen author source and complete independent source-to-statement/proof/all-actual-TYPE/VALUE review, plus exact-source server kernel/transitive-axiom receipt, are still required.

## Open scope

Next282 may compose qualified276 with these law/event equalities while preserving common N before λ,m,z, true conditional mean/projection/variance, n/2≤m≤n, λ∈[0,1], all original external hSZ/hSZC inputs and the exact z≥1 window. This is not performed or claimed here.

Full anomalous-value conditioning, interaction/Δ estimates, quantitative low-s_B costs, anomaly exponential integration, discarded large K/Q probability, original unconditional PE-R/PE-L/NR/DC/full OQ56/root conclusions remain OPEN. A finite conditioning identity is not a tail estimate or root theorem.

## Evidence and author separation

All20 original immutable inputs matched before first write. The later two279 qualification bindings matched before being consumed. Existing exact successful reviews and original objects are reused; no accepted old proof/check is replayed. The proposal author has made no independent proof-acceptance claim and has launched no reviewer/child.

Only unit281/proposal-01 new files were written. SourceAccepted=false, KernelChecked=false and Qualified=false for281. Requested settings are gpt-6.1-sol/xhigh; actual model/backend/effort and token breakdown remain null when not exposed. The final unique LAST releases all active/dormant identities and records all six work-state counters zero, with no queued continuation and no active wait.
