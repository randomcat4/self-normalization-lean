# Unit 261 interface proposal: original current-level physical finite-cost tail

Status: PROPOSAL_READY; no proof implementation, Lean check or qualification is claimed. The lead owns the freeze. Unit 260 must qualify at its exact current source before implementation begins.

The proposed module is `Shao.OQ6.OriginalCurrentLevelPhysicalFiniteCostTail`, with one public theorem `actual_original_current_level_physical_finite_cost_tail`. Its public conclusion contains only original-μ product-space integrals and the physical statistic. It includes the exact finite-cost lower/upper pair, the inherited nonnegative/cubic source-cost bound, and the direct cubic replacement pair. The latter is elementary monotonicity, with no positivity requirement on either lower correction factor.

## One witness and quantifier order

Call qualified 259 `actual_original_level_dependent_upper_physical_frontier` exactly once on μ,h and their original assumptions. Its single `m₀, hm₀, hcg` witness (259 lines 14–34; implementation 823–834) is selected before introducing n,z,p,cSZ or the envelope data. Retain its analytic packet and its original physical-payment packet together. Do not call another coding producer or reselect m₀ per level, moment, budget, or tolerance.

Project out the `cg` at 259 lines 533–551. The public ordering is exactly: original μ/h; g,r,v,rho; exists positive cg; all Cenv,aenv,t0,Menv and their signs; eventually n with 4≤n; all w with original-law envelope conditions; current z and its three separate windows; p∈(2,3] with original-μ p-integrability; cSZ,C1,C2,C3,C4 and explicit hSZ; then the exact β/cWindow disjunction. Thus the eventual n is uniform over w,z,p and the scalar engine constants, just as 259 is. No claim is made that cg or that eventual threshold is explicit.

The same canonical witness is internal because the public target no longer mentions coded quantities. This hides no assumption: m₀ and every coding datum are constructed from the original hypotheses by the one call to 259. A second coding witness, arbitrary normalized family, arbitrary theorem-as-callback, or full-original-space coding map is not a permissible replacement.

## Original quantities retained literally

Use original mN/P from 259 lines 294–300, ξ0=g/√n (307), residualStatisticD and current-z clipping with c=512 (308–316), and the true original deleted functions. Public sourceCost0 is precisely 259 lines 371–398, using the *full* I0 in every term. Public δoriginal/Loriginal are 259 lines 496–502. The public physical statistic and zero convention are 259 lines 682–684. Public payment is 259 lines 692–694, namely 3exp(−boundedPolylogMomentOrder(t0,n))+exp(−cg*n)+4exp(−z√n/2). No normalization by a deleted I and no compact/untilted substitute enters the finite-cost target.

The proposed head's D2 let makes the exact clipping visible even though the final formula uses B0 and the physical statistic. The underlying definitions preserve the original n/(n−2)^2 and clipping1 behavior; no definition is altered in this unit.

## Exact instantiation of 260 primitives

In the following table line numbers are the actual fully read sources, 259=1136c7f4…/1114LF and 260=67e7b06f…/338LF. The table is an implementation route, not additional theorem premises.

| 260 input | Value and exact 259 bearing |
|---|---|
| X/O, measures and probability | X=(Fin n→Ω×ℝ), mAug, ν; O=(Fin n→Ω), original mN, P. Definitions 294–343 and physical packet 695–699; analytic probability 404–406. |
| n and hn | Same original n; 4≤n from 538 implies 1≤n. |
| ξ, ξ0, η | The actual ξ0, ξ, actualNormalizedFamily ν (Y k), using the same quantized Y and ε(k)=1/(8√n(k+1)), at 306–343. No abstract replacement. |
| D,D2,B | D=D1∘q, D2=current-z clippedCenteredDelta∘q, B=B0∘q, at 308–316, 327, 355–358. |
| Aη,Adeleteη,Bdelete | Aη=Anew, Adeleteη=AdeleteNew (Adelete+Mdelete), Bdelete=B0delete∘q, at 359–368. This is the true perturbed deletion and cannot be replaced by Adelete alone. |
| A0,B0,A0delete,B0delete | Original-space functions at 311–316. |
| originalClip,physical | T0=clippedCenteredStatistic at 310; physical at 682–684. |
| hξ,hD,hD2,hOriginalClip,hPhysical | ξ measurability 409; D,D2 augmented measurability 703–704; original T0 707; original physical 712. |
| hη,hηindep,hη2,hηmean,hηenergy | Same η packet at 417–424 (also η measurability 740). |
| hD2pos | Original pointwise 1/2≤1+D2 at 414, pulled back by q; no exceptional-set or reduced-Hsource assumption. |
| hηpos | The normalized positive Vη a.e. component of 417–424. |
| hSZ | Exact public ScalarShaoZhouFiniteCostTailInput.{u}; its positive cSZ is also the budget used below. |
| full scalar factors, 260:81–87 | Combine 259:458–461 factors for Dη,D2 with 450–452 triple Ffull=(M,Anew,B); select its second and third real coordinates for FA,FB. Measurability follows from measurable product projections. |
| true deleted scalar factors, 260:88–93 | From 259:453–457 triple Fdelete=(Mdelete,AdeleteNew,Bdelete), select second/third components. Every deleted factor sees only η_j with j≠i. |
| pointwise nonnegative full/deleted envelopes | Anew and AdeleteNew at 435–438; B and Bdelete nonnegative from the retained all-ε packet 218–219, instantiated at ε0>0 (never ε=0), then pulled through q. These B functions are the exact same current-z ones. |
| a.e. domination | Signed bound |Dη|≤Anew from 425–428; |D2|≤B0 from 414 pulled through q. |
| exponential integrability and positive Iη | Iη positivity at 468. Integrability can be obtained from `NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits` (API lines 173–218), with the exact ξ/Y/ε primitive packet 407–413; its full-Iη output is API line 214. Alternatively derive locally from 259 η measurability and t−t²/2≤1/2, giving exp(Sη)≤exp(n/2), by finite-measure bounded domination. No new assumption. |
| full and deleted weighted integrability | Exact full-I normalized functions at 462–465, with Anew/AdeleteNew, Sη/Sηminus. |
| eventual strict coordinate/total budgets | Apply 259:491–531 with p,hgp,cBudget=cSZ and hcSZ extracted from hSZ. The exact β=0 OR positive-β window gives δη_i<1/2 and Lη<cSZ*z². Positive tolerances τ=δ=1 suffice for the eventual budget projection, or take the common eight-condition packet at 770–793 with τ=δ=γ=1. |
| Lη→Loriginal | 259:519–521 gives Lη→L0; 508–509 identifies L0=Loriginal on original P. Do not replace this by Lcompact. |
| sourceCostη→sourceCost0 | 259:480, using literal true deleted cost and full Iη; original sourceCost0 is 393–398/651–656. |
| exact clipped real law | 259:710–711 gives map(T0∘q)ν=map(T0)P. To match 260's codedClip, use W=projectionW∘q,V=V0∘q at 705–706 and the retained clipped statistic identity T0=Tclip at 163; equivalently unfold T0/clippedCenteredStatistic once to match its zero branch and denominator. This is a definitional/function equality, not a law hypothesis. |

All primitive inputs of 260 are therefore to be discharged from qualified 259 and its exact imported normalized-projection API (or the elementary exponential bound). No 260 hypothesis is exposed as a new public callback.

## Four separate fees, all derived and set to the one payment

Internally call 260 with pUpper=payment, p2=payment, pZ=payment, pClip=payment. These names do not occur in the proposed public head.

1. Coded moving numerator error: 259 lines 764–765 gives for every γ>0 eventually ν.real(E k)≤payment+γ; use as 260:108.
2. Coded denominator error: 259 lines 758–760 gives ν.real(E2)≤payment; use as 260:107.
3. Coded *unperturbed projection-zero* event: 259 lines 758–760 gives ν.real(Z)≤payment; use as 260:106. Do not confuse this with the a.e. zero-free normalized Vη.
4. Original clipping disagreement: 259 line 734 gives P.real(Eclip)≤payment, with Eclip literally `{ζ | T0 ζ≠physical ζ}` at 685; use as 260:105.

260 lines 117–121 retain the coded zero fee and original clipping fee separately and yield exactly lower0−2payment and upper0+4payment. The moving numerator and denominator terms occur only on the upper side. Do not infer an uncharged lower physical tail or coalesce the coded/original event charges before invoking the theorem. No assumption that the lower multiplicative factor is positive is required.

## Cubic replacement

259 lines 482–485 supplies 0≤sourceCost0≤cubicCost, with cubicCost=64*exp(1/2)^4*(1+4*512)*(1+rho)*(1+z)^3/√n. This is the source cost itself, not an absolute or relative payment bound. From hSZ (definition in NormalizedIntegrableTailAssembly lines 18–20), C2>0,C4>0. From `Shao.standardNormalTail_basic` (GaussianTail lines 91–95), the normal tail is positive; the exponential prefactors are positive. Hence sourceCost0≤cubicCost lowers 1−C2*cost and raises 1+C4*cost. Chain these two monotonicities with the exact-cost bounds. The sign of either lower correction factor is irrelevant.

## Precisely pending work and limits

There is no mathematical premise gap identified from these exact sources. The outstanding *gate* is unit 260 final independent qualification; its successful native02 and same-FIRST-O audit do not themselves authorize using it as accepted evidence. The proposed Lean head is unelaborated; product-component syntax, reduction of codedClip to T0∘q, and the long conjunction projections still require ordinary implementation/type-checking after lead freeze. The existing projection API supplies exponential integrability without any extra mathematical hypothesis, so a failure to extract it would be an implementation issue.

This proposal does not prove the broader-L2 hSZ input, assert its literature extension, bound payment relative to a Gaussian tail, prove a CDF/relative-tail/DC/root statement, or close OQ56. Original/root scope remains OPEN. No external web/literature work was requested or performed; this is a source-bound application of exact local interfaces, with explicit external-result attribution preserved.
