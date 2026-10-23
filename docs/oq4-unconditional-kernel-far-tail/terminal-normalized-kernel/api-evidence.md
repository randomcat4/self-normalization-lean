# Pinned source/API evidence for the terminal normalized consumer proposal

This is read-only source inspection and a mathematical/declaration packet. It is not elaboration, independent review, kernel/object or axiom evidence. No Lean/import/toolchain/build command, remote operation, Git/cache mutation or process wrapper was run or created. No new API server request was necessary. All later Lean checks remain designated-server-only under the existing OQ4 single-heavy CPU18–21 lease, with the first new full source check producing its object via the mature runner's -o path. This author has no heavy execution authority.

The file pin library/lean-toolchain was read: leanprover/lean4:v4.36.0-rc1. SERVER.md fixes mathlib807d3836b165983210ee2ecf3cd28f239436949c. These are file pins, not runtime probes. Source/byte/hash bindings and exactly what was inspected are recorded in static-inventory.json; no accepted old proof was recompiled or re-reviewed.

## Exact direct calls

1. In each row, use the given hprob j as a proof-local letI. The exact actual coefficient calls, with derived lower integrabilities hId,hSq and derived hM0:0<=M, are

       cosineCoefficient_large_h_bounds (nuSeq j) M (hSeq j)
         hId hSq (h3 j) (hmean j) (hsecond j) hM0 (hM j) hh1 hlarge

       cosineCoefficient_log_error_mul (nuSeq j) M (hSeq j)
         hId hSq (h3 j) (hmean j) (hsecond j) hM0 (hM j) hh1 hlarge q.

   q is the ACTUAL natural NSeq j or floorHorizon T (hSeq j). The first bound's .2.2.1 is3/4<=rho and .2.2.2 isrho<1. The latter error is exactly

       |(q:Real)*log rho+pi^2*q/(8*h^2)|
         <=(pi^3*M/48+pi^4/8)*q/h^3.

   Rewrite lambda=pi^2/8 by real ring arithmetic. No desired rate-limit premise is added. CosinePowers was read completely; the exact local source is qualified, and its inverse-scalar proof already uses log_pow/log_inv/exp_log with proven positive powers.

2. Existing principalRate nu h has NO probability-instance parameter: it is the ordinary cosineCoefficient nu (pi/(2*h)). The normalizedKernelMass/normalizedKernelCosine parameters are measure, implicit probability instance, real h, natural n, real z, in that order. Thus varying-row expressions use exactly

       @normalizedKernelMass (nuSeq j) (hprob j) (hSeq j) k 0;
       @normalizedKernelCosine (nuSeq j) (hprob j) (hSeq j) k 0.

   Definitions in KernelRecurrence lines15–30 and KilledIteration lines19–27 were read. No new alias or top-level instance is introduced. This proposal uses the inspected actual values and principal cosine interpretation; the rest of that qualified module is not re-reviewed here, and no arbitrary block premises are imported.

3. The new finite normalized theorem calls exactly

       BrownianTerminalKernelBlock.terminal_kernel_block nu T hT h hh n.

   This exact full276-LF LOCAL source was read. It gives actual G(n+floorHorizon T h), the actual cosine killedAction, and the literal sourceSurvivalError plus remainderC*exp(-9*lambda*T), times actual G(n), for all n including0. Multiplication by the positive inverse rho^(n+L), pow_add and real field identities give the new public P2. cos(pi*w/(2*h)) equals principalCosine h w by ring arithmetic. No finite P1 coefficient, error or event is supplied as a new public premise.

4. For the varying-law source error, call exactly

       BrownianUniformSurvival.uniform_brownian_survival_momentClass
         CanonicalBrownian.B CanonicalBrownian.law CanonicalBrownian.isBrownianReal
         T hT M (epsilon/2) (half_pos hepsilon).

   It yields A>0 and one h>=A threshold for every nu, explicit probability witness, integrable third power, mean0, second1, beta<=M, and every physical |z|<=h. Instantiate those arguments at the actual row. It gives STRICT pointwise error<epsilon/2. The new helper uses csSup_le to obtain NONSTRICT E<=epsilon/2, and epsilon/2<epsilon finishes the convergence proof. The source's public head and complete proof lines306–368, literal survivalError and existing supremum-bound proofs262–304 were read. Its fixed-law tendsto_survivalError is not used on the changing-law sequence.

   The canonical exact public names are B, law, instIsProbabilityMeasureLaw and isBrownianReal; their public source headings were inspected. The actual canonical model is internal. The public consumer does not take a Brownian process/law/identity as input. Parent-reported qualified canonical source/object binding is inherited and must be verified at integration; no old full source review is repeated here.

5. The common-M row call is exactly

       BrownianLongTimeRelativeBridge.varying_row_long_time_relative_bridge
         nuSeq hprob h3 hmean hsecond M hM Cq Cs hCq hCs hAC hS
         hSeq NSeq hpos hinfty hlong hshort.

   Its entire frozen combined13-head contract and complete row proof were read. After reducing the existing local lets R,H, it supplies H>0, eventually forall k<=N the nonnegative bound Ghat<=H, and forall epsilon>0 eventually forall floor(h^2)<=k<=N the STRICT cosine error<epsilon. H=2*(1+(2*Cs)*exp(pi^2))*exp(pi^2), independent of every future T. The original fixed-law long_time_relative_bridge is not used to cover changing laws. This exact row extension remains qualification-pending.

6. Use BrownianTerminalSpectral.remainderC_pos directly. The exact literal constant is4/(3*pi*(1-exp(-2*pi^2))). Its frozen all-head/value contract was read completely, and its LOCAL source literal/public heads and relevant exp algebra were inspected. The fixed-time spectral tail has exp(-9*lambda*T); multiplication by the derived inverse-rate factor exp(lambda*T) leaves exp(-8*lambda*T). This consumer does not need a new spectral premise or reprove the spectral module.

7. After the normalized limit and free compensation, the exact actual finite product conversion is

       killedMass_eq_closedStrip_probability (nuSeq j) (NSeq j) (hSeq j)
         (hpos j).le,

   under local instance hprob j. Its exact proof and shiftedClosedSurvival_eq_closedStrip were read at KilledPathLaw248–262. The preceding killedMass_eq_path_probability165 identifies the actual restricted finite product law. The equality includes time0 via |0|<=h. Shao.closedStrip is the literal forall k<=n, |prefixSum a k|<=h event; its actual definition and zero-prefix convention were read in ClosedSurvival. The final probability head writes that actual finite-product event explicitly.

## Existing primary pinned Mathlib source evidence reused

No new source-only server API call is needed. The saved actual148/150 source/API packets already identify the following primary pinned files and exact heads; these excerpts and relevant actual usages were read. The supporting earlier requests remain in their original directories and are not replayed or copied here.

| Pinned primary source | Exact API used and existing evidence |
|---|---|
| Mathlib/MeasureTheory/Function/L1Space/Integrable.lean, SHAd80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759 | Integrable.mono'104–106: integrable dominator, AEStronglyMeasurable target, AE norm bound. integrable_const166 and Integrable.add420. Actual148 api-evidence.md records the primary excerpts; the same lower-moment domination body appears in the inspected148/152 sources. |
| Mathlib/MeasureTheory/Integral/Bochner/Basic.lean, SHA66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670 | integral_nonneg647–649 derives beta>=0; no integrability assumption on a totalized integral value is substituted. |
| Mathlib/Algebra/Order/Floor/Semiring.lean, SHA7c0fa92ce68350dc4e97bac5ba8cadc3d2c4da70f36eb6c42d5647176d587f68 | Nat.floor_le47 needs nonnegative argument; Nat.lt_floor_add_one63 holds for the actual real argument. Their use with t*h^2 is paid by T:NNReal, with h^2 by sq_nonneg. |
| Mathlib/Topology/Algebra/Order/Field.lean, SHA35482bce0fa30cac4daa22bc80dad118f4bc912a9604086f349c2ff41b4c0e32 | tendsto_inv_atTop_zero75–79 composed with hinfty, then pow2, gives h^-1 and h^-2 limits. |
| Mathlib/Topology/MetricSpace/Pseudo/Defs.lean, SHA3463e90a92cb1c28bcf0062c46ea9ad4eb2737e1774232e8796bf69bad98d64b | Metric.tendsto_atTop910–913 is the epsilon/threshold criterion. Real.dist_eq and the eventual absolute-value squeeze are already exercised by148's actual power-limit proof. |
| Mathlib/Topology/Algebra/GroupWithZero.lean, SHA989120f181b074fc7b65ca2416188a67eec4ae251ea29d78fc6b139a8285db2a | Tendsto.inv₀107–109 requires a nonzero LIMIT. Here that limit is exp(-lambda*T)>0. It never inverts a survival probability. |
| Mathlib/Analysis/SpecialFunctions/Log/Basic.lean, SHA0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97 | Real.exp_log59 needs positive argument; Real.log_pow288 gives log(rho^q)=q*log rho. Positivity is derived from3/4<=rho. |
| Mathlib/Analysis/SpecialFunctions/Exp.lean, SHA1dcb27b9ea4dbfea015fd97196f0cb6ac294633be79590dba8af8685d11b03e8 | Real.continuous_exp153–154 supplies exp of a convergent real sequence. The exact exp_add/exponential positivity/order operations are witnessed in the inspected actual149 source and qualified coefficient source; exp(-x)*exp x=1 follows from exp_add and exp0. No unlocated exp-decay limit is required: terminal_tail_small uses the explicit max/log construction in proof section9. |
| Mathlib/Order/ConditionallyCompleteLattice/Basic.lean, SHAf464444b33d463cfa8502c20a2a8c619108b1337a9003ae430383dce22be641a | le_csSup197 needs BddAbove and membership; csSup_le201 needs nonempty and a bound on every entry. Actual150 saved api-order-host-result.json and api-evidence.md preserve these primary heads. Both requirements are paid, without strict-sup or attainment claims. |
| Mathlib/MeasureTheory/Measure/Real.lean, SHA1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d; Probability.lean SHA00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b | measureReal_nonneg53 and measureReal_le_one44–46 bound each actual probability in[0,1], with the actual probability instances. The bound needs no measurability premise for the event. |

The public declarations contain only the exact primitive/moment/scale premises or, in the separate finite P2 theorem, actual coefficient positivity. The proposal is designed for the pinned existing interfaces; future elaboration may not silently widen heads, add new top-level helpers or imports. Any genuine interface change must first go back to the parent freeze owner. This packet claims no formal success and introduces no additional administrative permission gate.
