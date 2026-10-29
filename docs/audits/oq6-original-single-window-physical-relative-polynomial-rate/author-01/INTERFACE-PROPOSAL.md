# Unit263 complete interface proposal and bearing feasibility

Status: INTERFACE_PROPOSAL_ONLY. This is an exact declaration proposal and mathematical route, not a proof implementation, independent review, or kernel result. No proof delimiter or proof body is supplied. The lead must freeze the complete proposed statement, and qualified unit262 evidence plus a fresh implementation activation must be supplied, before any implementation.

Proposed module: `Shao.OQ6.OriginalSingleWindowPhysicalRelativePolynomialRate`.

Proposed sole public theorem: `actual_original_single_window_physical_relative_polynomial_rate`. The complete public type is HEAD-PROPOSAL.txt, with PREAMBLE-PROPOSAL.txt and CLOSING-PROPOSAL.txt. There are no proposed helper declarations, public callbacks, budget hypotheses, or axiom additions.

## Exact source and upstream status

The original inputs p51.md SHA256 96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359 /17326B and p54.md SHA256 e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43 /6045B were both read completely. The immediate source target is p51 lines223-232, S19 and its surrounding S3 argument: one sufficiently small fixed positive constant in the beta-inverse p-window, not four separately assumed windows. The bounded-product part of S16-S17 supplies the relevant original branch. The theorem remains conditional on the exact broader-L2 scalar hSZ packet; it does not prove the published external result or broaden that packet's attribution.

Unit262 candidate SHA256 06bf9452ba1bcb23e751749739d231c10f93fa77fb7e615bcbc448d3e4b78e7b /18403B/357LF was read completely. Its stable frozen mathematical type is used solely as draft bearing. Its independent SOURCE review is active, and it is NOT qualified in this proposal's binding. Unit261 qualified evidence was read as a dependency-status input; no old proof, kernel, object, or AX check was replayed. The proposed import of unit262 is a future assembly dependency, not a claim that this candidate is accepted or currently present in the curated library.

## Proposed exact quantifiers and dependencies

The order is: arbitrary original measurable space and probability law μ; the original measurable symmetric L2 kernel h with its original centering and unit projection second moment; the derived original g,r,v,rho; fixed p with 2<p<=3 and integrable |g|^p; fixed cSZ,C1,C2,C3,C4 and the unchanged external hSZ packet; fixed Cenv,aenv,t0,Menv with their original signs; the original beta and the explicit original K0,Ktail; then one existential c>0; then one eventual n; then all w and z satisfying the original envelope assumptions and the single p-window.

Thus c and the eventual index are chosen before w,z,n is specialized. c cannot depend on n,w,z. The mathematical candidate c below depends only on the fixed original law/kernel through beta,rho, on p,cSZ, and on t0,Menv. It need not depend on Cenv,aenv or C1-C4, although their prior quantification permits that harmless dependence. The eventual index may depend on all fixed parameters and c; it cannot depend on w or z. The threshold set is uniform over every admissible w, including a different admissible w at each n.

The head deliberately omits unit262's auxiliary existential cg, all four named public window hypotheses, and the beta-zero disjunction. cg is an internal upstream witness. Beta positivity is derived internally from existing assumptions. No beta positivity, moment normalization, or new measurability premise is added.

The head adds the explicit eventual conclusion `1 <= c * beta^(-1/p) * n^q`. This is a consequence of the same fixed assumptions and prevents a merely empty eventual z-window. It is a proposed stronger conclusion, not a premise or a silently assumed nonempty window. The lead can evaluate this exact addition before freezing; the proposal has only one recommended complete head.

The coefficient is unchanged, with K0 = 64*exp(1/2)^4*(1+4*512) and Ktail = 8*(1+C1+C2+C3+C4)*exp(C3)*(1+K0). Ktail positivity is returned before the eventual quantifier and follows from the positive components of hSZ even if no admissible envelope w exists.

## Internal positivity obligation for beta

Set f(o)=Real.rpow |g(o)| p and beta=integral f. Pointwise f>=0 gives beta>=0. If beta=0, the supplied integrability hgp and the nonnegative-integral zero criterion give f=0 μ-a.e. At each such point, g(o)!=0 would imply |g(o)|>0 and therefore f(o)>0 by `Real.rpow_pos_of_pos`, a contradiction. Hence g=0 μ-a.e.; `integral_congr_ae` then forces integral(g^2)=0, contradicting the original hprojectionsecond=1. This uses no stronger moment, finite-support assumption, non-atomicity, or new restriction on Ω. The argument does not require a separately added integrability assumption for g^2; the integral-congruence identity alone suffices for that contradiction.

This is the bearing route for a future internal positivity step, not a supplied Lean proof. It intentionally avoids relying on an unverified exact signature for an rpow-zero equivalence: positivity of a positive-base rpow already excludes any nonzero g at a zero-f point.

## One fixed constant and four internal windows

For fixed parameters use the following mathematical candidate, where all powers are real rpow:

* q = (p-2)/(2*p).
* cMoment = (min(1/2,cSZ)/2)^(1/p), exactly unit262's cWindow.
* cRemainder = remainderWindowScale (BoundedProductEnvelopeTails.tailScale Menv) t0.
* cAbsorb = min(1,sqrt(t0)/2), exactly unit262's extra absorption scale.
* cTilt = 1/(2*exp(1/2)).
* cGeometry = 1/(1+rho).
* cOther = min cRemainder (min cAbsorb (min cTilt cGeometry)).
* c = min cMoment (cOther * beta^(1/p)).

Each factor is strictly positive. hSZ supplies cSZ>0; beta>0 is the internal obligation above. `remainderWindowScale_bounds` gives cRemainder>0 once tailScale Menv>=0 and t0>0. The tailScale definition is a maximum containing exp(1)*(Menv+1), which is positive for Menv>=0. t0>0 gives cAbsorb>0; exp positivity gives cTilt>0; rho=sqrt(v)>=0 gives cGeometry>0. Finite positive minima and beta^(1/p)>0 then give c>0.

For beta>0, beta^(1/p)*beta^(-1/p)=beta^0=1. Consequently c*beta^(-1/p)<=cOther. This cancellation is valid for every positive beta, including beta<1; the route does not assume beta>=1 or use an unrecorded Lyapunov inequality.

For 2<p<=3, 0<q<=1/6. The upper bound is equivalent, after multiplication by positive 2*p, to 6*(p-2)<=2*p, which follows from p<=3. For n>=4, (n:Real)>=1, so n^q<=n^(1/6)<=n^(1/2)=sqrt(n). From the sole public hWindow, the following internal bounds are then available uniformly in w,z:

1. Moment window: c<=cMoment, and beta^(-1/p),n^q are positive, so z<=cMoment*beta^(-1/p)*n^q. Supply unit262's moment disjunction by its positive-beta branch only.
2. Envelope window: z<=cOther*n^q<=cRemainder*n^(1/6).
3. Absorption window: z<=cOther*n^q<=cAbsorb*n^(1/6).
4. Tilt window: z<=cOther*n^q<=cTilt*sqrt(n)=sqrt(n)/(2*exp(1/2)).
5. Geometry: z<=cOther*n^q<=cGeometry*sqrt(n), hence (1+rho)*z<=sqrt(n), because 1+rho>0.

Items2-5 discharge all four named non-moment window hypotheses of unit262; item1 discharges its distinct moment-window argument. None is reintroduced as a public condition. The same single c works for the closed endpoint of the public z-window.

## Eventual uniformity and final upstream application

Use the original unit262 existential cg and its eventual assertion at the fixed envelope parameters. This supplies one eventual event containing n>=4 and its uniform conclusion for every w,z,p and hSZ packet. Fixing p and hSZ earlier in the new statement only specializes that stronger upstream quantification; it does not choose an upstream index after observing w,z.

Separately, q>0 gives n^q -> +infinity along natural n. The fixed coefficient c*beta^(-1/p)>0 makes the proposed single window eventually at least1. Intersect this event with the existing unit262 eventual event. No new asymptotic comparison is needed for the four windows: n>=4 suffices for the exponent comparisons. At an n in that intersection, apply the SAME original unit262 theorem at the original μ,h,g,r,rho and the current original w,z, with the four internally obtained non-moment windows and the positive-beta moment branch. Specializing its result returns the exact proposed ratio bound and original Ktail.

The physical random variable is definitionally the original one: P is the n-fold product of the same μ on Fin n -> Ω; D1=residualStatisticD n r; physical=(projectionW+D1)/sqrt(centeredSq), with physical=0 when sqrt(centeredSq)=0. No recoding, alternative iid witness, normalized surrogate statistic, alternate Studentizer, tail-continuity limit, or change of zero convention is introduced here.

## Read-only Lean API feasibility

This is a static interface-feasibility assessment, not elaboration or mechanical validation. The pinned toolchain read from library/lean-toolchain is leanprover/lean4:v4.36.0-rc1; no local toolchain was probed or executed, per the project's stronger server-only rule and this proposal activation.

* Upstream exact type: unit262 frozen head plus complete candidate source. Required call is its sole public theorem at original μ,h,hh,hh2,hhsymm,hcenter,hprojectionsecond, followed by its fixed-envelope eventual assertion and its current w,z,p,hgp,hSZ specialization. No production proof change is proposed.
* Nonnegative integral zero criterion: `MeasureTheory.integral_eq_zero_iff_of_nonneg` is used in the curated EndpointRelativeError interface example at lines98-99 with a pointwise nonnegativity function and an Integrable proof. `integral_eq_zero_iff_of_nonneg_ae` is also available in curated sources. `integral_congr_ae` transfers the resulting g=0 a.e. identity to g^2. This reuses only the API shape, not those old proofs or their acceptance evidence.
* Positive rpow and multiplication: `Real.rpow_pos_of_pos`, `Real.rpow_nonneg`, `Real.rpow_add` for positive beta, and `Real.rpow_zero` supply cancellation; unit261/262 and accepted IIDSourceStrictMomentBudgets already expose the same real-power representation. Parenthesization and, where needed, the established `Real.rpow_eq_pow` normalization are elaboration details for a later authorized implementation.
* Exponent monotonicity: `Real.rpow_le_rpow_of_exponent_le` for base>=1, plus `Real.sqrt_eq_rpow`, occur in the curated OriginalExceptionalTailAbsorption interface. Rational inequalities use hp2,hp3 with positive denominator 2*p. No numerical probing is needed.
* Remainder positivity: exact public `Shao.OQ5.P51.remainderWindowScale_bounds (K t0) (0<=K) (0<t0)` returns positivity as its first component. The accepted tailScale definition is read-only and directly gives its required nonnegative input from hMenv.
* Eventual nonemptiness: `tendsto_natCast_atTop_atTop`, `tendsto_rpow_atTop` with q>0, composition, eventual_ge_atTop, and multiplication by a fixed positive coefficient provide the needed eventual lower bound. The accepted absorption module and current unit262 candidate contain those exact asymptotic API patterns. One can alternatively ask n^q>=1/(c*beta^(-1/p)) and multiply by the positive coefficient, avoiding a separate scaled-tendsto lemma.
* All explicit measurable-space and product-measure lets in the proposed head are copied from unit262's stable type. Keeping these explicit avoids silently changing the same original probability space or relying on an inferred different measurable structure.

No new mathematical API blocker was identified in this static route. Exact elaboration, qualified upstream binding, full independent source-to-statement/proof review, and the future server kernel/all-owned-type-value/transitive-axiom receipts remain outstanding. No such future receipt is asserted here.

## Source scope and exclusions

This proposal removes a real public-interface gap between unit262 and p51 S19 for the original bounded-polylog product-envelope tail branch z>=1. It retains arbitrary original Ω and μ and does not insert standard Borel, countable-generation, atomlessness, or higher mixed-moment hypotheses. It does not claim that an arbitrary fixed unbounded envelope satisfies the n-dependent bounded assumptions.

The complete p54 repair is retained: conditional p-moment convergence is only qualitative with a uniform eventual bound, not an arbitrary polynomial rate. This theorem concerns the fixed original law, and neither uses nor asserts a conditioning uniformity claim. The p54 atom-safe upper-tail payment remains upstream original evidence; this proposal changes only window selection, not the strict-margin or signed exact-coding arguments.

No compact 0<=z<=1 estimate, CDF theorem, atom transfer, DC result, unbounded-conditioning reduction, external broader-L2 Shao-Zhou theorem, or full OQ56/root completion is claimed. Full OQ56 and root remain OPEN.

## Implementation gate and retained authority

Lead action needed for future work is exact complete declaration freeze and a new implementation activation binding the final QUALIFIED unit262 source/evidence. This author retains exclusive proposal-directory authority while idle. No FINALWRITE is issued at the proposal stage. Current runtime upon proposal-ready is zero writers, zero heavy commands, zero inflight operations, zero uncertain operations, zero pending external operations, and zero children. There were zero server/network calls, zero Lean/AX calls, and zero publication actions.

Requested configuration is gpt-6.1-sol/xhigh with fresh context. Actual backend/model/effort and input/cached-input/output/reasoning-subset usage are unexposed and remain null. They are not inferred from the requested configuration.
