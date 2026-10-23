# OQ3 U22av independent complete final review

STATUS: CORRECT

The sole public theorem, its complete proof and every proof-local value, the generated theorem, and the final frozen auxiliary scope are CORRECT. No critical mathematical or evidence gap was found. This unit establishes genuine finite-measure integrability of the actual open-ball pair-supremum oscillation, its pointwise closed-thickening majorant, and the resulting integral bound. It closes the generic integration component of repair01 equation(4), within the stated maximum-norm metric; it does not close original OQ3 B/D or the later geometric and probability dependencies.

Reviewer: sole fresh independent complete final reviewer, separate from the author, assigned gpt-6.1-sol / xhigh. Applied math-theorem, current AGENTS.md, SERVER.md, compact TEAM/REGISTRY and streamlined acceptance. The current OQ3 writer is activated and the previous writer released. Only this report is written. No source, freeze, receipt, cache, prior review or continuation file is changed; no child agent, math-ultra, model switch, Lean/lake invocation or gate replay occurred. All remote observations used tools/server.py and CPU14-17 affinity, read-only. Actual separate input, cached-input, output and reasoning-subset counts are unavailable to this reviewer; no token count or subscription-percentage allocation is invented.

## Exact inputs and complete coverage

Evidence directory: C:/game/shao lean/drafts/oq3/. The entire final source was read: 82/82 lines, 4061 bytes, including imports, setup, all proof-local declarations, every proof step and both closing lines. The entire freeze, actual export, audit program, receipt and environment manifest were read. Actual owner coverage is 2/2 complete types: one public theorem and one generated theorem, with zero global definitions and zero private theorems. Counts were independently derived from the actual DECL/KIND/VALUE export and matched to the receipt's exact names.

| Input | SHA256 | Lines / bytes |
| --- | --- | --- |
| hundred-twenty-ninth-unit-scope.md | 6a0833cffeda9c6c9f4ea3cf191ffe502ef2d73211f3d97637dbfc208ea48c7a | 23 / 2388 |
| u22av-source.lean | d92e1728663023c77a4315ce3dee53aff5d230e46d65a7f98657ba411f4d7487 | 82 / 4061 |
| u22av-receipt.json | 55e01d2b15e23cdce395b582ad50d49c064d76ebce3a951ab80d86116725a760 | 115 / 4536 |
| u22av-Audit.lean | 197938882053cf1c9068a8a97059e199eb363b7a0730e5b974dd67e8b6243c7e | 48 / 1996 |
| u22av-actual-types.txt | 99e1e389989195350f9ef49bcffbb3fd5e3e2b89a1e5d8ff25d007f33c4c9ab8 | 21 / 1265 |
| u22av-audit-environment.json | 5efe20bdc836517cd8128baaf024ba2f97db343a5819198a05e098af8faf255e | 13 / 708 |

All hashes were recomputed locally and independently on the server, with equality. The files are strict UTF-8 without BOM or CR bytes and use LF. The complete declaration preceding `:= by` matches the complete frozen code after whitespace normalization: all objects, binders, assumptions and three conclusions are unchanged. Server scope.md has an earlier mtime than both source snapshots, consistent with the preimplementation freeze. The source scan contains no sorry/admit/new axiom/unsafe/native_decide.

Observed worktree: /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3; branch feat/oq3-cell-oscillation-probability; HEAD e541a9ec39cf235fad723cf465a2b6ba575f637c. The new source remains untracked. Its current bytes equal source-02.lean and the reviewed local source, so this review binds the source hash rather than the parent HEAD alone. Other continuation files, including AW, are outside this review.

## All complete actual owned types

The exact export was read in full locally and within the full existing server audit log. Both constants have transitive axioms `[propext, Classical.choice, Quot.sound]`; neither is a definition.

```lean
-- Generated theorem: Shao.OQ3.indicator_cell_averaged_oscillation_bound._simp_1_1
∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α} {ε : ℝ},
  (y ∈ Metric.closedBall x ε) = (dist y x ≤ ε)

-- Public theorem: Shao.OQ3.indicator_cell_averaged_oscillation_bound
∀ (μ : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsFiniteMeasure μ]
  (A : Set (ℝ × ℝ)) (g : ℝ × ℝ → ℝ) (C L h : ℝ),
  0 ≤ C →
    0 ≤ L →
      0 ≤ h →
        (∀ u ∈ A, |g u| ≤ C) →
          (∀ u ∈ A, ∀ v ∈ A, |g u - g v| ≤ L * dist u v) →
            MeasureTheory.Integrable (Shao.OQ3.openBallOscillation (A.indicator g) h) μ ∧
              (∀ (z : ℝ × ℝ),
                  Shao.OQ3.openBallOscillation (A.indicator g) h z ≤
                    (Metric.cthickening h A).indicator (fun x => 2 * L * h) z +
                      (Metric.cthickening h (frontier A)).indicator (fun x => 2 * C) z) ∧
                ∫ (z : ℝ × ℝ), Shao.OQ3.openBallOscillation (A.indicator g) h z ∂μ ≤
                  2 * L * h * μ.real (Metric.cthickening h A) +
                    2 * C * μ.real (Metric.cthickening h (frontier A))
```

Generated theorem verdict: CORRECT. In every universe and every PseudoMetricSpace, closed-ball membership is exactly the non-strict distance inequality with the displayed orientation. The equality is between propositions; no radius positivity or true-metric assumption is hidden. Its full type, ownership and recursive axioms are included in the existing source-bound audit.

## Qualified direct parents and inherited functional

AU source u22au-source.lean SHA256 f1e693a8b9b2db416dd730bcdfb596030d768b911015bcfdfc50a16e97e62e2d was read in full (97 lines / 4403 bytes), including the complete definition value, both complete public types/proofs and all locals. Its complete actual export was read (24 lines / 1464 bytes, SHA256 6ffe4fb44aecebd2853b382f45d52f22f7f20f91219356ac337366b81d30fe11). Its existing complete independent report u22au-proof-review.md was read in full and reused unchanged: SHA256 c889f6d17b8fd2415f20ab3dd5ade726d011097668bd17ff73a2bd66f38440e0, 139 lines / 22221 bytes, STATUS CORRECT. All four actual AU owners, including its definition and generated theorem, retain that complete qualification; no old gate is repeated.

The consumed definition is exactly `fun f h z => sSup (insert 0 {r | ∃ u ∈ Metric.ball z h, ∃ v ∈ Metric.ball z h, r = |f u - f v|})`. This is a genuine real pair-difference supremum, with inserted zero to cover empty balls. Under the global bound |f|≤C and C≥0, AU supplies actual boundedness above by 2*C, nonnegativity, domination of every genuine pair, open strict superlevel sets and Measurable of this same function. Its integrability theorem quantifies every finite measure and every real h, requiring only that global bound. The measurability proof uses arbitrary unions of open intersections for fixed pair witnesses, so it does not need f measurable. This correctly supports the present use even when A or g is nonmeasurable; no measurable envelope, essential supremum or assumed integral replaces the functional.

AQ source u22aq-source.lean SHA256 df0428c0d002bdeb2a4c2e436c5024f32e6f58b61d8ef1e129953d1a07919909 was read in full (95 lines / 4075 bytes), including all statement/implementation values and both full proofs. Its complete actual types were read (19 lines / 1031 bytes, SHA256 bc0e3f894fe4d8f8c839e76ddd2728cdc217d036973b37c1cf0b51bed1a3a36e). The complete existing AP/AQ independent report u22apaq-proof-review.md was read and reused unchanged: SHA256 4d513e9cd8bd3ae775e697c5d39e8a4d4dc62247fac4aa6aa892ac167e784509, 138 lines / 28115 bytes, STATUS CORRECT. Its full AQ qualification remains intact; the unrelated AP proofs are not a new dependency claimed here.

AQ's exact consumed type has C,L,h≥0 and bounds/regularity only on A, with arbitrary center z and both points in closedBall(z,h). Its complete local values Near=(closedBall(z,h)∩A).Nonempty and Edge=(closedBall(z,h)∩frontier(A)).Nonempty are literal existential hits, not an assumption that an arbitrary set attains its distance infimum. Its bound is 2*L*h on Near plus 2*C on Edge. The qualified off-frontier theorem uses preconnectedness of the closed ball and the disjoint open interiors of A and its complement; thus no closedness, openness, measurability or boundary regularity of A is assumed. U22av applies precisely that bound, without changing its two-point domain or parameters.

The current server AU/AQ sources match these qualified hashes. In accepted-source-view, OpenBallOscillation.olean resolves to the own worktree object SHA256 e8302c05e5b9717224b8ef8a78cad3a469d277b7f4c8fb5cc80e9a14509dca06 (162104 bytes), and CellBoundaryOscillation.olean to e03be4ab012a530b438d88ff5ea3fa6fc28420c86e1dfa6ad27799230f50479b (154672 bytes), exactly as qualified in their reports. No parent source/object discrepancy is left open.

## Every final proof step and local value

Public theorem verdict: CORRECT (source10-79). The exact hypotheses quantify arbitrary A and g on the usual product-real measurable space, any finite measure μ, and nonnegative real C,L,h. The only g assumptions are |g(u)|≤C for u∈A and |g(u)-g(v)|≤L*dist(u,v) for u,v∈A. There is no A/g measurability, absolute continuity, Gaussian, probability, compactness, positive-radius, density or atomlessness premise.

Source24-25 defines the sole term-level lets N=cthickening(h,A) and E=cthickening(h,frontier(A)); these are exactly the final sets. Source26-27 proves ha:0≤2*L*h and hb:0≤2*C from the listed sign assumptions. Source28-30's hnonneg proves nonnegativity of every nonnegative constant indicator by the two literal membership branches; it is valid for arbitrary T without measurable-set evidence.

Source31-41's hhit is a one-sided domination for every T, K≥0 and center z. In the hit branch, source35 extracts an actual w∈closedBall(z,h)∩T. Source37-38 uses dist(z,w)≤h, obtained from the correctly oriented closed-ball membership by symmetry, and w∈T to put z in cthickening(h,T). Source39 reconstructs the hit proposition from the surviving witnesses after destructuring; source40 then makes both sides K. In the no-hit branch, if z belongs to the thickening the inequality is 0≤K; otherwise it is 0≤0. This direction is valid even when T is empty or nonclosed and an infimum is not attained. No reverse identification of a thickening with an actual hit is made.

Source42-47 derives the required global hind:∀x,|indicator_A(g)(x)|≤C. On A this is exactly hbound. Outside A the indicator is zero, and C≥0 supplies the bound, with no hypothesis on g(x) there. Source48-49 applies the qualified AU integrability theorem to this identical indicator function, C and h. Therefore hint proves genuine Integrable of the exact oscillation, rather than relying on the totalized Bochner integral's default value for a nonintegrable function. AU's real-supremum interpretation is justified by this derived global bound and its qualified BddAbove/nonempty proof.

Source50-60 proves hpoint for every z. Source53 applies the actual conditional-real-supremum upper-bound theorem csSup_le with the explicit inserted-zero nonempty witness. Its other premise is a bound for every member of the value set, which itself supplies boundedness above; no missing BddAbove premise is suppressed. Source55 splits all possible members into zero and a genuine pair value. For zero, source56 uses hnonneg for N and E with exactly ha,hb. For a pair, source57 extracts actual u,v in the exact open ball and r=|indicator(u)-indicator(v)|, without an attained-maximum assumption. Source58-59 places each point in the same closed ball via ball_subset_closedBall and applies AQ with unchanged A,g,C,L,h and all the original assumptions. Source60 adds the two hhit inequalities, for T=A,K=2*L*h and T=frontier(A),K=2*C, then composes this with AQ. This proves the displayed pointwise majorant of the genuine supremum, rather than only a single-pair estimate.

Source61-62 proves MeasurableSet N and E from isClosed_cthickening.measurableSet in the usual Borel product space. The pinned definition is `{x | infEDist x T ≤ ENNReal.ofReal h}`; its distance function is continuous and the sublevel set is closed for every T. Thus measurability needs no regularity of A. Source63-66 proves hiN and hiE by integrability of real constants under IsFiniteMeasure μ and Integrable.indicator on these measurable sets. This is genuine integrability of both majorant summands, and hiN.add hiE gives integrability of their sum.

Source67 assembles the genuine integrability and all-center bound, leaving precisely the third conjunct. Source69-72 invokes integral_mono with BOTH required Integrable proofs, hint and hiN.add hiE, and the pointwise inequality hpoint. This is the real Bochner integral inequality with the same μ on both sides; neither missing integrability nor a probability expectation change is concealed. Source73-75 uses integral_add with hiN,hiE, then integral_indicator_const with the respective measurable sets, and real scalar multiplication becomes multiplication. The result is μ.real(N)*(2*L*h)+μ.real(E)*(2*C). Source76-79 unfolds only N,E and uses commutative-ring identities to put the coefficients first, giving exactly the frozen final expression.

Measure.real is literally `(μ T).toReal`; it would send infinite mass to zero in general. Here IsFiniteMeasure supplies μ(T)<∞ for every set T, so neither mass term has that failure mode. The two constant-indicator identities and all integrability premises therefore have the intended finite-mass meaning. A future probability specialization has the standard IsProbabilityMeasure→IsZeroOrProbabilityMeasure→IsFiniteMeasure instances; no specific Gaussian law is silently instantiated here.

Boundary/degenerate cases are covered. At h=0 the open balls are empty and the inserted-zero oscillation is zero, while cthickening(0,T)=closure(T), so the possibly positive frontier majorant is harmless. A=∅ gives zero test/oscillation and empty thickenings. Empty frontier, singleton/thin/nonclosed sets, arbitrary discontinuity or nonmeasurability of A/g consistent with the on-A hypotheses, C=0, L=0, zero measure and finite measures with atoms all remain within the statement. There is no removal of closure points, no null-boundary premise and no strict-to-nonstrict endpoint loss. Repeated u=v, equality at distance h and a nonattained supremum are included. The theorem makes no claim for infinite μ or negative C,L,h beyond its explicit premises.

## Pinned primary APIs and warning investigation

The server lean-toolchain reads leanprover/lean4:v4.36.0-rc1. Actual mathlib resolves to /root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages/mathlib, HEAD 807d3836b165983210ee2ecf3cd28f239436949c. No toolchain command or rebuild was invoked. The actual consumed new API statements/definitions and their relevant contexts were read: cthickening, mem_cthickening_of_dist_le, isClosed_cthickening, Integrable.indicator, integrable_const, integral_mono, integral_add, integral_indicator_const, Measure.real, measure_lt_top and the probability-to-finite instances. csSup_le was also checked directly: it requires nonempty s and ∀b∈s,b≤a, and constructs BddAbove from that upper bound. Every primary file below was byte-compared with git show at the exact pin and matched.

| Primary Mathlib file | SHA256 |
| --- | --- |
| Topology/MetricSpace/Thickening.lean | 6429465471cb6e7121b79c0509583ea258efadd837133350e9faf7c47775a220 |
| MeasureTheory/Integral/Bochner/Basic.lean | 66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670 |
| MeasureTheory/Integral/Bochner/Set.lean | e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75 |
| MeasureTheory/Integral/IntegrableOn.lean | d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2 |
| MeasureTheory/Function/L1Space/Integrable.lean | d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759 |
| MeasureTheory/Measure/MeasureSpaceDef.lean | 3853c6899a36759a64c9658969fb2f1ea97f0d026598c0f0468c30fe2a5d7356 |
| MeasureTheory/Measure/Real.lean | 1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d |
| MeasureTheory/Measure/Typeclasses/Finite.lean | a8ef0ba0a9b953a5aae9fb16188cd7ad93e0e8d5767c564d02e9f2e8c57eedf2 |
| MeasureTheory/Measure/Typeclasses/Probability.lean | 00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b |
| Order/ConditionallyCompleteLattice/Basic.lean | f464444b33d463cfa8502c20a2a8c619108b1337a9003ae430383dce22be641a |

The known Lake local-changes warning therefore does not hide a changed primary declaration used in this new proof. The unchanged qualified parent reports already bind the product maximum norm, ball/closedBall definitions, indicator branches and parent measure/measurability APIs to the same pin. Their evidence is reused without another old-proof review or build.

## Existing exact-source server kernel and recursive axiom evidence

Run directory: /root/rivermind-data/shao-lean-20261021/runs/oq3/u22av-20261023. Full build-01.log, build-02.log, audit.log, build-history.json and audit-record.json were read, not only summaries. All source/log hashes and byte lengths were recomputed. receipt.build_history equals the complete build-history.json, receipt.audit equals audit-record.json, and the entire actual-types.txt is embedded verbatim in audit.log. Its exact DECL order/names equal receipt.all_owned_names. No successful check is replayed.

| Evidence | Result / SHA256 |
| --- | --- |
| Final source-02 kernel | exit 0; 4.971727875992656 seconds |
| build-02.log | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626; 2 lines / 133 bytes |
| First complete whole-owner audit | exit 0; 6.821983762085438 seconds; U22AV_AXIOM_GATE PASS |
| audit.log | 2fdee8d2b44ecea24bec80230be760ca624908d7182fca7280848d67a330230e; 28 lines / 1517 bytes |
| build-history.json | eeae1415b4bdd5bf0b04242bbc6fdbf8145218572693a8d68b94dbcbdfab5d92; 50 lines / 1814 bytes |
| audit-record.json | bd46af3006d1382dd4c4067e263cf0ec2aa0ba0f68b6b8560328945ba9d33cd6; 18 lines / 498 bytes |
| Current own CellAveragedOscillation.olean | 9f8cbe1ee0085940580934321bb5827d6c104849ff82b5218b7a9f041209e4ce; 136480 bytes |

The accepted-source-view symlink resolves to that identical own worktree object. The environment manifest records unchanged read-only view reuse and only the new own artifact, with the exact AU/AQ parent source hashes. Both successful records specify CPU14-17, native memory 8192 MiB, jobs4 and autoImplicit=false. The successful source log contains only the known two-line Lake/mathlib local-changes warning; no source warning or proof error is omitted or suppressed.

The complete 48-line audit program first requires the frozen public target to exist as a theorem, then iterates every environment constant with actual module owner Shao.OQ3.CellAveragedOscillation using getModuleIdxFor?. For EVERY owned constant it rejects an owned axiom, recursively calls Lean.collectAxioms and rejects anything outside propext/Classical.choice/Quot.sound. It logs complete types and definition values if any, and reports zero frozen definitions, one frozen theorem, two total theorems and two total declarations. Thus private/generated ownership is covered, rather than only a public-name list or namespace-prefix test. Both actual owners have exactly the standard three transitive axioms.

Archived source-01.lean SHA256 c56569a1869b80f9628fc2315439090cb036a91e244b2a18da1c92bfae8b995f (82 lines / 4004 bytes) has exit1 and remains preserved. Its full failed log SHA256 e4a461980666bc1c6fc578ecb6d0c4a6e363442c1ffe05be93d4e887c73dc8f7 (29 lines / 1097 bytes) reports a consumed `hit` hypothesis after destructuring and a redundant no-progress dsimp. The complete source01-to-source02 diff reconstructs hhits from the same witnesses and removes only that redundant dsimp. Frozen declarations and mathematical assumptions are unchanged. This failed attempt is not counted as kernel success, and neither warnings nor failure history was erased.

## Original-source fidelity and final scope

Read the complete original repair01.md section2, lines43-110, including equations(2)-(6), and report.md lines112-216, including the real test, Gaussian oscillation/Edgeworth input, cell change of measure and equation(9). Read-only original whole-file identities are repair01.md SHA256 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd and report.md SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55, under C:/game/shao/current/oq3/proofs/r2/.

The source test is the actual exponential g_Q times indicator of the affine standardized cell B_Q. The present generic theorem integrates the actual pair-supremum and derives the two expected interior/boundary mass terms from bounds only on the cell. It therefore supplies the integration component needed for equation(4), with explicit 2*L*h and 2*C constants. Its closed thickenings are safe measurable majorants of actual hits; identifying or estimating them for the source's concrete family is still a separate obligation. It does not assume the desired mass estimates or final probability error as hypotheses.

The formal norm on ℝ×ℝ is the existing maximum of coordinate norms. Consequently all current distances, open balls, closed balls and cthickenings use that metric. No Euclidean radius/constant, uniform norm comparison or covariance-square-root identity is asserted. The source's Euclidean quantitative constants and a genuine Gaussian/actual-standardized-cell specialization need the appropriate concrete data. This theorem also makes no standalone identification with an externally defined bar-omega functional beyond its explicitly reviewed real open-ball pair-supremum functional.

Not established here: planar tube/area/perimeter geometry in equation(5), the uniform n^(-7/2) estimate in equation(6) or report equation(9), actual covariance-whitening family and family-uniform constants, the Edgeworth probability comparison, per-cell probability error, summation/full exterior bound, full Laplace probability, or original OQ3 B/D. Source fixed x∈(0,1), strict beta<2/5, actual moment/spectral/WC/global-saddle assumptions, corrected constants, positive-curvature obligations, the far-probability gap, Song/Angst-Poly attribution, p54 repairs and accepted root scope remain unchanged. No novelty certification or additional original-root closure is claimed.

Final individual verdicts: indicator_cell_averaged_oscillation_bound is CORRECT; its generated _simp_1_1 theorem is CORRECT. All final source lines, complete actual owned types and proof-local values are covered. With the verified existing exact-source kernel and whole-owner recursive axiom evidence reused, U22av meets LEAN_FULLY_CHECKED in this precise frozen auxiliary scope. The final integrity check rechecks all reviewed local inputs unchanged and returns this report's SHA256, byte count and line count; afterward this reviewer stops all tools/writes and the lane owner continues.
