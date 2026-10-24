# Independent complete final review: C12 units 97–99

**STATUS: CORRECT.** This verdict binds exactly the three source/object/freeze/receipt versions below. I independently reviewed every new source statement and proof, the original mathematical source, all 33 actual defining-module-owned full types, and the complete non-theorem owner inventory. All 33 owners are theorems; there are no non-theorem values. No critical mathematical or evidence gap was found.

The substantive combined result includes the genuine unit-time, start-zero Brownian identity

\[
P\bigl[\forall t\in[0,1],\ B_t<a;\ B_1\le v\bigr]
+\gamma([2a-v,\infty))=\gamma(( -\infty,v]),
\qquad a>0, v<a, \gamma=\mathcal N(0,1),
\]

where survival is strict at every time and the endpoint cuts are closed. This is the precise unit99 process-probability dependency. Pointwise bridge completion, arbitrary start/horizon, killed/free-kernel identification and the original roots are outside this verdict.

Reviewer: fresh `/root/polygonal_rademacher_final_review`, independent of author chat `01a16c4c-25a6-7740-a10e-12635a13edae`. The prescribed configuration is `gpt-6.1-sol / xhigh`; independently exposed actual model/effort and token telemetry are unavailable, so telemetry fields and input/cached-input/output/reasoning-subset counts are null. No subscription-percentage estimate is made. I used math-theorem, no math-ultra and no children. All writes were confined to this review folder. Production, freezes, prior reports/receipts, shared files, library, Git metadata, cache and server files were read-only. Reviewer Lean/build/audit commands and successful gate replays: zero.

## Exact versions

| Unit | Module | Source SHA256 | Object SHA256 |
| --- | --- | --- | --- |
| 97 | `Shao.C2.PolygonalRademacherReflection` | `a4ae9732231dc0966fff4c4cf99d4fa3f8c5ed0d4ca061fbdb330fb52cbbecee` | `f9f47c3ea012fabf2f47e0e9a7b129f354dad94b8ffdb285c92eb173942c4a72` |
| 98 | `Shao.C2.RademacherBrownianEndpointLimit` | `9d0ac8bd8205c7cd5a4f968eebea0e96d36893915d7acd596d7aba70006e0cb8` | `613ab79b6d865bcebdb7b0c07c44d2d1b888453ea751106adbc49ae9633387ba` |
| 99 | `Shao.C2.BrownianUpperJointReflection` | `8d11c5c0383f1e6867c5a5c41e2c1c9b6ffbefab2e1995cf523b888e165991e3` | `179eb63f1130819dd87d8153534462910294d885262fcbcde26eb26e82471113` |

| Unit | Final freeze SHA256 | Original author receipt SHA256 |
| --- | --- | --- |
| 97 | `11120665a9d13466d1d6d37bc7598da8d9044275d8ebce1c76c4960c7aa1d982` | `9fd8c6ef66dc1a9cc944c8e88d426cb76234a8b2a226cf217d02cf7c0e0689fb` |
| 98 | `b95e219479caf0db9b52e7ff5744c22fced259593e01a3e72dfe0dbeeead1c94` | `9868c6fdcb8eb98b29257285b3abdcdb2f61f12bf4d1473d04856d61438e6317` |
| 99 | `818c0fde98aa6c047fd284a7fc433c3a81087282e2476f6643dd7ea5fdf99080` | `3698622f80c81d3f7a6348c624f6d18fb8195f8f3c5c12a8cc83d03c0d7ad9ee` |

Every current production source equals its successful archived source snapshot; every original successful object equals the installed object. All source bytes are UTF-8 without BOM, LF only, with no CR bytes. The JSON contains every individual owner, full-type/block hash, source location, original operation binding and artifact hash. All production sources contain no `sorry`, `admit`, new `axiom`, `unsafe` or `native_decide`.

## Original source and scope

I read the entire requested original supplement range 4192–4315 from read-only `C:/game/shao/current/c12/supplement.tex`, whole-file SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. It defines strict Brownian-bridge completion as a killed/free-density quotient, its wall and zero-energy conventions, profiles, derivative/PDE/Taylor bounds, and invokes half-line reflection at line4247.

These units provide a finite-reflection-to-Brownian-probability route toward that invocation. Unit97 supplies exact real/floor barrier transport and a rounding bound; unit98 supplies actual moment/weak-limit/endpoint facts for one explicit mesh; unit99 closes the stated Brownian joint identity. The formula is at start zero and horizon one. It does not establish that a previously defined bridge kernel equals a conditional survival function at every endpoint, nor the arbitrary-horizon/start formula, killed/free quotient, interval image/sine equality or derivative/Taylor conclusions. These are classical auxiliary results; no novelty claim is made. C12/OQ3/OQ4/OQ56 original root groups remain OPEN. OQ3 remains PAUSED_BY_USER. The p54 repairs and external-result attribution are preserved. Unfinished unit100 was not reviewed.

## Substantive freezes and retained failures

The chronology below comes from narrowly selected original rollout FileChange/CommandExecution records and completed responses, not file dates or author descriptions. Original added freeze contents reconstruct the retained bytes exactly; original implementation dictionaries reconstruct each first failed source hash in memory without executing those scripts. Removing only theorem proof bodies reproduces the final complete frozen imports/context/heads exactly.

| Unit | Original freeze completed UTC | First implementation FileChange UTC | Successful kernel UTC | All-owner audit UTC |
| --- | --- | --- | --- | --- |
| 97 | 2026-10-24 15:20:11.892 | 15:20:56.624 | attempt002, 15:21:23.406 | 15:22:00.440 |
| 98 | 2026-10-24 15:27:35.241 | 15:28:46.046 | attempt003, 15:32:19.420 | 15:32:38.617 |
| 99 | 2026-10-24 15:34:36.771 | 15:35:56.292 | attempt002, 15:36:28.390 | 15:36:46.688 |

97 froze all five complete heads, including both private helpers. Its only proof repair replaces `ring` by field cancellation using the already-assumed `h>0`, followed by `ring`. The failed goal displays precisely the missing cancellation of `h*h⁻¹`. No head or context changed.

98 initially froze all nine complete heads at SHA256 `6d5adb8f9b39bb160741be06dd11bd2134742282c9745b15fd8981e7292a54a2`. Its retained v2 freeze adds only `β := ProbabilityMeasure C(BridgeTime, ℝ)` to the one weak-path-limit `Tendsto`. Both law constructors were already explicitly annotated with that exact probability-measure type in v1. The first failure is an unresolved `TopologicalSpace {μ // IsProbabilityMeasure μ}` inference, not a proof or counterexample about weak convergence. The explicit codomain selects the intended canonical weak probability-measure topology; its full actual elaborated type was reviewed. There is no mathematical parameter, premise, endpoint event, value, import or other-head change. The v2-only operation completed 15:31:26.323 UTC, before the separate revised-proof command began. V1, its failed source/log and the explicit delta record remain intact.

Other 98 attempt001 errors concern an inapplicable finite-limit `add_const` lemma, evaluation measurability and set-of/preimage presentation. The repaired divergence proof is an actual atTop argument; evaluation uses the explicit measurable-evaluation lemma. Attempt002 then fails only on two reflexive mesh inequalities, closed by `le_refl` in attempt003. I read the initial/final sources, complete intervening deltas and all three full diagnostic logs. All kernels' saved original response logs match their receipt hashes exactly.

99 froze both complete heads. Its sole source delta consistently renames the proof-local scalar `GL` to `gaussCDFValue`; the failed diagnostic shows capture by general-linear-group notation. All downstream errors follow that wrong local type. The repaired source keeps both heads/context unchanged and passes. The failed diagnostic's pretty-printed recovery `sorry` terms are Lean error recovery, not source holes; the final source scan and every-owner transitive axiom audit exclude such terms from the accepted result.

## Unit97: every source proof and its semantics

`measurable_prefix` unfolds the actual filtered finite coordinate sum. Coordinate evaluation is measurable in the finite-product measurable space and finite sums preserve measurability. It works for every natural prefix index, including beyond the path length.

`real_law_preimage` uses the whole proved equality `wordLaw.map realWord = actual real Rademacher pi law`, then `Measure.map_apply` on the explicitly measurable event. The Boolean word domain is finite/countable with measurable singletons, so the complete map is measurable. Applying `toReal` proves the exact real-measure equality without a support slogan or a completeness assumption on another sample space.

`closed_prefix_reflection` takes the integer barrier `H=floor(a)+1` and endpoint cutoff `X=floor(v)`. From `a>0`, integer floor nonnegativity gives `H>0`; floor monotonicity from `v<a` gives `X<H`. Each prefix event is measurable, using countable intersections over natural k and the subsingleton proof index `k≤n`, then the endpoint intersection. All three event preimages are proved exactly: integer-prefix casts `≤a` become integer prefixes `<H`, endpoint `≤v` becomes `≤X`, and the reflected tail becomes `≥2H-X`. The actual finite cardinal reflection identity and `wordLaw_real_card` give the real probability equation by casting the cardinal sum and dividing by the common positive `2^n`. The finite function/subtype spaces exclude the infinite-cardinality zero fallback.

The theorem includes n=0, negative v, integral/nonintegral thresholds, parity and unreachable endpoints. There is no hidden `n>0` or `v≥0` premise. At n=0, all prefixes are zero and the reflected tail is empty under the stated positive barrier and endpoint separation.

`scaled_polygonal_reflection` consumes the complete actual `upperJoint_real_prefix` type with arbitrary increment measure, then applies the preceding theorem at `a*h,v*h`. Positivity of h preserves both required inequalities. Dividing both tail sides by positive h cancels exactly; the endpoint CDF equivalence is `S_n/h≤v ↔ S_n≤v*h`. The exact horizon relation `h²=n` supplies the genuine unit polygonal joint event. Those hypotheses exclude n=0 for this scaled statement explicitly.

`scaled_reflected_cut_bounds` has no a/v sign or ordering premise. If the two floor errors are `r_a=a*h-floor(a*h)` and `r_v=v*h-floor(v*h)`, both lie in [0,1), and the error numerator is `2-2*r_a+r_v`. Its weak bounds 0 and3 follow from all four floor inequalities. Dividing by positive h gives exactly [0,3/h]. The formal field cancellation uses only the declared h>0.

## Unit98: every source proof and its semantics

The private `ae_unit_eval_one` specializes the qualified simultaneous AE continuous-path representative equality at horizon/time one; `1*1=1` gives the actual Brownian endpoint on the same full-measure set.

`rademacher_moments` directly evaluates the actual two half-weighted Dirac atoms. Every real-valued function is integrable at each Dirac atom because its value has finite norm and real singletons are measurable. Finite half-weight scaling and addition preserve integrability. The integral formula is precisely `(f(1)+f(-1))/2`; substitution proves mean0, second moment1 and third absolute moment1, as well as integrability of the third absolute moment. This publicly exposes the literal calculation copied from the qualified producer's inaccessible private helper; it does not change that producer or invoke an unproved moment oracle.

`rademacher_pathLaw_tendsto` supplies the actual law and all proved moments to the qualified general row weak-limit theorem. Here `h_j=j+1>0`, `n_j=(j+1)^2`, the exact square/horizon condition follows by natural casts, and divergence follows by the explicit eventual lower-bound argument for natural casts. The uniform third-moment bound is1. The result is convergence in the canonical weak topology on actual probability measures on continuous unit-interval paths, as confirmed by its complete actual type.

`brownian_endpoint_real` proves measurability of evaluation and its scalar-set preimage, applies the AE-measurable genuine Brownian path pushforward, and uses the private simultaneous endpoint equality. Brownian marginal `HasLaw` at time1 supplies exactly `gaussianReal 0 1`. S is any measurable real set; no endpoint-CDF or reflection assertion is assumed.

`polygonal_endpoint_real` similarly applies the actual finite-product polygonal pushforward to the measurable evaluation event. Its complete preimage equality follows from the qualified exact endpoint identity. It retains arbitrary ν and all declared positive/exact mesh assumptions, without silently requiring probability or moments for this measure-value equality.

The private `endpoint_set_tendsto` applies continuous evaluation's frontier-preimage inclusion. A measurable scalar S with frontier contained in `{r}` has a path-event frontier contained in endpoint=r, whose Brownian path-law measure is zero by qualified unit95. Portmanteau applies to the proved path-law convergence and this null frontier. The limit law is a probability measure, so its relevant ENNReal value is finite and `toReal` is continuous there. Exact polygonal endpoint and Brownian endpoint identities then give normalized-prefix probability convergence. No variable threshold is substituted into a fixed-set theorem.

`rademacher_endpoint_cdf_tendsto` and `rademacher_endpoint_tail_tendsto` specialize to Iic v and Ici v with their proved singleton frontier inclusions. Both cuts stay closed, v is arbitrary, and there is no parity or finite-grid reachability restriction. `rademacher_upper_joint_tendsto` supplies the same actual moments and exact mesh to qualified unit95's all-time joint-event limit. The resulting Brownian survival is strict and the endpoint remains closed; the only extra barrier premise is a>0. None of these convergence results takes moments, convergence, null boundaries or reflection as a new unpaid hypothesis.

## Unit99: complete fixed-cutoff squeeze and boundary passage

The private `gaussian_tail_from_right` defines `r_m=b+1/(m+1)`. Positive denominators and the reciprocal order lemma prove r antitone, hence Ici(r_m) increases. Its union is exactly Ioi b: positivity excludes b in one direction; the Archimedean reciprocal witness gives membership for every x>b in the other. Genuine measure continuity from below gives convergence to Gaussian measure of Ioi b. Finite Gaussian mass permits conversion to real probabilities. Variance1 is nonzero, so Gaussian singleton-nullness and the exact AE interval lemma identify Ioi b and Ici b. This proves precisely the needed right-tail continuity, with no assumed general CDF-continuity premise.

The public theorem uses the genuine fixed mesh, finite product law, joint probability J_j, endpoint CDF F_j, and antitone endpoint tail Q_j(r). Unit97 gives `J_j+Q_j(cut_j)=F_j` and `b≤cut_j≤b+3/h_j`, where b=2a-v. Unit98 gives actual limits for J_j, F_j and Q_j(r) at each fixed r. The real-measure monotonicity use is justified because the actual product law is a probability measure.

Since `cut_j≥b`, `Q_j(cut_j)≤Q_j(b)`, so `F_j≤J_j+Q_j(b)`. Taking the proved fixed-threshold limits gives GaussianCDF(v)≤JL+GaussianTail(b). For every fixed δ>0, the reciprocal witness and eventual natural-index bound prove `3/h_j<δ`; then `cut_j≤b+δ`, so `Q_j(b+δ)≤Q_j(cut_j)` and `J_j+Q_j(b+δ)≤F_j` eventually. Taking those fixed-threshold limits gives JL+GaussianTail(b+δ)≤GaussianCDF(v). Finally δ=1/(m+1) and the private Gaussian-tail limit give the reverse inequality at b. Antisymmetry yields exactly the frozen equation. The directions, subtraction limits, eventual inequalities and final closed endpoint boundary are all correct. There is no circular reflection assumption, numerical approximation, unsupported moving-threshold substitution or pointwise bridge identification.

## Complete actual owners, dependencies and original server evidence

Counts are derived from the actual owner/name maps and exact exports:97 has18 theorem owners (3 public source,2 private source,13 generated);98 has13 (7 public,2 private,4 generated);99 has2 (1 public,1 private,0 generated). Total: **33 full theorem types,11 public source heads,5 private source heads,17 generated theorem owners,0 non-theorem owners and0 non-theorem values**. Full type exports total91,763bytes. All owner kinds are theorem; an opaque/other non-theorem value was not filtered away.

97/99 full types were read directly. For98, I fully read all25 literal-subexpression dictionary entries and the entire encoded13-type stream. Exact recursive expansion round-trips to all62,789 original bytes. This reuses literally identical subexpressions; it is not a claim to reread repeated raw bytes. Every nonrepeated binder, instance and target context was read, including the complete canonical probability topology. The four generated98 types are two reflexive-order proposition equalities and the exact Iic/Ici membership equalities. The13 generated97 types are the floor/cast/preimage/order and nonzero arithmetic helpers detailed per owner in JSON. Giant generated theorem proof-value certificates were not unfolded; every production source proof and all actual types were reviewed completely, and all recursive axioms were checked.

The exact fresh qualified complete reviews for91–92,93 and94–96 are reused, not recommissioned. Their complete Markdown reports and release records were read and their JSON/Markdown/release hashes bound. Qualified JSON hashes are respectively `013d75bb939e71d4f4299fd59174ae743dd89268f11be530bad3797b7c7f9c40`, `77495bac0a4e8a9e1348e8d65aa47f01645bf777f09178ee426f50ac5f297ab5` and `881694bfe0e4c1e4f893705c1a7a08b083be92dbdcda093fe2613a6a2cb6c4e0`. Release hashes are `eea5de0dbb94f6503cfd75cbef34d17ddb5ee4e9b772033d56cbfca5d3d95be7`, `4ff8c371a12c25bc6fa88527c3d2c820f17388d65b63cc5e1d22de4cf5b7b454` and `adcfa54c1908d7be8282ffc493f966dea1fa54979f022f90fe89b42e15bfbcf3`.

The complete consumed actual cardinality/probability/prefix types and full relevant definition values were read, including boolStep, the actual integer-prefix recursion, boolCoin, wordLaw, realWord, actual Path/prefixSum, the two-atom real law, upperJointSet and the genuine polygonal and Brownian pushforwards. The actual weak-limit, simultaneous representative, probability, endpoint-null, row-joint and exact polygonal-endpoint interfaces were read completely. A separate complete lossless dictionary and encoded dependency stream round-trip to50,967bytes. Exact prior per-owner blocks or original complete export hashes bind those interfaces. Current remote source/object pairs match their qualified versions. The actual Rademacher law also remains bound to accepted v71 source/object reuse; no old producer was recompiled. Direct97/98 consumers in99 are reviewed within this same combined report.

The needed pinned Mathlib declarations/proofs and enclosing contexts were read for floor/cast arithmetic, measurable finite sums/projections/countable intersections, pushforward application, finite Dirac moments and Bochner integrals, continuous evaluation/frontier preimages, Portmanteau, real-measure monotonicity, reciprocal witnesses, Gaussian singleton-nullness and interval/measure continuity. The21 consumed Mathlib files were byte-compared with commit `807d3836b165983210ee2ecf3cd28f239436949c`. This addresses the retained cached-checkout local-change warning for these actual APIs without asserting that the entire checkout is clean. All probability/finiteness, countability, measurable-singleton, complete-real target, continuity and positive-denominator conditions are discharged at use sites.

Read-only server verification matched49 artifact/source-snapshot/current-source/object/receipt bindings across97/98/99 (15/19/15). Every original audit's complete type stream equals the exported full-type file; its non-theorem value export is empty. All residual audit text was read and consists only of the cached-checkout warning and the matching final counts. Every kernel log, original exit marker and every-owner axiom row was checked. The audit programs select by exact `env.getModuleIdxFor?` defining-module identity across all names, including private/generated/other namespaces, and apply recursive `Lean.collectAxioms` to every selected owner. All33 rows lie within exactly `{propext, Classical.choice, Quot.sound}`.

Original commands activate before changing to `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`, then use `c12-heavy.lock`, CPU14–17, native `-M8192 -j4`, Lean `leanprover/lean4:v4.36.0-rc1`, the pinned Mathlib commit and shared-v34 packages. The read-only current branch/head are `author/c12-brownian-reflection-v71` / `7b900d279af5a6e1a8827d7feaa7b80970559b38`. Reviewer heavy commands, Lean/audit/build invocations, producer recompiles, server/cache writes, objects produced and successful gate replays are all zero. Raw logs, binaries, objects and caches were not downloaded into the local workspace.

## Release

These three exact versions are independently CORRECT within the combined scope above. Their original successful source-bound kernel and every-owner recursive-axiom receipts are reusable together with this report. `writer-release.json` binds the complete Markdown/JSON reports and all three exact source/object/freeze/receipt versions. Review-folder writer and execution authority are released, heavy activity is false and in-flight operations are empty. No production write authority was taken. The parent may continue the separate pointwise bridge/completion dependency; this reviewer turn ends and does not claim persistent execution or root closure.
