# Independent complete final review: C12 units 94–96

**STATUS: CORRECT.** This verdict covers only the three exact source/object/freeze/receipt versions below. I independently read every source declaration and proof, the original mathematical source, all 31 actual module-owned types, and all three complete actual non-theorem values. Unit 96 has no non-theorem owners and its value export is exactly empty. No mathematical or evidence gap was found.

Reviewer: fresh `/root/brownian_joint_limit_final_review`, separate from author chat `01a16c4c-25a6-7740-a10e-12635a13edae`. Prescribed configuration: `gpt-6.1-sol`, `xhigh`. Actual model/effort/token telemetry is not exposed; the JSON records unavailable telemetry and input/cached-input/output/reasoning-subset counts as null. No subscription-percentage inference is made. I used math-theorem, no math-ultra, and no children. All writes were confined to this review directory. Production, freezes, old reviews/receipts, library, shared coordination, cache and server files were read-only.

## Exact version bindings

| Unit | Module | Complete source SHA256 | Object SHA256 |
| --- | --- | --- | --- |
| 94 | `Shao.C2.BrownianUpperBoundary` | `52a7fd9c460bc1f4fbaf2e9142231ab79d3e13317a771dc439b29b6d6bf27e36` | `d9e43a49668b3f238faaa4c0076da11190b92d7b9625d337c7d96d36b75baeb2` |
| 95 | `Shao.C2.BrownianUpperJointLimit` | `a62a9073f064d7a1dce64b27d9b5ff4bff047a5dd71f12018c9de98fa2ae25b4` | `bdec7064edc97a72a1738cfd417e4eeb4b3ede656bb2ab1f56c73118162a3274` |
| 96 | `Shao.C2.PolygonalPrefixEvents` | `9b304eea42ad006805199354a6bd47aa6f6f41c559f3aec8c5e9c10baa06d258` | `b6baaa9e3a341612ba7d8d4a4f6cdbd74894a8438ad96b5302f921cfcae706fc` |

| Unit | Freeze SHA256 | Original author receipt SHA256 |
| --- | --- | --- |
| 94 | `89caa8744d8e7afda3feefbb96e2ac22fe107d8d656abdf34465c8c9b78a061e` | `7189e69be099a469ab075a1cdcb3edddc28e1dc69d4234c7904aa71f63091537` |
| 95 | `d964c5ea98103c2ee8cdcaf49a89c35ffd16e148b74c4fc8379d40e015882f04` | `ac9dcdaa3caccfd883fb61de28702e7be0d3d8ae80909daaf9c2725e5dc5f735` |
| 96 | `a9a74a4916b78b85c087900111b8a5fec06950b8e1bc87fc9e796f819fc088b1` | `b80a187fa1c4e55c008dc00d22c977bfd7b217a080eb84d9c31055c6f6586259` |

The full JSON contains every individual actual owner, full-type/block hashes, complete-value/block hashes, source locations and evidence bindings. Source files are UTF-8 without BOM with LF line endings and zero CR bytes. Lexical scans of the actual production sources find no `sorry`, `admit`, new `axiom`, `unsafe` or `native_decide`.

## Original source and accepted scope

I read the complete original read-only `C:/game/shao/current/c12/supplement.tex`, lines 4192–4315, within the supplied target excerpt. Lines 4194–4206 specify the monitored interval/half-lines, interior positive-time strict Brownian-bridge completion, its killed/free-density interpretation, and separate degenerate extensions. The proof invokes half-line reflection at 4247; the subsequent image/sine arguments, derivative/PDE claims and compensated Taylor remainder are distinct obligations.

These modules close three preparatory dependencies toward that reflection invocation: an actual Brownian upper-touch null event, a continuity-set weak-limit transfer, and exact finite polygonal/prefix-event identification. They do not prove a numerical reflection formula or the killed/free quotient. Unit 94 uses the explicit amplitude-scaled unit-interval process `y + sqrt T * B(t)`. It does not identify it samplewise with elapsed-time `B(T*t)`. Unit 95 is at time one/start zero with positive wall `a`, arbitrary endpoint cutoff `v`, and all row hypotheses visible. Unit 96 uses the chosen exact mesh `h > 0`, `h² = n`; it does not assert the event equivalence for mismatched horizons.

All original C12/OQ3/OQ4/OQ56 root groups remain OPEN. OQ3 remains PAUSED_BY_USER. The p54 repairs, source scope and external-result attribution are preserved. Unit 97 is outside this review. These are standard auxiliary probability/topology/mesh arguments, with no new-theorem novelty or conference-value claim.

## Substantive freeze before implementation

I narrowly parsed 19 original FileChange/CommandExecution records from the actual author rollout, without dumping session metadata or rerunning any command. Each complete original freeze content equals the archived frozen bytes. Deterministically removing only theorem proof bodies from each final source reproduces its complete frozen imports/context/heads/literal definitions exactly.

| Unit | Original freeze completed UTC | First implementation record UTC | Kernel history | Whole-owner audit |
| --- | --- | --- | --- | --- |
| 94 | 2026-10-24 14:59:45.059 | 15:02:02.626 | attempt001 PASS | PASS |
| 95 | 2026-10-24 15:05:55.842 | 15:07:10.399 | attempt001 FAIL; attempt002 PASS | PASS |
| 96 | 2026-10-24 15:15:45.717 | 15:16:23.614 | attempt001 FAIL; attempt002 PASS | PASS |

The timestamps are from the original rollout, not file modification times. I also checked start/completion millisecond ordering. All five public heads plus the entire `upperTouch` value were frozen for 94; all nine heads including its private helper plus both entire Set values for 95; all six heads including its private segment helper for 96. No assumptions or literal definitions changed after those freezes.

I read the complete failed sources and complete failed/successful diagnostic logs for 95/96 from the server, and verified their receipt hashes. For 95 the two proof changes give an explicit type to the closed endpoint cut and expose the preimage as a set-of before `HasLaw.measure_eq`. For 96 five proof changes explicitly simplify `NNReal.coe_one` and the local variables `x`/`t`. Its pre-first-gate change merely supplies the already-assumed `h ≠ 0` to `field_simp`. All are proof elaboration/normalization changes; no signature, event, scale or hypothesis changed. The exact failed-log bytes also match the diagnostic captured by the original command response. Failure evidence is retained.

## Unit 94: complete proof and semantic review

`upperTouch` is exactly the conjunction that the affine endpoint-parameterized bridge stays at most `a` at every `BridgeTime` and equals `a` at some such time. It is not a countable-grid substitute or a numerical reflection assumption.

`upperTouch_section_subsingleton` fixes arbitrary pinned continuous noise `g`. If coordinates `q < r` both qualify, choose a touching time of the `q` path. That time cannot be zero because the bridge starts at `y < a`; hence its real coordinate is positive. The path increase is `t * sqrt(T) * (r-q) > 0`, using precisely `T > 0`. Thus the `r` path is above `a` there, contradicting its closed upper bound. Applying this argument both ways proves equality of the two coordinates. This does not assume monotonicity of a maximum functional or that a touch occurs before the terminal time.

`measurableSet_upperTouch` proves the parameter-to-continuous-path map continuous by the continuous uncurried evaluation formula. The strict all-time upper set is open in the compact-open topology because the entire time domain is compact and the target `Iio a` is open. The all-time closed set is an arbitrary intersection of closed evaluation cuts; arbitrary closed intersections are valid. The touch set is exactly closed survival minus strict survival, proved in both directions using the closed inequality. Its measurability follows. There is no invalid uncountable intersection of merely measurable sets.

`product_upperTouch_zero` installs Gaussian singleton-nullness with the checked nonzero variance `1`. Each endpoint section is either empty or a subset of a singleton, so its Gaussian measure is zero even before asking for section measurability. Genuine `Measure.prod_apply` applies to the jointly measurable event and the Gaussian's s-finiteness. The resulting nonnegative integral is identically zero. The arbitrary bridge law `ν` is not chosen to encode the conclusion; it is a stated probability measure.

`brownian_upperTouch_zero` uses the already-qualified genuine joint law of `(bridgeNoise B, B 1)` and the simultaneous AE identity `g(t)=B(t)-t*B(1)`. Expanding the bridge formula cancels the endpoint term for every time on the same full-measure set. Thus the raw all-time Brownian event is AE equal to the measurable joint-law preimage; `measure_congr`, `HasLaw.measure_eq` and the product null result yield zero. No hidden completeness assumption on the original sample space is used, and no AE-for-each-time assertion is exchanged for a simultaneous one.

`brownian_upper_strict_closed` excludes that entire null touching event. On its complement closed survival implies strict survival at every time; strict survival always implies closed survival. `measureReal_congr` therefore gives the stated equality. The only additional generated theorem is the complete propositional double-negation equality type, which I read; it introduces no probability premise.

## Unit 95: complete proof and semantic review

The two full values are literal path-space sets: `upperJointSet a v` requires all-time `f(t) ≤ a` and `f(1) ≤ v`; `upperBoundarySet a` is closed upper survival minus strict upper survival. They contain no chosen measure, opaque oracle, convergence assumption or modified path.

The private `ae_unitPath_eq` specializes the qualified simultaneous continuous-representative identity to horizon one and simplifies `1 * t = t`. All later transfers use this same AE identity. The closed joint set is an intersection of the closed all-time cuts and a closed endpoint cut. The boundary difference is measurable by the same compact-open strict-event argument as 94.

`frontier_upperJointSet_subset` first uses closedness to obtain membership in the joint set together with nonmembership in its interior. Outside `upperBoundarySet`, that membership forces strict upper survival. If the endpoint equality also fails, the already known endpoint inequality is strict. The intersection of the open strict path condition and the open strict endpoint condition then supplies an open neighborhood contained in the joint set, a contradiction. Both possibilities in the claimed union are therefore covered; no uniform margin is assumed without the compact-open argument.

`brownianUnitPathLaw_upperBoundary_zero` applies the genuine AE-measurable pushforward formula to the measurable boundary set, then identifies its preimage AE with the closed-and-touch raw Brownian event and applies 94 at `y=0`, `T=1`. The hypothesis `a>0` exactly discharges `y<a`. `brownianUnitPathLaw_endpoint_zero` similarly identifies evaluation at time one with `B(1)`, uses the actual Brownian marginal law `gaussianReal 0 1`, and invokes singleton-nullness. The cutoff `v` is unrestricted.

`brownianUnitPathLaw_joint_frontier_zero` combines the proved frontier inclusion with the union of these two null sets. `brownianUnitPathLaw_upperJoint_real` transfers the closed joint event to the raw process and excludes only the upper-touch null event, retaining the closed endpoint inequality. It does not silently replace the endpoint cutoff or interchange strict and closed endpoint events.

`row_upper_joint_tendsto_brownian` consumes the exact qualified row weak-limit theorem for actual polygonal path laws. Its hypotheses retain probability row laws, integrable third absolute moments, mean zero, second moment one, a uniform third-moment bound, positive scales tending to infinity, and `h_j² ≤ N_j`. At horizon one that last condition is exactly the old theorem's required `T*h_j² ≤ N_j`. Portmanteau applies to the proved null frontier in the actual continuous-path space. The limiting measure is a probability measure, hence the relevant ENNReal value is finite; continuity of `toReal` is used at that finite value. The preceding joint-real identity gives exactly the strict Brownian upper-survival/closed endpoint event in the result. No numerical reflection law or FDD/tightness hypothesis is newly assumed.

I also read both complete additional generated types: the double-negation equality and `Shao.OQ4.PolygonalBrownianWeakLimit.brownianUnitPathLaw.eq_1`. The latter is owned by this new defining module despite its older namespace; its full type states the literal pushforward equality. It is included in the 13-owner audit and this review, not omitted by a namespace-prefix filter.

## Unit 96: complete proof and semantic review

The private `exists_segment` handles every `0 ≤ x ≤ n` with `n>0`. If `x<n`, natural floor and its bounding inequalities provide the segment. Otherwise `x=n`, and `n-1` is the last valid segment. In particular the closed final endpoint is not lost through a half-open grid convention.

`unitPolygonalPath_one` specializes the genuine ramp-path grid identity at `k=n`; `h²=n` and positivity reduce its time to one. `unitPolygonalPath_segment` derives `n>0` from the explicit scale assumptions, sets `x=t*h²`, chooses the segment, and takes `θ=x-k` in `[0,1]`. The existing on-grid-interval identity yields the exact affine combination of neighboring normalized prefix sums. All equalities use the already-qualified actual ramp-sum polygonal path and its unit-interval wrapper.

For `unitPolygonalPath_le_iff`, evaluating at each actual grid time `k/h²` proves necessity for every `0≤k≤n`. Conversely every time is the affine combination above; multiplying both neighboring prefix bounds by the nonnegative interpolation weights proves the all-time bound. Multiplication/division uses `h>0`, with the correct barrier `a*h`. The empty prefix `k=0` is included; no positive-wall restriction is silently introduced.

The strict version uses the same grid necessity. For sufficiency, `θ=1` is handled directly by the strict upper endpoint bound. Otherwise `1-θ>0`, so the lower endpoint's strict bound and the upper endpoint's weak consequence give a strict affine-combination bound. This covers both interpolation endpoints and interior times, with no assumption that both weights are positive.

`upperJoint_real_prefix` unfolds the genuine finite-product pushforward, applies `Measure.map_apply` using measurability of the actual unit polygonal observable and closedness of the actual joint set, and proves its preimage equality by the closed all-time equivalence and endpoint identity. The resulting event has exactly the same `k≤n` quantifier and endpoint barrier `v*h`. The increment measure `ν` is arbitrary: this is an equality of `Measure.real` values; it has a probability interpretation when `ν` is a probability measure. No probability, moment or independence premise is secretly added; the product law itself is explicitly present on the right.

All eleven actual owners are theorems. Besides the six source heads there are four generated natural-arithmetic contradiction types and the externally named `Shao.OQ4.PolygonalPathTightness.polygonalPathLaw.eq_1` literal pushforward equality. I read every complete type, including both generated private names and both arithmetic `k+1≤n` obligations. The full actual value export has SHA256 of the empty byte string because there are zero non-theorem owners, not because values were filtered away.

## Complete actual-owner and dependency coverage

Counts are derived from the exact actual owner maps and exports, not copied from historical narrative: 94 has 7 owners (6 theorem/1 definition), 95 has 13 (11/2), and 96 has 11 (11/0). Total: **31 owners, 28 theorem types, 3 definition types and 3 entire definition values; 18 public source theorems, 2 private source theorems and 8 generated theorems.** The selected defining-module test covers private/generated owners and other namespaces. No owner kind is `other` and there is no opaque non-theorem value omitted from the coverage.

The entire expanded streams for 94/95 were read through an exact literal-subexpression dictionary; all dictionary entries and all four encoded streams were fully read, and expansion recovers each original byte stream without normalization or loss. The complete 96 type export was read directly. No ellipsis, missing metavariable, selected-head-only display or giant generated proof-value expansion substitutes for reading the actual types. Giant generated theorem proof certificates were not unfolded, as permitted; all source proofs and actual non-theorem values were read completely.

For existing dependencies I reused the exact qualified independent complete reviews, rather than repeating their full proof reviews. I read the complete actual consumed types and entire values for the bridge/noise/path/law interfaces, the actual Brownian representative and path-law weak-limit interface, the actual finite polygonal wrapper/product pushforward, and the ramp/grid/affine interfaces. The source definitions and enclosing namespace/instance contexts were also read. The two direct B3 grid/affine source proofs and relevant ramp helper were read in full as requested for the newly added unit 96.

The old bridge-interface type/value hashes match the corresponding all-owned coverage in the qualified reviews. The OQ4 complete PP exports match their original accepted manifest/qualification hashes. Current remote source/object pairs match those qualified versions for BridgeDomination, BrownianBridgeLaw, BridgeEndpointIndependence, RademacherReflectionProbability, PolygonalBrownianWeakLimit, PolygonalPathTightness and PolygonalThirdMomentB3. The three OQ4 source versions also match the accepted v71 source map. In particular the row weak limit is an actual proved theorem, and 93 is only an import dependency of 94, not a hidden Brownian reflection assumption. The dependency JSON files retain all exact qualification hashes.

I read complete needed pinned declarations/proofs and enclosing contexts for `Measure.prod_apply`, Gaussian singleton-nullness, the compact-open open-set and currying facts, the probability-measure Portmanteau null-frontier theorem and its squeeze proof, and the natural-floor segment inequalities. Each consumed Mathlib source file was byte-compared with the pinned Git commit, which addresses the general cached-checkout local-changes warning for these actual APIs. Required s-finiteness, nonzero Gaussian variance, open-measurable/path topology, compactness and finite limiting measure conditions are discharged at their use sites.

## Server/kernel/axiom evidence and resource boundaries

All Lean evidence is original server evidence. Reviewer Lean/build/audit commands: **0**. Successful gate replays, old producer recompilations and newly produced objects: **0**. I performed only local deterministic text/hash extraction and bounded read-only remote queries.

The server hashes verified 40 receipt-artifact/source-snapshot/current-source/object/receipt bindings across the three units (12/14/14). Complete actual-type and value exports equal the corresponding complete original audit-log blocks; all residual text was read and consists only of the cached-checkout warning and final matching owner counts. Successful source logs contain only style/deprecation warnings. All original kernel and audit exit markers were recovered from the author rollout and agree with the artifacts.

The audit program iterates all environment constants, checks `getModuleIdxFor?` against the actual defining module and applies recursive `Lean.collectAxioms` to every selected constant. I read each complete audit program and every per-owner axiom row. Every row is a subset of exactly `{propext, Classical.choice, Quot.sound}`; 96's four arithmetic certificates use the smaller `{propext, Quot.sound}` subset. No source-prefix or public-only selection was substituted for defining-module ownership.

Original command records use the pinned `leanprover/lean4:v4.36.0-rc1`, Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, shared read-only `cache-overlays/shared-v34/packages`, the C12 worktree, `c12-heavy.lock`, CPU14–17, native `-M8192 -j4`, and activation before changing to the worktree. The current pins/cache path were confirmed read-only. No local Lean execution, cache mutation, `lake update`, full Mathlib rebuild or external CPU0–9 action occurred.

The historical 94/95 gates were on `author/c12-interval-identification-v71` at `23cc8da1f557e76c447cf9fadbcecc9e89024181`. The parent subsequently published the already-qualified 88–93 packet as PR308 and continued on `author/c12-brownian-reflection-v71` at `7b900d279af5a6e1a8827d7feaa7b80970559b38`; 96 was checked there. This legitimate metadata progression is recorded separately from the original 94/95 gate bindings. Their source/object/freeze/receipt bytes have not changed. It is not a reason to replay passed checks.

## Release

The exact three versions are independently CORRECT within the auxiliary scope described above. The source-bound original kernel and every-owned recursive-axiom receipts are reusable at acceptance together with this review. Writer and execution authority for this review are released with no heavy work and no in-flight operations; `writer-release.json` binds this report, the complete JSON and every source/object/freeze/receipt version. This final answer ends this reviewer turn; it does not claim continuing execution or authorize a new owner to write production.
