# Unit 47 HalfLineGaussianStep: independent final complete review

**STATUS: CORRECT.** The exact frozen scalar half-line retained-remainder module has a complete proof. I found no critical gap in the full source-to-statement translation, the proof, any of its 22 actual owned types, or its three complete transparent definition values. This qualification is restricted to the explicit normalized scalar model. Actual Brownian probability identification and the original root groups remain open.

Reviewer: fresh independent FINAL context `/root/halfline_gaussian_step_final_review`, separated from the author. The prescribed invocation and registry are `gpt-6.1-sol/xhigh`; the host exposes no independent model-introspection or usage-counter field. The report therefore preserves that provenance and records unavailable actual-host and input/cachedInput/output/reasoningSubset counters as null. No subscription percentage or credit allocation is inferred. I used math-theorem and the current streamlined acceptance policy; no math-ultra, Goals, automations, sidebar threads, subdelegation, Lean run, toolchain installation, or production/shared-source write occurred.

## Exact scope and byte bindings

| Item | SHA256 |
|---|---|
| Final source, all 251 lines / 12301 bytes | `3c68c45c8eea27148d9929939458f069aa63abb6415a5c86603b0627c2d8eb35` |
| Successful output and installed object | `180c37ee880f0113c25648a9fa36e98ce2739c6cd6a43900b68386f3e1666b46` |
| Frozen imports, all nine public heads and three complete values | `27239638d6a984e60a8d124e7446be4b83bd87e181700774c85f26ef4f49e353` |
| Author source-bound receipt | `c6a0fd4b782b5dd903c0db13d019df5b1fab3b564552b7cbf7f577d3d9fb112b` |
| Complete actual types, 32230 bytes | `54318daab9cf2d263787069973e535301eca7e52b9a33414162d6aaf90fba10f` |
| Complete actual definition values, 6520 bytes | `1ec5256af99a08ee2f34f639c50d970c76a77ee582f780ab5205eb2b6ae10d2b` |

The source is UTF-8 without BOM and with LF endings, CR count zero. I read the whole source and all proofs, the complete frozen declaration file, all 22 full elaborated type blocks, and all three full elaborated values directly. No sampling, abbreviated type or lossy/dictionary compression was used. A byte-exact proof-body removal independently reproduces the frozen imports/context, heads and values. Both saved attempt001 and attempt002 have this same complete projection. Chronological freezing was supplied by the coordinator's pre-implementation packet; the directly observed evidence here establishes exact preservation in both saved implementation versions.

The actual owner map, type-export set and value-export set agree by exact name. There are **22 owned constants: 19 theorem constants and three definitions**, with nine public theorems. The ten generated auxiliary theorems comprise seven compensation `_simp` lemmas, two equation lemmas, and the completion numeral proof. No unknown constant kind or unreviewed generated definition appears. The machine report records every declaration's full-type hash, complete value hash when applicable, source location, axiom list and specific review.

## Original source and normalized meaning

I read the complete readonly `C:/game/shao/current/c12/supplement.tex` passages 4192–4253 and 4319–4398. Its whole-file SHA256 is `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. The former introduces strict Brownian bridge completion, absorbing spatial extension, reachable zero-energy interior value one, the full compensated remainder and the small Taylor estimate. The latter gives projection and the one-local-Gaussian-envelope estimate and its case proof.

For a wall sign η, take u=a−ηy, v=a−ηz, normalized b=η times the original displacement and e=u−v=η(z−y). Thus the future distance is u−b, variance is T−b², D=1+|u−v|/√T, q=|b|/√T, and the single-wall envelope is

`Π = exp(-max(u-(|b|+max(u-v,0)),0)^2/T)`.

For the reflection formula, the oriented original derivative is f_y=−η*slopeTime, so the original `(original_b−original_b²*d/T)*f_y` becomes exactly `(b−b²*(u−v)/T)*(-slopeTime)`. The normalization therefore preserves the full time compensation and works for either wall orientation. It is not merely the first-order term b*f_y.

The new `completion` explicitly defines this scalar reflection model. If either endpoint is nonpositive it returns zero. For positive endpoints and T>0 it returns 1−exp(−2uv/T); at T=0 and equal positive endpoints it returns one, and all other nonpositive-time cases return zero. This does not modify any existing interval completion or spatial-cut convention, prove a killed-kernel/Brownian probability identity, or claim the separate terminal deterministic-interpolation convention for different zero-variance endpoints. The new estimates assume initial u,v,T>0 and b²≤T, so their future variance is nonnegative; negative-time total-definition branches are not used.

`localRemainder` has the exact future/old completion difference and full compensation. `retainedRemainder` selects the full projected remainder with displacement u precisely when b²≤T/2 and u−b≤0, including equality hits, and selects displacement b otherwise. This is the original retained ℓ in normalized scalar form. The source's additional negative-overshoot term is interval-only at line4371; this module does not assert an interval estimate or retain a separated positive overshoot.

## Complete public proof review

Write F=completion(u,v,T), Fnew=completion(u−b,v,T−b²), S=T−b², s=√T>0, q=|b|/s, t=|u−v|/s, D=1+t and Π for the envelope above.

1. **completion_positive_time** (line24) retains the complete assumptions u≥0, v>0, T>0. If u>0 the definition gives the formula; otherwise u=0 and both sides are zero. It includes the one-sided wall trace without replacing a closed condition by a strict one.

2. **completion_bounds** (line32) quantifies arbitrary real u,v,T. Failed endpoint guards give zero. Positive endpoints and positive time give exponent≤0, hence 0<exp≤1 and 0≤F≤1. At nonpositive time the two remaining branches are exactly zero or one. Both conjuncts and every branch were checked.

3. **completion_reachable_zero_time** (line45) preserves u>0, v>0 and u=v; the complete definition reduces to one. It does not assign one to an absorbing wall or to an unequal endpoint.

4. **compensation_envelope_bound** (line49) uses b²≤T to derive |b|≤s and q∈[0,1], hence q²≤q. The qualified unit32 j=1 reflection-power bound, complete unit34 slopeTime value and unit46 initial-profile comparison give `0≤slopeTime≤8DΠ/s`. The triangle bound for the full coefficient is `|b−b²(u−v)/T|≤|b|+b²|u−v|/T`. Multiplication and T=s² normalize it exactly to `8(q+q²t)DΠ≤8(q+qt)DΠ=8qD²Π`. All multipliers are nonnegative; all division/cancellation uses s>0 or T>0. No future positivity or reachability is silently assumed here.

5. **future_deficit_envelope_bound** (line98) keeps S≥0 and explicitly splits S=0. In the zero case, the frozen `hzero : S=0 → u−b=v` and v>0 imply a positive equal-endpoint future, so Fnew=1 and its deficit is zero. In the other case S>0. The closed-distance formula at u−b≥0 turns the deficit into exp(−2(u−b)v/S), and unit46's strictly-positive-future comparison applies with w=u, e=u−v<u. Its `0<S` assumption is never used at zero energy.

6. **completion_difference_envelope_bound** (line113) uses the complete global completion bounds. At nonnegative future distance, `|Fnew−F|≤(1−Fnew)+(1−F)`. The preceding theorem bounds the future deficit; `exp(−2uv/T)≤exp(−uv/T)≤Π` bounds the initial one. Thus the difference is at most2Π. At strictly negative future distance, Fnew=0 and u≤b≤|b| makes Π=1; the difference is F≤1≤2Π. Equality future distance belongs to the nonnegative branch and is covered. hzero remains explicit throughout.

7. **local_small_envelope_bound** (line145) derives S≥T/2>0 from b²≤T/2. It fully unfolds unit36's completionAlongSegment and unit35's distance/energy values at θ=0 and1, then uses completion_positive_time for both endpoints, including u−b=0. Unit38's exact qualified compensated Taylor bound has the same compensation, old slope and constant8000100. Unit46 gives incrementProfile(u,v,T,b)≤Π with e=u−v. The multiplier is nonnegative and `|b|³(1/√T)³=(|b|/√T)³`; the final conversion is an identity, not a changed estimate. Reachability is unnecessary because this regime has positive future variance.

8. **local_large_envelope_bound** (line163) covers T/2<b²≤T. Here q²=b²/T>1/2, q≥0 and q≤1. The proof correctly derives q≥1/2 and `1≤4q³`. D≥1 yields 1≤D³ and qD²≤D³. The full local remainder triangle inequality and the two preceding envelope bounds give

   `|R_b|≤(2+8qD²)Π≤10D³Π≤40q³D³Π≤8000100q³D³Π`.

   Every monotone multiplication has a nonnegative factor. No division by q or future S is used. The difference bound covers large surviving futures, large crossings, and the reachable zero-energy interior; hzero remains in the complete actual statement.

9. **retained_envelope_bound** (line223) exhausts small versus large, then small crossing versus survival. At a small crossing, 0<u≤|b| gives u²≤b²≤T/2. Apply the small theorem at displacement u: the projected future distance is exactly0 and its energy is at least T/2>0. Unit46 makes both the projected and original crossed-wall envelopes1. Since `(u/√T)³≤(|b|/√T)³`, its cubic bound transfers to the retained remainder. At a small surviving step u−b>0, apply the small theorem at b. At every large step apply the large theorem at b with the original hb and hzero. Threshold b²=T/2 belongs to the small regime; equality wall hits belong to the crossing regime. b=0 is covered as a small surviving step and produces zero remainder.

The final theorem consequently has precisely the frozen scope: for positive u,v,T, b²≤T and explicit reachable-zero-energy premise, `|retainedRemainder|≤8000100 q³D³Π`. It does not discard the time-compensation term or attempt to prove an arbitrary unreachable zero-time deficit formula.

## Complete generated and definition coverage

All three definitions' entire elaborated lambdas were read, not only their Real-valued types. The full `completion.eq_1` type repeats every guarded branch and real decidability instance; `localRemainder.eq_1` repeats the exact future/old subtraction and full oriented compensation. Their complete equation types match the source values. The remaining generated theorem types are:

| Generated suffix | Full mathematical content of the actual type |
|---|---|
| completion._proof_1 | Nat.AtLeastTwo(1+1), used to elaborate numeral2 |
| compensation..._simp_1_1 | Zero α, OfNat2 and NeZero2 imply proposition2=0 equals False |
| compensation..._simp_1_2 | Zero α, OfNat3 and NeZero3 imply proposition3=0 equals False |
| compensation..._simp_1_3 | Zero α, OfNat4 and NeZero4 imply proposition4=0 equals False |
| compensation..._simp_1_4 | Mul, Zero, NoZeroDivisors, a≠0 and b≠0 imply propositionab=0 equals False |
| compensation..._simp_1_5 | MonoidWithZero, IsReduced, arbitrary Nat n and a≠0 imply propositiona^n=0 equals False |
| compensation..._simp_1_6 | GroupWithZero, arbitrary Int n and a≠0 imply propositiona^n=0 equals False |
| compensation..._simp_1_7 | AddMonoidWithOne, CharZero and arbitrary Nat n imply proposition(n:R)+1=0 equals False |

The entire universe binders and typeclass paths were read in the original full export, including unrestricted natural/integer exponents and every nonzero premise. These generated proofs come from the fully reviewed source tactics and exact successful kernel object. They introduce no new mathematical assumptions. Every generated item is also in the actual-owner recursive axiom audit; there is no reliance on a namespace-prefix/public-only count.

## Consumed qualified interfaces and interactions

I reused the existing qualified independent complete proof reviews of units46,38,32,35,34,36. I did not recompile or repeat their old full-proof reviews. All six current server sources and installed objects match their exact reviewed source/object versions; all corresponding review writer/execution releases are true. Complete consumed source declarations, complete actual types and all consumed transparent values were read and bound in `consumed-interfaces.json`.

| Unit | Interface consumed | Independent review JSON SHA256 |
|---|---|---|
|46 GaussianWallEnvelope|wallEnvelope full value; bounds; initial and increment profile comparison; future reflection deficit with strict positive future time; crossed-wall value1|`4bec1714422c76be2a390fb6af2b1e44dfcec5f886148db2bb1e5e5914850ff9`|
|38 HalfLineSmallTaylor|complete compensated_small_taylor_bound, including hu,hv,hT,hsmall,hnew and constant8000100|`8fc5acf53a830dfdd128d483918570501f75121c483f1d7cb74259bb072d3523`|
|32 HalfLineSpatialProfiles|positive_reflection_power_profile with j=1 and hj>0|`207cdaed8fd92e51545abfdc8cbebb5e31e83392f457a40f2b18fcb788a95b81`|
|35 HalfLineTaylorSegment|segmentDistance=u−θb, segmentEnergy=T−θb², incrementProfile=exp(−max(u−|b|,0)v/T), all complete actual values|`0ff0cc92f656a87761ab28d636b7c4d141b13f4d0c89ad874e0273fec9f6fae7`|
|34 HalfLineMixedProfiles|slopeTime=(2v/T)exp(−2uv/T), complete actual value|`08f1a0c45b250d3763b38dec80a1b5e834af6e55a474f0fbfa5f41d5646d90a3`|
|36 HalfLineTaylorPath|completionAlongSegment=1−exp(−2*segmentDistance*v/segmentEnergy), complete actual value|`18e6ccf8ab0d013d9875b864153a48fbe4c587a464149366455312be19e9f2ee`|

Unit46's now-qualified full Markdown review and release were read, including its strict positive-future restriction. Its source is `5f8b3966e314c88f5091a5e7bf7353be0ec0cae4d6cf2842b83bc61a436d06d9`, object `54a9bd090e395db8d447e3cb095ef7a6e6ab9ec482a95150e20fe3a77a657e45`; its joint review release SHA256 is `138dbb4a3c160a37de181d1d76b9e2552773e8709cf92e4b5a6dc5f93d3a5850`. The author's earlier note that46 awaited review is historical, not the current dependency state. Unit47 imports46 and38 and adds no changed old definitions or overlapping owner names.

## Existing server kernel and complete recursive-axiom evidence

I made one bounded read-only server observation, with no Lean command or execution/heavy lease. At that observation the worktree was `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`, branch `author/c12-projection-overshoot-v71`, HEAD `73ac2a64924be782f630ef07391ace1f06ffbeaf`. The observation exactly verifies:

- Current source and successful attempt002 source snapshot have the final source hash above; successful output object and current installed object have the same stated object hash.
- The remote receipt itself matches the local bound receipt. Every declared audit source/JSON/log, full type/value export, failed/successful source snapshot and failed/successful log matches its receipt SHA256 and byte count.
- The complete type and value exports are exactly the corresponding untruncated blocks extracted from the bound audit log. Actual-owner rows and the local owner map are identical. The summary is `22 PUBLIC 9 THEOREMS 19 DEFINITIONS 3`.
- `OwnedAudit.lean` iterates `env.constants.toList` and uses `env.getModuleIdxFor?` for actual module ownership. For every selected constant it calls recursive `Lean.collectAxioms` and rejects all axioms outside `propext`, `Classical.choice`, `Quot.sound`. The public-name array is only a separate presence/count guard and does not restrict the audited set. All 22 selected constants pass; definitions and generated/private possibilities are included.
- Source token scanning finds no sorry, admit, new axiom, unsafe or native_decide. The complete source inspection agrees with this scan.
- The actual pin is `leanprover/lean4:v4.36.0-rc1`; mathlib HEAD is `807d3836b165983210ee2ecf3cd28f239436949c`; packages resolve to the accepted read-only `cache-overlays/shared-v34/packages`. These pin/path values match the established qualified package view. Toolchain file SHA256 is `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`; manifest SHA256 is `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`, recorded for exact observation provenance. The longstanding mathlib local-change warning is not a version upgrade or new reviewer write.

The reused author receipt records kernel attempt002 exit0 and all-owner audit exit0, CPU14–17, c12-heavy.lock, -M8192 and -j4. Source-bound kernel/axiom evidence is therefore successful for the entire frozen scalar module; I have not presented a new reviewer compilation as if it ran. The full remote observation metadata and hashes are retained locally, while the full compiler logs remain on the server.

## Failure preservation and final decision

I read the complete failed attempt001 log, successful attempt002 log and complete failed-to-final unified diff. The four changes are: replacing an untyped conjunction in simp; replacing reversed ordered-add API use with the explicit ordered sum; proving 1≤D from the nonnegative quotient rather than positivity; and expressing the absolute-subtraction triangle inequality with the local lets normalized. All imports, public theorem assumptions/conclusions and all three full definition values are byte-exact after projection in both attempts. There is no mathematical premise repair or weaker conclusion. The successful log contains deprecation, unused-variable/simp/tactic and tactic diagnostic messages, but no Lean error; the receipt records exit0. The failed snapshot and logs remain unchanged on the server. No successful gate was replayed.

**Accepted scope:** this exact source's nine public theorems, three definitions and ten generated auxiliary theorem constants, including the scalar normalized retained Gaussian local bound with constant8000100, all b²≤T and explicit zero-energy reachability. Correctness and complete proof are qualified; no novelty or original-root completion is claimed.

**Remaining open:** actual Brownian half-line reflection/probability identification and the actual reveal-state adapter; actual interval higher spatial/time/mixed regularity, PDE, Taylor and local bound; all original C12/OQ3/OQ4/OQ56 root groups. OQ3 remains paused by the human instruction. No interval negative-overshoot or separated positive-overshoot result is added by this module.

There are no critical gaps and no request to change the frozen declaration. Full per-declaration coverage, exact dependency maps and all evidence hashes are in `full-review.json`. Reviewer ownership and execution are explicitly released in `writer-release.json`, with no in-flight task and no heavy command.
