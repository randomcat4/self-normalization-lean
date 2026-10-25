# Unit 192 — complete independent static source/proof review

STATUS: CORRECT

This is a complete **static mathematical and source-to-statement judgment** for the exact source below. I found no critical mathematical gap, changed premise, missing case, wrong derivative sign, or source-scope substitution. The source implements the frozen pointwise three-bill classification. It has not yet been elaborated or checked by Lean in this review. Kernel acceptance, the actual owner map, full generated/private type/value coverage, and the transitive-axiom receipt remain mandatory before formal qualification.

## Exact subject and independence

The reviewed source is `drafts/c12-lane/actual-double-separated-classification-v1/ActualDoubleSeparatedClassification.lean`, SHA256 `a1f40c947e4af62aa5210a3f286af0acd09362215fc842cd1b6dc680211df26b`, exactly 27,825 bytes and 543 lines. I read every source line, including the three complete proof bodies and the sole source-level definition value. The frozen context/value/heads are `frozen.lean.txt`, SHA256 `199a8a03bceeb1a01e78e3a7836798e6fe46ea230108b5c2cfb128454d3423b6`. A deterministic local comparison confirms the complete prefix through `prefixAlive` and each of the three theorem heads are exact. The file is UTF-8 without BOM, has LF endings and a final LF, and contains none of the prohibited tokens `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide`.

My role is `/root/actual_double_separated_complete_source_review`, independent of the released source author `/root/actual_double_separated_classification_static_author`. I observed the author's `sourceWriter=0`, `inflight=0` release and did not edit any implementation, frozen input, accepted report, or coordination file. My write ownership is only this review directory. No child was delegated. All operations in this review were local reads and deterministic review-artifact writes: server commands, Lean/lake, kernel/axiom checks, heavy commands, uploads, Git and publication operations are all zero.

I applied the math-theorem verification role and the current project acceptance/resource instructions. This is a verification unit, not a new candidate-search or novelty exercise. No local Lean discovery, installation or execution was attempted; the project's explicit server-only rule and the parent's no-heavy instruction govern this phase.

`input-manifest.json` binds the exact source, freeze, all six mandatory inputs from the author's static audit, source format, declaration comparison and original excerpt comparison. `source-coverage.json` partitions all 543 source lines without a gap and records the complete consumed source values/heads. `file-manifest.json` binds the remaining locally read evidence. Hash bindings below are to actual bytes, not names or assumed historical versions.

## Source and accepted theory contract

I read the complete frozen theory subject, complete 272-line mathematical proof candidate, complete independent mathematical review, its verdict, the parent theory acceptance, and all 148 numbered original-source excerpt lines. The exact current theory hashes are:

- Frozen subject: `b7b252821f6c0d7690cdda9917fef13eec86b4b13b5e30aa940801398cec7968`.
- Complete mathematical candidate: `11a8cc57318178b6b769ad3b538abca29c3e64d38cb20fd76c057baaf1c2751d`.
- Parent theory acceptance: `244c2461e56449461a4801815d4dbcfa9156717e97b7bd10717e7d18a6cbe349`.
- Independent complete theory report: `f96fe7a1fbe59ab293badf7982dccd8efa2973ba9a207aee56e7742b63b026bd`.

The excerpt's 148 numbered lines match the read-only original `C:/game/shao/current/c12/supplement.tex` at ranges 4778–4808, 5433–5456 and 5496–5588. The original whole-source SHA256 is `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. The formal classification addresses especially 5564–5587. The raw finite state is preserved throughout: the same labelled path, permutation, rank and cap give `w=x sqrt(energy a)`, the reordered prefix `y`, actual remaining square sum `T`, raw terminal sum `z`, and next actual label `b=a(sigma(r))`.

The statement at lines 215–234 puts a positive universal constant **before** every probability space, Brownian motion, raw path, dimension, `x`, cap, rank and permutation. Its only restrictions on raw finite inputs are `x>=16`; the cap is arbitrary. It introduces no iid, support, moment, stopping-rank or conditional-observability premise. Its `G` is the actual derivative family of `bridgeLaw B P`. The conclusion is exactly

    0 <= U+L-I <= C exp(-x^2)(U+L)
                   + 1_Bad (U+L+max(-I,0))
                   + 1_not_HL U + 1_not_HU L.

Here `Bad` is the strict inequality `3*x*sqrt(T)/2 < |z-y|`. Equality is assigned to the regular branch, whose ratio hypothesis is inclusive. The formal result is a pointwise classification only. The theory's genuinely integrable finite-sum consequence, numerical rare/second-wall bills, cubic negative-interval producer and original C2/C12 completion are not new formal conclusions of this source. There is no use of the invalid full-amplitude interval/one-wall domination excluded by the source.

## Complete consumed values and established interfaces

The six mandatory current bindings all pass: the three theory files above, current Unit191 source `a05fc009d513978b9605af7ca384579c0a409db49cd68a7b3940685b12ac45d0`, `BrownianBridgeLawUniversality.lean` at `0ffdfbbb54df25f8502a8f13a770ae603a82b8fb40faa1a15209d6af4551bf62`, and `SourceActualRegularPhysicalRatio.lean` at `30ea7da3bd4924271c05e1eeb308aaa1502d9b098a9e9a0f883623b4699f3457`.

The historical theory `input-bindings.json` records an earlier whole Unit191 draft hash. I do not claim that historical whole draft is unchanged today or inherit its unqualified proofs. The implementation consumes only the complete transparent `actualDerivativeFamily` value, read at current Unit191 lines 27–31: upper maps to `halflineDerivative .upper`, lower to `halflineDerivative .lower`, and interval to `intervalDerivative Q`. The current Unit191 final manifest records those definition values unchanged, and `parent-qualified-all189191.json` binds qualified current Unit191 to `a05fc009...`. No Unit191 theorem proof is used by the present argument. The mandatory six current bindings, rather than the historical eight-file theory snapshot, are what this review revalidated.

I read the following complete values or complete theorem interfaces in their actual source files; the coverage manifest records exact files, ranges and hashes. Established proofs and successful checks are reused, not rerun or recommissioned.

- `Path n` is `Fin n -> real`; prefix sums/squares are the saturated finite filtered sums; actual energy is the full sum of squared labels; `reorder a sigma` is `a` composed with `sigma`. The consumed `prefixSquares_nonneg` head has no extra premise.
- `remainingSum` is raw terminal sum minus reordered prefix; `remainingEnergy` is full energy minus reordered prefix squares; `actualWall` is `x sqrt(energy a)`. `Interior` is strict upper, strict lower, or their lower/upper conjunction. `eventCompletionKernel` selects the corresponding actual bridge probability.
- `sourceAlive` is positive total energy AND strict domain terminal condition AND strict prefix condition for **every** `k<=r`, including rank zero. In contrast, the complete new `prefixAlive` value at 19–22 is only the final prefix clause. No endpoint test or energy test has been smuggled into the new flags.
- `projectionIncrement` uses weak crossings: upper projects to `w-y`, lower to `-w-y`, and interval gives upper priority then lower. On no crossing it is `b`. `localSeparatedOvershoot` is exactly zero unless `T>0` and `b^2<=T/2`; otherwise it is `-(b-p)*(1-(b+p)*(z-y)/T)*G`. `sourceSeparatedOvershoot` adds `r<n`, `r<nu`, actual `sourceAlive` and positive actual remaining energy before evaluating that local expression with the actual next label.
- The actual half-line derivatives are the negative/positive `slopeTime` values at `(w-y,w-z,T)` / `(w+y,w+z,T)`, with `slopeTime(u,v,T)=(2v/T)exp(-2uv/T)`. The interval derivative is the genuine spatial derivative of the interval probability kernel only under `w>0`, `T>0`, `|y|<w`, `|z|<w`, and zero otherwise.
- `actual_halfline_kernel_data` needs the two real reflection identities and a probability law. Its last component supplies `HasDerivAt` for the actual probability kernel at strict interior states. `actual_interval_kernel_data` additionally needs interior differentiability of `sourceIntervalCompletion`, and supplies the actual guarded interval derivative. The actual Brownian upper/lower formulas and `actual_source_interval_differentiable` discharge those requirements. At `T>0`, the complete value of `sourceIntervalCompletion` is the actual interval completion.
- `BridgeNoise` is the subtype of continuous paths on the unit interval pinned to zero at both ends. `bridgePath(y,T,z,g)(t)=(1-t)y+tz+sqrt(T)g(t)`. Strict events quantify over every time; completions are real probabilities of those events. Their complete measurability heads have no positivity restriction. `pinPath`, `bridgeNoise` and `bridgeLaw` were read as actual values; `bridgeLaw` is `P.map (bridgeNoise B)`.
- `ae_bridgeNoise_eq` says **almost every omega, for every bridge time t**, and `aemeasurable_bridgeNoise` and `isProbabilityMeasure_bridgeLaw` have exactly the Brownian/probability hypotheses available here. `bridgeLaw_eq_of_isBrownianReal` is equality of complete measures on `BridgeNoise`, with arbitrary two ambient probability spaces. The accepted lower-identification source explicitly uses `hB.neg` in precisely this environment; no extra negative-Brownian premise is missing.
- `projected_negative_part_control` has wall/time positivity, the selected-domain starting/terminal interiors, `eta=1` or `eta=-1`, its matching domain restriction, a **weak** directional crossing, and `b^2<=T/2`. Its complete ten-component conclusion gives the sign, positive gap, gap at most `|b|`, nonnegative excess, nonnegative coefficient, and the exact local formula. Both destructurings select its ninth component for that formula and seventh for coefficient nonnegativity.
- `source_separated_overshoot_sign_domination` needs probability, positive `x`, and genuine conditional interior derivative data for all three actual kernels. Its complete output is `U>=0`, `L>=0`, `I<=U+L`, `max(I,0)<=U+L`, and `U+L-I>=0`. No raw-path probability or cap condition is in the head.
- `actual_bridge_first_upper_gradient_ratio` chooses its `C>0` before every Brownian motion and has exactly `x>=16`, `T>0`, `w>=x sqrt(T)`, `0<w-y<=|b|`, `b^2<=T/2`, `|z|<w`, `|z-y|<=3x sqrt(T)/2`. It controls the genuine completion derivatives by `0<=dI-dU<=C exp(-w^2/T)(-dU)`. It is an existing qualified theorem, not a new caller oracle or a restatement added as an assumption.

## Whole-path reflection: lines 24–121

The local `R` at 33–38 negates the continuous path. Both pinning proofs are explicit and valid by the old endpoint equalities. Negation and subtype projection are continuous, so the measurability proof at 39–43 is mathematically valid with the inherited Borel structure.

Lines 44–54 intersect the actual all-time almost-everywhere reconstruction sets for `B` and `-B`. For each omega in their single common full-measure set, the proof checks every time and uses continuous-map then subtype extensionality. The algebra is `-(B_t-t B_1)=-B_t-t(-B_1)`. This proves equality as random elements of the path space, not just a marginal equality with time-dependent exceptional sets.

Lines 55–62 apply measurable pushforward composition to get `R_*Q=bridgeLaw(-B)`, and complete-law universality gives `R_*Q=Q`. The accepted universality source itself uses the same `AEMeasurable.map_map_of_aemeasurable` call order. This disposes of the particular continuous-modification choices almost everywhere.

The affine path identity at 63–67 is exact for arbitrary real wall, spatial parameters and time parameter, since `sqrt T` multiplies the negated path. The interval preimage proof at 68–92 swaps the two strict inequalities; the upper preimage at 93–104 is exactly the strict lower event. With the old complete measurable-event heads, lines 105–121 take pushforward probabilities and obtain the two frozen completion identities. No interior/positive-time assumption was needed or silently inserted in this first private theorem.

## Reflected lower-gradient ratio: lines 123–213

The proof chooses the existing upper-ratio witness before introducing the ambient space. For its lower hypotheses, `u=w+y>0` and `u<=|b|` with `b^2<=T/2` imply `u^2<=T/2` and `u<=sqrt T`. Positive time and `w>=x sqrt T>=16 sqrt T` then give both `-w<y` and `y<w`, as proved at 147–158. Thus every reflected spatial derivative is read at a valid interior state. Positive `w` is also derived, not assumed.

Lines 159–178 obtain actual half-line reflection data, actual reflected interval differentiability, and actual reflected upper differentiability. The interval transition from `sourceIntervalCompletion` to `intervalCompletion` holds as an equality of the whole spatial function because `T>0` is fixed. It is sufficient that differentiability is known at the reflected point.

The function identities at 179–186 hold for every spatial input. Composing each reflected differentiable function with `s -> -s` at `y` contributes the factor `-1`. Lines 187–199 consequently identify the reflected interval derivative as `-dI` and reflected upper derivative as `-dL`; they do not assume lower differentiability or forget the chain factor.

The upper theorem at `(x,w,-y,T,-z,-b)` has exactly the needed hypotheses: the upper wall gap becomes `w+y=u`; absolute label, label square and endpoint absolute value are invariant; the reflected displacement has the same absolute value. Substitution of the derivative identities in 206–213 gives

    0 <= dL-dI <= C exp(-w^2/T)dL.

This is the frozen lower-ratio statement with the same selected universal witness. No lower-ratio oracle, extra process symmetry assumption or unsupported pointwise equality of Brownian sample paths was introduced.

## Public theorem setup and easy bills: lines 235–348

The two ratio witnesses are chosen before any Brownian motion/raw input, and their maximum gives a positive universal `C`. The proof does not need to show those separately chosen witnesses equal. Both are dominated by the maximum, so the quantified universal order is retained.

The local `hReflection`, `hRegular` and `hDeriv` at 245–269 construct the genuine three-domain derivative data from actual Brownian producers. The interval case passes the exact absolute-interior equivalents of the lower/upper conjunction. The complete conditional derivative interface is established before sign-domination is invoked. Its final component is used for the lower bound; its first two provide nonnegative U and L. The exponential multiplier and the two prefix-failure payments are nonnegative at every raw state.

`hDead` at 283–289 unfolds only the actual outer source guards and proves zero when `sourceAlive` fails, including the out-of-range dependent branch. On strict `Bad`, lines 290–295 use the exact elementary inequality `-I<=max(-I,0)`; the interval negative part survives in full, and all other payments are nonnegative.

After not Bad, failure of the upper prefix flag gives `U=I=0` by the actual prefix component of `sourceAlive`. The interval history is converted by its upper component, with no terminal condition used. The final prefix-failure term pays exactly L, and the exponential term is nonnegative. Failure of the lower flag gives `L=I=0` and pays exactly U by the other term. These branches also cover both histories failing. They keep an exterior endpoint separate from a prior prefix hit.

With both flags live, the proof handles `r>=n`, `r>=nu`, nonpositive remaining energy and nonpositive actual total energy by the literal corresponding definition guards. Every relevant U/L/I term is zero. Empty paths, zero caps, saturated ranks, negative or zero remaining time, and energy-zero rank-zero equality phenomena lie in these branches. No division or positive-wall argument is used before these guards are removed.

## Local guards and actual geometry: lines 349–411

The local `w,y,T,z,b` are the exact source arguments, and the single `hLocal` equality is obtained from `r<n`, the actual cap, source live flag and actual T>0. On `b^2>T/2`, each domain is zero either through its dead source guard or through the local small-energy guard. This only removes large-energy **separated** terms; it does not assert the full retained remainder vanishes.

`hNoCross` at 373–379 is valid for every domain: on a live state, replacing the projection with b makes the factor `b-p` zero; otherwise the source guard is zero. It never needs an actual derivative bound outside the valid interior.

The nonnegative prefix square sum gives `T<=energy a`, hence `w>=x sqrt T`. The actual next label occurs in the full finite sum of squares, so `b^2<=energy a`, `|b|<=sqrt(energy a)` and `|b|<=w/x`. The proof assumes no external support bound. Independently, its already active `b^2<=T/2` gives the stronger `|b|<=sqrt T` used in the exterior contradiction.

Set `s=sqrt T>0`. The asserted strict gap at 400–402 follows because

    2w-|b| - 3xs/2 >= 2xs-s-3xs/2 = (x-2)s/2 > 0.

All its premises are explicit; the extra `hbWall` proof is harmless even though this stronger route is used. The not-Bad inequality supplies the inclusive displacement bound. For 403–411, `xs>=0`, `w>=xs` imply `w^2>=x^2*T`; division is only by positive T. Monotonicity of exp gives `exp(-w^2/T)<=exp(-x^2)`.

## Interior crossings: lines 412–519

When `|z|<w`, both live prefix histories, positive energy and strict endpoint conditions yield all three exact source live flags. The three `HasDerivAt.deriv` equalities at 420–425 identify the actual family values with the genuine probability-completion derivatives used by the ratios. The guarded interval derivative is consumed only at `w>0`, `T>0`, `|y|<w`, `|z|<w`.

At an upper weak crossing `w<=y+b`, positive w excludes a lower crossing and the lower projection equals b, so L=0. The upper and interval projection-control calls have the identical raw state, direction `eta=1`, selected wall and small-energy bound. Their common `u=w-y`, `e=|b|-u>=0` and `c=1-(|b|+u)(z-y)/T>=0` are therefore genuinely the same. The exact local formulas at 442–451 give

    U=-(e*c)dU, I=-(e*c)dI, U+L-I=(e*c)(dI-dU).

The upper ratio's positive gap and gap-at-most-|b| hypotheses come from those actual projection-control outputs. Multiplication uses only nonnegative `e*c`. The coefficient comparison uses `CU<=max CU CL`, the exponential comparison and nonnegative factors. Finally U>=0 allows multiplication of that coefficient inequality. This proves the exact regular interior upper bill `OD<=C exp(-x^2)(U+L)`.

On no upper crossing but a lower weak crossing `y+b<=-w`, the upper projection equals b, so U=0. The lower and interval calls use `eta=-1` and the same actual arguments. Now `u=w+y`, `e=|b|-u`, and `c=1+(|b|+u)(z-y)/T`, the eta=-1 coefficient. Their exact formulas at 486–495 give

    L=(e*c)dL, I=(e*c)dI, U+L-I=(e*c)(dL-dI).

The reflected ratio and the same nonnegative multiplier/coefficient argument give the regular lower bill. In particular the sign of the interval contribution is positive in I on this branch and is subtracted in OD, as required. No unjustified absolute derivative or cancellation was used.

If neither weak crossing holds, all three projections are b and all terms are zero. Equality at a crossed wall is already inside the weak-crossing branches: `|b|=u`, so e=0 and both exact local formulas vanish. There is no unhandled transition from <= to <.

## Exterior endpoints: lines 520–541

The failure of `|z|<w` is exhaustively split into `z<=-w` or `z>=w`. Equality endpoints are included because all relevant completion endpoint guards are strict.

For `z<=-w`, the lower and interval source endpoint tests are false, giving L=I=0. If there were an upper crossing, `y+b>=w` and `z<=-w` imply `y-z>=2w-b>=2w-|b|`. The negative side of the inclusive displacement bound gives `y-z<=3x sqrt T/2`. Together these contradict the previously established strict gap. Thus the upper projection is b, and U=0 by `hNoCross`.

For `z>=w`, upper and interval guards give U=I=0. A lower crossing would force `z-y>=2w+b>=2w-|b|`; the positive side of the displacement bound again contradicts the same strict gap. The lower projection is b and L=0. These are the correct opposite-wall endpoint contradictions; an exterior endpoint was never replaced with a false prior-hit assertion.

This exhausts every actual raw state, including bad displacement, dead histories, every literal zero guard, both crossing directions, no crossing, equality crossings and either exterior endpoint. Combined with the established global sign-domination lower bound it proves the exact frozen pointwise claim mathematically.

## Unresolved formal evidence, separated from mathematical findings

There are **no identified mathematical errors** and **no identified static syntax/type error** in this review. The following are explicit unresolved formal-evidence obligations rather than mathematical passes or claims of compilation failure:

1. The exact whole file has no first successful source-bound parser/elaboration/kernel receipt yet. In particular lines 33–62 rely on elaboration of the pinned subtype-negation map, its inherited topology/Borel instances, a.e. pushforward composition and private theorem naming. Existing accepted call patterns support these uses, but static inspection cannot certify that all elaborator obligations close.
2. Lines 167–213 rely on the native `DifferentiableAt.hasDerivAt` / `HasDerivAt.comp` interface, simplification of the negated identity derivative, and rewriting of the resulting full function expressions. I checked the mathematical domains and signs completely; I did not issue a native-source server query or execute these tactics. The exact elaborated chain-rule proof remains to be certified.
3. Lines 259–272, 283–541 rely on reducible equality of the selected actual family branches, nested let/tuple projection elaboration, dependent `if` proofs for the actual next label, and closure of the displayed `simp`, `ring`, `linarith` and `nlinarith` goals. All consumed project heads and values were inspected in full; their correct mathematical use does not substitute for those tactics succeeding under the pins.
4. No actual-owned map exists yet for this new source in the evidence reviewed. The four source-named declarations are **not** asserted to be the total actual-owned constant count. A later exact-source receipt must cover every actual-owned private/generated theorem's full type and every actual-owned non-theorem's full value, and recursive axioms with whitelist `propext`, `Classical.choice`, `Quot.sound`. It must bind the exact source and dependency map, with no namespace filtering. This source-level scan is not that audit.

The dependent continuation should bind the original successful kernel/all-owned receipt, inspect all actual unelided types and non-theorem values (lossless repeated-expression reuse is allowed by current policy), and review any actual uncovered delta. If a parser/tactic repair changes source, preserve this seal and the failure evidence and review only the changed proof/interface plus affected semantic interactions against the same frozen statement. A changed proof's old source hash is not a pass for its replacement. No additional complete old-unit proof review or repeated successful old gate is requested here.

## Release and usage

The requested review configuration is fresh `gpt-6.1-sol` with `xhigh`. Backend-resolved model/effort and the separate input, cached-input, output and reasoning-subset token counts are not exposed to this context and are null in the structured artifacts. No exact allocation of subscription usage is inferred.

This report completes the assigned static review. The final `RELEASE.json` records review-writer zero, source-writer zero, execution/inflight zero and the source-bound next dependency: first kernel/all-owned receipt, followed by the continuation machine-evidence delta review. Original C2/C12 remains OPEN and no numerical probability producer or mathematical root completion is claimed.
