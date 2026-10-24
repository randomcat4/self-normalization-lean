# Independent complete final review: reciprocal density, units 82–83

STATUS: CORRECT. Both exact frozen targets have complete source-to-statement and proof review, complete actual defining-module-owned type coverage, complete actual non-theorem value coverage, and verified original successful server kernel/transitive-axiom evidence. No critical gap remains within these two targets. This qualification covers 13 public source theorems and 72 actual owned constants: 66 theorem constants and 6 definitions. All original C1/C2/OQ3/OQ4/OQ56 root groups remain OPEN.

The reviewer is the fresh independent `/root/interval_reciprocal_final_review` context. The author is chat `01a16c4c-25a6-7740-a10e-12635a13edae`. Initial scope was unit 82; the parent explicitly extended it to released unit 83 during this review. No further unit is certified. The reviewer has only written this review directory; there were no production-source, shared-coordination, Git, cache or remote writes, Lean/audit invocations, successful-gate replays, or child contexts. Requested model/effort are gpt-6.1-sol/xhigh. Independently exposed actual runtime model, effort and input/cached-input/output/reasoning-subset usage are unavailable and are recorded as null.

## Exact bindings

| Item | Unit 82: `Shao.C2.IntervalReciprocalDerivatives` | Unit 83: `Shao.C2.IntervalReciprocalHighTime` |
|---|---|---|
| Source SHA256 | `83bd9d4e46f2b16a323aa16108a50602ed3a5940ec524309aac22d84c5d92d28` | `76668fc4662f341c3925d67c45e320023dbe43b9a3a34bb2b1ba767cf4d27ca9` |
| Output and installed object SHA256 | `9c77fe18553c4d9bf616384d34a9c7dbf079fcdcba7117d1e76a26519e7c3d33` | `ef4d31c573fd1891d6910b9a8635ba8a13b21b6fa0e488ec70959b11843610b9` |
| Freeze SHA256 | `e9d90ec377abe8b426a9e49f41f5e8c92642c3fa92cdd5fa5251fd01c90832bd` | `ba4170efe904a3e19761de9836199142db3807f0d1b2a287258779921c7d2020` |
| Receipt SHA256 | `2a1dc6b0e41874b3c348e3a8ac34cdfb1bb812d66f74dcd94b2c1273fddf15ca` | `26ee4e3ab4c324e4ce26220cb05f527abe38cbb9d56de2d221c2677e122220d1` |
| Complete actual type export SHA256 | `36bfe8e6a935cd1b64fdfe401120ef009b79f450aa6ccdcaf99acc376ce54d50` | `caf249da71991edcbe148b8e5453f912205aec46f611cb56b2653b8c68530cd4` |
| Complete actual value export SHA256 | `2ff036d5083ae1df7fd80a3ddb2c6a88875421addfc1c9e0967d79062a9881d5` | `b6df7e7eba0860250c66414f210842c461400d7a2a677463d9c4b4a511d3f50c` |
| Owned audit JSON SHA256 | `6329b879b03ab872c8dfe92c1e08f7e40229e20826a4fd64e07c94153c10cdc2` | `f7759557e3ef3ebb1b9adb96b86acaa088d03a43e358387397b67930427ad34d` |
| Public/actual theorem/actual definition counts | 7 / 56 / 5 | 6 / 10 / 1 |
| Successful kernel attempt | 004, exit 0 | 002, exit 0 |
| Owned audit exit | 0 | 0 |

Local author folders are `drafts/c12-lane/interval-reciprocal-derivatives-v1` and `drafts/c12-lane/interval-reciprocal-high-time-v1`. Server output roots are `/root/rivermind-data/shao-lean-20261021/outputs/c12-interval-reciprocal-derivatives-v71` and `/root/rivermind-data/shao-lean-20261021/outputs/c12-interval-reciprocal-high-time-v71`. Production sources are in `workspaces/c12-bridge-domination-v71/Shao/C2/`. Direct read-only observations verified each final source against its successful source snapshot, each output object against the installed object, and all receipt artifact hashes and byte lengths. Unit 82's object is 10026336 bytes; unit 83's is 1582864 bytes. Local source/export/freeze/receipt bytes match the observed server versions.

## Original source and mathematical target

I read the complete original read-only `C:/game/shao/current/c12/supplement.tex` lines 4192–4315, including the quotient definition at 4197–4198 and the high-time argument at 4284–4297. In particular, 4292–4294 invokes the reciprocal free density with fixed terminal endpoint, normalized drift at most two, and derivative scale `C T^((1-j-2l)/2)`. These units supply precisely that analytic producer for the ten orders `j+l≤3` needed by the local Taylor argument. They do not certify the source's arbitrary-order version or the complete quotient/kernel lemma.

Put `d=z-y` and

`g(z,T,y) = sqrt(2*pi) * sqrt(T) * exp(d^2/(2*T))`.

For `T>0`, the literal free density is `exp(-d^2/(2*T))/sqrt(2*pi*T)`. Unit 82 proves their product is one; there is no replacement of the free density by a mere formal symbol or assumed inverse. Its coefficient definition and mixed family give `F(j,l)=C(j,l,d,T)*g`. Differentiation holds `z` fixed. The final mixed identity is explicitly time derivatives after space derivatives:

`iteratedDeriv l (fun S => iteratedDeriv j (g z S) y) T = F(j,l,z,T,y)`.

This is an actual derivative expression on the left, not a definition of derivative notation in terms of the displayed family. Spatial derivatives have the ordinary real whole-line domain, and positive time is an interior condition. The theorem does not assert a separate general mixed-commutation theorem; the two verified transition directions and smooth explicit formula are consistent with the source's classical partial-derivative notation.

## Independent coefficient calculation

Let `A=-d/T` and `B=1/(2*T)-d^2/(2*T^2)`. Direct logarithmic differentiation gives `g_y=A*g`, `g_T=B*g`. Because `d_y=-1` and `d_T=0`, each spatial coefficient transition is `-∂d C+A*C`, and each time transition is `∂T C+B*C`. I independently applied these recurrences to all six starting pairs with `j+l≤2`, checking both routes to common mixed entries. The resulting ten entries exactly equal the frozen table and all actual exported equation types and the complete actual coefficient value:

| `(j,l)` | `C(j,l,d,T)` | Triangle bound for `|C(j,l,d,1)|`, `|d|≤2` |
|---|---|---|
| `(0,0)` | `1` | `1` |
| `(1,0)` | `-d/T` | `2` |
| `(2,0)` | `1/T+d^2/T^2` | `5` |
| `(3,0)` | `-(3*d/T^2+d^3/T^3)` | `14` |
| `(0,1)` | `1/(2*T)-d^2/(2*T^2)` | `5/2` |
| `(1,1)` | `d/(2*T^2)+d^3/(2*T^3)` | `5` |
| `(2,1)` | `-1/(2*T^2)-2*d^2/T^3-d^4/(2*T^4)` | `33/2` |
| `(0,2)` | `-1/(4*T^2)+d^2/(2*T^3)+d^4/(4*T^4)` | `25/4` |
| `(1,2)` | `-(3*d/(4*T^3)+3*d^3/(2*T^4)+d^5/(4*T^5))` | `43/2` |
| `(0,3)` | `3/(8*T^3)-9*d^2/(8*T^4)-9*d^4/(8*T^5)-d^6/(8*T^6)` | `247/8` |

All bounds are at most 32. The last column is a symbolic estimate for every real `d` in the interval, not numerical sampling. Every monomial `d^r/T^s` in an order `(j,l)` has `2*s-r=j+2*l`. Consequently it has exactly the scale `(1/sqrt(T))^(j+2*l)` after replacing `d` by `d/sqrt(T)` and setting normalized time to one. This independently verifies unit 83's exponent and the full coefficient scaling table.

The explicit default branch `C=0` applies only when none of the ten listed pairs matches. Every derivative theorem carries its explicit order guard; default zero is never used as an assertion about fourth or higher derivatives. Enumeration concerns finitely many derivative orders while all real arguments remain universally quantified. It is not evidence of any root theorem by finite sampling.

## Public declaration and proof review: unit 82

1. `reciprocalFreeDensity_mul_free`: `T>0` makes `sqrt(2*pi)*sqrt(T)>0`. The proof splits `sqrt(2*pi*T)` using nonnegativity of `2*pi`, rewrites the negative exponent as the negative of the positive exponent, reassociates, applies `exp(q)*exp(-q)=1`, and cancels the nonzero square-root factor. Actual export confirms the negation is outside the square, the denominator is `2*T`, and the result is the real number one.

2. `reciprocalFreeDensity_spatial_hasDerivAt`: the proof first obtains the genuine derivative of `w↦z-w` as `-1`, then uses the square, division by a constant, exponential chain rule and a constant multiplier. Function extensionality normalizes the whole differentiated function; the derivative algebra is exactly `-(z-y)/T*g`. No equality at a single point is used to infer differentiation.

3. `reciprocalFreeDensity_time_hasDerivAt`: the pinned square-root theorem requires `T≠0`, supplied by `T>0`. Its derivative `1/(2*sqrt(T))` is converted to `sqrt(T)/(2*T)` using `sqrt(T)^2=T` and nonzero `T,sqrt(T)`. The quotient derivative of the fixed numerator `d^2` over `2*S` has a nonzero denominator at `T`. Product and exponential chain rules give `B*g`. No implicit differentiability hypothesis is assumed.

4. `reciprocalMixedFamily_spatial_hasDerivAt`: the six cases exhaust `j+l≤2`. In every case the coefficient expression is differentiated from constants, `z-w`, powers, sums, products and quotients with nonzero denominators; it is then multiplied by the already-proved derivative of `g`. The resulting product derivative equals `F(j+1,l)` by the recurrence above. Complete function and derivative expressions are normalized; `T>0` discharges all denominators. Both mixed-order signs `(1,1)` and `(2,1)` are correct.

5. `reciprocalMixedFamily_time_hasDerivAt`: the same six exhaustive cases now treat `d` as constant and time as the identity. The coefficient quotient derivatives plus `B*C` give `F(j,l+1)`, including `(0,3)` and `(1,2)`. The proof uses actual `HasDerivAt` product rules, not only formal coefficient identities.

6. `reciprocalFreeDensity_spatial_iteratedDeriv`: induction includes order zero. In the successor step the induction hypothesis is proved for every spatial argument by `funext`; this supplies equality of the entire intermediate derivative function with `F(j,0)`. Only then is `iteratedDeriv_succ` rewritten and the genuine family derivative used via `.deriv`. The predecessor order is at most two as required.

7. `reciprocalFreeDensity_mixed_iteratedDeriv`: induction on the time order includes the spatial theorem as its base. For the successor, the induction hypothesis holds at every `S>0`. Since `(0,∞)` is an open neighborhood of `T>0`, the intermediate time derivative function is eventually equal to `S↦F(j,l,z,S,y)`. `EventuallyEq.deriv_eq` therefore legitimately identifies their derivatives at `T`. The transition has `j+l≤2`; no differentiation of merely pointwise equality occurs.

## Public declaration and proof review: unit 83

1. `reciprocalCoefficient_scaling`: `R=sqrt(T)>0` and `R^2=T` reduce the ten exhaustive order cases to field identities. The exact public coefficient equations from unit 82 are used. The independently checked monomial weights above prove the same identity. Naming `R` is algebraic normalization, not a new hypothesis or redefinition of time.

2. `reciprocalCoefficient_unit_bound`: `|d|≤2` gives `|d^n|≤2^n` for `n=1,…,6`; the proof explicitly obtains upper and lower bounds. Each table entry at time one is reduced using its actual equation, and the resulting signed polynomial is bounded between `-32` and `32`. The triangle estimates in the table give an independent check, including the largest coarse estimate `247/8`. No actual derivative bound is assumed in this coefficient proof.

3. `reciprocalFreeDensity_drift_bound`: `|d|≤2*sqrt(T)` implies `d^2≤4*T`, hence `d^2/(2*T)≤2` because `T>0`. The explicit density is nonnegative. Monotonicity of `exp` bounds its norm by `sqrt(2*pi)*exp(2)*sqrt(T)`. The proof never requires `d` itself to be positive.

4. `reciprocalMixedFamily_drift_bound`: positive `sqrt(T)` gives `|d/sqrt(T)|≤2`. Scaling and the coefficient bound yield `|C|≤32*(1/sqrt(T))^(j+2*l)` with a nonnegative right factor. Multiplying by the nonnegative density norm bound and reassociating gives `reciprocalHighTimeConstant*sqrt(T)*(1/sqrt(T))^(j+2*l)`. The complete constant value is exactly `32*sqrt(2*pi)*exp(2)`.

5. `reciprocalFreeDensity_mixed_drift_bound`: the proof substitutes unit 82's genuine actual mixed-iterated-derivative identity and applies the family norm theorem with the same `j+l≤3`, positive time and drift hypotheses. This is the essential link from an explicit formula to an actual derivative bound.

6. `reciprocalFreeDensity_mixed_highTime_bound`: the already-qualified `highTime_drift_bound` uses `a>0`, `|y|≤a`, `|z|≤a`, `T>0`, and `a^2≤T`. Its first conjunct is `|z-y|/sqrt(T)≤2`. Multiplication by positive `sqrt(T)` supplies precisely the drift condition for the previous theorem. Closed-wall endpoints are allowed; no survival probability or wall derivative assertion is used. The bound is equivalent, for `T>0`, to the source's time scale `C*T^((1-j-2*l)/2)`.

## Complete actual owned coverage and definition semantics

I fully read the final source and proofs, all frozen imports/context/13 complete public heads/4 complete surface values, all 72 complete actual owned types, and all 6 complete actual definition values. Unit 82's exports are 111133 and 79074 bytes; unit 83's are 18518 and 924 bytes. No actual binder, generated/private declaration, matcher, or other namespace was omitted.

For unit 82 only, lossless textual dictionary substitution was used to reduce repeated `pp.all` syntax. Every one of the 108 entire dictionary entries and both entire encoded streams was read. Reverse substitution is independently asserted byte-for-byte equal to each original UTF-8 export, including whitespace; `export-roundtrip.json` binds the original hashes. This is complete encoded-text reading, not a semantic summary of large matchers. Unit 83's actual exports were read directly in full.

The three surface definitions of unit 82 are exactly `g`, the displayed ten-case coefficient table with default zero, and `C*g`. Its generated `reciprocalCoefficient.match_1` is the full dependent dispatcher: `j=0` selects handlers for `l=0,1,2,3`; `j=1` selects `l=0,1,2`; `j=2` selects `l=0,1`; `j=3` selects `l=0`; all other pairs select the default handler. The private generated `.match_1.splitter` has the same dispatch and supplies the ten exclusion implications required by its default branch. I read its entire dependent motive, all handler binders, equality transports, impossible-case proofs and final default application. Both matchers have empty transitive axiom lists. Unit 83's sole definition is the exact positive explicit constant already stated.

Unit 82's 49 generated theorem constants consist of 11 coefficient equations, 11 private matcher equations, one mixed-family unfolding equation, five numeral-instance proofs, fourteen simplifier facts, two exhaustive-six-case arithmetic facts, four iteration-order arithmetic facts, and one exponential product fact. Their complete types match their uses: ordinary literal numeral inequalities, nonzero numeral/product/power consequences with explicit hypotheses, the finite Nat case split, predecessor bounds, the ten matcher equations plus explicitly excluded default, and `exp(x)*exp(y)=exp(x+y)`. Unit 83's four generated theorem constants are two numeral-instance proofs and two complete exhaustive-ten-case arithmetic facts. Every owner is listed separately in the accompanying JSON with kind, axioms, full-type block hash, semantic category and, for definitions, complete-value block hash. Counts are derived from actual owner maps rather than copied from prose.

Both actual audit programs were fully read. They select constants by `env.getModuleIdxFor?` and the exact defining module in `env.header.moduleNames`, not by a namespace-prefix approximation; this includes private/generated and other-namespace constants. `Lean.collectAxioms` runs on every selected name and rejects every axiom outside `propext`, `Classical.choice`, `Quot.sound`. It exports `pp.all` actual types and every definition value. Both complete audit JSON owner sets match the type headers exactly, and their definition subsets match the complete value headers exactly. There are no additional kinds. The target sources have no `sorry`, `admit`, new `axiom`, `unsafe` or `native_decide`; the final exported actuals have no ellipsis or unresolved metavariables. The audit-log streams were partitioned exactly into the fully read type/value exports and the fully read residual warning/count text, with no discarded log portion.

## Freeze and actual execution provenance

The saved parent rollout was parsed narrowly; I read the actual relevant original tool calls and their completed results, not just checkpoint claims. In `rollout-2026-10-24T13-04-52-01a16c4c-25a6-7740-a10e-12635a13edae.jsonl`:

| Evidence | Unit 82 | Unit 83 |
|---|---|---|
| Original freeze AddFile | line 9181, 13:36:08.980Z; completion 9184 | line 9338, 13:44:44.301Z; completion 9341 |
| Implementation AddFile | line 9262, 13:40:03.808Z | line 9405, 13:48:37.775Z |
| First kernel dispatch | line 9272 | line 9405 |
| Final successful kernel dispatch | line 9347 | line 9453 |
| Completed final kernel result | line 9361: `KERNEL_EXIT=0` | line 9465: `KERNEL_EXIT=0` |
| Owned audit dispatch/result | 9365 / 9368: `AUDIT_EXIT=0`, 61/7/56/5 | 9471 / 9474: `AUDIT_EXIT=0`, 11/6/10/1 |

Times above are UTC on 2026-10-24. Each original AddFile payload was reconstructed and checked byte-for-byte against the current freeze. Thus each substantive declaration/value freeze precedes its implementation. Stripping proof bodies from the final sources gives those exact freezes; the same check passes for every preserved failed source.

The actual commands source `/root/rivermind-data/shao-lean-20261021/activate.sh` before changing to the worktree, then use `flock /root/rivermind-data/shao-lean-20261021/locks/c12-heavy.lock taskset -c 14-17 lake env lean -M8192 -j4` on the targeted source or audit file. The output object is explicitly set and installed before the corresponding audit imports it. The final kernel command's shell result is 1 because its following `grep` finds no `error:`; the explicit recorded Lean result is 0. This distinction was verified in both completed results and in both full successful logs. Every original failed and successful kernel log was read completely from the server. Raw logs, objects and caches were not copied into the collaboration workspace.

Pinned environment is Lean `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, package view `cache-overlays/shared-v34/packages`, branch `author/c12-interval-reciprocal-v71` at base HEAD `c21c0b4b223f4bcb5aa9ceb0ba164ec580b332b7`. Direct read-only observation confirmed the package link, toolchain file and mathlib HEAD. The ordinary warning about local mathlib changes is retained. Needed square-root and differentiation source contexts were compared with exact pinned Git blobs; they are unchanged. No environment/pin/cache alteration or compilation was performed by this reviewer.

Unit 82's complete successful kernel log SHA256 is `fbd1fcf051a98e37ede50b367f4a92156ef6f30f476cb92bd5b19165a283bad4`; full owned audit log SHA256 is `f05f90bdbb895c2fdfc6f4a98bc490aaf2732b0bb22058d80e123f948c6c1d55`. Unit 83's corresponding hashes are `f50a2e28a6bb05db5b556c064a3ff5cbde75e5ebe8f0b312380882cea15bdcd8` and `cc0b86a8f980ab21d116944c9aa0534423fd768c6447d3926c2a55ab135c55d3`. Full original artifact maps are bound in the JSON.

## Failed-proof deltas and unchanged dependencies

Unit 82 attempts 001–003 are preserved with complete sources and logs. I read each full source-to-final diff, together with the complete final source, and verified all four sources have the same frozen imports, context, seven complete heads and three complete surface values. Attempt 001 exposed Pi-function/instance normalization, denominator nonzeroness syntax, exponential inverse cancellation and inverse-power field normalization. Attempt 002 retained the derivative-function normalization issue and no-progress `dsimp` uses. Attempt 003 retained no-progress `simp` uses. Final changes use the ordinary `const_sub` derivative, explicit denominator `change` statements, precise exponential cancellation, and `ring_nf` before `field_simp`. These repair proof elaboration/algebra only. No assumption, order, target, definition, mathematical strategy or source scope changed.

Unit 83 attempt 001 source/log are likewise preserved and read completely. Its full diff to final changes only proof bodies: imported coefficient matches are reduced by their exact public equations; the positive named square-root scalar makes the field normalization explicit. All six full heads, the one full constant value and context remain byte-exact after removing proofs. Failed attempts are not treated as accepted results. All local and remote source versions were already UTF-8 without BOM and with zero CR bytes before their first gate; no old source or accepted evidence was renormalized.

Unit 82 imports qualified unit 81 `IntervalSineHighTime` but calls no theorem or definition from it in its source proof. Its source hash `a54d687db2e17d73b67447783d4b083eabecd468c6802204bccb0f1860796e08` was confirmed unchanged. The existing complete independent 79–81 review is reused with JSON `67ff027602b2d00ffc8d6f837d67c225be8e4084032285d50fed4c882ba0e982`, Markdown `378b10a17b8f3a3baec3a27a7132cf2066b70c864b5956fea0c4598ef839e365`, release `9946f9c9fdf51787f6ceb77027ed1faa8fd47a8682d5f610f2b69586fa66a572`. No old accepted proof was replayed or newly requalified merely for this import.

Unit 83 consumes the unit 82 interfaces reviewed here and only `highTime_drift_bound` from qualified unit 78 `IntervalHighTimeProfiles`. Its full actual consumed type, source proof and receipt were read; its source `0ae211f02c224c4c7b2456f441fc08a41a62d20f76fb8c840696aa8af0e64020` and installed object `32dee6333a142d2f536f1d563be45cc843311785786392274af0fa6a386d7f34` are unchanged. Reused independent 77–78 review JSON is `4ac7eab2a86ff66a801d7c477c816c3eab62f996756544d7abca6dea1c7515b0`, Markdown `aad4e09e6688d1f6cd4f698ad00ddfa60efbc91a7b0ad21439a0c8cceccba8d9`, release `a9a16050d59de8b72dc000952d525cc711a996739d3d21de6d070a46ecfc5701`. Its original receipt is `c2d0e94cea50588e955e93c8776ab10136bd739517818488165915dd67aa82e2`. Reuse is exact-hash-bound, not a fresh global old-proof review.

The needed standard contexts include the pinned `Real.hasDerivAt_sqrt`, with its full positive/negative case proof context, product/quotient/power/add/subtract/negate/constant and exponential differentiation interfaces with their variables, actual `HasDerivAt`/`deriv` definitions, `HasDerivAt.deriv`, `iteratedDeriv` zero/successor, and `EventuallyEq.deriv_eq`. The real structures and hypotheses match the complete actual target types. Consumed previous context hashes were rechecked without running Lean. The local inspection helpers initially encountered the Windows Python alias and absent server `rg`; the trusted bundled Python path and read-only Python text search resolved these, without repeating any mathematical gate.

## Boundaries and release

There is no uncovered obligation inside the two frozen targets. The established result is the reciprocal free Gaussian identity, its actual mixed derivatives through total order three, and the explicit corresponding high-time norm bound under the stated drift/closed-wall hypotheses. The work is an elementary analytic auxiliary formalization and makes no research-novelty claim.

Reciprocal-times-sine Leibniz assembly, image/sine equality, actual killed-kernel equality, strict Brownian-bridge survival probability identification, complete compensated Taylor/hSmall estimates and root closure are still outside this review. In particular the imported sine module is not silently identified with the source's killed heat kernel. No one-sided killed-kernel trace or probability statement follows from the ordinary whole-line reciprocal-density derivative theorem alone. Source scope, p54 repairs and external-result attribution remain unchanged. No unit 84 or later proof is certified.

The reviewer has no heavy command or other operation in flight, and releases writer/execution authority in `writer-release.json`. The parent may reuse these exact reports and original server receipts at acceptance and continue its separately owned next dependency. This final report is a completed review artifact, not a claim of persistent future runtime.
