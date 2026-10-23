# Independent complete review: OQ4 polygonal third moment B3

STATUS: CORRECT

Reviewer context 135, fresh gpt-6.1-sol / xhigh, using math-theorem and the current streamlined acceptance policy. Author context 132 and reviewer are separate. I reviewed the anonymous final Lean source, original mathematical source, exact freezes, complete actual interface and execution evidence. I did not read the author's `proof.md`, author report or another B3 verdict; execution metadata was used as evidence, not as a correctness vote. I changed no mathematical source or assumption and ran no Lean, server, Git, network or new mathematical test.

The verdict applies only to `Shao.OQ4.PolygonalThirdMomentB3`, pure source SHA256 `0e9c704432657c2a0baee0321ec24b90b0d513efcfe5738ff0736755ca387619`, 10,959 bytes, UTF-8 without BOM, 258 LF and zero CR. The successful server source copy is byte-identical. The combined checked source is exactly this source, one LF, and the reviewed audit suffix.

## Original source and frozen statement

The read-only original is `C:/game/shao/current/oq4/b01/proof01.md`, SHA256 `7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`. I read lines 233–255 completely and checked the row assumptions in lines 9–18: centered iid real increments, variance one, and a common third absolute moment bound. The present unit isolates B3, rather than the characteristic-function/FDD assertions or the tightness conclusion surrounding it.

The exact mathematical, public formal and private formal freezes have hashes respectively:

- `f00e1c7255124f539accf1899a53e6b92e23e4e8239df4526931ea25cb07cbc7`;
- `b742df4547e7a57add922f8e2c5115c158bec911995a3f1494c637504e065e64`;
- `fc792af64cdbc0fe7871d27e94a5a9ca50793c7f8c113800e2f9979abbf367cc`.

All 14 explicit declarations match the private formal freeze, and its five public declarations match the public freeze, including all binders, hypotheses, conclusions and three definition values. The deterministic comparison removes whitespace and proof bodies only; no header or definition-value mismatch occurred. I also read and compared the full elaborated types, not only the source headers.

The actual definition is

`W(n,h,a,t) = ∑ i : Fin n, max 0 (min 1 (t*h²-i.val)) * a i / h`.

This uses the actual finite coordinate path `Shao.Path n = Fin n → ℝ` and the actual saturated prefix sum, not a replacement process or a hypothesis identifying an arbitrary process. The two public identification theorems give exactly `prefixSum a k / h` at `k/h²` and the affine combination of consecutive prefix sums at `(k+u)/h²`, for the frozen grid hypotheses and both endpoints `0 ≤ u ≤ 1`.

For every natural `n`, real Borel probability measure `ν`, finite third absolute moment, mean zero, `h>0` and `0≤s≤t` with `t*h²≤n`, the actual exported results assert integrability and

`∫ |W(t)-W(s)|³ dν^n ≤ 24 (∫ |x|³ dν) (sqrt(t-s))³`.

Thus the original class with `β≤M` has `C_M=24M`. Omitting variance one from this finite-moment lemma is an explicitly frozen strengthening: its proof needs no variance normalization. It does not supply the variance assumption needed by a future Gaussian limit. The finite product encodes exactly the within-row iid law; there is no coupling or common-law requirement between rows. No fourth moment, symmetry, density, boundedness, exponential moment or tail assertion was added.

## Complete mathematical proof review

I read every line of the final 258-line proof.

1. Lines 24–58 define the actual path, `ramp x = max 0 (min 1 x)`, and its scaled increment coefficient. The ramp bounds and monotonicity use the ordinary real order. The identity `ramp x = max 0 x - max 0 (x-1)` splits `x≤0`, `0≤x≤1`, and `x≥1`, including the equality cases.

2. Lines 60–73 telescope the ramp sum to `max 0 u - max 0 (u-n)` for every real `u` and every natural `n`. The induction starts with the empty sum, and the successor step uses the final coordinate and the exact real cast of `n+1`. This is not restricted to a positive path length or to a generic interior time.

3. Lines 75–106 prove the coordinate affine identity by the exhaustive integer cases `i<k`, `i=k`, `i>k`. The hypotheses `u≥0` and `u≤1` justify the two clamping boundaries. In the last case `k+1≤i`, so the coordinate remains zero even at `u=1`. There is no rounding, floor, exceptional grid point or excluded endpoint.

4. Lines 108–116 distribute the difference of the actual path sums into the sum of `incrementCoeff i * a i` by a pointwise ring identity. This step is an exact identity, valid before any probability estimate.

5. Lines 118–160 establish the bearing estimate. From the frozen hypotheses and `h²>0`, both `s*h²` and `t*h²` lie in `[0,n]`. The telescoping identity therefore gives `∑d_i=(t-s)h²`, where `d_i` is the difference of the two ramps. Monotonicity gives `d_i≥0`, and the two ramp bounds give `d_i≤1`. Hence `d_i²≤d_i`. Division by the positive `h²` and summation yield `∑(d_i/h)²≤t-s`. The cancellation is justified by `h>0`. This single estimate works at every time scale; the original source's additional small-time case split is unnecessary.

6. Lines 162–205 cancel the grid-time denominator using `h²≠0`, substitute the coordinate identities, and identify the finite indicator sums with the real `Shao.prefixSum`. For the affine theorem the sum is distributed into the two actual consecutive prefix sums. The frozen `k≤n` and `k<n` hypotheses remain in the actual types. They are stronger than needed because the prefix sum is saturated; their unused-variable warnings do not hide a missing case.

7. Lines 207–217 apply the accepted B2 integrability theorem to the deterministic coefficient vector `incrementCoeff n h s t` and rewrite with the exact path-increment identity. B2's actual type quantifies over every real coefficient vector, including the empty vector. Its measure is exactly the same finite product probability measure. Integrability is proved separately, so the subsequent real integral inequality is not being made vacuous by the default value of a nonintegrable Bochner integral.

8. Lines 219–256 apply B2's actual mean-zero moment theorem with that same coefficient vector. The factor `β=∫|x|³dν` is nonnegative. Monotonicity of the real square root converts the energy estimate to the root estimate; nonnegativity of both roots justifies the square and cube multiplication inequalities. Multiplication by `24β≥0` preserves the order. The final rewrite is the actual path identity, and the numerical constant remains exactly 24.

The empty path `n=0`, zero time increment `s=t`, `s=0`, final time `t*h²=n`, integral-grid times and both affine endpoints are covered by these unrestricted finite-sum identities and non-strict inequalities. For `n=0`, the frozen time hypotheses force `s=t=0`; no positivity assumption on `n` was introduced. Atoms and lattice laws are unrestricted. No critical mathematical gap was found.

## All actual owned types and definition values

The environment difference, module ownership and stage-2 ownership lists agree exactly. They contain 18 constants: five public, nine explicit private and four generated; equivalently three transparent definitions and 15 theorems. I reviewed all 18 complete elaborated types in `round003/owned-interface.txt` and all three full definition values. `P.` below is `Shao.OQ4.PolygonalThirdMoment.`; `V.` is `_private.Shao.OQ4.PolygonalThirdMomentB3.0.Shao.OQ4.PolygonalThirdMoment.`. These abbreviations identify the exact actual names, not a namespace filter used to establish ownership.

| Exact name after the stated prefix | Coverage and finding |
|---|---|
| `P.polygonalPath` | Full type and value: actual finite ramp path, exactly frozen. |
| `P.polygonalPath_at_grid` | All `n,h,hh,a,k,hk` binders and the actual grid/prefix equality, correct. |
| `P.polygonalPath_on_grid_interval` | All binders including `hk,hu0,hu1`; exact two-prefix affine equality, correct. |
| `P.polygonal_increment_abs_cube_integrable` | Probability instance, third-moment premise, all time premises and actual product integral, correct. |
| `P.polygonal_increment_abs_cube_le` | Adds exactly `hmean`; same actual process/law and constant 24, correct. |
| `V.ramp` | Full real function type and clamped value, exactly frozen. |
| `V.incrementCoeff` | Full `n,h,s,t,i` type and the actual two-ramp difference divided by `h`, exactly frozen. |
| `V.ramp_bounds` | Conjunction `0≤ramp x ∧ ramp x≤1` for every real `x`, correct. |
| `V.ramp_monotone` | Ordinary real `Monotone ramp`, correct. |
| `V.ramp_eq_pos_sub` | Exact positive-part difference for every real input, correct. |
| `V.sum_ramp` | All natural lengths and real inputs; exact two-boundary telescoping formula, correct. |
| `V.ramp_grid_affine` | Natural `k,i`, real `u∈[0,1]`, correct indicator identity. |
| `V.polygonal_increment_eq_sum` | Unrestricted actual increment identity, correct. |
| `V.incrementCoeff_energy_le` | Exactly the frozen positive-scale/time-domain premises and bound `≤t-s`, correct. |
| `P.polygonalPath_on_grid_interval._simp_1_1` | Generated universally quantified additive-commutative-monoid finite-sum distributivity equality, correct. |
| `V.incrementCoeff.eq_1` | Generated unfolding equality, exactly its full definition value, correct. |
| `V.ramp.eq_1` | Generated unfolding equality, exactly its full definition value, correct. |
| `V.ramp_grid_affine._simp_1_2` | Generated preorder fact `(x<x)=False`, with its actual universe and instance binders, correct. |

The complete raw `Lean.Expr` exports contain all 18 types and all three transparent definition values, with no ellipsis. A local parser handles both literal names and nested `Lean.Name.mkStr`/`mkNum` encodings of private names. Its extracted constant sets match every exported type reference and every definition-value reference exactly. There are no owned opaque declarations or hidden owned axioms. The generated theorem types are auxiliary algebra/order facts, not stronger unreviewed assumptions.

## Exact server execution and transitive axioms

I reused the first successful source-bound execution, round003. Round001 and round002 remain failed evidence and contribute no pass; specifically the failed round002 closure count 34,797 is not the accepted count.

The actual execution response has exit code 0. The request specifies the pinned Lean `v4.36.0-rc1`, CPU18–21, the OQ4 exclusive flock, `-M8192 -j4`, `autoImplicit=false` and `debug.skipKernelTC=false`. The native audit independently records trust level 1025 with both Boolean options false. The command emits no B3 object. The final server metadata records the process reaped, zero active source Lean commands, and the heavy lock unheld. Elapsed time is **null**, because the original response supplies no elapsed field.

| Evidence | SHA256 | Bytes |
|---|---|---:|
| Actual request | `0858f6830cefc152d72b5f591ce94a86a7e984cc13daaca3c24a46c237767e20` | 4,871 |
| Actual execution response | `71aae302a334d16e26a6d7e15cb01b89db37ecfb59e3d419f206074392ac60aa` | 111 |
| Server stdout fingerprint | `24e17794946bc81a90021c9cf3a8337d22d9522b596df3ecf89eb8ab86d8094c` | 2,966 |
| Server stderr fingerprint | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| Audit export | `53aa42bd80edc7173fabcf60c7b98548557f4f5f66412f3bf0c321a8033067ce` | 24,989,278 |
| Raw expression export | `2a10168108af229f66e8a957c909a7a38e19be3252a3ce2592704e72c7a93b48` | 179,975 |
| Complete actual interface | `daf8b24447a8bb7cd9229319ddcaabfe50130a9d0e5fcae6547593053eeb900e` | 24,484 |
| Final author evidence receipt | `3d04be3bc38fde6b6513540c73192762d52bbbc2d09a540e82c701229a5c7151` | 17,182 |

There are six unused-variable warnings, concerning the two frozen grid-size hypotheses and the four frozen integrability time hypotheses, and zero errors. All frozen premises remain in the actual types.

I read the entire audit suffix. It captures ownership by three unfiltered environment methods, checks every owned root, and traverses both type and value references. It explicitly calls `ci.value? true` and rejects any unavailable opaque body. My independent local traversal verifies all 34,794 unique nodes and 951,755 directed type/value reference entries, with zero missing references, zero unreachable exported nodes, zero unsafe/partial declarations and zero new axioms. All 28 transitive opaque bodies are available; unavailable ordinary values occur only for constructors, inductives, recursors, quotient primitives and the three allowed axioms. Separate traversal from each of the 18 owned roots reproduces that root's exported axiom set. The complete union is exactly `propext`, `Classical.choice`, `Quot.sound`.

## Dependency and runtime binding review

The two actual project imports are only `Shao.Basic.FinitePath` and `Shao.OQ4.WeightedThirdMomentB2`. I checked the full actual public B2 types and their use here, and reused B2's qualified complete independent review rather than reviewing its accepted proof again. The B2 review receipt is SHA256 `71f1cf59ea46689df80f6542302035841089c0b8f6ef11d2a2876196e33f97b0`; its sole pure-source object receipt is `1f2cf961ac474ff8f54906e6aba588c32d8da7c722b498775bccbf201463e8ec`.

- B2 source: `72147edf65e2b322bf7ee43569004069ea9cc01be53753323b3c1c8c894681fe`; sole object: `9f17fff7fa969fa5e69c8cb06e8a0962280f033d93e58f1fdb0d47924e62a2bd`.
- Basic.FinitePath source: `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`; object: `14238ea05500cb0e3d6b105253aaeca80c5744612687a1054906de7dd64f2572`.

The actual 25 project dependency rows contain 24 rows exactly matching B2's accepted closure and the newly consumed, already accepted `Shao.prefixSum` interface. I inspected the actual prefix definition in the hash-bound curated source: it sums precisely those `Fin n` coordinates with `i.val<k`. No newly consumed mathematical interface is assumed without identification.

All 4,466 actual `findOLean` results match the current runtime-binding map. The 4,464 nonproject imports retain their exact accepted paths, resolved paths, fingerprints and target identities; the two project aliases resolve to the accepted objects above. The post-success project identity records match their pre-success records and actual resolver paths. This reuses the accepted read-only 4,653-entry runtime guard and 161-entry Init supplement through B2's hash-bound map; the actual imported subsets are 4,303 guard entries and 161 supplemental entries. There is no uncovered actual import, new cache hash, project rebuild or copied B2 object in this review. Raw logs and objects remain server evidence; I independently hash the local evidence files and reuse the recorded server log/object fingerprints without claiming a fresh local raw-log or cache rehash.

## Acceptance boundary

The frozen B3 finite-moment unit is fully reviewed and its exact source has a successful server kernel/all-owned transitive-axiom receipt: `LEAN_FULLY_CHECKED` for this unit. This report closes only the actual finite polygonal grid/affine identification and third-increment moment layer. Joint FDD convergence, path-space tightness, B0/B1, Brownian boundary continuity, killed-set limits, K/Kv and general OQ4 remain OPEN; rawleaf delta is zero. No novelty claim is made.

The complete deterministic consistency findings, per-root axiom coverage and exact artifact hashes are in `evidence-check.json` (SHA256 `abff19958f70e8710cfd91450eafed807db4b1efa2b557d54fd28a761929ecca`). This review was written only in its assigned review directory. Reviewer work is complete and write authority is released after delivery.
