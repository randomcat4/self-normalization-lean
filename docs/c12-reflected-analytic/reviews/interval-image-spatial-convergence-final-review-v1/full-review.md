STATUS: CORRECT
JUSTIFICATION: The final frozen module proves a genuine summable Gaussian bound and uniform convergence of the grouped actual spatial-derivative image tail on every closed positive-time strip. All eight complete statements and proofs, all 22 actual owned types, all four complete non-theorem values, the original source, and the exact author kernel/recursive-axiom evidence have been reviewed. There are no gaps within this frozen target.

# Independent final complete review: C12 unit55

This review covers only `Shao.C2.IntervalImageSpatialConvergence`. The reviewer is a fresh context distinct from the author. Its only write scope is `drafts/c12-lane/interval-image-spatial-convergence-final-review-v1/`; it made no production, freeze, shared, Git or cache edits, invoked no Lean/build/audit command, and created no children. Prescribed model/effort: `gpt-6.1-sol` / `xhigh`. Configuration comes from the parent task/spawn prescription; independent model telemetry and token counters are not exposed.

## Exact accepted target

| Artifact | SHA256 |
|---|---|
| Final source, 9030 bytes, 170 lines | `0f35dcb8ba433f3b68bb41379416ac4811c832e45b0ed0198c91461c1c776043` |
| Author output and installed object, 567344 bytes | `43367be3d89b272cba78d98c879dbced18499f12f8adb4331f2c82d323300223` |
| Current V2 freeze, 3174 bytes | `8ae88b65778451c0d96cbd1d1cb66abfd54b426aaddc9777b646560667862e16` |
| Preserved V1 freeze, 3122 bytes | `287868ee197a0edeb83c38c5c89e892b5b26ea2ee99eb42ffcdf3ca4a435f27a` |
| Author receipt | `fc2bb0426c7a6e8cd74744e39b71141adf6a3a0a6068f98f12c687f15687abaa` |
| Author writer/execution release | `e327456ba7df5c1649b3c842fb76e14fb9df5ae4357d81199f96f01fd8f20812` |
| Complete actual types, 27505 bytes | `9136e8692b9192ddb890cad77ffb5c535d306cc158c88cca4c2b9effee0406a5` |
| Complete actual values, 7966 bytes | `500770e0aa4fc5c88cf4ccb9b9ba543844194924558573db04dd765ad89dc6a8` |
| Module-owner recursive-axiom map | `33f930d4604c3b716de32901a28bac3743c180b97b545a9e7e435849ac1d2ad0` |

The final source, remote attempt002 snapshot, current remote worktree source, author output object and installed object agree with these bindings. All 12 receipt-listed remote artifacts and all seven corresponding locally present receipt-listed artifacts match exact hashes and byte lengths. Source encoding is UTF-8 without BOM, with LF endings and zero CR bytes. The complete import/namespace context, all eight full mathematical heads, and all four full definition values equal the final freeze exactly after removal of proof bodies.

## Original source and semantic scope

The full read-only source `C:/game/shao/current/c12/supplement.tex` has SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. Lines 4255–4300 were read completely, together with all context lines 4192–4254. The relevant original formulas are

- `A_m = 8 m² a² + 4 m a (z-y)`;
- `B_m = 2 (y+(2m+1)a) (z+(2m+1)a)`;
- differentiated individual image terms have a half-exponential bound; signed tails have quadratic Gaussian growth;
- normally convergent positive-time expansions are used at source lines 4298–4299 to justify later differentiations and traces.

Here `a>0`, the terminal endpoint satisfies `|z|<=a`, and `0<H<=U`. `StripPoint a H U` is exactly the set of pairs `(y,T)` with `|y|<=a` and `H<=T<=U`. Thus time is uniformly separated from zero. The theorem is uniform in `(y,T)` for each fixed natural derivative order `j` and admissible fixed `z`; it does not claim uniformity over all `j` simultaneously.

The complete `spatialTailBlock` value uses the actual ordinary spatial iterated derivatives with image indices `A_(n+2)`, `A_-(n+2)`, `B_(n+1)`, `B_-(n+2)` and signs `+,+,-,-`. Its derivative variable is `w`, while the walls, terminal endpoint and time remain fixed, as prescribed at source lines 4221–4222. The omitted finite terms are `A_0,A_1,A_-1,B_0,B_-1`. No identification with the full integer series is smuggled into this definition.

The proven bound is a genuine summable normal-convergence estimate for these grouped derivative-tail functions on the strip. It is the spatial, positive-time tail-convergence dependency of source line 4298. It is not the complete source derivative-and-Taylor lemma. In particular the theorem does not assert the derivative of an infinite sum, a full integer-series regrouping, the image/killed-kernel/Brownian-bridge probability identity, time or mixed derivative convergence, an actual one-sided trace identity, the quotient PDE, the high-time sine estimate, `hSmall`, or any original root closure. All original C12/OQ3/OQ4/OQ56 root groups remain OPEN.

## Complete proof review

1. `summable_exp_neg_nat_sq`, source lines 26–43. For `c>0`, positivity of `exp(-c)` and `exp(-c)<1` give a convergent geometric series. The proof checks `n=0` and `n>=1` separately to obtain `(n:Real)<=(n:Real)^2`. Multiplication by `-c<=0` reverses this inequality, and exponential monotonicity gives `exp(-c*n²)<=exp(-c*n)=exp(-c)^n`. The real norm is exactly the positive exponential. The comparison theorem proves the claimed `Summable`, with no missing finite prefix.

2. `gaussianMajorant_summable`, lines 45–47. It instantiates the preceding lemma with `c=4*a²/U`. Strict positivity follows from the explicit positive `a,U` assumptions, and the complete majorant value agrees definitionally. It makes no assertion for width zero or nonpositive upper time.

3. `tail_exponent_lower_bounds`, lines 49–75. The signed A tails use real parameter `m=n+2>=1`; the signed B tails use `m=n+1>=0`. The qualified B exponents at indices `0` and `-1` are nonnegative for closed endpoints. The A residual above `8*n²*a²` is bounded below by `8*a²*(3*n+2)>=0`, while the B residual is `8*a²*(2*n+1)>=0`. The negative B theorem has index `-m-1`, exactly `-(n+2)`, and the explicit rewrite preserves that shift. Every Nat-to-Int-to-Real cast in the actual owned type was read and checked. All four conjunction branches, including `n=0`, are correct.

4. `exponent_half_le_majorant`, lines 77–89. From `0<T<=U` obtain `U>0`. Let `q=8*n²*a²>=0`. The two positive-denominator comparisons give `q/(2U)<=q/(2T)<=C/(2T)`. Negating and applying exponential monotonicity gives the desired direction; field normalization identifies `q/(2U)=(4*a²/U)*n²`. The claim validly has no positive-`a` premise, because only `a²>=0` is needed.

5. `spatial_prefactor_bound`, lines 91–111. The closed endpoint conditions yield `|z-y|<=2a`. Since `0<H<=T`, both square roots are positive and `sqrt(H)<=sqrt(T)`. Reciprocal-denominator inequalities bound `4/sqrt(T)` by `4/sqrt(H)` and the distance quotient by `2a/sqrt(H)`. Both products and the natural power are compared only with the required nonnegative factors established. Multiplication by `1+2^j*j!>=0` gives exactly the full frozen prefactor. The argument includes `j=0`, `H=T` and endpoints on either wall.

6. `spatialTailBlock_bound`, lines 113–151. The strip provides `0<T`, the spatial bound, `H<=T` and `T<=U`. Each complete qualified actual jth-derivative profile is combined with the correct one of the four exponent lower bounds, the half-exponential-to-Gaussian estimate, and the common fixed spatial prefactor. All multiplication directions use explicitly nonnegative factors. The complete four-term absolute-value triangle inequality handles both minus signs. It yields exactly `norm(block)<=4*spatialPrefactor(j,a,H)*gaussianMajorant(a,U,n)`, independent of the strip point. The named `hHU` is redundant here because a supplied point already carries `T<=U`; retaining the frozen premise is harmless.

7. `spatialTailBlock_summable`, lines 153–157. The explicit `0<H<=U` implies `U>0`; Gaussian summability is scaled by the real constant `4*spatialPrefactor`. The universal norm bound satisfies every hypothesis of `Summable.of_norm_bounded` for the complete real normed additive group. This proves summability of the actual grouped derivative terms at every supplied strip point.

8. `spatialTailBlock_uniformly_convergent`, lines 159–168. The same summable scalar majorant and bound for every `n,p` instantiate the pinned `tendstoUniformly_tsum_nat` exactly. Its domain type is the strip subtype and its codomain is `Real`, with the required complete normed additive-group instances. The actual type has range-N partial sums and the pointwise unconditional `tsum`, at `Filter.atTop`. No continuity, differentiability of the sum, full-series identity or stronger function is assumed to derive convergence.

At derivative order zero the factorial and zero power are legitimate and only make the chosen constant loose. At tail index zero the Gaussian is one and every exponent lower bound is nonnegative, so no endpoint degeneracy is lost. Time zero and width zero are excluded exactly where the frozen claims say so. `H=U>0`, `y=±a`, `z=±a`, and vanishing individual image exponents are covered. The four image-index sequences are disjoint within each image family and contain precisely the stated tails; no omitted term is declared zero.

## Entire actual-owner coverage

The `OwnedAudit.lean` source was read completely. It enumerates every environment constant whose actual module index is this module, rather than selecting only a namespace prefix or public list. It runs transitive `Lean.collectAxioms` for every selected constant and rejects any axiom outside `propext`, `Classical.choice`, `Quot.sound`. Its successful map contains 22 actual owners: eight public source theorems, ten generated theorems and four definitions; there are no other kinds or other-namespace owners.

All 433 lines / 27505 bytes of `actual-owned-types.txt` were emitted and read without elision in contiguous exhaustive ranges. All 7966 bytes of `actual-definition-values.txt` were emitted and read literally. No sampling or dictionary encoding was used. Both exports were independently shown byte-for-byte equal to the corresponding complete blocks of the remote audit log. The owner names in the map and the type export agree exactly. All complete theorem actual types preserve the frozen binders, assumptions, quantifiers, codomains and target functions. All four complete actual values preserve their frozen values.

In addition to the eight public statements reviewed above, the entire generated type coverage is:

| Generated theorem | Complete actual statement checked |
|---|---|
| `spatialPrefactor._proof_1` | `Nat.AtLeastTwo (3+1)`, certificate for numeral 4 |
| `spatialPrefactor._proof_2` | `Nat.AtLeastTwo (1+1)`, certificate for numeral 2 |
| `exponent_half_le_majorant._simp_1_1` | Under the complete Zero/OfNat/NeZero hypotheses, `2=0` is equivalent to False |
| `exponent_half_le_majorant._simp_1_2` | The corresponding complete statement for numeral 3 |
| `exponent_half_le_majorant._simp_1_3` | The corresponding complete statement for numeral 4 |
| `exponent_half_le_majorant._simp_1_4` | Product of two nonzero elements is nonzero under Mul/Zero/NoZeroDivisors |
| `exponent_half_le_majorant._simp_1_5` | Every natural power of a nonzero element is nonzero under the full MonoidWithZero/IsReduced hypotheses |
| `exponent_half_le_majorant._simp_1_6` | Every integer power of a nonzero element is nonzero under GroupWithZero |
| `exponent_half_le_majorant._simp_1_7` | Natural cast plus one is nonzero under AddMonoidWithOne/CharZero |
| `spatialTailBlock_bound._simp_1_1` | `a+(-b)=a-b` in the full SubNegMonoid context |

The four definition types and values were each read in full: `StripPoint`, `spatialPrefactor`, `gaussianMajorant`, `spatialTailBlock`. There are no additional non-theorem constants whose values remain unread. Generated certificate proof terms are covered by the complete production proof context and existing source-bound kernel/axiom evidence; no extra generated-term expansion was invented as a requirement. The JSON report records every one of the 22 names, full-type block hash, axiom set and specific review, plus every full non-theorem-value block hash.

## Qualified dependency reuse and pinned interfaces

Unit53 `Shao.C2.IntervalImageExponents` is reused from qualified independent CORRECT review SHA256 `bc79b61da27e33e961f01411b52ded3c1fd10a569fa410aec6d275ef61e80731`, with source `a2ade7b54d268c9d9052d995309eceeaee3db8899fea95f2138fb2e2871d157b`, object `d7cf70b797a7567622e110104b1bb94a5144a77eef647646873f9293cc488072`, receipt `bebde98e69f421c0e39e454bfd6eb5e8149ace7eb8a913ab36bac9e45e398ab4`. The complete consumed actual interfaces `imageA`, `imageB`, `imageB_nonneg`, `imageA_positive_tail`, `imageA_negative_tail`, `imageB_positive_tail`, `imageB_negative_tail`, and complete `imageA,imageB` values were read. Their exact cast and sign conventions match all uses above.

Unit54 `Shao.C2.IntervalImageSpatialProfiles` is reused from qualified independent CORRECT review SHA256 `d5d6bdbf83c0d6cad7002d0e9b856bfb7bf5a6d3d607440a5eede8b5bae7b939`, with source `56592b1a2d9dc75067b4fe04d4867dc7f45e1449ef0abf08a63c55219ef17ca4`, object `d7e239194216e88373ddab9c8296738f9be0fd014dddfe6112211bc7e2d21847`, receipt `9e895e7b5a9de92bd9fe3ea89a88be02f531906a6aee8757e60955f9805f3754`. Both complete consumed actual derivative-profile types were read, including all their real/Int parameters, closed endpoint assumptions, positive-time assumption and precise half-exponential coefficients. Its sole complete definition value was also read. Neither unit's accepted proof was re-reviewed in full or rebuilt.

For both dependencies, current worktree source, retained source snapshot, author object, installed object, complete type/value exports and remote/local receipt hashes match the reused review bindings. There is no uncovered mathematical delta between the accepted interfaces and this consumer.

The complete consumed declarations and required variable contexts of `summable_geometric_of_norm_lt_one`, `Summable.of_norm_bounded`, `Summable.mul_left` and `tendstoUniformly_tsum_nat` were read from the accepted package view. The whole FunctionSeries source was also read. The relevant four Mathlib source files equal Git commit `807d3836b165983210ee2ecf3cd28f239436949c` byte-for-byte, despite the general package-working-tree warning. Real satisfies all displayed completeness, normed-ring, geometric-series and topological multiplication requirements. The existing FunctionSeries object was observed; no hydration or rebuild was performed.

## Freeze history, failed attempt and exact receipt reuse

V1 was frozen before implementation. Remote output-directory freeze mtimes reflect later archival copies and cannot establish that ordering. Instead, the exact original parent tool event at `2026-10-24T10:48:17.525Z`, session line 6546 / call `call_bdff944fce844f8e9e3b9717855b08de`, was independently read and its JSON-string `apply_patch` argument decoded. The complete added file reconstructs byte-for-byte to the archived 3122-byte V1 freeze SHA256 `287868ee197a0edeb83c38c5c89e892b5b26ea2ee99eb42ffcdf3ca4a435f27a`. The exact event-line hash without its terminator is `4d3faf9153da4952b2209363a55b3b055db3cfe6e5cbeef0245c4b3bc42b9f88`. Its matching successful output at line 6550 / `10:48:19.691Z` reports the same SHA, byte count, eight heads and four definitions. The retained parent provenance identifies first proof implementation at `10:50:54.311Z`.

The entire remote attempt001 failure log, complete source diff and entire attempt002 success log were read. Attempt001 fails because `tendstoUniformly_tsum_nat` is not imported; the subsequent `No goals to be solved` is a secondary consequence. The exact V1-to-V2 source and freeze deltas each add only `import Mathlib.Analysis.Normed.Group.FunctionSeries`. All mathematical heads, all four definition values, the rest of the context and every proof body remain unchanged. Local V2 freeze and import-only record timestamps `10:51:32.842328Z` precede the remote attempt002 source snapshot at `10:51:47.290504Z`. Both old and new full source projections equal their respective freezes exactly. Failure evidence remains retained.

The author receipt is kernel attempt002 / kernelExit 0 / auditExit 0. The successful log contains style/unused-variable warnings only; the exact object and complete module-owned recursive-axiom report match the source. The audit log has its completion marker for 22 constants / eight public / 18 theorems / four definitions. Every axiom is in the standard whitelist. The production source contains no `sorry`, `admit`, new `axiom`, `unsafe` or `native_decide`; complete exports contain no elision, unresolved metavariable or `sorryAx` marker.

Observed worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`; branch `author/c12-interval-gaussian-v71`; observed HEAD `b7c9d5d80f39b2eb2e942a114c2a90fff940dea3`. Pinned toolchain is `leanprover/lean4:v4.36.0-rc1`; package view is `/root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages`. The reused author commands record CPU14–17, `c12-heavy.lock`, `-M8192 -j4`. Reviewer execution was read-only observation, with zero Lean invocations, audit replays, producer recompiles or cache writes. Remote raw logs were read in place and were not copied into the workspace.

A first reviewer metadata-only proof projection used an unsuitable blank-line stripper; the established exact expression replaced it and both complete projections compare equal. A remote lookup lacked `rg`; a read-only Python lookup then located and exposed the full required pinned interfaces. These observation issues changed no source and caused no Lean/check replay.

## Disposition and release

CORRECT / `LEAN_FULLY_CHECKED_FOR_FINAL_FROZEN_LOCAL_TARGET_REUSED_AUTHOR_RECEIPT`, limited to the eight frozen local targets and their complete actual owners. No uncovered scope remains within this unit. Mathematical novelty and original root closure are not certified by this auxiliary analytic formalization.

The report is source/object/freeze/receipt bound, with exhaustive per-owner coverage in `full-review.json`, deterministic checks in `local-checks.json`, compact read-only server bindings in `remote-observation.json`, and exact original-freeze reconstruction in `freeze-provenance-verification.json`. Writer and execution authority are released explicitly in `writer-release.json`; heavy execution is false and the in-flight list is empty. Input, cached-input, output and reasoning-subset token counts are each null because not exposed; no subscription-percentage allocation is inferred.
