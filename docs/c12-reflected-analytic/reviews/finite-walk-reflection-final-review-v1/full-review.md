# Independent complete review: finite-walk reflection, units 91–92

STATUS: CORRECT

Both exact frozen auxiliary units are correct. The full final source proofs and statements, every actual owned type, and every actual non-theorem value have been reviewed independently. No critical gap was found. Exact original author kernel and whole-owned transitive-axiom evidence is reused; this reviewer ran no Lean/build/audit or Git command and changed no production source, freeze, cache or shared file.

The requested reviewer configuration is gpt-6.1-sol/xhigh. Actual model, effort and input/cached-input/output/reasoning-subset telemetry are unavailable and are recorded as null. No subscription-percentage inference is made. This fresh reviewer was separate from the author and spawned no children.

## Exact evidence and coverage

### Unit 91: Shao.C2.FiniteWalkReflection

- sourceSHA256: `1a032a7c13a63ec10a5cc0831e1c87909eb27743d439a48b2348e5f4daece97b`
- objectSHA256: `ced52a10853be67a1e233753e59aa40f51cd7dec8864d2b2415de744fc99b3f5`
- frozenSHA256: `c644f8fa148c54ea4274d1b815739cbe9def3241300fbb3ec58107cca96d7d5c`
- receiptSHA256: `bef8d7f4a3bdc4836b5062b5b2396a82be674777862a72c37608e7afd76054d2`
- authorReleaseSHA256: `d2ab41a072464b76c609f72f47fa8e26c8c00924f72443eccfe5ceb2bafb79e3`

Complete coverage: 15 public source theorems, 5 surface definitions, 40 actual owned declarations = 31 theorem constants + 9 definitions. All 40 full types and all 9 full definition values read without elision. Successful kernel attempt002, kernel/audit exit0.

### Unit 92: Shao.C2.FiniteWalkReflectionCount

- sourceSHA256: `84d896567bfce4a0b0a97752b08bef965aef0bce10dfeb409c96868bdc76b318`
- objectSHA256: `8432e055d6d624b50e59d8a64afd7c69736e2736c4af759effed1c4caf98b1ad`
- frozenSHA256: `ae0c51e7e62ca0ed25d6c1dea91559dacfea48cda89c150890b2689d7a1a5ea1`
- receiptSHA256: `b7738847ae994347e482b587ee242a4165460e483e8b5cad0d8f0dfb523fdb03`
- authorReleaseSHA256: `cda513434a64e55bad779560794c232b8f2011d566601ebeead5fe84b6f35311`

Complete coverage: 4 public source theorems, 0 surface definitions, 10 actual owned declarations = 9 theorem constants + 1 definitions. All 10 full types and all 1 full definition values read without elision. Successful kernel attempt001, kernel/audit exit0.

The combined counts are 19 source-public theorems, five surface definitions, 50 actual owned declarations, 40 actual theorem constants and ten actual definition values. Full types total29,532bytes and full values7,269bytes. Counts were derived from the exact audit owner/name maps and cross-checked against the complete exports, rather than copied from descriptions. All recursive/matcher/generated/alternate evaluator owners are included.

Selection uses `env.getModuleIdxFor?` to require the exact defining module. It does not filter by namespace or visibility. `Lean.collectAxioms` is invoked on every selected constant; all 50 results contain only `propext`, `Classical.choice`, `Quot.sound`. No forbidden source term occurs. The fully inspected `walkPrefix._unsafe_rec` name belongs to a compiler-generated alternate evaluator; the logical `walkPrefix` value uses `Nat.brecOn` with `_f`. No source theorem references that alternate evaluator and no user unsafe declaration or proof bypass is present.

The complete audit logs were read losslessly by verifying byte equality of every type/value block against the already-read complete exported files, then reading their complete residual warning/totals text. The complete three retained kernel logs were read. Unit91's complete failed source was also read: the sole delta replaces `by omega` with `by change ¬k ≤ j; omega` for the constructed `Fin.val`. All imports, context, 15 public heads and five full surface definition values are unchanged. The failure was arithmetic normalization, and is retained as a failure; it is not treated as a proof result. Unit92 passed its first check.

## Complete mathematical source review

The entire read-only supplement4192–4315 was read, with whole-file SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. It defines the strict Brownian-bridge completion as killed/free heat-kernel quotient, the zero-energy/wall conventions, profiles, derivative/PDE/Taylor conclusions and their proposed argument. Line4247 uses the half-line identity `f=1-exp(-2uv/T)` by reflection.

These units explicitly take an alternative finite-nearest-neighbor route toward that unpaid reflection step. The objects are natural-length Boolean words and integer prefixes, not a Brownian process or an assumed survival kernel. The finite result is faithful to its own frozen auxiliary statement, but is not the displayed Brownian formula. The source interval image/sine expansions and derivative/PDE/Taylor discussion remain outside this accepted scope. The source boundary conventions are not claimed to have been discharged by a finite word argument.

## Unit91: all five surface definitions and all 15 public proofs

- `boolStep`: Boolean true gives integer+1 and false gives−1. The exported complete value uses ordinary Bool equality/decidability and integer negation.
- `walkPrefix`: starts at0 and adds the actual indexed increment when k<n, otherwise0. Hence it is constant after n. `_f` implements the same recurrence through `Nat.below`; the full `_sunfold`, `_unsafe_rec` and matcher values were read and checked against the recurrence. The matcher is ordinary `Nat.casesOn`; no added mathematical input occurs.
- `reflectAfter`: flips exactly the increments with index i≥k. The position at time k, whose last used increment has index k−1, is retained.
- `firstHit`: selects the least natural k satisfying k≤n and prefix=h with `Nat.find`, or n+1 if no bounded hit exists. Its complete actual value contains a bounded-existence decidability instance and `Nat.find` of the explicit conjunction, with the declared sentinel branch.
- `reflectAtHit`: exactly `reflectAfter (firstHit h w) w`; it contains no assumed invariance or endpoint condition.
- `boolStep_not`: complete Boolean case split gives sign reversal.
- `walkPrefix_zero`: the recurrence's zero equation, by reflexivity.
- `walkPrefix_step_le_one`: in-range Boolean cases give increment±1; out-of-range gives0. Thus the upper-step bound holds at every natural k, including after n.
- `walkPrefix_reaches_level`: with h>0 the zero-time branch is contradictory; the induction either reuses an earlier exact hit or, if the previous integer prefix is below h, uses the upper-step bound and the endpoint premise to force the next prefix to equal h. Returned j≤k and k≤n keep the hit bounded. No continuity, parity, endpoint law or hitting conclusion is assumed.
- `reflectAfter_involutive`: coordinatewise double Boolean negation for flipped indices, identity otherwise, followed by function extensionality.
- `reflectAfter_eq_self_of_length_le`: i<n≤k excludes every flip, for every coordinate. Empty words are covered without a nonempty premise.
- `walkPrefix_reflectAfter_of_le`: induction on j≤k; the step index j<k is unflipped when j<n, and otherwise both increments are0. The repaired natural-value normalization changes no mathematics.
- `walkPrefix_reflectAfter_of_ge`: induction for all j≥k starts from equality at k; each in-range flipped increment changes sign, yielding `2*S_k-S_j`. The saturated step after length is also checked. No unstated k≤n or j≤n restriction is needed.
- `firstHit_spec`: the explicit existence branch reduces to `Nat.find_spec` for the conjunction k≤n and prefix=h.
- `firstHit_le_of_hit`: packages the supplied bounded exact hit and uses `Nat.find_min'` with precisely that conjunction.
- `firstHit_min`: j<firstHit≤n provides j≤n, so a hypothetical earlier equality would contradict `firstHit_le_of_hit`.
- `firstHit_reflectAtHit`: on a hit, the unchanged prefix at the original cut supplies a reflected hit, so the reflected firstHit is at most the original. If it were earlier, fixed-cut prefix preservation would give a forbidden earlier original hit. On a miss, firstHit=n+1 and reflection is the identity. Thus equality holds on all words, including zero-time hits.
- `reflectAtHit_involutive`: the proved firstHit preservation makes the second cut identical, and the fixed-cut involution cancels both reflections.
- `reflectAtHit_endpoint`: a bounded-hit premise gives cut≤n and prefix at cut=h; substitution into the post-cut formula gives exactly `2*h-S_n`.
- `reflectAtHit_bijective`: the standard involution-to-bijection lemma has no missing nonemptiness or finiteness condition.

All 31 actual theorem types were checked: the 15 public statements, six generated equation statements and ten generated arithmetic proof statements. Every arithmetic helper's full explicit variables/premises match the contradiction needed at its use. The nine complete actual definition values comprise the five surface definitions and four generated walk-recursion/matcher helpers.

The unrestricted reflection statements permit h=0, negative h and n=0. At h=0 the first hit is0 and all increments flip. On a miss the sentinel is outside every coordinate. At n=0 only h=0 hits; the unique empty word is fixed. Hitting at n permits an empty flipped suffix. Cuts beyond length and saturated prefixes satisfy the fixed-cut identities. Positivity appears explicitly only where upward crossing from0 requires it.

## Unit92: all four public proofs and the generated owner

- `reflectAtHit_hasHit`: the original least bounded hit remains a reflected hit because the position at the cut is unchanged. It permits any integer h under the explicit hit premise.
- `strictBelow_iff_noHit`: strict prefixes exclude equality directly. Conversely, a prefix not strictly below a positive h has prefix≥h, and unit91's exact crossing theorem produces a bounded hit. All k≤n, including0, occur in the predicate.
- `hit_endpoint_cdf_card`: an explicit equivalence maps a hit path with S_n≤x to its canonical reflected path. The endpoint formula gives S'_n=2h−S_n≥2h−x. The inverse also uses canonical reflection: a tail endpoint S_n≥2h−x exceeds h since x<h, so h>0 and unit91 crossing prove that it actually hits. Reflection preserves that hit and gives S'_n≤x. Both compositions equal the original subtype by the all-word involution and `Subtype.ext`. Neither inverse membership nor probability transport is assumed.
- `killed_endpoint_cdf_card`: set E to the actual S_n≤x word subtype and H to its actual bounded-hit predicate. `Equiv.sumCompl H` partitions E as H+¬H. Complete explicit subtype equivalences identify the hit side with hit-and-CDF, and the complement with strict-survival-and-CDF using the proved iff. `Nat.card_sum`, the preceding reflected-hit count, and additive commutation yield survivalCDF+reflectedTail=endpointCDF in the stated order.

All ten actual types and the one full generated definition value were read. `strictBelow_iff_noHit.match_1_1` is ordinary `Exists.casesOn` followed by `And.casesOn` into Prop. The other five generated theorem constants are the required arithmetic contradictions; no additional surface definition is concealed by the source count0.

No hidden infinite-cardinality fallback is used: `Fin.fintype n`, `Bool.fintype` and `Pi.instFintype` make Fin n→Bool a genuine finite function space, including n=0. `Finite.of_fintype` and repeated `Subtype.finite` supply the two `Finite` arguments required by `Nat.card_sum`. `Nat.card` therefore means the actual finite cardinalities here. Parity, unreachable endpoints, arbitrary negative x and the n=0 case need no extra assumption. For n=0, the reflected tail is empty under 0<h and x<h; both the surviving and total CDF sides agree according as0≤x.

## Library/import, chronology and server evidence

The complete needed declaration contexts and proofs of `Nat.findX/find/find_spec/find_min/find_min'`, `Bool.not` and double negation, `Function.Involutive` and its bijectivity lemma, `Nat.card`, `Nat.card_congr`, finite-guarded `Nat.card_sum`, and `Equiv.sumCompl` were read from the pinned server tree. The full relevant `Fin`, Bool, Pi-function and subtype finite-instance constructions and their conditions were also read. Their source hashes/ranges and the direct Cardinal.Finite object hash are recorded in `library-context-bindings.json`. Unit92's consumed project interfaces are the completely reviewed unit91 definitions and theorems in this same report.

Unit90 is solely the unit91 import anchor, with no explicit use of its declarations. Its exact qualified fresh independent full review is reused at SHA256 `0850a417ff9a7499ad383bb94a41274280c22601f4e32ddeecc06487f2023c1b`; source `24f57360865e681d281d6c24bd1c79b493bd33694fa5601b1758aea753095e34` and installed object `bccf5cf411d8f685d3ef67889a2fa54a700229798a69098d1c2afce9262dc279` match. The exact original source/freeze/receipt/release bindings and prior-review independence were checked. No old full proof or successful gate was replayed.

Original parent-rollout calls and completed results establish actual freeze-before-implementation, rather than file dates or author descriptions. Unit91 freeze call10258 completed14:38:00.612Z before implementation call10269 at14:38:52.746Z. Unit92 freeze call10350 completed14:43:25.283Z before implementation call10359 at14:44:28.384Z. Both original added freeze payloads reconstruct the exact present frozen bytes. Complete original implementation/kernel, repair and audit calls/results were read, including kernel001 failure, kernel002 success, first unit92 success, object installation and whole-owned audit exit0. Exact call IDs/timestamps/input-and-result hashes are recorded in `original-operation-bindings.json`.

Read-only server verification matched every retained receipt artifact, final source and snapshot, original object and installed object, plus both remote receipts. The two final sources are UTF-8 without BOM or CR. The live worktree branch/head are `author/c12-interval-identification-v71` / `23cc8da1f557e76c447cf9fadbcecc9e89024181`, Lean4.36.0-rc1 and mathlib807d3836b165983210ee2ecf3cd28f239436949c, accepted read-only shared-v34 package view. Original commands use CPU14–17, c12-heavy.lock, -M8192 -j4. No reviewer compilation, audit, cache write, source mutation or raw-log/binary download occurred. The retained mathlib-local-change warning and all deprecation warnings were read; the accepted pinned cache is reused, with exact needed source hashes recorded.

## Accepted scope and release

The accepted result is the exact finite nearest-neighbor reflection construction and two finite cardinality identities under their frozen premises. This is classical auxiliary mathematics; no novelty claim is made.

Rademacher product-law probability transport, the justified Brownian limit, actual Brownian numerical joint reflection, pointwise standard-bridge hUpper/hLower identification, the killed/free quotient, image/sine expansions, derivative/PDE/Taylor/hSmall and all original root closures remain OPEN. C12/OQ3/OQ4/OQ56 original root groups remain OPEN. OQ3 remains PAUSED_BY_USER; p54 repairs and external-result attribution are preserved.

The reviewer releases its writer and execution authority with zero heavy work and no in-flight operation. No production write authority was taken. The lead may continue by freezing the precise finite-count-to-Rademacher-law transport, without inferring Brownian or root closure.
