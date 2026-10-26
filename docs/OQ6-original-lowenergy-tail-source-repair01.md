# Unit 203 repair01 — same independent reviewer's affected source review

STATUS: SOURCE_CORRECT

The repaired `hLLinear` proof is mathematically correct under the unchanged frozen interfaces. Exact byte substitution and map validation show that it is the only changed named proof. I combine this affected review with my earlier complete, exact-hash-bound source review for the unchanged proof, statement, primary interfaces, scope and boundaries. This verdict is source-only: `qualified=false`, `actualOwned=UNKNOWN`, and native02/kernel/all-owned TYPE/FULLVALUE/recursive-AX review remain pending. It is not a prediction of successful elaboration.

I am the same independent reviewer, not the author or parent lead. My configured model/effort remain gpt-6.1-sol/xhigh; actual model/effort and input/cached-input/output/reasoning-subset counts are not exposed and are null. I wrote only inside this fresh `repair-source-01` directory. The earlier source seal and all author, frozen, shared, failure and interruption evidence remain immutable. Reviewer server/Lean/AX/upload/Git/API/network/child calls are zero; no local Lean probe was run.

## Exact version and reuse boundary

The reviewed repair is `author-01/stage2/repair-01/OriginalLowEnergyTail.lean`, SHA256 `77b67bfee626f5b9eb0cf97aeb2fa36c709f14f803d794093eb9c5536a9c1ce1`, 14282 UTF-8 bytes/320 LF, no BOM/CR and one final LF. It is exactly the old source `f2d4eeee50b5e2c9731b907fb73b56d3d531fbd32eefd9956966c048a6f1fb7b` with one unique byte fragment replaced. The old byte range is [9018,9351); the new range is [9018,9926). Both the shared prefix and suffix match byte-for-byte. The delta's `CharStart/End` fields are **PowerShell UTF-16 code-unit offsets**, not Python Unicode code-point indices; the independent validator uses UTF-16 slicing and independently derives the byte bounds. That representation distinction is not a source defect.

The unchanged complete source evidence is my earlier manifest `db84cb3702a2a777cabe45dc047fabfd397861a0315faba52af6ea210ad64f5a`, review `9ac507a2d3cd45099dd4e55774c1523cfd5a3462c824696b96603524abd2a9d0`, and coverage `10de9d71425b2d7e1e67b462049317868cb410966a2824b21c5861d03824d6b5`. Their payloads and controls were rechecked by exact hash, not rewritten. I reuse that full reading for unchanged content rather than claim a second full literal reading of all old proof/source/library bytes. I read the complete new 7167-byte repair notes, exact replacement, the entire affected named proof at current lines 201–227, and the three new anonymous equality obligations with complete types, proof terms, captures and scopes.

The repair author's manifest is `a0df98d7d709a2d5a5dade7a0047e72114f2913b24374067028fffe1cfa23903`, eight exact payloads/213937 bytes. Parent intake `880811c670855cde6670682132d8edaad478cb3e29a6bc005510c7adf176c33c` and author RELEASE0 `0eca3ae70ace7b139f32282dd844abf8c04e86cbbbb2222cd0b4072c4984679d` bind that source. All author writer/execution/heavy/inflight/pendingExternal/queuedLeanAX/children counts are zero. The declaration/data freeze `f21e3b9c228ee3d4902822e5bc1c44f9d28c053c54c774e61e066469a9123c0c` and canonical contract `4581c7789b4a9512d35d748c5cc70ca84b7e3fa01a3abf2dfd005c47b5a7e35b` remain exact.

## Complete affected proof review

The containing named fact remains `hLLinear : L ≤ 1 - 3 * s / 4`. At this point Y and Y² are integrable, f and U are integrable, f≤U pointwise, 7/8≤EY≤1, E(Y²)≤K, s>0 and s²K=s/8. These already reviewed inputs and their proofs are unchanged. The first step `L≤∫U` still uses integral monotonicity with `hfInt`, `hUInt` and `hPointwise`. The final moment/sign comparison and ring identity are byte-identical. Only representation of the integral linearity equality changes.

The first anonymous equality (lines 208–212) separates the constant-one integrand from the difference sY−s²Y²:

`∫[1−(sY−s²Y²)] = ∫1 − ∫[sY−s²Y²]`.

Its `exact integral_sub` term receives `integrable_const 1` and the difference of `hYInt.const_mul s` and `hYsqInt.const_mul (s^2)`. Thus both operands are proved integrable. The library theorem's function subtraction is definitionally the pointwise subtraction in the explicit expected type; this is precisely the representation for which the old rewrite matcher failed. Real-valued integration uses original Ω/mΩ/μ, with hμ supplying the finite-measure premise for the constant integrability. No new condition is assumed.

The second anonymous equality (lines 213–218) keeps the identical outer constant integral and separates the inner difference:

`∫1 − ∫[sY−s²Y²] = ∫1 − (∫sY − ∫s²Y²)`.

`congr 1` exposes the equality of the second operands of subtraction. The existing exact `integral_sub` term then uses the already established integrability of sY and s²Y². Congruence is an ordinary equality obligation, not an additional named mathematical interface. It requires no sign or probability assumption.

The third anonymous equality (lines 219–222) normalizes scalar multiplication and the constant integral:

`∫1 − (∫sY − ∫s²Y²) = 1 − (s·∫Y − s²·∫Y²)`.

The two `integral_const_mul` rewrites and `integral_const` are the same previously read primary APIs. `probReal_univ`, real smul-as-multiplication and one-multiplication give ∫1=1 under the original hμ. In particular no new normalization, finite-integral conclusion, or moment premise is imported. The resulting expression is exactly the old target of the linearity step. The unchanged inequalities use s≥0 and s²≥0 to substitute EY≥7/8 and E(Y²)≤K, then s²K=s/8 yields the desired coefficient 3/4.

The three full equality types, source spans/hashes, proofs and captures are in the attached coverage. Their direct source context is Ω, μ, s and Y; the first two proof terms also capture hYInt/hYsqInt. mΩ is inherited through the integral and integrability types; hμ is used for constant integrability in the first equality and probability normalization in the third. All real algebra/norm/integral classes are the pinned standard instances. Every new written o or anonymous `_ : Ω` is confined to its own integral. No n, sample point, new selector, alias, local data, named fact, helper, global instance, API or premise is introduced. All compiled minimal captures and actual owners remain unknown until the server audit.

## Interfaces, maps, scope and boundaries

The sole 520-byte public head remains `09361ab66494ab696223eab3331149c34d5ad11ee2b713dab8d66892b34aba88`. All eleven imports, namespace/options/open commands, 18 data types/initializers and 56 Prop heads/scopes match the old independent coverage and parent freeze. All 74 current source spans are independently revalidated. Exactly hLLinear has a changed proof block; the other 73 blocks are byte-identical, even where their positions shift. The six embedded raw expressions and all 35 literal `fun` source lines/types/corrected capture contexts are unchanged and rebound to current positions. The canonical 74-node dependency graph is acyclic. The author's broader static graph includes six embedded nodes and an empty-string non-node bookkeeping entry; the independent graph uses only actual canonical dependency names and introduces no mathematical dependency from that placeholder.

The repaired maps preserve my prior distinction between named-argument labels and free variables. Early `(F := Z) (f := X)` does not capture future F/f; `(μ := P) (f := F)` uses P/F. Generic cutoff and induction indices remain locally bound, and the Pi/summand captures remain scope-correct. The three new calc goals add implicit integrand lambdas and integral-bound dummy variables, fully covered by their displayed types, rather than new literal `fun` occurrences or frozen named declarations.

The selected cutoff stays at line 87; the result witness and forall n move to lines 239–240. Thus c stays fixed before n. The theorem retains arbitrary measurable Ω, probability μ, measurable g, MemLp g 2 μ and ∫g²=1. It gains no mean-zero, fourth/higher/exponential moment, boundedness, standard-Borel, atomless or n>0 condition. The reused full review still covers n=0, empty product/energy and strict empty event, zero values, atoms/repeated samples and unbounded g. The repaired equality is in the single-coordinate calculation before n, so none of those boundaries is changed.

Only the p51 S3/S11 lower-energy payment is covered. WV204, Gy union, full S11 and C2/C12/OQ56 remain OPEN; C1 immutablev85 remains complete and OQ3 PAUSED_BY_USER. p54 repairs and external Shao–Zhou 2016 (92)/Jing–Shao–Wang 2003 Lemma 6.4 attribution remain; no new external fulltext reading or novelty claim is made, and unified124 is not a prerequisite. Pinned Lean v4.36.0-rc1/mathlib807d3836 remain fixed. No old primary/library/producer/kernel/leafAX replay was performed.

## Failure preservation and machine boundary

The saved native01 diagnostic records natural RC1, one line207 rewrite error, one haveI style warning, no object, no timeout/cleanup and all owned processes ended. Receipt `fa1c818bc3a99ce77132c95acef6d86421a1d3b0fbcaac85566d19c153c4e67b` remains failed evidence. The unchanged haveI warning shifts to line247 and is retained. The standing stderr warning remains historical evidence. The author summary-expression failure, parent UTF16/code-point assertion failure and other display/projection failures were read and preserved; they did not mutate mathematical source and are not proof results. Earlier capacity interruptions remain execution interruptions, not mathematical or quota conclusions.

The independent binding gate passed with no failures; all 93 bound inputs remained unchanged through sealing. This review authorizes no reviewer execution. The next dependency belongs to the parent: first new native02 on these exact bytes, then if successful the **same first original object** all-actual full TYPE/non-theorem FULLVALUE/recursive-AX evidence. Final qualification must cover every module-index owner including private/generated/foreign namespaces, with whitelist propext/Classical.choice/Quot.sound. Resume this same independent context for final machine review in another new subdirectory; both source-review seals remain immutable. At release all reviewer writer/execution/heavy/inflight/pendingExternal/queuedLeanAX/child authority is zero.
