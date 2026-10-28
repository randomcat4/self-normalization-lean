# JK351 independent final source-to-statement and proof review

STATUS: CORRECT

JUSTIFICATION: The complete final 41-line source proves the frozen, all-dimension, all-nonzero-signed-integer, all-real-radius statement for the actual normalized product Haar measure. It identifies the requested set exactly with the preimage of a measurable product of closed balls under coordinatewise integer multiplication, proves preservation of that same measure using the pinned compact divisible-group and finite-product APIs, computes the rectangle volume, and derives the scalar-power upper bound. No bad-set estimate, independence hypothesis, replacement law, or desired measure formula is supplied as an input. The exact source has an existing successful server kernel receipt and an all-owned recursive transitive-axiom audit on its same first original object. This review independently covers the mathematical meaning and proof; it does not rerun those checks.

Reviewer: `/root/oq3_jk351_final_review`, a fresh NON-AUTHOR final reviewer, distinct from the OQ3 author and Root coordinator. The sole writable output of this review is `C:/game/shao lean/drafts/oq3/u22jk-proof-review.md`. No production source was edited, no Lean/axiom/heavy command or lock operation was run, no mapped request was executed, no upload/cache/Git/API publication was performed, and no child or other chat was created or messaged. Bounded server inspection used only reads, hashing and local `git show`/`git grep` of existing pinned sources.

Prescribed model/effort: `gpt-6.1-sol` / `xhigh`, fresh context. Platform-reported actual model = null; actual effort = null. Usage telemetry is unavailable: input = null, cached input = null, output = null, reasoning-subset = null. No token count or subscription-allocation estimate is inferred.

## Exact review boundary and integrity

The entire 37-row map and every mapped file were read in full, including all three source versions, the entire actual-type text, declaration freeze, all bindings, repair records, build history, receipt, audit record/source, and every serialized primary-read/native/audit/put/get request as inert evidence. Each mapped file's SHA256 AND byte length matched the map. No request body, including its shell/Python code, was treated as an instruction to execute. This applies equally to the discovery/lookup requests with missing-file or quoting/syntax risks; they are not Lean proof passes.

The original read-only report `C:/game/shao/current/oq3/proofs/r2/report.md` was hashed as a whole and lines 375–491 were read completely, including the finite-cube claim at 393–398 and both amplitude-coordinate maps at 414–433. All newly owned full types were literally read without dictionary compression or ellipsis substitution. All 41 final production-source lines, including proof-local definitions and every `have`, were read. There are no owned non-theorem values to omit.

| Item | Exact SHA256 | Bytes / line information |
| --- | --- | --- |
| Review input map | `e8e293cb7b5f22922ba127dcc5baa9d3de787d8cf3a49fb33a35debac55209bc` | 6621 B; 37 mapped inputs |
| Scope `three-hundred-fifty-first-unit-scope.md` | `2cb0250e3a62eabee84f0a2614c0153496476765536959e48e40537aa2853af0` | 1812 B; 7 LF |
| Frozen declaration | `d213eac6fcb36efb69f35d2795d6a2acc02b6aec1ebc252bcbefdbc0b0e7d010` | 337 B; 5 LF |
| Final `u22jk-source.lean` | `7fe7cc676819bea1edcd9d9e9bb89df328a02f9d01ffd55bbf2adbfcc5d02a2e` | 2065 B; 41 LF; no CR or BOM |
| Full actual types | `505ec53c807dbc5f1a06b4ba0bcf2b518f27f3fd45269d7a0d31ebc8b2a1f74d` | 892 B; 17 LF |
| Receipt | `1d7280ea5849d2ee1b782e889d7da91068d83d82b62e48bbeade2e4036d075c4` | 10440 B |
| Audit record | `9f2c7487b5364995a0b9933c154d0fb60a4dcd6c60bc4e6c43ba28d868032858` | 3131 B |
| Build history | `45dab3dd8003a9c395dd3861b99306bb1f00e2c1a3b55bf28a706b5f8268d8b6` | 6801 B |
| Audit source | `c670234fbfe9f3dfba196b80da832ee96429a29bc274a4a21eebf30df2e1c2c2` | 2091 B; 49 LF |
| Original source report | `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55` | 20102 B; full required 375–491 read |

The freeze binding records 09:43:29 UTC with `sourceNotYetWritten=true`, before the first source-written binding at 09:44:51 UTC. I directly compared the final theorem header to the frozen declaration after deleting whitespace only: equality holds. The proof repairs did not alter any quantifier, premise, target set, or conclusion. The source has no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`.

## Current authority and review method

I read the math-theorem skill and its prompt-library, openai-workflow and Lean-verification references, SERVER.md, the applicable current AGENTS general/source/proof rules and explicit 2026-10-27 OQ3 resumption, selected TEAM precedence/audit-output rules, and relevant REGISTRY fields. The current authoritative state and explicit later AGENTS resumption govern historical pause/resource paragraphs. Sole Root is `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`; sole OQ3 owner is `01a16c48-80ee-7520-a9d9-faeeb6d05c78`.

The phase file is `coordination/resource-reallocation-20261027/OQ3-RESUMPTION-PHASE-40.json`, SHA256 `2b69e1eb2251724f2236bd8176623e7445a794dbb12a4f17a346885469fba480`, 6181 B. It assigns OQ3 CPU36–39,44–47, the existing historical-name c12-heavy.lock, one heavy ceiling and one child ceiling, with pinned native `-M8192 -j4`. This reviewer has heavy allowance zero and performed no execution admission or lock acquisition. Recorded phase39 memory-helper labels describe the unchanged helper formula; the unit receipts explicitly bind phase40 and actual OQ3 affinity. I did not reinterpret a lease or dispatch as evidence of active execution.

The skill's generic recommendation to run Lean locally is superseded here by the explicit server-only and successful-evidence-reuse rules. The exact successful server receipts were inspected instead. No accepted old producer, current producer, leaf axiom check, or prior proof review was replayed.

## Natural statement and exact encoded meaning

Let C = R/Z = UnitAddCircle, with its quotient circular-distance norm and Haar mass one, and let μ_m be the finite product of these circle measures on Fin m → C. For every m : Nat, q : Int with q ≠ 0, and eps : Real, define

`B = {x : Fin m → UnitAddCircle | ∀ j, ‖q • x j‖ ≤ eps}`.

The theorem concludes both

`μ_m B = (ENNReal.ofReal (min 1 (2 * eps))) ^ m`

and

`μ_m B ≤ (ENNReal.ofReal (2 * eps)) ^ m`.

All quantifiers and the sole nonzero-integer premise occur explicitly in the final source lines 10–14 and in its frozen header. `Fin m` ranges over the whole requested finite dimension; no lower bound on m, positivity of eps, sign restriction on q, almost-everywhere modification of the target set, or choice of a substitute measure is introduced. The `ofReal` truncation and empty-product exponent convention are part of the stated conclusion, not hidden premises.

The primary definition in Topology/Instances/AddCircle/Defs.lean:189–203 is the actual additive quotient by integer multiples of the period, with coercion respecting signed integer scalar multiplication. Real.lean:45–52 makes UnitAddCircle exactly AddCircle (1 : Real). Analysis/Normed/Group/AddCircle.lean:43 defines the quotient NormedAddCommGroup, its complete norm proof at 68–86 and UnitAddCircle.norm_eq at 223 identify the norm with `|t - round t|` for a real representative. Thus the norm in B is distance to the nearest integer. It is not the constant Euclidean norm of a point on a complex unit circle and has no implicit 2π factor.

Periodic.lean:61–85 equips AddCircle T with `ofReal T • addHaarMeasure top`, proves total mass `ofReal T`, additive Haar invariance and finiteness. At T=1 this is exactly Haar mass one. Pi.lean:214–216 and 660–662 identify function-space volume with the finite product of those same coordinate volumes. This fixes the normalization before the bad set is measured.

## Complete proof review, lines 15–38

1. Lines 15–17 introduce only proof-local objects: `F x j = q • x j` and `S = Set.pi Set.univ (fun _ => Metric.closedBall 0 eps)`. These are the actual coordinatewise multiplication map and the full closed-ball rectangle. They are not global definitions, assumptions, or statement lets.

2. Lines 18–20 prove `MeasurePreserving F volume volume` using `volume_preserving_pi` on each coordinate's `Measure.measurePreserving_zsmul volume hq`. The pinned source for the latter is the `@[to_additive]` theorem measurePreserving_zpow in MeasureTheory.Measure, Unique.lean:1028–1032, with the full namespace and variable context read. Its conditions are a commutative topological group, Borel measurable structure, Haar measure, compactness and integer rootability; the additive translation uses AddCommGroup and integer divisibility. Real.lean:33–35 proves the circle compact for positive period; Defs.lean:556–574 constructs DivisibleBy (AddCircle p) Int by division of a representative and proves cancellation for every nonzero signed integer. Divisible.lean:90–117 makes the resulting map surjective. The quotient supplies its topological/Borel structure, and Periodic supplies the actual Haar measure. The instantiated conditions are properties of the specified circle, not new user hypotheses.

   The underlying continuous-surjective-hom Haar theorem, Unique.lean:943–967, was read with its complete proof and type context. It requires equal total masses and fixes the scalar by that equality; here both measures are literally the same volume, so equality is reflexive. Its compact-codomain Haar uniqueness route supplies the required finite/inner-regular setting; the direct signed-multiplication API does not require an omitted user regularity hypothesis. It does not assume the desired bad-set measure. Negative q is explicitly covered by Int divisibility and the signed scalar theorem, with no replacement of q by a positive natural and no missing negative-sign case.

   The full finite-product preservation theorem and proof at Pi.lean:908–925 use coordinate measurability and equality of pushforwards, under sigma-finiteness of target coordinate measures. Each circle measure is finite, hence sigma-finite. This proves preservation of the same finite-product volume, without a separately assumed independence assertion. F may have several preimages when |q| > 1; surjectivity, not injectivity, is the condition used, so no incorrect 1/|q| factor occurs.

3. Lines 21–23 prove `MeasurableSet S`. The complete MeasurableSet.pi contract/proof at MeasurableSpace/Constructions.lean:708–718 requires countability of the index set and measurability of each coordinate set. Fin m is finite/countable, and a metric closed ball is Borel for every real radius. Nothing requires eps ≥ 0. The rectangle is defined by Set.pi and remains valid in dimension zero.

4. Lines 24–26 prove the literal set identity `B = F ⁻¹' S` by extensionality and the full pi/closed-ball membership equivalences, followed by `dist_zero_right`. For each coordinate it transforms `F x j ∈ closedBall 0 eps` into `‖q • x j‖ ≤ eps`. It neither enlarges B to a different event nor replaces its measure by an estimate. The two generated `_simp` declarations implement these membership equalities; their complete actual types are reviewed below.

5. Lines 27–35 compute the exact measure. Line 30 uses `hF.measure_preimage hS.nullMeasurableSet`. The complete pinned measure_preimage theorem/proof in Dynamics/Ergodic/MeasurePreserving.lean:142–145 requires a NullMeasurableSet in the target measure, exactly what hS.nullMeasurableSet supplies. It gives `volume (F ⁻¹' S) = volume S`, with source and target measures both the intended volume.

   Lines 31–32 apply volume_pi_pi to this rectangle. Its complete contract at Pi.lean:664–666, finite product definition and underlying pi_pi proof at 291–294 were read. No nonempty-index or positive-radius condition is present. Lines 33–35 use AddCircle.volume_closedBall and the constant finite product identity, with `Fintype.card (Fin m) = m`. The entire closed-ball formula and proof at Periodic.lean:102–119 was read: its input is any real eps, its sole period constraint is Fact (0 < T), and its value is `ofReal (min T (2 * eps))`. At T=1 this gives the stated factor exactly. The proof accounts for the half-period saturation and boundary through the actual quotient closed-ball preimage and an interval fundamental domain. No source-specific bad-set theorem is imported; the imported facts are classical Haar and product-measure APIs.

6. Lines 36–38 pair the equality with the upper bound. After rewriting by hvolume, `min 1 (2 * eps) ≤ 2 * eps` passes through monotonicity of ENNReal.ofReal and then through the natural power. The explicit lower-base nonnegativity is bottom ≤ ofReal(...), so it holds even when eps is negative. There is no unstated positivity side condition, reversal of the comparison, or illicit finite-real subtraction from an infinite measure.

Every declaration, proof-local let, local hypothesis, and final conjunction branch is covered by this review. The theorem is a direct library-based measure computation, not a circular dependency on the desired estimate.

## Boundary and failure attacks

- m=0: Fin 0 is empty, the predicate is vacuous and B is the entire one-point empty product. The rectangle/product-volume theorem gives the empty product 1. Both right sides are `a^0 = 1`, including a=0. All preservation and measurability APIs used also allow this index type. Thus no m>0 premise is needed or hidden.
- eps<0 with m>0: every norm is nonnegative, so B is empty; both `ofReal (min 1 (2 * eps))` and `ofReal (2 * eps)` are zero. The equality and upper bound correctly become zero. When m=0 the preceding empty-product calculation correctly gives one instead.
- eps=0 with m>0: the event consists of the finite q-torsion coordinate grid and has zero Haar product volume. The closed-ball formula gives zero and the proof obtains this through preservation, without silently substituting open balls or dropping the boundary. Dimension zero still gives one.
- 0<eps<1/2: the coordinate closed ball has length 2*eps on the period-one circle, so the exact factor and upper bound coincide.
- eps=1/2 and eps>1/2: the closed ball is the entire circle, including the antipodal boundary, and the exact measure saturates at one. The claimed upper bound remains at least one in positive dimension, and equals one in dimension zero.
- q<0: multiplication is a continuous surjective additive homomorphism by integer divisibility; the signed theorem applies directly. q=0 is explicitly excluded and would generally make the asserted formula false, so the premise is mathematically substantive and correctly used.
- There is no independence assumption, no law chosen to encode the answer, no real-coordinate pullback smuggled into a finite-torus theorem, and no normalization change to a 2π-periodic metric.

## Full actual ownership, types and axioms

The entire actual-types file is 17 LF / 892 B. Its three actual module-owned declarations are:

| Actual owned name | Full semantic type reviewed | Axioms |
| --- | --- | --- |
| `Shao.OQ3.torus_simultaneous_bad_set_volume._simp_1_1` | For every dependent family, index set s, coordinate sets t and function f, `(f ∈ s.pi t) = (∀ i ∈ s, f i ∈ t i)` | propext |
| `Shao.OQ3.torus_simultaneous_bad_set_volume._simp_1_2` | For every PseudoMetricSpace, x,y and real eps, `(y ∈ Metric.closedBall x eps) = (dist y x ≤ eps)` | propext, Classical.choice, Quot.sound |
| `Shao.OQ3.torus_simultaneous_bad_set_volume` | The complete frozen all-m/all-signed-q/nonzero/all-eps conjunction above | propext, Classical.choice, Quot.sound |

The table is explanatory; the underlying full types, including all universe/binder/instance contexts, were read literally in the original text. They contain no ellipses, hidden dependent lets, added premise, or extra target. The two generated theorem types are proposition-equality forms of the source's membership simplifications. There are exactly 3 TYPEs, 3 theorems, 1 public source theorem, 2 generated theorems, 0 non-theorem VALUEs, and 0 statement lets. F and S are proof-local, fully read objects and do not require separate owned VALUE entries.

The complete Audit.lean was read. It enumerates env.constants and selects by `env.getModuleIdxFor?` equal to the actual module, not by a namespace prefix or a handpicked public-only list. It rejects any owned axiom; recursively applies Lean.collectAxioms to every actual-owned declaration; rejects any axiom outside propext, Classical.choice and Quot.sound; checks safe definitions if any; and checks the single frozen target. The complete 1144 B audit log confirms all counts and the axiom gate PASS. No generated/private/non-theorem owner is silently excluded. Printing enormous theorem proof terms is not required by the current TEAM rule; the full 41-line source proofs and complete actual types were reviewed instead.

## Server and pinned-primary evidence reused

Read-only inspection independently observed worktree `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`, HEAD `b3d26f999234dc45deef150448757e130bbd7d83`, toolchain file `leanprover/lean4:v4.36.0-rc1`, and mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c` in the shared-v34 package view. Current production source bytes equal preserved source-03. Sixteen corresponding run artifacts were mechanically checked against local mapped hashes/byte lengths, including all sources, four whole logs, frozen scope/declaration, receipt/history/audit/type/binding files.

The first original object is 77968 B, SHA256 `3c437efaa3a66e2d42582d94d4ffdb822c34c3554960b0892021931f12052840`. The accepted-source-view entry is a symlink to that exact original object: resolved paths are equal and the content hash/byte count match. The audit request checks the object's hash before and after auditing; the observed current object is unchanged. There was no post-PASS source edit, object copy or reviewer rebuild.

- Native attempt003: natural RC0, 4.833816623315215 seconds, complete log 133 B, SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`.
- Same-first-object all-owned audit: natural RC0, 5.485719088464975 seconds, complete log 1144 B, SHA256 `3cc27ad42a14f38322243741bba568b47524fbc8bc8d5280bb36719d225596d9`.

Both whole logs were read. The sole successful-native diagnostic is the generic existing mathlib-local-changes warning. The required primary source files were independently compared byte-for-byte with local `git show` at the pinned commit, so that warning does not conceal an altered primary contract in this review.

| Required pinned primary | Whole-file SHA256 / bytes | Complete relevant contracts/proofs/context read |
| --- | --- | --- |
| MeasureTheory/Integral/IntervalIntegral/Periodic.lean | `9aea999167a463bbd43b9989cf51a5cf8e6e1cf09ec474b7bfd0c6c051a8dae5` / 23668 B | imports and namespace; fundamental-domain proof; 61–100 actual measure/Haar/finite/quotient normalization; 102–119 complete closed-ball formula proof |
| MeasureTheory/Measure/Haar/Unique.lean | `243cfd79d72daa1fdc96ae44fbba0b0434e428df6abd0f8d1b8e3c49a72b1016` / 60926 B | namespace MeasureTheory.Measure and group variables; 943–967 complete continuous-surjective-hom theorem/proof; 973–1039 commutative/compact/rootable context and complete integer multiplication route |
| MeasureTheory/Constructions/Pi.lean | `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef` / 47126 B | finite-index context; product measure/MeasureSpace definition; pi_pi and empty-index-compatible context; volume_pi/volume_pi_pi at 660–666; complete measurePreserving_pi and volume_preserving_pi 908–925 |

Additional directly inspected pinned definitions/contracts were also byte-compared with the same commit: AddCircle/Defs.lean `f11657ae9714b0ec56030bfab7a7f2c462b531d3e39c27c410d2a5c62b70071b` (36700 B); AddCircle/Real.lean `e3106d477af53038e6eacf5da730df7a09c57f786ef88eb5e15655aa0016d625` (3104 B); Analysis/Normed/Group/AddCircle.lean `a1d30f7eb7fa7d6d9b1105d668151062d9c0e6cb48e9873f20754d6dd89a0616` (9371 B); GroupTheory/Divisible.lean `8efcea8025081f16a3515bd8a772d88ee05d2b1669882e3e72087367c39eb16b` (10636 B); Dynamics/Ergodic/MeasurePreserving.lean `c4623b5a97ea419bfa2698cc8643e1aa937a5e1fec3501bdb56e07159f0decde` (11787 B); MeasurableSpace/Constructions.lean `03bdd1fd16c69f61acf8ae50d684f54c9b565d03c6fa880fc338fcbd3bbebadb` (49519 B); and MeasurableSpace/Pi.lean `a50acacac9f9b3195d6746cc234f4dd5c49dcd55f1bb9101061393e5c9064b85` (4780 B). Only required intervals/contracts were read from large primary files; I do not claim to have reviewed every unrelated theorem in them.

A bounded read-only discovery command initially found rg unavailable on the server; it had already returned the requested preceding primary excerpts and then ended RC1. Subsequent bounded searches used local Git's grep. This was a read-only tool availability failure, not a mathematical/Lean result, and caused no replay of a mapped request or gate.

## Complete failed-attempt denominator and repairs

All three preserved source attempts were read completely and hashed locally and against their server snapshots. All failed and successful logs were read in full; neither failed attempt is counted as proof success.

| Attempt | Source SHA256 / bytes / LF | Natural result and complete log binding |
| --- | --- | --- |
| 001 | `333bd08dc769066fb37b22828938399749dead6c3a2a1086bfabcd3fb6807cdd` / 1962 B / 41 LF | RC1 / 2.277741702273488 s; 408 B log `2d8f2c9229348160cc7f53382c79d0d75d894638e0cb118bc919dae990b3e010`; missing unnecessary Group.AddCircle compiled object |
| 002 | `27aa01066f339a8dc536b95dd88854d34688699f19f2665ba379a5c82b2cab50` / 1981 B / 41 LF | RC1 / 4.677317924797535 s; 1138 B log `27c5ada317e13ef78f7dd05365a54fa372d96ce806255db3c158191222140ee5`; namespace, NullMeasurableSet argument and ENNReal zero-bound interface errors |
| 003 | `7fe7cc676819bea1edcd9d9e9bb89df328a02f9d01ffd55bbf2adbfcc5d02a2e` / 2065 B / 41 LF | RC0 / 4.833816623315215 s; exact source reviewed here |

Repair001 replaces the unnecessary Group.AddCircle import with the already compiled, verified Periodic primary that actually supplies measureSpace/closed-ball volume. Repair002 qualifies the generated theorem with Measure, supplies `hS.nullMeasurableSet`, and spells out ENNReal nonnegativity via bot_le. The final source differs from source02 only at those three proof references. These are interface repairs, with no mathematical premise, frozen declaration, resource limit or desired conclusion changed. Their archived failures and repair records remain intact; the reviewer made no repair.

## Original-source implication, exclusions and verdict

Original report 393–398 needs a q-independent simultaneous small-distance cube estimate before substituting eps = q^(-gamma), summing and applying Borel–Cantelli. JK351 supplies the exact finite-torus measure and its upper bound for any finite dimension, so in particular for dimensions 7 and 6 used with gamma=3/16 in 414–415. It is a mathematically sound component of that route.

It does not yet prove the real-ratio pullback, signed-integer summability and Borel–Cantelli conclusion, passage from almost-everywhere torus coordinates to the two ratio maps on one positive ordered eight-amplitude vector, null-set pullback/Fubini or actual witness existence. It also does not establish near-resonance, strong-nonlattice failure, genuine nonlattice, the small-positive global saddle, the original D strictness theorem or the OQ3 root. Those source obligations remain OPEN, as the scope explicitly says. The period-one normalization has been verified here; a future 2π real-phase conversion still needs its own correct scaling argument.

Correctness is accepted for this exact JK351 source only. This is a classical Haar/product-measure consequence and no novelty claim is made. There are no critical gaps in the frozen statement, complete proof, actual owned type/value coverage or inspected exact machine-evidence bindings. Root/lane acceptance may reuse this qualified independent review with the existing same-source/same-first-object receipts; this report does not itself publish, merge or assert completion of later scope.

## Final integrity and release

The finalization script rehashed all 37 mapped inputs, the map itself, the scope and frozen declaration after writing this report, with exact SHA256 and byte-length checks. It then read back the ENTIRE saved report. The report's own SHA256/bytes/LF are returned separately because embedding its own digest would be circular.

Runtime state at release: COMPLETED_STOPPED. Sole report writer RELEASED. Reviewer heavy=0, inflight=0, pending=0, uncertain=0, children=0. No next unit or additional authority is taken.
