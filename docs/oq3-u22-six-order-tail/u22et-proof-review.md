# ET231 independent complete final review

STATUS: CORRECT

JUSTIFICATION: The complete current 68-LF source proves both exact frozen public declarations. The actual fiber cardinalities give the three finite-word identities with their full quantifiers. The actual normalized degree hypothesis, together with the same word and q <= 6, yields the stated physical degree interval. All seven actual-owned declarations, including all five generated omega certificate types, are covered below. The first successful complete native receipt and the same-first-object all-owner transitive-axiom receipt bind the reviewed source exactly and pass with only the three allowed standard axioms. No critical mathematical, statement-fidelity, or evidence-binding gap was found.

Review role: fresh independent final reviewer, delegated configuration gpt-6.1-sol / xhigh. The parent is the proof author; this reviewer made no proof, frozen-statement, source, or receipt changes. This review uses math-theorem, not math-ultra. The only owned output is this report. No server connection, Lean/AX execution, Git/publication operation, external-chat message, additional agent, or accepted-check replay was performed by this reviewer.

## Exact reviewed inputs

All paths below are relative to `C:/game/shao lean/drafts/oq3/`. Hashes are SHA-256. The whole source, frozen declaration, scope, actual types, audit source, audit record, failure provenance, and primary API extraction were read. Receipt/build-history fields were parsed completely; duplicated history and resource structures were compared mechanically rather than repeatedly displayed.

| Input | Bytes / LF | SHA-256 |
| --- | --- | --- |
| u22et-source.lean | 2621 / 68 | 3de6e3398858f80b78a02b1e38d5da776d454af66c327df772d8f6c5d31a8a3c |
| u22et-frozen-declaration.lean.txt | 602 / 11 | 3b39f9fff87d3f387f6ec7ab95ecc8a53cb2f4496cdc8aad0bdedb0c71c46371 |
| two-hundred-thirty-first-unit-scope.md | 1567 / 24 | 28c6690461d9707f6d7119d45a0a502f7ebc3a9a7dcababa9e9f466fc6991eed |
| u22et-actual-types.txt | 2021 / 35 | b9f3f161665dd5fb7a00dbf896575b30263ac71d4a1ac9075911cead09d9da5e |
| u22et-Audit.lean | 2032 / 47 | b95a6d815f562f39c5a15823bffa7e0f93ef8cdb468455b94878b6f292671ad9 |
| u22et-audit-record.json | 3374 / 109 | 02fd7410141bf5188fab28d60fff9e491eef13ad7a8d064d9cade4d33133bbe7 |
| u22et-receipt.json | 12649 / 431 | eba40e67934a4303133b58ff3beb0e9513365b0633a92bc2b9bc7aa432088f28 |
| u22et-build-history.json | 8613 / 322 | af4757b3bf740cb7b91f91cc5ae19435963d9ed109794c58bcbee2b2979fb45e |
| u22et-import-only-failure-provenance.json | 1670 / 50 | 750f65003d5f3f4607b1d651fd34a4dda61366610ff8311ca461631262df6407 |
| u22et-primary-api.txt | 3281 / 112 | cde773ec32b25dc0859f65a7aa2441e05f1506482bf5dd2f29de5e672ccfab5b |

These local inputs are UTF-8/LF with zero CR bytes. The two public source signatures, after removing only their proof-introducing ` := by`, concatenate to the frozen file byte for byte, including its one blank separator and final LF. Their reconstructed hash is the exact frozen hash above. No signature or premise was repaired during this review.

Additional original-source coverage: `C:/game/shao/current/oq3/proofs/r2/report.md`, whole hash 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55, lines 1-158 and terminal scope/accounting lines 486-523; `C:/game/shao/current/oq3/verdict.md`, whole hash fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5, all 58 LF. This is the assigned original-source scope, not a claim to have rereviewed all 523 lines of the analytic proof.

## First public theorem: finite_word_monomial_encoding

Source lines 11-42 and actual-type lines 10-16 were fully reviewed. The quantifiers range over arbitrary finite types ι and κ, in independent universes, with `[DecidableEq κ]` explicit before the statement is elaborated. The function sigma is an arbitrary actual word ι -> κ. There is no injectivity, surjectivity, nonemptiness, ordering, law, or asymptotic hypothesis.

The single statement-level let is exactly `p j := Fintype.card {i : ι // sigma i = j}`. Thus p is the actual multiplicity function of this same sigma. It is not a free exponent vector and no desired degree condition is inserted through it. The displayed actual type's `have p := ...;` is Lean's pretty-printing of this same dependent let, not an additional assumption or theorem-owned definition. The explicit decidable equality supplies finite fiber instances; `classical` in the proof supplies any further proof-side instances without changing the statement.

For an arbitrary natural weight function w, lines 20-25 show that the inner sum over the j fiber is `w j * p j`: every fiber member carries its equality `sigma i = j`, `sum_congr` rewrites the summand using that equality, and the finite sum of a constant is its natural cardinal multiple. Natural multiplication commutativity gives the displayed orientation. Lines 26-29 use the equality in the reverse direction for every outer j and then apply `Fintype.sum_fiberwise sigma (fun i => w (sigma i))`. Each position i appears in exactly its actual sigma fiber, so this is an exact partition identity, not an estimate. Lines 30-31 specialize the already universal weight identity to w = 1 and simplify both finite sums, proving total multiplicity equals `Fintype.card ι`.

For an arbitrary complex input function a, lines 33-38 rewrite every factor in a fiber to `a j`, then use the finite constant-product identity to obtain `a j ^ p j`. Lines 39-42 reverse this equality inside the outer product and apply `Fintype.prod_fiberwise sigma (fun i => a (sigma i))`. Complex multiplication is commutative, which permits this regrouping without retaining the order of the original positions. This proves the product-of-powers identity for the same actual word and its actual counts. Both regrouping equalities have the orientations needed by the calculation; as equalities, the resulting weighted-sum and product identities can also be used symmetrically by a consumer.

The primary packet contains the pinned `Fintype.prod_fiberwise` declaration and proof with `[Fintype ι] [Fintype κ] [CommMonoid M] [DecidableEq κ]`, together with its `@[to_additive]` tag. Its generated additive counterpart is precisely the sum-over-subtype-fibers identity used here, with AddCommMonoid replacing CommMonoid. It imposes no extra range or surjectivity condition. The packet also includes `Finset.prod_fiberwise`, `Finset.prod_const`, its generated simp additive counterpart, and their namespace/typeclass contexts. Pinned primary file hashes are 45b548e8d8491da4820c71eb29b0a2c92786f98e300d947e677f6fbe16e6f78a for `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` and fea364f581c3617c70802adff7fcddc40f5d60b53aa97541b418e4f33fac9a34 for `Mathlib/Algebra/BigOperators/Ring/Finset.lean`. The elementary cardinal identities used by simp have their ordinary Fintype meanings: the sum of 1 counts elements and `card (Fin q) = q`. The successful exact-source kernel receipt confirms these simplifications in the pinned environment; this review did not request another check.

Boundary coverage is complete for this statement. Empty ι gives zero counts and empty sums/products. An unused letter has an empty fiber and exponent zero, so its product factor is 1, including when its complex input is zero. Empty κ is compatible only with those ι admitting the given function, and the fiberwise partition still applies. Repeated letters are counted with their full multiplicity; there is no assumption that positions have distinct letters. Complex signs, phases, and zero inputs are unrestricted. Natural w is the exact stated domain; the theorem does not claim a signed-weight extension. No division, cancellation, positivity of a, logarithm, or branch choice occurs.

The theorem encodes each word by its counts. It does not assert a bijection from words to multiplicity vectors, an inverse construction for arbitrary counts, a multinomial coefficient formula, or a grouping-of-coefficients formula. The many-to-one loss of word order is harmless for the proved commutative identities and remains relevant to the later coefficient assembly.

## Second public theorem: fin_six_word_physical_degree_bounds

Source lines 44-65 and actual-type lines 5-9 were fully reviewed. The exact inputs are a natural q, q <= 6, an actual sigma : Fin q -> Fin 6, and the actual normalized degree hypothesis `7 <= sum_i ((sigma i).val + 1)`. The conclusion is the conjunction `9 <= sum_i ((sigma i).val + 3)` and that same physical sum <= 48. The actual type prints natural `.val` as a coercion; it introduces no real/complex reinterpretation.

Lines 49-53 derive 1 <= q rather than assuming it. If this fails, natural arithmetic gives q = 0. Substitution makes the index type empty, so the normalized sum is zero and hdegree is contradictory. Thus the empty Taylor word cannot enter the omitted-degree branch. In fact q = 1 is also impossible under hdegree because the one normalized letter weight is at most 6; no extra exclusion is required by the theorem.

Lines 54-59 prove the exact split P = D + 2*q, where D is the normalized sum and P is the physical sum for the same sigma. The pointwise identity is `(val + 3) = (val + 1) + 2`; distribution of finite sums and the cardinality of Fin q turn the added constant into 2*q. There is no subtraction or truncated-natural arithmetic in this step.

Lines 60-64 use the actual Fin 6 bound `(sigma i).val < 6`, so every physical letter weight is at most 8. `Finset.sum_le_sum` gives P <= sum_i 8 = q*8. The closing two omega calls prove the lower bound from D >= 7, P = D + 2*q, and q >= 1, and the upper bound from P <= q*8 and q <= 6. Thus P >= 9 and P <= 48. The lower endpoint is a valid uniform bound and need not be attained. The upper endpoint is attained for q = 6 and all letters of value 5. Neither target physical-degree bound is a premise.

For interface fidelity only, I read the qualified ES230 frozen declaration, hash 53fe54c47e3969069e1b5d5ee315aea23bd8163d2ece37177651a011d0c0fdd9, and its 24-LF scope, hash e59e57272401a9a7b5e9565ace1972f56258a81990886ebe738d933d487a78c2. With w(j) = j.val + 1 and p the actual ET231 fiber counts, the first theorem rewrites ES230's two weighted multiplicity sums to D and P, since w(j)+2 = j.val+3. The second theorem then supplies the required 9 <= P <= 48 for words of q <= 6 with D >= 7. This validates the announced degree interface. It does not instantiate the entire ES230 analytic estimate, construct its omitted-term index set, or redo its accepted proof/AX evidence.

## Complete coverage of all seven actual-owned declarations

All 35 LF of `u22et-actual-types.txt` were read literally. The seven DECL names match the receipt/audit-record owner-name set exactly, with seven `KIND theorem` entries and zero VALUE entries. There is no omitted private definition value, generated non-theorem constant, or extra owned axiom. The two public types match the frozen statements, including all binders, typeclasses, conjunctions, and the one dependent let described above.

The five additional declarations are omega-generated proof certificates, all under `Shao.OQ3.fin_six_word_physical_degree_bounds`:

| Suffix | Full actual-type coverage and mathematical check |
| --- | --- |
| `_proof_1_1` | `forall q <= 6, forall sigma : Fin q -> Fin 6, not (1 <= q) -> not (q = 0) -> False`. For a natural q, failure of 1 <= q implies q = 0. The unused q <= 6 and sigma binders impose no extra assumption. This covers source line 51. |
| `_proof_1_2` | `forall q sigma (i : Fin q), not ((sigma i).val + 3 = (sigma i).val + 1 + 2) -> False`. This is associativity/evaluation of natural addition, with no range or positivity hypothesis. It covers source line 56. |
| `_proof_1_3` | `forall q sigma (i : Fin q), (sigma i).val < 6 -> not ((sigma i).val + 3 <= 8) -> False`. Natural value < 6 means value <= 5, hence value+3 <= 8. It covers the summand bound in source line 63. |
| `_proof_1_4` | `forall q sigma, 7 <= D -> P = D + 2*q -> P <= q*8 -> not (9 <= P) -> False`, with D and P the exact displayed sums for that sigma. Its actual type omits hqpos and hq, which are not required for this arithmetic consequence: if q = 0, P <= 0 and P = D contradict D >= 7; otherwise q >= 1 gives P >= 9. It covers the final lower-bound call. No missing helper premise is being assumed. |
| `_proof_1_5` | `forall q <= 6, forall sigma, 1 <= q -> P <= q*8 -> not (P <= 48) -> False`. q <= 6 gives q*8 <= 48; the included positivity hypothesis is harmless and unnecessary. It covers the final upper-bound call. |

The above table accounts for every binder and hypothesis of each full actual type, including the certificates whose inference contexts omit unused author hypotheses. All seven actual declarations record exactly `[propext, Classical.choice, Quot.sound]`. Tactic proof-term values were not expanded; their full types, complete authored proof, original object binding, and transitive axiom coverage are the project-required certificate boundary.

## Exact machine evidence and import-only failure provenance

The reviewed successful producer is native004, the first complete RC0 build of module `Shao.OQ3.FiniteWordMonomialEncoding`. Its source hash/2621 bytes/68 LF match the source table exactly. It ended at 2026-10-27T16:35:12.167988+00:00, elapsed 4.120858129113913 seconds, with log hash fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 and 133 log bytes. The retained first original object is hash d7cbe65f990780cda58ee1b0add159cfbce1630a836dd6f70b9cba370db9d7b3, 146824 bytes.

The same-first-original-object audit is RC0, ended at 2026-10-27T16:35:41.712026+00:00, elapsed 4.880414489656687 seconds, audit-log hash 731e95232f2393501bee040823c533ea537552a9a54c16a9c8a7dc863d89a58d, 2273 log bytes. Its actual-type hash is the reviewed 35-LF type file. The audit source identifies both public targets, obtains actual module ownership via `env.getModuleIdxFor?`, and traverses every owned constant. It rejects any newly owned axiom and calls `Lean.collectAxioms` on every owner without namespace-only filtering. Every collected axiom must be in the exact standard-three whitelist. It reports seven actual-owned theorems, both public targets, zero non-theorem values, and PASS. Target counts, actual names, all types, all axioms, source bytes, freeze/scope hashes, and first object agree between the audit record and receipt.

The standalone build history equals the receipt's entire embedded build history. After removing only that duplicate history field, the receipt and audit record agree in all fields. The recorded execution uses CPU36-39,44-47, native -M8192 -j4, current resource phase ROOT_OQ56_OQ3_40 and the existing c12-heavy.lock assignment. The reused admission-helper metadata retains its historical ROOT_OQ56_OQ4_39 label; the execution resourcePhase and CPU fields record the current OQ3 allocation. Project budget/guard/hard limit are 140/180/200 GiB, other/system reserve 60 GiB; audit memory events max/oom/oom_kill are zero and cacheMutation is false. This is receipt review, not an independent current process observation or a claim that another check is running. The pinned environment is Lean v4.36.0-rc1 with mathlib 807d3836b165983210ee2ecf3cd28f239436949c, as recorded in SERVER.md.

All earlier failures remain failures:

| Attempt | Full source SHA-256 / bytes / LF | RC | Retained log hash / bytes | Meaning |
| --- | --- | --- | --- | --- |
| native001 | 120793211b1cf419925d8651356cb7464f276558d8704949f3b540af021fc4b5 / 2491 / 65 | 1 | d98b731d740fff25f0669e74eb9da4f40ed52c203e19a473314ec225a1002409 / 365 | Missing umbrella Mathlib.Tactic object; no successful producer. |
| native002 | 7b1f7f46dfc6d288a088e334aca5613cacfc75a14449bf23623d1ab1768683bb / 2529 / 66 | 1 | 81727e062bcceba22c352338991bfa7e84126767f55143c70db6b11ef023ed0a / 1254 | Narrow imports lacked Complex notation and sum_le_sum; elaboration used error recovery and did not certify these types. No source sorry was added and no successful object is inferred. |
| native003 | 1f0169dae121d06de6626a465308dee0e7c41307c53653db9a11b12734d55425 / 2618 / 68 | 1 | 05c30a2685f8d3fd9309c72fdd2d299c8686583b8ec9c0791600bd80ddc73728 / 389 | Missing Data.Complex.Basic object; no successful producer. |
| native004 | 3de6e3398858f80b78a02b1e38d5da776d454af66c327df772d8f6c5d31a8a3c / 2621 / 68 | 0 | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 / 133 | Complete current source passes using known existing Complex.Norm and the required order big-operator import. |

I independently reconstructed all four complete source versions in memory from their recorded import lists plus the complete final namespace/statement/proof body, including every blank line and final newline. Every reconstructed whole hash and byte length matches its historical record. The shared complete body hash is a9bea644ad0e1d22cfa8278c1a9255d4bef653add2b450126ad10ea5cec0f97b. Thus the import-only comparison is verified for the entire body, not merely for a small proof diff or matching theorem names. There were zero proof/freeze changes and zero cache writes in the supplied provenance. Raw failed/successful logs remain server-only; no concrete binding discrepancy required downloading them or rerunning a command. A direct full-source scan found no sorry, admit, axiom, unsafe, or native_decide token. The accepted current audit excludes sorryAx and every other non-whitelisted transitive axiom for all seven owners.

## Original-source fidelity, limits, and decision

The original report's sections 1-2 describe the fixed-x tilted-law weak-Cramer/Edgeworth route with actual model data, uniform 8+delta moments, covariance control, and strict 0 < beta < 2/5. Its terminal section separates local Fourier work from the external rate-gap treatment. The complete original verdict preserves the accepted counterexample to genuine joint nonlattice sufficiency and describes only one sufficient quantitative repair, with explicit remote localization and external-result attribution. Its final repair attribution is to Song's uniform-in-law theorem, while the earlier report discusses Angst-Poly; this finite ET231 helper does not use either analytic theorem or resolve their downstream formalization.

ET231 supplies exact finite word/count algebra and a derived degree range for a prospective order-six exponential-polynomial assembly. The primary packet's pinned `Fintype.sum_pow` has the actual word index `Fin n -> ι`, so the word shape matches that future expansion. ET231 itself does not use sum_pow or prove the Taylor expansion/filter identity, factorial or multinomial grouping, explicit six-order coefficients, cumulant coherence, a remainder norm estimate, actual characteristic-function comparison, full-frequency/Fourier inversion, exterior/rate-gap control, B-D, or the original OQ3 root. Those obligations remain OPEN. In particular this finite helper has no hidden analytic premise that supplies a desired root estimate.

No actual E or rho is replaced, no alternative law is introduced, no beta endpoint is extended, and no p54 repair, accepted counterexample evidence, or external attribution is altered. The theorem is an elementary auxiliary application of pinned finite-fiber identities, not a new analytic theorem or a certified priority claim. Its correctness has no implication that the broader source problem has closed.

ISSUES: None requiring a source, statement, or evidence change for the exact ET231 helper. Scope limits above are acceptance boundaries, not defects in the two frozen declarations.

DECISION: CORRECT for the exact two public statements, one statement let, complete 68-LF proof, all seven actual-owned types, zero VALUE obligations, and the bound first-native/same-first-object transitive-axiom evidence. This is a qualified independent final review suitable for exact-source reuse at parent intake. It does not change publication/acceptance records or authorize a build replay.

Usage: model gpt-6.1-sol; reasoning effort xhigh; input_tokens = null; cached_input_tokens = null; output_tokens = null; reasoning_subset_tokens = null. Token counters were not exposed to this reviewer. No subscription allocation or purchased-credit estimate is inferred.

Final context and report-writer state: COMPLETED_STOPPED. All proof/source/server/execution/publication authority stayed with the authorized parent; the review-only writer is released after this report. No pending delegated child or external operation exists in this review context.
