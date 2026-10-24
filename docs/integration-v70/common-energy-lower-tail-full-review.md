# Independent complete review: QuadraticEnergyLowerTail

STATUS: **CORRECT**

The two frozen public declarations and all five private theorem proofs are correct for the exact source `e0cffb4e4d3cea7213c3b92a8c3d8f0d5406014ea2bc76613ac3d4711d68d9fc`, source-only commit `bcf09531ed60e12dfa9e144cc755f4a172b95b3c`. I found no critical mathematical, statement-fidelity, actual-owner, or evidence-coverage gap. This is a complete independent review of this module, not root acceptance or a claim that C2 is closed.

Reviewer: `/root/common_energy_lower_tail_full_review`, fresh `gpt-6.1-sol` / `xhigh`, distinct from `/root/common_energy_lower_tail_actual_author`. Root's persisted activation verifies the author's explicit source/producer release. I did not author, edit, or repair the production proof, declarations, audit code, old modules, or accepted evidence. Only reviewer outputs were written. Token counters are unavailable; no usage percentage is inferred.

## Exact artifact and review coverage

- Module: `Shao.Probability.QuadraticEnergyLowerTail`; branch `feat/common-energy-lower-tail`; worktree `/root/rivermind-data/shao-lean-20261021/workspaces/common-energy-lower-tail-v69`.
- Commit `bcf09531ed60e12dfa9e144cc755f4a172b95b3c`, tree `cd33eeca7d7bbcf20842ebc292d2f11a967ca8b6`, clean Git status, sole changed source `Shao/Probability/QuadraticEnergyLowerTail.lean`.
- Parent is accepted v69 head `896e101115eb9106866e1c76226aafe42e27a95b`, tree `a2bbef75ac7865a2797930a3a5e311d2e4326a5d`, matching the archived exact-tree v69 merge record. The GitHub merge commit need not be present in this worktree's local object database.
- The 10,108-byte UTF-8/LF/no-BOM local reviewed source equals the server current source, Git committed blob, and original successful `attempt003.lean` bytes.
- Original successful and current production object SHA256: `6a42ffb03b5e1a755fff036877956bff3b11b6162d1ad4df687143879bed9912`.
- Entire mathematical candidate, complete new source including every proof/head/local literal, original `main.tex` 1254–1269 and normalization context 1212–1254, actual `Path`/`energy` definitions, and relevant measurability interfaces were read. The product-integration API in the pinned Mathlib source was inspected.
- Every one of the seven actual-owner complete elaborated types was separately extracted from the original audit log and read without elision. Every named type and theorem-value byte interval, its SHA256, and its surrounding declaration-name/type/proof markers were checked against the unchanged log. Actual non-theorem/definition values, including private/generated: **zero**.
- Two complete public heads equal the root freeze; all five private heads equal their preimplementation freeze. The public declaration file SHA256 is `3db651638124c7ba78f4fc99e210aebd2bb61873c1e44f9e8d6973b3c5b73a49`; private freeze SHA256 is `523f7155373d48f768826b1c75ac688cb6ed97275b07d84cd06283caa8c54f87`.

The detailed source ranges, proof-body/head hashes, actual-type hashes, theorem-value ranges/hashes, individual axiom sets, local literals, dependency bindings, and failure records are in `coordination/common-energy-lower-tail-full-review-coverage.json`. The read-only remote and local bindings are in `drafts/c12-energy-lower-tail-review/server-readonly-binding.json` and `local-readonly-binding.json`.

## Source-to-statement fidelity

Let `nu` be a probability measure on the usual Borel real line, `n>0`, with actual integrability of `z^2` and `|z|^3`, and `n * integral(z^2,nu)=1`. The frozen literal values are

`beta = n * integral(|z|^3,nu)` and `P = Measure.pi (fun _ : Fin n => nu)`.

The accepted old definition is exactly `Path n = Fin n → ℝ` and `energy v = sum_i (v i)^2`. It is the full observed square sum, not a deterministic variance, truncated statistic, centered surrogate, or a separately supplied target quantity. The actual elaborated public types use the standard real arithmetic/Borel/product-measure instances and these exact literal values. There is no hidden argument supplying a Laplace estimate or desired probability bound.

The first public theorem asserts actual integrability of `exp(-s*energy)` and its integral bound `exp(-s + (sqrt s)^3*beta)` for all `s>=0`. The second asserts **derived** `beta>0` and

`P.real {v | energy v <= 1-kappa} <= exp(-(kappa^3/(8*beta^2)))`

for `0<kappa<=1`. It retains the weak inequality throughout. The `kappa=1` event includes every zero-energy atom. No atomlessness or strict/weak interchange is used.

In the original source, normalized observations are `A=X/sqrt(n)`, so the original `Q/n` equals this module's full normalized energy and `n E|A|^3` equals the source's `delta`. The module proves the first exponential bound at original line 1261. It does not prove the following `<= C*u*Psi(x)` absorption, the preceding signed-walk comparison, or their complete assembly. The stronger original bounded/centered setting can use this lemma, but centering, bounded support, symmetry, density, and an original-law positive exponential moment are not needed or silently added here.

## Complete proof review

1. **`exp_neg_sq_le_cubic`, source lines 22–35 — CORRECT.** For `u>=0`, `1+u^2` is strictly positive and at most `exp(u^2)`. Reciprocation therefore bounds `exp(-u^2)` above by `1/(1+u^2)`. Multiplying the remaining inequality by the positive denominator reduces exactly to `u^3*(u^2-u+1)>=0`. The second factor is `(u-1/2)^2+3/4`, so the polynomial reasoning is valid globally. There is no restriction to small `u`, no missing range split, and no fourth-moment assumption. `u=0` is included.

2. **`coordinate_energy_laplace_integrable`, lines 36–43 — CORRECT.** The coordinate function is measurable by continuity, positive, and at most one because `-s*z^2<=0`. Under a probability law the constant one is integrable. `Integrable.mono'` thus proves actual Bochner integrability. This works at `s=0` and for unbounded observations without an original positive exponential moment.

3. **`energy_laplace_integrable`, lines 44–54 — CORRECT.** The accepted full finite energy is continuous and nonnegative. The exponential composition is therefore measurable and bounded in norm by one. The finite product probability measure supplies integrability of the dominating constant. No replacement of random energy by expected energy occurs.

4. **`coordinate_energy_laplace_bound`, lines 55–90 — CORRECT.** The substitution `u=sqrt(s)*|z|` is nonnegative; its square is `s*z^2`, and its cube is `(sqrt s)^3*|z|^3`. The global scalar inequality consequently gives the pointwise polynomial majorant. The proof explicitly constructs its integrability from the two frozen actual moment assumptions. Integral monotonicity is applied between two integrable functions. Integral linearity, constant multiplication, and probability mass one give `1-s E z^2+(sqrt s)^3 E|z|^3`. The final bound is `1+t<=exp(t)` for the exact correction `t`. No default value of a nonintegrable integral is used.

5. **`normalized_third_moment_pos`, lines 91–117 — CORRECT.** The third absolute moment is nonnegative. If its integral were zero, the nonnegative-integrable integral-zero criterion gives `|z|^3=0` almost everywhere; the nonzero natural exponent gives `|z|=0`, hence `z=0` and `z^2=0` almost everywhere. Integral congruence makes the second integral zero, contradicting normalization. Finally `n>0` gives the strictly positive product. The theorem's `h2` is unused in this proof, harmlessly retaining the frozen interface; no positivity premise is inserted.

6. **`finite_iid_energy_laplace_bound`, lines 118–163 — CORRECT.** Integrability is first supplied for the true full-energy exponential. The pointwise identity `exp(-s*sum_i v_i^2)=prod_i exp(-s*(v i)^2)` is exact. `integral_fintype_prod_eq_prod` is the scalar finite-product Fubini theorem over the actual `Measure.pi`; its sigma-finite hypotheses are supplied by the coordinate probability laws. The coordinate integral is nonnegative, so the real product comparison uses the correct nonnegative-product theorem. Recombining the constant exponential product and using `n E z^2=1` yields exactly the frozen exponent. No independence hypothesis is missing: independence and identical distribution are encoded by the literal product measure. `s=0` gives mass one. `hn` is unused here but retained exactly as frozen.

7. **`finite_iid_energy_lower_tail`, lines 164–222 — CORRECT.** Positive `beta` is obtained from item 5. The body uses the exact public `beta`/`P` and then `a=kappa/(2*beta)>0`; hence `sqrt(a^2)=a`. The first public theorem is applied at the nonnegative parameter `a^2`. The actual event is measurable because the accepted energy is measurable. On that weak event, `exp(-a^2*(1-kappa))<=exp(-a^2*energy)`; off it the constant indicator is zero and the latter exponential is positive. Integral monotonicity uses explicitly integrable indicator and Laplace functions. The constant indicator integral is precisely the event's real probability times its exponential constant. Division is by a strictly positive exponential. The final exponent is `-kappa*a^2+beta*a^3=-kappa^3/(8*beta^2)`, valid since `beta>0`. This includes all equality and zero-energy atoms. `hkappa1` is unused because the same bound also follows for larger positive `kappa`; retaining the declared source range does not weaken the promised proof.

All seven literal `let` occurrences were checked: the two public `beta`/`P` pairs, the lower-tail body's same `beta`/`P` pair, and its `a`. There is no `letI`, new instance declaration, or hidden alternate measure/arithmetic value. All other local proof expressions, including pointwise substitutions, integrability witnesses, indicator constants, and normalization substitutions, are covered by the complete source reading. No `sorry`, `admit`, new axiom, `unsafe`, or `native_decide` appears.

## Kernel, actual ownership, and transitive axioms

The first whole exact-source success is the original `attempt003`, native return code **0**. Its unchanged original log SHA256 is `385feba19e2c050ba9fff00c5d948ca93ba52f86a5cfa0b6fd069da7072c8717`; source/current object bytes agree with the original successful snapshot. Same-call production and source/object capture are recorded in the author's receipt and verified release chain; I reused that original evidence and did not run another compiler.

The sole original owned audit has native return code **0**. Its code was completely read: it enumerates `env.constants`, resolves each actual module owner with `env.getModuleIdxFor?`, selects equality to this target module, rejects **every** non-theorem kind, and calls transitive `Lean.collectAxioms` for each selected constant. It uses no namespace filter. It prints full actual types and theorem values with `pp.all`, `pp.deepTerms`, and `pp.proofs`. The unchanged log is 25,018,954 bytes, SHA256 `6d95ff34172a1f9094a86ed3ad8e1bce2e0b5c760179da7b21024b6e6b70d81d`. Its named records are exactly two public and five private theorem constants, zero definitions including private/generated, with no omitted extra declaration marker.

For **each** of the seven individually named constants, the transitive axiom set is exactly `{propext, Classical.choice, Quot.sound}`. Each complete actual type matches the reviewed frozen source head. The source proofs were fully read; the much larger tactic-generated theorem proof certificates were mechanically bound by their exact original log byte ranges and hashes rather than read as 25 MB of model input. This is the explicit review boundary in root's activation, not an omitted actual-definition review: there are no actual non-theorem values. The per-name record does not claim a full model reading of those machine proof terms.

Pinned environment is Lean `leanprover/lean4:v4.36.0-rc1`, Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. The producer's CPU10–13, root lock, `-M8192/-j4`, and disabled `autoImplicit`/asynchronous elaboration are existing author execution provenance; this review made no Lean, build, cache, or audit invocation. The ordinary Mathlib dirty-worktree warning is preserved. Its canonical package path equals accepted v69's shared package path; no new package patch is part of this module or was introduced during review.

## Accepted dependency reuse and failure preservation

The actual transitive old Shao import closure was independently derived from the reviewed imports and contains exactly seven modules: `TruncationIntegrals`, `TruncationBudget`, `MeasurablePath`, `Normalization`, `Events`, `FinitePath`, and `TwoSided`. Each source equals its parent-commit blob, accepted v69 worktree, archived accepted v69 source map, and local curated copy. All **35** recorded old object/artifact and private-alias entries agree byte-for-byte with accepted v69. Source and object hashes are preserved in the binding/coverage records. No old theorem/proof/axiom check was replayed and no accepted old source was changed.

- `attempt001`: original source SHA256 `60312649a69486085b873cb6e2ab5c719c9e6311959790c65019d446ca17a62d`, native **1**, no object. Its original log and all source differences to the fully read final source were inspected. Failures concerned integral rewrite elaboration/syntax, a nonexistent power-zero API, the nonnegative real-product API, and polynomial normalization.
- `attempt002`: original source SHA256 `d270fb6a7a1490ab813b671583a9eab48b29eaaa07ef370b89c2f9cf8d374a6b`, native **1**, no object. Its full original log and sole source difference to the final version were inspected: the nonexistent `measureReal_univ_eq_one` was replaced by the existing `probReal_univ`.
- `attempt003`: source SHA256 equals the reviewed frozen final source, native **0**, original object retained. Its complete original log contains warnings only. The unused-variable/tactic warnings require no mathematical repair and were not cleaned up by changing accepted bytes.

The original failed sources, original logs, native return-code files, final successful object, and original audit remain untouched on the server. Per-attempt hashes are recorded in coverage. A reviewer read-only metadata extraction initially failed when trying to resolve the GitHub merge SHA absent from the local repository; it was corrected to use the archived accepted v69 tree. This was not a proof failure, audit failure, or successful-producer replay.

## Verdict, limits, and release

The complete frozen module is **CORRECT**, with full source-to-statement/proof review and reused exact-source original server kernel/all-owned-transitive-axiom evidence. It is the classical Chernoff energy-fee auxiliary estimate already attributed to the original source, not a novel theorem claim. Existing p54 repairs and external-result attribution are unaffected.

The normal-tail absorption, full C2 double-hit comparison, and all still-open original C1/C2/OQ3/OQ4/OQ56 root groups remain **OPEN**. No PR, push, merge, shared import, cache change, or root acceptance was performed. Root alone decides acceptance and the next integration/consumer step.

Review write authority and any execution rights are released after the final records are persisted; there is no in-flight tool command or production operation. Runtime state is `RELEASED_IDLE_COMPLETE_INDEPENDENT_REVIEW`. The next dependency belongs to root: read this complete report once, bind the exact reviewed bytes and preserved evidence, then perform only the required integration/consumer work. This final review does not itself provide a persistent execution mechanism.
