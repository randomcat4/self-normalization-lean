# C12 units 169-170: independent complete final review

STATUS: CORRECT

This is a fresh independent complete source-to-statement and proof review of `Shao.C2.AuxiliaryMarkedRareBase` (169) and `Shao.C2.AuxiliaryUnmarkedBlockCauchy` (170). The reviewer did not author or change the production source, declarations, assumptions, dependencies, server artifacts, prior reviews, or publication records. Report ownership is restricted to this review folder. Parent qualification remains required; this report does not itself publish, merge, or close C2/C12. The detailed unit 169 review comes first; the complete unit 170 review and combined disposition follow it. Unit 170 is explicitly conditional and contains no cubic mark.

## Exact version and scope

| Artifact | SHA256 |
| --- | --- |
| Production source, 7,889 bytes | `9e6e9c2a97d2c3762885708f173ebda026f4eb5fdfe581687d5c27a94dd08ee1` |
| Kernel object | `58261c5212e0ef128058be3b7d28bcc5d8ae96d756a9cacecafc0da0df737846` |
| Author receipt | `731370f0a59f5755d018db03f80a35b5902d674c68a55d73e4d5cdf9067b11c1` |
| Frozen imports/context/complete head | `a3cc5891888700acad368ce111e729d1d47f1d00dc4e7210b56346b58e67c748` |
| Complete actual-owned type export, 41,169 bytes | `9e16cae3c8fe5ef7af765541a5e201285a739fcc792fb6fec0006b716aaaf200` |
| Complete non-theorem value export, 0 bytes | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

The complete production file, complete frozen file, source-and-proof note, freeze record/comparison, author release, receipt, audit program, actual owner map, and both complete exports were read. The complete actual type export was read contiguously in two parts, lines 1-239 and 240 through the end. Every owned declaration is covered below. Read-only observations independently reproduce the frozen-head comparison and show the type/value exports are exact complete blocks from the successful owned-audit output, without ellipses or metavariables.

The exact claim is a specialized marked rare Laplace base at exponent a=0. It controls the raw iid product integral of the actual first-coordinate cubic mark and actual-energy exponential on the full weak terminal event. It has one linear auxiliary third-moment factor and the stronger full Gaussian tail factor. It does not assert the general-a marked or unmarked moments, inverse moments, weighted records, a circular witness, or a C2/C12 root theorem.

## Original mathematical source and translation

The read-only paper bindings are:

* `main.tex`: `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`.
* `supplement.tex`: `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

The actual passages read include main 158-184, 1188-1224 and 1270-1297; supplement 4978-4999, 5038-5085, 5085-5171 and 5768-5787. Supplement 4771-4854 and 5260-5305 were also observed for adjacent notation/context, without extending this leaf's scope. Main 162-166 specifies weak multiplication crossings including the all-zero sample; main 169-171 identifies Psi as the standard normal upper tail. Main 1211-1216 states that the centered variance-one law and its third moment are the auxiliary law used throughout these estimates. No finite-third assumption is inserted on a distinct original law.

Supplement 4984 defines H=K beta^2(1+x)^6 and m=ceil H. Lines 5094-5139 give the common tilt estimate at t>=m, l=t or t-1, and st<=Lx^2, with v_x=sqrt(9x^2/4-1). Lines 5141-5147 delete the marked coordinate and give the positive-energy deterministic implication. Lines 5149-5154 give the marked factorization; lines 5162-5166 retain precisely one linear cubic mark. Lines 5768-5787 fix numerical constants before choosing the auxiliary law. The formal result instantiates the marked base with full length t=n+1 and remaining length l=n. Its cutoff is literally ceil(K beta^2(1+x)^6)<=n+1, not a relaxed or renamed remaining-length cutoff; its time condition is s(n+1)<=Lx^2.

The auxiliary-law hypotheses are explicit: a probability measure nu on the real Borel line, integrability of z^2 and |z|^3, mean zero, and second moment one. The theorem holds for this broader finite-third auxiliary class; it therefore covers the paper's bounded auxiliary laws without adding a hidden boundedness or density premise. x>=1, s>=0, the two displayed K lower bounds, rhoStar in (0,1/16], and L>=0 are all exposed. The large explicit K bounds are the already-qualified sufficient choices from producer 168. The universal C is chosen before rhoStar, L, K, nu, s, x, n. K is quantified before the auxiliary law and sample parameters. No target-tail or integrability oracle is assumed.

The full event contains no positivity restriction on energy. At all-zero energy the weak endpoint event can be true. The mark is then zero, which is why retaining the event is legitimate. The formal result specializes the marked component of the source argument at a=0 and obtains a full Psi factor rather than relying on the later combined square-root-tail estimate. No normalization by sample energy, random stopping rank, or conditional permutation law is substituted for the actual deterministic iid product.

## Complete frozen declaration

The imports are exactly `Shao.C2.AuxiliaryRareLaplace`, `Shao.C2.AuxiliaryMarkedDeletion`, `Shao.OQ4.KilledPathLaw`, and `Mathlib.MeasureTheory.Integral.Prod`. The context is `autoImplicit false`, `maxHeartbeats 3000000`, a noncomputable section, namespace `Shao.C2.AuxiliaryMarkedRareBase`, and the `MeasureTheory`, `ProbabilityTheory`, and `BigOperators` openings. There is one source theorem, no private source theorem, no new definition or instance. The complete public head is:

```lean
theorem auxiliary_original_cutoff_marked_rare_base :
    ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ L : ℝ, 0 ≤ L →
          ∀ K : ℝ, 8000000 * (1 + L) ^ 2 ≤ K →
            2 * (768 / rhoStar) ^ 2 ≤ K →
            ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu],
              Integrable (fun z : ℝ => z ^ 2) nu →
              Integrable (fun z : ℝ => |z| ^ 3) nu →
              (∫ z : ℝ, z ∂nu) = 0 →
              (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
              ∀ s : ℝ, 0 ≤ s →
                ∀ x : ℝ, 1 ≤ x →
                  ∀ n : ℕ,
                    Nat.ceil (K * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 * (1 + x) ^ 6) ≤ n + 1 →
                    s * ((n + 1 : ℕ) : ℝ) ≤ L * x ^ 2 →
                    let P : Measure (Shao.Path (n + 1)) :=
                      Measure.pi (fun _ : Fin (n + 1) => nu)
                    let B : Set (Shao.Path (n + 1)) := {v |
                      ((3 / 2) * x) * Real.sqrt (Shao.energy v) ≤
                        |Shao.prefixSum v (n + 1)|}
                    let F : Shao.Path (n + 1) → ℝ := fun v =>
                      |v 0| ^ 3 * Real.exp (-s * Shao.energy v)
                    Integrable (B.indicator F) P ∧
                      (∫ v : Shao.Path (n + 1), B.indicator F v ∂P) ≤
                        C * (∫ z : ℝ, |z| ^ 3 ∂nu) *
                          Real.exp (-(7 / 8) * s * (n : ℝ)) *
                            Shao.standardNormalTail ((3 / 2) * x) := by
```

The fully elaborated public type was checked against this entire head: every quantifier, probability instance, moment hypothesis, mean/normalization equality, real/natural cast, ceiling, inequality direction, three lets, coordinate-0 mark, actual product measure, and conclusion agrees. There is no additional hidden premise in the actual type. In particular, the head uses the full weak event rather than {energy>0} intersected with it.

## Full proof review, source lines 41-148

1. **Universal constant and the remaining rare factor, lines 41-58.** The proof obtains C, its positivity, and the entire producer 168 theorem before introducing all target parameters. With beta=int |z|^3, it defines the genuine remaining product Ptail=pi nu on `Path n`, threshold a=sqrt((9/4)x^2-1), A={energy>0 and a sqrt(energy)<=|prefixSum|}, and g=A.indicator(exp(-s energy)). It applies 168 with t=n+1, remaining rank n, exactly the target cutoff and time hypotheses, and the second rank alternative n=(n+1)-1. Thus g is integrable and its integral is at most C exp(-(7/8)sn) Psi(3x/2). No cutoff factor, K, C, or source order changes.

2. **Scalar marked coordinate, lines 59-74.** For f(z)=|z|^3 exp(-s z^2), f is nonnegative. Since s>=0 and z^2>=0, exp(-s z^2)<=1, so f<=|z|^3 pointwise. Its continuity gives the required strong measurability; `Integrable.mono'` with the real norm equal to f yields integrability from the stated third-moment hypothesis. `integral_mono` then gives int f<=beta. The proof separately establishes beta>=0 and g>=0, including the indicator's zero branch. This uses neither a sixth moment nor a bound on an undamped higher mark.

3. **Actual product splitting and exact Fubini, lines 75-84.** The chosen e is the native measurable equivalence `piFinSuccAbove` at coordinate 0, from `Path(n+1)` to R x `Path n`. Native `measurePreserving_piFinSuccAbove` maps the actual pi measure P to nu.prod Ptail. `hf.mul_prod hLap.1` makes (z,w) |-> f(z)g(w) integrable on that product, and measure-preserving composition makes Q(v)=f((ev).1)g((ev).2) integrable on P. The measurable-equivalence version of integral composition and `integral_prod_mul` give the exact identity int Q=(int f)(int g). The argument establishes both factors' integrability before using this equality, so it does not exploit an undefined Bochner integral's default value.

4. **Genuine path reconstruction, lines 85-118.** Unfolding the actual finite sum of squared coordinates gives energy(cons z w)=z^2+energy(w). The accepted OQ4 public `prefixSum_cons` at k=n gives prefixSum(cons z w)(n+1)=z+prefixSum(w)n, including n=0. Native `piFinSuccAbove_symm_apply` reduces e.symm to `Fin.insertNthEquiv`; `Fin.insertNth_zero` and constant-family casts make it exactly `Fin.cons`. This is the genuine coordinate decomposition, not an assumed equality in distribution.

5. **Every pointwise case, lines 88-114.** If cons z w is outside B, the target indicator is zero and Q is nonnegative. Inside B, if full energy is zero, the accepted `energy_eq_zero_iff` forces z=0; both the target cubic weight and the scalar marked factor vanish. This case is handled explicitly even when nu has an atom at zero and B is true there. Otherwise nonnegativity of actual energy and its nonzero value give strict full-energy positivity. Rewriting genuine energy and prefix sum turns B into exactly the two hypotheses of qualified deletion theorem 164. It gives w in A, with positive remaining energy and the weak remaining endpoint. The two indicators can now be unfolded. `exp(-s(z^2+Ew))=exp(-s z^2)exp(-s Ew)` proves equality of the remaining weights, hence the claimed domination. No weak boundary, equality sample, or zero-energy atom is discarded.

6. **Transport, measurability, and target integrability, lines 119-138.** e.symm(e(v))=v and the reconstructed `Fin.cons` identity extend the domination to every full path v. B is measurable as an inequality between the measurable actual square-root energy and the continuous absolute actual prefix sum. F is continuous by continuity of coordinate evaluation, absolute value, powers, actual energy, and the exponential. The target indicator is nonnegative in both membership branches. Its real norm is therefore itself; measurable indicator plus pointwise domination by integrable Q satisfies `Integrable.mono'`. This proves the actual integrability required by the public head.

7. **Final integral inequality, lines 139-148.** `integral_mono` bounds the integrable target by integrable Q, and exact Fubini substitutes (int f)(int g). The final `mul_le_mul` uses int f<=beta and the bound on int g, with exactly the necessary side conditions 0<=int g and 0<=beta. Reassociation yields C beta exp(-(7/8)sn) Psi(3x/2). There is precisely one cubic moment factor and no Cauchy inequality applied to the whole marked product. The proof covers s=0, weak endpoint equality, arbitrary atoms, and all natural n allowed by the frozen cutoff. It does not silently assert existence of a valid small n when the cutoff precludes it.

## Complete actual-owner coverage, including generated theorems

The map is derived from all actual target-module-owned constants and checked bijectively against all `TARGET_DECL` blocks. It gives **3 constants, all 3 theorems: 1 public source theorem, 0 private source theorems, 2 generated theorems, 0 global non-theorem values**. More precisely, the two generated declarations comprise one arithmetic proof theorem and one simplification theorem; the author's collective description as two generated simp obligations does not alter the actual names or counts.

| Actual owner name suffix | Complete type/proof analysis | Transitive axioms |
| --- | --- | --- |
| `auxiliary_original_cutoff_marked_rare_base` | Entire elaborated 463-line public type read; it agrees with the complete frozen head above. Full production proof and all new interactions reviewed in the seven steps above. | propext, Classical.choice, Quot.sound |
| `auxiliary_original_cutoff_marked_rare_base._proof_1_1` | Complete actual type is `forall (K : R) (nu : Measure R) (x : R) (n : Nat), Not (n = (n+1)-1) -> False`. The first three parameters are unused. For every natural n, successor subtraction gives (n+1)-1=n; reflexivity then contradicts the negated equality. This is the generated arithmetic obligation at source line 55, discharged by `omega`; it contains no rank or cutoff assumption and establishes precisely the rank specialization needed for 168. | propext, Classical.choice, Quot.sound |
| `auxiliary_original_cutoff_marked_rare_base._simp_1_2` | Complete actual type is `forall {alpha : Type u} [Preorder alpha] (a : alpha), (a <= a) = True`. Reflexivity gives a<=a; both propositions are true, so proposition extensionality yields the displayed equality. This generated simplification supports the zero-branch reflexive inequalities. It introduces no event restriction, positivity hypothesis, density, or mathematical assertion about nu. | propext |

The short descriptions above are complete readable reductions of the actual generated types; the exact fully elaborated forms were read in the 41,169-byte export. Their proof obligations are elementary and explicitly checked here in addition to the source-bound kernel and recursive-axiom receipt. There are no other actual private, generated, non-theorem, opaque, or instance owners omitted from coverage. The complete empty definition-value export agrees with the actual map, rather than being inferred from the absence of source `def` text alone.

## Consumed interfaces and their new interactions

Qualified producer proofs are reused. Their complete public heads/context and the relevant definition contracts were read for this new use; their old complete proofs and accepted checks were not re-reviewed or replayed.

* **164, deterministic marked deletion.** Source `d41692110c947b26f92f6bd2f9511a0c1f25a20e0a470d59dcd19b770cc196e5`, object `e5b27b3e0a19791a148e8db4f210c9f2b7ba7df343e692fe65ff9f046ed3bd01`. The complete head takes an actual w:Path n, v,x:R, x>=1, 0<v^2+energy(w), and (3/2)x sqrt(v^2+energy(w))<=|v+prefixSum(w)n|. It concludes positive remaining energy and sqrt((9/4)x^2-1)sqrt(energy(w))<=|prefixSum(w)n|. The exact full-energy and endpoint premises are paid only in the positive-energy membership branch, as required. Its sealed review JSON is `6bf95cca027918fdf4bcc0c497ffceb4d23f1c53985f3d1f48df7e5f3b6adcc4`; parent qualification is `f2aa5279ec91684de2bc70f8ca61be2f2b73b3a45873fcb090f629bd7de4f447`.
* **168, original-cutoff rare Laplace.** Source `06b4ca90fe289342c88c7b4bd218ca6b28fac676a7fe0c2f2bc46da19630d9e1`, object `7dccd0f0cb2f2b025b18147930d8631730a39c0196691818f86c571b31dc0621`. Its complete head, including both rank alternatives, all moment and source parameters, actual A/W/Praw lets, integrability and bound, was read. C, rhoStar, L, K, nu, s, x remain identically ordered and instantiated; t=n+1 and n=t-1 are the only rank substitution. Its sealed combined 167/168 review JSON is `21436600b23811b271ce5481148f71fd4940c7f55746461a8fad6e991462f7fd`; parent qualification is `9747ff970b09cc6190a8a0c9119b2b11cfca12c599ee0ce95704ae5ab51d1774`. Its previously qualified native tilt/product mechanism remains upstream; no new abstract-law oracle replaces it.
* **Accepted OQ4 and common interfaces.** `prefixSum_cons (n)(y)(a)(k)` states exactly `prefixSum (Fin.cons y a) (k+1)=y+prefixSum a k`; the new call uses k=n. Its accepted `KilledPathLaw` source hash is `1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f`, object hash `73cff303358b3121caf2c0d9c9976dbd323f75853bdf125bd3e7e067db789f43`. Existing 167 evidence binds it in the accepted 24-module common closure and root v85 receipt `bee6010790734dfc41f2819b76948946a7dec1ac6bd08a5139c8accf1e493fdd`. Fresh read-only hashes confirm that closure's actual source/object bindings. `Path n` is Fin n -> R, `energy` is the sum of true coordinate squares, and `prefixSum` is the actual saturated prefix sum, not variance or a centered substitute. Full relevant public statements for energy nonnegativity, energy-zero iff all coordinates zero, energy and prefix-sum continuity, and square-root-energy measurability were read. `standardNormalTail x` is `(gaussianReal 0 1 (Ioi x)).toReal`, the source Psi. The Gaussian atomless tail convention does not change the weak auxiliary event.

Native contracts were read with their surrounding section variables and relevant typeclass instances from the actual shared-v34 package view. All nine inspected native source files also match their blobs at the pinned mathlib commit `807d3836b165983210ee2ecf3cd28f239436949c`.

| Native contract | Premises and exact application |
| --- | --- |
| `MeasurableEquiv.piFinSuccAbove` | For measurable coordinate types, separates coordinate i and the `succAbove i` remainder; its inverse is the actual `Fin.insertNthEquiv`. At i=0 and constant real family the inverse is `Fin.cons`, including the dependent casts verified by `insertNth_zero`. |
| `measurePreserving_piFinSuccAbove` | Requires every coordinate measure sigma-finite and sends pi(mu) to mu(i).prod pi(mu(i.succAbove -)). Here all measures are nu; probability implies finite, sigma-finite and S-finite. The remaining product is literally Ptail. |
| `MeasurePreserving.integrable_comp_of_integrable` | Takes the measure-preserving map and integrability on its target measure. Both are supplied; no embedding premise is needed for this direction. |
| `MeasurePreserving.integral_comp'` | Requires a measure-preserving measurable equivalence; it supplies the needed measurable embedding itself. The new e has exactly this type and its target measure is nu.prod Ptail. |
| `Integrable.mul_prod` | Requires a normed ring and the two integrable scalar factors; real scalars qualify. Its local S-finiteness assumption is explicitly omitted in the native contract. |
| `integral_prod_mul` | Requires real-like scalars and the scoped S-finiteness of both measures. nu and Ptail satisfy these: `pi.instIsProbabilityMeasure` works for every finite index including Fin 0; probability -> finite -> sigma-finite -> S-finite. Both factors have already been proved integrable. |
| `Integrable.mono'`, `integral_mono` | The first requires measurable target and an almost-everywhere norm bound by an integrable real dominator; target nonnegativity makes its norm itself. The latter requires both integrals integrable and a pointwise inequality. Every premise is supplied in the scalar and final-target uses. |

No undefined measurable inverse, unproved independence, absent sigma-finiteness, or unpaid Fubini/integrability premise remains. Standard real topology/normed-space/complete-space instances pay the remaining native scalar contracts.

## Kernel and all-owned recursive axiom evidence

The author is writer/execution released at the exact source above, with no inflight work. Attempt 002 has original server kernel exit 0 and audit exit 0. Its preserved command uses the designated C12 server worktree, `c12-heavy.lock`, CPU14-17, Lean `-M8192 -j4`, pinned Lean `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, and the shared-v34 read-only package view. Worktree branch is `author/c12-rare-laplace-continuation-v71`; observed HEAD is `ddd9c7f5ad88f3a92f9bfe533b231c8782d15d90`, tree `34ec1668815aecd315869af0fd3a8dce1efc41fd`. The output object and actual imported worktree object both match the exact source-bound receipt.

The complete OwnedAudit program enumerates `env.constants.toList`; it selects an entry iff `getModuleIdxFor? name`, resolved through `env.header.moduleNames`, equals the target module. The public-name list only checks the expected public theorem count and is not the owner selector. Thus generated/private owners cannot be omitted by namespace or public-only filtering. The actual map has exactly the three owners tabulated above.

For every selected constant the program invokes `Lean.collectAxioms` and rejects any axiom outside propext, Classical.choice, Quot.sound. The actual pinned collector source was read completely: it visits types and proof/definition/opaque values recursively, uses imported precomputed transitive entries with local body fallback, and computes exported dependency entries against the private checked environment. The environment's actual `getModuleIdxFor?` contract was also read. The complete collector hash is `b39bd22253a76816ee6d24284e69674d0b491be343fd71f9ee9376833d1485f6`; environment source hash is `e7b97a029388b84c3f69c58e8df9e30064415e34a863781e1843e8c6c15e0e8f`. All actual owner axiom lists are within the whitelist, including both generated declarations. No `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide` occurs in the production source. Source bytes are UTF-8 without BOM and LF-only, and stripping only the completed proof reproduces the exact frozen file.

Attempt 001's zero-energy indicator, measurable-equivalence coercion and energy-continuity elaboration failures remain preserved with their original command/source/log hashes. Only attempt 002 is accepted. The unchanged frozen head and proof-only fixes are not represented as a changed mathematical result. Reviewer Lean/audit executions, successful-gate replays, server writes, and cache writes are all zero.

## Evidence provenance and bounded observation corrections

The initial 66-entry read-only binding observation found one inherited path absent: the C12 worktree does not contain the shared `Shao/Probability/SourceOriginalFullRelative.lean` source. This is the already-qualified path correction in the 167/168 review, not a new source change. Both canonical copies in `common-original-full-relative-v85` and `integration-bearing-v85` match source hash `9fb2a134affb98aafead8012d9975e6b2de273fff7c2796867fb54b4b6af3b14`; the actual C12 imported object matches `120612e9a6ce6ba95ce5b36d809ba3c1d5e676312c2460840a04e9f395b18b52`. The corrected 112-entry observation is entirely exact, including new source/object/snapshot/receipt/freeze/audit/types/values, qualified 164/168 interfaces, and reused actual common sources/objects. No missing source was copied, no object rebuilt, and no accepted gate rerun. The original failed observation remains preserved.

Two initial native-location queries failed read-only: one shell quote error and then absence of `rg` on the server. Python file inspection supplied the required source locations without executing a proof or audit. Those observations are retained. They have no effect on the mathematical result. Final fresh bindings and current local-evidence seal validation are recorded alongside this report.

The two earlier parent qualifications and all named sealed payload hashes were checked deterministically; their accepted full proof reviews are reused, not repeated. Unit 169 is not claimed to be covered by an old PR. In particular, PR347's previously published 161/163/165/166/167/168 scope is not enlarged by this review.

## Review disposition and release requirements

There is no critical mathematical, source-fidelity, actual-type, interface, kernel-binding, or recursive-axiom gap in this exact version. CORRECT applies only to this leaf and the exact frozen/source/object bindings above. No claim of new mathematical novelty or complete C2/C12 closure is made.

The reviewer configuration is the prescribed fresh `gpt-6.1-sol` / `xhigh`; actual backend telemetry and input, cached-input, output, and reasoning-subset counts are unavailable and remain null. No subscription allocation is inferred. The reviewer has no source/execution/cache/publication authority and releases all report writing at the final seal with no heavy command or inflight operation. The parent must read this complete Markdown and verify the full-review JSON, validation and release seals, exact source/evidence bindings, coverage, interactions and limited original scope before qualification.

## Unit 170: exact conditional unmarked-block Cauchy primitive

STATUS: CORRECT for the exact conditional statement below.

| Artifact | SHA256 |
| --- | --- |
| `AuxiliaryUnmarkedBlockCauchy.lean`, 4,569 bytes | `8ad60d527d05965fcc30ada9b2a5f9dd42618561aa50bc6e13a00fef8e6af4a1` |
| Kernel object | `ea74caf7dd5c9ca2265ccc5d842821142c634ad839e92e6c6692359e37797192` |
| Author receipt | `dcd39db7066d4a330562952ad09080a9d84d0edd5d678e70f8d57356fb34f02e` |
| Frozen imports/context/complete head | `6d6b0ae6b4b6dd2bc2b38f7a90b05ba0de4c36c4abf5692139be7da14108bc66` |
| All actual types, 6,780 bytes | `3984fd76901da44dd9a8edc798bac663c9689ad25cb8def48474a654d7252297` |
| All non-theorem values, 0 bytes | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

The full frozen file, full 91-line production source, complete source-and-proof note, freeze record/comparison, receipt, writer/execution release, complete OwnedAudit program, actual owner map, complete 6,780-byte actual type export, and empty value export were read. The new source imports only the accepted actual path measurability module and native `Mathlib.MeasureTheory.Function.L2Space`; context is `autoImplicit false`, `maxHeartbeats 3000000`, a noncomputable section, namespace `Shao.C2.AuxiliaryUnmarkedBlockCauchy`, and the `MeasureTheory`/`ProbabilityTheory` openings. One public head and no private/global non-theorem values were frozen before implementation. The complete head is:

```lean
theorem auxiliary_actual_unmarked_block_cauchy
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (A : Set (Shao.Path n)) (hA : MeasurableSet A)
    (hDamped : Integrable
      (fun v : Shao.Path n => |Shao.prefixSum v n| ^ (2 * p) *
        Real.exp (-s * Shao.energy v)) (Measure.pi (fun _ : Fin n => nu))) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let W : Shao.Path n → ℝ := fun v => Real.exp (-s * Shao.energy v)
    let D : Shao.Path n → ℝ := fun v => |Shao.prefixSum v n| ^ p * W v
    Integrable (A.indicator D) P ∧
      (∫ v : Shao.Path n, A.indicator D v ∂P) ≤
        Real.sqrt (∫ v : Shao.Path n,
          |Shao.prefixSum v n| ^ (2 * p) * W v ∂P) *
        Real.sqrt (∫ v : Shao.Path n, A.indicator W v ∂P) := by
```

The complete elaborated public type matches every parameter, natural exponent, probability instance, measurable-event hypothesis, damped-integrability premise, actual raw product, three lets, and both square-root integrals in this head. In particular, `hDamped` is a visible premise rather than a hidden instance, and its integrand is the actual full-block sum raised to 2*p multiplied by the actual Gaussian energy damping. There is no mark, beta factor, high moment of the scalar law, supplied rare-tail estimate, or final C2 assertion in the statement.

### Source-to-statement scope

This is the first Cauchy inequality on the unmarked block in supplement 5155-5159, already read in the original source passage above. It bounds the actual event integral by the square root of the actual unrestricted damped 2p-moment and the square root of the actual event Laplace factor. The rare-event Laplace estimate and the ordinary damped-moment estimate are separate obligations for a later consumer; this primitive does not assert or assume their numerical upper bounds.

The source writes general fixed a>=0, whereas this frozen leaf uses natural p. Thus acceptance covers precisely the natural-exponent conditional Cauchy step, not the complete real-exponent or higher rare-moment assertion. It is valid for any measurable event A and any probability nu, with no centering, variance or finite-third requirement needed for Cauchy itself. A later original finite-third rare-moment theorem must discharge `hDamped` from a qualified ordinary damped-moment producer in its actual applicable parameter range. In particular, at s=0, the displayed `hDamped` premise becomes raw block even-moment integrability; the current leaf makes no unconditional finite-third assertion at that endpoint. At s>0 it is the Gaussian-damped integrability obligation exactly as written. No raw sixth-moment hypothesis is silently installed on the original or auxiliary law of a root theorem.

### Complete proof review, source lines 25-89

1. Lines 25-35 introduce the actual raw product P and its probability instance, W(v)=exp(-s E(v)), H(v)=exp(-s E(v)/2), f(v)=|S(v)|^p H(v), and g=A.indicator H. Here S is the actual `prefixSum v n`, and E is the actual sum of coordinate squares. Accepted continuity of S/E gives continuity of H/f/W. There is no substitution by variance or a centered path and no law-transport premise.
2. Lines 36-40 show W integrable by domination by the integrable constant 1 under the probability product. W is positive, its norm equals itself, and s>=0 with E>=0 gives W<=1. This works for n=0, s=0 and arbitrary atoms. It pays the unmarked event-Laplace integrability without an independent oracle.
3. Lines 41-55 establish exact pointwise identities H^2=W, f^2=|S|^(2*p) W, and g^2=A.indicator W. `exp_nat_mul` and real ring arithmetic prove the first. Squaring the product and the natural power identity give the second, with p*2=2*p explicitly rewritten. The third covers both A membership branches; outside A, 0^2=0 is kernel-decided arithmetic, not `native_decide`. These are exact identities even at S=0 and p=0.
4. Lines 56-62 use the native real L2-square equivalence. Continuous f is strongly measurable, and its square is precisely the integrable function in the explicit `hDamped` premise, so f belongs to MemLp 2 P. The measurable indicator g is strongly measurable, and its square is the measurable-event restriction of integrable W, so g also belongs to MemLp 2 P. No integrability or higher moment is manufactured by treating an undefined real integral as finite.
5. Lines 63-73 use native `MemLp.integrable_mul` for the two actual L2 functions. The pointwise product is exactly A.indicator D: inside A the two half-damping factors multiply to W, outside A both sides are zero. This proves the required target integrability, independently of the later numerical inequality.
6. Lines 74-82 prove f and g nonnegative in every branch, then apply the native nonnegative integral Holder theorem with real conjugate exponents 2 and 2. The two MemLp 2 facts simplify to exactly the required `MemLp _ (ENNReal.ofReal 2)` premises. Both the scalar real conjugacy and the ENNReal Holder-triple instance have been checked from their actual native definitions.
7. Lines 83-89 use `Real.rpow_natCast` at 2 to identify each real exponent-2 power with its natural square, substitute the exact square identities and product identity, and use `Real.sqrt_eq_rpow` to obtain the precise frozen two-square-root bound. Both square integrands are nonnegative and integrable, so these are the actual finite nonnegative integrals intended by Cauchy. No constant, beta, whole-marked-product Cauchy estimate, or extra moment bound is introduced.

Boundary checks are explicit: when p=0, |S|^0=1 including S=0, and the proof becomes the ordinary event-Laplace Cauchy inequality. For n=0 the raw product is a probability measure on the single empty path, S=E=0, and the same identities cover p=0 and p>0. For s=0, W=H=1 and Cauchy remains valid whenever its literal `hDamped` premise holds. A can be empty, full, atom-supported or a weak equality event; the proof uses only measurability and covers both indicator branches. No energy division, strict endpoint conversion, null-set deletion, or positive sample-length premise appears.

### Every actual unit 170 owner and recursive axiom coverage

The complete actual map yields **2 owned constants, both theorems: 1 public source theorem, 1 generated simplification theorem, 0 private source theorems, 0 global non-theorem values**. Its names are bijective with the complete actual type export.

* `Shao.C2.AuxiliaryUnmarkedBlockCauchy.auxiliary_actual_unmarked_block_cauchy`: complete elaborated type and production proof reviewed above; recursive axioms are exactly propext, Classical.choice, Quot.sound.
* `Shao.C2.AuxiliaryUnmarkedBlockCauchy.auxiliary_actual_unmarked_block_cauchy._simp_1_1`: complete actual type is `forall {alpha : Type u} [Preorder alpha] (a : alpha), (a <= a) = True`. Preorder reflexivity and proposition extensionality prove it for every such alpha/a. It is the generated reflexive inequality simplification in the zero branch of g's nonnegativity. Its only axiom is propext. It introduces no additional parameter restriction or mathematical hypothesis.

The complete empty value export matches the absence of any actual non-theorem owner. The full unit 170 audit program uses the same actual module-owner selector and recursive collector analyzed above, now with its exact unit 170 target and public-name count check. It audits both generated/public entries, not just the public list. Both recursive axiom lists stay within the standard whitelist. Attempt 001 has original server kernel exit 0 and owned-audit exit 0; there is no failed Lean attempt to replace or replay. Source, successful snapshot, output object and actual worktree-imported object are bound to the released bytes. All frozen imports/context/head bytes remain exact. The source is UTF-8 without BOM, LF-only, and contains none of the forbidden proof shortcuts.

### New native L2/Holder contracts and paid premises

The new native contracts were read from actual pinned sources and surrounding variables, extending the already-reviewed shared native integrability/product contracts. The required native source files match the exact pinned mathlib blobs. The L2Space object is observed in the accepted package view; no cache hydration or rebuild occurs.

| Native contract | Complete relevant premises and new use |
| --- | --- |
| `memLp_two_iff_integrable_sq` | For a real-valued AEStronglyMeasurable f under any measure, `MemLp f 2 mu` iff integrability of f^2. Both new functions' measurability and square integrability are explicitly established as described above. There is no hidden finite-measure, sigma-finite, density, or nonzero-n premise. |
| `MemLp.integrable_mul` | For a normed ring, requires MemLp f p mu, MemLp g q mu and ENNReal `HolderTriple p q 1`. Real scalars qualify; ENNReal `HolderConjugate.instTwoTwo` supplies the actual (2,2,1) instance through the identity 2^-1+2^-1=1. |
| `Real.HolderConjugate.two_two` | The real structure requires positive exponents and p^-1+q^-1=1. Its actual native constructor proves these at p=q=2. It supplies precisely the exponent condition in the integral Holder theorem. |
| `integral_mul_le_Lp_mul_Lq_of_nonneg` | Requires the real conjugacy, almost-everywhere f>=0 and g>=0, and MemLp f/g at `ENNReal.ofReal` of the two exponents. The proof supplies pointwise nonnegativity and actual L2 membership for exactly P; the theorem concludes int(fg)<=(int f^2)^(1/2)(int g^2)^(1/2). It assumes no rare-event probability estimate. |
| `Real.exp_nat_mul`, `Real.rpow_natCast`, `Real.sqrt_eq_rpow` | Read at their actual pinned definitions. These identities apply to the exact real H/f/g and exact natural square/exponent casts used. The final square-root conversion does not require an omitted sign premise; the square integrals are nonnegative in any case. |

No unpublished scalar-polynomial producer, extra rare-event oracle, old private helper reimplementation, or unit 169 conclusion is consumed by unit 170. Its only project interactions are the accepted actual path definitions, continuity and nonnegative energy, already covered above and exact-bound afresh. The Cauchy step is applied solely to the unmarked remaining block.

## Combined milestone disposition

Both exact leaves are CORRECT under their complete frozen hypotheses. Combined actual counts, derived from both actual owner maps and both complete exports, are **2 modules / 2 public source theorems / 5 actual owned theorems / 3 generated theorems / 0 private source theorems / 0 non-theorem values**, with **47,949 bytes** of complete actual types and **0 bytes** of definition values. The generated declarations comprise one arithmetic proof and two simplification theorems.

Unit 169 supplies the beta-linear marked a=0 bound. Unit 170 supplies the conditional natural-exponent unmarked Cauchy integration primitive, with its Gaussian-damped moment integrability premise still to be paid in any later higher rare-moment consumer. Combining these accepted leaves does not discharge that later premise, prove general marked/unmarked moment bounds, supply inverse moments or weighted records, or close C2/C12. Review independence, exact-source receipts, actual whole-owner axiom coverage, source fidelity, no server changes, zero Lean/audit executions, zero successful-gate replays, prescribed model/effort and null unavailable usage telemetry apply to both units. Final bindings, validation and exclusive report-writer release are sealed alongside this report; parent complete reading and qualification remain required.

The final read-only observation at `2026-10-24T22:59:49.506179+00:00` verifies **144 exact remote bindings**, both complete audit-log-derived exports and empty value exports, both frozen comparisons, both original successful kernel/audit exits, both author releases, and **no running target Lean/lake process**. All **14 inspected native source files** match their pinned mathlib blobs. The actual native L2Space object is present with SHA256 `5003966f03550ac64767bb0bfc18491936a2613cf68cb4cd8627778d423975d0`. Branch, HEAD, tree, toolchain and package view remain exactly those recorded above. These are fresh read-only observations, not new proof or audit executions.
