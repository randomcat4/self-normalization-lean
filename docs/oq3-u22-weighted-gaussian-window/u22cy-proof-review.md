# U22CY184 independent complete final review

STATUS: CORRECT
JUSTIFICATION: The exact frozen four declarations are faithfully implemented and completely proved. The saved exact-source server kernel and whole-module recursive axiom receipts pass. The result is genuine Lebesgue integrability on the whole real plane for every natural Euclidean radial power and every strictly positive Gaussian coefficient.

Reviewer: fresh independent non-author context `oq3_u22cy_full_review`, prescribed gpt-6.1-sol / xhigh. I used math-theorem, not math-ultra, and read the applicable AGENTS.md, SERVER.md, relevant TEAM/REGISTRY ownership and resource entries, takeover/restart rules and current streamlined acceptance. OQ3 ownership remains with the activated lead, with child ceiling one. My sole written artifact is this report; I changed no proof, declaration, scope, shared file, receipt, Git state or server artifact. No Lean/build/axiom command was rerun.

## Exact coverage and artifact identity

I read all 86 source lines, all 18 freeze lines, all 21 exported actual-type lines, all 47 audit-source lines, and the complete saved build history, receipt, audit record, audit environment, dependency binding and both original logs. All local and corresponding saved server bytes agree. The canonical server source also has the same hash.

| Local artifact in drafts/oq3 | SHA256 | Coverage |
|---|---|---|
| u22cy-source.lean | `95aa9d280eb607c46768688ae6adcd758205f9cbf00d8891277e98d50145bbeb` | 86 lines, 3812 bytes, complete |
| hundred-eighty-fourth-unit-scope.md | `7e740d77129abdc5f0dbcafbea01ba084b65358b8df70c1c30f3eedc5369e434` | 18 lines, 1448 bytes, complete |
| u22cy-actual-types.txt | `1c9ab44cd8b155bd4ac3d9aa1b1cee392486041bcfb643ecdc1db357b681046e` | 21 lines, 974 bytes, complete |
| u22cy-Audit.lean | `06ff94916048090c399f02ca538a17ff70b824212c6a4a2a2928ba2458593081` | 47 lines, 2163 bytes, complete |
| u22cy-receipt.json | `074cd2b02b835b11067741febff705cbe527ed49d1b248afa57399ed8af8a38e` | 93 lines, 4190 bytes, complete |
| u22cy-build-history.json | `b586e3d441891f54d8c4d6f24d151ede344f1b8bcda7542259bf78783323363a` | 26 lines, 1132 bytes, complete |
| u22cy-audit-record.json | `004f09910f3952246b652c6153f34c744b6e52757dc258b02d3d50f58c95f7e8` | 18 lines, 498 bytes, complete |
| u22cy-audit-environment.json | `b2f8d3aa434005c5f675f1c931b14765eb92454bb02919c819aa1c6e279bff62` | 13 lines, 1391 bytes, complete |
| u22cy-dependency-source-binding.json | `bceb11f1a9896098eb79714bf8098f9062b6858ea97a34133e28f19a9b1be68b` | 34 lines, 2163 bytes, complete |

The local source/freeze/type/audit/evidence files are UTF-8 without BOM and have LF line endings. The substantive freeze contains exactly the four implemented theorem signatures, with unchanged domains, quantifiers, hypotheses and conclusions. It explicitly specifies whole-plane Lebesgue integrability, every natural power, every a > 0, literal Euclidean radius and Mathlib-only dependencies.

## Complete actual ownership, types and definition-value coverage

The original audit exports exactly the following complete 21-line actual inventory, which I read against the source and freeze:

```text
DECL Shao.OQ3.integrable_euclidean_radius_power_gaussian
TYPE ∀ (k : ℕ) (a : ℝ),
  0 < a →
    MeasureTheory.Integrable (fun w => √(w.1 ^ 2 + w.2 ^ 2) ^ k * Real.exp (-a * (w.1 ^ 2 + w.2 ^ 2)))
      MeasureTheory.volume
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
DECL Shao.OQ3.one_add_nonnegative_power_bound
TYPE ∀ (x : ℝ), 0 ≤ x → ∀ (k : ℕ), (1 + x) ^ k ≤ 2 ^ k * (1 + x ^ k)
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
DECL Shao.OQ3.integrable_one_add_square_power_gaussian
TYPE ∀ (k : ℕ) (a : ℝ),
  0 < a → MeasureTheory.Integrable (fun x => (1 + x ^ 2) ^ k * Real.exp (-a * x ^ 2)) MeasureTheory.volume
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
DECL Shao.OQ3.integrable_even_power_gaussian
TYPE ∀ (k : ℕ) (a : ℝ),
  0 < a → MeasureTheory.Integrable (fun x => x ^ (2 * k) * Real.exp (-a * x ^ 2)) MeasureTheory.volume
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
```

There are four public source theorems, four actual owned constants, four actual theorems, zero private theorems, zero generated theorems and zero owned definitions. These counts come from the actual module-owner enumeration and complete log, rather than a descriptive count copied from another unit. There are no omitted definition values or statement-level lets. The only proof-level `let` is source line 63, `r : ℝ := Real.sqrt (w.1 ^ 2 + w.2 ^ 2)`; I reviewed its full value and every subsequent use. The proof-local `h1`, both majorants `hg`, and the exponent side condition are derived proof terms, not added hypotheses.

## Actual consumed primary interfaces and meanings

I read the pinned primary GaussianIntegral source through its complete consumed declarations and their proofs (lines 62–117, with the preceding namespace/import context), the Real power definition and cast proofs (lines 27–61), and the complete product-integrability implementation chain (Integral.Prod lines 261–302 with its measure/type context). These are the APIs actually consumed, not similarly named project wrappers.

1. The Gaussian API is the GLOBAL `integrable_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) : Integrable (fun x : ℝ => x ^ s * Real.exp (-b * x ^ 2))`. It has no positivity restriction on x and no assumed finite integral. Its proof obtains the positive-half-line result from the convergent Gamma integral and scaling, then joins the two half-lines using reflection and norm domination. Thus it proves genuine all-real Lebesgue integrability, including near zero and both tails. The global `integrable_exp_neg_mul_sq hb` is its s = 0 consequence, again on the entire real line.
2. `Real.rpow` has full value `((x : ℂ) ^ (s : ℂ)).re`. The exact theorem `Real.rpow_natCast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n` has NO x ≥ 0 premise. Its proof goes through `rpow_intCast`. Therefore the cast rewrite at source lines 31–32 is valid also for negative x and for x = 0, n = 0. It produces the literal natural even power, not an unverified absolute-power replacement.
3. `MeasureTheory.Integrable.mul_prod` takes `Integrable f μ` and `Integrable g ν` and concludes `Integrable (fun z : α × β => f z.1 * g z.2) (μ.prod ν)`. The consumed implementation is `smul_prod`, then `op_fst_snd`, which proves strong measurability and finite norm integral via the product integral bound. It requires no finite-volume assumption. Here f = g = `(1 + x ^ 2) ^ k * exp (-a * x ^ 2)` and μ = ν = real volume.
4. I read Measure/Prod lines 179–184: the product `MeasureSpace` instance has full volume value `volume.prod volume`, and `volume_eq_prod` is `rfl`. Hence the product-integrability result is exactly the default volume on `ℝ × ℝ`, not a different ambient measure. I read the actual `Integrable` definition (L1Space/Integrable lines 55–60): `AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`, with default μ = volume. `HasFiniteIntegral` is the strict finiteness of the extended norm integral (HasFiniteIntegral lines 79–84). The claims therefore do not rely on the default value of an undefined Bochner integral.
5. The consumed `Integrable.mono'` contract (L1Space/Integrable lines 104–106) is: integrability of a real g, AEStronglyMeasurable f, and `∀ᵐ x ∂μ, ‖f x‖ ≤ g x` imply integrability of f. Both applications supply every condition. `fun_prop` supplies AEStrong measurability from global continuity of the displayed natural polynomials, exponential and, in the planar case, continuous real square root. Both norm rewrites are justified by nonnegativity of the full target. The displayed inequalities hold pointwise, so the empty `filter_upwards` premises introduce no exceptional region.

Primary exact source/object bindings, independently rehashed through the existing server package paths:

| Primary module | Source SHA256 | Existing .olean SHA256 / bytes |
|---|---|---|
| Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral | `4378f161cf5d482be77941cc9aea0195d2e83fe54eeb51b2ab33db1a318ccb9c` | `5b2ecbcdf0f059aa0c68dcb2e5406037f8b732ff727076309f981a40d8b0f3ef` / 41920 |
| Mathlib.MeasureTheory.Integral.Prod | `8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05` | `274aad1a33fb62f0ca5339e5769ff80c62f8af9e2720b86371e2224d927ba0fe` / 284712 |
| Mathlib.Analysis.SpecialFunctions.Pow.Real | `f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd` | `351f2c4f9fdd5a426267926a1c39729c45c82073e13e477f45ac5c254f3b18a3` / 409416 |

The objects resolve into the existing read-only `cache-overlays/shared-v34/packages/mathlib/.lake/build/lib/lean` tree. The dependency binding records `before_first_kernel: true`; its saved mtime is 2026-10-23T22:21:28.619100Z, before the frozen source snapshot (22:21:50.483040Z) and first kernel log (22:21:51.459037Z). The current hashes agree with that recorded pre-first-kernel binding. Supplementary semantic source hashes read here are Measure/Prod `007561e86f53a65ad411fcbd20d05df9e922f01c5a93eff0f9de26ac49f12ca3`, L1Space/Integrable `d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759`, and L1Space/HasFiniteIntegral `cab8f2f4781c1363583f9c91df1d08843de863a48f5f94a308823e74ed83410f`.

## Complete source-to-statement and proof review

### 1. Nonnegative power bound — source lines 9–24

The statement quantifies every real x ≥ 0 and every natural k. When x ≤ 1, 0 ≤ 1 + x ≤ 2 gives `(1+x)^k ≤ 2^k` by monotonicity of natural powers on nonnegative reals. Also x^k ≥ 0, so multiplication by 2^k ≥ 0 gives `2^k ≤ 2^k(1+x^k)`. When x > 1, the proof derives 1 ≤ x, then `0 ≤ 1+x ≤ 2x`. Raising to k gives `(1+x)^k ≤ (2x)^k = 2^k x^k ≤ 2^k(1+x^k)`. Both branch bounds and both multiplier signs are justified. No division, positivity of k, or omitted x = 1 branch is used.

### 2. Genuine even Gaussian moment — source lines 26–32

For arbitrary k : ℕ, the real cast s = (2*k : ℕ) is nonnegative, hence -1 < s. With b = a and the sole given hypothesis 0 < a, the actual global Gaussian rpow-integrability theorem applies. `simpa only [Real.rpow_natCast]` changes exactly the real exponent s into the natural exponent 2*k for every real x. This proves the displayed all-real Integrable conclusion. There is no moment-integrability premise, truncation, positivity assumption on x, or replacement by a finite integral equality. Evenness also makes x^(2*k) nonnegative for all x, as needed by later domination.

### 3. Polynomial Gaussian envelope — source lines 34–51

Define the derived majorant `g(x) = 2^k * (exp(-a*x^2) + x^(2*k)*exp(-a*x^2))`. It is integrable by the actual Gaussian integrability result, theorem 2, integrable addition and scalar multiplication. The target `f(x) = (1+x^2)^k * exp(-a*x^2)` is continuous and nonnegative, so its norm is f(x). Apply theorem 1 with x replaced by x^2 ≥ 0, then multiply by the nonnegative exponential. The resulting upper bound is exactly g(x), because `(x^2)^k = x^(2*k)` by `pow_mul`, followed by ring distributivity. Consequently `hg.mono'` proves integrability on all of ℝ with its measurability and norm-bound requirements fully discharged.

### 4. Whole-plane Euclidean radial envelope — source lines 53–83

The source integrand is literally `F(u,v) = sqrt(u^2+v^2)^k * exp(-a*(u^2+v^2))`. It is not the product max-norm radius. Let `p(x) = (1+x^2)^k * exp(-a*x^2)`. Theorem 3 gives integrability of p, and the genuine product theorem gives integrability of `G(u,v) = p(u)*p(v)` for product real Lebesgue measure, definitionally the displayed planar volume.

The target is continuous and nonnegative, so its scalar real norm equals itself. For every pair, source line 63 defines `r = sqrt(u^2+v^2)`. The proof obtains r ≥ 0 and r^2 = u^2+v^2, with the square-root input nonnegative. Put `P = (1+u^2)(1+v^2) = 1+r^2+u^2*v^2`. From `(r-1)^2 ≥ 0`, one has `1+r^2 ≥ 2r`; since r ≥ 0 and u^2*v^2 ≥ 0, this implies r ≤ P. These are precisely the facts passed to `nlinarith` at lines 66–67, so the geometrical domination is valid globally.

Monotonicity of natural powers gives `r^k ≤ P^k = (1+u^2)^k * (1+v^2)^k`. Ring algebra and `Real.exp_add` give `exp(-a*(u^2+v^2)) = exp(-a*u^2)*exp(-a*v^2)`. Multiplication by this nonnegative product yields `F(u,v) ≤ G(u,v)`, with exactly the rearrangement in lines 76–83. The pointwise inequality supplies the required almost-everywhere norm bound, and `hg.mono'` concludes genuine integrability on the entire plane. No finite-volume or compact-support fact is invoked.

### Boundary, sign and quantifier audit

- k = 0 is included throughout. Natural zeroth powers equal one even at zero. The first bound becomes 1 ≤ 2; the integrability statements reduce to Gaussian integrability, with no division by k or positive-exponent assumption.
- At (0,0), r = 0 and the square-root identity holds. For k > 0 the radial factor is zero; for k = 0 it is one. The proof and majorant cover both cases directly.
- Either coordinate axis, either coordinate sign and arbitrary negative x in theorem 2 are covered. Squares and the exact all-real natural-cast API justify the uses; there is no quadrant restriction or discarded axis.
- Every a > 0 is permitted without a hidden positive lower bound, relation to k or upper bound. Strict positivity is used in genuine Gaussian integrability. No uniformity in a, endpoint a = 0, negative k or fractional radial power is claimed.
- The real norm rewrites apply to scalar integrand values. They do not identify the norm of a pair with Euclidean radius. The planar measure is product Lebesgue volume, independently checked from its defining instance.
- Both AEStrong measurability obligations, both norms, all multiplier signs, the exponent cast, exponent multiplication and the exact product measure are covered. There is no concealed assumed conclusion or unused mathematical prerequisite.

## Saved server kernel, environment and recursive axiom evidence

Server run: `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22cy-20261023`.
Worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`.
Module: `Shao.OQ3.EuclideanGaussianPolynomialIntegrability`.

The saved first and only kernel attempt is attempt 1, exact source SHA256 `95aa9d280eb607c46768688ae6adcd758205f9cbf00d8891277e98d50145bbeb`, inner exit 0, 4.882227826863527 seconds. Its full 133-byte log has SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`. I read the complete log: it contains only the known Lake warning that the mathlib repository has local changes. Actual consumed source/object hashes are explicitly bound above, so I did not infer cleanliness from the Git commit alone.

The first whole-owner recursive axiom audit has inner exit 0, 5.484799779951572 seconds. Its complete 1226-byte log has SHA256 `a78c567daf555db35b53ea4c76e83ad17c27573eecd4382a3ccfe2b55975ea76`. It contains the same Lake warning, the complete four-owner inventory reproduced above, and `U22CY_FROZEN_DEFINITIONS 0`, `U22CY_FROZEN_THEOREMS 4`, `U22CY_ALL_THEOREMS 4`, `U22CY_ALL_DECLARATIONS 4`, `U22CY_AXIOM_GATE PASS`.

I read the entire audit implementation. It enumerates environment constants, identifies actual ownership by `env.getModuleIdxFor?` equal to this exact module, rejects owned axiom declarations, recursively collects axioms for EVERY owned constant and rejects anything outside `propext`, `Classical.choice`, `Quot.sound`. It checks every frozen target exists with theorem kind, counts the actual owners and prints any owned definition values. Its complete output proves all four actual owners are the four expected theorem constants, with no omitted private/generated/value scope. Each recursive axiom set is exactly the standard three. The printing-only options `pp.deepTerms` and `pp.maxSteps` do not weaken kernel checking.

The entire source has no `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, `implemented_by` or `set_option`; its `noncomputable section` is not a logical bypass. The proofs use ordinary kernel-checked order, arithmetic, continuity and integration results. Both recorded gates use CPU14–17, native -M8192, -j4 and autoImplicit false under the OQ3 single-heavy limit. I reused the saved successful gates and did only bounded read-only file/hash/Git observations through tools/server.py; successful read requests had inner exit 0. No raw logs, cache files or binaries were downloaded, and no package/cache write, update, local Lean invocation or publication occurred.

I read the server `lean-toolchain`: `leanprover/lean4:v4.36.0-rc1`, SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`. I read the full lakefile: mathlib revision `807d3836b165983210ee2ecf3cd28f239436949c` and autoImplicit false; its SHA256 is `444f3a3a01fd8ff99f219cff08a99b20459c0d177c4e2c884af9eead481daf44`. The actual server mathlib checkout reports that same pinned revision. These are existing accepted packages, not newly built dependencies.

The current canonical CY object was observed read-only with SHA256 `36c2389b115b169053ff1062ff3382405677eac5a34060bff352650b4ee6ac5e`, 274320 bytes. The saved audit environment's added-own-artifact path is that exact worktree `.lake/build/lib/lean/Shao/OQ3/EuclideanGaussianPolynomialIntegrability.olean`; the `runs/oq3/accepted-source-view/Shao/OQ3/EuclideanGaussianPolynomialIntegrability.olean` symlink resolves to it with the same hash. This current-object observation is distinct from the pre-first-kernel primary dependency binding and does not invent an earlier recorded object hash.

The build history contains exactly one successful source version, no failed Lean attempts and no repairs. The first-success source remains unchanged. All saved histories, both logs and the archived frozen bytes were preserved; there was no PASS edit or replay.

## Historical/current boundaries and acceptance scope

The receipt's historical author-check parent is `9c8680b44f12d634bd74d9251ec2f26caac921e8` on `feat/oq3-low-frequency-and-inversion` (frozen PR228). At my 2026-10-23T22:40:34.584324Z read-only observation, that remained the observed lane HEAD, tree `d0a6f95c0b3dc46353c07f9a0025c42fb4084ecb`; CY source was untracked and still exact-hash unchanged. These are time-stamped observations, not a requirement that the lead keep HEAD fixed while publishing the separately qualified CQ–CX milestone. This report binds CY bytes and evidence, not later branch movement. CY/CZ/DA are not attributed to that separate publication.

I checked the local root v62 receipt SHA256 `921918687d9649bbbeda534ce9b9fd4901e5f34334bdeb6bf8ecbc0268673745`: its actual checked code commit is `3425d698ca49d38787597ba1f18f83aa781ddf0a`, tree `47e73e2fcbb28d894b4d4aa46a0f334636af1fc3`, status PASS and the same mathlib pin. These are distinct from the root notice's main `0d096cf56be001f9ed84a76b74c9e6fa0bef66a8`, accepted head `489d0249a0e498958859a2be88282dbba97c1899`, tree `3152c4d078580467007482cccd7ba439a19410d8`. Root history is background provenance; this unit imports only the two displayed Mathlib modules and does not depend on an old project proof or claim a new root check.

This is an elementary Gaussian envelope integrability producer for the actual raw-iid weighted-L1 small-frequency error chain. CY itself neither states nor proves the characteristic-function error, the downstream weighted-error estimate or an original OQ3 root. Those require their separately frozen consumers. It does not close original B/D, higher Edgeworth, remaining-frequency control, inversion, exterior estimates or new-rho Laplace asymptotics. Original strict `0 < beta < 2/5`, p54 repairs and external-result attribution are unchanged. No novelty or research-root completion claim is made.

Final independent verdict: CORRECT for all four exact frozen declarations and the complete proof/actual-owner scope of source SHA256 `95aa9d280eb607c46768688ae6adcd758205f9cbf00d8891277e98d50145bbeb`. No critical gap, uncovered owner/value, disallowed axiom or source-fidelity discrepancy remains in this unit. The saved exact-source author kernel and whole-owner axiom evidence can be reused with this qualified review; no duplicate gate is needed for unchanged bytes.
