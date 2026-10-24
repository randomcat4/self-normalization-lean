# U22CZ185 independent complete final proof review

STATUS: CORRECT
JUSTIFICATION: The complete exact frozen theorem is faithfully implemented and proved. The saved exact-source server kernel and all-owned recursive transitive-axiom checks pass. The weighted error is genuinely integrable on the exact scaled ball, and its nonnegative Lebesgue integral is bounded by the stated genuinely integrable whole-plane Gaussian moment. This is an explicitly conditional integration helper, not an original OQ3 root estimate.

## Independence and review boundary

Fresh non-author final reviewer, dispatched as gpt-6.1-sol / xhigh; sole child lease, no subagents. I applied math-theorem and the current AGENTS.md, SERVER.md, selected current TEAM/REGISTRY ownership/resource fields and streamlined-acceptance instructions. OQ3 old-writer release and replacement activation are recorded; this reviewer owns only this report. No implementation, receipt, status, shared coordination or Git file was changed. No Lean/Lake command, build, axiom rerun, cache write, publication or old successful gate was executed in this review. Server observations were bounded read-only source/log/hash/object/pin reads. Exact token counters were not supplied and no usage allocation is inferred.

I read all 103 final source lines, all 33 scope lines, all 23 actual-type lines, all 47 audit-source lines, and the complete local receipt, build history, audit record, audit environment and dependency binding. I read all three original server logs, the entire source01-to-source02 diff, and verified local/saved-server/canonical-source correspondence. Established old independent reviews are reused for unchanged dependencies; their complete consumed interfaces, actual types, relevant values, qualification hashes and source/object bindings were checked without repeating an old complete proof/report review.

## Exact reviewed bytes

| Artifact | SHA256 | Lines / bytes |
| --- | --- | --- |
| Final source / server source-02.lean | `4fdc3834b387aec486ce31df8808d4c3758afcbb93cf9c92b7b48191e2b4776c` | 103 / 4846 |
| Complete declaration freeze / scope.md | `833f34f1f40ed95f4a48492205420dcbb2369b724305e4b03ece86692151b228` | 33 / 2539 |
| Actual types | `032178f4a3a10e3e08ed6df395c70fddce0c5509e5a576f23b17c1268f2092df` | 23 / 1517 |
| Audit.lean | `58bd0dd3950516672a4bbe446b6e7be76a5ec962e50ae63597fb07ffee4400e2` | 47 / 2031 |
| Receipt | `7a8c1119b90565830568d5efdb1f4d92966224cc9dee04d78ccdeb3756f4d6e2` | 115 / 5793 |
| Audit environment | `b00fea07ce2d11c821cd01bba2b2b1ece8e97ba69075348b4666c3a1eeb8e177` | 12 / 1566 |
| Audit record | `9a5a8065abd46430475c5db29f7d66d1ef6b0662e993e020d06ff90d7db32bdd` | 18 / 498 |
| Build history | `57b724e95d8e4ec54ba9c9fe972923437e1bb10f606112d19bb703987a424d8c` | 50 / 2628 |
| Dependency source binding | `9100afe3596be7ed49425679f88d805f519ee00bbbbebe9068f3354d57dc3706` | 40 / 2461 |

All these local artifacts are UTF-8 without BOM and use LF, with no CRLF. The 27-line source theorem header, including all four statement-let values, equals the complete frozen Lean declaration exactly. The server canonical `Shao/OQ3/PairCharacteristicWeightedIntegral.lean` has the final source hash above. The complete actual-type file equals the declaration/type/axiom/kind extraction from the original audit log byte-for-byte.

## Actual owned statement and values

The sole actual owner is the public theorem `Shao.OQ3.pair_characteristic_small_frequency_weighted_integral_bound`. The complete exported elaborated type is:

```text
∀ (rho : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsProbabilityMeasure rho] (n : ℕ),
  1 ≤ n →
    ∀ (delta B : ℝ),
      0 ≤ B →
        (∀ (xi eta : ℝ),
            √((xi / √↑n) ^ 2 + (eta / √↑n) ^ 2) ≤ delta →
              ‖∫ (w : ℝ × ℝ), Complex.exp (↑(xi * w.1 + eta * w.2) * Complex.I) ∂rho -
                    ↑(Real.exp (-(xi ^ 2 + eta ^ 2) / 2))‖ ≤
                B / √↑n * √(xi ^ 2 + eta ^ 2) ^ 3 * Real.exp (-(xi ^ 2 + eta ^ 2) / 8)) →
          ∀ (k : ℕ),
            have small := {w | √((w.1 / √↑n) ^ 2 + (w.2 / √↑n) ^ 2) ≤ delta};
            have error := fun z =>
              ‖∫ (w : ℝ × ℝ), Complex.exp (↑(z.1 * w.1 + z.2 * w.2) * Complex.I) ∂rho -
                  ↑(Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2))‖;
            have weight := fun z => √(z.1 ^ 2 + z.2 ^ 2) ^ k;
            have envelope := fun z => √(z.1 ^ 2 + z.2 ^ 2) ^ (k + 3) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8);
            MeasureTheory.Integrable envelope MeasureTheory.volume ∧
              MeasureTheory.IntegrableOn (fun z => weight z * error z) small MeasureTheory.volume ∧
                0 ≤ ∫ (z : ℝ × ℝ) in small, weight z * error z ∧
                  ∫ (z : ℝ × ℝ) in small, weight z * error z ≤ B / √↑n * ∫ (z : ℝ × ℝ), envelope z
```

The four statement-let values have types `Set (ℝ × ℝ)`, `(ℝ × ℝ) → ℝ`, `(ℝ × ℝ) → ℝ`, `(ℝ × ℝ) → ℝ`, respectively. They are the literal scaled closed ball, actual complex characteristic-function-minus-real-Gaussian norm, Euclidean-radius natural power and radius-to-the-(k+3) Gaussian envelope. This uses the displayed Euclidean radius, not the product space's norm. The phase law is exactly rho, the complex Gaussian is the cast of the displayed real exponential, and all outer integrability/integrals use `MeasureTheory.volume` on the pair space. There is no substituted law, artificial error, changed Gaussian, finite test set or hidden integrability premise.

The proof-local `small`, `error`, `weight`, `envelope` in lines 38-48 repeat these exact values after `dsimp only`. The fifth local value `c : ℝ` is exactly `B / Real.sqrt (n : ℝ)`. All local mathematical aliases and proof types are covered below; no named definition values or generated owners remain outside this review.

| Proof-local name | Complete role / type and value check |
| --- | --- |
| `hc` | Proof of `0 ≤ c`, from `div_nonneg hB (Real.sqrt_nonneg _)`. |
| `hp` | CY184 instantiated at natural exponent `k + 3`, real coefficient `1 / 8`, and a proof of `0 < (1 / 8 : ℝ)`; its integrand is radius^(k+3) times exp(-(1/8)(z.1²+z.2²)). |
| `hexp` | For every pair z, equality of `Real.exp (-(1 / 8 : ℝ) * (z.1 ^ 2 + z.2 ^ 2))` and `Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)`, proved by congruence and ring arithmetic. |
| `hen`, `hg` | Proofs of `Integrable envelope volume` and `Integrable (fun z => c * envelope z) volume`; `hg` is `hen.const_mul c`. |
| `hF`, `hG` | Continuity of the displayed actual rho-characteristic integral and displayed cast real Gaussian on all of ℝ². |
| `hecont`, `hwcont` | `Continuous error`, from the norm of the continuous difference, and `Continuous weight`, from continuous square/sum/square-root/natural-power operations. |
| `hsmall` | `MeasurableSet small`, from the closed sublevel set of the continuous scaled-radius function. |
| `hnonneg` | `∀ z : ℝ × ℝ, 0 ≤ weight z * error z`, using nonnegative square-root powers and complex norms. |
| `h`, inside `hbound` | The exact herror inequality at `z.1,z.2`, multiplied by the nonnegative radius^k; no estimate outside small is invoked. |
| `hbound` | `∀ z ∈ small, weight z * error z ≤ c * envelope z`, with `pow_add` combining k and 3 and ring arithmetic preserving c and the exponent. |
| `hei` | `IntegrableOn (fun z => weight z * error z) small volume`, obtained by genuine norm domination under `volume.restrict small`. |

Local bound variables z/w are always pairs of reals; xi/eta are real frequency coordinates; hz is membership in the exact small set. There are no local typeclass/selector/witness values that impose a new mathematical hypothesis.

## Complete proof and source-to-intent review

Lines 9-36 quantify an arbitrary actual pair probability measure, natural n with the frozen `hn : 1 ≤ n`, arbitrary real delta, nonnegative real B, the explicitly supplied pointwise actual error estimate on the exact scaled ball, and EVERY natural weight k. The four conclusions match the freeze without strengthening the premise or shrinking any domain. This helper does not assert that an arbitrary law satisfies the pointwise estimate: deriving that estimate is the canonical caller's obligation. No IID, centering, covariance, moment or weak-Cramer hypothesis is secretly inferred from the probability typeclass.

Lines 49-60 first establish nonnegativity of c and genuine whole-plane integrability of the actual envelope. CY184 applies for all natural k+3 and strictly positive 1/8. The exponent conversion is an equality for every pair, so `hen` concerns the literal final integrand. Multiplication by finite real c gives the genuine majorant integrability `hg`; no totalized value of an unproved Bochner integral is used.

Lines 61-70 use CI168's actual probability-law characteristic-function continuity, not a surrogate continuity premise. That qualified interface has no weak-Cramer or moment assumptions and no statement lets/definition values. Its characteristic integrand has norm identically 1 under the probability law, so the underlying characteristic integrals are genuine; continuity is not masking a nonintegrable totalized phase integral. The displayed real Gaussian is continuous after complex casting; taking a norm of their difference proves continuity of the actual error. Weight continuity includes the origin and k=0. The scaled radius is continuous for the fixed denominator, and its weak sublevel set is closed and measurable even when delta is zero or negative.

Lines 71-86 establish pointwise nonnegativity everywhere and the exact pointwise domination on small. The only estimate consumed is `herror z.1 z.2 hz`; multiplication is licensed by the explicitly nonnegative radius^k. The algebra combines radius^k times radius^3 into radius^(k+3) and retains the factor B/sqrt(n) and decay exp(-(xi²+eta²)/8). It neither drops a sign nor substitutes a norm convention.

Lines 87-92 establish genuine integrability under the restricted Lebesgue measure. The actual primary `Integrable.mono'` contract takes an integrable real majorant, AEStronglyMeasurable actual target under the SAME measure, and AE norm domination. Here `hg.integrableOn` supplies the majorant for `volume.restrict small`; continuity of `weight * error` supplies AEStronglyMeasurable for that restricted measure directly. `ae_restrict_mem hsmall` places almost every restricted point inside small. The explicit pointwise `change` unfolds the Pi multiplication application; `Real.norm_eq_abs` and `abs_of_nonneg (hnonneg z)` turn its norm into the actual nonnegative product, allowing exactly `hbound z hz`. This proves finite integrability, rather than appealing to a default value for a nonintegrable integral.

Lines 93-101 return hen and hei before comparing integrals. The nonnegativity conclusion follows from the everywhere nonnegative target under the restricted measure, and hei already proves this is a genuine integral. I read the complete actual Mathlib contracts, including their surrounding integrability variables: `setIntegral_mono_on` requires IntegrableOn for BOTH functions, a measurable set and pointwise ordering on that set; these are exactly hei, hg.integrableOn, hsmall and hbound. `setIntegral_le_integral` requires whole-space integrability and AE nonnegativity of the majorant; hg and `mul_nonneg hc` with nonnegative envelope provide them. Finally `integral_const_mul` factors the finite real c out of the genuinely integrable whole-plane envelope. All measures and domains agree throughout.

Boundary audit: k=0 uses the usual natural-power convention, including radius^0=1 at the origin, and `pow_add` remains valid. The origin, either coordinate axis, and the closed-ball boundary are included without division by a frequency or radius. B=0 gives a zero integrable majorant and the supplied bound forces the nonnegative weighted target to vanish on small. For delta<0 the small set is empty since square roots are nonnegative; for delta=0 and n≥1 it is the origin. The uniform proof covers both without a positivity assumption on delta. n=0 is excluded by the frozen hn; mathematically n≥1 makes sqrt(n)>0, but the proof only needs its nonnegativity. hn is honestly surplus for this domination argument and is preserved unchanged. No linter-silencing edit or weakened setting was introduced.

## Qualified unchanged dependencies and actual source/object binding

CI168 module `Shao.OQ3.WeakCramerPairCompactGap`: exact 54-line source `87853bd10cb17b802c46cdeceb957c6630fb8f7b06b5d304709d660876c03d54`; receipt `683b7dd00c27c12bed3745bad35348633ff0b9a3fc43028967b3513c81090e52`; qualified complete joint CH/CI final review `398b579b32857c6e83d70ff507bb3fb9200f8d8760ac0cec7ec67ed3b77e1f7b` (105 lines, STATUS CORRECT). Its actual owner map has two theorems, no definitions or generated/private owners. I checked the entire consumed `continuous_pair_characteristic` declaration and exported actual type: arbitrary probability measure on ℝ² implies continuity of exactly the displayed actual characteristic integral, with no extra premise and no let values. I reused the existing qualified proof/kernel/axiom evidence, not a repeat full proof review. The original dependency object is `3df95be58fb921cb56f58ee8bec60a20ae04c2a3483caad63c59d8cda31ef142`, 131040 bytes, matching the pre-first-kernel binding and current server object.

CY184 module `Shao.OQ3.EuclideanGaussianPolynomialIntegrability`: exact 86-line source `95aa9d280eb607c46768688ae6adcd758205f9cbf00d8891277e98d50145bbeb`; receipt `074cd2b02b835b11067741febff705cbe527ed49d1b248afa57399ed8af8a38e`; qualified complete final review `c6e2b660894524e59bd5526b4aefe98b95c854bad14ca16ba66e6838a469ad12` (135 lines, STATUS CORRECT). Its actual four-theorem owner map, all exported types and unchanged-source coverage are consistent. The consumed declaration is exactly `∀ (k : ℕ) (a : ℝ), 0 < a → Integrable (fun w : ℝ × ℝ => sqrt(w.1²+w.2²)^k * exp(-a*(w.1²+w.2²))) volume`, with no let values or named definitions. Thus CZ's required CY qualification has now been supplied for the SAME source and object, despite the chronologically earlier CZ receipt/binding honestly saying CY was awaiting review. No retroactive receipt edit is needed. CY's original object is `36c2389b115b169053ff1062ff3382405677eac5a34060bff352650b4ee6ac5e`, 274320 bytes, matching the pre-first-kernel binding and current server object.

Both dependency canonical source hashes match their local snapshots and the saved CZ binding. Their `runs/oq3/accepted-source-view/Shao/OQ3/*.olean` symlinks resolve to the original lead-oq3 worktree objects with the hashes above. The primary Bochner.Set source has SHA256 `e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75`; its shared-v34 package object is `e5ff2ff4c696d3896f72186015ebd3ce61e3fdc5261b4d998b6ec64fdef349da`, 430504 bytes. These match the saved pre-first-kernel primary binding. The relevant actual `Integrable.mono'` source contract was also read in Mathlib/MeasureTheory/Function/L1Space/Integrable.lean, lines 104-106.

The local read-only library CI source has the same `87853bd1...` hash. Root v62 receipt SHA256 `921918687d9649bbbeda534ce9b9fd4901e5f34334bdeb6bf8ecbc0268673745` is PASS, pins that exact CI source, and explicitly checks code `3425d698ca49d38787597ba1f18f83aa781ddf0a`, tree `47e73e2fcbb28d894b4d4aa46a0f334636af1fc3`. This is distinct from the historical notice/main `0d096cf56be001f9ed84a76b74c9e6fa0bef66a8` and accepted `489d0249a0e498958859a2be88282dbba97c1899`, tree `3152c4d078580467007482cccd7ba439a19410d8`; those identities are not substituted for the checked source tree.

## Saved kernel, actual ownership and transitive axioms

Server run: `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22cz-20261023`; worktree `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`. Original author receipts specify CPU14-17, native Lean memory 8192 MiB, jobs 4, autoImplicit=false and the reused read-only accepted source view. The actual project pins remain `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`; read-only Git confirms the mathlib commit. The actual lakefile contains autoImplicit=false. Its known local-changes warning is retained, and exact consumed sources/objects are bound explicitly rather than inferred clean from Git alone.

| Original saved gate | Result | Log SHA256 | Bytes |
| --- | --- | --- | --- |
| Kernel attempt 01, source `d0b6ec4ecc2128c2213d55aca520424076f1a7f82ec9d61985c4068d43ac0119` | FAIL, inner exit 1, 5.663856204599142 s | `71794f9c6cccb6de54a065639f06cc181c60909de1eec369f1e7bc0d718f8d78` | 1808 |
| First successful kernel, attempt 02, final source `4fdc3834...` | PASS, inner exit 0, 5.366950947791338 s | `78b67ce7bdb15c41ab5792bff1840f5b81b1903453abe4302584729c23979314` | 489 |
| First whole-owner recursive axiom audit, final source | PASS, inner exit 0, 5.562557628378272 s | `2275f99702c8977140a9e0317b03750a19356944317eee5dc13e9ff24d09bbf6` | 1769 |

I read the complete original logs and inspected the JSON bridge's INNER exit codes, not only its outer process exit. Attempt 01 failed because rewriting the pointwise product norm did not syntactically match `|(weight * error) z|`. The ENTIRE source diff is one added line, `change ‖weight z * error z‖ ≤ c * envelope z`, before the existing norm/abs rewrites. It changes no theorem header, let value, domain, assumption or mathematical argument. The failed 102-line / 4791-byte source and log are preserved; attempt 02 is the first complete successful final source. Its complete log has only the known Lake warning and frozen hn unused-variable warning. The linter's suggested option text is diagnostic output, not an option present in the source.

The complete Audit.lean checks target theorem kind, enumerates EVERY environment constant and selects actual module ownership with `env.getModuleIdxFor?`, rather than relying on public names or a namespace prefix. It rejects owned axioms and applies `Lean.collectAxioms` recursively to EVERY owned constant, allowing only `propext`, `Classical.choice`, `Quot.sound`; it would print owned definition values. The complete saved output contains exactly one owned theorem, the complete actual type reproduced above, and exactly those three axioms. It reports `U22CZ_FROZEN_DEFINITIONS 0`, `U22CZ_FROZEN_THEOREMS 1`, `U22CZ_ALL_THEOREMS 1`, `U22CZ_ALL_DECLARATIONS 1`, `U22CZ_AXIOM_GATE PASS`. Consequently there are zero definitions, private/generated/external-namespace owned declarations or values omitted from coverage. The print-only options pp.deepTerms and pp.maxSteps do not weaken kernel checking.

The complete final source contains no sorry, admit, new axiom, unsafe, native_decide or implemented_by and no weakened proof settings. Its sole theorem has the standard-three transitive axiom set. The current own canonical object is SHA256 `85ba927b7074a9674e846d731425b80420ccf6c718e12cf83aa90b122b27bd68`, 175624 bytes. Its accepted-source-view symlink resolves to the saved audit environment's exact added-own-artifact worktree path with the same hash. This current-object observation is separate from the historical source-bound successful receipts and does not fabricate an earlier object hash.

The source-bound check parent `9c8680b44f12d634bd74d9251ec2f26caac921e8` and old branch name in the archived receipt are historical. Read-only current worktree observations give branch `feat/oq3-weighted-frequency-and-inversion`, HEAD `02095ebaab475791c10b052e2942731590fcc4cb`, tree `6dd80e9be2658f5b9227fd68f037225c34c27876`, the supplied frozen PR232 identity. CY and CZ canonical source files are still untracked there and therefore are not claimed to be included in that publication. Exact unchanged source/dependency/object evidence, rather than the branch name, is the basis for reusing the saved gates. This report makes no new publication, rebuild or integration claim.

## Scope and verdict

The eliminated obligation is the analytic passage from the explicitly supplied actual small-frequency Gaussian error bound to genuine ALL-natural-weight restricted Lebesgue integrability and its nonnegative integral bound with the explicit B/sqrt(n) factor and actual whole-plane Gaussian moment. This is a reusable modular integration theorem; the Gaussian integrability and comparison tools are attributed to the qualified CY184/CI168 and Mathlib interfaces, not claimed as a new root theorem or novel Gaussian result.

The canonical caller must derive herror from its actual CX183 estimate and original probability-law construction; assuming the desired original root estimate would not close that obligation. DA186 is a separate downstream unit and is not accepted by this report. Higher Edgeworth terms, remaining frequency regions, inversion, exterior estimates, new-rho Laplace and original B/D remain OPEN here. Strict 0<beta<2/5, p54 repairs and external-result attribution are not weakened or overwritten. Existing historical A/root closures are not re-reviewed or enlarged.

Final independent verdict: CORRECT for the complete exact 103-line CZ185 source SHA256 `4fdc3834b387aec486ce31df8808d4c3758afcbb93cf9c92b7b48191e2b4776c`, its complete frozen statement, all four statement-let values, all proof-local values and types, complete proof and sole actual owner. The saved exact-source server kernel and whole-owned transitive-axiom evidence are verified and reusable with this qualified independent review. No critical gap remains in this unit. Review complete; after reporting this file's hash/line count, this reviewer performs no further writes or continuation task.
