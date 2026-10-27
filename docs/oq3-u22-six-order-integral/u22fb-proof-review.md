# FB239 independent complete final source, statement, proof and evidence review

STATUS: CORRECT

JUSTIFICATION: The entire exact FB239 implementation proves the unchanged frozen generic majorization statement. It derives genuine whole-plane Lebesgue integrability of the Gaussian envelope and restricted integrability of the actual weighted norm error, then obtains the nonnegative integral and the stated bound. Every quantifier and all three statement lets match the exported actual type. The saved native002 and same-first-object all-owned transitive-axiom evidence pass for these exact bytes. Qualified CY184 reuse is acceptable with its legacy object-hash limitation stated honestly below. No original OQ3 root theorem or canonical consumer is certified by this report.

Reviewer: fresh independent non-author context `oq3_fb239_final_review`; model `gpt-6.1-sol`, reasoning effort `xhigh`, as assigned. I used math-theorem, not math-ultra. This is the separate final verification context, not the proof author. My only write is this report. I ran no Lean, axiom check, server command, upload, Git operation, publication, child delegation or cross-chat message, and changed no source, statement, dependency, receipt, ownership or shared implementation.

The current explicit OQ3 resumption in `coordination/resource-reallocation-20261027/OQ3-RESUMPTION-PHASE-40.json` supersedes historical OQ3 pause entries. The applicable source-fidelity, author/reviewer separation, server-only checking, accepted-evidence reuse and restricted write rules remain in force. This review uses the existing saved server results; it does not claim a new execution or a replay of any accepted check.

## Complete reading and exact identity

I read the entire 20-LF frozen declaration before the entire 84-LF final source. I then read the complete 21-LF actual-type export, entire 23-LF unit scope, entire 81-LF failed source, and complete receipt, audit record, build history, 47-LF audit source, qualified-dependency binding, server-dependency binding and own-first-object view binding. I compared the failed and final proof text, checked the frozen statement as an exact source substring, and checked the byte hashes, UTF-8 validity, lack of BOM and zero CR count of the mathematical inputs. All advertised hashes matched.

| Artifact under drafts/oq3 | SHA256 | Bytes / LF / CR |
|---|---|---|
| u22fb-frozen-declaration.lean.txt | `3dea06692ca7fc4e434979486c51d44728cbdf139ea92dd742b46fe76284d9c0` | 1161 / 20 / 0 |
| u22fb-source.lean | `dde1d75d0f69740c12e208af3cd47ac289cfe44909eccc1a1c56e6624b915dd4` | 3892 / 84 / 0 |
| u22fb-actual-types.txt | `153e94a51ac637d1f4682e95bccf36c369c6ddd1b6b1b76c49bb88ed4d8ebd46` | 1230 / 21 / 0 |
| two-hundred-thirty-ninth-unit-scope.md | `688a3bcfa27780d3dca6fae2f5d99a27f98b67d786f6034931a4c4b9b2f7e39e` | 1478 / 23 / 0 |
| u22fb-attempt01-source.lean | `dc831d85db79f4f2a3dad84596e3f09edb5e6177a1a64a33bd8d9c7c4f5b2bd9` | 3856 / 81 / 0 |
| u22fb-Audit.lean | `bbcb5f8a69be9996080c8625f4ddb68618c0cd281029e91bb3222fd802b30334` | 2029 / 47 / 0 |
| u22fb-receipt.json | `c55e11399c1129e0a7f85816024723c2f626e13038c1a14c56bf6e029be51d92` | 7919 / 267 / 0 |
| u22fb-audit-record.json | `84e0bdcc2f9d3eeb2224479fea5e58d3505f456358144ae86ca628770a7731d7` | 3043 / 103 / 0 |
| u22fb-build-history.json | `136ef781393abbef080a843ed7b08eaa4697d26285760a5e5ec595c447457c00` | 4530 / 164 / 0 |
| u22fb-qualified-dependency-binding.json | `dc0f5aa816bc15322b36bd6a2728672cf9c657055b69d405dedcdfad3ab2e12a` | 1282 / 27 / 0 |
| u22fb-server-dependency-binding.json | `4f14ba0f4fad074a3a5349978bfda3fa8b813552e09d2ca86ff8d6b3de8d7b22` | 870 / 16 / 0 |
| u22fb-own-firstO-view-binding.json | `26087104974262c4e9ff5fec666e93616c5cdc56b34a10302716bf9450bc02ec` | 579 / 10 / 0 |

I also read original `C:/game/shao/current/oq3/proofs/r2/report.md` lines 1-158 and its terminal scope, the entire `proofs/r2/repair01.md`, and the entire `C:/game/shao/current/oq3/verdict.md`. The verdict is at the OQ3 directory root, not in `proofs/r2`; I located and read the actual file. I read the pinned local `library/lean-toolchain` as `leanprover/lean4:v4.36.0-rc1`; the project/server pin is mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. No local toolchain was installed, probed by execution or used to compile.

## Frozen statement, all three lets and the sole actual type

The sole public theorem is `Shao.OQ3.complex_gaussian_damped_local_weighted_integral_bound`. It quantifies an arbitrary continuous complex function on the real plane, every natural `n`, every real `delta` and `C`, the explicit hypothesis `0 <= C`, the displayed pointwise bound on the closed window, and every natural weight exponent `k`. There is no implicit positive-n, positive-delta, nonzero-frequency, probability-law, independence, integrability or moment hypothesis.

Write `r(z) = sqrt(z.1^2 + z.2^2)` and `c = C / ((n:Real)^3 * sqrt(n:Real))`. The three statement lets are completely reviewed:

1. `small = {z | r(z) <= delta * sqrt(n)}` is the exact closed Euclidean-radius window, with no deleted origin and no replacement by a product max norm.
2. `weight z = r(z)^k` is the specified natural radial weight on every point of the plane.
3. `envelope z = (r(z)^(k+9) + r(z)^(k+56)) * exp(-(z.1^2+z.2^2)/8)` is the specified real nonnegative envelope on the whole plane. The powers and Gaussian coefficient are unchanged.

The four conclusions, in order, are whole-plane `Integrable envelope`, `IntegrableOn (weight * norm(f)) small`, nonnegativity of the restricted real integral, and its upper bound by `c` times the whole-plane envelope integral. Both integrability propositions and both integrals use ordinary Lebesgue volume on `Real x Real`; they are not probability expectations, truncated envelopes, extended-real integrals or finite formal sums.

I read every line of the actual export. It contains exactly one `DECL`, one `TYPE`, one theorem kind and zero `VALUE` blocks. The export preserves the full quantifier order, continuity, `hC`, entire pointwise premise, all three lets, all four conjuncts and Lebesgue volume. The pretty-printed `have small/weight/envelope` are the elaborated lets, not extra premises. No generated definition, private auxiliary declaration, additional owner or omitted value appears in the complete source/export/receipt inventory.

## Complete proof review

Source lines 30-32 introduce the three fixed lets and `c`. Since the cast of a natural, its cube, and its square root are nonnegative, and `C` is nonnegative, `c >= 0` follows by nonnegative division. This requires no assertion that the denominator is nonzero.

Lines 33-42 instantiate the qualified CY184 theorem `integrable_euclidean_radius_power_gaussian` at each natural `j` and coefficient `a = 1/8`, satisfying its sole coefficient condition `a > 0`. The exponential argument equality is exactly `-(1/8)*S = -S/8`, with `S = z.1^2+z.2^2`, proved by ring normalization. Thus the proof obtains integrability of `r^j exp(-S/8)` on the whole real plane for every required power, without assuming the desired finite integral.

Lines 43-47 add the two integrable functions for `j = k+9` and `j = k+56`. `Integrable.congr` then transfers their integrability to `envelope` using an everywhere pointwise identity, hence also an almost-everywhere identity: `r^(k+9)*exp(-S/8) + r^(k+56)*exp(-S/8) = (r^(k+9)+r^(k+56))*exp(-S/8)`. The explicit `filter_upwards`, unfolding and `ring` prove this exact distributive equality. This is a valid integrability transfer, not a weakened equality, dropped term or new premise.

Lines 48-53 establish integrability of the whole-plane dominator `c * envelope`, continuity of the weight, measurability of the closed window, and pointwise nonnegativity of the weighted norm error. The closed-window measurability follows from continuity of the Euclidean radius and the constant right side. Continuity of the weighted norm error follows from `Continuous weight` and `Continuous f` followed by continuity of the complex norm. Every natural power of the nonnegative radius is nonnegative.

Lines 54-67 multiply the exact `herror z hz` by `r(z)^k >= 0`. The rearrangement is precisely

`r^k * (c * (r^9 + r^56) * exp(-S/8)) = c * (r^(k+9) + r^(k+56)) * exp(-S/8)`.

Natural `pow_add` and commutative ring algebra justify this at every radius, including zero. No division, logarithm, inverse power, cancellation of the error or replacement by an asymptotic comparison occurs. This proves the bound for the actual integrand at each point in `small`.

Lines 68-73 derive `IntegrableOn` by domination. The dominator is already integrable on the whole plane and thus on the restricted measure; the actual error integrand is strongly measurable there by the continuous product. `ae_restrict_mem hsmall` supplies membership almost everywhere for exactly the restricted volume measure. Because the weighted error is nonnegative, its real norm equals itself, so the norm domination required by `Integrable.mono'` is exactly the previously proved `hbound`. No input integrability of `f`, its norm or the weighted error is assumed.

Lines 74-81 assemble the integrability conjuncts and integral nonnegativity, then use the two legitimate ordinary Bochner-integral comparisons. First, both restricted functions are integrable, the set is measurable and `hbound` holds on it, so `setIntegral_mono_on` gives the restricted comparison. Second, `c * envelope` is globally nonnegative because `c >= 0`, the radius powers are nonnegative, and the exponential is positive; `setIntegral_le_integral` therefore bounds the restricted dominator integral by its full-plane integral. Finally `integral_const_mul` pulls out the same real coefficient `c`. All ordinary integrals are backed by the previously established integrability facts, so the result cannot exploit the convention for nonintegrable Bochner integrals.

This covers every proof line through both namespace/section closures. The final source contains no `sorry`, `admit`, added `axiom`, `unsafe`, `native_decide`, hidden execution command, alternative statement or extra mathematical assumption. The mathematical proof is complete for its frozen generic helper scope.

## Quantifiers, signs and degenerate cases

- `n = 0`: Real division by zero is total and makes `c = 0`. The window is `r <= 0`, regardless of `delta`. The explicit `herror` forces `norm(f(0,0)) <= 0`, hence `f(0,0) = 0`; no missing denominator-positivity premise is used. The derivation remains valid. This algebraic extension does not claim that an actual Edgeworth error at `n = 0` satisfies the premise.
- `n >= 1` and `delta < 0`: the right side of the radius test is negative, so the window is empty. Restricted integrability and zero integral are consistent with the proof; whole-plane envelope integrability is independent of the window. For `delta = 0`, the window is the origin, whose pointwise obligation is retained.
- `C = 0`: the bound forces the error to vanish on the window; the right side of the conclusion is zero. For arbitrary `C >= 0`, the proof uses only its nonnegativity. No strict positivity is hidden.
- `k = 0` and the origin: natural zero powers and `pow_add` retain their Lean meanings, including `r^0 = 1`. Both envelope exponents remain positive (`9` and `56` when `k = 0`), so the origin is compatible with the premise. No `0^0` simplification or positive-frequency exception is needed.
- Every finite real `delta`, every natural `n` and `k`, and every continuous complex `f` satisfying the exact window bound are covered. There is no finite cutoff in `k`, eventual-n replacement, strict-window substitution, omitted boundary or almost-everywhere weakening of the pointwise input. No claim of a uniform constant across varying functions/laws is introduced beyond the supplied `C`.

## Qualified CY184 interface reuse and honest legacy provenance

I read all four complete public source headers of CY184, not just the consumed name, and the entire 21-LF actual-type export. These are the nonnegative power estimate, one-dimensional even-power Gaussian integrability, one-dimensional `(1+x^2)^k` Gaussian integrability, and whole-plane Euclidean-radius-power Gaussian integrability. There are four actual theorem types, zero values and zero statement lets. The consumed final theorem has exactly the required domain `Real x Real`, Lebesgue volume, every natural exponent, and any strictly positive Gaussian coefficient. In particular it supplies genuine whole-plane integrability at `1/8`; it does not supply a truncated bound or assume the integral finite.

I read the entire CY receipt and audit-environment record, and selected the CY184 row from `publication-u22-cy-df/docs/oq3-u22-weighted-gaussian-window/manifest.json`. Its verified manifest hash is `2be2c6f747a30630ecfd5578dbc2d59fc5ce0e0de65da563ae9d81e708108f90`. The row records four public/actual theorems, zero generated theorems/definitions, and parent complete reading of the qualified prior proof review and actual types. The accepted old proof itself is not re-reviewed here and no old kernel/axiom check is replayed.

The exact reused CY bindings are:

| CY artifact | SHA256 | Coverage/binding |
|---|---|---|
| u22cy-source.lean | `95aa9d280eb607c46768688ae6adcd758205f9cbf00d8891277e98d50145bbeb` | 3812 bytes, 86 LF; all four public headers read |
| u22cy-actual-types.txt | `1c9ab44cd8b155bd4ac3d9aa1b1cee392486041bcfb643ecdc1db357b681046e` | 974 bytes, entire 21 LF; four TYPE, zero VALUE |
| u22cy-receipt.json | `074cd2b02b835b11067741febff705cbe527ed49d1b248afa57399ed8af8a38e` | Entire legacy receipt read |
| u22cy-audit-environment.json | `b2f8d3aa434005c5f675f1c931b14765eb92454bb02919c819aa1c6e279bff62` | Entire original environment/path record read |
| qualified u22cy-proof-review.md | `c6e2b660894524e59bd5526b4aefe98b95c854bad14ca16ba66e6838a469ad12` | Verified 135-LF accepted report, CORRECT; existing complete review reused |

The legacy CY receipt does not archive an SHA256 of its own original object. I do not infer that an unrecorded old hash was known or cryptographically preserved. It does record exact qualified source, first native001 success in 4.882227826863527 seconds at `2026-10-23T22:21:55.372243+00:00`, same-source original-module all-owned axiom success, and the audit environment's original own-object path. These are distinct from a newly observed object digest.

The FB server-dependency binding explicitly identifies the currently retained CY object as `36c2389b115b169053ff1062ff3382405677eac5a34060bff352650b4ee6ac5e`, 274320 bytes, at the recorded original worktree path. Its recorded mtime is `2026-10-23T22:21:54.967027+00:00`, consistent with completion of the first legacy native attempt. The existing accepted-source view target is unchanged, with zero old-entry changes, new CY links or cache writes. The timestamp is corroborating provenance, not a substitute for a historical object hash. This is a new recorded read-only observation, not a retroactive amendment to the old receipt. I reviewed the saved observation; I did not observe or hash the server object myself.

This is acceptable exact qualified legacy reuse: unchanged source/header/type hashes and the existing qualified complete review/native/all-owner evidence are retained, and the new FB kernel plus recursive axiom audit use the view bound to the current retained CY object. It does not warrant claiming a stronger historical cryptographic object chain than was actually archived. No old receipt is rewritten, old producer recompiled, old axiom success replayed, shared cache mutated or dependency theorem strengthened. The interface consumed by FB has no new law-level hypothesis or missing mathematical side condition.

## New exact-source kernel, ownership and transitive axioms

The entire saved FB receipt, audit record and standalone build history agree on the final source, frozen declaration, scope, actual types and first original object. The standalone build history equals the receipt's build-history array. The original first successful FB object is SHA256 `996c6fdeb24bd466f53e5cb0b025742d4005c5e72226366de72886be6c560613`, 203264 bytes. The own-first-object view binding points to that own worktree object; it adds one new own link with zero old-entry changes, binary copies or shared-cache writes.

Native002 on the final 3892-byte source ended RC0 in 5.415031252428889 seconds at `2026-10-27T17:33:25.432657+00:00`; its log is 133 bytes, SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`. The same-original-object audit ended RC0 in 5.6153032053261995 seconds, recorded at `2026-10-27T17:33:40.258237+00:00`; its log is 1482 bytes, SHA256 `91e3198151354039be3ef1724daa869cedac0dc339fe078dc2ff50106899000f`. These are saved author-side server receipts reviewed here, not new reviewer executions. The assigned context records only the known shared Lake package-dirty warning, with no additional source/style warning. I did not fetch raw remote logs.

The audit imports the exact FB module and enumerates actual environment constants by module ownership. It checks that the frozen target exists as a theorem, rejects any owned axiom, recursively collects axioms for every owned declaration and rejects anything outside `propext`, `Classical.choice`, `Quot.sound`. It exports every owned type and every definition value, checks nonempty ownership and the frozen theorem count, and records the actual counts. The actual export and records identify one owner, one theorem, one TYPE, zero non-theorem values, and no unreviewed generated owner. The complete transitive axiom union is exactly the standard whitelist; no new project axiom or bypass is present.

The saved executions use phase `ROOT_OQ56_OQ3_40`, OQ3 CPUs 36-39/44-47 and native `-M8192 -j4`. The memory payload retains its historical phase39 helper label while recording the explicitly current phase40 resource allowance and unchanged helper hash. This is consistent with the phase40 contract, not evidence of an unauthorized old lane activation. Memory records preserve 140-GiB project process budget, 180-GiB aggregate guard, 200-GiB hard limit and 60-GiB other/system reserve, with no cache mutation or active-file/slab discount and no OOM event. This review starts no execution and makes no resource-state claim beyond the saved evidence.

## Failed attempt and exact repair provenance

Native001 on the archived 3856-byte/81-LF source ended RC1 in 5.3450862523168325 seconds at `2026-10-27T17:32:26.604750+00:00`; its saved 1081-byte log hash is `bdad8a7e78510d2cb96d2dfe28953aebebfb292f9f395c82efee51c87a658f42`. It is retained as a failure, not counted as a pass, uncertain request or successful replay.

An exact text comparison verifies that the only final-source difference replaces the former `simpa only [envelope, add_mul] using (hpow ...).add ...` at the envelope-integrability step by the explicit `Integrable.congr` / `filter_upwards` / `dsimp` / `ring` normalization in lines 44-47. All remaining source text, including the entire frozen statement, is unchanged. This is a proof elaboration repair of the same distributive identity, with no altered assumption, quantifier, integral, exponent, bound or imported module. Native002 is the first success of the repaired exact source. Its successful producer and successful axiom audit are not replayed in this review.

## Original-source fidelity and acceptance limit

FB239 is a generic local Gaussian-majorization helper. Its continuity and pointwise estimate are explicit premises appropriate to that helper. Acceptance does not promote them to assumptions of the original OQ3 law. An actual canonical consumer must separately derive continuity and this exact pointwise error bound for the same actual characteristic function, true cumulants/Pn, E/IID-rho witness and window. The existence or reported first-native success of another consumer is outside this review; I read no other consumer implementation and certify none of it.

The original report/repair/verdict require the strict weak-Cramer range `0 < beta < 2/5`, preserve the jointly nonlattice counterexample, and attribute the uniform-in-law Edgeworth input to Song with order `s = 8`. The repair also keeps the explicit far-field localization requirement and the exact boundary Laplace constant. FB239 changes none of those conditions or the p54 repairs, proves no endpoint extension, and supplies no replacement for the attributed external result. The terminal report's positive result is one sufficient quantitative repair, not a characterization of minimal hypotheses or certified historical priority.

The new result closes only the frozen integrability/weighted local-integral majorization obligation. It does not close whole-frequency control, the middle/far-frequency estimates, Fourier inversion, the exterior probability, all original B-D dependencies, a root OQ3 theorem, or any C1/C2/OQ4/OQ56 root group. Original counterexample evidence, p54 repairs and external-result attribution remain preserved. Correctness of this standard domination helper is separate from novelty or publication priority; no new novelty claim is accepted.

No mathematical repair or additional proof check is needed for this exact FB239 helper on the supplied qualified evidence. Parent must read this entire report before qualifying these exact bytes; a mathematical source/interface change or a concrete evidence gap would require only the affected new review/check. The current report does not authorize publication or other writes.

## Usage and sole-authority release

Model: `gpt-6.1-sol`. Reasoning effort: `xhigh`. Fresh final-review context with author/reviewer separation. Runtime token telemetry is unavailable to this context: input_tokens = null; cached_input_tokens = null; output_tokens = null; reasoning_subset_tokens = null. These nulls mean unavailable, not zero. No purchased-credit or exact subscription-percentage allocation is inferred.

Run state after writing this report: `COMPLETED_STOPPED`. Sole write authority for `drafts/oq3/u22fb-proof-review.md` is released. Writer processes = 0; Lean/axiom/heavy commands = 0; delegated children = 0; inflight = 0; pending = 0; uncertain writes = 0. This final review is complete and does not continue in the background.
