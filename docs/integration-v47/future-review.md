# Actual future/noise Fourier product — independent complete review

STATUS: **CORRECT**

Reviewer `/root/common_future_review`, fresh `gpt-6.1-sol` / `xhigh`, independent of `/root/common_highfreq_author`. No source, draft, package, object or shared-state edits; no Lean/audit execution; no delegated contexts. Only this report and its companion JSON are reviewer-owned.

## Exact version and evidence

- Author commit `a0f11f97f6fc0dc0145d2366d8c6dc4568dd4128`, parent `22a68e78abc981e898f823bef7f019efa3731504`; independently observed server HEAD equals this commit and the tracked worktree is clean. Its sole changed path is the added `Shao/Probability/SourceFutureNoiseFourier.lean`.
- Complete source: 258 lines / 11796 bytes, SHA256 `4ddfbc6be3917fb60f441156158babb9cbbfd939d19b9604039cd0b281454807`. The server working source, Git author blob and completely read local draft have identical bytes.
- Target object: 412856 bytes, SHA256 `284987012197dc7db3c5abd55d4ff6441d737b1de07b7612a08bf4f806f11fd2`.
- The four public declarations exactly match the candidate frozen by `coordination/public-future-noise-declaration-freeze.md` (freeze SHA256 `75d4d67627bbeeb4d08e04b0d8bb538791e29e3187123a65c659cf30508e8891`); candidate SHA256 `727d51ec39a93b31288b65c5f174cf196bc402dcafbf1494c6fa1981bca1c415`. Its earlier CANDIDATE_ONLY banner is superseded by the explicit coordinator freeze.
- Reused author targeted compile `future-targeted-06.log`, exit 0; SHA256 `05767ebe787071692167a8ffd2b171b974a5e0792742fdaa18fe378f9e2a32a1`. Full log read: package-overlay and style warnings only.
- Reused complete module-ownership/transitive-axiom gate: 20 constants = 15 theorems + 5 definitions, including private/generated declarations; exactly 2 public definitions + 2 public theorems. Every transitive axiom list is exactly within `propext`, `Classical.choice`, `Quot.sound`. Audit script, JSON and log fully read and hash checked; source banned-token scan empty.
- Complete actual-type/definition-value log: 29567 bytes, SHA256 `31fc7ba4272e3b5527ff1c76c0af69c026996057204263067c497e6b2f1b1761`. All 20 actual types and all 5 actual definition values read without truncation; exported names equal audited names, and definition-value names equal audited definitions. In particular, no hidden factorization or integrability premise appears.
- Toolchain `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. Existing checks used server CPU10–13, root-heavy lock and `-M8192 -j4 -DautoImplicit=false`; reviewer only read and hashed evidence.

Server evidence directory: `/root/rivermind-data/shao-lean-20261021/outputs/common-centered-characteristic-v44/`. Full paths/hashes and per-declaration coverage are in the companion JSON. No full logs were copied into the local workspace.

## Source fidelity and mathematical reasoning

Original `main.tex` 578–586 defines the future operator by independent future sums and actual square sums; 613–620 defines smoothing by **positive** `(Z,Y)` shifts of `H_y(w,q)=chi(q)1{|w|<y sqrt(q)}`. Original `supplement.tex` 2343–2353 fixes the **negative unit-frequency** Fourier phase and the exact identity `fhat = Hhat * Xi * phi^m`. Complete required excerpts were read. Source hashes are respectively `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` and `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

The actual definition integrates `sourceFourierTest` first over `quadraticFullNoiseLaw nu`, then over the canonical iid path law `Measure.pi (fun _ : Fin m => nu)`. Its two coordinates are exactly `p.1 + prefixSum a m + z.1` and `p.2 + energy a + z.2`. `Path m = Fin m → Real`; the full prefix is the sum of all coordinates, and energy is the uncentered sum of their squares. No variance substitution or centered quadratic statistic occurs. The transform is the actual complex Lebesgue integral on `Real × Real`, with phase `exp(-i(u p.1+v p.2))`, not a supplied transform.

`shifted_joint_integrable` proves product-measure absolute integrability before Fubini. Its integrand is measurably composed from the actual test and shift. Every spatial section is integrable by translation invariance of genuine two-dimensional Lebesgue measure. The section's integral norm is the fixed finite L1 norm of the actual test, so it is integrable over a probability law. `kernel_eq_joint` separately pays its pointwise product-integral rewrite using the test's measurable bound by one and the finite product probability law. The public L1 theorem takes the spatial marginal of the joint-integrable function.

For the transform, the complex phase is measurable with norm one. Thus `averaged_transform` obtains actual joint absolute integrability of `J(omega,p)=H_y(p+b omega) exp(-i frequency(p))`, moves the real-to-complex inclusion through the inner integral, and applies the two orders of Fubini to this integrable J. The translation calculation is pointwise: `frequency(p+b)=frequency(p)+frequency(b)`, hence `H_y(p+b) exp(-i frequency(p)) = exp(+i frequency(b)) [H_y(p+b) exp(-i frequency(p+b))]`. Translation invariance gives the actual `Hhat`, with the required **positive** characteristic phase of the shift.

The shift is exactly the sum of independent actual path/noise coordinates. Coordinate evaluation under the canonical product law has distribution nu and is independent across `Fin m`; accepted `iid_quadraticChar_factor` therefore gives the actual `quadraticChar nu u v ^ m`. Splitting the shift phase on the path/noise product law gives the integral defining actual `quadraticFullNoiseChar`; commutative reassociation yields precisely `Hhat * Xi * phi^m`. There is no factorization hypothesis.

Both public theorems consume the frozen `nu` probability, third absolute moment integrability, strictly positive actual variance, `h>0` and almost-everywhere support `|a|≤h` through accepted `quadraticFullNoise_law_data` to establish probability of the actual full-noise law. They need no `gamma≤2h`, mean-zero assumption or centered energy. The source's subsequent `T≤4/3` is not needed for this identity.

The accepted kernel source is unchanged at SHA256 `151fe42cda5414873ea9c9ea3359d256e971132073ea9d1c714ea0105af234d3`, independently CORRECT in `common-kernel-review` and accepted in receipt-v46. The prior centered-characteristic and power sources are unchanged at their receipt hashes. Existing accepted proofs were not re-reviewed; the actual needed definitions and theorem interfaces of the test, full-noise law, quadratic characteristic and finite path were read and matched to server source hashes. Relevant pinned mathlib translation, product-integrability/Fubini, product characteristic, coordinate independence and real-to-complex integration interfaces were checked against exact pinned Git blobs. The package-overlay warning does not indicate a changed relevant library source.

## Complete declaration coverage

Every row is CORRECT; names below omit the common private prefix where appropriate. Full actual types and definition values, not just source signatures, were checked.

| Declaration | Lines | Review and scope |
|---|---:|---|
| `sourceFutureNoiseKernel` | 16–22 | Actual canonical iid / full-noise positive-shift average; no free kernel or assumed law. |
| `sourceFutureNoiseKernelTransform` | 24–27 | Actual spatial Lebesgue integral with negative unit-frequency phase; does not assert frequency-L1. |
| `test_measurable` | 29–38 | Open strict-event set from continuous absolute value / square root, measurable cutoff indicator. |
| `test_norm_le_one` | 40–46 | Both event branches, actual nonnegative cutoff bounded by one. |
| `pair_volume_rightInvariant` | 48–51 | Standard product Lebesgue measure is right-translation invariant. |
| `shifted_joint_integrable` | 53–72 | Measurability, every translated section L1, constant finite section-norm integral; supplies genuine Tonelli/Fubini precondition. |
| `futureShift` | 74–75 | Actual full prefix sum plus noise first coordinate; actual energy plus second coordinate. |
| `futureShift_measurable` | 77–79 | Finite actual coordinate sums/squares and projections are measurable. |
| `kernel_eq_joint` | 81–103 | Pointwise bounded integrability pays nested-to-product conversion; coordinate associativity only. |
| `sourceFutureNoiseKernel_integrable` | 105–118 | Frozen hypotheses pay actual noise probability; genuine joint L1 gives the real spatial kernel L1. |
| `frequency` | 120 | Exactly `u*p.1+v*p.2`, no scaling or shifted frequency. |
| `negativePhase` | 122–123 | Exactly `exp(-((t:Complex)*I))`. |
| `negativePhase.eq_1` | 122–123 | Generated defining equation, actual exported type has only t and the exact defining expression. |
| `negativePhase_norm` | 125–126 | Pure imaginary exponent has norm one for every real t. |
| `negativePhase_continuous` | 128–130 | Continuous phase, enabling measurable product integrand. |
| `positive_shift_transform` | 132–158 | Pointwise algebra and spatial translation give positive shift phase times actual Hhat. |
| `averaged_transform` | 160–189 | Complex joint L1 proved before both Fubini uses; cast and constant factors moved correctly. |
| `canonical_future_characteristic` | 191–209 | Actual iid coordinate laws and independence instantiate accepted factor theorem with real prefix/energy. |
| `joint_characteristic` | 211–235 | Product-law exponential splits; actual Xi integral times actual iid power. |
| `sourceFutureNoiseKernelTransform_factor` | 237–256 | Uses actual law probability, kernel equality, integrable averaging and joint characteristic; proves frozen exact product for all u,v. |

## Boundaries and remaining work

All natural `m` including zero, every `y≥0` including zero, and every real `u,v` are retained in actual types. `Fin 0` uses the empty iid product and `phi^0=1`; no nonempty-index assumption occurs. At `y=0` the strict event is empty. This proof introduces no division by u or v, so zero frequencies are covered directly; the previously accepted Hhat formula supplies its own u=0 branch. No interval-boundary or atom omission enters this unit.

Accepted scope is **real spatial kernel L1 integrability and the exact source-normalized Fourier product only**. The module does not prove L1 of the transform as a frequency function, Fourier inversion, inversion of derivatives, marked-norm/mark-sine estimates, boundary vanishing, frequency-region estimates, or any C1/C2 probability/root closure. Subsequent use of mathlib's `2*pi` normalization must explicitly rescale both frequencies and pay the two-dimensional `(2*pi)^(-2)` inverse normalization.

Critical gaps: none. Required fixes: none. The next independent source-bound obligation remains actual frequency integrability / inversion / marked-kernel estimates under a separately frozen interface. Review complete; reviewer has no source write authority or running Lean/audit/delegated process. Completion of this bounded review ends this review turn, without implying persistent execution.
