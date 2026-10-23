# Independent complete review: bounded quadratic tilt

STATUS: **CORRECT** for the complete new module `Shao.Probability.BoundedQuadraticTilt` at author commit `5e1a6a7fef2121bc0208798f7a0678975b44a0e9`. This is a source-to-statement and complete proof review, with verification and reuse of the original successful server kernel and all-owned transitive-axiom artifacts. It is not a closure of C1/C2 or any original open root.

Reviewer: fresh `/root/common_bounded_tilt_review`, prescribed `gpt-6.1-sol` / `xhigh`, independent of the production author. The author had released production write authority before this review. I changed no production source, assumptions, imports, producer objects, historical evidence, or shared ownership files. I ran no Lean command and no local build. No mathematical or evidence gap requiring another check was found.

## Exact version and immutable statement

- Branch: `feat/common-short-time-kernel`; server worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/common-short-kernel-v51`.
- Parent: `2da0aba7f23b43b901f7d229b714c8a14adf1e56`; tree: `3e2037854d2d86f72d82b5fe327205fb0167221a`. Read-only server Git inspection confirmed the frozen head, parent and tree and exactly one changed file: `Shao/Probability/BoundedQuadraticTilt.lean`.
- Entire 948-line source, local and server SHA256: `93c302d9de61bc4bf0cb238e82a4ed5b7f66e0ddbd2e833fec5bc6bbb25a8257`.
- Produced `.olean` SHA256: `cd1e326090a3fce3ecab7d8b38c14d7239c6b4fcedb600f8bb8dffb14d3dc2ec`.
- Candidate SHA256: `8cfbe112eff7822ae646f978b5eba52575e142fb81abf4e59798647861b3fcdd`; full source contract: `e47eb619c8f708668026c72d4084f29b77123865b85a704bbffd4f6acadb6927`; original root freeze: `e00bdbaecad07aca91057c733bca55535fe35af45ff90ef835eaa2b835d3628f`.
- Immutable syntax addendum 1: `d3369a262669ed926d1a8714a43081f223b2a37333159bf3f7be92ee0ffe2c6f`; corrective addendum v2: `f7fe987b34b8e20b62845147153b04c0bea60c06e123e27137056dad96a3558e`.

I read the entire candidate and contract, both addenda, the full new source and all proof bodies. An independent deterministic comparison of all three complete public heads, including every literal `let`, restores only `«λ» → λ` and `«hλ» → hλ`, then disregards whitespace. All three equal the original candidate exactly. No other token or mathematical change was accepted. In particular v2 supersedes the first addendum's incorrect claim that `hλ` required no quotation. The additional `ExpDeriv` import is permitted proof support. There are zero new global definitions.

| Complete public head | Literal lets | SHA256 of representation-normalized, nonwhitespace head after theorem name |
|---|---:|---|
| `boundedQuadraticTilt_density_moments` | 9 | `d3e59fa93e4e1330a9cfcf2e3d6419dac201ea272100bbd13b4ca694a546b69f` |
| `boundedEnergyTilt_drift_decay` | 13 | `6e217399624a3b91e8762afd5aa2bb74216da8bc03f4ccf431d605a62319f755` |
| `boundedQuadraticTilt_joint_moments_normalizer` | 13 | `6aced7ca58b9cb546b8976e6ca0bb6c714ac1757edc386abe59eea5a5885fb8a` |

The exact source is UTF-8, LF only, no BOM. Independent token inspection found no `sorry`, `admit`, new `axiom`, `unsafe` or `native_decide`.

## Source fidelity and consumed definitions

I read original `C:/game/shao/current/c12/supplement.tex` lines 2238–2300, 2700–2741 and 3551–3625. Its verified SHA256 is `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. The auxiliary proof really occurs in this supplement, rather than a separate auxiliary file.

The energy theorem covers the one-coordinate law, moments, mean shift and scalar normalizer decay in 2239–2279 and 2292–2298. The joint theorem supplies the generic actual-law statements underlying parts (a) and (b) of the source tilt lemma, 2718–2729 and 3551–3597. The general theorem supplies actual density/L1/variance comparisons used in those arguments. None assumes a centered or symmetric original law.

I read the consumed pinned Mathlib definition values and complete relevant API statements: `Measure.tilted` is exactly `withDensity (ofReal (exp(f)/∫exp(f)))`; `evariance` and `variance` use the actual mean; probability, mutual absolute continuity, arbitrary-function integrability and integral APIs have the genuine exponential-integrability guard where required. `taylor_mean_remainder_lagrange_iteratedDeriv` has `ContDiffOn ℝ (n+1)` on `uIcc`, a point in `uIoo`, and denominator `(n+1)!`. These match the actual uses. The cached package path resolves to the accepted `cache-overlays/shared-v34/packages/mathlib`, at commit `807d3836b165983210ee2ecf3cd28f239436949c`; toolchain is `leanprover/lean4:v4.36.0-rc1`. Exact source/object bindings for all four direct imports are in the JSON report. No old Shao theorem is imported by this new module, and no unchanged parent proof was re-reviewed or rechecked.

The source-parameter payments remain consumer work: with `y≥2` and `h>0`, from `N≥1/16`, `λ≥y/√N`, `yh≤1/4` and `s=0` or `λy/√N`, both `s≤λ²` and `sh≤λ` follow separately. Energy uses `s=κy²` and `sh_x²≤1`. These statements do not equate the energy case `b=0,s>0` with the joint case `λ=0`.

## Complete mathematical proof review

For the general theorem, the true phase is bounded by `±S`, where `S=|b|h+sh²`. Constant domination proves genuine exponential L1 before invoking the probability-tilt API; the actual normalizer lies in `[exp(-S),exp(S)]` and is positive. The normalized actual density lies in `[exp(-2S),exp(2S)]`. Both directions of L1 equivalence are valid for an arbitrary real function: bounded multiplication by `exp(f)` proves one direction, and multiplication of the integrable weighted function by the measurable bounded reciprocal `exp(-f)` proves the converse. No unstated measurability of the original test function is assumed. The integral identity is the actual tilted integral identity. Integrating density inequalities gives the claimed nonnegative-test-function comparison. Actual transferred AE support yields every natural signed/absolute moment, including power zero.

The square-shift identity is derived with finite first and second moments under each actual probability law: `∫(a-c)² = V+(μ-c)²`. For the variance lower bound use `c=μρ`; for the upper bound use `c=μ`. The discarded terms are nonnegative squares, giving the single density factors in the freeze. `Vρ=0 ↔ V=0` uses positivity of the exponential factors and variance nonnegativity, never division by variance.

For the energy theorem the phase interval is the sharper `[-S,0]`, so normalization gives density and variance/raw-moment comparison factors `exp(±S)`. Actual normalization and `∫(a-μ)=0` prove precisely the centered numerator identity. The integrability of each expanded numerator term is established before integration. The scalar bound `|exp(-t)-1|≤t` for `t≥0` bounds its absolute integral by `s(m3+|μ|m2)`. The private Lyapunov argument proves `sqrt(m2)*m2≤m3` from the pointwise nonnegative polynomial `( |a|-r )²(2|a|+r)`, with `r=sqrt(m2)`; variance nonnegativity gives `|μ|≤r`. Thus `|μ|m2≤m3`, including `m2=0`, and division by the positive `Z≥exp(-S)` pays exactly `2s exp(S)m3`. The bound for the new mean retains `|μ|`.

The centered-third helper proves integrability and `∫|a-μ|³≤8m3` using `|a-μ|³≤4(|a|³+|μ|³)` and `|μ|³≤m3`. Under the true changed law this gives exactly the frozen centered-third factor. The smallness guard is used where needed: `0≤sa²≤1` implies `exp(-sa²)≤1-sa²/2`. Integration proves the actual `Z≤1-sm2/2≤exp(-sm2/2)`. Positivity permits raising to every natural power, with the real cast in the exponent. The explicit `s=0` branch uses the true constant-tilt identity.

For the joint theorem the sign alternatives prove `|b|=λ`. The independent slope guard gives the true phase interval `[-2λh,λh]`. A symmetric enlargement to `[-2λh,2λh]` pays the frozen `exp(±4λh)` comparison; the sharper upper normalizer bound still uses the true interval. The mean numerator is exactly `μ+∫a(W-1)`, and `|exp(r)-1|≤exp(|r|)|r|` yields the stated `exp(4λh)(|μ|+λm2+sm3)` bound. The raw and centered third moments refer to the actual changed law. The gamma division is performed only after `V>0` and the variance lower bound imply `Vρ>0`; it first gives `exp(8λh)m3/V`, then the frozen, looser `Γ=8 exp(8λh)m3/V`.

The normalizer proof computes genuine first, second and third derivatives of `F(a)=exp(ba-sa²)`. For the Lagrange point between `0` and either sign of `a`, `|t|≤h`, `|b-2st|≤3λ` and `s≤λ²` give `|(b-2st)³-6s(b-2st)|≤45λ³`; also `F(t)≤exp(λh)`. Global smoothness supplies the full Taylor hypothesis. The derivative-within conversion has unique differentiability on the nondegenerate `uIcc`; the `a=0` branch is separate. The degree-two polynomial is exactly `1+ba+(λ²/2-s)a²`. The actual Lagrange denominator is `3!=6`, so `45/6≤24` pays the frozen coefficient without any sign restriction on `a` or on `λ²/2-s`. The remainder and its dominating raw third power are integrable before integration. `log Z≤Z-1` is used only after `Z>0`, preserving the signed `bμ` and full quadratic coefficient. Finally `λ=0` forces `s=0` from the explicitly frozen square guard and forces `b=0` from the sign alternatives, so the actual law and normalizer become `ν` and `1`.

Degenerate, atomic and biased laws are covered. No variance denominator is used in the zero-variance comparisons. The quotient conclusion has its explicit positive-variance implication; the literal real `Γ` outside that implication has no asserted statistical meaning. The formulas are consistent for `m3=0`, `s=0`, `λ=0`, atoms at nonzero points and nonsymmetric laws. There is no hidden `λh≤1` assumption.

## Declaration-by-declaration coverage

Every proof body and every actual printed type listed below was read completely. The JSON report binds each of all 35 actual owned constants to its exact type hash, original log line interval and recursive axiom list.

| Source theorem | Reviewed proof obligation |
|---|---|
| private `bqt_integrable` | AE constant domination with actual measurability |
| private `bqt_powers` | signed/absolute natural powers and moment upper bound |
| private `bqt_mean_bound` | norm of integral and first absolute moment |
| private `bqt_var_formula` | genuine L2 input to actual variance subtraction formula |
| private `bqt_square_shift` | complete finite-integral expansion around arbitrary center |
| private `bqt_general` | actual tilt, L1 equivalence, support, all moments and variance comparison |
| private `bqt_lyapunov` | nonnegative-polynomial moment inequalities, including zero moments |
| private `bqt_centered_third` | actual centered-third integrability and factor 8 |
| public `boundedQuadraticTilt_density_moments` | literal quadratic phase bound and full general bundle |
| private `bqt_exp_neg` | exponential difference bound on the nonnegative half-line |
| private `bqt_exp_neg_half` | scalar decay on the entire closed interval `[0,1]` |
| private `bqt_abs_integral` | domination of actual absolute integral |
| private `bqt_mean_tilt` | literal tilted-mean normalization identity |
| public `boundedEnergyTilt_drift_decay` | all frozen energy conclusions, identity, drift and powers |
| private `bqt_derivatives` | all three actual iterated-derivative function equalities |
| private `bqt_taylor` | both signs of the argument, all guards, exact degree-two remainder |
| private `bqt_exp_abs` | exponential difference bound for both signs of its argument |
| public `boundedQuadraticTilt_joint_moments_normalizer` | all joint moments, gamma, signed Taylor/log and zero branches |

The remaining 17 actual constants were also read in full: private `bqt_general._proof_1_1`, public joint bundle `._proof_1_8`, energy bundle `._simp_1_1` through `._simp_1_8`, and joint bundle `._simp_1_1` through `._simp_1_7`. Their actual types are numeral/nonzero and natural/integer power simplification facts, the natural-cast successor nonzero fact, and the exponential natural-power identity. They contain no additional assumptions for a public theorem and no new definition values. This accounts for exactly 15 named private helpers, 3 public theorems and 17 generated theorem constants: 35 actual owned theorems, zero definitions of any visibility.

## Original execution and recursive axiom evidence

I inspected the original request and return files, full original successful target log, original direct-exit artifacts, audit source, all 35 `TARGET_DECL` / `ACTUAL_TYPE` blocks and their complete recursive `AXIOMS` arrays, plus the three public `#print axioms` results. The owner selector uses the environment's actual defining module and iterates all constants, including private/generated ones; `Lean.collectAxioms` is applied to every selected constant and rejects anything outside `propext`, `Classical.choice`, `Quot.sound`. Its 35 rows and zero definition values match the actual source and log, rather than a descriptive declaration count.

Original successful target command, after activation and worktree selection:

```sh
flock /root/rivermind-data/shao-lean-20261021/locks/root-heavy.lock taskset -c 10-13 lake env lean -M8192 -j4 -o .lake/build/lib/lean/Shao/Probability/BoundedQuadraticTilt.olean Shao/Probability/BoundedQuadraticTilt.lean > /root/rivermind-data/shao-lean-20261021/outputs/common-bounded-quadratic-tilt/check10.log 2>&1
rc=$?
```

Original audit command:

```sh
flock /root/rivermind-data/shao-lean-20261021/locks/root-heavy.lock taskset -c 10-13 lake env lean -M8192 -j4 -DautoImplicit=false /root/rivermind-data/shao-lean-20261021/outputs/common-bounded-quadratic-tilt/OwnedAudit.lean > /root/rivermind-data/shao-lean-20261021/outputs/common-bounded-quadratic-tilt/actual-owned-types-values-and-axioms.log 2>&1
rc=$?
```

Both immediately captured **direct Lean exit 0**. The target source and project options both specify `autoImplicit=false`. The target return records `error_count 0`; its full log contains warnings only. The audit return also records direct exit 0. Check09's parser failure and earlier development failures remain preserved; they are not substituted for the successful exact-source gate. No successful check was replayed.

All paths in this table are under server `outputs/common-bounded-quadratic-tilt/` and were independently hashed read-only:

| Original artifact | SHA256 |
|---|---|
| `check10-request.json` | `32432cd6423b7c07cf96bb874b4f410b53caf26b786ba33700c866cb489452e7` |
| `check10-return.json` | `b8d4b7e822b15354528301cf40bf7e5115142df6bac20729e03f9c534bd230f9` |
| `check10-exit.json` | `2c298bd92312340300f7865ea744930679b403cdcd04c33940d6fee02a606817` |
| `check10-source.sha256` | `6a9486b4b9389c07015c09446dc7b9666b2ad37bcacbb483bc84b6f00b506a80` |
| `check10.log` | `3e5dcb00e91a342f14f587fd6ccc6c6757c481ffc707d0fd23395199404fd4b7` |
| `audit-request.json` | `de06e634e3041a0be678c7efeca519bee5d99b2925ee90a4ec1664117f79dff4` |
| `audit-return.json` | `c43fea308e9463275ad744eb9adb6c3a0cf1d595d493f661a66dce03b46c036e` |
| `audit-exit.json` | `2c298bd92312340300f7865ea744930679b403cdcd04c33940d6fee02a606817` |
| `OwnedAudit.lean` | `02eab17c77566b12ad8af94ef59eea0b097a6554d3710a87d91038480890233b` |
| `actual-owned-types-values-and-axioms.log` | `573a0aee7068dd146147188e125250b37024f7c026d373663b432cca48a1af5b` |
| `owned-audit.json` | `83b919065e5740dff68d8d5b422ebd397bb81ff843d83daf218eaeb0dcefb797` |
| `author-receipt.json` | `3df290d512fca555b01dcf88777a4fb2f286627beeb7a7196c2ee5fc2eb40541` |

## Scope of acceptance and remaining work

This review accepts exactly the frozen three theorem bundles and all their new private/generated proof support at the recorded hashes. Their one-dimensional actual-law conclusions are complete and usable as producer interfaces.

It does not certify source tilt part (c), changed raw-second/variance comparability such as `m2ρ≤2Vρ`, the characteristic-power bound, source drift-factor payment, survival, an unconditional regulator second moment, actual product-weighted `U_i/Q_i` identities, complex shift, growing-y kernels, inversion, desmoothing, or C1/C2 closure. Existing product-measure results retain their own external attribution and input requirements. Source scale/clock/conditional-law instantiation remains with consumers. C12/OQ3/OQ4/OQ56 original roots remain OPEN except separately accepted prior closures.

Final verdict: **CORRECT**, no blocking issue, no additional assumption, no proof repair requested. Evidence is qualified for root reuse at the exact source/object version above. Reviewer production write authority: none; review assignment complete and slot released. The coordinator's next dependency is integration/consumption of this producer, followed by the still-open actual weighted-regulator and joint-tilt downstream obligations; this final report is not a persistent runtime mechanism.
