# ER229 independent complete final review

STATUS: CORRECT

JUSTIFICATION: The exact frozen declaration is proved for every stated measurable space, probability measure, real-valued function, true exponential-domain interior hypothesis, actual mean-zero hypothesis, and natural number n >= 1. The proof derives the order-zero, order-one, and order-two actual CGF coefficients from pinned primary mathlib interfaces, then proves precisely the displayed finite complex polynomial identity. There is no assumed coefficient, moment-error estimate, coherence condition, or covariance-I identity. Acceptance is restricted to this helper's frozen scope.

## Role, independence, and complete reading

- Reviewer: fresh `oq3_er229_final_review`, prescribed model `gpt-6.1-sol`, reasoning effort `xhigh`; independent of the parent author of this source.
- Method: math-theorem independent critical-gap verification, not math-ultra. No additional agent was used.
- Sole writable artifact: this report. No proof/source, server, Lean, axiom-check, Git, publication, shared implementation, or external-chat action was performed by this reviewer.
- Complete direct reading: all 43 LF source lines, all 13 LF frozen-declaration lines, all 21 LF scope lines, all 14 LF actual-type lines, all 185 LF receipt lines, all 82 LF build-history lines, all 103 LF audit-record lines, all 47 LF Audit.lean lines, and all 224 LF pinned primary API extraction lines. The entire theorem proof and both actual statement-let definitions were read; no proof or type was replaced by a summary.
- Original-source reading: `C:/game/shao/current/oq3/proofs/r2/report.md` lines 1-158 and 493-523, including sections 1-2 and terminal scope/audit; all 58 LF of `C:/game/shao/current/oq3/verdict.md`. These original files were read only.

Exact local input identities were independently recomputed from bytes:

| Artifact | SHA256 | Bytes | LF |
| --- | --- | ---: | ---: |
| u22er-source.lean | ae3883790c028b072e081216fd09b20d2c4ab81e54ee7fd64bc4b4d6b493aa19 | 1848 | 43 |
| u22er-frozen-declaration.lean.txt | 3f19678f0f1e3052d41b31d0dc82a523f96a3c60fc76788cb452872086c28936 | 759 | 13 |
| two-hundred-twenty-ninth-unit-scope.md | 3881f3692e3d63cbe51bd29e5c7bdb90b62989e4677fde49b250efacd3d2ef90 | 1413 | 21 |
| u22er-actual-types.txt | c50ff8a304ebd643f23b7d17047964c83b7c02cb5473c5e64a5fd251651bb373 | 802 | 14 |
| u22er-receipt.json | 8b9b645ab79d13d8ff34b720e71bdc15730fdd63aa19bcb874ef18c9f53bbf48 | 5373 | 185 |
| u22er-build-history.json | 64bb5fbc8884e81f103d9fd0a9e07151dc23de37054d4fe2e70e602d8ff9964a | 2158 | 82 |
| u22er-audit-record.json | 4ea8b6d73dbc0c1844c4a373493d66e76f90908c1ed5179249a116361c08d6ca | 3033 | 103 |
| u22er-Audit.lean | d12ec85b75f562feffc552837d20b12286449ddea6a180940683d5a65ab52272 | 2019 | 47 |
| u22er-primary-api.txt | 2a3e115db72cd3e14580c68c5f5a33a9620ce97c0ca3703e7cd7561b9e8a9db7 | 8436 | 224 |

All nine files above have zero CR bytes. Original report whole-file SHA256 is `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55` (20102 bytes, 523 LF); original verdict SHA256 is `fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5` (3041 bytes, 58 LF). Their hashes agree with the task's original-source bindings.

## Frozen statement, actual type, and both lets

The only actual owner is the theorem `Shao.OQ3.centered_actual_cgf_normalized_octic_polynomial`, in module `Shao.OQ3.ActualCGFNormalizedOcticPolynomial`. The frozen declaration equals the source declaration before `:= by` byte for byte, including its trailing LF; this comparison was checked deterministically.

The actual type retains the same unrestricted universe-polymorphic domain `{Omega : Type u}`, `MeasurableSpace Omega`, probability measure `mu`, and actual function `X : Omega -> Real`. Its premises are exactly:

1. `0` belongs to the interior of `ProbabilityTheory.integrableExpSet X mu`;
2. the integral of this same `X` under this same `mu` is zero;
3. `n : Nat` and `1 <= n`.

There is no hidden scalar replacement, distribution replacement, vector witness, frequency, finite-law restriction, pointwise boundedness assumption, covariance normalization, assumed higher coefficient, or supplied error estimate.

The first actual statement let is the full function `kappa j = iteratedDeriv j (ProbabilityTheory.cgf X mu) 0`. These are the actual real CGF derivatives, not arbitrary coefficients chosen to make the conclusion true. The second let is the full complex sum over `Finset.range 9`, with summand `I^j / j! * (kappa j) * n / (sqrt n)^j`. Thus it includes exactly orders 0 through 8, and every coefficient is evaluated for the same `X` and `mu`. Both let values appear completely in the actual type; neither is an extra hypothesis or an opaque external definition.

The conclusion's integral is the actual second moment `integral (X^2) dmu`, cast from Real to Complex. The second sum is over `Finset.range 6` and uses `kappa (j+3)`, factorial `(j+3)!`, and denominator `(sqrt n)^(j+1)`. Hence it represents exactly orders 3 through 8 and scales from `n^(-1/2)` through `n^(-3)`. The actual type has no omitted binder, conclusion, let body, or additional non-theorem value to review.

## Complete proof audit

Source lines 1-7 import only pinned mathlib `MGFAnalytic` and `IteratedDeriv.Lemmas`, open notation, and establish the namespace/noncomputable section. There is no project-producer dependency or additional mathematical hypothesis hidden in an import.

Source lines 22-23 introduce classical reasoning and the two definitional statement lets. Introducing these lets preserves their defining values; it does not replace them by independent arbitrary data.

Source lines 24-25 prove `deriv (cgf X mu) 0 = 0`. The complete pinned primary declaration `deriv_cgf_zero` takes exactly the hypothesis `0 in interior (integrableExpSet X mu)` and concludes that the derivative is `integral X dmu / mu.real Set.univ`. Rewriting with the stated actual mean zero and `zero_div` proves the needed equality without an additional denominator assumption.

Source line 26 proves `kappa 0 = 0` by unfolding the actual kappa and simplifying order-zero differentiation and `cgf_zero`. The primary `cgf_zero` requires `IsZeroOrProbabilityMeasure mu`; the existing `IsProbabilityMeasure mu` supplies that instance. It states `cgf X mu 0 = 0` for arbitrary `X` under the stated instance.

Source line 27 proves `kappa 1 = 0` by identifying the first iterated derivative with the ordinary derivative just proved. There is no moment-to-cumulant premise.

Source lines 28-31 prove `kappa 2 = integral (X^2) dmu`. After unfolding kappa, the complete pinned primary `iteratedDeriv_two_cgf h0` at `v=0` is

`D^2 cgf(v) = integral [X^2 * exp(v*X)] dmu / mgf X mu v - (deriv (cgf X mu) v)^2`.

Its complete declaration and section-variable context introduce no hidden measurability, finite-measure, centering, or covariance assumption. The same supplied exponential-interior hypothesis is its sole explicit premise. At zero the exponential factor is one, the pinned probability identity `mgf_zero` gives denominator one, and the established derivative is zero. The result is exactly the actual second moment, with no rescaling or alternate law. The primary proof itself handles the zero-measure branch separately before quotient differentiation; in this theorem the stronger probability instance already excludes a zero measure.

Source line 32 derives `0 < (n : Real)` from `1 <= n` by an exact natural-to-real cast. Line 33 applies `Real.sqrt_pos` to obtain a nonzero real square root. Line 34 transfers nonzeroness through the injective real-to-complex cast. Lines 35-36 transfer `Real.sq_sqrt` to obtain `(sqrt (n : Real) : Complex)^2 = (n : Complex)`. The cast directions, domains, and nonnegative-square-root condition all agree; no positivity of a random-variable variance is used.

Source lines 37-40 unfold only the actual Qn8, expand both finite ranges, replace kappa0/kappa1/kappa2, evaluate the numeric factorials and powers of I, replace complex n by the square of its complex-cast real square root, clear the proven-nonzero denominator, and finish a polynomial identity by `ring`. This is exact finite algebra after the three primary identities. There is no analytic continuation, limiting operation, asymptotic approximation, summation interchange, or unproved Taylor remainder hidden in this closing step.

The algebra can be checked independently by putting `s = (sqrt (n : Real) : Complex)`: the order-two term is `I^2/2! * kappa2 * n/s^2 = -kappa2/2`, while for each `m=3,...,8`, `n/s^m = 1/s^(m-2)`. Writing `m=j+3` makes `m-2=j+1`, exactly the conclusion's exponent. The six signs and factorials are respectively `-I/6`, `1/24`, `I/120`, `-1/720`, `-I/5040`, and `1/40320`; no sign or order is dropped. Numeric factorials are nonzero in Complex, and `s != 0` justifies every variable denominator clearing.

## Quantifiers, domains, and boundary attacks

- The domain-interior condition is the true exponential-integrability domain of the actual `X,mu`, not a stand-in openness certificate. It is used at zero in both derivative formulas. The primary declarations permit an arbitrary function `X` with that condition, so no missing global measurability premise has been silently added by this proof.
- Probability normalization is essential to the actual second-moment formula and is explicitly present. A zero measure cannot satisfy `IsProbabilityMeasure mu`. A valid probability law concentrated at zero, or `X=0` almost everywhere, is allowed and gives zero kappa/second-moment terms; no nondegeneracy or variance lower bound is needed.
- `n=1` is included: `sqrt 1=1`, all denominators are nonzero, and both finite polynomial expressions still agree. The statement makes no claim at `n=0`; that value is correctly excluded by the stated hypothesis, not silently discarded in the proof.
- Neither the mean nor the second moment is taken under a different law. There is no hidden independence, iid, compact-parameter, frequency, or uniform-in-law quantifier. All complex casts are of the real quantities shown in the actual type, and all powers/factorials use natural indices.
- An identity such as `integral X^2 dmu = u^2+v^2` is neither assumed nor concluded. Degenerate and non-unit-variance centered laws remain in scope, which is consistent with the displayed actual-second-moment coefficient.

No critical gap or missing case was found.

## Exact server evidence and axiom coverage

This reviewer reused the exact existing compact server receipts, as authorized, and ran no Lean or axiom command. The pinned configuration is Lean `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. The complete primary extraction records `Moments/Basic.lean` SHA256 `73264d34c22038347bc73821a45442346ce12756475359325ebb9340a89af8fa` and `Moments/MGFAnalytic.lean` SHA256 `4cd9ee9d7724459443aef04ad083267bc1e11da13a98b28b6cf59bee9dbb94c2`, together with the relevant variable contexts and complete primary declarations/proofs.

Native attempt 001 is the first and only entry in the exact build history: source SHA `ae3883790c028b072e081216fd09b20d2c4ab81e54ee7fd64bc4b4d6b493aa19`, 1848 bytes/43 LF, exit code 0, 6.267231138423085 seconds, recorded at `2026-10-27T16:16:07.180612+00:00`. It binds build log SHA256 `56a0ff8784818c946735057e05cd54d0d966d573ed5a2027a4e6e09435da55e8`, 555 bytes. There is no failed attempt to overwrite, omit, or replay in this supplied history.

The same-first-original-object audit records exit code 0, 5.727478658780456 seconds, and `2026-10-27T16:16:22.900379+00:00`. It binds original object SHA256 `81721abf718d8592feb7788e37b3d20330e0be3b1c0a418494c3cdc219f12f0f`, 630856 bytes; audit-source SHA256 `d12ec85b75f562feffc552837d20b12286449ddea6a180940683d5a65ab52272`; audit-log SHA256 `c9b7329f4f93fad133a1df3f1b420ce8e4c886670ffb7318f732f4adc4d9ddb1`, 1054 bytes; and actual-types SHA256 `c50ff8a304ebd643f23b7d17047964c83b7c02cb5473c5e64a5fd251651bb373`.

Audit.lean imports the target module, enumerates actual environment owners using `env.getModuleIdxFor?`, and applies exact owner-module equality rather than a namespace-prefix filter. For every actual owner it rejects a new axiom, runs `Lean.collectAxioms`, and rejects any dependency outside `propext`, `Classical.choice`, and `Quot.sound`. It prints complete owned types and any definition values, and verifies the frozen target exists as a theorem. The supplied audit result and actual type agree on 1 actual owner/1 theorem/1 TYPE/0 non-theorem VALUE; the two statement lets are fully visible in that TYPE. The transitive axiom set is exactly the standard whitelist. There is no private/generated/non-theorem owner missing from the supplied one-owner result.

Direct source inspection and a forbidden-token scan find no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`. `classical` uses the permitted foundational axioms and does not introduce a mathematical assumption. The theorem proof itself was fully reviewed; dumping its generated theorem proof-term value is not required by the established mechanical-audit boundary.

Raw logs were not directly read by this reviewer. They remain server-only at `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22er-20261028/build-01.log` and `audit.log`, bound by the exact compact receipts above. The first original object was not copied or rehashed locally by this reviewer. The parent reports retained style warnings; this review does not suppress, alter, or independently reclassify those raw diagnostics. No concrete receipt/source/actual-type mismatch calls for a replay. `no_success_producer_replay` remains true in the supplied receipt.

## Original-source fidelity and limits of acceptance

The original report sections 1-2 place actual standardized variables and their small-frequency eighth-order cumulant expansion inside a larger weak-Cramer/Edgeworth argument. ER229 supplies an exact finite algebraic component compatible with that part of the construction. It does not supply the analytic remainder, the conversion from real CGF derivatives to the relevant characteristic/log expansion, or exponentiation into the complete order-six Edgeworth polynomial.

The leading coefficient is deliberately the actual second moment. A later canonical projection consumer must separately derive its equality with `u^2+v^2` from the qualified same-law covariance-I statement. This review gives no permission to replace `X`, `mu`, a canonical witness, or any original frequency/domain condition to obtain that identity.

The original strict range `0 < beta < 2/5`, fixed-point/regularity/uniformity/remote-region qualifications, p54 repairs, retained counterexample evidence, and external-result attribution remain unchanged. The original verdict's sufficient-repair and non-priority-certified limits remain intact; ER229 supplies no new novelty certification. In particular the helper proves no error bound, full order-six polynomial or expansion, Gaussian damping estimate, Fourier inversion, exterior control, B-D result, or OQ3/root closure. Those scopes remain open as appropriate. Its lack of a beta premise is consistent with a universal finite identity and does not weaken a later theorem's beta requirements.

Verdict within the exact frozen helper scope: complete source-to-statement/proof/actual-type/both-let review CORRECT, with the supplied exact-source server kernel and same-original-object all-owned transitive-axiom receipts passing. No mathematical repair is requested.

## Usage and release

Actual prescribed model/effort: `gpt-6.1-sol` / `xhigh`. `input_tokens: null`; `cached_input_tokens: null`; `output_tokens: null`; `reasoning_subset_tokens: null`, because reliable usage counters are unavailable to this context. No raw-token count or credit estimate is assigned to a subscription percentage.

COMPLETED_STOPPED. The sole report-writing authority and this review context are released after saving this report. No proof/source writer or execution authority was acquired; no child, tool, server command, or external write remains in flight. Further source changes require review of the affected exact bytes; this verdict binds only the hashes above.
