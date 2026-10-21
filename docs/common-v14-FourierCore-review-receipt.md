# QuadraticCharacteristic author implementation receipt

Status: AUTHOR IMPLEMENTATION COMPLETE; awaiting independent final proof review.
This is the implementation author's receipt, not an independent correctness verdict.
Author: `/root/deletion_inequality` (authorized GPT-6.1-sol, xhigh).
Date: 2026-10-21.

## Frozen statement and artifact identity

The original scope remains byte-for-byte unchanged:

```text
drafts/c12/FourierCore-next-scope.md
add680178670044bc54e90a143a1057b2d6bc74e0d08f42769480951bfe2c656
```

The independent preimplementation statement review was CORRECT with no changes:

```text
drafts/c12/FourierCore-statement-review.md
2f31ff4beec0ac9185e751d50db44f21688e1d56ac52fdc3a4c2482fd3dbf4be
```

As explicitly named in the frozen scope, the implemented module is
`Shao.Probability.QuadraticCharacteristic`, rather than the task shorthand
`FourierCore`. The coordinator was informed of this name before implementation.

Identical local and server source SHA256:

```text
8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5

C:/game/shao lean/drafts/c12/QuadraticCharacteristic.lean
/root/rivermind-data/shao-lean-20261021/workspaces/lead-c12/Shao/Probability/QuadraticCharacteristic.lean
```

Only this new Lean source and this separate author receipt were written.
No frozen source, scope, root import, cache or lock was changed. All Lean
compilation and API probes were executed on the designated server.

## Delivered public API

One public definition and all seven frozen theorem signatures are implemented,
with no added hypotheses or altered constants:

| Declaration | Local source line | Content |
|---|---:|---|
| `quadraticChar` | 21 | Actual integral of `exp(i(ua+va²))` under the fixed law. |
| `norm_quadraticChar_le_one` | 86 | Norm at most one under probability, without moments. |
| `iid_quadraticChar_factor` | 93 | Actual finite iid sample phase has expectation `quadraticChar^n`, including `n=0`. |
| `quadraticChar_odd_hasDerivAt` | 206 | Actual first real-frequency derivative `2i ∫ a cos(ua) exp(iva²)`. |
| `quadraticChar_odd_deriv_hasDerivAt` | 217 | Actual derivative of the actual first derivative, `-2i ∫ a² sin(ua) exp(iva²)`. |
| `quadraticChar_odd_remainder` | 281 | Mean-subtracted odd remainder at most `m3 (|u|³/3+2|u||v|)`. |
| `quadraticChar_odd_bound` | 311 | Odd difference at most `2|μ||u|` plus that remainder. |
| `quadraticChar_odd_derivative_bounds` | 333 | Mean-subtracted first derivative and second derivative bounds with exact frozen constants. |

The only analytic moment input is actual `Integrable (fun a => |a|^3) ν`
for the supplied increment law `ν`. No global third moment of an original
untruncated variable, centering, symmetry, positive variance, nonzero frequency,
frequency cut, or differentiability premise was added.

## Proof structure and actual-integrability gates

* A private phase is literally `exp((t:ℂ)*I)`. It is continuous and has
  norm one; each characteristic integrand is actually integrable under
  probability. The public characteristic function remains the frozen actual
  integral, not an abstract replacement.
* The iid theorem first rewrites the genuine linear sum plus the genuine
  energy as the sum of coordinate phases. `Complex.exp_sum` and
  `iIndepFun.integral_fun_prod_comp` then factor across iid observations.
  Each coordinate integral is transferred by the actual `IdentDistrib`
  input. The linear and quadratic coordinates of one observation are not
  independently averaged.
* `moments_of_third` derives first and square integrability from the
  integrable dominator `1+|a|³`; the probability premise supplies the
  constant part. Separate helpers establish sine, `a*cos(ua)` and
  `a²*sin(ua)` integrability. Multiplying an integrable real weight by the
  phase preserves actual integrability because the phase has norm one.
* The actual odd identity is obtained by subtracting the two integrable
  characteristic integrals and applying the pointwise exponential identity.
  It is `d=2i ∫ sin(ua) exp(iva²)`, with the same `v` in both frequencies.
  No erroneous partial-reflection/conjugation identification is used.
* Both derivatives use
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the real parameter,
  complex-valued integrand, `s=univ`, actual original integrability, continuous
  derivative integrands, and integrable dominators `|a|` and `a²`.
  The second public theorem rewrites the actual `deriv` using the first
  theorem at every parameter; it does not define a surrogate derivative.
* The pointwise sine error is bounded by
  `|b|³/6+|b||c|`, using the exact decomposition
  `(sin b-b)exp(ic)+b(exp(ic)-1)`. The cosine error is bounded by
  `b²/2+|c|`. Both are integrated against the actual third moment.
  Integral subtraction uses already established integrability; a helper
  explicitly handles the real-to-complex integral conversion.
* The factor `2i` yields the frozen constants `1/3` and `2` in the odd
  remainder. The derivative error gives `m3(u²+2|v|)`. Finally
  `|sin(ua)|≤|ua|` gives the genuine second derivative bound `2m3|u|`.

## Server validation

Server workspace:

```text
/root/rivermind-data/shao-lean-20261021/workspaces/lead-c12
```

After sourcing the common activation script and changing to that workspace,
the final exact-source targeted compilation was:

```text
taskset -c 0-3 lake env lean \
  -o .lake/build/lib/lean/Shao/Probability/QuadraticCharacteristic.olean \
  Shao/Probability/QuadraticCharacteristic.lean
```

Result: **exit 0, stdout empty, stderr empty**. No warnings were suppressed.
The successful final compile produced the module's own `.olean`; no shared
cache retrieval or cache mutation was performed by this author.

A separate server `lake env lean --stdin` import audited the resulting
artifact. It ran `#check` on the definition and all seven public theorems,
then `#print axioms` on each. All eight reported exactly the accepted set:

```text
[propext, Classical.choice, Quot.sound]
```

It additionally enumerated every environment declaration whose name begins
with one of the public API prefixes or the new module's private prefix,
and ran `Lean.collectAxioms` with a failing check for any axiom outside that
whitelist. Result:

```text
AUDITED_DECLARATIONS 29
exit 0
stderr empty
```

The enumeration includes generated internal declarations, not only the
eight public API declarations. The server word-token scan for `sorry`,
`admit`, `axiom`, `unsafe`, and `native_decide` found no match. The source
sets `autoImplicit false` and contains no custom axioms or suppressed proof
obligations. Source hash on the server equals the local draft hash above.

## Scope and remaining mathematical dependencies

This implements only the frozen real-plane component of the original
`h:supp:oddcommon` and the actual finite iid factor. It supplies the
`d,d',d''` factors used later in `h:supp:oddpowerderivatives`; it is not a
Gaussian/Fourier comparison theorem.

The source anchors remain those recorded in the unchanged scope:
`main.tex:673–678`; `supplement.tex:2348–2351`, `2384–2392`,
`3197–3219`, `2477–2484`, and `3438–3447`. Neither the strict CDF test nor
the zero-energy branch is changed or resolved by these estimates.

Still open: low-frequency variance-retention/spectral-gap damping,
law-adapted high-frequency smoothing, individual characteristic derivatives
and whole-power/T-scale derivative bounds, complex tilting, clock
concentration, Fourier inversion, and smoothing/defect payment back to the
strict CDF comparison. The counterexamples B1–B6 in the frozen scope still
apply to the tempting altered statements and are not bypassed here.

Minimum next action: a fresh independent proof review of the exact source
hash above, followed by coordinator integration if accepted.
