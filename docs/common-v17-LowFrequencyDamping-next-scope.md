# Actual fixed-law low-frequency damping: pair truncation and spectral gap

Status: PROPOSED FOR INDEPENDENT DECLARATION REVIEW. No candidate Lean source,
proof or declaration has been written, elaborated or compiled. Only this scope
and read-only server source/API probes belong to this work unit. Existing
frozen mathematical sources, caches and common interfaces are unchanged.

## Exact source claim and proposed next unit

The selected target is the genuine fixed-law low-frequency lemma
`h:supp:lowfreq`, not a generic test identity or an assumed spectral gap.
The candidate first proves actual independent-pair moment retention and
the exact characteristic gap identity, then proves the quantitative gap
and exponential norm bound. It uses the actual noncentered increment law.

Read-only source SHA256:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

Source anchors and literal mathematical content:

* `main.tex:546–551`, `h:eq:conditionallaw`: the actual conditional increment
  is `A = ξ | {|ξ|≤h_x}` and `The conditional mean need not be zero.`
* `main.tex:622–625` and `supplement.tex:1977–1983` define the actual moments
  `μ=E_x^* A`, `m_r=E_x^*|A|^r`, `τ²=m_2-μ²`, and `γ=m_3/τ²`.
* `main.tex:673–678` defines the true coupled characteristic integral
  `φ(u,v)=E_x^* exp(iuA+ivA²)`, already formalized as `quadraticChar`.
* `supplement.tex:2371–2377`, `h:supp:lowfreq`, states that absolute
  `κ,c>0` exist such that

  ```text
  |u|≤κ/γ, |v|≤κ|u|/γ  =>  |φ(±u,v)|≤exp(-c τ²u²).
  ```

* The true proof is `supplement.tex:3155–3192`. It uses independent
  copies `A,A'` under the same conditional law, `D=A-A'`, and the retained
  pair event `Acal={|A|≤d0,|A'|≤d0}`. At `3159–3162` it chooses
  `d0=min(c/|u|, |u|/(4|v|))`, with the second term infinite at `v=0`.
* Its moment payment is `3169–3178`: the bad-pair square moment is at most
  `τ²`, whereas `E D²=2τ²`, so `E[D² 1_Acal]≥τ²`.
* Its phase payment is `3180–3187`:

  ```text
  |v(A+A')|≤|u|/2,
  1-|φ(u,v)|² = E[1-cos{D(u+v(A+A'))}]
                ≥ c' u² E[D² 1_Acal] ≥ c' τ²u².
  ```

* `3189–3192` then passes from the genuine gap to exponential damping,
  applies the calculation to `-u`, and treats `u=0` separately (the
  assumptions then force `v=0`).
* The immediate consumers are `supplement.tex:2477–2486` (odd finite-power
  damping) and `3438–3459` (the low-frequency odd-power derivative table).
  The table additionally needs individual characteristic derivative
  controls and the finite differentiated power-difference algebra.

The proposed explicit constants are `κ=1/128` and `c=1/32`. The source
only asserts some absolute positive constants; selecting these concrete
valid constants does not change the moment or distribution assumptions.

## Fixed true law, raw third moment, and no new support/fourth moment

In the proposed module `ν` is the actual law of `A` and is fixed throughout.
Write only actual quantities

```text
μ = integral a dν,
m3 = integral |a|³ dν,
V = ProbabilityTheory.variance id ν = integral a² dν - μ²,
γ = m3/V.
```

The public input is a probability law, actual integrability of its raw
absolute cube, and `V>0` where the source requires a nondegenerate law.
Actual first/square integrability and the variance identity must be
derived; no totalized nonintegrable integral is used to obtain a bound.
There is no premise that `μ=0`. The derived difference `D=A-A'` has mean
zero because it uses two independent copies of the same law, which does
not center the original increment `A`.

No global third moment of the original untruncated `ξ` is requested.
The actual conditional increment is bounded and therefore supplies `h3`
once its genuine conditioning mass is positive. No fourth moment enters
this real-frequency norm estimate. The low-frequency proof itself does
not require an additional support bound `|A|≤h_x` or the larger
`h=ε0/(1+y)`; these support facts belong to the actual conditional-law
specialization and later complex/noise estimates.

The moment cutoff `d` used for the pair proof is an auxiliary proof
parameter, distinct from the original retained-observation cutoff `h_x`.

## A smaller legitimate pair-tail payment

The source bounds the bad-pair moment by
`C{m3/d + m2*m3/d³}` and invokes Lyapunov to absorb the second term.
For the selected target there is a direct pointwise alternative:

```text
on max(|a|,|b|)>d>0,
d(a-b)² ≤ (|a|+|b|)³ ≤ 4(|a|³+|b|³).
```

Indeed `d≤|a|+|b|`, `|a-b|≤|a|+|b|`, and all factors are nonnegative.
The cubic inequality follows from the exact identity
`4(r³+s³)-(r+s)³=3(r+s)(r-s)²≥0` for `r,s≥0`.
After actual integration under `ν.prod ν`, this gives

```text
E[D² 1_bad] ≤ 8m3/d.
```

This is a proved scalar/moment obligation of the candidate, not an input
variance-retention assumption. It avoids the extra Lyapunov sublemma and
does not add any distribution or moment hypothesis. For `8m3≤dV`, it
leaves `E[D² 1_good]≥V` because the true full pair moment is `2V`.

For the final frequency theorem choose `d=16γ`. Positive variance plus
actual third integrability implies `m3>0`: if `m3=0`, nonnegativity and
actual integrability give `a=0` almost everywhere, hence `V=0`, a
contradiction. Thus `γ,d>0` are derived rather than new premises.
The frequency restrictions give

```text
|u|d ≤ 1/8 ≤ 1/3,
4|v|d ≤ |u|/2 ≤ |u|,
8m3 ≤ dV.
```

This fixed cutoff is an admissible alternative to the source's minimum
cutoff (take the source small phase constant `c=1/8`). Multiplicative
frequency conditions avoid introducing infinity at `v=0` or dividing by
`u`. They also preserve the `u=0` boundary explicitly.

## Proposed public API: zero definitions and six theorems

Future file: `Shao/Probability/LowFrequencyDamping.lean`.
Namespace `Shao.Probability`; `open MeasureTheory ProbabilityTheory`;
`set_option autoImplicit false`.
Reuse `quadraticChar` exactly. No new characteristic function, variance,
conditional law, truncation-budget definition or abstract damping predicate
is introduced. Definitions inside theorem `let` binders are actual moments,
not additional free parameters.

### 1. Actual independent-pair square integrability and exact moment

```lean
theorem quadratic_pair_square_moment (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) :
    Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (ν.prod ν) ∧
      (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂ν.prod ν) =
        2 * variance (id : ℝ → ℝ) ν
```

The equality is `2(m2-μ²)`, not `2m2`. Independence is the actual product
law. Genuine integrability must precede the expansion and factorization.

### 2. Strict bad-pair cube payment

```lean
theorem quadratic_pair_tail_square_bound (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (d : ℝ) (hd : 0 < d) :
    Integrable
      (fun z : ℝ × ℝ =>
        if d < |z.1| ∨ d < |z.2| then (z.1 - z.2) ^ 2 else 0) (ν.prod ν) ∧
      (∫ z : ℝ × ℝ,
        if d < |z.1| ∨ d < |z.2| then (z.1 - z.2) ^ 2 else 0 ∂ν.prod ν) ≤
        8 * (∫ a : ℝ, |a| ^ 3 ∂ν) / d
```

### 3. Closed retained-pair variance lower bound

```lean
theorem quadratic_pair_retained_square_lower (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (d : ℝ) (hd : 0 < d)
    (hbudget : 8 * (∫ a : ℝ, |a| ^ 3 ∂ν) ≤
      d * variance (id : ℝ → ℝ) ν) :
    Integrable
      (fun z : ℝ × ℝ =>
        if |z.1| ≤ d ∧ |z.2| ≤ d then (z.1 - z.2) ^ 2 else 0) (ν.prod ν) ∧
      variance (id : ℝ → ℝ) ν ≤
        (∫ z : ℝ × ℝ,
          if |z.1| ≤ d ∧ |z.2| ≤ d then (z.1 - z.2) ^ 2 else 0 ∂ν.prod ν)
```

The input is an actual scalar cutoff/moment inequality. The retained
variance lower bound itself is proved from the full pair identity and
tail payment; it is not passed into the later damping theorem as an
unproved premise. Boundary atoms at `|a|=d` stay in the retained event.

### 4. Actual characteristic norm-square gap identity

```lean
theorem quadraticChar_gap_identity (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (u v : ℝ) :
    1 - ‖quadraticChar ν u v‖ ^ 2 =
      ∫ z : ℝ × ℝ,
        1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂ν.prod ν
```

This bounded-integrand identity needs no moments. It must be derived from
the actual coupled characteristic integral using product integration,
complex conjugation of the entire phase, and its real part. It does not
identify `φ(-u,v)` with the conjugate of `φ(u,v)`.

### 5. Genuine local spectral gap from paid pair truncation

```lean
theorem quadraticChar_local_gap (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (d : ℝ) (hd : 0 < d)
    (hbudget : 8 * (∫ a : ℝ, |a| ^ 3 ∂ν) ≤
      d * variance (id : ℝ → ℝ) ν)
    (u v : ℝ) (hu : |u| * d ≤ 1 / 3)
    (hv : 4 * |v| * d ≤ |u|) :
    variance (id : ℝ → ℝ) ν * u ^ 2 / 16 ≤
      1 - ‖quadraticChar ν u v‖ ^ 2
```

On the retained pair event, `|v(a+b)|≤|u|/2`, so
`|u+v(a+b)|≥|u|/2`, while the full phase has absolute value at most
`3d|u|≤1`. Prove the elementary bound `t²/4≤1-cos t` for `|t|≤1`, then
integrate the lower bound `u²D²/16` on the retained event. Off that event
the cosine gap remains nonnegative. Thus the spectral gap is a theorem
consequence, not an assumed input.

### 6. Explicit actual low-frequency exponential damping

```lean
theorem quadraticChar_lowFrequency_damping (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (u v : ℝ)
    (hu : |u| ≤ (1 / 128 : ℝ) /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν))
    (hv : |v| ≤ (1 / 128 : ℝ) * |u| /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν)) :
    ‖quadraticChar ν u v‖ ≤
        Real.exp (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32) ∧
      ‖quadraticChar ν (-u) v‖ ≤
        Real.exp (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32)
```

The final theorem has no cutoff, variance-retention, cosine-gap or damping
hypothesis: those are proved using the previous theorems and `d=16γ`.
After obtaining the gap `V u²/16`, use
`1-t≤exp(-t)` and nonnegative squares to pass from the actual norm square
to `exp(-Vu²/32)`. The negative frequency satisfies the same absolute
frequency conditions; no symmetry of `ν` is required.

## Analytic obligations and current cached APIs

All proposed candidate proofs remain unwritten. The actual inspected
Mathlib pin is `807d3836b165983210ee2ecf3cd28f239436949c`.
The intended minimal imports are the frozen `QuadraticCharacteristic`,
cached product integration/complex continuous-linear-map integration,
L2 and variance modules. No characteristic-function redefinition is
needed; the existing literal phase is sufficient.

Actual integrability obligations:

* Derive actual first/square integrability from the probability-space
  dominator `1+|a|³` and measurability of real identity/square.
* The full pair square is dominated by `2a²+2b²`. The cross product is
  integrable by the product of two actual L1 variables before its integral
  is factored. Use the actual variance bridge for the noncentered law.
* Both pair masks are measurable and dominated by the full pair square.
  The cube-tail dominator is an actual integrable sum of the two marginal
  cubes. Establish all these integrabilities before splitting good/bad
  integrals or applying integral monotonicity.
* Both complex phase factors have norm one; their product with a conjugate
  is genuinely integrable on `ν.prod ν`. The real cosine gap is bounded
  between zero and two. Prove these facts before Fubini or taking the
  real part of the actual integral. Do not use default-zero Bochner
  integrals in any of these equalities.
* A private small-angle cosine lemma may use the cached global sine
  remainder and `sin²(t/2)=(1-cos t)/2`. For example, at `|t|≤1`,
  `|sin(t/2)|≥(5/6)|t/2|`, so `1-cos t≥25t²/72≥t²/4`.
  The origin is included without division by `t`.

Source/API probes found these existing declarations (namespace corrections
are reflected here):

| Existing API | Contribution |
|---|---|
| `Integrable.comp_fst`, `.comp_snd`, `.mul_prod` | True marginal/cross integrability on the actual product measure. |
| `integral_prod_mul` | Actual product expectation factorization, with integrability separately proved. |
| `integral_conj`, `integral_re` | Conjugation and real part of the actual complex integral. |
| `Complex.exp_conj`, `.mul_conj`, `.normSq_eq_norm_sq` | Actual phase conjugation and norm-square algebra. |
| `variance_eq_sub`, `variance_congr` | The actual raw/centered variance bridge, and the `m3=0` contradiction. |
| `Real.abs_sub_sin_le`, `Real.sin_sq_eq_half_sub` | Small-angle cosine lower bound with the explicit constant. |
| `Real.one_sub_le_exp_neg` | Final exponential conversion of the genuine spectral gap. |
| `integral_eq_zero_iff_of_nonneg_ae` | Derive `m3>0` from positive variance, without another moment inequality premise. |

The exploratory probes corrected nonexistent guessed names
`Integrable.prod_mul`, `Complex.integral_re`, and `Complex.conj_exp` to the
actual names above. No candidate theorem was supplied to Lean in a probe.
Read-only artifact inspection found the complex continuous-linear-map
integral module cached. The generic characteristic-function Basic module
is now also cached, but inspection did not reveal the specific coupled
pair-gap identity here; the independent characteristic-function module
is not cached and is not required for the explicit product-integral route.
No cache acquisition or cache write is requested by this scope.

Transport note: the successful earlier read-only probe outputs printed the
actual types of the corrected product/complex/trigonometric APIs above.
Those exploratory Lean streams also reported the guessed-name errors noted
here. A final cleaned API-only probe could not be dispatched: the server
relay repeatedly returned `operation_failed` with
`operation_may_have_started=false`, null remote exit code, and no output.
The coordinator was informed. No final cleaned-probe exit-0 claim is made,
and no candidate declaration was implemented or checked. This transport
fault does not erase the actual existing API types already observed.

## The actual h_x law versus the existing reciprocal-cutoff interfaces

The source law is fixed at `x`:

```text
ν_A = cond ν_ξ {|z|≤h_x},    h_x=ε/(1+x).
```

The earlier common interface is instead

```text
retainedCutoffLaw ν_ξ b = cond ν_ξ {|z|≤1/b}.
```

It is not legitimate simply to instantiate that interface with `b=x` or
`b=1+x`. There is, however, a precise mathematical reuse route:

```text
a=1+x, b=a/ε; prove 1/b=ε/a=h_x,
then prove the retained sets and true conditional measures equal.
```

For the original normalized law assume the genuine source inputs
`x≥0`, `0<ε≤1/2`, `E ξ=0`, `n E ξ²=1`, actual original square
integrability, and `R=truncationBudget ν_ξ n x<ε³/8`.
This is consistent with the source's smaller `η(ε)` budget, rather than
an additional global-third-moment assumption. The existing modules give
the following exact reusable path, once the bridge is separately proved:

1. `truncationBudget_scale_one_le` with scale `1/ε` gives
   `H_b=n E F(bξ)≤ε⁻³R<1/8≤1`. This is the actual rescaled budget, not
   an assumption that `R_n(b)≤1`.
2. `Shao.truncationBudget_sample_size_lower` from `TruncationSampleSize`
   can be applied
   at the original `t=x`, `ρ=R`: `R<ε³/8≤1/64≤1/16`. Its quantitative
   middle expression gives
   `n≥(1-R)³a⁶/R²≥a⁶/ε⁶=b⁶`, using
   `R²≤ε⁶/64` and `(1-R)³≥(15/16)³>1/64`.
   This uses the actual positive original budget, derived by its existing
   normalization interface. It does not assert `b⁶≤n` without payment.
3. Since `b≥2`, the accepted retained mass/moment interfaces apply at `b`.
   `retainedCutoffMass_bounds` gives positive true conditioning mass,
   and `integrable_retainedCutoffLaw_abs_cube` gives the exact conditional
   `h3` from original L2, without any full third original moment.
4. The accepted `retainedSample_variance_third_moment_bounds` at
   `j=0`, with the proved `b⁶≤n`, proves positive actual conditional
   centered variance. Its existing raw/centered variance identity and
   Mathlib variance bridge identify this with `variance id ν_A>0`.
   The conditional mean is retained, not asserted zero.

The relevant frozen sources inspected are:

```text
TruncationSampleSize.lean 017a62c7f2e9e8ed43259d28d145e67b7010152a0c233d671680fcc5a01635de
RetainedSample.lean       a507e549e2973dd04ce25f22e2c6973e0e6c491433a1d7fd2d88fbb082e86ca4
RetainedVariance.lean     5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6
```

This rescaling/set-equality/budget/sample-size/variance transport chain is
**not yet a proved common source-specific bridge**. It is outside the six
candidate signatures above and must not be reported as already closed.
It shows a legal reuse route and identifies the remaining formal work;
there is no justification for silently replacing `h_x` by `1/x` or for
assuming positive variance without that route. The generic fixed-law
damping lemma remains independently meaningful and provable while this
specific source instantiation is pending.

## Independent boundary and altered-statement checks

* **Boundary atoms:** the good pair event uses both weak inequalities
  `|a|≤d,|b|≤d`; its complement is exactly the strict union in the tail
  theorem. No equality atom is discarded or counted twice.
* **Zero frequency:** the final domain at `u=0` forces `v=0` after the
  derived `γ>0`. The exponential bound is one; no division by `u` or `v`
  is used. The local gap theorem itself also handles `u=v=0`.
* **Degenerate law:** the pair moment and gap identity include zero or
  constant laws. The final gamma-ratio theorem explicitly requires actual
  positive variance, as the source does; no division by zero is hidden.
* **The global extension is false:** the fair law on `{-1,1}` has `V=1`,
  `m3=1` and `φ(u,0)=cos u`. At `u=2π` its norm is one, contradicting
  `exp(-c u²)<1` for every `c>0`. The low-frequency restriction cannot be
  dropped or represented as a global Gaussian bound.
* **The quadratic strip is essential:** the fair law on `{0,1}` has
  `V=1/4>0`; at `v=-u`, the true phase `uA+vA²` is identically zero, so
  the characteristic norm is one even for arbitrarily small nonzero `u`.
  The proposed strip excludes this cancellation for nonzero `u`.
* **Centered third moment cannot replace the raw source m3:** take the
  fair law on `{L-1,L+1}` with `L>1`. Its mean is `L`, variance is one,
  centered absolute cube is one, but raw `m3=L³+3L`. For `v=-u/(2L)`,
  both atoms have the same phase `u(L²-1)/(2L)`, so the norm is one.
  For any proposed positive `κ`, choose `L≥1/(2κ)` and `0<u≤κ`.
  Replacing the true gamma with centered-gamma `1` would satisfy both
  erroneous low-frequency conditions and falsely predict a strict gap.
  The actual raw gamma correctly shrinks the domain and excludes it.
* **No fictitious phase-coordinate independence:** the gap is for the
  coupled phase `(a-b)(u+v(a+b))`. The true dependence of `A` and `A²`
  remains; product independence is only across the two copies under
  `ν.prod ν`.

These are exact mathematical boundary checks, not Lean implementation of
the proposed candidate. No source event or strict CDF boundary is changed.

## Work ledger and minimum next action

| Item | State |
|---|---|
| Source statement, true noncentered law, actual pair proof and consumers | READ and explicitly bound above |
| Pair-tail alternative and explicit `κ=1/128,c=1/32` | DERIVED algebraically, awaiting independent semantic review and later Lean proof |
| Current product/integral/trigonometric APIs and cache | Read-only probes; no cache mutation |
| h_x versus reciprocal cutoff | Exact mathematical reuse plan identified; formal bridge OPEN |
| Candidate Lean implementation | NOT STARTED; awaiting declaration review/freeze |
| Low-frequency finite-power derivative table | Still OPEN as a downstream combined theorem |
| High-frequency noise/damping, clock probability, Fourier inversion and strict-CDF smoothing | OPEN |

Minimum next action: independently review and freeze the six exact
signatures and constants above. Only then implement the new owned module,
using actual product-law integrability and server-only Lean checks, hash
and transitive axiom gates. The conditional `h_x` source specialization may
be assigned as a distinct bridge unit; it is not a new premise or an
unproved claim inside the generic damping theorem. After freeze, preserve
these proposal bytes and put progress in a separate receipt.
