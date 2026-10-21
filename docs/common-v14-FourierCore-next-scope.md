# Actual quadratic characteristic function and its real odd estimates

Status: PROPOSED FOR INDEPENDENT STATEMENT REVIEW. No Lean implementation
of this candidate has been written or checked. Only this scope and
read-only server API/cache probes belong to the current work unit.
Existing frozen sources, root imports, shared cache and locks are unchanged.

## Selected actual analytic unit

The selected next unit is the **real-frequency part of the actual
`h:supp:oddcommon` estimate**, together with its true finite-iid Fourier
factor. It proves quantitative cancellation and first/second derivative
bounds for the actual characteristic function, rather than another
telescoping wrapper or a theorem assuming the desired Fourier bounds.

Write `ν=P_A` for the law of the actual conditional increment `A`,

```text
φ(u,v) = integral exp(i(ua+va²)) dν(a),
μ = integral a dν(a),  m3 = integral |a|³ dν(a),
d(u,v) = φ(u,v)-φ(-u,v).
```

This is one joint characteristic function of `(A,A²)`, with their true
dependence. The proposed unit uses every real `u,v`; it imposes no
centering, symmetry, variance bound or artificial frequency cut. Its
analytic moment input is the genuine integrability of `|A|³` under `P_A`.
It does **not** require a global third moment of the original untruncated
`ξ`: the source conditional law is bounded, and hence supplies the needed
conditional moments even in the original `p<3` branch.

The real-plane estimates have explicit constants, slightly stronger than
the source's unspecified absolute `C`:

```text
|d(u,v)-2iuμ| <= m3 (|u|³/3 + 2|u||v|),
|d(u,v)| <= 2|μ||u| + m3 (|u|³/3 + 2|u||v|),
|∂u d(u,v)-2iμ| <= m3 (u²+2|v|),
|∂u² d(u,v)| <= 2m3|u|.
```

The derivatives are also identified as actual integrals, not merely given
names and assumed to satisfy bounds.

## Exact source anchors and consumption

Read-only source snapshot hashes:

```text
C:/game/shao/current/c12/main.tex
beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
C:/game/shao/current/c12/supplement.tex
b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

The following are literal source formulas, with their current line anchors:

* `main.tex:673–678`, `h:eq:charfunctions`:
  `\varphi(u,v)&=\E_x^*e^{\ii uA+\ii vA^2}`.
* `supplement.tex:2348–2351`, `h:supp:transform`:
  `\widehat f_{n-i}(u,v)=\widehat H_y(u,v)\Xi(u,v)\varphi(u,v)^{n-i}`.
  The finite-iid theorem below supplies the actual future-increment
  expectation factor `φ^(n-i)`. It does not by itself prove the full
  Fourier transform, convolution, inversion or differentiation formula.
* `supplement.tex:2384–2392`, `h:supp:oddcommon`, on the real plane:
  `|\partial_u d(u,v)|\le C\{|\mu|+m_3(u^2+|v|)\}` and
  `|\partial_u^2d(u,v)|\le Cm_3|u|`.
  The proposed derivative estimates imply these assertions with an
  explicit absolute constant.
* `supplement.tex:3197–3205`, proof of `h:supp:oddcommon`:
  `d=2\ii\E_x^*[\sin(zA)\ee^{\ii vA^2-sA^2}]` and
  `d-2\ii z\mu =2\ii\E_x^*[(\sin(zA)-zA)\ee^{\ii vA^2-sA^2}] +2\ii z\E_x^*[A(\ee^{\ii vA^2-sA^2}-1)]`.
  The first quantitative theorem below is exactly the real specialization
  `z=u`, `s=0`, with its integrals and constants proved.
* `supplement.tex:3207–3219`, same proof:
  `\partial_u d(u,v)=2\ii\E_x^*[A\cos(uA)\ee^{\ii vA^2}]` and
  `\partial_u^2d(u,v)=-2\ii\E_x^*[A^2\sin(uA)\ee^{\ii vA^2}]`.
  These are the actual derivative identities proposed below.
* `supplement.tex:2477–2484` consumes the real odd difference together
  with the separate low-frequency damping lemma and the algebraic power
  difference, obtaining
  `|\varphi(u,v)^{n-i}-\varphi(-u,v)^{n-i}|`
  bounded by a Gaussian-damped multiple of
  `(n-i)|\mu||u|+(n-i)m_3(|u|^3+|uv|)`.
* `supplement.tex:3438–3447`, `h:supp:oddpowerderivatives`, explicitly says
  `Use Lemmas~\ref{h:supp:oddcommon} and~\ref{h:supp:lowfreq}` before its
  table for derivative orders `0,1,2`. The present unit supplies the
  actual `d,d',d''` factors for that table. It does not claim the other
  factors, including `φ_u`, `φ_uu` and the Gaussian decay, are already closed.

The full complex-shifted assertion in `h:supp:oddcommon0` uses
`z=u-iλ`, `ζ=v+is`, `λ,s≥0`, and a support-dependent `exp(Cλh)` factor.
That larger domain is **not** in this first batch. Restricting this batch
to the real assertions is explicit; no real result is reported as proving
the later tilted-complex-frequency estimates.

## Proposed Lean module and frozen-candidate API

Proposed future file: `Shao/Probability/QuadraticCharacteristic.lean`.
Namespace `Shao.Probability`; `open MeasureTheory ProbabilityTheory`;
`set_option autoImplicit false`.
The candidate is **one definition and seven theorems** below. No current
kernel, conditional law, energy, test or event is redefined.

### Actual characteristic integral and unit bound

```lean
noncomputable def quadraticChar (ν : Measure ℝ) (u v : ℝ) : ℂ :=
  ∫ a : ℝ, Complex.exp
    (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν

theorem norm_quadraticChar_le_one (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (u v : ℝ) :
    ‖quadraticChar ν u v‖ ≤ 1
```

The definition is the actual source expectation, not an abstract
function characterized by desired bounds. All phase exponentials have
norm one and are actually integrable under a probability measure; no
moment assumption is needed for this definition or unit bound.

### The actual finite iid factor, including an empty future

```lean
theorem iid_quadraticChar_factor
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (u v : ℝ) :
    (∫ ω, Complex.exp
      (((u * Shao.prefixSum (samplePath X ω) n +
          v * Shao.energy (samplePath X ω) : ℝ) : ℂ) * Complex.I) ∂μ) =
      (quadraticChar ν u v) ^ n
```

The genuine squared sample observations remain in the phase. This theorem
does not make the linear and quadratic coordinates independent. It uses
only genuine iid sample inputs, with no finite moment or nonzero variance
assumption. The `n=0` value is `exp(0)=1=φ^0`.

### Real odd third-order error and the source-ready bound

```lean
theorem quadraticChar_odd_remainder (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    ‖quadraticChar ν u v - quadraticChar ν (-u) v -
        2 * Complex.I * (u : ℂ) * (μ : ℂ)‖ ≤
      m3 * (|u| ^ 3 / 3 + 2 * |u| * |v|)

theorem quadraticChar_odd_bound (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    ‖quadraticChar ν u v - quadraticChar ν (-u) v‖ ≤
      2 * |μ| * |u| + m3 * (|u| ^ 3 / 3 + 2 * |u| * |v|)
```

In particular, without a new hypothesis these imply the source real-plane
`C{|μ||u|+m3(|u|³+|uv|)}` bound with `C=2`.

### Actual first and second odd derivatives

```lean
theorem quadraticChar_odd_hasDerivAt (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => quadraticChar ν r v - quadraticChar ν (-r) v)
      (2 * Complex.I *
        ∫ a : ℝ, ((a * Real.cos (u * a) : ℝ) : ℂ) *
          Complex.exp (((v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν) u

theorem quadraticChar_odd_deriv_hasDerivAt (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => deriv
        (fun s : ℝ => quadraticChar ν s v - quadraticChar ν (-s) v) r)
      (-(2 * Complex.I) *
        ∫ a : ℝ, ((a ^ 2 * Real.sin (u * a) : ℝ) : ℂ) *
          Complex.exp (((v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν) u

theorem quadraticChar_odd_derivative_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let d : ℝ → ℂ := fun r => quadraticChar ν r v - quadraticChar ν (-r) v
    ‖deriv d u - 2 * Complex.I * (μ : ℂ)‖ ≤ m3 * (u ^ 2 + 2 * |v|) ∧
      ‖deriv (fun r : ℝ => deriv d r) u‖ ≤ 2 * m3 * |u|
```

All derivatives are real-parameter derivatives of complex-valued
functions. The third-order input implies actual first/square
integrability under probability by the dominator `1+|a|³`; these are proof
obligations, not extra public inputs. There is no assumed differentiability
or derivative domination premise in the public theorems.

## Analytic proof obligations and available exact APIs

The proof must derive the actual real odd identity

```text
d(u,v) = 2i integral sin(ua) exp(iv a²) dν
```

from the actual characteristic integrals. Its subtraction of `2iuμ` then
gives the literal source two-term decomposition quoted above, with `s=0`.
The global elementary bounds are:

```text
|sin t-t| <= |t|³/6,
|cos t-1| <= t²/2,
|sin t| <= |t|,
norm(exp(it)-1) <= |t|.
```

Integrating the first term yields `(m3 |u|³)/3`; integrating the second
yields `2m3|u||v|`. In particular the proposed pointwise Fourier bound is
proved, not put in a hypothesis.

For differentiating the actual integral, use the globally integrable
derivative dominators `2|a|` and `2a²`; the parameter-dependent complex
exponentials retain norm one. Prove measurability and actual integrability
of the original integrands and their derivatives before applying the
dominated parameter-integral theorem. This cannot be replaced with
Bochner's default value in a nonintegrable case. The derivative identities
and their subsequent bounds must use the same fixed law `ν` as `u` varies.

Read-only server probes imported only existing cached modules and checked
the following existing API types; the corrected probe exited 0 with empty
stderr. No proposed definition or theorem was supplied to Lean.

| Checked/source API | Contribution |
|---|---|
| `iIndepFun.integral_fun_prod_comp` | Actual finite iid expectation factorization for complex products; no moment assumptions. |
| `Real.abs_sub_sin_le` | Global remainder `|t-sin t|≤|t|³/6`. |
| `Real.one_sub_sq_div_two_le_cos` | Together with `cos≤1`, the global quadratic cosine remainder. |
| `Real.abs_sin_le_abs` | The actual second odd derivative is controlled by `2m3|u|`. |
| `Real.norm_exp_I_mul_ofReal_sub_one_le` | The exponential remainder with its exact real phase; its namespace is `Real`, despite the complex-valued conclusion. |
| `Complex.norm_exp` | Norm-one phase integrability. |
| `HasDerivAt.ofReal_comp`, `HasDerivAt.comp_ofReal` | Real parameter differentiation of complex expressions. |

The crucial derivative-under-integral API was inspected in the actual
mathlib source:

```text
Mathlib.Analysis.Calculus.ParametricIntegral
hasDerivAt_integral_of_dominated_loc_of_deriv_le
```

It returns both derivative-integrand integrability and `HasDerivAt` from
actual original integrability, local measurability, a genuine integrable
derivative bound, and pointwise `HasDerivAt`. That module's `.olean` was
missing at the probe time; the coordinator has been given this exact
module name for central cache preparation. The author did not fetch or
write any cache.

The following artifacts are already cached:

```text
Mathlib.Probability.Independence.Integration
Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
Mathlib.Analysis.Complex.RealDeriv
```

The generic characteristic-function modules
`Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic` and
`Mathlib.Probability.Independence.CharacteristicFunction` also had source
APIs but no cached artifacts at the probe time. They are not necessary for
this literal source-integral first batch: the actual coupled phase is
defined explicitly and finite product integration is cached. The future
module may relate this integral to the generic characteristic function of
the pushforward phase if useful; no such unproved identification is an
input assumption here.

## Independent boundary/counterexample checks

These exact calculations check nearby altered statements; they are not
candidate Lean proofs.

**B1 — the linear mean term cannot be dropped.** Under `ν=δ_1`, `v=0`,
`d(u,0)=2i sin u`, `μ=m3=1`. At `u=1/2`,
`sin(1/2)≥1/2-(1/2)³/6=23/48`, so `|d|≥23/24`.
The altered zero-mean-style right side `m3 |u|³/3` would be `1/24`.
The candidate correctly keeps `2iuμ`; the source conditional law need
not be centered.

**B2 — global Gaussian damping is false.** For the fair two-point law on
`{-1,1}`, `τ²=1`, `m3=1`, `γ=1`, and `φ(u,0)=cos u`. At `u=2π`, its norm
is one, while `exp(-c τ²u²)<1` for every `c>0`. Thus the source low-frequency
domain cannot be silently discarded, nor can the high-frequency problem
be solved by applying a Gaussian bound at all frequencies.
The same obstruction survives normalization: for the fair law on
`{-a,a}`, `a>0`, resonance occurs at `u=2π/a`, while `τ²=a²`. Taking
`a=1/√n` gives the source second-moment scale without removing the
resonance.

**B3 — the quadratic frequency restriction matters.** For the fair law
on `{0,1}`, `τ²=1/4>0`. At `v=-u`, the phase `uA+vA²` vanishes on both
atoms, hence `φ(u,-u)=1` for every real `u`. Thus even arbitrarily small
nonzero `u` cannot have the desired Gaussian damping without control of
`v` relative to `u`. This is precisely why the actual source's
`|v|≤κ|u|/γ` low-frequency strip or its relevant cone may not be omitted.

**B4 — the two phase coordinates are not independent.** For the same fair
law on `{0,1}`, take `u=v=π`. The true coupled phase is `2πA`, so `φ=1`.
But separately averaging `exp(iπA)` and `exp(iπA²)` gives zero in each
factor. Replacing the true joint characteristic function by their product
would give zero and be false. The actual finite iid factorization is
across independent observations, not across `A` and `A²`.

**B5 — origins and degeneracy.** At `u=0`, `d(0,v)=0` and the remainder
bound is zero. Its derivative generally still has the `v`-dependent error
measured by `2m3|v|`; no cancellation of that term is assumed. Under
`ν=δ_0`, `m3=0`, `φ=1` and all odd quantities vanish. For `n=0`, the
finite iid factor is one. These valid cases require no positive variance
or nonzero frequency premise.

**B6 — partial reflection is not complex conjugation.** In general
`φ(-u,v)` is not the conjugate of `φ(u,v)`; the valid joint-characteristic
conjugation reverses both frequencies. For `ν=δ_1`, `u=0`, `v=π/2`,
`φ(-u,v)=i` whereas `conj(φ(u,v))=-i`. The candidate must keep the energy
frequency fixed in its actual odd difference, exactly as the source does.

## Exact nonclosure boundary and next consumers

This is an actual analytic input for the odd part; it does **not** claim
the full comparison or even full low-frequency decay.

The next damping lemma remains the source statement
`h:supp:lowfreq`, `supplement.tex:2371–2377`, with its exact domain:

```text
there exist absolute κ,c>0 such that
|u| <= κ/γ and |v| <= κ|u|/γ
imply |φ(±u,v)| <= exp(-c τ²u²).
```

Its actual proof at `supplement.tex:3155–3192` preserves most of the
independent-pair variance after truncating at
`d0=min(c/|u|, |u|/(4|v|))`, derives the real cosine spectral gap, and
then obtains the exponential bound. No such pointwise Fourier bound,
variance-retention statement or clock probability is an assumption of any
candidate signature above.

The eventual low-frequency power estimate must combine the candidate
actual odd estimates with that independently proved damping and genuine
individual `φ_u,φ_uu` controls. The short-time derivative table is not
closed by the present seven theorems alone.

At high frequencies the lattice counterexample persists. The source
uses the actual law-adapted biased-pair/chord smoothing multiplier `Xi`,
the **cone-restricted** comparison

```text
(4/9)(1-|φ|²)/(τ²u²) <= K <= 4(1-|φ|²)/(τ²u²),
```

and its finite-power gap optimization to obtain polynomial damping
(`main.tex:691–721`). The actual noise, quotient at zero, cone comparison,
outside-cone oscillatory integrals, Fourier inversion/differentiation,
complex tilting, Gaussian tail comparison and final defect payment remain
open dependencies. They are not suppressed by choosing a polynomial
real-plane error bound that happens to hold at all frequencies.

Finally, the original strict CDF test remains
`1_{q>0, abs(w)<t sqrt(q)}`. A generic bounded-test Duhamel identity and
the new characteristic-function estimates do not remove the `q>0`
restriction, change strict boundaries, or give the error when replacing
that test with the smoothed `H_y`/fixed-noise test. That passage still needs
the source clock/concentration and smoothing/anti-concentration work.

## Work ledger and next action

| Item | Status |
|---|---|
| Actual φ, real odd bounds, their source proofs and downstream use read | COMPLETE |
| Quantitative constants `1/3,2,1,2` independently derived from elementary remainders | CHECKED algebraically; not Lean-verified candidate proofs |
| Existing cached API probe | EXIT 0 after correcting namespaces; no candidate declarations |
| Parameter integral module | Exact missing module reported to root; no author cache write |
| B1–B6 boundary/altered-statement checks | Exact examples recorded |
| Candidate independent statement review/freeze | PENDING |
| Candidate implementation | NOT STARTED |
| Low/high-frequency damping, clock bound, smoothing and root comparison | OPEN; not premises of this unit |

Minimum next action: independently review and freeze this one definition
and seven theorem signatures, then authorize implementation. All later
Lean checks, axiom scans and recomputation must remain on the server.
