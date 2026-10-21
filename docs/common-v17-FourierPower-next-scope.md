# Actual finite-power characteristic derivatives and normalized time scale

Status: PROPOSED FOR INDEPENDENT STATEMENT REVIEW. No candidate Lean source
has been written, elaborated or compiled. This proposal and read-only server
API probes are the only new work in this unit. Frozen sources are unchanged.

## Selected source claim and exact dependency boundary

The next independently closable analytic unit is the whole-real-plane
assertion `h:supp:powerglobal`, specifically its genuine finite-sum moment
payment. This is part (d) of `h:supp:highderivatives`, rather than the
Gaussian-damped odd-power table or its cone-restricted high-frequency part.

Read-only source snapshot SHA256:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

Literal source anchors:

* `main.tex:546–551`, `h:eq:conditionallaw`: the actual increments are iid
  under the true conditional law `A = ξ | {|ξ|≤h_x}`; explicitly,
  `The conditional mean need not be zero.`
* `main.tex:553–556`, `h:eq:boundedstatistics`:
  `S_i=\sum_{j=1}^i A_j,\qquad Q_i=\sum_{j=1}^i A_j^2,\qquad S_0=Q_0=0.`
* `main.tex:574–578`: the future copy has genuine sums `S'_ℓ,Q'_ℓ` and
  `S'_0=Q'_0=0`.
* `main.tex:622–625`: `μ=E_x^* A`, `m_r=E_x^*|A|^r`,
  `τ²=m_2-μ²`, and `Λ_y=(1+y)n|μ|+(1+y)^3nm_3`.
* `main.tex:673–678`, `h:eq:charfunctions`:
  `\varphi(u,v)&=\E_x^*e^{\ii uA+\ii vA^2}`.
* `supplement.tex:2343–2351`: `T=(n-i)m_2`, `T≤4/3`, and the true future
  Fourier factor is `φ(u,v)^(n-i)`.
* `supplement.tex:2614–2617`, `h:supp:powerglobal`:
  `On the whole real plane,`
  `|\partial_u^a\varphi(\pm u,v)^{n-i}|\le CT^{a/2},\qquad a=0,1,2.`
* Its actual proof is `supplement.tex:3403–3417`, not an unproved
  power-differentiation formula. It says
  `\E_x^*|S_{n-i}-(n-i)\mu|\le\tau\sqrt{n-i}` and
  `\E_x^*\{S_{n-i}-(n-i)\mu\}^2=(n-i)\tau^2`, then
  `Differentiate the characteristic function of $(S_{n-i},Q_{n-i})$.`
  The resulting bounds are
  `|\partial_u\varphi(u,v)^{n-i}|≤τ√(n-i)+(n-i)|μ|`
  and
  `|\partial_u^2\varphi(u,v)^{n-i}|≤(n-i)τ²+(n-i)^2μ²`.
  Finally it uses `(n-i)τ² asymp T` and
  `(n-i)|μ|≤CT n|μ|≤C√T`.
* `supplement.tex:524–527`, `h:eq:momentbudget1/2` gives
  `3/4≤nm_2≤4/3`, and an actual bound on `n|μ|`.
  `supplement.tex:3398–3400` and `3453–3457` state the relevant small
  drift input `n|μ|≤Λ_y<η_0/2`; the fixed choice in `2860–2863` includes
  `η_0≤1/16`. Thus the proposed normalized specialization `n|μ|≤1`
  follows from the source's own budget; it is not a centering assumption.
* The consumers are `supplement.tex:2593`, which needs the actual second
  derivatives after two integrations by parts, and the subsequent regional
  bounds using part (d). The separate low-frequency table
  `supplement.tex:3441–3459` additionally calls the odd estimates,
  individual characteristic derivatives and actual low-frequency damping.
  The present unit closes the global (d) input, not that full table.

The proposed source-level theorem is actually stronger than the source's
unspecified absolute `C`: its zeroth, first and second bounds have explicit
constants `1,2,3`, respectively. The proof needs only finite second moment
of the fixed true increment law. No third/fourth moment, bounded support,
positive variance or centering is required for this real-plane unit.

## Reuse of the accepted finite iid moment module

The following accepted OQ56 source was read directly on the server:

```text
Shao/OQ5/P35/FiniteIIDMoments.lean
SHA256 4b2c65ec7fb03767b6a469ef5918592c9a76e993ad95262e6a7aae6840c4520b
namespace Shao.OQ5.P35
```

Its public `finite_iid_sumSquare_integral` at lines 407–426 proves the exact
generic identity

```text
E(S_ℓ²) = ℓ m2 + ℓ ((ℓ-1 : ℕ) : ℝ) μ²
```

from genuine measurability, iid/common-law inputs and `MemLp id 2 ν`, for
every natural `ℓ`, including zero, with arbitrary mean. Its
`finiteFeatureSum` is literally the coordinate sum, so it equals the
already shared `prefixSum (samplePath X ω) ℓ`. Its proof already handles
the natural subtraction at `ℓ=0` correctly. It must be **reused**, not
reproved in another C1/C2 module. The centered identity needed here is a
short algebraic consequence of that identity and the actual first moment
`E S_ℓ=ℓμ`, rather than another competing iid-moment theorem.

There is a packaging prerequisite: the source and its `.olean` are not
currently present in `lead-c12`, and the theorem/coordinate-sum definition
are in an OQ5 namespace importing OQ5 `RowIdentity`. Root should either
provide an approved shared entry point for this accepted generic theorem,
or explicitly authorize consuming the frozen OQ5 module. The recommended
sharedization is a coordinator-owned decision; this author has not moved,
copied or edited the accepted source, recreated its identity, or created a
new shared interface. Public signatures proposed below are independent
of that packaging decision and use the existing common path definitions.

## Proposed public API: no new definitions, five theorems

Future file: `Shao/Probability/QuadraticCharacteristicPower.lean`.
Namespace `Shao.Probability`, `open MeasureTheory ProbabilityTheory`,
`set_option autoImplicit false`.

Reuse the already frozen `quadraticChar`, `samplePath`, `Shao.prefixSum`,
`Shao.energy`, and `iid_quadraticChar_factor`. No surrogate characteristic
function, recursively defined future law or free moment parameters are
introduced. In all signatures below the law `ν` is fixed as `u` varies.

### 1. First derivative as the genuine finite-sample integral

```lean
theorem iid_quadraticChar_power_hasDerivAt
    {ℓ : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin ℓ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => (quadraticChar ν r v) ^ ℓ)
      (Complex.I * ∫ ω,
        (Shao.prefixSum (samplePath X ω) ℓ : ℂ) *
          Complex.exp
            (((u * Shao.prefixSum (samplePath X ω) ℓ +
                v * Shao.energy (samplePath X ω) : ℝ) : ℂ) * Complex.I) ∂μ) u
```

### 2. Actual second derivative as the genuine square-sum integral

```lean
theorem iid_quadraticChar_power_deriv_hasDerivAt
    {ℓ : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin ℓ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => deriv (fun s : ℝ => (quadraticChar ν s v) ^ ℓ) r)
      (-(∫ ω,
        ((Shao.prefixSum (samplePath X ω) ℓ ^ 2 : ℝ) : ℂ) *
          Complex.exp
            (((u * Shao.prefixSum (samplePath X ω) ℓ +
                v * Shao.energy (samplePath X ω) : ℝ) : ℂ) * Complex.I) ∂μ)) u
```

These are genuine real-parameter derivatives of the actual power,
identified through the already proved true iid integral factor. They do
not merely restate the chain rule with unknown bounds on `φ_u,φ_uu`.

### 3. Moment-paid, mean-sensitive whole-power bounds

```lean
theorem quadraticChar_power_derivative_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (ℓ : ℕ) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let V : ℝ := m2 - μ ^ 2
    let f : ℝ → ℂ := fun r => (quadraticChar ν r v) ^ ℓ
    ‖deriv f u‖ ≤ Real.sqrt ((ℓ : ℝ) * V) + (ℓ : ℝ) * |μ| ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤
        (ℓ : ℝ) * V + (ℓ : ℝ) ^ 2 * μ ^ 2
```

Here `V` is the actual raw-second-moment minus actual squared mean;
`V≥0` and its equality to Mathlib variance must be derived from `h2` and
probability, not asserted as extra premises. In particular no `V>0`
assumption is needed. This is exactly the source's two moment-paid bounds,
including its drift term, with `sqrt(ℓ V)=τ sqrt ℓ` where `τ=sqrt V`.

### 4. Explicit general normalization and bias payment

```lean
theorem quadraticChar_power_derivative_scale_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (n ℓ : ℕ) (hℓ : ℓ ≤ n) (θ B : ℝ)
    (hθ : 0 < θ)
    (hscale : θ ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν)
    (hbias : (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ B)
    (u v : ℝ) :
    let T : ℝ := (ℓ : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν
    let f : ℝ → ℂ := fun r => (quadraticChar ν r v) ^ ℓ
    ‖deriv f u‖ ≤ Real.sqrt (1 + B ^ 2 / θ) * Real.sqrt T ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤ (1 + B ^ 2 / θ) * T
```

The theorem derives `B≥0`, `n>0`, `m2>0` and `T≥0` when needed; these are
not extra inputs. Neither the desired full derivative bounds nor finite
sum moments appear among the hypotheses. There is no arbitrary unrelated
time parameter: `T` is literally `ℓ m2`. `ℓ≤n` is the source future-length
condition; in the application `ℓ=n-i` for `0≤i≤n`.

The sharper first bound here comes from
`E|S_ℓ|≤sqrt(E S_ℓ²)` and the actual raw iid square identity. The key
scale payment is

```text
ℓ² μ² ≤ (B²/θ) (ℓ m2),
E S_ℓ² = ℓ(m2-μ²)+ℓ²μ² ≤ (1+B²/θ)T.
```

For `ℓ=0` both sides are zero and no division by `ℓ` or `T` is used.
For positive `ℓ`, a proof may safely establish the relevant positivity
before division. The theorem is also valid without the source upper bound
`nm2≤4/3`: the displayed lower normalization and the full-sample drift
budget already suffice. Omitting an unnecessary upper bound here does not
claim that its separate downstream consumers have been proved.

### 5. Source-ready all-plane `±u` bounds with constants 1,2,3

```lean
theorem quadraticChar_power_global_normalized (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (n ℓ : ℕ) (hℓ : ℓ ≤ n)
    (hscale : (3 / 4 : ℝ) ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν)
    (hbias : (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ 1)
    (σ u v : ℝ) (hσ : |σ| = 1) :
    let T : ℝ := (ℓ : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν
    let f : ℝ → ℂ := fun r => (quadraticChar ν (σ * r) v) ^ ℓ
    ‖f u‖ ≤ 1 ∧
      ‖deriv f u‖ ≤ 2 * Real.sqrt T ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤ 3 * T
```

Taking `σ=1` or `σ=-1` gives precisely the real `±u` assertion, with the
correct chain-rule sign in the first derivative and its square in the
second. The general normalization gives `1+B²/θ=7/3` at `θ=3/4,B=1`,
so `sqrt(7/3)≤2` and `7/3≤3` give the displayed constants. This proves
the whole-plane assertion `a=0,1,2` with one uniform absolute `C=3`.
There is no low-frequency strip or cone premise and no `u≠0` premise.

## Proof obligations: moments and dominated differentiation

For the two sample-integral identities, set
`S(ω)=prefixSum (samplePath X ω) ℓ` and
`Q(ω)=energy (samplePath X ω)` using existing definitions only.

1. From `h2` and measurability of real identity derive `MemLp id 2 ν`
   using `memLp_two_iff_integrable_sq`. Transport it to every actual
   coordinate via `IdentDistrib.memLp_iff`; then finite summation gives
   `MemLp S 2 μ`. Probability and L2 give actual `Integrable S`,
   `Integrable |S|`, and `Integrable S²` before integral linearity.
2. The true sample phase has norm one. Its first and second `u`
   derivatives have norms `|S|` and `S²`. Their actual integrability and
   measurability follow from the preceding step. Use the globally valid
   derivative dominators `|S|` and `S²` in the cached dominated
   parameter-integral theorem, on `s=univ`. No integrability of `Q²`,
   global fourth moment, or third moment is needed: only `u` varies.
3. Rewrite the original sample expectation as `(quadraticChar ν r v)^ℓ`
   with the already frozen `iid_quadraticChar_factor` for every real `r`.
   For the second theorem, identify the actual `deriv` using the first
   theorem at every `r` before applying the second dominated derivative.
4. Reuse the accepted finite iid square identity. Derive the actual mean
   by finite integral linearity and the marginal laws. Its centered form
   is `E(S-ℓμ)²=ℓV`. The real Cauchy–Schwarz bound is applied only after
   establishing L2 and probability. One cached proof route derives
   `(E|Y|)²≤E(Y²)` from `variance_nonneg` and `variance_eq_sub` for the
   L2 real variable `|Y|`, avoiding any new analytic library.
5. The first norm is at most `E|S|≤E|S-ℓμ|+ℓ|μ|`; the second is at most
   `E S²=ℓV+ℓ²μ²`. This establishes the actual moment-paid bounds.
   For the sharper normalized result, instead use
   `E|S|≤sqrt(E S²)`, then the explicit algebraic budget above.
6. Law-only theorems use the genuine canonical finite product law `ν^ℓ`
   with the coordinate evaluation functions. Cached product-law APIs
   supply genuine iid and marginal laws; no invented independent copy
   or assumed moment identity is a public input. This route also includes
   the empty product correctly.

Private helper proofs and direct algebraic consequences are permitted;
recreating the accepted generic raw-square iid proof or another public
finite-sum convention is not part of this scope.

## Existing API and cache evidence

Actual server imports and corrected read-only `#check` probe succeeded
with exit 0, empty stderr, and no candidate declarations. The imports were

```text
Shao.Probability.QuadraticCharacteristic
Mathlib.MeasureTheory.Function.L2Space
Mathlib.Probability.Moments.Variance
```

The probe checked:

| API | Needed contribution |
|---|---|
| `memLp_two_iff_integrable_sq` | Convert the exact frozen square-integrability input to L2. |
| `MemLp.integrable`, `MemLp.integrable_sq`, `MemLp.norm` | Actual first/square/absolute moment integrability under probability. |
| `memLp_finsetSum` | Actual finite sum L2, no iid or centering shortcut. |
| `IdentDistrib.memLp_iff`, `IdentDistrib.integral_eq` | Transport actual common-law moments to the observations. |
| `variance_nonneg`, `variance_eq_sub` | Actual Jensen/Cauchy–Schwarz and the raw-to-centered moment bridge. |
| `HasDerivAt.cexp`, `.comp`, `.deriv` | Actual complex exponential derivatives with a real parameter. |
| `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | Two actual integral derivatives with genuine integrable dominators. |
| `iIndepFun_pi`, `measurePreserving_eval` | Canonical product observations and their actual common marginal. |
| `Real.sqrt_mul`, `Real.sq_sqrt`, `Real.sqrt_le_sqrt` | Exact square-root scale payment with proved nonnegativity. |

The initial exploratory probe included a few guessed convenience names
that did not exist (`integral_mul_le_L2_mul_L2`, `integral_sq_sqrt`,
`Real.sqrt_add_le`); none is an assumed dependency. The corrected probe
uses the existing variance and square-root APIs listed above.

Read-only artifact inspection found the following Mathlib modules present:

```text
Mathlib.MeasureTheory.Function.L2Space
Mathlib.Probability.Moments.Variance
Mathlib.Analysis.Calculus.ParametricIntegral
Mathlib.MeasureTheory.Integral.MeanInequalities
```

The exact Mathlib pin remains `807d3836b165983210ee2ecf3cd28f239436949c`.
No new Mathlib cache is currently requested. Only the accepted OQ56
generic-moment source/entry-point packaging described above is pending.
No cache retrieval, shared-interface edit or local Lean invocation occurred.

## Independent boundary and altered-statement checks

* **Zero future:** `ℓ=0` gives `φ^0=1`, both actual derivatives zero and
  `T=0`. There is no artificial positive-future restriction. In the
  generic sample identities all coordinate premises are vacuous, but the
  fixed law and `h2` remain well-defined inputs.
* **Zero full sample:** the general moment and integral-derivative theorems
  include it. In normalized theorems `n=0` is impossible because the
  strictly positive lower normalization would read `θ≤0`; this is derived,
  rather than concealed by division by `n`.
* **Degenerate law:** `ν=δ_0` is allowed in the unnormalized theorems;
  all derivative and moment bounds vanish. A constant nonzero law has
  `V=0` and derivatives of sizes `ℓ|μ|`, `ℓ²μ²`: the mean terms cannot be
  dropped even when the variance is zero.
* **Small mean budget is essential for uniform T scaling:** take the fair
  law on `{0,sqrt(2/n)}` for positive `n`, and `ℓ=n`. Then `nm2=1` and
  `V=1/(2n)>0`, but at `u=v=0` the first derivative norm is `sqrt(n/2)`
  and the second is `(n+1)/2`, while `T=1`. No uniform constants are
  possible from second-moment normalization alone. Here
  `n|μ|=sqrt(n/2)` violates the proposed bounded bias premise.
* **Lower second-moment normalization is also essential:** take the fair
  law on `{0,2/n}`, `ℓ=n`. Then `n|μ|=1`, but `T=nm2=2/n`; the first
  derivative norm at the origin is 1 and the second is `1+1/n`. They
  cannot be bounded by fixed multiples of `sqrt T,T` as `n` grows.
* **Future length must be tied to n:** with `n=1`, `ν=δ_1`, the lower
  normalization and bias bound hold, but letting `ℓ` grow gives derivatives
  `ℓ,ℓ²` and `T=ℓ`. Omitting `ℓ≤n` invalidates uniform T-scale constants.
* **Real frequencies only:** the phase has norm one for every real `u,v`,
  including zero, negative values and resonant lattice frequencies. This
  gives global polynomial derivative bounds, not Gaussian decay. Complex
  shifts and `v` differentiation have different domination requirements
  and are not consequences of this unit.
* **Natural subtraction:** the existing iid square identity contains
  `((ℓ-1:ℕ):ℝ)`. At zero this must not be replaced factorwise with
  `(ℓ:ℝ)-1`; the whole expression is still zero because of its outer `ℓ`.
  Any conversion to the polynomial centered form must split that boundary
  or reuse the accepted whole-expression proof.

These are exact algebraic checks of the hypotheses, not Lean proofs of the
proposed candidate. No source test, strict boundary, or zero-energy event
was modified in obtaining them.

## Explicit nonclosure and minimum next action

This candidate closes the actual whole-plane `h:supp:powerglobal` input
after the source normalization/bias hypotheses are supplied. It does not
close the Gaussian-damped odd-power table in `3441–3447`: that still needs
the actual low-frequency variance-retention/spectral-gap lemma and the
individual `φ_u,φ_uu` low-frequency controls. Cone-restricted high-frequency
derivative damping additionally needs the actual law-adapted noise and
finite-power gap optimization; lattice resonances are not removed here.

Also open: the source-specific conditional-law moment/budget specialization
at cutoff `h_x`, global clock probabilities, complex tilting, Fourier
inversion/oscillatory integration, smoothing cost back to the strict CDF
test `1_{q>0, |w|<t sqrt q}`, and the full C1/C2 comparison. The generic
frozen retained-law units at cutoff `1/x` must not be silently substituted
for the source's different `h_x` law.

Minimum next action: independent semantic review and freeze of these five
signatures, and coordinator selection of the already accepted generic iid
moment import/shared entry point. Only after that authorization should the
new module be implemented, with all elaboration, compilation, source-hash
gates and transitive axiom audits on the designated server. The original
proposal bytes must then remain fixed; progress belongs in a separate
receipt.
