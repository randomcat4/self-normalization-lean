# Real odd-power difference and its low-frequency derivative table

Status: PROPOSED FOR INDEPENDENT STATEMENT REVIEW. This file is the only new
deliverable. No candidate implementation has been written or compiled. The
server checks below are read-only API probes, not verification of the proposed
theorems. All previously frozen sources remain unchanged.

## Source binding and selected next dependency

Read-only paper snapshot SHA256:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

The next independently closable dependency is the actual real-frequency
finite-power difference and the table `h:supp:oddpowerderivatives`. The earlier
zeroth-order consumer must be covered by the same interface. The object is
the difference of two powers of the true characteristic function, not the
odd part of a centered proxy law and not an odd integer exponent restriction.
Every natural exponent is allowed in the residual-power theorem.

Exact source anchors:

* `main.tex:546–551`, `h:eq:conditionallaw`: the increment law is the true
  conditional law `A = ξ | {|ξ|≤h_x}`. Its conditional mean need not be zero.
* `main.tex:622–625`, `h:eq:Lambda`: `μ=E_x^*A`, `m_r=E_x^*|A|^r`,
  `τ²=m2−μ²>0`, `γ=m3/τ²`, and
  `Λ_y=(1+y)n|μ|+(1+y)^3 n m3`.
* `main.tex:673–678`, `h:eq:charfunctions`: the true phase is
  `φ(u,v)=E_x^* exp(iuA+ivA²)`, with real `u,v` in this unit.
* `supplement.tex:524–531`, `h:eq:momentbudget1/2/3`: source payment includes
  `3/4≤n m2≤4/3`, `1/2≤n τ²≤4/3`, the actual mean and third-moment budgets,
  and `m2≤γ²`. These are source claims about the same conditional law, not
  independent formal hypotheses that have already been discharged here.
* `supplement.tex:2343–2357`: `ℓ=n−i`, `T=ℓm2`; the Fourier factor is
  `φ(u,v)^ℓ`. The odd factor subsequently used in inversion is
  `D_ℓ=(1/2)(φ(u,v)^ℓ−φ(−u,v)^ℓ) Ξ(u,v)`. This proposal proves estimates
  for the difference before multiplication by `Ξ`.
* `supplement.tex:2371–2378`, `h:supp:lowfreqbound`: both `φ(u,v)` and
  `φ(−u,v)` have actual variance damping on
  `|u|≤κ/γ`, `|v|≤κ|u|/γ`.
* `supplement.tex:2383–2401`, `h:supp:oddcommon0/1/2` and
  `h:supp:powerdifference`: the real single-factor odd estimates and the
  polynomial identity
  `a^ℓ−b^ℓ=(a−b) Σ_{j<ℓ} a^(ℓ−1−j)b^j` are the inputs. The separate
  complex-shift part of `oddcommon0` is not included in this unit.
* `supplement.tex:2461–2462`: source constants satisfy `L2≥2J+4`, and
  `T≥L2 γ²`, `m2≤γ²` imply `ℓ≥L2`. Here `J=8`, so the source range
  has `ℓ≥20`; it lies inside the proposed normalized range `6≤ℓ`.
* `supplement.tex:2477–2484`: the first unresolved consumption is
  `|φ(u,v)^ℓ−φ(−u,v)^ℓ|≤C exp(−cTu²)
  {ℓ|μ||u|+ℓm3(|u|³+|uv|)}` on the low-frequency region.
* `supplement.tex:2593` requires `D_ℓ''` and `(uE_ℓ)''` after integration
  by parts. `2614–2617`, `h:supp:powerglobal`, has already been handled
  by the accepted finite-power derivative module; it is not reimplemented.
* `supplement.tex:3420–3459`: the source proof first uses
  `|φ_u−iμ|≤|u|m2+|v|m3`, `|φ_uu|≤m2`, and then the table
  `h:supp:oddpowerderivatives` at `3441–3447`. Its coefficients are
  `a_ℓ=ℓ|μ||u|+ℓm3(|u|³+|uv|)` and
  `b_ℓ=ℓ|μ|+ℓm3(u²+|v|)`.
  The three rows, each multiplied by `C exp(−cTu²)`, are
  `a_ℓ`, `b_ℓ+sqrt(T)(1+sqrt(T)|u|)a_ℓ`, and
  `ℓm3|u|+sqrt(T)(1+sqrt(T)|u|)b_ℓ+T(1+Tu²)a_ℓ`.
  The proof explicitly counts the first and second derivatives of the
  finite geometric sum and retains `n|μ|≤Λ_y<η0/2`.
* `supplement.tex:2860–2863` fixes `η0≤1/16`. Thus `n|μ|≤1` in the
  normalized interface is a sufficient weakening of the source payment,
  not a zero-mean assertion. `3461` onward additionally differentiates
  the noise and integrates; those steps remain separate.

The source uses unspecified absolute constants. The proposed source-ready
table supplies explicit sufficient constants `2,4,18` and damping exponent
`1/256`. These are auxiliary formal constants, not quotations of numerical
constants from the paper and not claims of optimality.

## Accepted dependencies and exact reuse

These actual sources were read, and their hashes were checked against the
server `lead-c12` copies:

```text
Shao/Probability/QuadraticCharacteristic.lean
  8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5
Shao/Probability/QuadraticCharacteristicPower.lean
  5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8
Shao/Probability/LowFrequencyDamping.lean
  ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65
```

Reuse `quadraticChar ν u v` literally:

```lean
∫ a : ℝ, Complex.exp
  (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν
```

* `quadraticChar_odd_bound` already gives the single-factor zeroth-order
  coefficient with the true mean and true third absolute moment.
* `quadraticChar_odd_derivative_bounds` already gives
  `‖d'−2iμ‖≤m3(u²+2|v|)` and `‖d''‖≤2m3|u|` for
  `d(r)=χ(r,v)−χ(−r,v)`. It also has the required actual integral
  `HasDerivAt` companions. None will be reproved.
* `iid_quadraticChar_power_hasDerivAt` and
  `iid_quadraticChar_power_deriv_hasDerivAt` provide actual first/second
  integral derivatives, with genuine finite second-moment domination.
  Specialize to `ℓ=1`, `Ω=ℝ`, `X : Fin 1 → ℝ → ℝ := fun _ => id`,
  probability `ν`. Subsingleton independence and `IdentDistrib.refl`
  give the hypotheses. This recovers the actual single-coordinate
  derivatives and their differentiability at every real point without a
  new differentiation-under-integral proof or a duplicate finite-power
  iid identity.
* `quadraticChar_power_derivative_bounds` at `ℓ=1` also immediately
  bounds the second derivative by
  `(m2−μ²)+μ²=m2`. It needs no new fourth moment.
* `quadraticChar_lowFrequency_damping` supplies, under the exact closed
  frequency hypotheses below,
  `‖χ(u,v)‖, ‖χ(−u,v)‖ ≤ exp(−V u²/32)`.
  Here `V` is Mathlib's actual variance. Its positivity and finite third
  absolute moment imply `m3>0`; consequently `γ=m3/V>0` must be derived
  before using any real division in the proof.
* Probability and `h3` imply actual integrability of `a` and `a²`, and
  `V=m2−μ²`, `0≤V≤m2`. These facts will be derived, not supplied as
  additional mean-zero, Jensen or moment hypotheses.

## Proposed public API: zero definitions, three theorems

Future module: `Shao/Probability/QuadraticCharacteristicOddPower.lean`.
Namespace `Shao.Probability`; `open MeasureTheory ProbabilityTheory`;
`set_option autoImplicit false`.

All frequencies and all actual moments in these signatures are real. Norms
on values and derivatives are complex norms. Derivatives are with respect
to the real first frequency; `ν`, `v` and the exponent stay fixed.

### 1. Single-coordinate derivative payment

```lean
theorem quadraticChar_single_derivative_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν) (u v : ℝ) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let f : ℝ → ℂ := fun r => quadraticChar ν r v
    ‖deriv f u - Complex.I * (μ : ℂ)‖ ≤ m2 * |u| + m3 * |v| ∧
      ‖deriv (fun r : ℝ => deriv f r) u‖ ≤ m2
```

This is the missing individual derivative estimate actually used at source
lines `3431–3436`. It allows zero variance and atomic/constant laws. In
particular, it does not assume the conditional mean is zero. The first
derivative itself is bounded by `|μ|+m2|u|+m3|v|` by the triangle
inequality; there is no need for a fourth public statement for that step.

### 2. Exact residual-power jet bounds, including exponents 0, 1, 2

```lean
theorem quadraticChar_odd_power_residual_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (ℓ : ℕ) (u v : ℝ)
    (hu : |u| ≤ (1 / 128 : ℝ) /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν))
    (hv : |v| ≤ (1 / 128 : ℝ) * |u| /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν)) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let q : ℝ := Real.exp (-(variance (id : ℝ → ℝ) ν) * u ^ 2 / 32)
    let a0 : ℝ := 2 * |μ| * |u| + m3 * (|u| ^ 3 / 3 + 2 * |u| * |v|)
    let a1 : ℝ := 2 * |μ| + m3 * (u ^ 2 + 2 * |v|)
    let a2 : ℝ := 2 * m3 * |u|
    let L : ℝ := |μ| + m2 * |u| + m3 * |v|
    let N : ℝ := (ℓ : ℝ)
    let N1 : ℝ := ((ℓ - 1 : ℕ) : ℝ)
    let N2 : ℝ := ((ℓ - 2 : ℕ) : ℝ)
    let d : ℝ → ℂ := fun r =>
      (quadraticChar ν r v) ^ ℓ - (quadraticChar ν (-r) v) ^ ℓ
    ‖d u‖ ≤ N * a0 * q ^ (ℓ - 1) ∧
      ‖deriv d u‖ ≤
        N * a1 * q ^ (ℓ - 1) +
          N * N1 * L * a0 * q ^ (ℓ - 2) ∧
      ‖deriv (fun r : ℝ => deriv d r) u‖ ≤
        N * a2 * q ^ (ℓ - 1) +
          2 * N * N1 * L * a1 * q ^ (ℓ - 2) +
          N * N1 * m2 * a0 * q ^ (ℓ - 2) +
          N * N1 * N2 * L ^ 2 * a0 * q ^ (ℓ - 3)
```

The natural subtractions occur before casts, exactly as displayed. There
is no division by `χ(u,v)`, `χ(−u,v)`, their difference, `ℓ` or `T`.
This is a true estimate of the actual power difference, not a generic
bound which assumes the desired odd-power estimates as premises.

The interpretation of the coefficients is explicit. Write
`f(r)=χ(r,v)`, `g(r)=χ(−r,v)`, and
`H_ℓ(r)=Σ_{j<ℓ} f(r)^j g(r)^(ℓ−1−j)`. Then
`d=(f−g)H_ℓ`. The required counts for `H_ℓ,H_ℓ',H_ℓ''` are respectively

```text
ℓ,
ℓ(ℓ−1),
ℓ(ℓ−1) with one second derivative,
ℓ(ℓ−1)(ℓ−2) with two first derivatives.
```

The cross term in `d''` has coefficient 2. The remaining numbers of
undifferentiated factors are respectively `ℓ−1`, `ℓ−2`, `ℓ−3`, which
explain the three residual powers of `q`. These counts remain natural
counts at the small exponents.

### 3. Source-ready three-row low-frequency table

```lean
theorem quadraticChar_odd_power_lowFrequency_normalized (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (n ℓ : ℕ) (hℓ : ℓ ≤ n) (hℓ6 : 6 ≤ ℓ)
    (hscale : (3 / 4 : ℝ) ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν)
    (hbias : (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ 1)
    (hcomp : (∫ a : ℝ, a ^ 2 ∂ν) ≤ 4 * variance (id : ℝ → ℝ) ν)
    (u v : ℝ)
    (hu : |u| ≤ (1 / 128 : ℝ) /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν))
    (hv : |v| ≤ (1 / 128 : ℝ) * |u| /
      ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν)) :
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let T : ℝ := (ℓ : ℝ) * m2
    let A : ℝ := (ℓ : ℝ) * |μ| * |u| +
      (ℓ : ℝ) * m3 * (|u| ^ 3 + |u| * |v|)
    let B : ℝ := (ℓ : ℝ) * |μ| + (ℓ : ℝ) * m3 * (u ^ 2 + |v|)
    let R : ℝ := Real.sqrt T * (1 + Real.sqrt T * |u|)
    let E : ℝ := Real.exp (-T * u ^ 2 / 256)
    let d : ℝ → ℂ := fun r =>
      (quadraticChar ν r v) ^ ℓ - (quadraticChar ν (-r) v) ^ ℓ
    ‖d u‖ ≤ 2 * E * A ∧
      ‖deriv d u‖ ≤ 4 * E * (B + R * A) ∧
      ‖deriv (fun r : ℝ => deriv d r) u‖ ≤
        18 * E * ((ℓ : ℝ) * m3 * |u| + R * B + T * (1 + T * u ^ 2) * A)
```

This has exactly the actual three source row shapes, with one possible
common source constant `C=18`, `c=1/256`. The lower length `6` is a
sufficient convenient choice for paying three removed factors; it is
weaker than the actual source's `ℓ≥20`, not a claimed sharp threshold.
There is no requirement that the exponent itself be an odd number.

`hcomp` is a numerical raw/variance comparison, not an assumed damping
conclusion. The source's `n m2≤4/3`, `nV≥1/2` imply
`m2≤(8/3)V≤4V`, since those same inequalities imply `n>0`.
The normalized theorem does not need the additional source upper bound
on `n m2`, nor the time upper bound `T<y²`: they are needed elsewhere.
Source-specific discharge of these moment conditions is owned by
`SourceTruncationBridge`; this unit neither changes its proposal nor
asserts those obligations have already been closed.

## Proof decomposition and explicit constant payment

1. Derive first/second integrability from `h3` under the real probability
   law. Specialize the accepted true finite-power derivative theorems to
   the singleton iid sample for differentiability and the first derivative
   integral. Subtract `iμ` inside a genuinely integrable difference. The
   existing real phase inequality gives
   `|a| |exp(i(ua+va²))−1|≤|u|a²+|v||a|³`.
   Integrate this bound. Obtain the second bound from the accepted power
   second-derivative estimate at length 1. No new dominated integral
   theorem is introduced.
2. Prove a private deterministic finite geometric-sum derivative estimate
   for two twice differentiable complex functions, using the polynomial
   identity and the counts above. Such a private lemma may use jet bounds
   for its inputs; the public theorem must derive them for the actual
   `quadraticChar` using the accepted odd and damping theorems and public
   theorem 1. The private statement is not a proxy law or a public
   assumption of the desired difference estimate.
3. Both `u` and `−u` satisfy the same closed low-frequency inequalities.
   For `g(r)=χ(−r,v)`, keep `g'(u)=−χ_u(−u,v)` and
   `g''(u)=χ_uu(−u,v)`; the second derivative has positive chain sign.
   The bounds on `f−g`, `(f−g)'`, `(f−g)''` are exactly `a0,a1,a2`.
4. For the normalized theorem put `V=Var[id;ν]`. Derive
   `m3|v|≤V|u|/128≤m2|u|/128`, hence
   `L≤|μ|+2m2|u|`. From `ℓ≤n`, the scale lower bound and drift budget,
   derive `(ℓ|μ|)²≤(4/3)T`, hence `ℓ|μ|≤2sqrt(T)` and `ℓL≤2R`.
   These are algebraic payments from the actual moment assumptions; none
   is a premise asserting the target power derivative estimate.
5. For `j=1,2,3` and `ℓ≥6`, `ℓ−j≥ℓ/2`. Since `m2≤4V`,
   `q^(ℓ−j)≤exp(−T u²/256)=E`. This uses only positivity of an actual
   real exponential, not nonvanishing of the characteristic function.
6. Write `N=(ℓ:ℝ)`. Directly, `N*a0≤2A`, `N*a1≤2B`,
   `N*a2=2N*m3*|u|`, `N1≤N`, `N2≤N`. Therefore the three residual
   bounds are at most

   ```text
   E · 2A,
   E · (2B+4RA),
   E · (2N m3|u|+8RB+2TA+8R²A).
   ```

   Since `R²≤2T(1+Tu²)`, the last display is bounded by the stated
   `18 E {N m3|u|+RB+T(1+Tu²)A}`. This accounts for every coefficient,
   including the mixed first-derivative term.

The argument is finite polynomial differentiation plus real moment and
exponential inequalities. It does not redo the already accepted finite
iid sum-square computation or finite-power integral differentiation.

## Boundaries, drift and actual-law interpretation

* `ℓ=0`: the actual difference is `1−1=0`; both derivatives vanish.
  Every residual right-hand term has the outer factor `N=0`.
* `ℓ=1`: the actual difference is the accepted single-factor odd part.
  `N1=0`; only `a0,a1,a2` remain, with `q^0=1`.
* `ℓ=2`: the one-differentiated-factor terms remain, while `N2=0`
  removes the nonexistent two-first-derivative terms in `H_2''`.
  At `ℓ=3`, the last residual damping factor is correctly `q^0=1`.
  Natural truncation must be preserved; `((ℓ−1:ℕ):ℝ)` is not replaced
  by `(ℓ:ℝ)−1` at zero, nor `N2` by `N−2` at small exponents.
* The normalized theorem is explicitly restricted to `ℓ≥6`. The residual
  theorem supplies all smaller lengths; no uniform positive Gaussian
  fraction for the nonexistent residual factors is asserted there.
* `n=0` is incompatible with the normalized positive scale and length
  inputs, as a derived fact. The law-only and residual statements do not
  introduce an unnecessary sample-size parameter or hidden nonempty set.
* Real negative `u,v` are included. The frequency boundaries are closed
  `≤`, just as in the accepted damping theorem. In the damping region,
  `u=0` forces `v=0`, because `γ>0`. Then `d(0)=d''(0)=0`, but in
  general `d'(0)=2 i ℓ μ`. Thus its bound must retain `ℓ|μ|` in `B`.
  A biased two-point law with positive variance already prevents deleting
  that term. This is not an implicit centering approximation.
* Atomic laws and zeros of `χ` are allowed. A nondegenerate atomic law
  can satisfy all damping assumptions. The proof is polynomial even
  where `χ=0`, so logarithmic differentiation and `χ'/χ` are prohibited.
  The single-coordinate theorem also allows `V=0`; the local damping
  statements require `V>0` explicitly, matching the source definition of
  `γ`. No claim about `0/0` frequencies for a constant law is made.
* The three generic theorems can be instantiated with any actual
  probability law satisfying their hypotheses. In the intended consumer
  `ν` must be the one fixed true conditional truncated increment law.
  It is not the original untruncated law and not the later exponential
  tilted law. `h3` is integrability under that very same `ν`; it imposes
  no global third absolute moment on the original variable, no fourth
  moment, no mean-zero premise and no uniformity over a moving law.
* Bounded cutoff support is not required by these analytic statements.
  When used for the true truncated law it supplies actual `h3`; the
  source moment bridge must also pay scale, bias, variance comparison
  and positive variance. No boundedness assertion is silently used to
  replace a missing hypothesis.

## Server API evidence and cache requirements

Read-only source searches and a corrected successful server `--stdin`
probe used the project-pinned Lean `4.36.0-rc1` and Mathlib
`807d3836b165983210ee2ecf3cd28f239436949c`. The successful probe imported

```lean
import Shao.Probability.QuadraticCharacteristicPower
import Shao.Probability.LowFrequencyDamping
import Mathlib.Algebra.Ring.GeomSum
```

and checked these actual names; nested server `exit_code=0`, stderr empty:

```text
geom_sum₂_mul
Commute.mul_geom_sum₂
iIndepFun.of_subsingleton
HasDerivAt.pow
HasDerivAt.fun_sum
HasDerivAt.mul
HasDerivAt.scomp
Real.norm_exp_I_mul_ofReal_sub_one_le
Real.exp_nat_mul
norm_pow
norm_sum_le
```

`geom_sum₂_mul` is in `Mathlib/Algebra/Ring/GeomSum.lean:307–309` and
states `(Σ_{i<ℓ} x^i y^(ℓ−1−i))*(x−y)=x^ℓ−y^ℓ` over a commutative
ring. `Commute.mul_geom_sum₂` at `195–197` has the difference on the
left and needs no division or inequality between the two elements.
`HasDerivAt.pow` is in `Analysis/Calculus/Deriv/Pow.lean:109`, finite
sum/product rules in `Deriv/Add.lean:218` and `Deriv/Mul.lean:254`.
`iIndepFun.of_subsingleton` is in `Probability/Independence/Basic.lean:245`.
The real phase bound is in `Analysis/SpecialFunctions/Trigonometric/Bounds.lean:286`.

An earlier API probe used the nonexistent name `Finset.norm_sum_le` and
returned Lean exit 1. It was corrected to the actual global name
`norm_sum_le`, and the repeated API probe above exited 0. Earlier search
paths `Algebra/GeomSum.lean` / `Algebra/GeomSum/` were likewise corrected
to the actual `Algebra/Ring/GeomSum.lean`. These were API discovery
failures, not candidate proof results. No candidate theorem has been
compiled or claimed checked. No new cache modules are currently needed;
all three intended imports were actually available. No cache files were
downloaded or changed, and no local Lean was run.

## Explicit remaining gaps and acceptance gates

This proposed unit closes the actual undressed real low-frequency
odd-power estimate and its first two derivative bounds. It does not
close derivatives of the noise `Ξ`, noise construction, high-frequency
damping at lattice resonances, complex frequencies or exponential
tilting, oscillatory inversion, regional integrals, smoothing removal,
clock specialization at `h_x`, a Gaussian comparison, or C1/C2.
The half-factor and the product with actual `Ξ` in `D_ℓ` still require
the ordinary product rule with separately established noise estimates.

Minimum next step: independent semantic statement review and root freeze
of these zero-definition / three-theorem signatures. Only then implement
the new module. Reuse the accepted `.olean` dependencies; check only the
new target on the server. Acceptance must include fresh statement review,
target compilation, small-exponent and original-mean semantic checks,
module-ownership enumeration of all new declarations, the full actual
project dependency axiom gate against only `propext`, `Classical.choice`,
`Quot.sound`, forbidden-source scan and exact source SHA256. Progress
after freeze belongs in a separate receipt; this proposal's bytes must
not be rewritten to describe a changed theorem.
