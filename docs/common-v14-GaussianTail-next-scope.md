# Proposed actual standard-normal tail interface

Status: PROPOSED FOR INDEPENDENT STATEMENT REVIEW; no target implementation
has been written. This author owns only this scope and read-only server API
probes. The coordinator owns all cache preparation and shared interfaces.

## 1. Actual source need and selected scope

The two read-only sources are at `C:/game/shao/current/c12/`:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

| Actual anchor | Common consumption | Proposed output |
|---|---|---|
| Main 169-171 | Defines `Psi=PhiBar=1-Phi`, where `Phi,phi` are the standard normal CDF/density. | Use the real Mathlib probability law `gaussianReal 0 1` and its real density; prove the tail/CDF/integral identity. |
| Supplement 97-99 and 294; main 395-397 | Lower bounds by fixed normal tails; `PhiBar(0)=1/2`. | True positive tail, antitonicity, exact value at zero and reflection. |
| Supplement 1027-1029, `h:supp:mills` | `PhiBar(z)` comparable to `exp(-z^2/2)/(1+z)` for `z>=0`; also used at 818, 949, 1309 and 1369-1377. | Actual uniform Mills bounds with explicit constants, not an asymptotic axiom. |
| Supplement 205-211, `h:supp:conditionalcoarse` | After the separate bounded-random theorem, compare the retained threshold `y=sqrt(x^2-j)` to `x`. | A standalone actual normal-tail deletion-threshold comparison; no assumption of the probabilistic theorem. |
| Main 457-465, `h:eq:neighborhood` | For nonnegative neighboring thresholds `|t-x|<=1/(1+x)`, compare the normal weights. | Explicit two-sided local comparison with factor `exp(2)`. |
| Main 807-812, `h:eq:localerrorbound` | Uses `phi(u)/PhiBar(u)<=u+4`, then the existing budget factor eight to get `8 exp(4)`. | Prove the stronger hazard bound `phi/PhiBar<=1+u`, and local factor `exp(2)`; these imply the stated looser source constants. |

The first nontrivial missing deterministic analytic dependency is the Mills
and tail-comparison interface, not Berry--Esseen. It is shared by the C1 and
C2 comparisons, their truncation weights and their normal denominators.
This scope does not identify the Brownian absolute-maximum tail `H` with a
standard normal tail, nor does it prove a sample-path Gaussian comparison.

The selected batch is two actual definitions and seven public theorems.
The first three theorem interfaces reuse existing probability/integral
facts and elementary calculus. The new analytic step is one independently
provable weighted Gaussian integral identity yielding Mills bounds; only
the concrete combinations consumed above are added afterward.

## 2. Actual objects, no proxy assumptions

Proposed new file: `Shao/Probability/GaussianTail.lean`, namespace `Shao`,
`open MeasureTheory`, `autoImplicit false`. Candidate imports:

```text
Mathlib.Probability.Distributions.Gaussian.Real
Mathlib.Probability.CDF
Mathlib.MeasureTheory.Integral.IntegralEqImproper
Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
Mathlib.Analysis.Calculus.MeanValue
```

The definitions are exactly:

```lean
noncomputable def standardNormalDensity (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 x

noncomputable def standardNormalTail (x : ℝ) : ℝ :=
  ((ProbabilityTheory.gaussianReal 0 1) (Set.Ioi x)).toReal
```

The Gaussian variance argument is `1 : NNReal`, not a standard deviation
parameter. Thus the density is exactly

```text
phi(x) = (sqrt(2*pi))^(-1) * exp(-x^2/2),
```

by the existing `gaussianPDFReal` definition. The law is the actual
mean-zero, variance-one probability measure, not a distribution specified
through desired CDF, derivative or tail axioms. The real value of its
strict tail is used in the definition; the no-atom and CDF bridges below
make it the same `PhiBar=1-Phi` as the source at every real threshold.
No new standard-normal measure, CDF, abstract Mills ratio, or anonymous
positive normalizer is introduced.

## 3. Exact proposed public theorem signatures

### 3.1 Strict/weak/CDF/density-integral bridge

```lean
theorem standardNormalTail_representation (x : ℝ) :
    standardNormalTail x =
        ((ProbabilityTheory.gaussianReal 0 1) (Set.Ici x)).toReal ∧
      standardNormalTail x =
        1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x ∧
      standardNormalTail x =
        ∫ a : ℝ in Set.Ioi x, standardNormalDensity a
```

The actual law has no atoms because its variance is nonzero. The strict
tail in the definition and weak tail in the first output therefore agree,
without any no-atom hypothesis concerning the original increment law.
The CDF is Mathlib's actual CDF of the same Gaussian measure. The final
integral is with respect to real Lebesgue volume, not Gaussian measure.

### 3.2 Basic global range, monotonicity, zero and negative thresholds

```lean
theorem standardNormalTail_basic :
    Antitone standardNormalTail ∧
      standardNormalTail 0 = (1 / 2 : ℝ) ∧
      (∀ x : ℝ, 0 < standardNormalTail x ∧ standardNormalTail x < 1) ∧
      ∀ x : ℝ, standardNormalTail (-x) = 1 - standardNormalTail x
```

These are global real-threshold facts. They handle the zero and negative
boundaries explicitly. In particular for `x<=0`, the tail is at least one
half; for `x<0`, reflection reduces any needed comparison to the positive
side. No `1/(1+x)` Mills expression is claimed across its negative pole.

### 3.3 Actual density and tail derivatives

```lean
theorem standardNormal_derivatives (x : ℝ) :
    HasDerivAt standardNormalDensity (-x * standardNormalDensity x) x ∧
      HasDerivAt standardNormalTail (-standardNormalDensity x) x
```

Both derivatives hold at every real threshold, with genuine Lebesgue
density integrability established from the library. No differentiability,
CDF regularity, domination or integrability premise is imposed on the caller.

### 3.4 Uniform Mills bounds and the source-consumed hazard bound

```lean
theorem standardNormal_mills_bounds (x : ℝ) (hx : 0 ≤ x) :
    standardNormalDensity x / (1 + x) ≤ standardNormalTail x ∧
      standardNormalTail x ≤
        (4 / 3 : ℝ) * standardNormalDensity x / (1 + x) ∧
      standardNormalDensity x / standardNormalTail x ≤ 1 + x
```

These exact constants give the source's `exp(-x^2/2)/(1+x)` form with
`c=1/sqrt(2*pi)` and `C=4/(3*sqrt(2*pi))`. Both are actual strictly
positive fixed reals. They are convenient valid constants, not an optimality
claim or a quotation of constants absent from the source. The third output
is a source-facing combination of the first bound and true positive tail;
it immediately implies the looser `x+4` at main line 809.

### 3.5 General nonnegative-threshold tail comparison

```lean
theorem standardNormalTail_ratio_bound (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    standardNormalTail y ≤
      (4 / 3 : ℝ) * ((1 + x) / (1 + y)) *
        Real.exp ((x ^ 2 - y ^ 2) / 2) * standardNormalTail x
```

No ordering between `x,y` is required. The form avoids division by a tail
in its public conclusion, while global positivity permits the usual ratio
form. This is the exact Mills combination used for denominator layers at
supplement 1369-1377 as well as the simpler fixed deletion threshold.

### 3.6 Local tail comparability at the source scale

```lean
theorem standardNormalTail_local_comparison (x t : ℝ)
    (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hneigh : |t - x| ≤ 1 / (1 + x)) :
    Real.exp (-2) * standardNormalTail x ≤ standardNormalTail t ∧
      standardNormalTail t ≤ Real.exp 2 * standardNormalTail x
```

This works when an endpoint is zero. It is stronger than the `exp(4)`
factor used in the source; combining it with the existing budget factor
eight gives the required looser normal-weight bound. It does not assume
the budget or error comparison itself. Negative `t` is intentionally
outside this local positive-threshold interface and is handled separately
by the source's event/error convention, not by forcing the Mills domain.

### 3.7 Exact deletion-threshold normal-tail comparison

```lean
theorem standardNormalTail_deletion_comparison (j : ℕ) (x : ℝ)
    (hx : 0 ≤ x) (hj : (j : ℝ) ≤ x ^ 2 / 2) :
    standardNormalTail (Real.sqrt (x ^ 2 - (j : ℝ))) ≤
      3 * Real.exp ((j : ℝ) / 2) * standardNormalTail x
```

No sample length, original-law moment, conditional probability, positive
variance, or Berry--Esseen premise occurs. This is the missing actual normal
tail comparison at supplement 209-211. It can be composed with a future
proved bounded-random probability theorem, but that theorem is neither an
input here nor claimed to follow from this deterministic comparison.

## 4. Proof decomposition and true integral obligations

### Existing facts to reuse, not reprove

Use the existing library probability instance of `gaussianReal 0 1`,
`nullSingletonClass_gaussianReal` with the explicit nonzero variance one,
`gaussianReal_apply_eq_integral`, `integrable_gaussianPDFReal`,
`integral_gaussianPDFReal_eq_one`, `gaussianPDFReal_pos`, the Gaussian
negation map, and `cdf_eq_real`. These provide the actual normalization,
absolute continuity, positive density, measure/density bridge, symmetry
and CDF semantics. The Gaussian integral is not an assumed new theorem.

For 3.1, the difference between `Ici x` and `Ioi x` is a null singleton.
The complement of `Iic x` is `Ioi x`, so the finite real measure complement
identity gives `1-cdf`. Taking `.toReal` of the genuine nonnegative density
integral gives the last equality, using its actual integrability and
nonnegativity before any `ENNReal.ofReal` cancellation.

For 3.2, positive continuous Gaussian density gives positive mass on each
nonempty real interval, so both a finite strict tail and its complement
have positive mass. Monotonicity follows from inclusion of strict tails;
the Gaussian negation-map identity plus atomlessness gives reflection.
At zero the reflection identity and unit mass give exactly one half.
No event involving an original atomic increment law is changed by this
Gaussian-specific no-atom argument.

For 3.3, differentiate the explicit density. For the tail derivative, the
genuine global density integrability and continuity imply

```text
Psi(x) = Psi(0) - integral_(0..x) phi(t) dt
```

with an oriented interval integral for negative `x`. FTC-1 gives the
claimed derivative everywhere. The proof cannot use a tail integral's
default value at a nonintegrable function: the existing Gaussian density
integrability is established first. The actual density also tends to zero
at positive infinity by its displayed exponential formula.

### One new weighted primitive proves both Mills bounds

For `t>=0`, set only inside the proof

```text
F(t) = phi(t)/(1+t),
A(t) = (t^2+t+1)/(1+t)^2.
```

The density derivative gives `-F'(t)=phi(t)*A(t)`. The two pointwise
polynomial identities

```text
(1+t)^2 - (t^2+t+1) = t,
4(t^2+t+1) - 3(1+t)^2 = (t-1)^2
```

give `3/4<=A(t)<=1` on `t>=0`, with the denominator strictly positive.
In particular the derivative integrand is genuinely integrable on
`Ioi x` for any `x>=0`, by domination by the integrable Gaussian density.
Continuity at the finite endpoint and `F(t)->0` at infinity then allow
the actual half-line FTC theorem to prove

```text
phi(x)/(1+x) = integral_(x,infinity) phi(t)*A(t) dt.
```

Both sides of each subsequent `integral_mono` comparison are truly
integrable. The bounds on `A` give

```text
(3/4)*Psi(x) <= phi(x)/(1+x) <= Psi(x).
```

These are exactly the first two inequalities in 3.4. This proof also
handles `x=0` directly; it never divides by `x`, nor imports a sharp
`phi(x)/x` bound with an unusable zero-threshold endpoint. Global tail
positivity and `1+x>0` then justify the actual hazard division in the
third output.

### The two source combinations

For 3.5, use the exact positive density identity

```text
phi(y) = exp((x^2-y^2)/2)*phi(x)
```

and apply the upper Mills bound at `y` and the lower bound at `x`.
All denominators `1+x,1+y` and both tails are positive on the displayed
domains. This is an exact comparison of the actual Gaussian function.

For 3.6, the actual tail derivative and its positivity give

```text
(log Psi)'(s) = -phi(s)/Psi(s),
abs((log Psi)'(s)) <= 1+s,  s>=0.
```

Write `delta=|t-x|`. On the real interval between the two nonnegative
endpoints, `1+s<=1+x+delta`. The derivative/mean-value norm bound therefore
gives

```text
abs(log Psi(t)-log Psi(x)) <= (1+x+delta)*delta <= 2,
```

because `(1+x)*delta<=1` and `delta<=1`. Exponentiating yields 3.6.
No logarithm at a zero tail is used, and no derivative estimate is imposed
as an input. This is sufficient for the source's `exp(4)` comparison;
no attempt to optimize the local constant is needed.

For 3.7, set `y=sqrt(x^2-j)`. From `j<=x^2/2`, prove the radicand is
nonnegative and `y^2=x^2-j`; also `y>=x/2`, so
`(1+x)/(1+y)<=2`. Thus 3.5 gives a coefficient at most `8/3`, which is
relaxed to the public constant three, and the exponent is exactly `j/2`.
The stronger `y>=x/sqrt(2)` also holds, but no sample-length hypothesis
is required for this purely numeric conclusion.

## 5. Domains and boundaries

- All definitions and the representation/basic/derivative interfaces are
  for every real `x`. The Mills, general ratio and local comparison are
  explicitly restricted to nonnegative thresholds, where their linear
  denominators are strictly positive. Nothing crosses the pole at `x=-1`.
- `Psi(0)=1/2` is exact. The Mills theorem includes zero and therefore
  never relies on dividing by `x`; its denominator is `1+x` instead.
- Negative thresholds retain the true Gaussian value in `(1/2,1)` using
  positive density (hence strict decrease), the half value and reflection.
  They are not assigned zero,
  one, or a source-specific crossing convention by this interface.
- Strict/weak Gaussian tails agree only because the actual variance-one
  Gaussian is atomless. Original sample paths may have atoms, zero energy,
  strict survival or weak crossing; none of those events is changed here.
- In 3.7, equality in `j<=x^2/2` is allowed, as are `j=0` and `x=0`.
  At `x=0`, the premise forces `j=0`; the tail is one half. There is no
  artificial positive-threshold or nonempty-sample premise in this purely
  Gaussian/numeric theorem. The source retained comparison independently
  derives its genuine nonempty sample from its own size assumptions.
- Constants `1`, `4/3`, `2` (in the local exponent), and `3` (in deletion)
  are absolute and chosen before all thresholds, laws, sample sizes and
  deletion sets. They do not depend on a truncation budget or an unproved
  Gaussian error bound, and they are not claimed optimal.

## 6. Pinned-library search, exact APIs and cache status

All source/API inspection used the pinned Mathlib commit
`807d3836b165983210ee2ecf3cd28f239436949c`, Lean `4.36.0-rc1`, and the
designated `lead-c12` server worktree. A read-only search of
`Mathlib/Analysis` and `Mathlib/Probability` found no Mills-ratio,
Gaussian-tail-inequality or erfc interface to reuse. This is a recorded
name/text search, not a claim that no equivalent result could exist under
an unrelated name. Existing Gaussian normalization and probability facts
are reused rather than reproved.

The first cache inventory found the Gaussian Real, CDF, GaussianIntegral and
IntegralEqImproper artifacts missing. The coordinator then centrally
prepared `Gaussian.Real`, `Probability.CDF`, `IntegralEqImproper` and their
transitive dependencies (reported 93 files, cache get exit 0). This author
did not fetch or modify any cache. After that preparation, the actual
read-only import and `#check` probe exited 0 with empty stderr:

```text
taskset -c 0-3 lake env lean --stdin
```

The probe imported the five candidate modules above and confirmed:

| Actual API | Type information relevant to this scope |
|---|---|
| `gaussianReal`, `gaussianPDFReal` | Parameters are real mean and nonnegative-real variance. |
| `gaussianReal_apply_eq_integral` | For variance nonzero, actual set mass equals `ofReal` of the real density set integral. |
| `integrable_gaussianPDFReal`, `integral_gaussianPDFReal_eq_one` | Actual global density integrability and normalization. |
| `gaussianPDFReal_pos` | Actual pointwise strict density positivity at variance one. |
| `nullSingletonClass_gaussianReal` | Requires variance nonzero; supplies the strict/weak bridge. |
| `gaussianReal_map_neg` | Actual measure symmetry at mean zero. |
| `cdf_eq_real` | Under actual probability, Mathlib CDF equals real mass of `Iic x`. |
| `measureReal_compl` | For a measurable set under a finite measure, real complement mass is total real mass minus its mass. |
| `integral_Ioi_of_hasDerivAt_of_tendsto'` | Requires true derivative integrability on `Ioi x`, derivative identity on `Ici x`, and the actual limit at infinity. |
| `intervalIntegral.integral_hasDerivAt_right` | Requires interval integrability, local strong measurability and continuity at the endpoint. |
| `Convex.norm_image_sub_le_of_norm_deriv_le` | Controls log-tail differences from an actual derivative bound on a convex real interval. |

No candidate definition, theorem, placeholder, target proof or new `.olean`
was supplied by the probe. No local Lean command was used. There is no
outstanding cache request for the listed candidate imports as of this scope.

## 7. Exact nonclosure boundary and next gate

This batch proves only properties of the actual standard normal law and
the displayed deterministic tail comparisons. It does not assume or prove
Berry--Esseen, a central limit theorem, the bounded-random or bounded-endpoint
sample inequality, exponential/square-tilted moment transfer, binomial
averaging over deleted sets, Brownian maximum formulas, clock concentration,
Fourier inversion or the full relative-error C1/C2 comparison.

In particular, composing 3.7 with `RetainedComparison` alone still does not
give a Gaussian upper bound for the canonical raw product event: the
bounded-random probability theorem remains necessary. Likewise 3.6 compares
the actual Gaussian factor in `w_n`; the existing truncation-budget estimate
and the separate sample error estimates still have to be supplied before
claiming the source's weighted comparison.

After independent statement review and an explicit coordinator freeze, a
future implementation would be confined to the new module and its author
receipt, followed by targeted server checks, a full new-declaration
transitive standard-axiom audit, and a fresh proof review. No source or
existing implementation, probability interface, root entry point, pin,
cache or audit script has been modified by this author.
