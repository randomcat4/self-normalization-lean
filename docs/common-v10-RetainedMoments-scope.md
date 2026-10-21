# Retained cutoff law and its actual conditional moments

Status: the coordinator froze the first three definitions and nine theorem
signatures on 2026-10-21 and authorized their implementation. The frozen
proposal SHA256 was `4ac0982a6237b241e45cb6e21c15a7ad85ca886fb4a3d1d17d9c248877ea66ec`.

## Source contract and two important distinctions

Rechecked `supplement.tex` around lines 80–220, including `h:supp:xn`,
`h:supp:boundedrandom`, and the fixed-set conditioning passage. Also checked
the later bounded-endpoint proof for the centered-moment quantities that would
eventually use the variance.

The normalized variable has true probability law `ν` and satisfies

```text
∫ z dν = 0,    n ∫ z² dν = 1.
```

For the coarse estimate, the actual common input `h:supp:xn` is

```text
H_x := n ∫ F(xz) dν ≤ 1,    x^6 ≤ n.
```

It is **not** a standing assumption that `R_n(x)≤1` over both branches of the
original comparison domain. The original `p`-moment branch gives `H_x≤1`
directly; the small-budget branch gives `H_x≤R_n(x)≤1`. With the existing
unchanged definition, `H_x=truncationBudget ν n (x-1)`. The core APIs below use
the literal source integral `n∫F(xz)≤1`; a caller with `R_n(x)≤1` can derive
that premise by the already proved nonnegative-scale monotonicity. This avoids
silently narrowing the source to only its small-budget branch.

The probabilistic argument reduces to `x≥8`, while the retained-moment
arithmetic itself uses only `x≥2`. Together with `n≥x^6`, that implies `n≥64`
and in particular `n≥2`.

Write exactly

```text
B_x = {|z|≤1/x},   q_x = ν(B_x),
ν_x = cond ν B_x = (ν(B_x))⁻¹ • ν.restrict B_x.
```

This is the actual conditional measure. Its mass must first be proved positive;
it is not an arbitrary law merely satisfying similar moment inequalities.
The cutoff is always `1/x`, and the large region is strictly `|z|>1/x`.
Atoms at equality remain in the retained law. No substitution of `1/(1+x)` is
permitted.

The source's displayed bounds concern **raw second moments**, not variances:

```text
n |E_(ν_x) z| ≤ 2/x,
1-x⁻² ≤ n E_(ν_x) z² ≤ 1+2/n,
n E_(ν_x) |z|³ ≤ 2/x³.
```

In the bounded-random lemma the symbol `ν=k E z²` is also a raw second-moment
sum. The conditional mean is generally nonzero. Actual variance is
`E_(ν_x)(z-μ_x)² = E_(ν_x)z²-μ_x²`; it will not be replaced by `E_(ν_x)z²`,
and positive raw second moment will not be used as an assumption of positive
variance.

## First independently closable unit: conditional mean and raw second moment

Proposed new file: `Shao/Probability/RetainedMoments.lean`, importing the frozen
truncation integral interface and `Mathlib.Probability.ConditionalProbability`.
No existing definition or frozen source is changed.

Namespace `Shao`; `open MeasureTheory`; `autoImplicit false`.

The three definitions and nine theorems below are the exact proposed first
implementation batch. In these statements `[IsProbabilityMeasure ν]` is the
source's real-law assumption, not a premise imposed on the earlier general
measure budget results.

```lean
def retainedCutoffSet (x : ℝ) : Set ℝ := {z | |z| ≤ 1 / x}

noncomputable def retainedCutoffMass (ν : Measure ℝ) (x : ℝ) : ℝ :=
  (ν (retainedCutoffSet x)).toReal

noncomputable def retainedCutoffLaw (ν : Measure ℝ) (x : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond ν (retainedCutoffSet x)

theorem measurableSet_retainedCutoffSet (x : ℝ) :
    MeasurableSet (retainedCutoffSet x)

theorem retainedCutoffLaw_isProbabilityMeasure (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x) :
    IsProbabilityMeasure (retainedCutoffLaw ν x)

theorem ae_abs_le_retainedCutoffLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x) :
    ∀ᵐ z : ℝ ∂retainedCutoffLaw ν x, |z| ≤ 1 / x

theorem integrable_retainedCutoffLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x)
    (f : ℝ → ℝ) (hf : Integrable f (ν.restrict (retainedCutoffSet x))) :
    Integrable f (retainedCutoffLaw ν x)

theorem integral_retainedCutoffLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x)
    (f : ℝ → ℝ) (hf : Integrable f (ν.restrict (retainedCutoffSet x))) :
    (∫ z : ℝ, f z ∂retainedCutoffLaw ν x) =
      (∫ z : ℝ in retainedCutoffSet x, f z ∂ν) / retainedCutoffMass ν x

theorem retainedCutoffMass_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 < x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    1 - 1 / (n : ℝ) ≤ retainedCutoffMass ν x ∧
      1 / 2 ≤ retainedCutoffMass ν x ∧ retainedCutoffMass ν x ≤ 1

theorem integrable_retainedCutoffLaw_id_sq (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (x : ℝ) (hq : 0 < retainedCutoffMass ν x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Integrable (fun z : ℝ => z) (retainedCutoffLaw ν x) ∧
      Integrable (fun z : ℝ => z ^ 2) (retainedCutoffLaw ν x)

theorem retainedCutoffLaw_mean_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 < x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    (n : ℝ) * |∫ z : ℝ, z ∂retainedCutoffLaw ν x| ≤ 2 / x

theorem retainedCutoffLaw_second_moment_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 < x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    1 - 1 / x ^ 2 ≤ (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) ∧
      (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) ≤ 1 + 2 / (n : ℝ)
```

The generic conditional-law theorems take `hq>0` to express legitimate
conditioning. The source moment-bound theorems do **not** assume `hq>0`:
they derive `q_x≥1/2` from the source budget and `n≥2` before applying those
interfaces. Likewise they do not assume positive variance.

The first-moment integrability used in `hmean` is derived, not hidden: on a
probability space `|z|≤1+z²`, and `h2` makes this dominator integrable. The
conditional mean and square integrals likewise receive actual integrability
proofs. There is no use of a nonintegrable Bochner integral's default value.

The mean bound does not need `hnorm`; the square bound does not need
`hmean`. These unused source assumptions are deliberately omitted from the
respective minimal interfaces.

### First-unit proof dependencies

- On `|z|>1/x`, `1≤F(xz)`. Integrating yields
  `n ν(B_xᶜ)≤H_x≤1`, hence `q_x≥1-1/n≥1/2`. This is an actual event-mass
  bound and must be proved; the existing first/second tail moments alone will
  not be confused with a mass without the corresponding pointwise comparison.
- Conditional integrals are retained integrals divided by this actual `q_x`.
- Mean zero gives `∫_(B_x) z = -∫_(B_xᶜ) z`. Its absolute value is at most the
  tail absolute first moment, whose budget is `n E[|z|;B_xᶜ]≤1/x`.
- The square split and `n E[z²;B_xᶜ]≤x⁻²` give retained square sum at least
  `1-x⁻²`. Dividing by `q_x≤1` preserves that lower bound. The upper bound
  uses `n E[z²;B_x]≤1` and
  `1/q_x≤1/(1-1/n)≤1+2/n` for `n≥2`.

## Second batch: raw third moment and the retained sample length

With the same actual conditional law and `H_x≤1`, prove integrability of its
absolute cube and the remaining source bound

```text
n E_(ν_x)|z|³ ≤ 2/x³.
```

This requires no global third moment under `ν`. The previously proved
truncated-third kernel is integrable from the square moment, and the
conditional integral is its retained numerator divided by `q_x≥1/2`.

Now let `j=|I|`, `m=n-j`, and `y=sqrt(x²-j)`. The source inputs for transferring
the single-variable bounds to the retained row are

```text
x≥2,   x^6≤n,   j≤x²/2,   H_x≤1.
```

Here `j` and `n,m` are natural numbers, with `j≤x²/2` interpreted after coercion
to reals. Derive, rather than assume,

```text
j<n,   m≥1,
x/√2 ≤ y ≤ x,   y≥1,
m/n ≥ 1-1/(2x^4) ≥ 31/32.
```

The actual bounded-random inputs then follow with the source's constants:

```text
|z|≤1/x≤1/y       ν_x-almost surely,
1/2 ≤ m E_(ν_x)z² ≤ 2,
m |E_(ν_x)z| ≤ 2/y,
m E_(ν_x)|z|³ ≤ 2/y³.
```

The sample length `m` enters at this stage only; neither the conditional law
`ν_x` nor its first batch of `n`-normalized moments depends on the particular
deleted set or its cardinality. A separate product-law conditioning theorem
is needed to establish that the actual retained observations, conditional on
`J=I`, are iid with law `ν_x`. The univariate moment results do not certify
that joint-law assertion.

## Third batch: actual variance and standardized Lyapunov quantity

This is deliberately outside the proposed first twelve declarations.
Set `μ_x=E_(ν_x)z` and
`τ_x²=E_(ν_x)(z-μ_x)²`, with finite centered moments proved from the bounded
conditional law. First prove the genuine identity

```text
τ_x² = E_(ν_x)z² - μ_x².
```

Under the second-batch source size assumptions, variance positivity can be
derived quantitatively. For example the existing source bounds give

```text
m E z² ≥ (31/32)(3/4) = 93/128,
m μ_x² ≤ 4/(n x²) ≤ 1/64,
so 1/2 ≤ m τ_x² ≤ 2.
```

Indeed the lower estimate before relaxing the constant is `91/128>1/2`.
Thus `τ_x²>0` follows from `m≥1`; it is not a replacement hypothesis. Without
these size/separation inputs a conditional law can be degenerate, so a blanket
positive-variance claim from conditioning alone would be invalid.

The later bounded-endpoint proof uses the centered-cube comparison

```text
E|z-μ_x|³ ≤ 8 E|z|³,
m E|z-μ_x|³ ≤ 16/y³.
```

The comparison must be proved, including the conditional-law Jensen/moment
step; it is not a new input assumption. A useful explicit subsequent bound is

```text
L_m := [m E|z-μ_x|³] / (m τ_x²)^(3/2)
     = E|z-μ_x|³ / [sqrt(m) τ_x³]
     ≤ 32√2/y³ ≤ 64/y³,
where τ_x=sqrt(τ_x²)>0.
```

These are derived candidate constants for a later frozen unit; the source's
170–220 display itself gives the raw moments, not this standardized ratio.
No centered-third-moment or Berry--Esseen conclusion is claimed by the first
unit. Existing scalar, integral-budget, deletion, regularity, and sample-size
source files remain untouched.

## First-batch implementation and designated-server receipt

Only the frozen first three definitions and nine public theorem declarations
are implemented in `drafts/c12/RetainedMoments.lean` and the remote counterpart
`workspaces/lead-c12/Shao/Probability/RetainedMoments.lean`. Two private proof
helpers establish first-moment integrability from the square and rewrite the
strict-complement set integral; they add no assumptions to the public API.

After the pinned activation script and changing to `lead-c12`, the actual
targeted command was:

```text
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/Probability/RetainedMoments.olean Shao/Probability/RetainedMoments.lean
```

Exit code: 0. The final diagnostics are only three unused-parameter warnings:
`hq` in the generic support assertion, and `hq`/`hf` in the generic linear
conditional-integral identity. Their frozen hypotheses are retained. The
source moment inequalities derive positive `q` and prove actual integrability
before applying the conditional identities.

The tail mass proof explicitly integrates the indicator bound by `F(xz)`.
The mean proof uses the actual restricted numerator, its strict-complement
integral and mean zero. The raw-square lower bound first uses `A≥0` and
`q≤1` to get `A≤A/q`, then applies `1-x⁻²≤A`; it does not multiply a possibly
negative lower bound by an uncontrolled denominator. Thus every `x>0`, including
`x<1`, is covered by the frozen statement.

The designated-server source SHA256 is:

```text
512cf7a51125f18f94f42b4ef855e21290a28f7a3185865a3d375bde8100d6cb
```

A separate server import printed transitive axioms of all twelve public
declarations, thereby including the private helper dependencies. Exit code was
0; every list is exactly `[propext, Classical.choice, Quot.sound]`. The pinned
versions remain Lean `leanprover/lean4:v4.36.0-rc1` and mathlib
`807d3836b165983210ee2ecf3cd28f239436949c`.

Status: the complete frozen first batch is mechanically checked, with
independent blind semantic/proof review pending. The second and third batches
above remain proposals only: no conditional third-moment bound, retained-row
length transfer, centered variance bound, standardized Lyapunov bound, or joint
product-law conditioning theorem was implemented in this file.
