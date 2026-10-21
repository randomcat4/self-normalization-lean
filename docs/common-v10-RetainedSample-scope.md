# Frozen retained raw third moment and retained-row input bounds

Status: the root coordinator froze all five public signatures at proposal
SHA256 `96748781cff64579e8aa9a48870b256c2c38dc5d7c8670798f861efbac5a3b95`
before implementation. `RetainedSample.lean` in this directory passes its
targeted server check and transitive axiom audit; see its author receipt.
Existing retained-cutoff definitions and sources are unchanged. Independent
blind review remains separate.

## Source contract and dependency

Read `RetainedMoments-scope.md`'s second batch and actual first-batch declaration
signatures. The first-batch source hash is
`512cf7a51125f18f94f42b4ef855e21290a28f7a3185865a3d375bde8100d6cb`;
it has since been independently reviewed CORRECT by the coordinator's separate
reviewer and its existing server artifact is reused without rebuilding.
This author does not treat the dependency author's receipt as independent acceptance.

Read-only `supplement.tex` lines 170-220 give the retained iid law and the
three raw-moment bounds at retained sample size. Lines 88-99, especially
`h:supp:xn`, give the common input in both source branches:

```text
H_x := n integral F(xz) dν <= 1,     x^6 <= n.
```

The shared premise is not `R_n(x)<=1`: that would silently restrict the source
to one of its two comparison branches. The source eventually uses `x>=8`,
but the raw retained-row arithmetic only needs `x>=2`.
Supplement source hash:
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

Reuse, without redefining, the existing `retainedCutoffSet x`,
`retainedCutoffMass ν x`, and `retainedCutoffLaw ν x`:

```text
B_x = {z | abs z <= 1/x},
q_x = (ν B_x).toReal,
ν_x = ProbabilityTheory.cond ν B_x.
```

All new conditional moments refer to this genuine normalized restriction,
not a measure chosen to satisfy analogous inequalities.

## Frozen new module and exact public interfaces

New file `Shao/Probability/RetainedSample.lean`, namespace `Shao`,
`open MeasureTheory`, `autoImplicit false`. No new global definition is needed.
Five public theorems separate the genuine conditional third moment from two
pure numeric interfaces and their retained-row application.

### Conditional absolute cube is actually integrable

```lean
theorem integrable_retainedCutoffLaw_abs_cube
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x : ℝ) (hx : 0 < x) (hq : 0 < retainedCutoffMass ν x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    Integrable (fun z : ℝ => |z| ^ 3) (retainedCutoffLaw ν x)
```

This is a generic legitimate-conditioning interface, so it takes `hq>0`.
The source bounds below derive that fact and do not add it as a premise.
No full third moment under the original measure is assumed.

### The remaining n-normalized raw moment

```lean
theorem retainedCutoffLaw_third_moment_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 < x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    (n : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂retainedCutoffLaw ν x) ≤ 2 / x ^ 3
```

Neither mean zero nor square normalization nor the stronger source size bound
is needed for this univariate third-moment estimate, so none is inserted.

### Deterministic retained sample length and fraction

```lean
theorem retainedSample_size_bounds (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2) :
    64 ≤ n ∧ j < n ∧ 1 ≤ n - j ∧
      1 - 1 / (2 * x ^ 4) ≤ ((n - j : ℕ) : ℝ) / (n : ℝ) ∧
      (31 / 32 : ℝ) ≤ 1 - 1 / (2 * x ^ 4)
```

`n-j` is natural subtraction, not a silently signed length. Its strict
nonemptiness and the valid real cast identity are derived from the inputs.
There are no measure or distribution arguments in this theorem.

### Deterministic lowered threshold

```lean
theorem retainedSample_threshold_bounds (j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hj : (j : ℝ) ≤ x ^ 2 / 2) :
    x / Real.sqrt 2 ≤ Real.sqrt (x ^ 2 - (j : ℝ)) ∧
      Real.sqrt (x ^ 2 - (j : ℝ)) ≤ x ∧
      1 ≤ Real.sqrt (x ^ 2 - (j : ℝ))
```

This threshold fact needs no `n` or `hsize`, so those unused assumptions are
omitted. It gives a positive `y=sqrt(x²-j)` and, with `y<=x`, the usual
reciprocal inequality `1/x<=1/y`; there is no division by a zero square root.

### The actual raw inputs at retained sample length

```lean
theorem retainedSample_raw_moment_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    (∀ᵐ z : ℝ ∂retainedCutoffLaw ν x,
      |z| ≤ 1 / Real.sqrt (x ^ 2 - (j : ℝ))) ∧
    ((1 / 2 : ℝ) ≤ ((n - j : ℕ) : ℝ) *
        (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) ∧
      ((n - j : ℕ) : ℝ) *
        (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) ≤ 2) ∧
    ((n - j : ℕ) : ℝ) * |∫ z : ℝ, z ∂retainedCutoffLaw ν x| ≤
      2 / Real.sqrt (x ^ 2 - (j : ℝ)) ∧
    ((n - j : ℕ) : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂retainedCutoffLaw ν x) ≤
      2 / (Real.sqrt (x ^ 2 - (j : ℝ))) ^ 3
```

The support output is the source bounded-random input at `y`; the stronger
support at `1/x` remains the already existing theorem. The last three bounds
are the raw second-moment interval, absolute raw mean, and raw absolute cube,
with exactly the source constant `D=2`.

## Proof obligations and reuse

### Genuine conditional third moment

For any positive `x`, the existing marked small-third integrability theorem
proves integrability of `abs(z)^3 1_(B_x)` from `h2`. Restrict to the measurable
set `B_x`; the marked kernel equals `abs(z)^3` almost everywhere there. Apply
the existing `integrable_retainedCutoffLaw` interface to obtain the actual
conditional-law integrability in the first theorem. This does not invoke a
global third moment or the default value of a nonintegrable Bochner integral.

For the n-normalized bound, `retainedCutoffMass_bounds` supplies `q_x>=1/2` and
hence positive mass from `n>=2`, `x>0`, `h2`, and the literal `hcut`. The existing
integrated small-third bound at scale `x` and `hcut` give

```text
x^3 n integral_(B_x) abs(z)^3 dν <= 1.
```

The restricted integral is the actual marked numerator by measurable-indicator
integration. The existing conditional-integral identity divides it by the
actual `q_x`. With `q_x>=1/2`, nonnegative numerator, and `x>0`, this gives
`n E_(ν_x) abs(z)^3 <= 2/x^3`. Prove numerator and conditional integrability
before using the integral formula or inequalities.

### Size and lowered threshold arithmetic

From `x>=2`, get `x^4>=16`, `x^6>=64`, and `n>=64`. From `2j<=x²`,

```text
2 j x^4 <= x^6 <= n.
```

All displayed arithmetic here is after real casting. Its positive denominators
give `j/n<=1/(2x^4)<=1/32`, hence `j<n`, `m=n-j>=1`, and the exact fraction
chain in the size theorem. The cast `((n-j : Nat) : R)=n-j` is used only after
proving `j<=n`.

For the threshold, `x²-j>=x²/2>=2`, so the square root is real and at least
one. Squaring nonnegative candidates shows `x/sqrt 2<=y`; nonnegative `j`
gives `y<=x`. This part requires no probability, normalization, or sample size.

### Raw moment transfer

Write `N=(n:R)`, `M=((n-j : Nat):R)`, and `y=sqrt(x²-j)` only locally. The
size lemma supplies `N>=64`, `M>=1`, `M<=N`, and `M/N>=31/32`.
The old mean and second-moment theorems and the new third-moment theorem give

```text
N |E_(ν_x)z| <= 2/x,
1-x^(-2) <= N E_(ν_x)z² <= 1+2/N,
N E_(ν_x)|z|³ <= 2/x³.
```

The raw second moment is nonnegative. With `x>=2`, its n-normalized lower
bound is at least `3/4`, and therefore

```text
M E_(ν_x)z² = (M/N) (N E_(ν_x)z²)
             >= (31/32)(3/4) = 93/128 > 1/2.
```

For the upper bound, `M<=N` gives `M E z²<=1+2/N<=2`. For the mean and cube,
use `M<=N`, nonnegative absolute/raw-cube moments, and `0<y<=x`:

```text
M |E z| <= 2/x <= 2/y,
M E|z|³ <= 2/x³ <= 2/y³.
```

The old support theorem gives `abs z<=1/x` almost everywhere, followed by the
same reciprocal threshold comparison. Actual conditional-law probability and
integrability of id and square come from the existing first-batch interfaces
after deriving `q_x>0`; absolute-cube integrability comes from the new first
theorem. They are not implicitly assumed merely because Bochner integrals
appear in a conclusion.

## Boundaries, scope, and acceptance

- Natural `j=0` is allowed, yielding `m=n` and `y=x`. Equality in
  `j<=x²/2` is allowed. No strict-threshold or atomlessness assumption is added.
- Natural `n=0` is not an extra exclusion: `x>=2` and `x^6<=n` derive
  `n>=64`, ruling it out before any division or natural-subtraction cast.
- The conditional law depends only on the original real law and `x`; `j`
  affects the retained row length and lowered threshold, not its definition.
- These are raw moments. No variance identity, positive variance, recentering,
  centered third moment, standardized Lyapunov ratio, or Berry--Esseen input
  from the proposed third batch is in scope.
- The source's fixed-set iid claim is supplied by the separate ConditionalIID
  and RetentionEvent modules. These univariate bounds do not assert that a
  random-length retained sample is unconditionally iid and do not prove the
  bounded-random tail theorem itself.

Ownership: only this new scope, `drafts/c12/RetainedSample.lean`, its author
receipt, and remote `Shao/Probability/RetainedSample.lean`. The coordinator
froze the five declarations before implementation. The target now passes its
server-only check and transitive axiom audit at the recorded source hash;
fresh independent review is still required for acceptance.
No original source, cutoff definition, root import, version pin, common audit
tool, or shared cache will be changed.
