# Proposed retained centered moments, variance, and Lyapunov quantity

Status: the root coordinator froze the three signatures at proposal SHA256
`d8ab157b03ccbc398997044edecc6510abde8f3659a8d5834309cc405fadae9b`
and authorized implementation. This author owns only this new scope
and the future new `Shao/Probability/RetainedVariance.lean` module; all existing
retained-law definitions and frozen sources remain unchanged.

## Source meaning and actual next use

The read-only source is `C:/game/shao/current/c12/supplement.tex`, SHA256
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.
The retained-law passage at lines 170-210 asserts raw moments, rather than
variance bounds. Its inputs remain the original

```text
H_x = n integral F(xz) dnu <= 1,
x >= 2, x^6 <= n, j <= x^2/2,
integral z dnu = 0, n integral z^2 dnu = 1,
```

with a genuine probability law `nu` and an integrable square. Let
`m=n-j`, `y=sqrt(x^2-j)`, and use the existing unchanged definitions

```text
nu_x = retainedCutoffLaw nu x = cond nu {|z| <= 1/x},
mu_x = integral z dnu_x,
V_x = integral (z-mu_x)^2 dnu_x.
```

The bounded-endpoint proof at lines 1240-1309 actually uses a centered
increment `Y=B-E B`, its almost-sure bound, its positive variance, and its
finite centered absolute third moment. Its displayed generic constants are
`|Y|<=2/x`, `k E|Y|^3<=8D/x^3`, and `k Var(B) in [1/8,4]` after a reduction
to sufficiently large `x` depending on `D`. Its input symbol
`nu=k E B^2` is still a raw second-moment sum. These source assertions do not
identify raw second moment with variance.

The generic Berry--Esseen assertion at lines 1075-1080 and its completion
application at lines 1203-1225 use the actual ratio

```text
E|B-E B|^3 / (sqrt(k) * sqrt(Var(B))^3).
```

Thus a reusable bound for this ratio is useful at the next call boundary.
The original source does not define another standardized probability law or
assert the literal constant `64`. The `1/2`, `16`, and `64` conclusions below
are derived quantitative helper bounds for this specific retained law under
the stronger existing size assumptions. They are not quotations of the
source's generic bounded-endpoint lemma.

Dependencies, without modifying or rebuilding their frozen sources:

- `RetainedMoments.lean`, accepted source SHA256
  `512cf7a51125f18f94f42b4ef855e21290a28f7a3185865a3d375bde8100d6cb`.
- `RetainedSample.lean`, independently accepted source SHA256
  `a507e549e2973dd04ce25f22e2c6973e0e6c491433a1d7fd2d88fbb082e86ca4`,
  whose separate blind review the coordinator has accepted as CORRECT.

## Exact proposed public API

New file `Shao/Probability/RetainedVariance.lean`, namespace `Shao`,
`open MeasureTheory`, `autoImplicit false`; import the existing retained
sample module. Three public theorems and no new public definition are proposed.
Local `let` binders name actual integrals, rather than introducing a second
conditional law or treating moments as abstract assumed numbers.

### Actual centered integrability, mean, variance identity, and cube comparison

```lean
theorem retainedCutoffLaw_centered_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x : ℝ) (hx : 0 < x) (hq : 0 < retainedCutoffMass ν x)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    let μx : ℝ := ∫ z : ℝ, z ∂retainedCutoffLaw ν x
    Integrable (fun z : ℝ => z - μx) (retainedCutoffLaw ν x) ∧
      Integrable (fun z : ℝ => (z - μx) ^ 2) (retainedCutoffLaw ν x) ∧
      Integrable (fun z : ℝ => |z - μx| ^ 3) (retainedCutoffLaw ν x) ∧
      (∫ z : ℝ, z - μx ∂retainedCutoffLaw ν x) = 0 ∧
      (∫ z : ℝ, (z - μx) ^ 2 ∂retainedCutoffLaw ν x) =
        (∫ z : ℝ, z ^ 2 ∂retainedCutoffLaw ν x) - μx ^ 2 ∧
      (∫ z : ℝ, |z - μx| ^ 3 ∂retainedCutoffLaw ν x) ≤
        8 * (∫ z : ℝ, |z| ^ 3 ∂retainedCutoffLaw ν x)
```

This legitimate-conditioning interface takes `hq>0`. It does not take
original mean zero, original normalization, a global original third moment,
positive variance, or a Jensen inequality as an input. It also does not
assert positive variance: a genuinely conditioned law may be degenerate
without the later quantitative separation assumptions.

The centered first moment is included because the later centered-increment
argument uses a genuinely mean-zero increment. The three integrability
outputs certify the moments needed in that same call; they do not merely
assert equalities between Bochner integrals whose values could default to
zero in a nonintegrable case.

### Positive variance and retained-row centered inputs

```lean
theorem retainedSample_variance_third_moment_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    let μx : ℝ := ∫ z : ℝ, z ∂retainedCutoffLaw ν x
    let Vx : ℝ := ∫ z : ℝ, (z - μx) ^ 2 ∂retainedCutoffLaw ν x
    let M : ℝ := (n - j : ℕ)
    let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
    (∀ᵐ z : ℝ ∂retainedCutoffLaw ν x, |z - μx| ≤ 2 / x) ∧
      0 < Vx ∧
      ((1 / 2 : ℝ) ≤ M * Vx ∧ M * Vx ≤ 2) ∧
      M * (∫ z : ℝ, |z - μx| ^ 3 ∂retainedCutoffLaw ν x) ≤ 16 / y ^ 3
```

The support conclusion is the stronger actual cutoff bound `2/x`; since
`0<y<=x`, a caller also gets `2/x<=2/y`. Positive conditional mass,
`m>=1`, positive variance, and finite centered third moment are derived.
None is inserted as an extra hypothesis.

### Actual Berry--Esseen Lyapunov ratio

```lean
theorem retainedSample_lyapunov_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    let μx : ℝ := ∫ z : ℝ, z ∂retainedCutoffLaw ν x
    let Vx : ℝ := ∫ z : ℝ, (z - μx) ^ 2 ∂retainedCutoffLaw ν x
    let M : ℝ := (n - j : ℕ)
    let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
    (∫ z : ℝ, |z - μx| ^ 3 ∂retainedCutoffLaw ν x) /
        (Real.sqrt M * (Real.sqrt Vx) ^ 3) ≤ 64 / y ^ 3
```

This is the source's exact variance-normalized third-moment parameter, using
ordinary cubes and the actual positive square roots. No integer power is
substituted for a `3/2` power, and no conditional law is replaced by one
chosen to have unit variance. Equivalently, for the actual measurable
function `Z(z)=(z-mu_x)/sqrt(V_x)` under the unchanged `nu_x`, it is
`E_(nu_x)|Z|^3/sqrt(m)`. An auxiliary proof may verify the integral scaling
identity to certify this reading. A new public standardized-variable
definition, pushforward-law interface, or iid-transfer theorem is not needed
for the current source call and is outside this minimal batch.

## Proof decomposition and actual integrability

### Legitimate probability and uncentered moments first

In the first theorem, the existing conditional-law interface supplies
`IsProbabilityMeasure nu_x` from the genuine positive mass. The existing
conditional id/square integrability theorem and retained absolute-cube
integrability theorem supply the actual raw moments from `h2`, `x>0`, and
`hq>0`. In the last two theorems, first derive `n>=64`, `m>=1`, `y>=1`, and
`q_x>=1/2>0` from the already checked size, threshold, and mass theorems.
The same true-probability and integrability facts then apply.

### Variance is an actual expanded integral

The centered id is integrable as an integrable id minus an integrable constant.
The centered square is integrable either by its polynomial expansion or by
the nonnegative integrable dominator `2z^2+2mu_x^2`. Expanding

```text
(z-mu_x)^2 = z^2 - 2mu_x*z + mu_x^2
```

and using genuine integral linearity gives
`V_x=E z^2-mu_x^2`, because the law has mass one and `E z=mu_x`.
The same facts prove `E(z-mu_x)=0`. All expanded terms are actually
integrable before these identities are used.

### Jensen step is proved, not imported as a hypothesis

Write `b=|mu_x|`, `u=|z|`, and `C=E|z|^3`. Actual id integrability gives
`b<=E|z|` by the norm-of-integral inequality. For all `u,b>=0`,

```text
(u-b)^2 * (u+2b) = u^3 - 3b^2*u + 2b^3 >= 0.
```

The polynomial on the right is integrable under the true probability law:
the cube, absolute id, and constant are integrable. Integration yields
`3b^2 E|z|<=C+2b^3`. Multiplying `b<=E|z|` by `3b^2>=0` then yields the
actual scalar conclusion `|E z|^3=b^3<=C`. This proof does not assume
Jensen, a full third moment under the original law, or centered integrability.
The case `b=0` is included without dividing by `b`.

Pointwise triangle inequality and the elementary identity

```text
4(a^3+b^3) - (a+b)^3 = 3(a+b)(a-b)^2 >= 0,  a,b>=0,
```

give `|z-mu_x|^3<=4(|z|^3+|mu_x|^3)`. This is also an actual integrable
dominator for the centered cube. Prove centered-cube integrability using
this dominator and its measurability, then apply integral monotonicity with
both sides integrable. With the preceding derived Jensen step, obtain
`E|z-mu_x|^3<=8 E|z|^3`.

### Quantitative separation for positive variance

Set `N=(n:R)`, `M=((n-j:Nat):R)`. The old size interface gives `N>=64`,
`M>=1`, `M<=N`, and `M/N>=31/32`; `j<n` is proved there before using
the natural subtraction cast. The source's stronger old square and mean
statements give

```text
N E z^2 >= 1-1/x^2 >= 3/4,
N |mu_x| <= 2/x.
```

Keep this stronger information rather than subtracting a mean-square term
from the relaxed public raw bound `M E z^2>=1/2`:

```text
M E z^2 >= (31/32)(3/4) = 93/128,
M mu_x^2 <= N mu_x^2 <= 4/(N x^2) <= 1/64.
```

All squaring/dividing uses `N>0` and `x>0`. Therefore actual integral
expansion gives `M V_x>=91/128>1/2`. The upper bound follows from
`V_x=E z^2-mu_x^2<=E z^2` and the already checked raw upper bound
`M E z^2<=2`. Since `M>0`, the positive lower bound forces `V_x>0`.
This rules out a degenerate conditional law using the actual source inputs,
rather than assuming it is nondegenerate.

The source mean bound with `N>=2` gives `|mu_x|<=1/x`. Combine it with the
existing almost-sure `|z|<=1/x` to obtain `|z-mu_x|<=2/x`. Multiplying
the proved centered/raw cube comparison by `M>=0` and applying
`M E|z|^3<=2/y^3` gives `M E|z-mu_x|^3<=16/y^3`.

### Normalize the actual third-moment parameter

Let `C_c=E|z-mu_x|^3`, `s=sqrt(M V_x)`, and `tau=sqrt(V_x)`.
Here `M,V_x,y` are all positive, as already derived. Square-root product
identities give the exact equality

```text
C_c / (sqrt(M)*tau^3) = (M*C_c) / s^3.
```

Since `s^2=M V_x>=1/2`, also `s>=1/2`, so
`s^3=s*(M V_x)>=1/4`. Together with `M*C_c<=16/y^3`, this proves
the public bound `64/y^3` using only positive denominators. One can derive
the sharper `32sqrt(2)/y^3`, but it is not needed in this batch.

The standardized function, if mentioned in the proof, is exactly
`Z(z)=(z-mu_x)/tau` under `nu_x`. Its centered-cube integrability and
`E|Z|^3=C_c/tau^3` follow by constant scaling of the already integrable
centered cube and `tau>0`. The ratio is therefore an actual Lyapunov
quantity and not a formal numerical proxy or an assumed Berry--Esseen bound.

## Boundaries and exclusions

- `j=0` and equality in `j<=x^2/2` are allowed. The exact cutoff includes
  atoms at `|z|=1/x`; no atomlessness or strict cutoff is introduced.
- The generic first theorem permits a degenerate conditional law and makes
  no claim that its variance is positive. The full-source conclusions derive
  positivity and every nonzero denominator.
- `n=0` is ruled out by `x>=2` and `x^6<=n`, rather than by an extra premise.
  Natural subtraction is cast only after deriving `j<n`.
- No global third moment under `nu`, centered-moment hypothesis, Jensen
  hypothesis, positive-variance hypothesis, or BE conclusion is added.
- The law still depends on `nu,x`, not on `j`; `j` enters only `m,y`.
  No assertion about unconditional iid at random retained length is made.
- Generic tilted-law variance comparison, change of measure, completion,
  Berry--Esseen itself, Gaussian tails, and the bounded-endpoint or
  bounded-random root theorem remain outside this unit.

The coordinator explicitly froze these three signatures at the proposal hash
above. Implementation is limited to the new module and its receipt. All Lean
checks and transitive axiom audits run only in the designated server worktree,
with standard axioms `propext`, `Classical.choice`, and `Quot.sound` only. A
fresh independent review must follow; this author does not certify their own
encoding.
