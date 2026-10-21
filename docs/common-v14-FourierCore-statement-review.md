# FourierCore independent statement review

STATUS: CORRECT — statement/source review only. No mathematical signature
revision is required before freezing this one-definition/seven-theorem batch.
This is not an implementation/proof review or a claim of Lean certification.

The initial blind translation below was written from the proposed Lean
declaration blocks alone, before reading the scope prose or the original
source anchors. No target implementation or target author proof has been
read. Only this review file belongs to this reviewer.

Bound proposal: `FourierCore-next-scope.md`, SHA256
`add680178670044bc54e90a143a1057b2d6bc74e0d08f42769480951bfe2c656`.
The extracted proposal has one definition and seven theorem statements.

## Independent blind mathematical translation

For an arbitrary measure `nu` on the real Borel space and real frequencies
`u,v`, the definition is the complex Bochner integral

```text
phi_nu(u,v) = integral exp(i*(u*a+v*a^2)) dnu(a).
```

The imaginary unit multiplies a real phase cast into the complex numbers.
It is the characteristic function of the pair `(a,a^2)` evaluated on real
frequencies; no complex frequencies, exponential damping, centering, or
normalization by a variance are built into it. The integral remains a total
Lean definition at arbitrary measures, without making integrability claims
there.

1. For every real probability law `nu` and every real `u,v`, the complex norm
   of `phi_nu(u,v)` is at most one. No moment hypothesis occurs.
2. For every natural length `n`, measurable sample space `Omega`, probability
   laws `mu` on `Omega` and `nu` on the reals, and measurable coordinates
   `X_i` which are independent under `mu` and each have the actual law `nu`,
   the complex expectation of
   `exp(i*(u*sum_i X_i+v*sum_i X_i^2))` equals `phi_nu(u,v)^n`.
   The first sum is the existing full-length prefix sum and the second is
   the actual uncentered path energy. Length zero is included. There is no
   moment premise.
3. For every real probability law with actually integrable absolute cube,
   all real `u,v`, actual mean `mu1=integral a dnu`, and actual
   `m3=integral |a|^3 dnu`, the odd difference
   `D_v(u)=phi_nu(u,v)-phi_nu(-u,v)` satisfies
   `|D_v(u)-2*i*u*mu1| <= m3*(|u|^3/3+2*|u|*|v|)`.
   Here every absolute value of a complex expression denotes its complex
   norm. Only the first frequency changes sign; `v` stays fixed.
4. Under exactly those same hypotheses,
   `|D_v(u)| <= 2*|mu1|*|u|+m3*(|u|^3/3+2*|u|*|v|)`.
   Nonzero conditional means have not been silently discarded.
5. At every real `u`, the map from real `r` to `D_v(r)` has real derivative
   into the complex normed space equal to
   `2*i*integral a*cos(u*a)*exp(i*v*a^2) dnu(a)`.
   This is a `HasDerivAt` assertion with real domain, not a complex
   holomorphic derivative or a derivative in `v`.
6. At every real `u`, the real function `r -> deriv D_v r`, with complex
   values, has derivative
   `-2*i*integral a^2*sin(u*a)*exp(i*v*a^2) dnu(a)`.
   The minus sign belongs to differentiating the cosine. The statement is
   about the derivative function itself, rather than merely a formal
   integrand derivative.
7. For the same `mu1,m3,D_v` and all real `u,v`,
   `|deriv D_v(u)-2*i*mu1| <= m3*(u^2+2*|v|)`, and
   `|deriv (r -> deriv D_v r)(u)| <= 2*m3*|u|`.
   No original-variable global third moment, zero-mean premise, fourth
   moment, positive variance, no-atom assumption, or sample size restriction
   is present.

The proposed derivative theorem uses third-absolute-moment integrability of
the displayed law `nu` itself. When consumed under a conditional increment
law, it must be that true conditional law's moment. The declaration does
not authorize replacing it by a moment of an unrelated original variable.

## Source and boundary comparison

After writing the blind translation, I read the complete bound scope and
the actual read-only original source anchors. I did not use the scope
author's API receipts, cache assertions, boundary examples, or derivation
claims as proof evidence. No target implementation was available or read;
no Lean command or arithmetic recomputation was necessary for this
statement review.

Actual original-source hashes checked from local bytes:

```text
C:/game/shao/current/c12/main.tex
beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
C:/game/shao/current/c12/supplement.tex
b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

The proposal was rehashed after the source pass and remained
`add680178670044bc54e90a143a1057b2d6bc74e0d08f42769480951bfe2c656`.

### Source mapping and domain

| Candidate content | Actual source anchor | Result of comparison |
|---|---|---|
| Literal coupled characteristic integral | Main 673-678, especially 675 | Exactly `E_x^* exp(i*u*A+i*v*A^2)`. `A` and `A^2` are dependent coordinates of one observation, not independent laws. |
| Finite iid factor | Supplement 2343-2357, especially 2348-2351 | Independence across future observations supplies `phi^(n-i)`. The candidate proves that expectation factor, not the full Fourier transform involving `H_y` and `Xi`. |
| Odd function and mean subtraction | Supplement 3194-3205, especially 3197-3201 | The source decomposition specializes to real `z=u`, damping `s=0`. The first frequency changes sign while the quadratic frequency remains fixed. The linear term is precisely `+2*i*u*mu`. |
| First derivative | Supplement 3207-3213 | Exact factor `+2*i`, integrand `a*cos(u*a)*exp(i*v*a^2)`, with a subtraction of `2*i*mu` when obtaining the refined error. |
| Second derivative | Supplement 3215-3219 | Exact factor `-2*i`, integrand `a^2*sin(u*a)*exp(i*v*a^2)`. |
| Real source estimates | Supplement 2384-2392 | Candidate bounds imply the real parts of `(a)` and the real-parameter `(b),(c)` with explicit absolute constants. |
| Actual low-frequency power consumer | Supplement 2477-2484 | The odd estimate is only one input; algebraic power difference and independent low-frequency damping are also used. |
| Odd-power derivative table | Supplement 3435-3447 | Additional individual `phi_u,phi_uu` controls and damping remain required, as the scope explicitly says. |
| Whole-plane power derivative consumer | Supplement 2614-2616; proof 3403-3417 | Not proved by these odd-only derivative results. The source separately controls moments of the actual full sum and differentiates its characteristic function. This remains a later obligation. |

The source's larger domain at 2385-2390 permits
`z=u-i*lambda`, `zeta=v+i*s`, with nonnegative `lambda,s`, and uses a
support-dependent exponential factor. Every proposed public frequency
variable is explicitly real, and the actual definition has a real phase
times `i`. The candidate therefore correctly claims only the real-plane
specialization. Norm one and the bounds below cannot simply be extended
to imaginary shifts without further domination and the source support
factor. Nothing in the seven statements claims that extension.

### Independent check of all constants

Put `e_v(a)=exp(i*v*a^2)`; it has complex norm one for all real `v,a`.
Direct subtraction of the actual phase exponentials gives

```text
D_v(u) = 2*i * integral sin(u*a)*e_v(a) dnu(a).
```

Under the stated probability and actual absolute-cube integrability,
the actual first moment is integrable. Integral linearity and the
real-to-complex integral conversion therefore give the exact subtraction

```text
D_v(u)-2*i*u*mu1
 = 2*i * integral (sin(u*a)-u*a)*e_v(a) dnu(a)
   + 2*i*u * integral a*(e_v(a)-1) dnu(a).
```

Using globally valid real inequalities
`|sin t-t|<=|t|^3/6` and `norm(exp(i*t)-1)<=|t|`, the norms of these two
terms are respectively at most

```text
2*(|u|^3/6)*m3 = (|u|^3/3)*m3,
2*|u|*|v|*m3.
```

Thus the proposed remainder's constants `1/3` and `2` are correct for all
real signs, without a small-frequency restriction. Triangle inequality
and `norm(2*i*u*mu1)=2*|u|*|mu1|` yield the second odd bound exactly as
stated. In particular that bound implies the source's unspecified
`C*(|mu1||u|+m3*(|u|^3+|u*v|))` with `C=2`.

Differentiating the same actual odd integral gives

```text
D_v'(u) = 2*i * integral a*cos(u*a)*e_v(a) dnu(a),
D_v''(u) = -2*i * integral a^2*sin(u*a)*e_v(a) dnu(a).
```

For the first refined error, split

```text
a*cos(u*a)*e_v(a)-a
 = a*(cos(u*a)-1)*e_v(a) + a*(e_v(a)-1).
```

The global bound `|cos t-1|<=t^2/2` gives, after multiplication by the
outside factor of modulus two,

```text
norm(D_v'(u)-2*i*mu1) <= m3*u^2+2*m3*|v|.
```

For the second derivative, `|sin(u*a)|<=|u|*|a|` gives
`norm(D_v''(u))<=2*|u|*m3`. The resulting source-style first derivative
bound is `norm(D_v')<=2|mu1|+m3*(u^2+2|v|)`, which is bounded by
`2*(|mu1|+m3*(u^2+|v|))`. The second derivative source constant can be
chosen as two. No factor of two, imaginary unit, or mean term is missing.

### True integrability and derivative exchange

The mathematics of the signatures closes with the displayed hypotheses;
the implementation must still prove these obligations, rather than replace
them by new assumptions:

1. For the unit bound and iid factor, the phase and each finite product are
   measurable and have norm exactly one. Under their probability measures,
   their complex Bochner integrability follows from domination by the
   integrable constant one. No first, second, or third moment is needed.
2. For the other five statements, `h3` and probability imply first and
   square absolute integrability. The pointwise bounds
   `|a|<=1+|a|^3` and `a^2<=1+|a|^3` supply genuine integrable dominators.
   The conditional increment's mean is consequently an actual integrable
   expectation, not the default value of a nonintegrable integral.
3. The original odd integrand `2*i*sin(r*a)*e_v(a)` is measurable and
   integrable. Its real-parameter derivative has norm at most `2|a|`,
   uniformly in every real `r` and fixed `v`. This is a genuinely
   integrable dominating function for the first exchange.
4. The first derivative's actual integral representation can then be
   differentiated again: the derivative integrand has norm at most
   `2a^2`, again globally in `r`. This requires the already derived square
   integrability, not a fourth moment and not a derivative of the
   quadratic frequency. The source measure `nu` is held fixed as `r`
   varies.
5. The first derivative identity is quantified at every real argument;
   it identifies the whole derivative function. The second
   `HasDerivAt` statement can therefore be proved for the actual
   `r -> deriv D_v r`, not just for a formal integrand derivative. All
   hypotheses needed for a dominated parameter-integral theorem are
   available from the preceding uniform bounds and continuity/measurability.
6. The refined remainder integrands and their absolute bounds are truly
   integrable from `h3`, as are all linear terms split off from them.
   Pulling the real mean into the complex integral and applying norm
   bounds must use those true integrability facts. No Bochner default
   zero is needed at any step.

The real domain and complex codomain of `HasDerivAt`/`deriv` are appropriate:
complex numbers are a complete real normed vector space. There is no
holomorphic derivative claim and no missing imaginary-frequency
integrability condition. The coordinator reports the fixed-version
parameter-integral module has now been cached; this review did not rerun
that preparation or depend on an author compilation receipt.

The finite iid factor is also implementable without hidden moments:
`exp(i*(u*sum X_i+v*sum X_i^2))` is the finite product of the measurable
single-observation phases. Independence is used across observations.
Actual same-law pushforward identifies each factor integral with
`quadraticChar nu u v`. No independence between `X_i` and `X_i^2`, nor
between the linear and quadratic totals, is asserted or needed.

### Conditional-law meaning and boundaries

The source notation `E_x^*` is the actual bounded conditional increment law
`P_A`; main line 622 uses its actual mean and absolute moments. The generic
candidate `nu` can be instantiated by that law. Its `h3` is exactly the
third absolute moment of that chosen law. It does not require the original
untruncated variable to have a global third moment; in particular it does
not exclude the original `p<3` branch. The consumer must still connect
`nu` to the actual conditional law, using its real normalization and
support, rather than substitute an arbitrary law or the coarse cutoff law
at a different threshold.

- At `u=0`, the odd difference and its remainder are exactly zero. The
  first derivative need not equal `2*i*mu1` at nonzero `v`; the candidate
  correctly retains the error term `2*m3*|v|`. The second odd derivative
  is zero there.
- At `v=0`, the formulas reduce to the usual sine/cosine odd expansion;
  for nonzero means the leading term is `+2*i*u*mu1`. Testing the symbolic
  point mass at one gives `D=2*i*sin u`, `D'=2*i*cos u`,
  `D''=-2*i*sin u`, confirming all coefficient directions.
- Under the point mass at zero, `phi=1`, `mu1=m3=0`, and all odd quantities
  and their derivatives vanish. No positive variance or no-atom hypothesis
  is introduced. Other atomic and nonsymmetric laws are also permitted.
- Negative real `u` or `v` changes no bound improperly: all sign-sensitive
  error terms use absolute values or `u^2`. Partial reflection keeps
  `v` fixed; it is not complex conjugation, which would reverse both
  real frequencies. No such invalid identity is used in these statements.
- At sample length zero, the genuine prefix sum and energy vanish and
  the integral is the complex constant one under a probability measure,
  matching `phi^0=1`. No nonempty-index or positive-energy premise is needed.
- These formulas do not choose an open/closed CDF event, change a retained
  cutoff, or remove the later strict test's `q>0` restriction. At a zero
  realized square sum, the quadratic phase simply has its actual zero
  square contribution. No zero-clock probability has been bounded here.

### Exact limit of the downstream claim

The current seven theorems do not by themselves give the Gaussian-damped
power difference at supplement 2477-2484. That consumer separately uses
the low-frequency strip, a true damping lemma for both `phi(u,v)` and
`phi(-u,v)`, and the algebraic finite-power difference. A real polynomial
bound holding at all frequencies is not a replacement for those inputs.

In particular the whole-plane power bound at 2616 is a different obligation.
Its proof at 3403-3417 uses the independent full-sum moments
`E|S_l-l*mu|<=tau*sqrt(l)` and `E(S_l-l*mu)^2=l*tau^2`, then differentiates
the characteristic function of the actual pair `(S_l,Q_l)`. It further
uses `T`/variance comparability and the small mean control to reach
`C*T^(a/2)`. The iid factor here identifies that characteristic function
with `phi^l`, but the odd derivative identities do not supply individual
`phi_u`, `phi_uu` or these scaled full-power bounds. No theorem in this
batch contains `T` or claims to close 2616; the scope already expressly
leaves the missing individual derivative controls and power table open.

High-frequency damping still needs the actual smoothing/noise multiplier
and its cone restrictions. Complex shifts, Fourier inversion and
differentiation of the full smoothed kernel, clock/concentration payment,
strict CDF-to-smoothed-test passage, Gaussian comparison, and final C1/C2
comparison all remain open. No alleged sufficient noise, variance, or clock
bound has been inserted as a premise of these seven candidate theorems.

## Final verdict

CORRECT for the bound proposal's one definition and seven public theorem
statements. Their real-frequency domain, actual law and moments, complex
norms, finite iid factor, mean subtraction, imaginary-unit directions,
constants, and first/twice-differentiation requirements are mathematically
consistent and match the stated source specialization. No mathematical
signature correction is required.

After freeze, implementation must establish the true complex integrability,
dominated exchanges, whole derivative-function identity, and finite-product
integral identity, then pass a targeted server check, transitive standard-
axiom audit, and a fresh proof review. This verdict is solely a statement
and source-fidelity judgment; it is not acceptance of an implementation or
any low/high-frequency, clock, Fourier-kernel, or complete comparison root.

No source, candidate scope, implementation, dependency, cache, or shared
interface was modified. Only this independent review file was written.
