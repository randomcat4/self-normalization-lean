# Actual bounded quadratic exponential tilt — source contract

State: `CANDIDATE_COMPLETE_NOT_FROZEN_NOT_PROVED`.
This is a source-bound auxiliary producer proposal, not a proof or an
acceptance report. All prior accepted results are reused at their exact
interfaces; none was recompiled or re-reviewed in preparing this candidate.

## Source identity and exact scope

Read-only source: `C:/game/shao/current/c12/supplement.tex`, SHA256
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.
Line references are the actual UTF-8 file's lines, with no source edits.
The relevant auxiliary proof is **in this same file**, lines 3551–3625;
there is no separate `c12/auxiliaryproof.tex` in this source snapshot.

| Source lines | Actual mathematical object/claim | Proposed coverage |
|---|---|---|
| 2238–2245 | `s=κy²`, `Z_s=E exp(-sA²)`, actual changed law, actual mean and variance | Energy theorem's `ρ=ν.tilted (fun a => -s*a²)`, actual integrals and `variance id ρ`. `s=κy²` is later specialization. |
| 2246–2255 | threshold pays `s h_x²≤1`; `exp(-s h_x²)≤Z_s≤1`; normalized density lies in `exp(±s h_x²)` | Exact energy assumptions and density/normalizer outputs, with `h=h_x`. |
| 2256–2262 | comparison of actual variance, raw second and raw absolute third moment | Exact energy `exp(±s h²)` comparison. The proposed variance proof uses least-squares centering, which gives this stronger single-density factor; it preserves the same actual variance and does not assume the conclusion. |
| 2264–2274 | subtract original nonzero mean, exact mean-shift identity, bound `C s m3` | Exact identity in energy theorem and `|μρ-μ|≤2*s*exp(s*h²)*m3`; under `s h²≤1`, absolute `C=2*exp(1)`. |
| 2275–2279 | source-scale `nV_s≈1`, drift bound, centered third moment | Centered third moment is provided. `nV_s` and `n|μ_s|` require the accepted source-scale/moment payments and the actual choice `s=κy²`; they are consumer work. |
| 2280–2285 | real survival/cyclic first/second regulator moments under changed law | **Not covered.** These require the actual survival and second-moment chain. |
| 2287–2291 | actual product change of measure for `U_i,Q_i` | **Not covered by the three new signatures.** The accepted quadratic sample change-of-measure factorization is an existing upstream bridge; specialization to actual `U_i` and `Q_i` remains a consumer obligation. |
| 2292–2298 | `Z_s≤1-s*m2/2≤exp(-s*m2/2)`, powers and source `exp(-csi/n)` | Energy theorem gives exact decay and all natural powers. Using `n*m2≥3/4`, consumer gets `c=3/8`; no conclusion about `U_i` is inferred from this scalar decay alone. |
| 2700–2707 | actual source `h`, `N=q+T`, `N≥1/16`, `λ≥y/√N`, `s∈{0,λy/√N}` | Exact numerical payment of both `s≤λ²` and `s*h≤λ` is recorded below. The generic joint declaration exposes them. |
| 2709–2715 | actual joint laws with sign `±`, real normalizers, product independence | Joint theorem uses `b=λ∨b=-λ` and literal actual tilt. Existing sample-product theorem supplies independent copies/product factorization when needed; no independence conclusion is assumed to prove one-dimensional moments. |
| 2718–2724 / 3551–3577 | actual variance comparison, `m3ρ/Vρ≤L3 exp(L3 λh) γ`, actual mean bound | Joint theorem gives `exp(±4λh) V`, `Γ=8 exp(8λh)γ`, and `|μρ|≤exp(4λh)(|μ|+λm2+s m3)`. Quotient bound requires `V>0`, supplied by the actual conditional-law bridge. |
| 2726–2729 / 3579–3597 | signed log normalizer bound preserving `±λμ+(λ²/2-s)m2` | Joint theorem preserves those coefficients exactly. Remainder is `24 λ³ m3 exp(λh)`; no zero-mean cancellation is used. It also proposes the stronger absolute Taylor remainder bound for `Z`. |
| 2730–2739 / 3599–3625 | additional `(y+λ)Γ≤c`, tilted raw-second/variance comparability, low-frequency power bound | **Not covered.** In particular this candidate never asserts `m2ρ≤2Vρ` merely from density comparison. Tilted smallness, drift-to-variance, characteristic decay and later complex shift remain open consumers. |

## Existing interfaces read, with exact bytes

1. `library/Shao/Probability/SourceTruncationBridge.lean`, SHA256
   `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1`.
   `Shao.sourceTruncation_law_data` provides the probability instance, true
   AE cutoff and finite signed/absolute raw moments of the fixed-cutoff
   conditional law. `Shao.sourceTruncation_variance_bounds` gives
   `V=m2-μ²`, `0<V`, `3/4≤n*m2≤4/3`, and `1/2≤n*V≤4/3`.
   These statements do **not** say that the conditional law's mean is zero.
2. `library/Shao/Probability/SourceFourierScale.lean`, SHA256
   `5f31eb92eff8ded33b91f55a59a16de4e58cdd7a9e0514d082a2c4932f5feff0`.
   `Shao.sourceTruncation_gamma_bounds` uses the exact same conditional law,
   `m3=∫|a|³`, `V=variance id`, and `γ=m3/V`. It provides `m3>0`, `γ>0`,
   `sqrt(m2)*m2≤m3`, `m2≤γ²`, `γ≤2h_x`,
   `(3/4)*n*m3≤γ≤2*n*m3`, and `n*m3≤2r`, `γ≤4r`.
   `Shao.sourceTruncation_oddPower_scale_inputs` provides its own remaining
   length and bias/variance inputs. No old proof is changed or re-audited.
3. Accepted `Shao.Probability.SourceFourierParameterPayment`, source commit
   `52b6e4727f84f23810f019a2c20c068974be3acc`, SHA256
   `e6b366379bb3997678076327835bbce2f2da3661594552f83cb6be2695f70d30`.
   Its production source hash was read-only checked from
   `workspaces/common-cone-derivatives-v44` on the server. The exact
   `sourceTruncation_threshold_fourier_parameter_payment` output gives the
   true conditional-law AE support at `h=ε0/(1+y)`, `h_x≤h`, `0<h≤1/4`,
   and `h*y≤δ` for the same threshold neighborhood. It does not give tilted
   mean, variance or normalizer facts. Root reports the exact v52 aggregate
   accepted head `184e1ee3c7ccfa900757056c44eec8b27c8b2174`; this candidate
   does not change that receipt or rely on stale v51 acceptance metadata.
4. Existing `Shao.OQ3.QuadraticSampleChangeOfMeasure`, read from
   `drafts/oq3/publication-u22-ai-aq/Shao/OQ3/QuadraticSampleChangeOfMeasure.lean`,
   SHA256 `b27ee727239ca0c31db3e3f04275eae1a13813adb1f1749edb564749df7d9bda`.
   Its `iid_quadratic_sample_tilt` is stated for a genuine bivariate MGF
   domain input and the literal quadratic tilt, and proves product
   exponential integrability, `Z^n` normalization, and equality to the
   product of the actual one-coordinate tilted measures. Its cell
   change-of-measure theorem is for actual empirical `(mean,energy)` cells.
   For this producer set `theta=(b,-s)`; bounded support supplies its actual
   MGF-domain integrability. No duplicate product theorem is proposed.

## Pinned Mathlib reading

Read-only official Mathlib checkout on the server:
`/root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages/mathlib`,
actual read-only `git rev-parse HEAD` returned
`807d3836b165983210ee2ecf3cd28f239436949c`. Project toolchain specified in
`SERVER.md` is `leanprover/lean4:v4.36.0-rc1`; it was not invoked here.

`Mathlib/MeasureTheory/Measure/Tilted.lean`, SHA256
`355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f`, defines
the **actual** measure as

```lean
def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity (fun x =>
    ENNReal.ofReal (Real.exp (f x) / ∫ x, Real.exp (f x) ∂μ))
```

This definition can be zero if `exp∘f` is not integrable. The proposed
theorems therefore prove true integrability and a strictly positive real
normalizer before asserting a probability law. Relevant inspected APIs are
`isProbabilityMeasure_tilted`, `integral_tilted`,
`integrable_tilted_iff`, `tilted_absolutelyContinuous`,
`absolutelyContinuous_tilted`, `tilted_const`, and `tilted_congr`.

`Mathlib/Probability/Moments/Variance.lean` supplies
`variance_eq_integral`, `variance_eq_sub` under genuine `MemLp id 2`, and
nonnegativity of actual variance. `Mathlib/Analysis/Calculus/Taylor.lean`
supplies the inspected `taylor_mean_remainder_lagrange_iteratedDeriv` and
`taylor_mean_remainder_bound`. The latter's bound has denominator `n!`,
not `(n+1)!`; the proposed remainder coefficient `24` is deliberately valid
for that weaker bound as well. No unverified theorem name is used as a
mathematical premise.

## Proof route and exact constants

This is a complete mathematical route for planning, not a replacement for
the required Lean proof and independent verification.

### 1. General actual density, integrability and variance

On the given AE support, `|b*a-s*a²|≤S=|b|h+s h²`. The exponential is a
continuous measurable function and is dominated by the integrable constant
`exp S`; its integral `Z` lies in `[exp(-S),exp S]`, hence is strictly
positive. The literal density `w=W/Z` consequently lies in
`[exp(-2S),exp(2S)]` AE. Apply the actual Mathlib tilted-measure APIs to get
its probability instance, mutual absolute continuity, transferred support,
and integral identity. Bounded density above and below gives equivalence
of real L1 integrability and the comparison for every integrable AE
nonnegative `g`. The support bound gives all natural signed and absolute
power integrability, including power zero, and the asserted moment bounds.

For any probability law σ with finite second moment and actual mean μσ,
expand and integrate

`∫(a-c)² dσ = variance(id,σ)+(μσ-c)²`.

Use the density upper bound with `c=μ` and the lower bound with `c=μρ`.
The squared correction is nonnegative, so
`exp(-2S)*V≤Vρ≤exp(2S)*V`. This uses each law's own actual mean. It gives
the claimed zero-variance equivalence without dividing by zero. The source
uses a pair identity, whose density product also proves a looser estimate;
the variance-minimization route reduces avoidable product-integral work.

### 2. Energy tilt and mean shift

For `b=0`, `W∈[exp(-S),1]` and `Z∈[exp(-S),1]`, so the normalized density
has the sharper range `[exp(-S),exp S]`. Repeat the same comparisons with
these constants. All means and powers remain integrable by the core.

Normalization and `∫(a-μ)dν=0` yield exactly

`μρ-μ = Z⁻¹ ∫(a-μ)(W-1)dν`.

For `s≥0`, `|W-1|≤s*a²`, hence the numerator has absolute value at most
`s*(m3+|μ|m2)`. Cauchy–Schwarz gives `|μ|≤sqrt(m2)` and Lyapunov gives
`sqrt(m2)*m2≤m3`, valid also at `m2=0`; therefore this is at most `2s*m3`.
Divide by `Z≥exp(-S)` to obtain the stated `2s exp(S)m3` bound.

For any real probability law with finite third absolute moment, Jensen's
inequality for `|.|³` and `|a-c|³≤4(|a|³+|c|³)` give
`∫|a-μρ|³dρ≤8∫|a|³dρ`. This gives the asserted centered-third bound.

Under the explicit `s*h²≤1`, `0≤s*a²≤1` on the support and the scalar
inequality `exp(-t)≤1-t/2` on `[0,1]` gives
`Z≤1-s*m2/2≤exp(-s*m2/2)`. Positivity of `Z` permits natural powers;
`exp(x)^i=exp(x*i)` yields the exact all-`i` bound. With the real source
input `3/4≤n*m2` and `n>0`, its later consumer obtains
`Z^i≤exp(-(3/8)*s*i/n)`.

### 3. Signed joint tilt: distinct guards and mean

From `b=±λ`, `λ≥0`, and **separately** `s*h≤λ`, one has
`S=λh+s h²≤2λh`. This pays the core density, raw-moment and variance
factors `exp(±4λh)`; also `-2λh≤b*a-s*a²≤λh` yields the stated sharper
normalizer range. No bound `λh≤1` is assumed or needed.

For every real `r`, `|exp r-1|≤exp(|r|)*|r|`. Thus on support
`|W-1|≤exp(S)*(λ|a|+s*a²)` and

`|μρ| ≤ exp(S)*|μ| + exp(2S)*(λ*m2+s*m3)
       ≤ exp(4λh)*(|μ|+λ*m2+s*m3)`.

The latter step uses `S≥0` and nonnegativity of both raw moments. It does
not discard `μ`. Centering the third absolute moment again costs `8`.
When `V>0`, the variance lower bound makes `Vρ>0` and division of
`m3ρ≤exp(4λh)m3` by `Vρ≥exp(-4λh)V` gives
`m3ρ/Vρ≤exp(8λh)*(m3/V)≤Γ`, with the literal source choice
`Γ=8*exp(8λh)*(m3/V)`. The existing source-scale bridge, when applied,
already supplies `m3>0,γ>0`; general `V=0` cases do not use this quotient.

### 4. Normalizer Taylor remainder, retaining its signed linear term

Let `F(a)=exp(b*a-s*a²)`. Direct derivatives give

`F'''(a)=F(a)*((b-2*s*a)^3-6*s*(b-2*s*a))`.

The stated guards imply, for `|a|≤h`,
`|b-2*s*a|≤λ+2*s*h≤3λ`, `s≤λ²`, and `F(a)≤exp(λh)`.
Consequently `|F'''(a)|≤45*λ³*exp(λh)`.

To avoid any sign restriction on a point `a`, apply the degree-two Taylor
bound to `G(t)=F(t*a)` on the fixed interval `[0,1]`. Then
`G(0)=1`, `G'(0)=b*a`, and `G''(0)=(λ²-2s)*a²`, using `b²=λ²`.
The third derivative bound on this interval is
`45*λ³*|a|³*exp(λh)`. The inspected Mathlib norm bound divides by `2!`,
so its remainder is at most `(45/2)*λ³*|a|³*exp(λh)`, and hence at most
`24*λ³*|a|³*exp(λh)`. Integrate this absolute error under the original ν
to obtain the exact proposed bound for `Z`; bounded support proves every
term's true integrability. Finally `log Z≤Z-1` for the already proven
`Z>0` gives the stated log bound. This preserves `b*μ` and the coefficient
`λ²/2-s`; no center-zero simplification or positivity of that coefficient
is assumed. If `λ=0`, the explicit `s≤λ²` and `s≥0` force `s=0`, and the
actual probability tilt is exactly ν with `Z=1`.

## Exact source parameter payment and remaining guards

For the growing-kernel source, take the actual conditional law `ν=ρ_x`
and `h=ε0/(1+y)` from accepted threshold payment. Require `y≥2`,
`N≥1/16`, `λ≥y/√N`, `s=0 ∨ s=λ*y/√N`, and `y*h≤1/4`.
No `N≤7` or remaining-time restriction is needed for this producer.

Because `sqrt(N)≥1/4>0`, the nonzero choice satisfies

`0≤s`,
`s=λ*(y/√N)≤λ²`,
`s*h=λ*(y*h)/√N≤4*λ*(y*h)≤λ`.

The zero choice satisfies the same inequalities directly. This is the
precise separate payment of both joint hypotheses. The already accepted
threshold-to-Fourier parameter payment can be instantiated at `δ≤1/4`
to supply `yh≤1/4` and the actual AE support. There is no implication
`s≤λ² ⇒ s*h≤λ` without this extra source payment.

For the energy source, take `b=0`, `h=h_x`, `s=κ*y²`. Its source guard is
`s*h_x²≤κ*ε0²≤1`, using the threshold closeness shown at 2246–2249.
This is independent of the joint theorem's λ. **An energy tilt with
`b=0,s>0` must use the general core/energy theorem, not set `λ=0` in the
joint theorem.**

Still required outside this milestone:

- Actual substitution of `κ`, source `Λ_y`, and source moments to bound
  the changed drift and pay any survival theorem's drift factor.
- Actual product-weighted `U_i^r exp(-sQ_i)` identity, its needed
  integrability, survival estimate, and the true regulator second moment.
- The source part-(c) implication from `(y+λ)Γ≤c` to the changed mean's
  smallness relative to changed variance, and then `m2ρ≤2Vρ`.
- Actual low-frequency characteristic power and all growing-y kernel
  interactions, including the actual `N=q+T` range.
- Complex shift, inversion, desmoothing, smoothed probability comparison,
  and the original C1/C2/root claims. Their status remains **OPEN**.

## Ownership, execution and review state

Only `drafts/c12-bounded-quadratic-tilt/` was written. No implementation,
imports, shared instructions, registry, status from another lane, remote
worktree or original source was edited. The existing released worktree
`common-short-kernel-v51` is a possible future implementation location
reported by root, not activated here. It was not written or checked.

Actual tool work was file reads, exact hashes, and bounded remote read-only
inspection of pinned sources. There was no Lean invocation, no local Lean
installation/check, no new source-format gate, no cache write and no
claimed server kernel/axiom receipt. Await complete root declaration
freeze and activation before implementation. A later independent final
review must read the full actual definitions/signatures/proof and source
mapping; the author cannot mark its own route `CORRECT`.
