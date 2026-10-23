# Canonical Brownian existence from an actual Gaussian product space

Status: **PROVED as an author mathematical construction; independent review pending.**
Formal status: **NOT IMPLEMENTED / NOT KERNEL CHECKED**. The adjacent declaration/value
proposal must be frozen by the lane lead before any implementation. No Lean command was
run by this context. No new axiom or additional Brownian premise is proposed.

Author: OQ4 context146, `gpt-6.1-sol`, `xhigh`, fresh context. Scope is this directory only.
This is a classical Lévy–Ciesielski construction, not a novelty claim. Its purpose is to
instantiate the actual `IsBrownianReal B law` required by OQ4's given-process consumers.

## Source contract

The read-only original `C:/game/shao/current/oq4/b01/proof01.md`, lines223–264,
uses a standard Brownian limit to prove pure-kernel statements B0/B1. Those statements
do not assume that the input law is accompanied by an arbitrary Brownian process.
The existing weak-limit/killed-functional modules and common Brownian supremum/grid
modules correctly accept a given `B`, `P`, and `IsBrownianReal B P`; they do not construct
such data. This unit supplies actual data on a specific sample space. It proves neither
the killed eigenfunction identity B4 nor B1 by itself.

The pinned primary sources do **not** contain a general projective-limit existence
theorem or a Kolmogorov continuous-modification theorem under those names or their
relevant definitions. `Projective.lean` gives the predicate and uniqueness;
`ProjectiveFamilyContent.lean` gives additive content; `Process/Kolmogorov.lean` gives
the moment-condition predicates. They are not existence certificates. The alternative
used here is fully explicit and uses the actually available `Measure.infinitePi`.

## 1. Literal objects and basic probability

Let

\[
 \Omega=\mathbb R^{\mathbb N\times\mathbb N},\qquad
 P=\bigotimes_{(m,j)\in\mathbb N^2}N(0,1),\qquad Z_{m,j}(\omega)=\omega(m,j).
\]

Use the product measurable space. In Lean these are the literal `Sample`, `law`,
and `coord` values in `declarations.lean.txt`; the measure is
`Measure.infinitePi (fun _ : ℕ × ℕ => gaussianReal 0 1)`.
`ProductMeasure.lean` proves it is a probability measure and proves its coordinate
pushforwards. `Independence/InfinitePi.lean` proves independence of the coordinates.
Instantiate those results with index type `ℕ × ℕ`, constant space `ℝ`, constant
measure `gaussianReal 0 1`, and identity coordinate maps. There is no choice of
a Brownian process in this step.

Let `c₄ = ∫ |x|⁴ dN(0,1)`. It is a finite nonnegative real number: use
`memLp_id_gaussianReal (μ := 0) (v := 1) 4`, then the defining fourth-power
integrability characterization of `MemLp`. Its numerical value3 is unnecessary.
The same fourth moment applies to every coordinate by its proved pushforward law.

Define, on all real arguments,

\[
 c(u)=\max(0,\min(1,u)),\quad
 \phi(u)=\max(0,1-|2u-1|),\quad
 a_n=\frac1{2(\sqrt2)^n},\quad
 h_{n,k}(u)=a_n\phi(2^n u-k).
\]

The tent `φ` is continuous, nonnegative, at most1, zero off `[0,1]`, zero at0/1,
and equals1 at1/2. For `k<2ⁿ`, `h[n,k]` is supported on
`[k/2ⁿ,(k+1)/2ⁿ]`, with height `aₙ` at its midpoint. At a fixed real `u`,
at most one of the finitely many tents for level `n` is nonzero: if two are
positive, both corresponding open intervals would contain `u`, whereas the
integer intervals `(k,k+1)` are disjoint. Consequently

\[
 \sum_{k<2^n}\phi(2^nu-k)\le1. \tag{1}
\]

All these assertions include arguments outside `[0,1]`; there all the level
tents vanish. Define

\[
 L_{m,n}(u)=\sum_{k<2^n} Z_{m,2^n+k}h_{n,k}(u),\qquad
 U_m^N(u)=uZ_{m,0}+\sum_{n<N}L_{m,n}(u),
\]
\[
 U_m(u)=uZ_{m,0}+\sum_{n\ge0}L_{m,n}(u).
\]

The last expression uses Lean's total `tsum` value on every sample, including
samples on which the series does not converge. All claims using convergence
will be made on one expressly constructed probability-one event. Since every
level is identically zero at0/1, the total definition satisfies

\[
 U_m(0)=U_m^N(0)=0,\qquad U_m(1)=U_m^N(1)=Z_{m,0} \tag{2}
\]

for **every** sample. In particular no exceptional-set convention changes endpoints.

## 2. One probability-one event gives all paths

Put `r=4/3`, and for each `m,n` define the measurable event

\[
 E_{m,n}=\{\exists k<2^n:\ |Z_{m,2^n+k}|>r^n\}.
\]

Each event is a finite union of inverse images of open sets by coordinate
evaluations. Markov's inequality applied to `|Z|⁴` and the union bound give

\[
 P(E_{m,n})\le 2^n c_4 r^{-4n}
       =c_4(81/128)^n. \tag{3}
\]

The strict inequality in the event is harmless: `{|Z|>rⁿ}` is contained in
`{|Z|⁴≥r⁴ⁿ}`, and `rⁿ>0`. The geometric series in (3) is finite since
`0<81/128<1`. The first Borel–Cantelli lemma therefore gives, for each `m`,
eventually no `E[m,n]`, almost surely. Intersect these events over `m∈ℕ`.
This countable intersection is the literal predicate `Good`; it has probability1.
No independence is needed for this Borel–Cantelli application.

Fix a sample in `Good` and fix `m`. For all sufficiently large `n`, (1) yields,
simultaneously for **all real** `u`,

\[
 |L_{m,n}(u)|\le a_n r^n
   =\tfrac12\left(\frac4{3\sqrt2}\right)^n. \tag{4}
\]

The ratio in (4) is positive and less than1: its square is8/9. Thus the
eventual geometric majorant is summable. The finitely many earlier levels
are bounded finite sums of continuous tents. The Weierstrass criterion shows
absolute convergence at every `u` and uniform convergence on the whole real
line of the level series. This is exactly an instantiation of the pinned
`tendstoUniformlyOn_tsum_nat_eventually` with `s=univ`,
`f n u=L[m,n](u)`, and the majorant in (4). Adding the fixed continuous
function `u↦u Z[m,0]` preserves uniform convergence. Hence

\[
 U_m^N\longrightarrow U_m\quad\hbox{uniformly on }\mathbb R,
 \qquad U_m\text{ is continuous}. \tag{5}
\]

This single event covers all `m` and all real time arguments. It does not
intersect uncountably many separate almost-sure convergence assertions.

## 3. All nonnegative times, exact zero, and measurability

For `t≥0` define the literal finite sums

\[
 B_N(t)=\sum_{m=0}^{\lfloor t\rfloor} U_m^N(c(t-m)),\qquad
 B(t)=\sum_{m=0}^{\lfloor t\rfloor} U_m(c(t-m)). \tag{6}
\]

The sum includes the index `floor t`, including at integer `t`. Its last
argument is0 at an integer, so its value is0 by (2). For every natural `M`
and `0≤t≤M`, both sums in (6) may instead be taken over the **fixed** range
`m<M`: any extra term has `m≥t`, hence clipped argument0 and value0.
To check both directions when extending or shortening the range, use
`floor t≤M`; if `floor t=M`, the only extra term is again zero because `t=M`.
This proves the proposed `B_eq_sum_of_le`; the identical argument applies
to `B_N` using `unitPartial_zero`.

For a sample in `Good`, each function `t↦U_m(c(t-m))` is continuous by (5).
Around any `t₀≥0`, choose a natural `M>t₀`; on the open subspace neighborhood
`{t<M}` the process equals the fixed finite sum over `m<M`. It is therefore
continuous at `t₀`. This argument includes every integer joining point and
the subspace endpoint0. Thus `Continuous (B · ω)` on `Good`, proving the
simultaneous almost-sure continuity required by `IsBrownianReal.cont`.

At time0, every term in the literal sum is zero, for every sample. Thus
`B 0 ω=0` holds everywhere, stronger than an almost-sure assertion.

For fixed `N,t`, `B_N(t)` is a finite linear combination of measurable
coordinates, hence measurable. For every `ω∈Good` and every fixed `t`,
the finitely many terms in (6) converge by (5). Hence `B_N(t)→B(t)` on
`Good`. Applying the actual pinned
`aemeasurable_of_tendsto_metrizable_ae'` gives `AEMeasurable (B t) law`.
No global measurability of the set of continuous functions in an uncountable
product is assumed or needed.

## 4. Deterministic covariance kernel on one unit interval

The coordinate index blocks are disjoint. Indeed if `k<2ⁿ`, then
`2ⁿ≤2ⁿ+k<2ⁿ⁺¹`. Two such dyadic integer intervals for distinct levels
are disjoint. Equality of their indices first forces equal levels, then
equal `k`. None of them is0. For different `m`, the first coordinate
already distinguishes the Gaussian variables.

Consequently the deterministic coefficient inner product of `U_m^N(u)`
and `U_m^N(v)` is

\[
 K_N(u,v)=uv+\sum_{n<N}\sum_{k<2^n}h_{n,k}(u)h_{n,k}(v). \tag{7}
\]

For different unit indices these coefficient inner products are zero.
This is an identity of the actual finite coefficients, not a premise about
some presumed Gaussian process.

We prove

\[
 K_N(j/2^N,k/2^N)=\min(j/2^N,k/2^N)
 \quad(0\le j,k\le2^N). \tag{8}
\]

First observe that `U_m^N` is affine on every closed dyadic cell of mesh
`h=2⁻ᴺ`: all breakpoints of a level `n<N` tent are integer multiples of
`2⁻ⁿ⁻¹`, hence are mesh-`2⁻ᴺ` points. The same separate-affinity property
holds for `K_N` in each variable, directly from (7).

For `N=0` the grid consists of0/1 and `K₀(u,v)=uv`, which agrees with
`min` at its four pairs of endpoints. Suppose (8) holds at level `N`.
The next kernel adds the level-`N` sum in (7). New grid points are old
endpoints and midpoints of old cells `[a,a+h]`.

* At old endpoints every new tent vanishes, so the old identities persist.
* At the midpoint `x=a+h/2` and an old endpoint `y`, separate affinity gives
  `K_N(x,y)=(min(a,y)+min(a+h,y))/2`. Every old endpoint has `y≤a` or
  `y≥a+h`; the expression is respectively `y` or `a+h/2`, in either case
  `min(x,y)`. The level-`N` correction is zero because it vanishes at `y`.
* For two midpoints in different cells `[a,a+h]`, `[b,b+h]`, assume the
  first cell precedes the second, so `a+h≤b`. Double affinity gives the
  average of the four old corner values. Those values are `a,a,a+h,a+h`,
  whose average is `a+h/2`. Different cells have different active tents,
  so the new correction is zero. This is the minimum of the midpoints.
* For the same midpoint in the same cell, the four corner values are
  `a,a,a,a+h`, so the old variance is `a+h/4`. Exactly one new tent has
  height `a_N`; its squared height is `a_N²=2⁻ᴺ/4=h/4`. Adding it gives
  `a+h/2`, as required.

Symmetry handles the reversed ordering. These cases exhaust old and new
grid points and prove (8) by induction. Degenerate endpoint0 and1 are
included in the old-endpoint cases; no division by a time parameter occurs.

For arbitrary `u,v∈[0,1]`, choose closed grid cells containing them,
including the final cell for the endpoint1. The value `K_N(u,v)` is the
bilinear interpolation of its four grid corner values, since it is separately
affine on these cells. The interpolation weights are nonnegative and sum1.
At any one of those corner pairs `(uᵢ,vⱼ)`, the function `min` satisfies

\[
 |\min(u_i,v_j)-\min(u,v)|\le
        \max(|u_i-u|,|v_j-v|)\le2^{-N}.
\]

Insert (8) into that convex interpolation. The triangle inequality yields

\[
 |K_N(u,v)-\min(u,v)|\le2^{-N}. \tag{9}
\]

Thus the coefficient kernels converge uniformly on `[0,1]²`. This proof
avoids any unlocated Haar-completeness, Gaussian-limit, or continuity theorem.

## 5. Coefficient kernel on the whole half-line

The coefficient inner product for the finite linear combinations `B_N(s)`
and `B_N(t)` is the literal `fullCov` value

\[
 C_N(s,t)=\sum_{m=0}^{\lfloor\max(s,t)\rfloor}
         K_N(c(s-m),c(t-m)). \tag{10}
\]

One may use the common longer index range because the extra coefficients
are zero at clipped argument0, and different `m` use disjoint coordinates.
Put `M=floor(max(s,t))+1`. Applying (9) to each term of (10) bounds its
error from `∑[m<M] min(c(s-m),c(t-m))` by `M 2⁻ᴺ`, which tends to0.

The limiting sum is exactly `min(s,t)`. To see this, assume `s≤t`.
Monotonicity of `c` makes each minimum equal `c(s-m)`. Write
`q=floor s` and `f=s-q∈[0,1)`. For `m<q`, `c(s-m)=1`; for `m=q`,
it equals `f`; for `m>q`, it is0. The sum therefore equals `q+f=s`.
If `s` is an integer, `f=0`, so the formula still holds. The symmetric
case gives `t`. This proves

\[
 C_N(s,t)\longrightarrow\min(s,t) \quad\text{for all }s,t\ge0. \tag{11}
\]

There is no fixed upper horizon in the construction or conclusion.

## 6. Actual finite-dimensional laws by characteristic functions

Fix any finite time set `I⊂ℝ≥0` and any real coefficient vector `a:I→ℝ`.
The variable `S_N=∑[i∈I] aᵢ B_N(i)` is a finite real linear combination
of the independent standard normal coordinates already constructed in
section1. Combine repeated occurrences of the same coordinate first.
For a finite coefficient family `dᵣ` and independent standard normals,
the characteristic function at1 is

\[
 E\exp(i\sum_r d_r Z_r)
 =\prod_r\exp(-d_r^2/2)
 =\exp(-\tfrac12\sum_r d_r^2). \tag{12}
\]

Every equality in (12) is an instantiation of the pinned independence
characteristic-function product theorem and `charFun_gaussianReal` with
mean0/variance1. Expanding the finite square and using the actual coefficient
inner products (10), we obtain

\[
 E e^{iS_N}=\exp\left(-\tfrac12
       \sum_{i,j\in I}a_i a_j C_N(i,j)\right). \tag{13}
\]

This is the proposed `partial_finite_characteristic`. For `I=∅`, both sides
are1 because `P` is a probability measure; no nonempty-index assumption is
silently introduced.

On the single event `Good`, all the finitely many `B_N(i)` converge to
`B(i)` by section3. Thus `exp(iS_N)→exp(i∑aᵢB(i))` almost surely.
The integrands are measurable and have complex norm1. The dominating
constant1 is integrable since `P` is a probability measure. Apply the
actual pinned Bochner dominated-convergence theorem, with codomain `ℂ`,
to the left side of (13). On the right side use (11), finite-sum limit
rules, and continuity of the complex exponential. Uniqueness of limits gives

\[
 E\exp\left(i\sum_{i\in I}a_i B(i)\right)
 =\exp\left(-\tfrac12
       \sum_{i,j\in I}a_i a_j\min(i,j)\right). \tag{14}
\]

The vector `F_I(ω)=(B(i,ω))ᵢ` is almost everywhere measurable by the fixed-time
measurability proved in section3 and finite product measurability. Its pushforward
is a probability measure. Push it through the measurable equivalence
`MeasurableEquiv.toLp 2 (I → ℝ)` to `EuclideanSpace ℝ I`. For a test vector
`a`, the real Euclidean inner product with this random vector is exactly
`∑aᵢB(i)`. Equation (14) is therefore its characteristic function.

The target `BrownianReal.projectiveFamily I` is **literally** the pullback
of `multivariateGaussian 0 (covMatrix I)`, with `covMatrix I i j=min i j`.
The pinned `posSemidef_covMatrix I` supplies the positivity hypothesis of
`charFun_multivariateGaussian`. That theorem gives precisely the right side
of (14) for the target after applying `toLp`. Both measures are finite;
the finite-dimensional real Euclidean space is complete, has its Borel
measurable space, and is second countable. The actual pinned
`Measure.ext_of_charFun` therefore equates their Euclidean pushforwards.
Injectivity of pushforward by the measurable equivalence then gives

\[
 \operatorname{HasLaw}\bigl(F_I,
         \operatorname{BrownianReal.projectiveFamily}(I),P\bigr). \tag{15}
\]

This proves the entire FDD field for every finite `I`. No Gaussian FDD,
covariance limit, or continuous modification has been passed in as a premise.

## 7. Closing the actual Brownian predicate

The pinned `IsPreBrownianReal` structure has the single field `hasLaw I`.
Supply (15). The pinned `IsBrownianReal` extends it with the single field
`cont : ∀ᵐ ω, Continuous (B · ω)`. Supply section3's conclusion on `Good`.
This constructs

\[
 \boxed{\operatorname{IsProbabilityMeasure}(P),
        \quad\operatorname{IsBrownianReal}(B,P)}
\]

for the concrete `Sample`, `law`, and literal `B` in the declaration proposal,
with no public premises at all. The argument supplies all times `ℝ≥0` on one
space, rather than separately chosen models for individual horizons.

The remaining public heads are direct specializations of accepted pinned
`IsPreBrownianReal` consequences, with their actual binders:

* `B_hasLaw_eval t`: `gaussianReal 0 t`, from `hasLaw_eval`.
* `B_integral t`: mean0, from `integral_eval`.
* `B_covariance s t`: `min s t`, from `covariance_eval`.
* `B_hasLaw_sub s t`: centered Gaussian variance `nndist s.1 t.1`, from
  `hasLaw_sub`, including equal times and either ordering.

`B_zero` was already proved everywhere from the literal value, without invoking
only the weaker almost-sure zero-time consequence. Integrability and independent
increments, if a consumer needs them, follow from the actual returned Brownian
predicate and its existing library consequences; they need no new assumptions.

## Formal frontier and acceptance limits

The mathematics above is a complete author proof. It has not received the required
independent complete source-to-statement/proof review. The declaration file contains
no theorem bodies and has not been elaborated. There is no server kernel receipt,
transitive-axiom receipt, PR, or root acceptance claim for this unit.

The exact remaining implementation obligations are the proposed heads, especially
`good_ae`, the deterministic dyadic covariance induction `unitCov_dyadic`, its
separate-affine extension `unitCov_approx`, and the finite coefficient expansion
`partial_finite_characteristic`. These are new helper proofs to implement, not
missing public assumptions or alleged existing Mathlib APIs. All their mathematical
proofs are given above. No root shared-definition edit is required for this construction.

The next source-bound step is lane-lead review and freeze of these literal values
and exact heads, followed by implementation of the Gaussian-product and tent-series
convergence block under the established OQ4 server-only resource policy. After this
model is independently reviewed and kernel/axiom-qualified, existing arbitrary-given-
Brownian consumers can specialize it. Pure B1 remains OPEN until its other actual
dependencies, including B4 and the normalized-kernel assembly, are qualified.
