# Source contract and complete mathematical route

Status: CANDIDATE. These are proposed mathematical statements and a derivation for root freeze and later independent review. There is no new production source, Lean result or author certification. All C1/C2 original roots remain OPEN.

## Source and unchanged probability objects

Read-only originals are `C:/game/shao/current/c12/main.tex` and `supplement.tex`. Exact original hashes and accepted dependency bindings are in `checkpoint.json`.

| Candidate content | Original source | Exact obligation discharged if the candidate is later proved |
|---|---|---|
| The two complex extension definitions and real compatibility | main 650–689, especially biased pair (3.36), chord (3.37), full noise (3.38), characteristic functions (3.39), K quotient (3.40), Xi product (3.41) | Give actual analytic extensions of the same K and Xi, with Bochner L1 established; no arbitrary function is substituted. |
| Universal complex cosine inequality | supplement 3718–3727 | The actual numerator bound, including the mixed sine/sinh term. |
| All-complex K quotient and real-cone denominator conclusion | main 681–697; supplement 3728–3737 | Prove the complex chord representation and denominator control from the real cone, including its continuous value off that cone. |
| Actual tilted pair comparison and true characteristic defect | supplement 2708–2715, 2735, 3738–3744 | The defect is exactly `1 - norm(quadraticChar rho u v)^2` for `rho = nu.tilted (b*a-s*a^2)`, rather than a supplied bound or a free defect variable. |
| Natural-power matching bound | main 704–718; supplement 3746–3757 | Genuine cancellation against the matching characteristic power and original clock `T = ell*m2`. |
| Reflected matching factor, fixed eight-copy full Xi | main 660–689; supplement 3758–3760 | Controls both actual factors at one complex contour without assuming the increment law symmetric. |

The existing objects are literally the definitions copied in `dependency-interfaces.md`. `quadraticBiasedPairLaw` uses the true uncentered pair difference squared divided by `2*variance id nu`; `quadraticChordLaw` maps its product with the triangular law; `quadraticFullNoiseLaw` maps exactly two eight-copy families and the fixed scalar bump law. Neither new extension depends on `h`, `lam`, `s`, a supplied bound, a supplied characteristic defect, or a new surrogate law.

The positive-variance guard is already required for the original biased-pair probability construction. The candidate makes no probability or division claim at zero variance. Probability laws may have atoms and nonzero means.

## Genuine complex transform, probability and L1

Let `V = variance id nu > 0`, `D = A-A'`, and `Sigma = A+A'`. The old law-data theorem supplies the actual biased and chord probability laws and AE bounds `|Z1| <= 2h`, `|Y1| <= 2h|Z1| <= 4h^2`. Therefore for every complex `z,w`,

`norm(exp(i(z Z1 + w Y1))) = exp(-Im(z) Z1 - Im(w) Y1)`

is bounded by the finite constant `exp(2h|Im z|+4h^2|Im w|)`. The integrand is measurable, so this proves actual Bochner L1, then the claimed K bound by integration. Its restriction to real coordinates is the existing `quadraticChordChar` by the identical integrand, with only complex-real coercion normalization.

For the full law, its literal map and the same supports give `|Z| <= 32h+|gamma|` and `|Y| <= 64h^2`, before imposing any source gamma bound. The scalar-law support is `|V0| <= 1`; its probability and L1 data are already accepted. These finite bounds prove full-law and scalar complex L1. No application of the old support theorem's `gamma <= 2h` guard is made before that guard is paid. The scalar transform `S` in the candidate is the literal fixed-law integral, with `norm(S z) <= exp(|gamma| |Im z|)`.

For joint complex differentiability, at each `p0 = (z0,w0)` use the unit ball in `C x C`. For a real noise point `x`, the exponential has the complex Frechet derivative

`delta ↦ i*(delta.1*x.1 + delta.2*x.2)*exp(i(z*x.1+w*x.2))`.

If `|x.1| <= M1`, `|x.2| <= M2`, its operator norm on that ball is bounded by the constant

`(M1+M2)*exp((|Im z0|+1)*M1+(|Im w0|+1)*M2)`.

Use `M1=2h,M2=4h^2` for the chord and `M1=32h+|gamma|,M2=64h^2` for the full law. The derivative is measurable in the real noise point; the bound is integrable under the actual probability law. The pinned Mathlib statement `hasFDerivAt_integral_of_dominated_of_fderiv_le`, ParametricIntegral 206–212, was read on the server: it requires exactly AE pointwise derivatives on a fixed neighborhood, parameter-local AE strong measurability, center L1, derivative measurability and an integrable derivative-norm bound. These conditions are furnished here. This proves joint `Differentiable C`; it is not an assertion inferred from an old real characteristic theorem.

## Actual complex triangle and chord formula

The required new private triangle calculation is

`integral exp(i*t*r) d(quadraticTriangleLaw)(r) = if t=0 then 1 else 2*(1-cos t)/t^2`, for every complex `t`.

This is a proof obligation, not an input hypothesis. At `t=0`, use actual triangular mass one. At `t != 0`, split the density on `[-1,0]` and `[0,1]`. With `c=i*t != 0`, exact primitives are

`exp(c*r)*((1+r)/c-1/c^2)` for `(1+r)*exp(c*r)` and

`exp(c*r)*((1-r)/c+1/c^2)` for `(1-r)*exp(c*r)`.

Differentiate with respect to the real interval variable and apply the complex-valued interval fundamental theorem. Endpoint evaluation gives `(exp(i*t)+exp(-i*t)-2)/(i*t)^2 = 2*(1-cos t)/t^2`. All interval integrands are continuous. Thus no real-only formula is reused at a complex argument.

For `theta=z+w*Sigma`, use `t=D*theta`. The density-weighted triangle transform is pointwise

`(D^2/(2V))*triangleTransform(D*theta) = Q(z,w,A,A')/V`,

with exactly the Q in the candidate. Check `theta=0`, `D=0`, and neither zero separately. The first case has the exact continuous value `D^2/2`; the second vanishes. There is no singular quotient left to assert integrable. In fact

`norm(Q) <= (D^2/2)*exp(|D*Im(theta)|)`

from the actual triangular expectation. Bounded support makes this integrable under `nu.prod nu`. The density formula, actual product Fubini, and measurable chord map yield the declared K formula. The independent finite product maps similarly yield exactly `Kc(z,w)^8 Kc(-z,w)^8 S(z)` for full Xi. Each use of map/Fubini has actual complex L1 as proved above. The real restriction of full Xi is its existing integral definition.

## Complex cosine bound with the literal constant 2

Write `g=1-cos a >= 0`. The addition formula gives

`norm(1-cos(a+i b)) <= g + (cosh b-1) + |sin a| |sinh b|`.

For every real `b`, integration of the hyperbolic derivatives, or the identity `cosh b-1=2*sinh(b/2)^2`, gives

`|sinh b| <= |b| exp|b|`, `0 <= cosh b-1 <= (b^2/2) exp|b|`.

Since `sin(a)^2 <= 2g`, the square inequality gives `|sin a||b| <= g+b^2/2`. Therefore the displayed norm is at most

`g + exp|b|*(g+b^2) <= exp|b|*(2g+b^2) <= 2 exp|b|*(g+b^2)`.

All inequalities include `b=0` and arbitrary `a`; no small complex shift is assumed.

## Cone, actual tilt and explicit coefficient 144

Let `lam>=0`, `b=lam` or `b=-lam`, `0<=s<=lam^2`, and `s*h<=lam`. The actual joint tilt theorem yields probability of `rho=nu.tilted(b*a-s*a^2)`, support, positive normalizer, and actual normalized density `w` in `[exp(-4lam*h),exp(4lam*h)]` AE under nu. Its full head was read at the accepted exact hash. The general density theorem could also supply these estimates with `|b|h+sh^2<=2lam*h`. The square guard is retained for the accepted joint theorem; the slope guard is what this cone estimate uses quantitatively.

On the real cone `u!=0`, `|v|<=|u|/(4h)`, put

`t=u+v*Sigma`, `B=-b+s*Sigma`, `theta=t+i B`.

AE, `|Sigma|<=2h`, `|D|<=2h`. The triangle inequality gives `|t|>=|u|/2>0`, so `norm(theta)>=|t|>=|u|/2` and `theta!=0`, without an extra nonzero-denominator hypothesis. Also `|B|<=3lam` and `|D*B|<=6lam*h`.

Apply the cosine theorem with real arguments `D*t,D*B`, then divide by `norm(theta)^2>=u^2/4`. The pointwise bound is

`norm(Q) <= 8 exp(6lam*h)/u^2 * (1-cos(D*t)+9lam^2 D^2)`.

This bound is under the ORIGINAL untilted pair law. The accepted pair-square identity gives `E_nu D^2=2V`. The actual density of `rho.prod rho` relative to `nu.prod nu` is `w(A)w(A') >= exp(-8lam*h)`. Prove that product identity by applying the actual one-variable tilt integral identity twice to the bounded measurable pair gap (Fubini is justified since the gap lies in `[0,2]`). Thus

`E_nu[1-cos(D*t)] <= exp(8lam*h)*E_rho[1-cos(D*t)]`.

The accepted `quadraticChar_gap_identity` applies to this actual probability rho and identifies its RHS integral with exactly `1-norm(quadraticChar rho u v)^2`. It does not require rho centered, nonatomic, symmetric or variance-positive. Dividing only by the original positive V yields

`norm(Kc) <= 8 exp(14lam*h)*gap/(V*u^2) + 144 exp(6lam*h)*lam^2/u^2`.

Since `lam*h>=0`, this is at most the candidate's `144 exp(14lam*h)*(gap/V+lam^2)/u^2`. This proves both branch signs directly; no transformation of an assumed bound occurs.

## Natural powers and source clock

Under the power head's explicit `m2<=2V`, bounded support and true variance give `m2>=V>0`, hence `T=ell*m2>0` for `ell>0`. Let `z=norm(quadraticChar rho u v)`, so `0<=z<=1` by the actual probability rho. Put `g=1-z^2>=0`.

For each integer `j>=1`, `z^2<=exp(-g)` gives `z^ell<=exp(-ell*g/2)`. Maximizing the elementary scalar function, or the accepted private-style monomial-exp argument proved anew as a private helper, gives

`z^ell*g^j <= (2j/ell)^j <= (2J/ell)^j`, for `j<=J`.

For `j=0` the needed bound is simply `z^ell<=1`. This handles the zero gap, `z=0`, `z=1`, and all atoms. Binomial expansion therefore proves the genuine cancellation

`z^ell*(g/V+lam^2)^J <= (2J/(ell*V)+lam^2)^J`.

The statement does not take this inequality as a hypothesis. Since `T<=2ell*V`,

`2J/(ell*V)+lam^2 <= (1+4J)*(T^(-1)+lam^2)`.

Raising the actual complex K bound to J and combining these inequalities gives the literal `CJ=[144*(1+4J)]^J` and exponential `exp(14J*lam*h)`. For `J=0`, the result is directly `z^ell<=1`, including the `0^0` convention in natural powers. This route needs only `ell>0`, so it proves a stronger scalar-clock estimate than the source's sufficient `ell>=2J+4` restriction, while preserving the actual source application.

For full Xi, source-comparable second moment pays gamma: `m3<=h*m2<=2h*V`, hence `0<=gamma<=2h`. At the shifted contour, each unmatched K factor has norm at most `exp(2lam*h+4s*h^2)<=exp(6lam*h)` and the scalar factor at most `exp(gamma*lam)<=exp(2lam*h)`. Use the J=8 bound on the matching factor. Its coefficient is exactly `(144*(1+4*8))^8=4752^8`, and the exponential is `exp((112+48+2)lam*h)=exp(162lam*h)`.

For the reflected branch the SAME Xi product's second factor is `Kc(-z,w)=Kc(-u+i b,v+i s)`. Its real frequency is `-u` and tilt parameter is `-b`. Thus the actual matching factor is `quadraticChar reflectedRho (-u) v`, with `reflectedRho=nu.tilted(-b*a-s*a^2)`. Apply the cone calculation directly with `(-u,-b)`. The first K factor is now unmatched. No equality between the two tilted laws or their characteristic functions is asserted. This also proves both signs of b.

## Payment by the actual original source; remaining scope

The law in the source remains `nu=P_A=cond originalLaw {|a|<=h_x}`, with fixed x, `h_x=epsilon/(1+x)`. The candidate uses any support upper bound h, so the growing-y choice `h=epsilon0/(1+y)>=h_x` does not change the noise law. Source supplement 2472–2475 defines precisely the narrower real cone used here and its inclusion in the original cone.

The accepted `sourceTruncation_variance_bounds` gives `V=m2-mu^2`, `n*mu^2<=1/4`, `n*V>=1/2` and `V>0`, under its complete original normalized, centered-unconditional/truncation-budget premises. With `n>0`, these imply `mu^2<=V/2`, hence in particular `m2<=2V`. There is no conditional centering assumption. The accepted `sourceTruncation_gamma_bounds` also gives `m2<=gamma^2` and `gamma<=2h_x`. All those full unchanged heads and their source hashes are retained in the interface/binding files.

In supplement 2700–2707 and 3714–3715, `y>=2`, `N in [1/16,7]`, `lam>=y/sqrt N`, `s=0` or `s=lam*y/sqrt N`. With the original sufficiently small epsilon0 chosen `<=1/4`, `y*h<=epsilon0` and `sqrt N>=1/4`. Hence `lam>=0`, `s>=0`, `s<=lam^2`, and independently `s*h<=lam` (the last uses `y*h/sqrt N<=1`). The original `T>=L2*gamma^2>0` supplies `ell>0`. Both guards must be paid; `s<=lam^2` alone does not imply the slope guard. The case `lam=0` is included in the candidate even though the growing-y source has positive lam: it forces `b=s=0`, and the actual tilt becomes the original law. `s=0` is also fully included.

No part(c) tilted low-frequency condition `(y+lam)*Gamma<=c` is used. No Fourier inversion, contour-displacement theorem, complex derivatives of the full growing-y comparison kernel, matching odd difference estimate, outside-cone estimate, smoothing/desmoothing or original C1/C2 theorem is claimed. Those are independent downstream obligations. This unit supplies only the genuine complex-noise chord and high-frequency matching multiplier at fixed source law.

## Exact implementation obligations and evidence state

The mathematical route above leaves these new Lean bodies open: complex triangular interval integration, actual product/map complex integral bookkeeping and entire parameter differentiation, the universal cosine bound, actual tilted pair-density comparison, and natural-power cancellation. They are concrete elementary/probability obligations, not missing mathematical premises, and none appears as a hypothesis of a new head. If a formal API obstacle is discovered, report its exact interface before changing the candidate.

No Lean command was run. Only read-only server source/API and accepted-source/object hash observations were made. All future Lean/audit commands require root activation of a released worktree, exact root declaration freeze, CPU10–13, `root-heavy.lock`, native `-M8192 -j4 -DautoImplicit=false`, pinned Lean/mathlib, and the existing single-heavy-command lease. One fresh independent complete source-to-statement/proof review plus exact-source kernel/all-owned transitive-axiom receipt are still mandatory. None of those later evidence states is claimed here.
