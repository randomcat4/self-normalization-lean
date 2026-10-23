# Actual joint tilted law, original part (c), and low-frequency powers

State: `CANDIDATE_COMPLETE_AWAITING_ROOT_FREEZE_NOT_LEAN_CHECKED`.
Owner: `/root/common_tilted_low_author`; actual model `gpt-6.1-sol/xhigh`.
Only `drafts/c12-tilted-low-frequency/` is writable in this phase. No Lean,
production source, remote Git mutation, package write, or independent review
has been performed for this candidate.

## Original identity and exact scope

Read-only original `C:/game/shao/current/c12/supplement.tex` has SHA256
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.
The original main article is `C:/game/shao/current/c12/main.tex`; its hash is
recorded in the checkpoint. The original source is unchanged.

| Original source | Meaning | Exact proposed payment or result |
|---|---|---|
| main 372–383 | `0 < epsilon0 <= 1`, `epsilon <= epsilon0/2`; `eta(epsilon) <= epsilon^3/8` and `eta(epsilon) <= epsilon^2 eta0/40` | The source head takes the actual budget `R <= epsilon^3/8` and the original epsilon constraints. The stronger eta/eta0 term is unnecessary for the base drift bound proved here. |
| main 638–640 | `y >= gamma`, `abs(y-x) <= 1/(2(1+x))` | The literal half-window is an input. In the growing branch `y >= 2`, the `gamma <= y` guard is actually derived from `gamma <= 2h_x <= 2h <= 2/3`. |
| supplement 463–477 | `A` is the actual fixed-cutoff conditional law; `mu=E A`, raw absolute moments, `V=m2-mu^2`, `gamma=m3/V` | Both source-law and tilted-law quantities are literal integrals and `variance id` of those literal measures. Conditional centering is never assumed. |
| supplement 522–531 and 2045–2139 | conditional moment and budget payments | Reuse accepted source interfaces at their exact bytes. Derive `n abs(mu) <= epsilon/(4(1+x)) <= 1/2` from the actual budget. |
| supplement 2700–2707 | `h=epsilon0/(1+y)`, `h_x<=h`; `T=(n-i)m2`, `N=q+T`; `y>=2`, `N in [1/16,7]`, `lambda>=y/sqrt N`, `s in {0,lambda y/sqrt N}` | The source head contains the literal actual `N=q+T` and the two choices of `s`. It derives both `0<=s<=lambda^2` and `s*h<=lambda`; the latter uses the explicit realization `y*h<=1/4` of original sufficiently small `yh`. |
| supplement 2709–2715 | actual density `exp(+-lambda*a-s*a^2)/Z` | `rho=nu.tilted (fun a => b*a-s*a^2)` with `b=lam` or `b=-lam`. The accepted producer identifies its actual measure and moments. |
| supplement 2718–2729 / 3551–3597 | original parts (a),(b), density, variance, third moment, mean, normalizer | Consume the qualified producer `boundedQuadraticTilt_joint_moments_normalizer`, with `Gamma=8*exp(8*lam*h)*(m3/V)` and `exp(+-4*lam*h)` variance comparison. These proofs are not repeated or changed. |
| supplement 2730–2739 / 3599–3625 | original part (c), small tilted mean, raw-second/variance comparison and actual characteristic powers | The proposed heads prove `abs(murho)<=sqrt(Vrho)`, `murho^2<=Vrho`, `Vrho<=m2rho<=2Vrho` under the explicit original-form condition `(y+lam)*Gamma<=1/8`. They also prove `sqrt(m2rho)<=Gamma`, `m2rho<=Gamma^2` and both actual characteristic powers with frequency constant `1/128` and decay coefficient `exp(-4*lam*h)/128`. |
| supplement 3147–3191 | original low-frequency independent-copy proof; Lyapunov | Reuse the accepted actual-law damping theorem, then raise the actual characteristic function to the actual remaining natural power. No abstract decay envelope replaces the characteristic integral. |
| supplement 2880–2893, 2935–2974 | specific later choices of lambda and the eventual payment of tilted smallness from eta0 | Not covered here. An arbitrary permitted lambda can be arbitrarily large, so the source guards alone cannot imply `(y+lam)*Gamma<=1/8`. The exact smallness stays visible as a comparison antecedent. |

The original displayed `m_r=E|A|^r` agrees with the head's `m2=integral a^2`
because `abs(a)^2=a^2`. There is no raw/centered third-moment substitution.
The exact real-frequency characteristic definition consumed is

```lean
noncomputable def quadraticChar (nu : Measure ℝ) (u v : ℝ) : ℂ :=
  ∫ a : ℝ, Complex.exp
    (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂nu
```

Thus `norm ((quadraticChar rho u v)^ell)` is exactly
`abs(phi_{+- ,s}(u,v))^ell`, using `norm_pow`. No contour extension is encoded.

## Consumed complete interfaces and qualification

The candidate reads the full consumed declaration heads and the values of
`quadraticChar`, `truncationBudget`, and `truncationF`. File hashes are recorded
in `checkpoint.json`. Reading old complete proofs or old full reports is not
required to reuse their already-qualified exact source versions.

1. `drafts/c12-bounded-quadratic-tilt/BoundedQuadraticTilt.lean`, SHA256
   `93c302d9de61bc4bf0cb238e82a4ed5b7f66e0ddbd2e833fec5bc6bbb25a8257`.
   Exact producer commit `5e1a6a7fef2121bc0208798f7a0678975b44a0e9`, object
   `cd1e326090a3fce3ecab7d8b38c14d7239c6b4fcedb600f8bb8dffb14d3dc2ec`.
   Root reports qualified complete independent review CORRECT at
   `coordination/common-bounded-quadratic-tilt-review.md`, SHA256
   `3f6c037bdecb6b989040a013fe8575eac35073923b986edc22be355823c44ec8`.
   Consumed complete head: `boundedQuadraticTilt_joint_moments_normalizer`.
   It supplies actual probability/support, finite moments, the exact variance
   identity, the mean bound `exp(4lamh)(abs(mu)+lam*m2+s*m3)`, variance factors
   `exp(+-4lamh)`, and positive-variance/actual-third-ratio facts. Actual Lean
   upstream binders are quoted `«λ»`/`«hλ»`; this candidate uses ASCII `lam`.
2. `library/Shao/Probability/LowFrequencyDamping.lean` complete consumed head
   `Shao.Probability.quadraticChar_lowFrequency_damping`: probability law,
   finite raw absolute third moment, positive actual variance, and frequency
   bounds `abs(u)<=1/(128*actualGamma)`,
   `abs(v)<=abs(u)/(128*actualGamma)` imply the two actual norm bounds
   `exp(-actualV*u^2/32)`, including the `-u` branch.
3. `library/Shao/Probability/SourceTruncationBridge.lean`, complete consumed
   heads `Shao.sourceTruncation_law_data`,
   `Shao.sourceTruncation_paid_moments`,
   `Shao.sourceTruncation_variance_bounds`. The first supplies the exact
   closed-cutoff conditional probability law, support, and finite moments.
   The second supplies `n*abs(mu)<=2R/(epsilon^2*(1+x))` and finite third
   moments. The third supplies the actual variance identity and
   `3/4<=n*m2<=4/3`, `n*mu^2<=1/4`, `0<V`, `1/2<=n*V<=4/3`.
4. `library/Shao/Probability/SourceFourierScale.lean`, complete consumed head
   `Shao.sourceTruncation_gamma_bounds`: actual `m3>0`, `gamma>0`,
   `sqrt(m2)*m2<=m3`, `m2<=gamma^2`, `gamma<=2h_x`, and source-scale bounds.
   Its existing private polynomial Lyapunov proof was read for API/route
   compatibility; a private same-polynomial helper may be needed for the
   generic tilted law because the existing helper is private. This is no
   extra public wrapper or global definition.

`Shao.truncationF z = z^2 * min |z| 1` and
`Shao.truncationBudget nu0 n x = n * integral (truncationF ((1+x)*z))`.
The third moment can be finite only after actual truncation; no global third
moment of `nu0` is assumed or used.

## Complete mathematical proof route for generic head

Write `a=lam*h>=0`, `tau=sqrt V`, `taurho=sqrt Vrho`. Every integral below is
with respect to its displayed actual measure. Bounded support and probability
make the first, second, and absolute third moments integrable: bound each
absolute power by `h^k` and use integrability of a constant.

1. From `n*V>=1/2` and `n>=0`, obtain `n>0` and `V>0`. The ordinary variance
   identity gives `V=m2-mu^2<=m2`, so `m2>0`. Comparing the two paid scaled
   bounds gives `m2 <= (8/3)*V`: indeed
   `n*m2<=4/3<=(8/3)*(n*V)` and cancel positive `n`.
   Likewise `n*abs(mu)<=1/2<=n*V`, so `abs(mu)<=V`.
2. For any of the two bounded probability laws with second moment `M2`,
   third absolute moment `M3`, and `t=sqrt M2`, use the pointwise factorization

       0 <= (abs(z)-t)^2 * (2*abs(z)+t)
         = 2*abs(z)^3 - 3*t*z^2 + t^3.

   Integrate it, use probability mass one and `t^2=M2`. This gives
   `t*M2<=M3`. Consequently, when actual variance `W>0`,
   `sqrt(M2)*W<=M3`, hence `sqrt(M2)<=M3/W`. This also implies `M3>0`.
   For the base law this proves
   `tau<=sqrt(m2)<=gamma`, `m3>0`, and `gamma>0`.
3. Apply the accepted literal joint-tilt producer with the frozen `h,lam,b,s`
   guards. Its output gives probability and support for `rho`, finite first,
   second, third moments, `Vrho=m2rho-murho^2`,

       exp(-4a)*V <= Vrho <= exp(4a)*V,
       m3rho/Vrho <= Gamma = 8*exp(8a)*gamma,
       abs(murho) <= exp(4a)*(abs(mu)+lam*m2+s*m3).

   Thus `Vrho>0` and `Gamma>0`. Apply step 2 to the actual `rho` law to get
   `sqrt(m2rho)<=m3rho/Vrho<=Gamma`. Square nonnegative quantities to obtain
   `m2rho<=Gamma^2`. These two outputs need no tilted-smallness assumption.
4. To prove the conditional comparison, the base payments from step 1 and
   step 2 give, with positive `tau`,

       abs(mu)/tau <= V/tau = tau <= gamma,
       m2/tau <= (8/3)*tau <= (8/3)*gamma,
       m3/tau = gamma*tau <= gamma^2.

   Taking positive square roots in `Vrho>=exp(-4a)*V` gives
   `taurho>=exp(-2a)*tau`. Divide the accepted mean bound by positive
   `taurho`, use this square-root lower bound and the three base estimates:

       abs(murho)/taurho
         <= exp(6a)*(gamma+(8/3)*lam*gamma+s*gamma^2).

   All factors multiplied here are nonnegative. Since `a>=0`, the definition
   of Gamma implies

       exp(6a)*gamma <= Gamma/8,
       exp(6a)*(8/3)*lam*gamma <= lam*Gamma/3,
       exp(6a)*s*gamma^2
         <= exp(6a)*lam^2*gamma^2 <= (lam*Gamma)^2/64.

   The last comparison uses `s<=lam^2` and `exp(6a)<=exp(16a)`.
   Put `k=(y+lam)*Gamma`. Then `0<=k`, `Gamma<=k/2` (because `y>=2`),
   and `0<=lam*Gamma<=k`. If `k<=1/8`,

       abs(murho)/taurho <= k/16+k/3+k^2/64
         <= 1/128+1/24+1/4096 < 1.

   This proves `abs(murho)<=taurho`, hence `murho^2<=Vrho`. The exact variance
   identity yields `Vrho<=m2rho<=2*Vrho`. No assumption of small `lam*h` was
   used; its exponential cost was absorbed by the defined Gamma.
5. For the low-frequency outputs define the actual positive
   `gammarho=m3rho/Vrho`. Step 2 for `rho` proves it is strictly positive,
   and the accepted producer bounds it by Gamma. Since each numerator in
   the frequency restrictions is nonnegative, the displayed bounds with
   denominator Gamma imply the accepted damping bounds with denominator
   `gammarho`. Therefore for either frequency sign

       norm(quadraticChar rho (+-u) v)
         <= exp(-Vrho*u^2/32).

   Raise the nonnegative sides to the natural `ell` and use `norm_pow` and
   `exp(t)^ell=exp(ell*t)`. Moreover

       Vrho >= exp(-4a)*V >= exp(-4a)*(3/8)*m2,
       ell*Vrho*u^2/32 >= (3/256)*exp(-4a)*(ell*m2)*u^2
                       >= (1/128)*exp(-4a)*(ell*m2)*u^2.

   Monotonicity of real exponential proves the literal desired power bounds.
   This step never uses `k<=1/8`. For `ell=0` both norms and upper bounds are
   one. For `u=0`, Gamma positivity forces `v=0`; the accepted theorem already
   includes this case. No positive lower bound on remaining clock is needed.

## Complete original-source parameter payment

1. Put `h_x=epsilon/(1+x)`, and let `nu=cond nu0 {abs(z)<=h_x}` exactly as in
   the source head. From `epsilon<=epsilon0/2` and `epsilon0<=1` infer
   `epsilon<=1/2`, so all accepted source-bridge hypotheses hold. Reuse their
   probability, support, integrability, exact variance, and scaled moment
   conclusions. There is no supplied conditional mean or variance input.
2. The paid mean and actual budget give, using `epsilon>0` and `1+x>=1`,

       n*abs(mu) <= 2R/(epsilon^2*(1+x))
         <= epsilon/(4*(1+x)) <= 1/8 <= 1/2.

   This alone supplies the generic mean payment. The original bound on
   `Lambda_y` from eta/eta0 is stronger but is not necessary here.
3. The half-window implies `y<=x+1/(2*(1+x))` and hence
   `1+y<=2*(1+x)`. As both denominators and epsilon0 are positive,

       h_x = epsilon/(1+x)
           <= (epsilon0/2)/(1+x) <= epsilon0/(1+y) = h.

   Thus actual nu support is within `h>0`, and the generic law is the same
   conditional law, not a new truncation. Source gamma bounds give
   `0<gamma<=2h_x<=2h<=2/3<=y`, paying the original comparison-threshold guard.
4. `m2>=0` and `0<=n-i<=n` give `0<=T<=n*m2<=4/3`. `N=q+T` is the literal
   expression used in all three clock-dependent hypotheses. Its lower guard
   gives `N>0` and `sqrt N>=1/4`. With `r=y/sqrt N`, obtain `0<=r<=4y` and
   `lam>=r>=0`.
5. If `s=0`, both needed guards are immediate. If `s=lam*y/sqrt N=lam*r`,
   use nonnegative lam and `r<=lam` to get `0<=s<=lam^2`. Separately,

       s*h = lam*r*h <= 4*lam*y*h <= lam,

   by `y*h<=1/4`. This is the actual payment of the second indispensable
   upstream guard. `s<=lam^2` alone would not pay it. `N<=7` remains the
   original upper clock context and is not used to invent a stronger bound.
6. Apply the generic theorem to these actually derived hypotheses and take
   `ell=n-i`. The literal T is exactly its exponent's remaining raw-second
   clock. Include all the paid source facts in the one bundled source output.
   The smallness comparison remains conditional because arbitrary permitted
   lam is not controlled above by the source guards.

## Boundary, independence, and remaining obligations

The joint sign is selected by `b=lam or b=-lam`; neither sign changes any
absolute-moment payment. Natural powers include zero. The original use
`1<=i<=n` is covered by the stronger `i<=n` result; `q>=0` and `N<=7` preserve
the actual original clock window. The original `T>=L2*gamma^2` restriction is
needed for later Fourier region estimates, not this true local damping
argument, and is not artificially imposed here.

The power theorem is for the actual one-coordinate characteristic function.
It does not itself construct a product law or a contour shift. Existing iid
product/tilt factorization can consume it later; no iid premise is needed for
the algebraic characteristic power stated here.

Still unpaid after this candidate: root freeze; production implementation;
exact-source server kernel and all-owned transitive-axiom receipts; qualified
fresh independent complete source-to-statement/proof review; later prescribed
lambda/eta0 payment of `(y+lam)*Gamma` where needed; complex shifts and actual
growing-kernel amplitude/derivative integration; survival/Spitzer and weighted
regulator second moments; microclock/large-displacement budgets; desmoothing
and original C1/C2 closure. All original root groups stay OPEN.

This is original-claim formalization, not a new theorem/new-prior-art claim.
No external search or novelty assertion is needed to identify its original
statement: the exact supplied local primary sources are read directly.
