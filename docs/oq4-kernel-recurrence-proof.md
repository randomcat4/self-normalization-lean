# Conditional kernel recurrence and exact normalization

Let ν be an arbitrary Borel probability measure on ℝ, h>0, a=π/(2h),
φ(w)=cos(aw), and ρ=∫cos(ay)ν(dy). Let P be the already constructed
closed-interval killed kernel and Uₙ its genuine finite-power integral
action. Put Fₙ(z)=Uₙφ(z), Gₙ(z)=Uₙ1(z), and
r(w)=Kcos(ν,a,h,w)−ρφ(w), exactly the existing cosineResidual definition.

## Test functions and positivity

The function φ is Borel and |φ|≤1 globally. If |w|≤h, then
|aw|≤(π/(2h))h=π/2, so 0≤φ(w)≤1 on the closed target interval.
For |z|≤h, every row of Pⁿ, including n=0, is almost everywhere in that
closed interval. Its integral therefore gives

    0 ≤ Fₙ(z) ≤ Gₙ(z) ≤ 1.

This uses closed-source-domain order. It never assumes global positivity
of the cosine. The endpoint values and h>0 are retained explicitly.

The one-step integral formula identifies U₁φ(w)=Kcos(ν,a,h,w) at every
real w. Since the one-step mass is at most one, |Kcos(ν,a,h,w)|≤1.
Consequently r is Borel and globally bounded by 1+|ρ|, and |r| is also
bounded Borel. Both functions are genuinely integrable against every
finite kernel row. Their finite actions are measurable and bounded by
the existing bounded-test results. No increment moment is needed.

## Exact defect identity

The true integral semigroup gives
Fₖ₊₁(z)=Uₖ(U₁φ)(z)=Uₖ[Kcos(ν,a,h,·)](z). Both Kcos and ρφ are genuinely
integrable against Pᵏ(z). Integral subtraction and real scalar linearity
therefore show, for every real z and every k≥0,

    Fₖ₊₁(z)−ρFₖ(z) = Uₖr(z).

## Conditional delayed defect estimate (D0)

Fix m≥0 and ε≥0, and assume the explicit R3-type block input
Uₘ|r|(w)≤ε for every |w|≤h. Let k≥m. Absolute-value domination first gives

    |Fₖ₊₁(z)−ρFₖ(z)| ≤ Uₖ|r|(z).

The natural subtraction identity (k−m)+m=k follows from m≤k; applying the
true semigroup yields Uₖ|r|=Uₖ₋ₘ(Uₘ|r|). The inner action is bounded Borel
and hence genuinely integrable against every outer row. Since |z|≤h,
the outer row is almost everywhere on the closed interval. Its order
comparison with the constant ε, followed by the constant integral, gives

    Uₖ₋ₘ(Uₘ|r|)(z) ≤ Uₖ₋ₘε(z) = εGₖ₋ₘ(z).

The proof includes k=m, where the outer row is δ_z, and m=0. The block
input is retained as a hypothesis, not derived here.

## Conditional block mass estimate (D1)

Let A,B≥0 and assume the R4-type input Gₘ(w)≤Aφ(w)+B for all |w|≤h.
The semigroup gives Gₖ₊ₘ(z)=UₖGₘ(z). Here Gₘ is bounded Borel with values
in [0,1]. The comparison function Aφ+B is bounded Borel globally, even
though it need not be nonnegative outside the interval. Closed-domain
order from the start z gives

    Gₖ₊ₘ(z) ≤ Uₖ(Aφ+B)(z) = AFₖ(z)+BGₖ(z).

The last equality uses genuine integrability of Aφ and of the constant B.
This holds for every k,m≥0, including both zero blocks.

## Exact normalization (D2 and D3)

Assume ρ>0 and set Fhatₙ=(ρⁿ)⁻¹Fₙ(z), Ghatₙ=(ρⁿ)⁻¹Gₙ(z).
Every power of ρ is strictly positive. Hence

    Fhatₖ₊₁−Fhatₖ = (ρᵏ⁺¹)⁻¹(Fₖ₊₁−ρFₖ).

For m≤k, the integer identity k+1=(m+1)+(k−m) is explicit. Multiplying
D0 by the positive reciprocal and using this identity gives exactly

    |Fhatₖ₊₁−Fhatₖ| ≤ [ε(ρᵐ⁺¹)⁻¹] Ghatₖ₋ₘ.

Similarly, multiplying D1 by (ρᵏ⁺ᵐ)⁻¹ and using ρᵏ⁺ᵐ=ρᵏρᵐ gives exactly

    Ghatₖ₊ₘ ≤ [A(ρᵐ)⁻¹]Fhatₖ + [B(ρᵐ)⁻¹]Ghatₖ.

These displayed factors are retained without any uniform estimate or
eigenfunction assumption.

## Finite initial-range bound (D4)

If also ρ≤1, then the nonnegative Fₙ and Gₙ remain nonnegative after
normalization. For n≤2m, monotonicity of powers of a number in (0,1]
gives ρ²ᵐ≤ρⁿ. Taking reciprocals of positive numbers reverses order.
Using Gₙ≤1 therefore yields

    0 ≤ Ghatₙ ≤ (ρⁿ)⁻¹ ≤ (ρ²ᵐ)⁻¹,
    0 ≤ Fhatₙ.

This includes n=0 and m=0; it is only the stated finite bound.

The module supplies conditional D0/D1 and their exact D2/D3/D4 algebra.
It does not prove R3/R4/O0, positivity of ρ for any moment class, uniform
block-power control, iid path equivalence, B1 initial constants, a long-time
limit, or 4/π. The root problems K, Kv, and OQ4 remain OPEN.
