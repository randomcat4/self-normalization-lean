# Anonymous proof: actual linear energy-tilt derivatives and centered-square identity

Version LinearDerivatives-v1, for frozen-energy-linear-derivatives-v1.md. Complete mathematical derivation awaiting independent verification and Lean implementation. This is only the derivative leaf of E2, not a centering/positive-variance theorem. All previous source objects remain fixed.

## Exact objects and hypotheses

Let ν be any Borel probability measure on ℝ with genuine square/cube integrability and ∫x²dν=1. Fix T≥0,h≥1,|s|≤T. Use precisely μ=energyTiltedLaw ν h s and the first leaf's actual L,A1,A2,μ_t,m. That leaf supplies μ and μ_t probability, their almost-everywhere closed support, L(t)>0, all required weighted integrabilities, and the true quotient moment identities. These are consequences rather than new premises. No original center,M,K,θ,variance lower bound, original bounded support or exponential/fourth moment is assumed.

## 1. Local domination for the genuine differentiation step

Fix an arbitrary real t0 and put r=2h>0. On the same μ-full set |x|≤r, for every u with |u−t0|≤1,

|u|≤|t0|+1,    |ux|≤r(|t0|+1).

For j=0,1,2 this gives the uniform local bounds

|x|^j exp(ux)≤r^j exp(r(|t0|+1)).

The bounds are constants on a probability space, hence genuinely integrable. They are μ-a.e. statements jointly uniform for all u in the local interval, not global bounds on ℝ or support assumptions on ν. All tested functions are Borel in x. For each individual x, the parameter functions are genuinely differentiable for every real u, with derivatives

d/du exp(ux)=x exp(ux),
d/du [x exp(ux)]=x²exp(ux).

The first leaf supplies integrability of the functions at t0, and the j=1,2 envelopes supply integrable local derivative domination. Thus the actual dominated differentiation theorem for parameter integrals applies with every hypothesis established internally. It yields

HasDerivAt L (A1(t0)) t0,
HasDerivAt A1 (A2(t0)) t0.

There is no assumed derivative or exchange identity. Because t0 was arbitrary, these hold for every real t, including both signs and zero.

## 2. Logarithm and quotient derivatives

At every t, first-leaf positivity gives L(t)>0. Applying the actual derivative-of-log rule to L gives

(log L)'(t)=A1(t)/L(t)=m(t).

Apply the quotient derivative rule to m=A1/L, with the already proved numerator/denominator derivatives and L(t)≠0. Its derivative is

[A2(t)L(t)−A1(t)²]/L(t)²=A2(t)/L(t)−m(t)².

These are genuine HasDerivAt conclusions, with the algebraic rewriting justified by the proved nonzero denominator. The total real log and division conventions are not used at a zero/negative normalizer.

## 3. The actual centered-square integral

Fix t and write m=m(t). Under the actual probability μ_t, the first leaf proves genuine id and square integrability and

∫x dμ_t=m,     ∫x²dμ_t=A2(t)/L(t).

The identity (x−m)²=x²−2mx+m² expresses the centered square as a sum of genuinely μ_t-integrable functions: square, a scalar multiple of id, and a constant under a finite probability measure. Therefore x↦(x−m)² is genuinely integrable. Integrating the identity using actual Bochner linearity and μ_t(ℝ)=1 gives

∫(x−m(t))²dμ_t=A2(t)/L(t)−2m(t)²+m(t)²
=A2(t)/L(t)−m(t)².

Combining with §2 supplies an equivalent HasDerivAt for m whose derivative is this actual integral. Its nonnegativity follows by integration of the pointwise nonnegative square. No abstract variance notation hides missing measurability/integrability, and no strict positivity is asserted. Degenerate tilted laws may have zero centered-square integral and zero mean derivative.

## 4. Continuity from the derivatives

Each actual HasDerivAt conclusion implies continuity at that t. Since all real t were allowed, L,A1,m and log L are continuous real functions globally. This is derived from the genuine derivative results; it is not a new continuity hypothesis supplied to a later endpoint argument.

## Boundaries and scope

The argument covers h=1,T=0,s=0,t=0, all negative/positive parameters, and atoms at zero and the closed support endpoints. The domination relies solely on the same actual μ-a.e. support from the first leaf, never original ν pointwise boundedness or exponential moments. All original frozen moment assumptions remain available without adding conditions.

Only this derivative/centered-square leaf is established. No common variance interval, variance≥1/2, endpoint signs, existence/uniqueness of θ, exact mean-zero law, selected-θ h⁻⁴ log L or final moment bounds is supplied. E2/E3/E4,K/Kv,random-denominator conclusions and all complete OQ4 roots remain OPEN.
