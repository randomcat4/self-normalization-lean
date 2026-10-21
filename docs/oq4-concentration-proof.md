# Closed-interval concentration from an explicit CDF error

Let μ be any Borel probability measure on ℝ. Assume L,ε≥0, a function G
with |G(x)−G(y)|≤L|x−y| for all x,y, and uniform CDF error
|μ.real(Iic x)−G(x)|≤ε. Fix a≤b.

For every δ>0, the closed interval [a,b] is contained in (a−δ,b]. The
latter has real mass μ.real(Iic b)−μ.real(Iic(a−δ)); this identity does
not discard the left atom of [a,b], because the cutoff is strictly below a.
The CDF errors and the Lipschitz estimate imply

    μ.real([a,b]) ≤ L(b−a+δ)+2ε.

For any η>0 choose δ=η/(L+1)>0. Then Lδ≤η, so the last bound is at most
L(b−a)+2ε+η. Letting η decrease to zero proves the exact closed-interval
bound. This includes a=b and bounds the full atom at a by 2ε.

For the actual standard Gaussian γ=gaussianReal 0 1, its standard library
density is (sqrt(2π))⁻¹ exp(−x²/2). The exponential factor is at most one,
and sqrt(2π)≥1 (already π≥2), so this actual density is at most one.
It is nonnegative and integrable. The actual Gaussian measure formula
therefore gives γ.real((a,b])≤b−a for a≤b by integration against the
constant density bound. Since cdf γ x=γ.real(Iic x), monotonicity and the
interval difference identity give

    |cdf γ x−cdf γ y|≤|x−y|

for all real x,y. No Gaussian Lipschitz premise is assumed.

Independently, let ν be any Borel probability law with genuinely integrable
y² and |y|³ and second moment one. For u=|y|≥0,

    2u³−3u²+1=(u−1)²(2u+1)≥0.

Integrating 3y²≤2|y|³+1, using the two genuine integrabilities and total
probability one, proves 3≤2beta+1, hence beta=∫|y|³dν≥1. No mean, density,
or fourth moment is needed.

Finally fix a natural t≥1. Its positive square root s=sqrt(t) is nonzero.
On the actual product probability Π_t, the shared prefix endpoint is
measurable. Push Π_t forward by prefixSum(·,t)/s to form an actual Borel
probability μ_t. Its Iic CDF is exactly the real product probability of
the displayed standardized sum event. Thus the stated BE-type premise is
precisely a CDF error at most ε=C_BE beta/s for μ_t and the actual standard
Gaussian comparison CDF.

Apply the first result with L=1 to the closed interval [a/s,(a+1)/s].
The preimage under the standardized sum is exactly the original closed
unit-interval event, including both endpoints and all atoms. Its mass is
at most 1/s+2C_BE beta/s. Since beta≥1, this is at most

    (1+2C_BE)beta/s.

All displayed probability and moment hypotheses remain explicit. The
module proves this BE-to-AC implication, not BE or unconditional AC.
It does not prove SP, one-sided S, O0/R3/R4, B1/Brownian inputs, K/Kv,
4/π or OQ4. No time-zero division is used, and no finite-sample density or
post-survival independence premise is introduced.
