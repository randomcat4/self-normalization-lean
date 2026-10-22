# LinearComparisons-v1: anonymous mathematical proof

Status: complete mathematical derivation of the frozen seven conclusions; MATH_ONLY, not Lean checked and not an independent verification verdict. Frozen interface: drafts/oq4/frozen-energy-linear-comparisons-v1.md. The only mathematical input beyond elementary real analysis is the actual first-leaf EnergyLinearTiltLaw interface, source SHA25663cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78, with its already fixed actual energy law. No derivative-leaf conclusion is used.

## 1. Quantifiers, actual objects and supplied integrability

Fix a Borel probability measure ν on ℝ, T≥0,h≥1,|s|≤T, with x↦x² genuinely ν-integrable and ∫x²dν=1, and, as in the frozen statement, x↦|x|³ genuinely ν-integrable. Fix an arbitrary real t. No bound on t is imposed. Write μ=energyTiltedLaw ν h s, and use the very same actual quantities

L=∫exp(tx)dμ, A1=∫x exp(tx)dμ, A2=∫x²exp(tx)dμ, B3=∫|x|³exp(tx)dμ,

μ_t=energyLinearTiltLaw ν h s t, m=A1/L,

m0=∫x dμ, u1=∫|x|dμ, q=∫x²dμ, r=∫|x|³dμ,

q_t=∫x²dμ_t, r_t=∫|x|³dμ_t, D=exp(2h|t|).

These are integrals of the fixed actual functions under the fixed actual laws, not freely supplied numbers or abstract measures. The first leaf internally provides μ and μ_t probability, μ-almost-everywhere |x|≤2h, and

0<D, 1/D≤L≤D, hence 0<L and 1/L≤D.                         (1)

Indeed its lower bound is exp(−2h|t|), whose product with D is1. The implication 1/L≤D follows from positive reciprocal order. Also D≥1 because 2h|t|≥0.

The first leaf supplies genuine μ-integrability of exp(tx), x exp(tx), x²exp(tx) and |x|³exp(tx). At parameter0 those same conclusions supply μ-integrability of 1,x,x² and |x|³. Absolute integrability of x supplies genuine μ-integrability of |x|, so u1 is an ordinary finite real integral. In particular u1,q,r≥0. It also supplies genuine μ_t-integrability of x,x² and |x|³, together with the exact identities

∫x dμ_t=m=A1/L, q_t=A2/L, r_t=B3/L.                       (2)

Thus every moment used below has its actual integrability certified before any integral subtraction or estimate. Differences of the displayed integrable functions and their absolute values are integrable, as are their constant multiples. For example |exp(tx)−1|, |x exp(tx)−x| and |x²exp(tx)−x²| are all genuinely μ-integrable. The majorants used below are respectively D|t||x|, D|t|x² and D|t||x|³, which are integrable by the same supplied moments. No statement uses a default value of a nonintegrable total integral.

The original cubic integrability assumption is retained in the frozen domain but is not needed in this proof: μ is the actual normalized closed energy truncation, so all its finite natural absolute moments already follow from its probability and almost-everywhere bounded support. Omitting that original assumption in a future formal interface would be a strengthening covering the full frozen statement, not an added hypothesis. Nothing about original ν support or exponential moments is inferred.

## 2. The pointwise exponential difference bound on the full μ-support set

For every real y,

|exp(y)−1|≤exp(|y|)|y|.                                   (3)

For y=0 both sides vanish. For y≠0, the real mean value theorem for exp on the compact interval with endpoints0,y gives a real c strictly between them with exp(y)−1=y exp(c). Every such c satisfies c≤|y|, so positivity and monotonicity of exp give (3). This argument is symmetric in the sign of y and has no atom or measure assumption.

On the same μ-full set S={x:|x|≤2h},

|tx|=|t||x|≤2h|t|, so exp(tx)≤D and exp(|tx|)≤D.

Apply (3) with y=tx to obtain

|exp(tx)−1|≤D|t||x|                                      (4)

for μ-almost every x. This is a bound on the actual μ-support set, not a globally bounded function assertion on ℝ and not an assumption about original ν support. The weak inequality includes the atoms at x=0 and x=±2h.

## 3. Four raw comparisons

Because μ is a probability and both terms are integrable, L−1=∫(exp(tx)−1)dμ. The triangle inequality for the genuine integral and then (4) give

|L−1|≤∫|exp(tx)−1|dμ≤D|t|∫|x|dμ=D|t|u1.                (5)

Likewise A1−m0=∫x(exp(tx)−1)dμ. On S, multiplying (4) by |x|≥0 yields

|x(exp(tx)−1)|≤D|t||x|²=D|t|x².

All terms are integrable as established above, hence

|A1−m0|≤D|t|q.                                          (6)

For the second numerator, A2−q=∫x²(exp(tx)−1)dμ. Since x²≥0, on S,

|x²(exp(tx)−1)|=x²|exp(tx)−1|≤D|t|x²|x|=D|t||x|³.

Integrating this genuine integrable bound gives

|A2−q|≤D|t|r.                                           (7)

Finally 0≤|x|³exp(tx)≤D|x|³ μ-almost everywhere. Genuine integrability of both sides and integral monotonicity imply

0≤B3≤Dr.                                                (8)

This proves exactly the four raw conclusions, for arbitrary real t.

## 4. Normalization: retain both error terms

By L>0 and the exact definition m=A1/L,

m−m0=((A1−m0)+m0(1−L))/L.

Consequently, using |1−L|=|L−1| and (5),(6),

|m−m0|≤(|A1−m0|+|m0||L−1|)/L
       ≤(D|t|q+|m0|D|t|u1)/L
       =(D/L)|t|(q+|m0|u1)
       ≤D²|t|(q+|m0|u1).                                (9)

The final multiplication is legitimate because |t|≥0,q≥0,u1≥0 and 1/L≤D. In particular the |m0|u1 term is retained: it is generated by normalization and would be lost by comparing only numerator deviations. The actual identity of m with the first μ_t moment is already supplied by (2).

For q_t, the exact actual identity in (2) gives

q_t−q=((A2−q)+q(1−L))/L.

Here q≥0, so (5),(7) and the same reciprocal bound yield

|q_t−q|≤(|A2−q|+q|L−1|)/L
       ≤(D|t|r+qD|t|u1)/L
       =(D/L)|t|(r+qu1)
       ≤D²|t|(r+qu1).                                   (10)

Thus the second additional normalization term qu1 and the factor D² are both exact. No centered second moment or variance interpretation is being substituted for the actual raw second moment q_t.

Finally, by (2),(8), L>0, r≥0 and 1/L≤D,

r_t=B3/L≤Dr/L=(D/L)r≤D²r.                               (11)

Also r_t≥0 follows from its nonnegative integrand, although only the upper bound is required. Equations (9),(10),(11) are precisely the three normalized comparisons.

## 5. Dependency and boundary audit

The mathematical dependencies are exactly the first leaf's actual μ probability/ae closed support, its actual weighted integral integrability for arbitrary real t and at0, the exact normalizer bounds and positivity, and the actual μ_t probability/moment integrability and quotient identities. At the named-interface level these are energyTiltedLaw_isProbabilityMeasure/energyTiltedLaw_ae_support (inherited fixed N1), energyLinear_integrability (or its stronger energyLinear_power_exp_integrable helper), energyLinearNormalizer_bounds, energyLinearNormalizer_pos and energyLinearTiltLaw_moments. Definitions of L,A1,A2,B3,μ_t,m are unchanged. All remaining steps are the real mean value theorem, integral triangle inequality/monotonicity/linearity with supplied integrability, positive reciprocal order and real algebra. No differentiation of a parameter integral, derivative-leaf result or open probabilistic input is used.

At t=0, D=1,L=1,A1=m0,A2=q,B3=r and the actual first-leaf measure identity μ_0=μ holds. The three deviation bounds and their normalized counterparts have zero right-hand sides, while the B3/r_t comparisons give equality. Both signs of t use the same |t| envelope. h=1,T=0,s=0 are allowed exactly as frozen. Probability measures with arbitrary atoms, including closed cutoff endpoints ±2h, are covered by the weak support inequality and almost-everywhere integration. Non-atomicity, density, symmetry and original centering are never used. Vanishing q,r or m0 causes no division by them; the sole division is by the internally positive L. All quantities remain finite for every fixed real t, regardless of the size of D.

The derivation adds no center,M,K,θ,variance bound, fourth moment, original ν support/exponential moment or conditional-law assumption. It proves only the seven frozen raw/normalized comparisons of the actual linear energy tilt. It gives no positive variance window, endpoint sign, selected θ, exact centering, selected-θ log bound, common final E2 constant or complete E2 result. E2/E3/E4,K/Kv,random denominator and every complete OQ4 root remain OPEN. Lean implementation/emission/checking is not authorized in this proof-only phase and has not been performed.
