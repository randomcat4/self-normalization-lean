# Anonymous proof: actual linear energy tilt law and finite integral family

Version LinearLaw-v1, for frozen-energy-linear-tilt-law-v1.md. Complete mathematical derivation, awaiting independent verification and Lean implementation. This is only the first object/interface leaf of E2, not a centering theorem. The fixed N1 energy law is used without modification.

## Objects and hypotheses

Let ν be any Borel probability law on ℝ with genuine square and absolute-cube integrability and ∫x²dν=1. Fix T≥0,h≥1,|s|≤T, and put μ=energyTiltedLaw ν h s, exactly the previously constructed law. N1 proves μ is a probability measure and |x|≤2h μ-almost surely. These are internal consequences, never hypotheses imposed on a new abstract law or a pointwise support restriction on the original ν.

For every real t define the actual integrals

L(t)=∫exp(tx)dμ,
A1(t)=∫x exp(tx)dμ,
A2(t)=∫x²exp(tx)dμ,
B3(t)=∫|x|³exp(tx)dμ,
m(t)=A1(t)/L(t),

and the actual density measure μ_t=μ.withDensity(x↦ENNReal.ofReal(exp(tx)/L(t))). These definitions contain no T,M,K or unknown θ. All integral statements below are justified as genuine integrals. In fact the first leaf uses only N1 probability/support, so some auxiliary conclusions can omit the unused original cube hypothesis while still covering the complete frozen domain.

## 1. True integrability for every positive or negative real t

On the same μ-full set |x|≤2h one has |tx|≤2h|t|. Hence

exp(−2h|t|)≤exp(tx)≤exp(2h|t|).

All functions are Borel. Their absolute values on this full set obey the finite constant bounds

|exp(tx)|≤exp(2h|t|),
|x exp(tx)|≤(2h)exp(2h|t|),
|x²exp(tx)|≤(2h)²exp(2h|t|),
||x|³exp(tx)|≤(2h)³exp(2h|t|).

Since μ is a probability measure, these almost-everywhere bounded Borel functions are genuinely integrable. The estimates are not asserted globally on ℝ, and no exponential or higher moment of the original ν is assumed. The reasoning also proves any auxiliary finite natural absolute-power exponential integrability under this same supported μ, if useful to implement the four cases uniformly.

## 2. Normalizer bounds and positivity

Integrate the two almost-everywhere exponential bounds from §1 using the genuine integrability and μ(ℝ)=1. This gives exactly

exp(−2h|t|)≤L(t)≤exp(2h|t|).

The lower bound is strictly positive for every real t. Thus L(t)>0 is proved, not assumed. There is no small-t condition, variance bound, center assumption, M bound or K parameter.

## 3. Constructed probability law and support

The real density exp(tx)/L(t) is Borel, nonnegative and genuinely integrable, with actual integral L(t)/L(t)=1. Its withDensity measure μ_t therefore has total mass one and is an actual probability measure. Since μ_t is absolutely continuous with respect to the same μ, its almost-everywhere closed support |x|≤2h follows immediately from N1's μ-a.e. support. This argument retains the weak endpoints and all atoms there; it does not replace the original ν by a globally bounded law.

## 4. Real mass and Borel test integrals

For every Borel A, exp(tx) restricted to A is genuinely μ-integrable by §1. The finite nonnegative density formula gives the real identity

μ_t.real A=(∫_A exp(tx)dμ)/L(t).

For every Borel real f such that f(x)exp(tx) is genuinely μ-integrable, its absolute value is |f(x)|exp(tx). Dividing by the proved positive L(t) preserves integrability of this density-weighted absolute function. The actual withDensity criterion proves that f is genuinely μ_t-integrable, and the Bochner density identity gives

∫f dμ_t=(∫f(x)exp(tx)dμ)/L(t).

No assertion for arbitrary nonintegrable f or parameter joint measurability is made. In particular no infinity division or default zero value of a nonintegrable real integral is used.

## 5. The actual moments and the actual mean function

Use the genuine weighted integrabilities of §1 in the test-function interface with f=x,x²,|x|³. It proves genuine μ_t-integrability of all three and the exact identities

∫x dμ_t=A1(t)/L(t)=m(t),
∫x²dμ_t=A2(t)/L(t),
∫|x|³dμ_t=B3(t)/L(t).

These are the very same actual integrals and density law defined above. No center equation or selected parameter is involved.

## 6. Zero parameter is the original energy law

For t=0, the integrand exp(0x) is identically one, so L(0)=μ(ℝ)=1. The actual density defining μ_0 is then identically one. The withDensity measure is exactly μ as a measure, not merely equal on moments. Likewise A1(0)=∫x dμ using the already established integrability, and m(0)=∫x dμ. The latter need not be zero. When s=0 the energy law μ itself is a normalized closed truncation, generally different from ν.

## Boundary and scope checks

All t∈ℝ are retained, including negative t and t=0. Cases h=1,T=0,s=0, the zero atom and ±2h atoms are included. All support statements are almost everywhere under the constructed laws. No original ν bounded-support, density, symmetry, nonlattice, atomlessness, fourth moment or linear/quadratic exponential moment is assumed.

This leaf proves no parameter derivatives for L,A1,m,log L, no common variance interval, endpoint signs, existence of θ, exact tilted mean zero, or h⁻⁴ log L/moment bounds at a chosen θ. Probability and support alone are not asserted to give positive variance. E2/E3/E4,K/Kv,random-denominator conclusions and all complete OQ4 roots remain OPEN.
