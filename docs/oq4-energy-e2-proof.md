# EnergyE2-v1: anonymous mathematical proof

Status: complete mathematical derivation of frozen-energy-e2-bounds-v1.md; MATH_ONLY, not Lean checked and not an independent verdict. The only new analytic obligation is the specified uniform h⁻⁴ log-normalizer error on the actual finite parameter window. The remaining E2 conclusions combine certified leaves for the same actual θ and law. No Lean source, server request, check or olean emission is part of this proof-only phase.

## 1. Fixed explicit constants and actual hypotheses

First fix arbitrary real M,T≥0. Keep exactly

P=energyE1Constant(T), A=P M, J=exp(2), K=1+4A,
B=JK(A+6), H2=energyLinearCenteringThreshold(M,T)
             =energyLinearVarianceThreshold(M,T,K),
C2=1+K+K(A+2K)+(A+B)+J A.

Thus H2 is the unchanged full fourth/fifth-leaf threshold, with no replacement height or unspecified existence constant. The certified E1 domination gives P≥1. Consequently A≥0,J>0,K≥1>0,B≥0 and every displayed summand of C2 is nonnegative. In particular

1≤C2, K≤C2, K(A+2K)≤C2, A+B≤C2 and J A≤C2.           (1)

All of K,H2,C2 depend only on M,T and are fixed before the law ν, h,s or a zero parameter θ is considered.

Now fix any Borel probability ν on ℝ with genuine square/cube integrability, original second moment ∫x²dν=1, original mean ∫x dν=0 and actual β=∫|x|³dν≤M. Original id integrability is internally supplied by the fixed original-moment/E1 interfaces, not added as a premise. Fix arbitrary h≥H2 and |s|≤T.

Use exactly μ=energyTiltedLaw ν h s, L(t)=energyLinearNormalizer ν h s t, m(t)=energyLinearMean ν h s t and μ_t=energyLinearTiltLaw ν h s t. In particular μ_t remains the actual withDensity measure with density exp(tx)/L(t) under that fixed μ. Let a=K/h². The certified common-height theorem supplies h≥2 and h≥energyLogThreshold(M,T), hence h>0,h²>0,h⁴>0 and a>0. No constant is chosen after h or θ.

## 2. The genuine initial mean and derivative family

The certified first-law zero-parameter identity and actual E1 estimate, already combined in the fifth leaf, give

m(0)=∫x dμ and |m(0)|≤A/h².                             (2)

Here the original mean0 is used only through E1 to obtain the small error; it is not asserted to be μ mean0.

The derivative leaf supplies actual continuity on ℝ of m and g(t)=log L(t), and genuine HasDerivAt g (m(t)) t for every real t. Its hypotheses hold because h≥2 and the present square/cube/unitsecond/T/h/s assumptions are exactly the certified ones. L(t)>0 is supplied by the first law, never assumed. At0 its exact L(0)=1 implies

g(0)=log1=0.                                            (3)

For each u with |u|≤a, the common variance-window theorem supplies the actual genuine statement

HasDerivAt m v(u) u, where v(u)=∫(x−m(u))²dμ_u,
and 1/2≤v(u)≤2.                                        (4)

The centered square is truly μ_u-integrable. In particular |v(u)|≤2. The statement (4) is the already certified derivative interface, not an assumed variance lower/upper bound or a formal differential identity.

## 3. A uniform small bound for the actual m throughout the closed window

We first prove, for every u with |u|≤a,

|m(u)−m(0)|≤2|u|.                                      (5)

If u=0 the assertion is immediate. If u>0, m is continuous on [0,u] by its actual global continuity. Every c∈(0,u) satisfies 0<c<u≤a, hence |c|≤a. At every such c, (4) supplies differentiability and the actual derivative v(c). Thus all real mean value theorem hypotheses on [0,u] hold. It yields c∈(0,u) with m(u)−m(0)=v(c)u. Since |v(c)|≤2, its absolute value is at most2u=2|u|.

If u<0, apply the same actual mean value theorem on [u,0]. Each c∈(u,0) has |c|≤|u|≤a, so (4) again supplies its differentiability and derivative bound. The equality is m(0)−m(u)=v(c)(−u), hence |m(u)−m(0)|≤2(−u)=2|u|. This orientation handles negative parameters without assuming oddness or symmetry.

Combining (5) with (2), for every |u|≤a,

|m(u)|≤|m(0)|+|m(u)−m(0)|
      ≤A/h²+2|u|
      ≤(A+2K)/h².                                       (6)

The initial error term is retained. Equation (6) is derived for the same actual m, uniformly on the entire closed window, without using a selected θ.

## 4. The actual log-normalizer error for every small t

Fix any real t with |t|≤a. We prove

|log L(t)|≤K(A+2K)/h⁴.                                 (7)

For t=0 this follows from (3). For t>0, g is continuous on [0,t]. At each c∈(0,t), its genuine derivative m(c) is supplied by the derivative leaf. Every such c satisfies |c|≤|t|≤a, so (6) applies there. The ordinary real mean value theorem therefore supplies c∈(0,t) with

g(t)−g(0)=m(c)t.

By (3),(6) and the parameter bound,

|g(t)|≤((A+2K)/h²)|t|
      ≤((A+2K)/h²)(K/h²)
      =K(A+2K)/h⁴.                                     (8)

All multiplied factors are nonnegative and all denominators positive. For t<0, use the compact interval [t,0]. Its interior points satisfy |c|≤|t|≤a. Genuine differentiability of g and the same actual mean bound are therefore supplied pointwise there. The mean value equality is g(0)−g(t)=m(c)(−t); taking absolute values gives exactly (8), since |−t|=|t|. This proves (7) for zero and both signs, including |t|=a.

Only genuine MVT calls are used. No unproved identity log L(t)=∫₀ᵗm(u)du, no differentiation/integration interchange and no new continuity or mean-smallness premise is introduced. The constant is the exact frozen K(A+2K), with the allowed nonoptimal2K² payment unchanged.

## 5. The same centered parameter and actual law

Apply the certified fifth-leaf actual centering-law theorem with the present ν,M,T,h,s and original hypotheses. It yields a single real θ such that

|θ|≤K/h², m(θ)=0,
μ_θ is a probability,
μ_θ-almost-everywhere |x|≤2h,
x,x² and |x|³ are genuinely μ_θ-integrable,
∫x dμ_θ=0.                                             (9)

This is exactly μ_θ=energyLinearTiltLaw ν h s θ with the same original μ,L and density exp(θx)/L(θ). We do not replace the law or reselect θ for any later inequality. All moment and probability statements in (9) remain attached to this one θ.

Since θ satisfies the same parameter window, (7) applies directly. By the dominations (1), and positive h²,h⁴,

|θ|≤K/h²≤C2/h²,
|log L(θ)|≤K(A+2K)/h⁴≤C2/h⁴.                          (10)

For the actual second moment q_θ=∫x²dμ_θ, the certified common-window moment comparison gives

|q_θ−1|≤A/h+B/h².

As h≥2≥1,B≥0, one has h²≥h>0, so B/h²≤B/h. Therefore

|q_θ−1|≤(A+B)/h≤C2/h.                                 (11)

This is an estimate for the genuine second integral of the exact law from (9); no abstract moment is substituted.

For r_θ=∫|x|³dμ_θ, the certified actual normalized comparison gives

r_θ≤D_θ² r,
where D_θ=exp(2h|θ|), r=∫|x|³dμ.

The common window supplies D_θ²≤J and the actual E1 initial third bound supplies r≤A. Since r≥0 and J≥0, both genuine integral bounds combine to give

r_θ≤Jr≤J A≤C2.                                         (12)

Thus the same θ simultaneously has all the probability/support/integrability/exact-mean conclusions in (9) and all four inequalities (10)–(12) with one C2 and the one unchanged H2. No part of this assembly assumes the four bounds as inputs or re-counts the previous leaves' original obligations.

## 6. Fixed-law specialization

Now fix a single ν satisfying the original probability,square/cube-integrability,unitsecond,mean0 conditions, and T≥0. Its actual β=∫|x|³dν is a finite real number and β≥0 follows internally from its nonnegative integrand. Set M=β in all the same explicit definitions above, so the common-class premise β≤M is equality. For every h≥H2(β,T) and |s|≤T, the result of Section5 applies with no new assumption. It gives the same actual-law conclusions and four bounds with C2(β,T),H2(β,T), and a single θ satisfying them all. Neither β≥1 nor a new integrability/support/variance premise is imposed in making this substitution.

## 7. Dependency and boundary audit

The explicit constants use actual energyE1Constant,energyLinearVarianceA/B,energyLinearCenteringK and energyLinearCenteringThreshold. Their nonnegativity and common heights are supplied by the already certified E1/window/centering facts. The true initial mean and error in (2) come from energyLinearCentering_initial_mean. The actual all-real m/g continuity, g derivative and L0 identity come from energyLinear_family_continuous,energyLinear_logNormalizer_hasDerivAt and energyLinearNormalizer_zero. Each local m derivative/value/bound comes from energyLinearVariance_window, and its |u|≤K/h² condition is checked explicitly on every MVT interval. The new argument is the two MVT-based absolute-error estimates (5) and (7). The same θ and law are supplied by energyLinearCentering_law. Its second payment uses energyLinearVariance_moment_bounds; its third uses energyLinear_normalized_comparisons,energyLinearVariance_exponential_bound and energyLinearVariance_initial_bounds. No unproved analytic or probabilistic input is used.

All quantifiers remain common M,T first, then every ν,h,s. h=H2 and the weak closed t-window endpoints are included. t=0 and θ=0 are covered by the exact L0 identity. T=0,s=0 and arbitrary atoms, including closed cutoff endpoints, are retained through actual ae law support and genuine moment interfaces. There is no extra M≥1 assumption for a possibly empty class with small M. K≥1 even when A=0, but no division by A or K is used. Original id integrability is supplied internally, and original ν mean0 is never silently transferred to μ. No original bounded support, exponential/fourth moment,density,symmetry,nonlattice,selected-law substitute or extra variance/differentiability hypothesis is introduced.

This proof gives the frozen finite one-dimensional E2 analytic bound and same-law assembly only. It makes no uniqueness, measurable/continuous selector, path representation or relative-path asymptotic assertion. No E3 path/common-operator, E4 conditional-energy,K/Kv,random denominator or complete OQ4 root is closed by it. The present author artifact is MATH_ONLY: E2 remains OPEN pending its actual implementation and all independent final gates, and any later finite-E2 completion still awaits separate root/main integration. All previous32 sources and proofs, and the other author's E3 files, remain untouched.
