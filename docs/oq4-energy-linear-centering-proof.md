# LinearCentering-v1: anonymous mathematical proof

Status: complete mathematical derivation of frozen-energy-linear-centering-existence-v1.md; MATH_ONLY, not Lean checked and not an independent verdict. The only new mathematical work is the strict endpoint sign and an intermediate-value existence argument for the fixed actual linear family. All law, integrability, derivative and variance-window facts are supplied by the already certified leaves. No new Lean source, server action or olean emission is part of this proof-only phase.

## 1. Common constants, full assumptions and actual objects

First fix arbitrary real M,T≥0. Let P=energyE1Constant(T), A=P M and

K=1+4A,
Hcenter=energyLinearVarianceThreshold(M,T,K).

The last threshold is exactly the fourth leaf's Hvar, with its explicit A,B,C,J and energyLogThreshold expressions unchanged; no new or unspecified threshold replaces it. The certified E1 constant domination gives P≥1, hence A≥0. Therefore

K≥1>0 and K/2−A=1/2+A>0.                              (1)

K and Hcenter depend only on the fixed M,T and are chosen before any ν,h,s below. In particular K does not depend on h.

Fix any Borel probability ν on ℝ with genuine ν-integrability of x² and |x|³, ∫x²dν=1, ∫x dν=0 and actual β=∫|x|³dν≤M. Original id integrability is internally supplied by the certified original-moment input theorem (also by |x|≤x²+1 under probability), not assumed separately. Fix arbitrary h≥Hcenter and |s|≤T.

Write μ=energyTiltedLaw ν h s and use the same actual first-leaf functions L,A1,A2,B3,m(t)=energyLinearMean ν h s t and measures μ_t=energyLinearTiltLaw ν h s t. In particular μ_t is the actual μ.withDensity measure with density exp(tx)/L(t), interpreted with ENNReal.ofReal exactly as in its frozen definition. No alternative zero-mean law will be constructed.

Because K≥0, the certified common-height theorem applies with these exact M,T,K. It supplies h≥2 and h≥energyLogThreshold(M,T). Consequently h>0,h²>0, and

a=K/h²>0.                                               (2)

Every division in this proof is by h²>0 (or by internally positive actual L in the supplied law interfaces); none is by A,M,T or an initial mean.

## 2. Actual initial mean, continuity and derivative on the whole closed window

The first leaf's genuine zero-parameter identity gives

m(0)=m0, where m0=∫x dμ.                                (3)

The fourth leaf's actual initial-bound theorem, which internally calls E1 under the present original mean0 and β≤M hypotheses, gives

|m0|≤A/h², hence −A/h²≤m(0)≤A/h².                      (4)

The original ν mean0 is used through that genuine E1 estimate. It is not treated as μ mean0, and no such equality is asserted in (4).

The certified derivative leaf proves that the actual real function m is continuous on all of ℝ under the current original square/cube/unitsecond and T/h/s hypotheses. Those hypotheses hold since h≥2. Thus m is continuous on every compact subinterval of [−a,a], including [−a,0],[0,a] and [−a,a]. This continuity is a supplied theorem about the actual function, not a new premise.

For each real u∈[−a,a], we have −a≤u≤a, hence |u|≤a=K/h². Apply the certified actual variance-window theorem at this u, with the same fixed M,T,K,h,s,ν. It supplies genuine centered-square integrability and the actual statement

HasDerivAt m v(u) u,
where v(u)=∫(x−m(u))²dμ_u and 1/2≤v(u)≤2.               (5)

In particular m is genuinely differentiable at u and its real derivative equals v(u). No formal differentiation or derivative bound is assumed. The mean value theorem below only uses (5) at interior points, all of which belong to this already verified closed window.

## 3. Interval comparison with all mean-value hypotheses supplied

For clarity, take any real x<y with −a≤x<y≤a. Continuity of m on [x,y] follows from its actual global continuity. For each u∈(x,y), the inequalities −a≤x<u<y≤a imply |u|≤a. Thus (5) supplies differentiability there and a derivative at least1/2. These facts verify all hypotheses of the ordinary real mean value theorem on the nondegenerate compact interval [x,y].

It yields c∈(x,y) with

m(y)−m(x)=m′(c)(y−x)=v(c)(y−x).

Since y−x>0 and v(c)≥1/2, the actual difference satisfies

m(y)−m(x)≥(y−x)/2.                                     (6)

The equality m′(c)=v(c) is justified by the genuine HasDerivAt in (5), not by a separate variance formula. No derivative estimate outside [−a,a] is used. This local interval comparison suffices; no global strict-monotonicity or uniqueness theorem is claimed.

## 4. Strict signs at the actual two endpoints

By a>0, the pair x=0,y=a is a nondegenerate interval in [−a,a]. Apply (6), then (4):

m(a)≥m(0)+a/2
    ≥−A/h²+K/(2h²)
    =(K/2−A)/h²
    =(1/2+A)/h²>0.                                     (7)

Every last inequality is strict because A≥0 and h²>0. In particular no extra support/nondegeneracy or variance premise is used beyond the already proved actual window (5).

Likewise x=−a,y=0 is a nondegenerate interval in [−a,a]. Applying (6) in that orientation gives

m(0)−m(−a)≥a/2.

Using the upper initial-mean bound from (4),

m(−a)≤m(0)−a/2
     ≤A/h²−K/(2h²)
     =−(K/2−A)/h²
     =−(1/2+A)/h²<0.                                   (8)

This orientation ensures the lower derivative bound pays the left endpoint in the correct direction. Equations (7),(8) prove the requested strict signs m(−a)<0<m(a), and therefore the weak source signs as well. The positive1 in K=1+4A preserves a strictly positive margin even if A=0.

## 5. A zero parameter of the same real function

The real function m is continuous on [−a,a], and −a<a by a>0. Its endpoint values satisfy (8),(7). The intermediate value theorem for this actual continuous function therefore yields a real θ∈[−a,a] such that

m(θ)=0.                                                 (9)

The interval membership is exactly

|θ|≤a=K/h².                                             (10)

The argument is pointwise existence for every admissible ν,h,s after the common constants are fixed. It makes no claim about a measurable/continuous choice of θ as ν,h,s vary. Although strict endpoint signs locate any such zero away from the endpoints, only the frozen closed-range existence is used or returned. θ may equal0.

## 6. The same actual μ_θ is a genuine centered probability law

Use precisely the θ from (9),(10), in the frozen first-leaf definition μ_θ=energyLinearTiltLaw ν h s θ. Under h≥1,ν probability,T≥0,|s|≤T and the original square-integrability/unitsecond hypotheses, the actual first-law interfaces supply:

- L(θ)>0 and IsProbabilityMeasure(μ_θ);
- μ_θ-almost-everywhere |x|≤2h;
- genuine μ_θ-integrability of x,x² and |x|³;
- the genuine actual identity ∫x dμ_θ=m(θ).

The first three items are the existing energyLinearNormalizer_pos,energyLinearTiltLaw_isProbabilityMeasure,energyLinearTiltLaw_ae_support and energyLinearTiltLaw_moments conclusions, with their hypotheses internally supplied. In particular support is a.e. under actual μ_θ, not a new bounded-support assertion about original ν. By (9), the last identity proves the exact genuine integral centering

∫x dμ_θ=0.                                              (11)

All law conclusions refer to the same μ and same normalizer L as the endpoint/zero argument. There is no post-hoc substitution of another centered measure, conditioning operation or independent construction. All integrals involved in (11) have already been supplied with actual integrability.

## 7. Dependency and boundary audit

The common scalar definitions use actual energyE1Constant and energyLinearVarianceA, with energyE1Constant_dominates for A≥0. Common h≥2 and the E1 threshold condition come from energyLinearVariance_height_bounds with K=1+4A. The initial small mean is supplied by energyLinearVariance_initial_bounds, and the exact initial-function identity by energyLinearMean_zero. Continuity comes from energyLinear_family_continuous. The genuine derivative, centered-square value and [1/2,2] bounds at every u∈[−a,a] come from energyLinearVariance_window. The sole new analytic steps are the mean value theorem with its continuity/interior differentiability/window conditions verified in Section3, the explicit endpoint arithmetic, and the intermediate value theorem in Section5. All actual law/probability/support/moment statements come from the certified first leaf. No new unresolved probability input or assumed endpoint/variance/continuity condition is used.

Every real M,T≥0 is covered without adding M≥1; an original unit-second/cubic class with too small M may be empty, but the conditional argument remains unchanged. A=0 is harmless because K≥1 and the endpoint margin is at least1/(2h²)>0. T=0 and s=0 retain all valid interfaces. h=Hcenter and parameter-window endpoints remain covered by the weak common-height/window hypotheses; mean-value points are verified inside those same closed windows. Arbitrary atoms, including0 and closed cutoff endpoints±2h, are handled entirely by the certified actual-law a.e. support and genuine integral theorems. No density,symmetry,nonlattice,original bounded support,exponential/fourth moment or additional centering hypothesis is introduced.

This leaf proves only the strict endpoint signs, existence/range of θ for the same actual family, and the genuine centered-probability law and requested integrability/support at that θ. It proves no θ uniqueness or measurable/continuous selector, no global monotonicity assertion, no selected-θ h⁻⁴ logL estimate and no final common second/third-moment estimates. Complete E2,E3,E4,K/Kv,random denominator and all complete OQ4 roots remain OPEN. All previous31 sources and their frozen proofs are unchanged; this phase creates only this anonymous mathematical proof and an author checkpoint.
