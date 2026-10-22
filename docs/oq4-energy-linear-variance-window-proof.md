# LinearVarianceWindow-v1: anonymous mathematical proof

Status: complete mathematical derivation of frozen-energy-linear-variance-window-v1.md; MATH_ONLY, not Lean checked and not an independent verdict. The actual E1, first-law, derivative and comparison leaves are used exactly as already certified. This proof-only phase performs no server request, Lean implementation/check or olean emission.

## 1. Fixed parameters and transparent common constants

First fix arbitrary real M,T,K≥0. Let

P=energyE1Constant(T), A=PM, J=exp(2),
B=JK(A+6), C=A+5JK,
H0=energyLogThreshold(M,T),
Hvar=H0+8(1+A+B+C+K).

These are exactly the frozen explicit constants. Their order of quantification is important: K, as well as M and T, is fixed before choosing h. No T-only or M,T-only bound for arbitrary K is asserted. E1 supplies P≥1 for T≥0. Hence A≥0, while J>0, B≥0 and C≥0. The existing threshold bounds give H0≥2 (also H0≥0), from the exact formula

H0=2(1+M+T+energyNormalizerErrorConstant(T)M)

and nonnegativity of the last constant for T≥0.

Now fix h≥Hvar and s,t satisfying |s|≤T and |t|≤K/h². All summands of 1+A+B+C+K are nonnegative. Direct comparison with the defining sum therefore gives

h≥H0, h≥2, h≥8A, h≥8B, h≥8C, h≥8K.                     (1)

For example Hvar−8A=H0+8(1+B+C+K)≥0; the other three coefficient inequalities are identical termwise comparisons. In particular h>0,h≥1 and h²≥h. No division by A,B,C,K or M occurs, including when any vanish.

## 2. Actual distributional inputs and supplied integrability

Fix an arbitrary Borel probability ν on ℝ. Assume genuine ν-integrability of x² and |x|³, original second moment ∫x²dν=1, original mean ∫x dν=0, and the actual β=∫|x|³dν≤M. Original id is genuinely ν-integrable by the already proved original-moment input theorem (also directly from |x|≤x²+1 under probability); it is not a new premise. Thus the original mean assumption is a statement about a genuine finite integral. The actual β is nonnegative and finite.

Use the same actual μ=energyTiltedLaw ν h s and μ_t=energyLinearTiltLaw ν h s t, with the frozen first-leaf L,A1,A2,B3 and m_t=m(t)=energyLinearMean ν h s t. Define only transparent notation

m0=∫x dμ, u1=∫|x|dμ, q=∫x²dμ, r=∫|x|³dμ,
q_t=∫x²dμ_t, r_t=∫|x|³dμ_t,
v_t=∫(x−m_t)²dμ_t, D=exp(2h|t|).

The certified E1 theorem applies because h≥H0, with all its genuine moment, unit-second, original-center, β≤M and parameter hypotheses supplied here. It returns actual μ probability, genuine μ id/square/cube integrability and ae closed support. The first-law theorem also returns actual μ_t probability, genuine id/square/cube integrability and the exact actual identities

m_t=∫x dμ_t=A1/L, q_t=A2/L, r_t=B3/L, L>0.               (2)

Absolute integrability of id gives genuine integrability of |x| under μ. Constant functions are integrable because μ is a probability. In particular u1,q,r are finite and nonnegative. These are properties of the same actual laws, not separate abstract measures or numerical inputs. No global support or exponential-moment condition on original ν is inferred.

## 3. The common exponential bound

Since |t|≤K/h² and h>0,

4h|t|≤4K/h≤1/2≤2.                                      (3)

The middle inequality is equivalent, on multiplying by positive2h, to 8K≤h, already in (1). It remains valid when K=0; there is no cancellation or division by K. The exponential addition identity gives

D²=exp(4h|t|)≤exp(2)=J.                                (4)

This explicitly supplies the frozen D²≤J, uniformly for every t in the entire closed window. Every exponential is finite for the fixed real parameters.

## 4. E1 small errors and initial raw-moment coarse bounds

The true E1 estimates and β≤M, multiplied only by nonnegative P and divided by positive h or h², give

|q−1|≤Pβ/h≤A/h,
|m0|≤Pβ/h²≤A/h²,
r≤Pβ≤A.                                                 (5)

The small terms in (5) are retained as explicit outputs for the subsequent comparison. From h≥8A and h>0,

A/h≤1/8,
A/h²≤A/h≤1/8.                                           (6)

The second inequality uses A≥0 and h²≥h, not A>0. Therefore

q≤1+|q−1|≤1+1/8≤2,
|m0|≤1/8≤1.                                             (7)

For all real x, |x|≤1+x². Both sides are genuinely μ-integrable: |x| from absolute integrability of id, and 1+x² from probability and actual square integrability. Actual integral monotonicity and total mass1 imply

u1≤∫(1+x²)dμ=1+q≤3.                                   (8)

Together (5),(7),(8) give exactly q≤2,u1≤3,|m0|≤1,r≤A, as internally proved conclusions. Neither a centered μ nor a variance estimate has been assumed.

## 5. Specialize the certified normalized comparisons

The comparison leaf applies to these same actual laws because h≥1 and all its original square/unit-second/probability/T/h/s premises hold. No comparison error is supplied as an input. Its actual normalized conclusions include

|q_t−q|≤D²|t|(r+qu1),
|m_t−m0|≤D²|t|(q+|m0|u1).                              (9)

Every integral and quotient in (9) is the genuine one in (2), with actual integrability and L positivity already internally certified. Using r≤A,q≤2,u1≤3, all nonnegative, gives

r+qu1≤A+6.

By (4), the parameter bound and nonnegativity,

|q_t−q|≤J(K/h²)(A+6)=B/h².                             (10)

The triangle inequality for real numbers, followed by (5),(10), gives

|q_t−1|≤|q_t−q|+|q−1|≤A/h+B/h².                       (11)

From h≥8B,h≥1 and B≥0, exactly as in (6), B/h²≤B/h≤1/8. Hence

A/h+B/h²≤1/8+1/8=1/4,
|q_t−1|≤1/4.                                           (12)

For the mean, q+|m0|u1≤2+1·3=5 by (7),(8). Retaining the initial mean error in (5), rather than assuming it is zero, yields

|m_t|≤|m0|+|m_t−m0|
     ≤A/h²+J(K/h²)·5
     =(A+5JK)/h²=C/h².                                 (13)

Finally h≥8C,h≥1,C≥0 imply C/h²≤C/h≤1/8≤1/2. Thus

|m_t|≤C/h²≤1/2.                                        (14)

Equations (10)–(14) are the precise normalized specializations required by the frozen statement. No coarse estimate was substituted for either preserved initial E1 small quantity, and the constants B=JK(A+6), C=A+5JK remain unchanged.

## 6. Genuine centered-square integral and the window [1/2,2]

The certified derivative leaf supplies genuine μ_t-integrability of x↦(x−m_t)² and its exact identity

v_t=∫(x−m_t)²dμ_t=A2/L−m_t²=q_t−m_t².                 (15)

The last equality uses the actual second-moment identity (2). This is an identity of a true integrable centered square under the same actual probability μ_t. It neither identifies the uncentered q_t with variance nor assumes m_t=0. Actual μ_t probability and genuine id and square integrability have already been supplied in Section2.

From (12), 3/4≤q_t≤5/4. From (14), 0≤m_t²≤1/4. Consequently (15) gives

v_t≥3/4−1/4=1/2,
v_t≤q_t≤5/4≤2.                                         (16)

Thus the actual centered-square integral belongs to the closed interval [1/2,2], with exactly the requested lower and upper constants. Its positivity is a conclusion of these numerical estimates, not a hypothesis used in proving them.

For the optional derivative-interface summary, invoke the certified actual theorem energyLinearMean_hasDerivAt_centeredSquare with the present original cube-integrability hypothesis and the already supplied square/unitsecond/T/h/s conditions. It gives the genuine statement

HasDerivAt (energyLinearMean ν h s) v_t t.               (17)

This call is to a genuine all-real-parameter theorem with internally proved local integral dominance. It is not a formal differentiation step or a newly assumed differentiability premise. Combining (16),(17) returns the real derivative together with its actual integral value in [1/2,2], including at endpoints of the current closed parameter window.

## 7. Dependencies, quantifiers and boundary audit

The numerical constant facts use energyE1Constant_dominates and energyLog_threshold_bounds, hence the exact already frozen P and H0. Section4 uses energyE1_common_bounds on the actual law. Section5 uses energyLinear_normalized_comparisons from frozen sourcef1aa93d33998f5365d236b9f96e2e04cab4e6235672a7b634988cd2330497cd4. Actual μ_t probability and genuine moments/quotients come from first-law source63cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78. Section6 uses energyLinear_centeredSquare_integral and energyLinearMean_hasDerivAt_centeredSquare from derivative sourcef84467d102660c9abfa09062d1dbe8b3c499058b9960d779aa86fcd653b9a6b2. Original id integrability is internally available from energyTilt_original_moment_inputs. No other unresolved or probabilistic input is used.

M,T,K are fixed first; Hvar depends exactly on all three. The assertions are uniform over every admissible actual ν,h,s,t thereafter. All division is by positive h,h² or internally positive L; A,B,C,K are allowed to vanish. In particular K=0 forces t=0, B=0,C=A and every calculation above remains valid. T=0 forces s=0 but does not change any proof. Zero and endpoint atoms are treated through actual ae closed support and integrable identities, without deleting boundary mass. h=Hvar and |t|=K/h² are preserved by weak inequalities throughout. For M<1 the original unit-second/cubic class may be empty; the conditional proof does not add M≥1 or use nonemptiness, and its scalar constant bounds remain valid for every M≥0.

The only original centering used is the frozen ∫x dν=0 needed for the true E1 mean bound. It is not transferred as μ or μ_t centering. No original bounded support, exponential/fourth moment, symmetry,density,nonlattice,selected θ or a priori variance hypothesis is added. Genuine probability, support, integrability and derivative conclusions are internally supplied, never made additional inputs. The proof selects no K(M,T), proves no endpoint sign or θ existence/uniqueness, and establishes no selected-θ log/moment error or complete common E2 constant. E2,E3,E4,K/Kv,random denominator and every complete OQ4 root remain OPEN.
