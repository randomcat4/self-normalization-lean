# Actual finite-row killed functional limits

STATUS: PROVED mathematical candidate. NOT LEAN CHECKED. Exact consumer declarations await the lead's freeze. The two outstanding producer targets named below are mathematical dependencies, not accepted evidence. Acceptance of this consumer requires their qualification, a fresh independent complete review, and the designated-server exact-source kernel/all-owned-axiom receipt.

Author: Context143, fresh gpt-6.1-sol / xhigh, 2026-10-23. Ownership is only this directory. No Lean implementation, heavy command, cache change, Git operation, production change, or shared coordination write was made.

Frozen target: `../frozen-polygonal-killed-functional-limit-v1.md`, SHA256 `1abd3230f95fbd6a2d75e7f57c07de57f54c5af07a89caeef42f4077e805954d`. Source: `C:/game/shao/current/oq4/b01/proof01.md:9–18,255–264`. This fills the actual fixed-time killed-limit passage in section 7. It is a classical continuous-mapping/continuous-approximation argument, with no novelty claim. No B4, uniform B0, B1, long-time K/Kv or original-root closure is claimed; rawleaf increment is zero.

## 1. Exact objects and dependencies

Write I for the actual unitInterval, E=C(I,R) with its uniform norm, and W(N,h,a,t) for the accepted B3 value

    sum_{i:Fin N} max(0,min(1,t*h^2-i.val))*a_i/h.

This value is never replaced by another interpolation. Put

    X_j(a)(s)=W(N_j,h_j,a,T*s),
    Q_j=Measure.pi (fun _:Fin N_j => nu_j),
    mu_j=Q_j.map X_j,
    L_j=Nat.floor(T*h_j^2), t_j=L_j/h_j^2.

Here T>0 is the given NNReal horizon, all displayed scalar operations are on its real coercion, and every h_j>0. The row assumptions are exactly the freeze: each nu_j is a probability law, |x|^3 is integrable, its mean is zero, second moment one, and its third absolute moment is bounded by the same real M. Also h_j tends to +infinity and T*h_j^2<=N_j. The starts u_j tend to the given u in [-1,1], and NNReal radii b_j tend to 1. No membership of u_j in its own strip is imposed.

The public event and observables proposed in `declarations.lean.txt` have the literal values

    E(N,l,h,u,b)={a | forall k:Nat, k<=l -> |u+prefixSum(a,k)/h|<=b},
    F(N,l,h,u,b,a)=indicator_E(a)*cos((pi/2)*(u+prefixSum(a,l)/h)),
    G(B,T,u,omega)=indicator_closedSurvival(B,T,u)(omega)
                        *cos((pi/2)*(u+B(T,omega))).

An indicator is implemented as `Set.indicator` applied directly to the cosine; this is pointwise the displayed product. E includes k=0, not only positive times. PrefixSum is the actual finite sum from Shao.Basic.FinitePath and is defined for every natural k, so the event's measurability statements do not need l<=N.

The proof consumes these concrete producer results, only after their own gates close:

1. Accepted B3 `polygonalPath_at_grid` and `polygonalPath_on_grid_interval`, source prefix `0e9c7044`. Their complete heads and definitions were read. The latter gives the exact affine formula including fractional weights 0 and 1.
2. Accepted `PolygonalPathTightness.isTightMeasureSet_polygonalPathLaw`, source prefix `cce691cd`, with its actual unitPolygonalPath and actual pi pushforward. All its hypotheses follow from the displayed row assumptions.
3. `PolygonalBrownianWeakLimit` mathematical target, freeze SHA256 `429311c4348546d77b83bb31143bdd1e826237a28ce022ab2f026b08cabde004`: mu_j tends weakly to the law of the literal Brownian continuous-or-zero path beta defined below. This producer derives convergence from the actual RowPolygonalFDD and tightness and is not a public premise of this consumer. Author142 was active at dispatch; it is not yet qualified evidence.
4. `BrownianSurvivalBoundary`, formal freeze source prefix `dedd0892`, author source prefix `c4b3acb6`: its raw closed event is null measurable, and for T>0,u in [-1,1] its raw pathSup has zero mass at 1. Its endpoint survival probabilities are zero. Author139's source is not yet kernel-qualified and is not represented as accepted evidence here.

For arbitrary measurable Omega and the given P,B,hB, the literal path is

    beta(omega)= if (s |-> B(T*s,omega)) is continuous on I
                then that particular continuous function else zero.

The weak-path producer proves beta is P-almost-everywhere measurable, its pushforward is a probability law mu, and outside one P-null set beta(omega)(s)=B(T*s,omega) for every s in I simultaneously. This definition depends only on B,T,omega. After author142's exact proposal appeared, the consumer was bound directly to its `brownianUnitPathLaw` and probability theorem: no private copy of its path definition or measurability proof is proposed. The final public theorems mention only the raw B event and raw B_T.

## 2. Deterministic strip identity for the actual B3 sum

Fix h>0, l<=N, a:Fin N->R, any real u and radius r (the proof even allows r<0). Then

    (forall k<=l, |u+prefixSum(a,k)/h|<=r)
      iff
    (forall real t in [0,l/h^2], |u+W(N,h,a,t)|<=r).       (2.1)

For the right-to-left direction, choose t=k/h^2. Since h^2>0, 0<=t<=l/h^2. Since k<=l<=N, the accepted grid theorem gives exactly W(N,h,a,t)=prefixSum(a,k)/h.

For left-to-right, first suppose t=l/h^2. The same grid theorem and the k=l inequality prove the assertion. Otherwise 0<=t<l/h^2, so x=t*h^2 satisfies 0<=x<l. Set k=Nat.floor x and v=x-k. The real floor facts give k<=x<k+1; hence 0<=v<1 and k<l<=N. They also give t=(k+v)/h^2 and k+1<=l. The accepted affine theorem for the actual finite ramp sum gives

    W(N,h,a,t)=(1-v)*prefixSum(a,k)/h
                      +v*prefixSum(a,k+1)/h.

Thus u+W is (1-v)*(u+prefixSum(a,k)/h)+v*(u+prefixSum(a,k+1)/h). The triangle inequality, v>=0, 1-v>=0, and both grid bounds give

    |u+W| <= (1-v)*|u+prefixSum(a,k)/h|
                   +v*|u+prefixSum(a,k+1)/h|
            <= (1-v)*r+v*r=r.

This proves the finite-sum/affine/convex-absolute-value chain, not an assertion that an unspecified interpolation has the desired property. When l=0 the only time is t=0 and the endpoint case applies, so no nonexistent interval or coordinate is chosen. N=0 forces l=0. Radius zero and equality at a grid boundary are included. For negative r the grid condition is already impossible at k=0, and the argument remains valid. The final probability applications use the given nonnegative radii.

## 3. Floor horizon and exact reparameterization

For every h>0 let x=T*h^2>=0 and L=Nat.floor x. Natural-floor facts give

    0<=L<=x<L+1.

Since x<=N, Nat.floor_le_of_le gives L<=N. Let t=L/h^2 and theta=t/T. Positivity of h^2 and T gives

    0<=t<=T, 0<=theta<=1,
    0<=T-t<1/h^2,
    0<=1-theta<1/(T*h^2).                             (3.1)

In particular theta is an actual element of I for every row, including a row with L=0. Since h_j->+infinity and h_j>0, 1/h_j^2->0; multiplying by the constant 1/T and squeezing (3.1) proves theta_j->1 in R and hence in I. This uses no assertion that floors stabilize, and no eventual positivity of L_j is needed.

For theta in I and f in E define

    R(theta,f)(s)=f(theta*s).

Its range argument is in I because 0<=theta,s<=1. The map (theta,f)->R(theta,f) is continuous in uniform norm. To verify this explicitly at (theta0,f0), for all s in I,

    |f(theta*s)-f0(theta0*s)|
      <= ||f-f0|| + |f0(theta*s)-f0(theta0*s)|.

Uniform continuity of f0 on compact I makes the second term uniformly small whenever |theta-theta0| is small, because |theta*s-theta0*s|<=|theta-theta0|. This proves continuity without any regularity of the sample space Omega. It also proves the continuous-map-valued construction has the required topology; no pointwise-to-uniform shortcut is used.

For p=(theta,(v,r)) in A=I x (R x R), put

    D(p,f)=||constant(v)+R(theta,f)||-r,
    C(p,f)=cos((pi/2)*(v+f(theta))).

Both are continuous on A x E; continuity of D follows from the preceding norm-continuity, and continuity of C follows either from continuous evaluation or the same uniform-norm estimate. |C|<=1 everywhere. The norm is the actual uniform norm of a continuous real function on a nonempty compact interval, so

    D(p,f)<=0 iff forall s in I, |v+f(theta*s)|<=r.       (3.2)

For r>=0 this is the usual uniform-norm characterization. For r<0 both sides are false, since the left norm is nonnegative and the right fails at any point of I. Thus (3.2) is valid for the real r used in the private parameter space.

For a row, take p_j=(theta_j,(u_j,b_j)). Since T*theta_j=t_j, the range of s |-> T*theta_j*s is exactly [0,t_j]. If t_j=0 both are the singleton {0}; if t_j>0 its inverse is s=t/t_j. Combining (2.1) and (3.2), pointwise for every actual a,

    a in E(N_j,L_j,h_j,u_j,b_j) iff D(p_j,X_j(a))<=0.    (3.3)

Also the grid theorem at L_j gives the exact terminal equality

    X_j(a)(theta_j)=W(N_j,h_j,a,t_j)
                   =prefixSum(a,L_j)/h_j.               (3.4)

No replacement of the terminal grid time by T is made inside a row. The whole floor correction resides in theta_j. Since b_j->1 and u_j->u, p_j tends to p=(1,(u,1)) in A.

## 4. Moving continuous tests on varying row laws

We prove the following general, strictly weaker helper. Let probability laws lambda_j on E tend weakly to lambda, suppose {lambda_j} is tight, let p_j->p in A, and let H:A x E->R be continuous with |H|<=K for some fixed K>=0. Then

    integral H(p_j,f) d lambda_j -> integral H(p,f) d lambda.    (4.1)

First, on every compact K0 subset of E, H(p_j,.) tends uniformly to H(p,.). Here is a full finite-cover verification. For any epsilon>0 and each x in K0, continuity at (p,x) supplies open neighborhoods U_x of p and V_x of x such that |H(q,y)-H(p,x)|<epsilon/2 for q in U_x,y in V_x. Intersecting V_x with the open set where |H(p,y)-H(p,x)|<epsilon/2 does not lose x. Take a finite subcover V_x1,...,V_xm of K0. Eventually p_j is in all U_xi. For y in K0 choose one covering V_xi and use the triangle inequality to get |H(p_j,y)-H(p,y)|<epsilon. If K0 is empty the assertion is vacuous.

Now fix eta>0. Tightness gives compact K0 with every lambda_j(K0^c)<=delta, where choose the real delta=eta/(4*(K+1)) and use ENNReal.ofReal delta in the tightness API. K0 and its complement are Borel because E is a metric space. The uniform result eventually bounds the integrand difference on K0 by eta/2. On K0^c its absolute value is at most 2K. Every involved function is measurable and bounded, hence integrable under these probability laws. Splitting the integral yields

    |integral H(p_j,f) d lambda_j - integral H(p,f) d lambda_j|
      <= eta/2+2K*lambda_j.real(K0^c)
      <= eta/2+2K*delta < eta.

The real comparison follows from ENNReal.toReal_mono with the finite right bound; probability measures also ensure every set measure is finite. Weak convergence applied to the fixed bounded continuous test f |-> H(p,f) supplies convergence of its integrals. Adding the vanishing parameter-change difference proves (4.1).

This is an argument on actual laws on the common space E. It is not a fixed-Omega Slutsky claim, does not place different row samples on one space, and requires no coupling. The tightness premise of this private helper is discharged by the actual accepted path-tightness theorem, and its weak premise by the concrete weak-path producer in the final application.

## 5. Continuous lower/upper cutoffs and the two limits

For m in N set epsilon_m=1/(m+1)>0 and rho(x)=max(0,min(1,x)). Define real continuous functions

    ell_m(d)=rho(-d/epsilon_m),
    r_m(d)=rho(1-d/epsilon_m).

For every d,

    0<=ell_m(d)<=indicator_{d<=0}<=r_m(d)<=1,
    0<=r_m(d)-ell_m(d)<=1.                             (5.1)

Indeed if d>0, ell=0 and the indicator is zero. If d<=0, r=1, while ell is between zero and one. The inequality ell<=r follows from monotonicity of rho and -d/epsilon<=1-d/epsilon. If d<0, eventually epsilon_m<-d, hence ell=r=1. If d>0, eventually epsilon_m<d, hence ell=r=0. At d=0, ell=0 and r=1. Consequently

    ell_m(d)->1_{d<0}, r_m(d)->1_{d<=0},
    r_m(d)-ell_m(d)->1_{d=0}.                          (5.2)

The three tests ell_m(D(p,f)), r_m(D(p,f)), and ell_m(D(p,f))*C(p,f) are jointly continuous in (p,f), bounded in absolute value by 1. Their difference test r_m(D)-ell_m(D) is likewise continuous and bounded by 1. Thus (4.1) applies to each fixed m.

Write d(f)=D(p,f), and assume for the moment lambda{d=0}=0. All indicators below are Borel because D is continuous. Dominated convergence, using the integrable constant bound 1, proves

    integral ell_m(d) d lambda -> lambda.real{d<=0},
    integral r_m(d) d lambda -> lambda.real{d<=0},
    integral (r_m-ell_m)(d) d lambda -> 0,
    integral ell_m(d)*C(p,f) d lambda
      -> integral 1_{d<=0}*C(p,f) d lambda.              (5.3)

For the first and fourth limits, the pointwise limit differs from the displayed indicator only on {d=0}, a null set; integral_congr_ae removes that difference. Thus there is no assertion that a discontinuous indicator is a bounded continuous test.

For probability, (5.1) sandwiches lambda_j.real{D(p_j,.)<=0} between the lower and upper cutoff integrals. For any eta>0, first choose m so the two limiting cutoff integrals are within eta/2 of the target, then use (4.1) to make the two row cutoff integrals within eta/2 of their limits. This proves the row event probabilities tend to lambda.real{d<=0}. It also proves the result without invoking a separate Portmanteau continuity-set API.

For the signed cosine observable, let I_j=integral 1_{D(p_j,.)<=0}*C(p_j,.) d lambda_j, and J_jm=integral ell_m(D(p_j,.))*C(p_j,.) d lambda_j. Pointwise, by (5.1) and |C|<=1,

    |1_{D<=0}*C-ell_m(D)*C|<=r_m(D)-ell_m(D).

Integrability allows the norm-of-integral bound, giving |I_j-J_jm| bounded by the row difference-test integral. Fix eta>0 and choose m so the corresponding limit error integral and the limiting weighted-cutoff approximation error in (5.3) are each less than eta/4. Then choose j large enough that the error-test integral and J_jm are each within eta/4 of their limits, by (4.1). The triangle inequality bounds the final weighted-integral error by eta. This proves the cosine limit. No sign assumption on the cosine on moving strips is used; in particular b_j is allowed to exceed 1.

## 6. Brownian boundary and raw-event identification

Apply the preceding argument to lambda_j=mu_j, lambda=P.map beta, and p=(1,(u,1)). Since R(1,f)=f,

    d(f)=||constant(u)+f||-1,
    C(p,f)=cos((pi/2)*(u+f(1))).

On the single full-P-measure set supplied by the weak-path producer, the literal beta equals the given Brownian path simultaneously at every s. For each such omega the map s |-> T*s is a bijection from I onto [0,T] (T>0), with inverse t |-> t/T. A continuous real function on compact I attains its maximum absolute value. Therefore, on this full-measure set,

    ||constant(u)+beta(omega)||
       =sSup {|u+B(t,omega)| : t in [0,T]}
       =BrownianSurvivalBoundary.pathSup B T u omega,

and

    beta(omega) in {d<=0} iff omega in closedSurvival B T u,
    beta(omega)(1)=B(T,omega).                         (6.1)

In the supremum equality the image sets are literally equal through t=T*s, are nonempty (time 0 exists), and are bounded (continuity on a compact interval). Thus no total sSup convention for an unbounded exceptional path is used. Exceptional beta values can be zero; all comparisons here are almost everywhere.

The set {d=0} is Borel. Since beta is P-AEMeasurable, Measure.map_apply_of_aemeasurable identifies its lambda-measure with the P-measure of its preimage. By (6.1) that preimage is almost-everywhere equal to {omega | raw pathSup=1}. The concrete Brownian boundary theorem, using exactly T>0 and u in [-1,1], makes the latter measure zero. Hence lambda{d=0}=0, the premise used in section 5 is derived here, not added to a public target.

Likewise (6.1) and measure congruence give

    lambda.real{d<=0}=P.real(closedSurvival B T u).

The raw closedSurvival need only be null measurable; no completeness of Omega is needed. For the weighted observable, integral_map applies to beta and the Borel bounded path observable 1_{d<=0}*C. Integral_congr_ae using (6.1) gives exactly integral G(B,T,u,omega) dP.

At u=1 and u=-1 the same boundary theorem is applicable and the argument is unchanged. The producer's explicit endpoint theorem furthermore identifies the limiting raw survival probability as zero. Since |G|<=indicator_closedSurvival and the event has measure zero, its integral is zero too. We do not exclude limiting endpoints or assume the starts u_j lie in their strips.

## 7. Measurability, integrability, and completion

For every N,l,h,u,b, each actual a |-> u+prefixSum(a,k)/h is continuous. Thus each closed bound is Borel and E is a countable intersection of Borel sets (equivalently the finite intersection k<=l). This remains true at h=0 as a total real operation, although the deterministic/probability limits use h>0. Its cosine endpoint is measurable and has absolute value <=1. Its indicator is measurable and bounded by 1, so under every real probability nu its Q=pi nu integral is genuinely integrable. This proves the public event-measurability and row-integrability heads independently of the limit proof.

For the Brownian cosine, hB.toIsPreBrownianReal.aemeasurable T makes the raw endpoint cosine P-AEStronglyMeasurable and |cos|<=1 makes it integrable. The raw survival event is null measurable by the concrete boundary module; Integrable.indicator₀ gives integrability of G. The same argument applies to its indicator of the constant 1. For the identity integral indicator=real measure, use integral_indicator₀ followed by setIntegral_const; or choose the measurable representative of the null-measurable set and use measureReal_congr/integral_congr_ae. Thus the use of P.real of the raw event never assumes its exact Borel measurability, and no default-valued integral is mistaken for an expectation.

Take the actual lambda_j and p_j above. The accepted path-tightness theorem discharges tightness in (4.1); the actual weak-path target discharges weak convergence with precisely the frozen row moment, height and horizon hypotheses. Sections 2–3 supply exact row event and terminal identities, section 6 supplies the boundary-null premise and both Brownian identifications, and section 5 supplies the two limiting statements. Integral_map transfers the Borel path observables to the actual pi row space using the accepted measurable_unitPolygonalPath; equality (3.4) gives the actual terminal prefix. The results are exactly the two public heads in `declarations.lean.txt`.

Finite-prefix degeneracies need no deletion: when b_j=0, E remains a Borel closed event and every bound/identity above applies. A finite number of such rows has no effect on convergence; the proof did not even discard them. L_j=0 is treated in sections 2–3. N_j=0 is compatible with the horizon only in degenerate situations excluded here by T>0,h_j>0, but the auxiliary deterministic and integrability statements include it. Grid endpoint ties are retained, and the exit convention is strict exit/closed survival throughout. No density, atomlessness of nu_j, coupling, StandardBorelSpace Omega, complete Omega, stopping-time law, strong Markov property, reflection argument, B4 or desired maximum identity was assumed.

## 8. Formal status and next interface

All mathematical consumer steps are given above. This is a PROVED candidate using the exact two producer targets as dependencies, not a statement that either unqualified producer is accepted. The next parent action is to review/freeze `declarations.lean.txt`, preserve its direct binding to author142's literal Brownian path law, and authorize implementation only after the producer evidence gates close. No Lean source implementation or Lean/audit command was run by this context. Full independent source-to-statement/proof/definition-values review and exact-source designated-server kernel/transitive-axiom checks remain mandatory. Allowed foundational axioms remain propext, Classical.choice and Quot.sound.
