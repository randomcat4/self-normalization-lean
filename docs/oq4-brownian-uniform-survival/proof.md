# Author147: complete source-bound B0 proof proposal

Status: PROVED as a mathematical derivation from the exact producer results listed below. NOT declaration-frozen, NOT Lean-implemented, NOT kernel-checked, NOT independently reviewed, and NOT accepted. Upstream139/143/145 qualification is still a dependency. This is a proof proposal for the parent to read before freezing declarations; it is not a receipt.

## Scope and quantifiers

The original target is C:/game/shao/current/oq4/b01/proof01.md223–258, specifically (B0). Fix T>0, an arbitrary measurable space Ω, a probability measure P on Ω, and an actual given process B satisfying IsBrownianReal B P. Define

    g_T(u) = P.real {ω | ∀t ∈ [0,T], |u+B_t(ω)|≤1}.
    L(T,h) = floor(T h²).
    E_ν(T,h) = sup_{z∈[-h,h]} |killedMass ν h L(T,h) z − g_T(z/h)|.

All suprema in the proposed interface are literal real sSup of the displayed nonempty bounded image when h≥0. No countable subset of starts replaces [-h,h].

For each fixed probability law ν on ℝ satisfying integrable |x|³, integral x=0 and integral x²=1, prove E_ν(T,h)→0 as real h→+∞. The source hypotheses are exactly these actual row moment conditions. A stronger, separately labelled conclusion is proposed: given a real number M and ε>0, there is H>0, shared by every probability law ν with these moments and integral |x|³≤M, such that every h≥H and every |z|≤h has error<ε. B/P/T remain fixed outside the existential H; the proposed formal statement does not quantify uniformly over different probability spaces or Brownian representatives.

There is no public weak-limit, tightness, boundary-null, continuity, atomlessness, completeness, Brownian-existence, or desired-identity premise. The Brownian process is the actual one already given by B/P/hB. B1, canonical Brownian existence, cosine normalization, and long-time recursion are outside this unit.

## Exact imported mathematical results

KNOWN_UPSTREAM139, source SHA256 c4b3acb66c78791028df96b1d09853b7cebb0892fa3b70784761c669694b09ab:
closedSurvival is the raw all-times event above, pathSup is sSup of |u+B_t| on [0,T], every closedSurvival event is NullMeasurableSet for P, and
P{ω | pathSup B T u ω=1}=0 for every u∈[-1,1] when T>0. The endpoint results also give P(closedSurvival B T 1)=P(closedSurvival B T (-1))=0. These statements apply to arbitrary given IsBrownianReal B P and do not require completion of Ω. Qualification is pending root's needed cache and exact producer gates; no unqualified object is used here.

KNOWN_UPSTREAM143, source SHA256 1a024c4bcfc22d42d5ff73ed7e1554abbac36ea352201fa673125f5006d3f98c:
discrete_survival_tendsto_brownian takes arbitrary varying probability laws ν_j, h_j>0→∞, integrable |x|³ in every row, mean0, second moment1, a common third-moment upper bound M, a row size N_j satisfying T h_j²≤N_j, radii b_j→1, and scaled starts u_j→u∈[-1,1]. Its conclusion is convergence of the actual π_{N_j}=ν_j^{N_j} probability of the k=0-inclusive event

    ∀k≤floor(T h_j²), |u_j+prefixSum(a,k)/h_j|≤b_j

to g_T(u). Its actual source and complete frozen interface were read. It internally proves the needed weak-path limit and continuity-set passage; neither is a premise of this unit. Qualification remains dependent on139;142's already-qualified path result is not rechecked here.

KNOWN_UPSTREAM145, source SHA256 6d61f01dbece7a656fbc0948d216ebefa3772cac7eabcae067b08c57b290a659:
discrete_killed_test_integral applies to every probability law ν, l≤N, h>0, b≥0, physical z with |z|≤b*h, and bounded measurable terminal F. It proves both integrabilities and exactly identifies the actual π_N discrete-event indicator integral of F(z+prefix_l) with killedAction ν (b*h) l F z. Only this generic finite bridge is used, not145's Rademacher/B4 identity. Its exact head and complete finite-bridge proof were read; it remains not kernel-qualified.

The source-only pinned mathlib APIs for DCT, null-measurable indicators, compact subsequences and strict-subsequence divergence were read on the designated server. Requests and complete responses are preserved beside this proof. They are source evidence, not Lean receipts.

## 1. Deterministic control of the actual path supremum

Fix a sample point ω for which t↦B_t(ω) is continuous, and let

    q_u = sSup {|u+B_t(ω)| : t∈[0,T]}.

The parameter set [0,T]⊂ℝ≥0 is compact and nonempty (it contains0). The function t↦|u+B_t(ω)| is continuous. Its image is therefore nonempty and bounded above; its real supremum is well-defined in the ordinary finite sense.

For every t∈[0,T], |u+B_t(ω)|≤q_u by le_csSup. Consequently the raw condition |u+B_t(ω)|≤1 for all t≤T is equivalent to q_u≤1: one direction takes the supremum of an upper bound1, and the other bounds each term by q_u. This proves continuous_pathSup_characterization; it uses no probabilistic measurability.

For arbitrary real u,v and t∈[0,T], the triangle inequality gives

    |u+B_t| ≤ |v+B_t|+|u−v| ≤ q_v+|u−v|.

Taking the supremum gives q_u≤q_v+|u−v|. Interchanging u,v gives q_v≤q_u+|u−v|. Thus

    |q_u−q_v|≤|u−v|.

This proves pathSup_abs_sub_le, uniformly in every real u,v on this single continuous path. In particular u_j→u implies q_{u_j}→q_u, by squeezing |q_{u_j}−q_u| between0 and |u_j−u|→0.

If q_u≠1, the indicators of q_{u_j}≤1 converge to that of q_u≤1. Indeed, if q_u<1 then eventually q_{u_j}<1, so both indicators are eventually1; if q_u>1 then eventually q_{u_j}>1, so both are eventually0. The preceding characterization transfers this exact eventual equality to the indicators of the raw closedSurvival events. This proves survival_indicator_tendsto. It does not require u_j∈[-1,1].

## 2. Continuity of the actual g_T, including ±1

Fix any sequence u_j→u with u∈[-1,1]. IsBrownianReal.cont supplies one common P-almost-everywhere set of continuous sample paths, independent of all these starts. Upstream139 supplies P{pathSup B T u=1}=0 at the limiting start u, including when u is either endpoint. Their intersection is still P-full. Section1 proves, on this intersection,

    1_closedSurvival(B,T,u_j)(ω) → 1_closedSurvival(B,T,u)(ω).

Every raw event here is NullMeasurableSet by139. The constant real function1 is AEStronglyMeasurable; the pinned AEStronglyMeasurable.indicator₀ API therefore proves that every displayed indicator is AEStronglyMeasurable. Its absolute value is at most1 pointwise, and1 is P-integrable because P is a probability measure. Apply tendsto_integral_of_dominated_convergence with bound1.

For a null-measurable set s and a finite measure μ, the pinned integral_indicator₀ API identifies integral of s.indicator 1 with the set integral of1. The constant-integral formula gives μ.real s. This proves the proposed private integral_indicator_one_nullMeasurable and converts DCT exactly into g_T(u_j)→g_T(u). No replacement process, completed space, Borel representative, or hidden integrability assumption has appeared.

Restrict g_T to the subtype [-1,1]. The preceding sequential assertion applies to every convergent subtype sequence after composing with the continuous inclusion into ℝ. By SeqContinuous.continuous on the first-countable real interval, this restriction is continuous. The pinned continuousOn_iff_continuous_domRestrict gives the proposed public continuousOn_brownianSurvival.

In particular the proof gives continuity at u=1 and u=-1 within the interval. Upstream139's endpoint identities imply g_T(1)=g_T(-1)=0; continuity here never assumes a positive gap from the boundary. This eliminates the source's endpoint uniformity issue.

## 3. Exact finite-kernel attachment with correct row size

For arbitrary h>0 define

    N(T,h)=ceil(T h²),   L(T,h)=floor(T h²).

The pinned Nat.le_ceil gives T h²≤N(T,h). Upstream143.floorHorizon_le, or equivalently pinned Nat.floor_le_of_le applied to this inequality, gives L(T,h)≤N(T,h). These prove rowLength_horizon and floorHorizon_le_rowLength. We NEVER set N=L, because floor(T h²) can be strictly smaller than T h² and would violate143's horizon premise.

Let l≤N, |z|≤h, and take145.discrete_killed_test_integral with b=1 and F≡1. The constant is measurable and bounded by1. The third component of its conclusion becomes

    integral_{π_N} 1_{∀k≤l, |z/h+prefix_k/h|≤1}
      = killedAction ν h l 1 z = killedMass ν h l z.

The discrete event is measurable by143.measurableSet_discreteClosedSurvival, so pinned integral_indicator_one identifies the left side with its actual π_N real probability. This proves discrete_survival_probability_eq_killedMass, with no approximation error and no moment conditions.

The generic145 bridge includes k=0 and uses exactly the physical starting condition |z|≤h. For l=0 both sides are1 under that condition, in agreement with the identity kernel. No initial-time condition is discarded. The extra N−l coordinates are integrated out by145's proved finite-prefix law; no independent-prefix law is inserted as an assumption.

Finally |z|≤h and h>0 imply -1≤z/h≤1 by division of -h≤z≤h by h. This proves scaledStart_mem.

## 4. Actual varying-row killed-mass limit

Suppose ν_j,h_j,z_j satisfy the precise private killedMass_tendsto_brownian head: each ν_j is a probability law with integrable absolute third moment, mean0, second moment1 and the same bound M; h_j>0→∞; |z_j|≤h_j; and z_j/h_j→u∈[-1,1].

Use143.discrete_survival_tendsto_brownian with

    N_j=N(T,h_j),  b_j=1,  u_j=z_j/h_j.

All its premises are now actual row hypotheses or the elementary ceil horizon inequality from section3. The constant radius tends to1. Its conclusion is the actual finite-product event probability tending to g_T(u). For each j, section3 identifies that probability exactly with killedMass ν_j h_j L(T,h_j) z_j. Substitution proves the private killedMass_tendsto_brownian. There is no common underlying Ω for the varying rows and no attempt to apply a fixed-space Slutsky theorem to them.

## 5. Uniformity over all starts and the moment class

Fix real M and ε>0. Assume, for contradiction, that the proposed law-uniform conclusion fails. For each integer j≥0, take the positive prospective threshold j+1. Failure supplies witnesses h_j≥j+1, a probability law ν_j satisfying precisely the moment class with bound M, and z_j with |z_j|≤h_j, for which

    |killedMass ν_j h_j L(T,h_j) z_j − g_T(z_j/h_j)| ≥ ε.    (*)

Classical choice selects these actual witnesses; it adds no probabilistic or regularity property. The lower bound h_j≥j+1 gives h_j>0 and h_j→∞. By section3, u_j=z_j/h_j belongs to the compact real interval [-1,1].

Pinned IsCompact.tendsto_subseq applied to isCompact_Icc gives a strictly increasing φ:ℕ→ℕ and u∈[-1,1] such that u_{φ(j)}→u. Pinned StrictMono.tendsto_atTop gives φ(j)→∞, so h_{φ(j)}→∞ by composition. Every actual probability/moment/bound condition survives this subsequence.

Section4 applied to the subsequence proves

    killedMass ν_{φ(j)} h_{φ(j)} L(T,h_{φ(j)}) z_{φ(j)} → g_T(u).

Section2 proves g_T(u_{φ(j)})→g_T(u). Subtracting these two real convergences and applying continuity of absolute value gives the error in(*) along φ tending to0. Since ε>0, it is eventually<ε, contradicting(*) at every subsequence index. This proves uniform_brownian_survival_momentClass.

This argument covers sequences approaching ±1 exactly as it covers interior limits, and permits starts z=±h at every finite scale. It also permits atomic, lattice, asymmetric and row-varying ν. If the moment class is empty, the universal conclusion is vacuous and any H>0 works; no extra condition such as M≥1 is needed in the public head.

For a fixed source law ν, take M to be its actual finite real third-moment integral. The moment-bound premise is equality followed by reflexivity. Applying the stronger result yields uniform_brownian_survival with exactly the source's fixed-law hypotheses and all |z|≤h.

## 6. Passage to the literal supremum in B0

For every probability ν, every actual event has g_T(v)∈[0,1] by measureReal_nonneg and measureReal_le_one, and killedMass ν h l z∈[0,1] by accepted KilledIteration. Thus every absolute error lies in[0,1]. For h≥0, [-h,h] is nonempty (contains0); its error image is nonempty and bounded above by1. Its real sSup therefore lies in[0,1]. This proves survivalError_bounds without any Brownian or moment hypothesis.

If every |z|≤h has error≤a and h≥0, csSup_le applied to this nonempty image gives E_ν(T,h)≤a. This proves survivalError_le_of_forall. It needs no attainment of the supremum and no measurability or continuity of the discrete kernel in z.

Given ε>0, apply the fixed-law uniform theorem with ε/2. For all h beyond its positive threshold, each error is<ε/2 and hence≤ε/2. The preceding supremum bound gives

    0≤E_ν(T,h)≤ε/2<ε.

This is exactly E_ν(T,h)→0 as h→+∞, proving tendsto_survivalError and the source's displayed B0. The use of ε/2 prevents the invalid inference that a strict pointwise bound<ε must yield a strict supremum bound<ε.

## Declaration map, hazards and remaining gates

The accompanying declarations.lean.txt lists ALL19 proposed owned heads: 3 literal definition values (2 public,1 private),12 private theorem heads and4 public theorem heads. Sections1–6 prove each of those heads. There is no additional proposed top-level helper hidden in this plan.

Covered hazards: nonempty/bounded real sSup; arbitrary measurable Ω; raw all-times events only null-measurable; one common continuous-path full set; noatom at limiting endpoints; k=0; l=0; ceil rather than floor row coverage; varying probability instances explicit with @killedMass; all physical starts; arbitrary real scale h→∞; empty moment class; sup of strict pointwise bounds handled with ε/2.

No mathematical gap has been identified in this reduction. Remaining work is operationally explicit: parent complete reading and declaration freeze; qualification of exact139/143/145 producers; implementation of the frozen heads only; source-bound server kernel/all-owned transitive-axiom gate under the OQ4 lease; fresh qualified independent complete source-to-statement/proof review. Until those complete, B0 and the general OQ4 root remain OPEN. No novelty claim is made: this is a faithful formalization of the source's invariance/compactness argument.
