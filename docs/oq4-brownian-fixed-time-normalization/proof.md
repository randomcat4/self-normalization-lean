# Fixed-time normalization of the actual killed cosine

STATUS: PROVED mathematical candidate from the exact producer statements below. NOT LEAN CHECKED, NOT INDEPENDENTLY QUALIFIED, and not a root-closure claim. This is a complete proof and exhaustive head/value proposal for lane-lead freeze. No Lean implementation, toolchain invocation, import/object check, kernel command, Git operation, cache write or shared-source change was made by this author.

Author148: fresh gpt-6.1-sol / xhigh, 2026-10-23. Ownership is only this directory. The prescribed math-theorem proof workflow is used; no math-ultra workflow or additional agent was started.

## 1. Original source and exact statement

Read-only source: C:/game/shao/current/oq4/b01/proof01.md, assumptions9–18, actual free coefficient177–186, and B1/B4 at223–264. In source notation,

    a_h = pi/(2h), f_h(w) = cos(a_h*w),
    rho_h = E cos(a_h*Y), m_h = floor(h^2),
    rho_h^(-m_h) K_h^(m_h) f_h(0) -> 1 as real h -> +infinity.

Fix an arbitrary probability measure nu on real satisfying exactly

    Integrable (x |-> |x|^3) nu,
    integral x dnu = 0, integral x^2 dnu = 1.

The mandatory public theorem is the real atTop limit of

    (cosineCoefficient nu (pi/(2h)) ^ Nat.floor(h^2))^(-1)
        * killedAction nu h (Nat.floor(h^2)) (w |-> cos((pi/(2h))*w)) 0

to1. These are the actual unchanged project definitions. The inverse is inverse of a natural power; it is the source rho_h^(-m_h) once eventual rho_h>0 is proved below. No supplied Brownian process, weak limit, Brownian identity, symmetry, lattice, density, survival estimate, or separately assumed first/second integrability occurs in the public hypotheses. The function is total for all real h, and only its eventually positive scales matter to atTop.

The separately labelled public varying-row theorem has probability laws nu_j, positive h_j tending to infinity, the same per-row three hypotheses, and one real M bounding all actual third moments. It states all three limits: actual free power -> c, actual killed numerator -> c, and the normalized product ->1, where c=exp(-pi^2/8)>0. Its h_j positivity is the actual producer143 row interface, not an additional premise of the original real-scale fixed-law theorem. The common-M result is consistent with source9–18 and its sequential uniformity convention; it is not called a new fixed-law assumption.

## 2. Exact dependencies and qualification boundary

All following declarations, definitions and proofs were read from the specified primary artifacts.

* Actual143 PolygonalKilledFunctionalLimit source SHA256 1a024c4bcfc22d42d5ff73ed7e1554abbac36ea352201fa673125f5006d3f98c, formal head/value freeze be40d0f71abed6a2c2da2a407a21e22e1f11bbf11231d32ba0e01d089c448060. Its public discrete_killed_cosine_tendsto_brownian concerns an n_j-coordinate product row, monitors l_j=floor(T*h_j^2), and requires T*h_j^2 <= n_j. Its literal discrete event includes k=0. Its output is the integral of its literal raw Brownian killed cosine. Its producer142 is already qualified in PR199 per the lane-lead task; this author does not rerun142.
* Actual145 BrownianKilledCosineIdentity source SHA256 6d61f01dbece7a656fbc0948d216ebefa3772cac7eabcae067b08c57b290a659, formal freeze94c205a87fdb7edab61a80397c0c6bd5aeaa46f115b05e86cfc0a3673ca59733. The public generic discrete_killed_test_integral returns killed-test integrability, inclusive-event integrability and exact integral equality to actual killedAction, for n>=l, h>0, radius b>=0 and |z|<=b*h. It includes l=0. Its public brownian_killed_cosine_identity proves B4 for the actual integrand, all T>=0 and u in[-1,1].
* Frozen146 CanonicalBrownian values and final heads, mathematical freezebfd4dc50d5d1d0575446c47bb120b1bbe1c5ff109b4020cc6ec06976d9ea0586 and formal freeze145099ed6579410f0cd4092dfbb0b302a05bd998d1e910708de475b9de33ab6a. We use precisely Sample=(Nat*Nat)->Real, law=the actual infinitePi standard-normal law, its probability instance, its literal process B and unconditional isBrownianReal. Its Lévy–Ciesielski construction is independent of143/145 and of the desired B1; it supplies the Brownian data internally, not as public input to B1.
* Accepted library/Shao/OQ4/CosinePowers.lean, CosineCoefficients.lean, KilledCosine.lean, KilledKernel.lean and KilledIteration.lean. In particular cosineCoefficient is the free integral of cos(a*x), while killedAction is the integral under the actual monoid power of the strict-exit/closed-strip killed kernel. The actual accepted cosineCoefficient_large_h_bounds and cosineCoefficient_log_error_mul require lower-moment integrability, which is discharged in section3.
* Pinned elementary Mathlib integration, floor/ceil, filter, log, exp and inverse-continuity interfaces, with exact located primary types in api-evidence.md.

Actual143/145 and construction146 are frozen local mathematical/formal dependencies, not yet kernel-qualified accepted facts. The present derivation is mathematically complete from their exact stated results; acceptance waits for their qualification and this consumer's own independent complete review and exact-source designated-server kernel/all-owned-axiom receipt. We do not turn any of their conclusions into new hypotheses of the public B1 theorem. Their graph is acyclic:146 constructs Brownian data directly from a Gaussian product,143 proves a given-process row limit,145 proves given-process B4 by finite Rademacher rows, and only this assembly combines them. None assumes B1.

The source proves B4 by Itô's formula for a bounded stopped martingale. Actual145 uses the independently described alternative finite Rademacher/functional-limit proof of that same identity. This assembly preserves that attribution and does not claim a formalization of the source's Itô argument or a novelty contribution.

## 3. Lower moments and nonnegative common bound

This proves the heads lower_moments_integrable and third_moment_nonneg.

For r=|x|>=0, both r<=1+r^3 and r^2<=1+r^3 hold for every x. If r<=1, then r<=1 and r^2<=1, proving both. If r>=1, then r<=r^2<=r^3: multiply r>=1 first by r>=0 and then by r^2>=0. The square identity x^2=|x|^2 gives

    ||x|| = |x| <= 1+|x|^3,
    ||x^2|| = x^2 <= 1+|x|^3.

The dominating function1+|x|^3 is integrable because nu is finite and the third absolute power is integrable. Identity and square are Borel measurable, hence almost-everywhere strongly measurable. Integrable.mono' applied to these pointwise norm bounds proves integrability of x and x^2. This does not infer integrability from the mere existence of the totalized real integral used in the mean/second-moment hypotheses.

Since |x|^3>=0 everywhere, integral_nonneg gives beta(nu)=integral|x|^3 dnu>=0. The latter auxiliary statement even holds for any real measure without a probability assumption. In its actual uses h3 guarantees beta is the genuine finite expectation.

For the varying-row hypotheses, choose the actual row j=0:0<=beta(nu_0)<=M. Therefore M>=0 is proved from the input rows; it is never an extra public assumption. For a fixed law set M=beta(nu), which is a real finite actual expectation; beta<=M is equality. No need to assume M>=1, or even to prove that stronger fact.

## 4. Ambient ceil, monitored floor and their limits

The sole new transparent definition is private rowLength(h)=Nat.ceil(h^2). Let N_h=rowLength(h) and m_h=Nat.floor(h^2). The heads rowLength_horizon and stepCount_le_rowLength follow exactly from

    h^2 <= (Nat.ceil(h^2):Real),
    Nat.floor(h^2) <= Nat.ceil(h^2).

They hold for every real h. Consequently the producer143 covering horizon at T=1 is satisfied by N_h, and every monitored prefix m_h is within the actual row. We never use n=m_h against its h^2<=n premise.

If h>0, the natural-floor inequalities with h^2>=0 give

    0 <= (m_h:Real) <= h^2 < (m_h:Real)+1.
    0 <= 1-(m_h:Real)/h^2 < 1/h^2.                 (4.1)

Division is legal because h^2>0. The first inequality follows from m_h<=h^2. For the strict upper bound multiply by h^2, reducing it to h^2-m_h<1, exactly the strict floor inequality. This proves stepCount_ratio_bounds even when m_h=0.

If every h_j>0 and h_j->+infinity, then1/h_j->0 by tendsto_inv_atTop_zero, so1/h_j^2->0 by squaring and rewriting inverse powers. Squeeze (4.1) to get1-m_j/h_j^2->0 and subtract from1 to get m_j/h_j^2->1. This proves stepCount_ratio_tendsto without assuming the floors are eventually constant or pretending their values depend continuously on h.

For every real M, h_j->+infinity implies eventually h_j>=1 and h_j>=pi*(1+M), by the defining atTop eventual bounds and their intersection. This is large_h_eventually; the statement needs no sign condition on M.

## 5. Actual free coefficient: positivity and scaled logarithm error

This proves row_free_log_error. Fix the varying rows and common M. By section3, M>=0 and each row's first and second moments are integrable. On the eventual set of section4 use the accepted actual-coefficient theorem with

    nu=nu_j, scale=h_j, M=M,
    hId/hSq from section3, hCube=h3(j),
    mean=hmean(j), second=hsecond(j), beta<=M=hM(j).

All its hypotheses are now discharged, including1<=h_j and pi*(1+M)<=h_j. Write rho_j=cosineCoefficient nu_j (pi/(2h_j)) and

    lambda=pi^2/8, C_M=pi^3*M/48+pi^4/8 >=0.

The exact accepted cosineCoefficient_large_h_bounds gives eventually

    3/4 <= rho_j < 1, hence rho_j>0.                 (5.1)

The exact accepted cosineCoefficient_log_error_mul at N=m_j gives

    |m_j*log(rho_j)+pi^2*m_j/(8*h_j^2)|
      <= C_M*m_j/h_j^3.                             (5.2)

Since0<=m_j<=h_j^2, C_M>=0 and h_j>0, we have

    C_M*m_j/h_j^3 <= C_M*h_j^2/h_j^3 = C_M/h_j.

The center pi^2*m_j/(8*h_j^2) equals lambda*(m_j/h_j^2) by field arithmetic at nonzero h_j. Thus (5.2) is exactly the eventual bound in the proposed row_free_log_error head. This retains actual free rho; it makes no claim that rho is an eigenvalue of the general killed kernel. No assumption of symmetry is used to discard a sine term.

## 6. Actual free rho power limit

This proves row_free_power_tendsto. The right side C_M/h_j in section5 tends to0. The absolute value on its left is nonnegative, so eventual squeeze gives

    m_j*log(rho_j)+lambda*(m_j/h_j^2) ->0.

Section4 gives lambda*(m_j/h_j^2)->lambda. Subtracting yields

    m_j*log(rho_j) -> -lambda.                       (6.1)

Continuity of real exp therefore gives exp(m_j*log(rho_j))->exp(-lambda). On the eventual set(5.1), rho_j>0 implies rho_j^m_j>0, so the actual Mathlib identities give

    exp(m_j*log(rho_j))
       = exp(log(rho_j^m_j)) = rho_j^m_j.            (6.2)

The first equality is Real.log_pow in reverse; the second is Real.exp_log at the strictly positive natural power. This is valid for m_j=0 as well. Eventually equality transfers the limit to the actual rho_j^m_j. Log at zero or at a negative coefficient is never used in the power-identification step. Eventual positivity is derived before (6.2), not inferred from its desired conclusion.

## 7. Exact finite integral bridge, including time zero

The heads cosine_test_measurable and cosine_test_bound hold for every real h: w |-> cos((pi/(2h))*w) is continuous even when h=0 under the total real division convention, and its absolute value is at most1 by Real.abs_cos_le_one. In applications below h>0.

For discrete_cosine_integral_eq_killed, fix n,l with l<=n, probability law nu, and h>0. Apply actual145 discrete_killed_test_integral with

    physical scale=h, radius b=1:NNReal,
    physical starting point z=0,
    F(w)=cos((pi/(2h))*w).

Its starting condition is |0|<=1*h, true because h>0. F is measurable and bounded by1 as just proved. Its physical killed threshold is (1:Real)*h=h, and the actual discrete scaled start is0/h=0. Thus its first conclusion is exactly the proposed Integrable F (killedIterKernel nu h l 0), not a totalized-integral substitute.

For every actual a:Path n, the terminal functions are pointwise equal:

    F(0+prefixSum(a,l))
      = cos((pi/(2h))*prefixSum(a,l))
      = cos((pi/2)*(0+prefixSum(a,l)/h)).

This is scalar arithmetic at h!=0. Multiplying the equality by the same Set.indicator of actual143's discreteClosedSurvival n l h 0 1 proves an everywhere equality with its literal discreteKilledCosine, not only equality in distribution. Actual145's integral equality therefore gives

    integral discreteKilledCosine(n,l,h,0,1,a) d(pi_n nu)
       = killedAction nu h l F 0.                   (7.1)

No monitored coordinate is discarded without a law argument:145 has already proved the exact first-l family marginal law in the n-coordinate product, including l=0. Its closed event includes k=0, while killedIterKernel kills only at positive times; the condition |0|<=h is precisely what bridges those conventions. At l=0 the kernel is dirac0, the event is the initial bound, and both expectations equal F(0)=1. No positive-l premise or density assumption is needed. At n=0, l=0 is permitted in this auxiliary head. Every integral in(7.1) is integrable by145/143.

## 8. Instantiate the actual canonical Brownian target

This proves canonical_killed_cosine_integral with no premises. Take exactly

    Omega = CanonicalBrownian.Sample,
    P = CanonicalBrownian.law,
    B = CanonicalBrownian.B,
    hB = CanonicalBrownian.isBrownianReal,

using the unconditional frozen146 probability instance. There is no arbitrary Brownian data argument and no existential desired process chosen by B4. Apply actual145 brownian_killed_cosine_identity at T=1:NNReal and u=0, whose interval hypothesis -1<=0<=1 holds. It gives

    integral brownianKilledCosine B 1 0 dP
       = exp(-(pi^2/8)*1)*cos(pi*0/2)
       = exp(-pi^2/8) = c.                          (8.1)

Integrability of this raw observable follows from actual143's integrable_brownianKilledCosine at the same hB; it is not an added assumption. Real.exp_pos gives c>0, hence c!=0. Neither source B0's supremum-over-starts conclusion nor author147's uniform-start module is used here.

## 9. Actual varying-row killed numerator

This proves row_killed_cosine_tendsto. Given its exact row assumptions, apply actual143 discrete_killed_cosine_tendsto_brownian with the canonical data of section8 and

    T=1:NNReal, nSeq(j)=rowLength(h_j)=ceil(h_j^2),
    hSeq=h_j, nuSeq=nu_j,
    bSeq(j)=1:NNReal, uSeq(j)=0, u=0.

T>0 holds; all row probabilities, third-integrability, mean, second and common-M bounds are precisely the hypotheses. Positive heights and their divergence are precisely its hpos and hinfty. The covering horizon1*h_j^2<=N_j is rowLength_horizon from section4. The constant radii tend to1 and the constant starts tend to0 by constant convergence;0 is in[-1,1]. Its actual floorHorizon 1 h_j is definitionally floor(1*h_j^2), rewritten by one_mul to m_j.

The producer conclusion therefore says that the integrals of the actual discreteKilledCosine N_j m_j h_j 0 1 converge to the integral in(8.1). For each j, section4 gives m_j<=N_j, so the actual exact bridge(7.1) identifies that row integral with

    @killedAction nu_j hprob(j) h_j m_j
       (w |-> cos((pi/(2h_j))*w)) 0.

The explicit probability instance is used in all proposed varying-row theorem heads so there is no missing instance hidden by notation. Every one of these equalities is exact at the actual n_j-coordinate product measure; n_j is not quietly replaced by m_j. Substitute these row equalities and(8.1) to obtain that the actual killed numerator tends to c. No public desired limit or B4 premise is supplied. In particular this is a fixed positive time, so it is not an estimate that divides a small long-time survival probability by an absolute-error remainder.

## 10. Varying-row normalized product

This proves varying_row_fixed_time_limits, the separately labelled stronger public form. Sections6 and9 give precisely its first two asserted limits, both to c=exp(-pi^2/8). Since c!=0, continuity of inversion at a nonzero real, in its exact Filter.Tendsto.inv₀ form, gives

    (rho_j^m_j)^(-1) -> c^(-1).

Multiplication with the killed numerator limit gives normalized product -> c^(-1)*c=1. No assumption that an arbitrary small rho_j^m_j is bounded away from zero was made: the nonzero positive fixed limiting constant establishes the needed reciprocal passage. In addition, section5 has already supplied eventual rho_j>0, so the expression is exactly the intended source negative power eventually. The public theorem simply returns the conjunction of these three results. A negative common M cannot be inhabited by these row hypotheses, as proved from row0 in section3, so no unhandled negative-M branch is present.

## 11. From all positive sequences to real atTop

This proves real_tendsto_atTop_of_positive_sequences for every real-valued f, with no continuity or measurability assumption on f.

Suppose every positive real sequence h_j->+infinity satisfies f(h_j)->a. If f did not tend to a at real atTop, the exact Metric.tendsto_atTop criterion would give an epsilon>0 such that, for every real threshold H, some h>=H has dist(f(h),a)>=epsilon. For each j choose such an h_j at threshold(j:Real)+1. Then h_j>0 and h_j>=j+1>=j. Since the real natural casts j tend to+infinity, monotone lower comparison gives h_j->+infinity. The assumed sequence limit makes dist(f(h_j),a)<epsilon eventually, contradicting its choice for every j. Thus f tends to a at real atTop.

This is ordinary classical countable choice, within the permitted foundational axiom policy. The argument does not assume a sequential criterion for a general filter without proof; it derives the needed criterion from the metric epsilon/threshold characterization. It also explains why negative or zero h values of our total expressions do not become public assumptions.

## 12. Fixed-law public results and original B1

For free_cosine_power_tendsto fix exactly nu,h3,hmean,hsecond. Let beta=integral|x|^3 dnu and take the constant row law nu_j=nu and M=beta. For every positive h_j->infinity, all hypotheses of row_free_power_tendsto hold: the row integrability and moment identities are the fixed inputs, the probability proof is the given instance, and beta<=M is equality. That theorem gives the required sequence limit of the exact real-scale f(h)=cosineCoefficient nu (pi/(2h))^floor(h^2). Apply section11 to conclude f->c at real atTop. This proves the exact proposed public head with no common-M or first/second-integrability input.

For killed_cosine_tendsto use the same constant rows and M=beta, now in row_killed_cosine_tendsto. Section11 turns every positive divergent sequence limit of the exact actual killed numerator into its real atTop limit c. This proves its exact public head and still has no Brownian premise.

For fixed_time_normalization combine those two public limits. Since c>0, apply inv₀ to free_cosine_power_tendsto and multiply by killed_cosine_tendsto. The limit is c^(-1)*c=1. This is the exact source B1 at original start0 and m=floor(h^2), with the actual free rho_h and the actual killed kernel. Both original first/second moment identities have been preserved, and the only integrability input is finite third absolute moment.

## 13. Exhaustive proposed declaration/value coverage

declarations.lean.txt lists exactly20 owned heads: one private definition rowLength, fifteen private theorem heads, and four public theorem heads. There is exactly one literal transparent value, rowLength(h)=ceil_N(h^2). No abbrev, structure, class, instance, additional top-level helper, alternative process, wrapper measure, law, kernel or test definition is proposed. All theorems display their complete binders and result, including the probability instances needed by row killedAction. Internal proof-local lets/haves introduce no extra top-level heads.

Every head has a proof above: lower moments and third nonnegativity in3; rowLength and prefix order plus ratio bounds/limit and large-h set in4; actual row log error in5; actual row free power in6; cosine measurability/bound and exact bridge in7; canonical target in8; row killed limit in9; the public three-limit row form in10; metric sequential-to-real helper in11; and all three fixed-law public limits in12. Literal rowLength is fixed in4. No interface or mathematical premise is left implicit for the lead to freeze.

## 14. Boundary, attribution and remaining gates

The proposed theorem covers arbitrary atoms, lattice cosets and asymmetric laws. Closed-strip/strict-exit conventions remain those of the actual kernel and producers. The auxiliary bridge covers m=0 exactly, includes time0, and uses physical start0 inside the strip. The actual time1 Brownian identity is instantiated with146; full T=0/endpoint B4 coverage stays in145 and is not reproved or weakened here. The positive-time ratio m/h^2 limit and eventual free-coefficient positivity are proved, not demanded. No all-starts supremum estimate or small-survival relative error is used.

This packet removes the mathematical fixed-time B1 assembly obligation once143/145/146 are qualified. It proves no long-time K/Kv theorem, general OQ4 root, global spectral/energy theorem, or unrelated root. The frozen local producers must still be qualified, the lead must first read and freeze this complete head/value packet, and only then may an implementation be produced. Its acceptance will require one fresh qualified independent complete source-to-statement/proof/actual type/value review and the designated-server exact-source kernel/transitive-all-owned-axiom receipt. Expected permissible axioms are propext, Classical.choice, Quot.sound; no such receipt is claimed here.
