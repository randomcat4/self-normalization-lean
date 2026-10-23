# Actual Brownian killed cosine identity: complete mathematical proof proposal

Author context145, 2026-10-23; prescribed model gpt-6.1-sol, effort xhigh. This is the mathematical proof/declaration proposal phase. No Lean proof implementation, Lean invocation, Git operation, compiled-object production, or server mathematical check has been performed by this context. The parent has not yet frozen these proposed heads/values. Independent review and exact-source kernel/all-owned-axiom receipts are still required. Producer143 is an exact dependency target, not an accepted compiled artifact.

**Result of this proof attempt: PROVED as a mathematical derivation from the exact upstream results listed below; formal and independent qualification pending.** No additional assumption is proposed for the public result. Original general OQ4, B0 and B1 roots remain OPEN.

## 1. Frozen external target and scope

Let Ω be any type with a measurable space, P any probability measure on Ω, and B : NNReal → Ω → real satisfy the actual unchanged `ProbabilityTheory.IsBrownianReal B P`. For every T : NNReal and every u in [-1,1], prove

    ∫ ω, PolygonalKilledFunctionalLimit.brownianKilledCosine B T u ω ∂P
      = exp (-(π²/8) T) cos (πu/2).

The integrand is exactly producer143's transparent value

    (BrownianSurvivalBoundary.closedSurvival B T u).indicator
      (fun ω => cos ((π/2) * (u + B T ω))),

where the raw event is `{ω | ∀ t : NNReal, t ≤ T → |u + B t ω| ≤ 1}`. The event includes t=0 and t=T. There is no completed-measure, standard-Borel, filtration, stopped-process, Itô, weak-convergence, tightness, boundary-null, integrability or desired-identity hypothesis in the public theorem. Integrability is obtained from producer143's actual `integrable_brownianKilledCosine`, including at T=0; it is never inferred merely from a totalized integral.

Source: `C:/game/shao/current/oq4/b01/proof01.md:233–264`, especially B4 at 259–264. The source proves B4 by Itô's formula for a bounded stopped martingale. The proof here is an alternative derivation of the same B4 from the genuine finite Rademacher eigenidentity and the actual general-row killed-functional limit. It does **not** formalize or claim to formalize the source's Itô argument. No novelty claim is made or needed.

## 2. Exact dependencies and their roles

1. Producer143 `PolygonalKilledFunctionalLimit.discrete_killed_cosine_tendsto_brownian`, with its exact actual Brownian and row hypotheses. Mathematical freeze SHA256 `1abd3230f95fbd6a2d75e7f57c07de57f54c5af07a89caeef42f4077e805954d`; formal head/value freeze `be40d0f71abed6a2c2da2a407a21e22e1f11bbf11231d32ba0e01d089c448060`; actual source `1a024c4bcfc22d42d5ff73ed7e1554abbac36ea352201fa673125f5006d3f98c`, 52106 bytes/970 LF lines. These three hashes were read and matched locally. The theorem's N-row length must satisfy T h² ≤ N, and its monitored terminal time is L=floor(T h²), not N. Its starts and radii may vary; it requires only their stated limits, not that every start lie in its strip. It explicitly covers limiting u=±1 when T>0.
2. Actual `Shao.OQ4.killedIterKernel_integral_iid_path` from `KilledPathLaw.lean`. This declaration is directly in namespace `Shao.OQ4`, **not** a `KilledPathLaw` subnamespace. It gives the killed-action integral on any probability space carrying measurable independent increments with the actual common law, and also supplies both integrability assertions. Its event `shiftedClosedSurvival` monitors 1≤k≤L only.
3. `RademacherIteration.killedAction_principal_power`, equivalently `killedIterKernel_integral_principal_power`, for m≥1, physical strip threshold h in [m,m+1), integer initial r in [-m,m], and every natural L, including 0. We use the threshold exactly m. The frequency is `angle m = π/(2(m+1))`.
4. `RademacherScalarBounds.SCA2`, `rho_eq_cosine_rho`, `H_pos`, `C_rho_pos`, and `RademacherCosine.rho_pos`. Here H=m+1, λ=π²/8 and Cρ=π⁴/48. SCA2 is the actual fourth-order logarithm bound.
5. Pinned Mathlib product-coordinate independence/law APIs, finite sums, integer/natural floor and natural ceil, elementary limits, continuity of exp/cos, and `IsPreBrownianReal.eval_zero_ae_eq_zero`. Exact usable primary declarations are recorded in `api-evidence.md`.

All are ordinary mathematical dependencies of the proposed theorem; unqualified upstream artifacts must be qualified before this module's final acceptance. We neither assume the output identity as an auxiliary lemma nor add any public convergence premise.

## 3. Explicit deterministic sequences

For m≥1 define

    H = H(m) = m+1,
    b_m = m/(m+1) : NNReal,
    p_m(u) = floor_Z(Hu),
    r_m(u) = max(-m, min(m, p_m(u))) : Z,
    v_m(u) = r_m(u)/H,
    N_m(T) = ceil_N(T H²),
    L_m(T) = floor_N(T H²).

Use rows m=j+1, j : Nat. The proposed literal Lean values are given separately; H and λ are consumed from the accepted scalar module rather than redefined.

The clamp gives -m≤r_m≤m for every real u. For u∈[-1,1], it also gives

    |r_m/H-u| ≤ 1/H.                                      (3.1)

Here is a complete floor/clamp verification. Put x=Hu and p=floor_Z x, so -H≤x≤H and p≤x<p+1.

* If p<-m, integrality gives p+1≤-m, hence x<-m. The clamp is r=-m. Since x≥-m-1, 0<r-x≤1.
* If -m≤p≤m, the clamp is r=p, and 0≤x-r<1.
* If m<p, integrality gives m+1≤p≤x≤H=m+1. Consequently x=p=H, r=m and x-r=1.

Thus |r-x|≤1 in every case. Division by positive H gives (3.1). It follows that v_{j+1}(u)→u, including u=±1. Also H(j+1)=j+2→∞ and b_{j+1}=1-1/H(j+1)→1. Convergence of b in NNReal follows from its subspace topology, since its real coercion has this limit. In particular, each actual scaled start lies in its own closed strip: |v_m|≤b_m; this is derived, not imposed on producer143.

Natural ceil gives T H²≤N_m. Nonnegativity of T H² and natural floor give 0≤L_m≤T H²≤N_m. We **never set N_m=L_m**: the covering hypothesis generally fails for the floor. This distinction also handles rows with L_m=0.

## 4. Full first-L joint law under the N-coordinate row

Fix any n,l : Nat with l≤n and any real probability law ν. Let μ_n=Measure.pi(fun _ : Fin n => ν). Define the measurable coordinate family on the actual n-coordinate space by

    X_i(a) = a(castLE(l≤n,i)),  i : Fin l.

Each X_i is the actual corresponding coordinate evaluation, hence measurable. All n coordinate evaluations are independent by `iIndepFun_pi` applied to identity functions. Precomposition with the injection `Fin.castLE` preserves independence, giving the full independence of (X_i)_{i<l}; no pairwise-to-joint inference is used. Each coordinate pushforward is exactly ν by `measurePreserving_eval`. Together with the identity pushforward ν→ν this gives the exact required `IdentDistrib (X_i) id μ_n ν`.

For every a : Path n and k≤l,

    prefixSum(samplePath X a,k) = prefixSum(a,k).            (4.1)

Indeed the first sum is indexed by `{i : Fin l | i.val<k}` and the second by `{q : Fin n | q.val<k}`. The map i↦castLE i preserves the value and the inequality. It is injective. Conversely q.val<k≤l yields the unique i : Fin l with value q.val; its cast is q. This is a bijection of the exact finite sum index sets and preserves every summand. This proves (4.1), including k=0, k=l and the empty path l=0. No stochastic support condition is needed for (4.1).

Thus the existing iid-path theorem applies directly to μ_n and this l-increment family. Equivalently, its `samplePath` map has exact l-coordinate product law by `iid_samplePath_map_eq_pi`. Either formulation is a genuine finite marginal argument; unused coordinates have not been dropped without proof.

## 5. Generic time-zero-inclusive event and killed-action bridge

The parent requested an exact reusable bridge for the next B0/B1 consumers before declaration freeze. Here is the full generic argument, using the same proved prefix law rather than duplicating it. Let ν be any real probability law, n≥l, h>0, b : NNReal, z : real with |z|≤b*h, and F : real→real any measurable bounded function. For each a : Path n and k≤l,

    |z/h+prefixSum(a,k)/h|≤b
      ↔ |z+prefixSum(a,k)|≤b*h.

This follows by combining the fractions and multiplying the absolute-value inequality by positive h. Equation (4.1) then identifies every positive monitored prefix with that of `samplePath X a`. At k=0, the missing condition is exactly the supplied |z|≤b*h. Therefore, everywhere,

    a ∈ discreteClosedSurvival n l h (z/h) b
      ↔ samplePath X a ∈ shiftedClosedSurvival (b*h) z.

The terminal value is also everywhere exactly F(z+prefixSum(a,l)) = F(shiftedEndpoint z (samplePath X a)) by (4.1). Apply the actual iid-path theorem with this ν, μ_n, l, threshold b*h, z, X and F. Its measurable/independence/common-law hypotheses are §4, and its F hypotheses are exactly those stated here. It supplies the integrability of F under the actual killed kernel and of the cut F under μ_n. Everywhere equality of the integrands transfers the latter integrability to the actual inclusive discrete-event indicator. The integral conclusion is

    ∫ a : Path n, (discreteClosedSurvival n l h (z/h) b).indicator
        (fun a => F(z+prefixSum(a,l))) a ∂μ_n
      = killedAction ν (b*h) l F z.                       (5.0)

The public proposal `discrete_killed_test_integral` returns both integrability assertions and (5.0). It holds for l=0, n=0 when permitted, b=0 and |z|=b*h. There is no moment, symmetry, non-atomicity or positive-time assumption. Its only initial-position hypothesis is exactly what equates the genuine positive-time kernel convention to the genuine inclusive event. This public helper does not weaken or replace B4.

## 6. Cosine specialization of the event and terminal observable

Fix m≥1, an integer r with -m≤r≤m, n≥l, H=m+1 and v=r/H. Write X for §4's prefix family. For every actual n-coordinate path a,

    a ∈ discreteClosedSurvival n l H v b_m
      ↔ samplePath X a ∈ shiftedClosedSurvival m r.         (5.1)

For each k≤l, arithmetic and H>0 give

    |v+prefixSum(a,k)/H|≤m/H
      ↔ |r+prefixSum(a,k)|≤m.

Use (4.1) for positive times. The missing condition at k=0 is precisely |r|≤m, which follows from the two integer bounds on r; `prefixSum_zero` is exact. Conversely the inclusive event immediately implies all 1≤k≤l conditions. If l=0 the positive-time event is univ and the inclusive event holds exactly because of this initial bound. This verifies that no time-zero kill has been silently lost.

For the terminal value there is a pointwise, everywhere identity

    cos((π/2)(r/H+prefixSum(a,l)/H))
      = cos(angle(m) * shiftedEndpoint r (samplePath X a)), (5.2)

because (4.1) identifies the l-prefix and `shiftedEndpoint` is r plus that prefix, while `angle m=π/(2H)`. Combining (5.1) and (5.2), the actual producer143 `discreteKilledCosine` is pointwise the iid theorem's explicit if-survival-then-principal-cosine-else-zero integrand. The physical strip parameter in that theorem is **m**, which satisfies m≤m<m+1. It is not H and it is not a scaled frequency π/(2m).

All events in this finite argument are measurable by the actual producer and killed-path measurability results. The test f(w)=cos(angle(m)w) is measurable and |f|≤1. Consequently the iid-path theorem supplies the integrability of f for the actual killed kernel and of the cut test for μ_n. The producer also supplies the integrability of the actual discrete integrand. Every integral below therefore has its ordinary integrable meaning.

## 7. Exact finite-row expectation

Take ν=RademacherCosine.law, the literal measure

    (1/2 : ENNReal) • dirac(1) + (1/2 : ENNReal) • dirac(-1).

Apply the public generic bridge (5.0) with ν=law, scale H, radius b_m, physical z=r and F(w)=cos(angle(m)w). Its physical threshold b_m*H is exactly m, and |r|≤m discharges the time-zero hypothesis. The cosine identification from §6 gives

    ∫ a : Path n, discreteKilledCosine n l H (r/H) b_m a ∂μ_n
      = killedAction law m l f r
      = rho(m)^l cos(angle(m)r).                           (6.1)

The second equality is exactly `RademacherIteration.killedAction_principal_power` with h=m and the frozen integer bounds. Thus (6.1) is proved for every n≥l, every l including 0, and every permitted r; n is not identified with l. The finite identity alone is not B4.

The same literal two-atom law satisfies the precise moment conditions needed later. Each real function is integrable for either Dirac measure; finite scalar multiplication and addition preserve integrability. In particular |x|³ is integrable, and the exact integral formula is

    ∫ f dlaw = (1/2)f(1)+(1/2)f(-1).

Apply it separately to x, x² and |x|³ to get mean 0, second moment 1 and third absolute moment 1. Probability is the existing `law_isProbabilityMeasure` instance. No not-found `RademacherMoments` module is assumed: the proposed private moment lemma proves these directly using the already established literal law.

## 8. Complete logarithmic power limit

Let λ=π²/8>0 and C=C_rho=π⁴/48>0. For m≥1 the actual rho(m)>0. Rewrite SCA2 using `rho_eq_cosine_rho` to get

    |log(rho(m))+λ/H²|≤C/H⁴.                              (7.1)

Put L=L_m(T). The natural floor inequalities imply

    0≤T-L/H²<1/H²,

so in particular L/H²→T along m=j+1. Set e=log(rho)+λ/H². The exact rearrangement and triangle inequality give

    |L log(rho)+λT|
      = |L e+λ(T-L/H²)|
      ≤ L|e|+λ(T-L/H²)
      ≤ L C/H⁴+λ/H²
      ≤ (TC+λ)/H².                                       (7.2)

The last inequality uses L≤T H², C≥0 and H>0. This is valid also at T=0, where L=0. The bound tends to 0 because H(j+1)→∞. Therefore

    L_{j+1}(T) log(rho(j+1)) → -λT.

For each row positivity gives

    rho(m)^L = exp(log(rho(m)^L)) = exp(L log(rho(m))),

using the actual `Real.log_pow` and `Real.exp_log`. Continuity of exp proves rho(j+1)^L→exp(-λT). There is no use of a logarithm at zero or a power/log identity requiring an unchecked sign.

Furthermore angle(m)r_m=(π/2)v_m→(π/2)u by (3.1). Continuity of cos and multiplication therefore give

    rho(j+1)^L cos(angle(j+1)r_{j+1})
      → exp(-λT) cos(πu/2).                               (7.3)

This treats endpoint starts by the same actual sequence; it does not extrapolate an interior identity by an unproved continuity of a survival expectation.

## 9. Consume the actual Brownian producer, T>0

Fix the arbitrary supplied Ω,P,B,hB,T,u with T>0 and u∈[-1,1]. In producer143 set

    nSeq j = N_{j+1}(T),   hSeq j = H(j+1),
    νSeq j = RademacherCosine.law,
    bSeq j = b_{j+1},      uSeq j = v_{j+1}(u),   M=1.

All its hypotheses have now been discharged: probability and the third-moment integrability/mean/second/common third bound are §7; positive scales and their divergence are §3; the exact covering horizon is §3's ceil inequality; radii converge in NNReal and starts converge in real by §3; the limiting endpoint-inclusive strip condition is the original hu. No stopped identity, weak limit, boundary-null fact, Itô theorem or desired B4 is an added argument. Internally producer143 has already proved the actual law and continuity-set facts; accepting it remains an upstream qualification requirement.

Its conclusion is exactly that the integrals on the left side of (6.1), now with n=N_m and l=L_m, converge to

    I = ∫ ω, brownianKilledCosine B T u ω ∂P.

The integrals equal the scalars of (7.3) for every row by (6.1), using L_m≤N_m, the clamp bounds, and m=j+1≥1. They therefore also converge to exp(-λT)cos(πu/2). Uniqueness of limits in real yields I=exp(-λT)cos(πu/2). This is the whole B4 conclusion for positive T, under the original arbitrary Brownian law.

At u=1 the explicit sequence is r_m=m, v_m=m/H; at u=-1 it is r_m=-m, v_m=-m/H. In both cases the cosine factor tends to cos(±π/2)=0 and the producer includes these limiting starts. Thus I=0 at both endpoints for T>0. This is consistent with the actual endpoint survival-null theorems of BrownianSurvivalBoundary, but their conclusion need not be supplied separately to this consumer.

## 10. Zero horizon and final theorem

Pinned Mathlib gives `hB.toIsPreBrownianReal.eval_zero_ae_eq_zero`, hence B 0 ω=0 for P-almost every ω. On that same full-measure set, any t : NNReal with t≤0 is t=0, so

    |u+B t ω| = |u|≤1.

Thus ω belongs to the actual raw closedSurvival B 0 u, and its actual killed cosine is cos((π/2)u)=cos(πu/2). This proves an almost-everywhere equality with a constant function, without any path-continuity or positive-time boundary-null argument. The integral equals the constant because P is a probability measure. Since exp(-λ*0)=1, B4 holds at T=0 as well. At u=±1 this value is 0; there is no assertion that zero-time survival itself has probability 0 (indeed it is 1 here).

Every T : NNReal is either zero or positive. Combine this calculation with §9 and expand the existing λ definition to obtain the exact proposed public theorem, including all original quantifiers and both boundary starts. No new axioms, `sorry`, `admit`, `unsafe`, `native_decide` or partial definitions are proposed. The expected transitive axiom whitelist is propext/Classical.choice/Quot.sound; only a later actual server audit can certify it.

## 11. Remaining gates, not mathematical premises

The parent must freeze the exact 22 heads/values in `declarations.lean.txt` before implementation. Producer143 and its Brownian139/weak-limit dependencies must obtain their own independent qualification and exact-source receipts before this consumer can be accepted. This proof and its eventual source require a fresh complete independent source-to-statement/proof review and server kernel/transitive-axiom evidence. None of those administrative gates changes the public mathematical statement. This context has not crossed the implementation or Lean-execution gate.
