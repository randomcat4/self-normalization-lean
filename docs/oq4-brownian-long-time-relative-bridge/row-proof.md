# Common-M varying-row actual long-time relative bridge

AUTHOR_STATUS: PROVED at the mathematical-proposal level from the exact qualified finite absorption theorem and the exact actual148 varying_row_fixed_time_limits contract. This is a separately labelled strengthening of fixed-law152. It is not implemented, parent-frozen, independently reviewed, or kernel/axiom-qualified. No Lean or remote command was run. The sealed fixed-law implementation is unchanged at SHA256 3e1198845c6d0a6a9b0ab1293582c4e84e59aa5308e225fad7cc93a4e0609d30.

Author152; prescribed gpt-6.1-sol/xhigh; math-theorem proof role. This proposal follows the parent's explicit next-dependency instruction and writes only row-proof.md, row-declarations.lean.txt and row metadata in the same owned directory. No new proof body is added to the frozen10-head source before a separate parent freeze.

## 1. Exact original scope and integration shape

The read-only original source C:/game/shao/current/oq4/b01/proof01.md has SHA256 7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38. Lines9–36 were read completely for this proposal, as were the complete section8/D8 lines266–314 in the prior unit. The source fixes a finite common M, permits a different centered unit-variance increment law in each row, requires iid increments only within a row, and imposes no coupling between rows. Its uniformity means that every choice of rows with the common third-moment bound and scale conditions has the asserted asymptotic conclusion. Rowwise finiteness without a common bound is explicitly excluded by the original source.

The fixed-law theorem in frozen152 does not cover that varying-row scope. This proposal proves the common-M row version of its D8 conclusion, still conditional on explicit unpaid actual S/AC primitives with common constants. It does not infer the final K probability asymptotic from D8 alone and does not close K, Kv, general OQ4, or the unpaid S/AC producers.

Proposed integration: after a new parent mathematical/head freeze, add exactly three theorem declarations inside the same Shao.OQ4.BrownianLongTimeRelativeBridge namespace and same source module, immediately before its existing closing namespace/section lines. Preserve all old10 heads and proof bodies and the old6 imports. There are no additional imports and zero new definitions, abbreviations or instances. The two new private helpers may reuse the existing same-file private lower_moments_integrable, third_moment_nonneg, bridge_constants_nonnegative, large_parameters_eventually, floor_le_horizon_eventually and absorption_coefficient_tendsto_zero. These six existing helpers are referenced, not redeclared or changed. The third new declaration is the separately labelled public varying_row_long_time_relative_bridge. Its final proof uses a proof-local scalar limit, with no omitted new top-level helper.

## 2. Exact hypotheses and target

For every natural j, let nu_j be a Borel real probability measure. The explicit hprob j instance is the instance used in the actual killed objects in every public output. Assume for every j:

    x -> |x|^3 is integrable under nu_j;
    integral x dnu_j = 0;
    integral x^2 dnu_j = 1.

Write beta_j = integral |x|^3 dnu_j. Assume one real M satisfies beta_j<=M for every j. We do not add M>=0 as a public premise; it will be derived from row0. This common-M condition is essential, not replaced by individually finite third moments.

Fix two common real constants Cq,Cs>=0. For every j retain literally:

    hAC j : iidIntervalConcentration nu_j beta_j Cq;
    hS j  : iidOneSidedSurvival nu_j beta_j Cs.

Thus for every row and all natural t>=1, actual t-coordinate product closed unit-interval probabilities are bounded by Cq*beta_j/sqrt(t), and both actual all-time nonnegative-wall survival probabilities are bounded by Cs*(d+beta_j)/sqrt(t), for every d>=0. These are actual primitive probabilities, not arbitrary desired block, normalization, D8, K, Brownian or limit conclusions. They remain unpaid. No root actual Spitzer/S producer is assumed complete or duplicated.

Let h_j>0 tend to +infinity. Let N_j be natural and assume

    (N_j:Real)/h_j^2 -> +infinity,
    d_j := (N_j:Real)/h_j^3 -> 0.

Let m_j=floor_nat(h_j^2). Using the actual definitions in KernelRecurrence, set for this proof only

    rho_j = principalRate nu_j h_j;
    Fhat(j,k) = @normalizedKernelCosine nu_j (hprob j) h_j k 0;
    Ghat(j,k) = @normalizedKernelMass nu_j (hprob j) h_j k 0.

The explicit instance argument in these formulas is mandatory in the formal heads: no global probability instance for a varying family is presumed. The killed kernel, closed state interval, strict-exit convention and signed cosine definition are unchanged.

Use fixed constants

    E = killedResidualConstant M Cq Cs
      = pi^3*M/48 + 2*pi*(12*Cq*Cs*M*(1+M))*(1+2*M);
    R = exp(pi^2);
    H = 2*(1+(2*Cs)*R)*R;
    Q = E*R*H.

All are proof-local abbreviations of existing literal expressions. The target is H>0 and

    eventually in j, for every natural k<=N_j: 0<=Ghat(j,k)<=H;                 (R1)

    for every epsilon>0, eventually in j, for every m_j<=k<=N_j:
      |Fhat(j,k)-1|<epsilon.                                                 (R2)

H is independent of j, the varying laws, h_j, N_j, epsilon, and every future terminal Brownian block time T. Its only nonuniversal input is the common Cs. Q may depend on the fixed common M,Cq,Cs, which is harmless because d_j->0.

## 3. Lower moments, common-M sign, and constants

For each row j, install only its given probability instance hprob j while proving row-local integrability. The real function1+|x|^3 is integrable because the probability measure integrates the constant1 and the absolute third power is assumed integrable. For r>=0, if r<=1 then both r and r^2 are<=1; if r>=1 then r<=r^2<=r^3. Hence for every real x,

    |x|<=1+|x|^3,          |x^2|=|x|^2<=1+|x|^3.

Identity and square are Borel measurable. Apply Integrable.mono' with the displayed dominator to obtain integrability of x and x^2 under each nu_j. This is exactly the existing lower_moments_integrable helper instantiated per row, with no uniform first/square-integrability premise needed.

Pointwise |x|^3>=0, so integral_nonneg gives beta_j>=0 for every j, independently of integrability conventions. Since the natural index contains0, beta_0>=0 and the supplied beta_0<=M imply M>=0. This derivation uses the actual row0 integral, not a new sign assumption or an arbitrary constant. With M,Cq,Cs>=0 the literal formula gives E>=0. R>0 follows from exp_pos. Since1+(2*Cs)*R>=1, H>0 and therefore Q>=0. There is no need for M>0, Cs>0 or a positive killed mass.

## 4. Eventual parameters and exact smallness

Since h_j->+infinity, eventually

    3<=h_j,             pi*(1+M)<=h_j.                                      (R3)

These thresholds use the same M for every row. Since N_j/h_j^2->+infinity, eventually N_j/h_j^2>=1. Positivity of h_j^2 gives h_j^2<=(N_j:Real). The actual natural floor satisfies (m_j:Real)<=h_j^2, so the order embedding of natural casts gives m_j<=N_j. In particular the target cosine range is eventually nonempty. No claim is made for early small-h, N=0 or m=0 rows.

For this fixed common M define the exact finite-theorem coefficient

    a_j = ((2*Cs)*R)*(E*R/h_j^3)*(N_j:Real)
          +(2*Cs*M)*R/h_j.

Associativity and the real division-as-inverse identity give exactly

    a_j = (((2*Cs)*R)*(E*R))*d_j
          +((2*Cs*M)*R)*(h_j)^(-1).                                        (R4)

The coefficient E is constant here. It is not the varying killedResidualConstant beta_j Cq Cs and is not bounded by silently replacing a varying factor in a limit. The supplied d_j tends0, and h_j->+infinity implies inverse h_j->0. Fixed scalar multiplication and addition give a_j->0. Hence eventually a_j<=1/2; for example take the metric threshold |a_j|<1/2. Intersect this eventual set with (R3) and m_j<=N_j. It is one eventual set satisfying all scalar/geometric inputs of actual finite absorption uniformly over the chosen rows.

The existing helper absorption_coefficient_tendsto_zero is already general in M,Cq,Cs and the two scale sequences, with no fixed-law parameter. It supplies precisely (R4)'s coefficient limit. The same existing large-parameter and horizon helpers supply the preceding eventual inequalities; their hypotheses do not change when the law varies.

## 5. Actual finite absorption per row with common M

Fix one row j in the eventual set above, install its probability instance hprob j, and call the qualified actual theorem killed_block_finite_absorption with

    nu=nu_j, M=the common M, h=h_j, Cq,Cs, N=N_j, z=0.

Every input is paid: h_j>=3 and pi*(1+M)<=h_j from (R3); the derived row-local first/square integrability; assumed row-local third integrability, mean0 and second1; derived M>=0; the supplied beta_j<=M; Cq,Cs>=0; the literal hAC j and hS j; m_j<=N_j; a_j<=1/2; and |0|<=h_j from h_j>0. No desired block or arbitrary finite recurrence is supplied as data.

The theorem yields exactly

    for every k<=N_j, 0<=Ghat(j,k)<=H,                                      (R5)

    for every m_j<=k<=N_j,
      |Fhat(j,k)-Fhat(j,m_j)|
        <=(E*R/h_j^3)*((k-m_j:Nat):Real)*H.                                 (R6)

The explicit output instances are hprob j: installing that row's local instance is definitionally identical to the corresponding explicit instance arguments in the frozen proposed head. This is a per-row instance application, not an assumption that all measures have a single shared instance.

For completeness, actual cosineCoefficient_large_h_bounds can be applied in the same row with common M and beta_j<=M. It gives3/4<=rho_j<1 under (R3), hence rho_j>0. The finite absorption theorem already obtains this internally. The inverse natural powers thus have their source normalization meaning on all rows where (R5)–(R6) are used; positivity is not inferred from totalized inversion.

Natural subtraction satisfies k-m_j<=k<=N_j. Casting to reals gives ((k-m_j:Nat):Real)<=(N_j:Real). Because E>=0,R>0,h_j>0,H>0, multiply this inequality without reversing its direction. The right side of (R6) is bounded by

    (E*R/h_j^3)*(N_j:Real)*H = Q*d_j.

Thus on one eventual set we have (R5) and, simultaneously for every admissible k,

    |Fhat(j,k)-Fhat(j,m_j)|<=Q*d_j.                                        (R7)

This is the new private varying_row_finite_absorption_eventually. No common bound on the actual beta_j beyond beta_j<=M was used implicitly: that exact inequality was passed to the actual finite theorem and E used the same M throughout. Since Q is fixed, Q*d_j->0.

## 6. Actual varying-row B1, not fixed-law composition

The fixed-law real-h B1 theorem cannot simply be composed with h_j when nu_j varies. Instead use the exact public producer

    Shao.OQ4.BrownianFixedTimeNormalization.varying_row_fixed_time_limits

from actual148 formal freeze SHA256 5121e85eaf86cd23acdf61ab2a4844a23786b94f59f6d762d0875776ea9fe7f0 and complete LOCAL source SHA256 7a02028309e0930971ce49de2c4883ea18369b81d2c86798bfa27cf0e8eb75d9. Its exact premises are nuSeq, hprob for every row, rowwise third integrability/mean0/second1, one common M and beta_j<=M, positive h_j and h_j->+infinity. These are precisely our inputs. It does not require S/AC or a supplied Brownian process.

Its third conjunct states

    (cosineCoefficient nu_j (pi/(2*h_j)) ^ m_j)^(-1)
      * @killedAction nu_j (hprob j) h_j m_j
          (w |-> cos((pi/(2*h_j))*w)) 0 -> 1.                                (R8)

Unfold only the existing normalizedKernelCosine, principalRate, kernelCosine and principalCosine. The function in (R8) is exactly j |-> Fhat(j,m_j), with the same instance hprob j. Therefore

    B_j := Fhat(j,m_j) -> 1.                                                (R9)

This proves the new private varying_row_fixed_time_normalization_along helper. It does not take B1, a desired limit, D8, a Brownian process, a Brownian identity, or K as input. Actual148 supplies the limit internally through its actual139/143/145/146 ancestry. That ancestry and actual148 qualification remain pending as recorded in the parent's current state; this mathematical proof does not fabricate receipts or replace an unqualified producer with an additional theorem premise.

## 7. Full quantified uniform convergence and source interpretation

For the new public theorem, first derive H>0 by section3 and retain the eventual all-k mass bound (R5). The scalar error limit Q*d_j->0 is a proof-local have obtained by hshort.const_mul Q; no additional theorem declaration is needed.

Fix epsilon>0. By (R9), eventually |B_j-1|<epsilon/2. By the scalar error limit, eventually |Q*d_j|<epsilon/2, hence Q*d_j<epsilon/2. Intersect those two eventual sets with the single eventual set on which (R5) and (R7) hold. This intersection is chosen before k. For every j in it and every m_j<=k<=N_j,

    |Fhat(j,k)-1|
      = |(Fhat(j,k)-B_j)+(B_j-1)|
      <= |Fhat(j,k)-B_j|+|B_j-1|
      <= Q*d_j+|B_j-1|
      < epsilon/2+epsilon/2
      = epsilon.

This proves exactly (R2), including its forall-epsilon/eventually-j/forall-k quantifier order. Together with (R5) and H>0 it proves the complete proposed public varying_row_long_time_relative_bridge. No monotonicity of hSeq or NSeq, convergence of nuSeq, coupling between rows, or uniform convergence-in-law premise is needed.

The theorem quantifies over every nuSeq and every admissible pair of sequences with the displayed common-M and common-S/AC constants. It therefore covers the varying-row sequential interpretation of the D8 bridge under those explicit primitive inputs. In the original source application, the as-yet-unpaid uniform S/AC producers must supply common constants from the source's moment class. This proposal does not pretend that freely varying unbounded Cq_j/Cs_j would suffice. It also makes no claim that individually finite unbounded beta_j suffices.

## 8. Declaration completeness, boundaries, and remaining work

The exact three added heads, existing six-import environment, unchanged module namespace, and zero new literal values are in row-declarations.lean.txt. The public head has no extra M>=0 assumption. Every actual normalized varying-law output is written with @ and its exact hprob j instance. No desired block, D8, K or Brownian premise is present. These additions are a proposal only: their future implementation requires the parent's separate complete proof/head freeze.

Early N_j=0, m_j=0 or small h_j rows are permitted because the conclusions invoking absorption are eventual. The all-k mass range includes k=0. The cosine range is eventually nonempty by m_j<=N_j. Atoms, asymmetry and lattice cosets remain allowed; the actual killed interval is closed and cosine positivity is only used on its actual support. There is no division by killedMass or an assumed positive survival event. H contains no future terminal T, no epsilon and no row-specific coefficient.

This mathematically fills the row-uniformity gap of the fixed-law D8 consumer when the exact producer contracts are available. Actual S/AC producers, actual148 and upstream qualification, this addition's later exact-source server kernel/all-owned-transitive-axiom receipt and fresh complete independent source-to-statement/proof/actual-type review remain mandatory. The final K probability asymptotic, Kv scaling, general OQ4 and other original roots remain OPEN. No novelty claim is made.

NEXT_DEPENDENCY: parent reads the complete row proof and all three proposed added heads/no-value/no-import delta, freezes the new mathematical scope and exact additions, then may authorize their implementation. The fixed10-head source remains sealed unchanged; this author stops and releases its directory after delivering the completed row proposal and static checkpoint.
