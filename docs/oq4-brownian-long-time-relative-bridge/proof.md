# Actual long-time relative bridge: complete mathematical proposal

AUTHOR_STATUS: PROVED at the mathematical-proposal level from the exact existing finite absorption theorem and the exact actual148 B1 contract. This is not a parent declaration freeze, independent review, Lean implementation, or kernel/axiom qualification. The actual148 source is complete LOCAL and remains unqualified in this intake. Its qualification and this unit's own complete independent review/server receipts are acceptance dependencies, not additional public mathematical hypotheses.

Author152; prescribed model gpt-6.1-sol, reasoning xhigh; math-theorem proof role. Sole writable directory: drafts/oq4/brownian-long-time-relative-bridge-author-v1/. No other owner, source, production, Git, cache or server state was changed. No Lean or heavy command was run.

## 1. Source, exact objects, and immutable scope

Original read-only source: C:/game/shao/current/oq4/b01/proof01.md, SHA256 7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38, section8 lines266–314, especially D8. Parent intake SHA256 edd68abc30ec3d8fd7ac05a91d281e14779470415d6660febdda962173833933 was read in full. This unit proves the fixed-law asymptotic consequence of the actual finite D8 bounds, explicitly conditional on the unpaid actual primitive S and AC inputs. It does not prove their producers or the original K/Kv/general OQ4 roots.

Fix a probability measure nu on the real Borel space, with

* x -> |x|^3 integrable;
* integral x dnu = 0 and integral x^2 dnu = 1.

Write beta = integral |x|^3 dnu. Fix real Cq,Cs >= 0 and retain the following exact hypotheses from qualified KilledBlockBounds, without replacing them by arbitrary block bounds or limit premises:

AC: for every natural t >= 1 and real x, the actual t-coordinate product probability that prefixSum a t belongs to the closed interval [x,x+1] is at most Cq*beta/sqrt(t).

S: for every natural t >= 1 and real d >= 0, both actual product probabilities of closedUpper d and lowerBlockSurvival d are at most Cs*(d+beta)/sqrt(t). These are literally iidIntervalConcentration nu beta Cq and iidOneSidedSurvival nu beta Cs. In particular they apply to every required half-block or whole-block time. No assertion here derives S or AC from the moments, Brownian data, conditional Spitzer consumers, or root's still-open actual Spitzer producer.

Use the actual definitions in KernelRecurrence:

    rho(h) = principalRate nu h = integral cos((pi/(2*h))*x) dnu;
    f_h(w) = principalCosine h w = cos((pi/(2*h))*w);
    F(h,k) = kernelCosine nu h k 0 = killedAction nu h k f_h 0;
    G(h,k) = killedMass nu h k 0;
    Fhat(h,k) = (rho(h)^k)^(-1) * F(h,k);
    Ghat(h,k) = (rho(h)^k)^(-1) * G(h,k).

The killed action is the existing actual iterated closed-interval kernel, without row renormalization. The cosine remains its signed global definition; positivity is used only on the actual support [-h,h]. No division by killedMass or assumption of its strict positivity occurs.

Let h_j > 0 be a real sequence tending to +infinity, and let N_j be a natural sequence with

    N_j / h_j^2 -> +infinity,       N_j / h_j^3 -> 0.

Natural-to-real casts are intended in both ratios. Set m_j = floor_nat(h_j^2). No monotonicity of either sequence is assumed.

## 2. Exact constants and target

Use the specific choice M = beta. It is finite because of third-moment integrability, and it is nonnegative as proved below. No enlarged, chosen, row-dependent or terminal-time-dependent M is needed. Define in this proof only:

    L = 12*Cq*Cs*beta*(1+beta);
    E = killedResidualConstant beta Cq Cs
      = pi^3*beta/48 + 2*pi*L*(1+2*beta);
    R = exp(pi^2);
    H = 2*(1+(2*Cs)*R)*R;
    Q = E*R*H.

These are proof-local abbreviations, not new top-level definitions or instances. The declaration packet proposes zero new transparent values. In particular H depends only on Cs and the universal number pi. It does not depend on h_j, N_j, j, epsilon, or any future terminal Brownian block time T. We will prove H > 0 and

    eventually in j: for every 0 <= k <= N_j, 0 <= Ghat(h_j,k) <= H;             (A)

    for every epsilon > 0, eventually in j: for every m_j <= k <= N_j,
        |Fhat(h_j,k)-1| < epsilon.                                            (B)

Here k is natural, so 0 <= k is built into its domain. The explicit H exhibits the requested positive constant C. The common eventual row threshold in (B) may depend on epsilon; it never depends on k. This is a quantified uniform statement, with no sSup or empty-set convention.

## 3. All lower-moment and sign obligations

For r >= 0, both r <= 1+r^3 and r^2 <= 1+r^3. Indeed, if r <= 1, then r <= 1 and r^2 <= 1, while r^3 >= 0. If r >= 1, multiplying 1 <= r by r and then r^2 shows r <= r^2 <= r^3. Apply this with r=|x|. Then

    |x| <= 1+|x|^3,              |x^2| = |x|^2 <= 1+|x|^3.

The dominating function is integrable: its constant part is integrable under a probability measure and its other part is the assumed integrable third absolute power. Identity and square are Borel measurable, hence almost-everywhere strongly measurable for nu. Integrable.mono' therefore gives integrability of x and x^2. This pays precisely the hId and hSq inputs of killed_block_finite_absorption and cosineCoefficient_large_h_bounds; they are not added to the public premise list.

Pointwise |x|^3 >= 0, so integral_nonneg gives beta >= 0. With Cq,Cs >= 0, L >= 0 and E >= 0 by their displayed literal formulas. Also R=exp(pi^2)>0. Therefore 1+(2*Cs)*R >= 1>0 and H>0. Consequently Q>=0. The case Cs=0 causes no algebraic division problem: H=2R>0. If S with that constant is inconsistent with the fixed moments, the conditional theorem remains valid; no proof step needs Cs>0 or beta>0.

## 4. Eventual geometric and natural-number admissibility

Since h_j -> +infinity, eventually both

    3 <= h_j,             pi*(1+beta) <= h_j.                                (C)

The first gives 1 <= h_j and positive powers of h_j. No assertion is made about finitely many earlier rows.

Since N_j/h_j^2 -> +infinity, eventually N_j/h_j^2 >= 1. Positivity of h_j^2 gives h_j^2 <= (N_j:Real). On the other hand Nat.floor_le applied to h_j^2>=0 gives (m_j:Real)<=h_j^2. Thus (m_j:Real)<=(N_j:Real), and the order-embedding of natural casts gives m_j<=N_j. This pays the exact finite-absorption hmN input and also proves that the target interval in (B) is eventually nonempty. It uses neither ceil(h^2) nor an unproved integer approximation equality.

For completeness, the actual principal rate is eventually positive. Apply the qualified cosineCoefficient_large_h_bounds with M=beta, the derived lower integrabilities, the three fixed moment hypotheses, beta>=0, beta<=beta, and (C). It yields

    3/4 <= rho(h_j) < 1,

so rho(h_j)>0. The actual finite absorption theorem also derives exactly this fact internally. The displayed inverse natural powers therefore have their source meaning on every row where the bounds are applied; we do not infer positivity just from totalized real inversion.

## 5. The exact smallness coefficient tends to zero

The finite theorem requires the following literal coefficient (with M=beta):

    a_j = ((2*Cs)*R)*(E*R/h_j^3)*(N_j:Real)
          + (2*Cs*beta)*R/h_j.                                               (D)

Let d_j=(N_j:Real)/h_j^3. By associativity and distributivity of real multiplication and division, including the natural cast already displayed,

    a_j = ((2*Cs)*R)*(E*R)*d_j + ((2*Cs*beta)*R)*(h_j)^(-1).                  (E)

This is an exact equality, not an asymptotic replacement of E, R, or the delayed exponents. The hypothesis gives d_j->0. Since h_j->+infinity, tendsto_inv_atTop_zero gives (h_j)^(-1)->0. The coefficients in (E) are fixed finite reals. Product and sum limit laws give a_j->0. Since 0<1/2, eventually a_j<=1/2; for example |a_j|<1/2 implies a_j<1/2. Intersect this eventual set with (C) and m_j<=N_j. The result is one eventual set on which every input of the actual finite absorption theorem holds.

No terminal block parameter T appears in (D) or (E). In particular this step has not used a Brownian approximation over time N_j/h_j^2, which diverges.

## 6. Apply the actual finite theorem and pay the uniform finite error

Fix a row j in the eventual set from section5. Invoke the qualified theorem killed_block_finite_absorption with

    nu; M=beta; h=h_j; Cq,Cs; N=N_j; z=0.

Its inputs are: 3<=h_j from (C); both lower integrabilities from section3; the assumed third integrability, mean0 and second1; beta>=0 and beta<=beta; Cq,Cs>=0; the literal actual hAC and hS; the second inequality in (C); m_j<=N_j from section4; a_j<=1/2 from section5; and |0|<=h_j from h_j>0. Every input is thus paid, and no arbitrary R3/R4 block bound is supplied as data.

Its conclusion, using exactly R and H above, is

    for all k<=N_j: 0<=Ghat(h_j,k)<=H,                                      (F)

    for all m_j<=k<=N_j:
      |Fhat(h_j,k)-Fhat(h_j,m_j)|
        <= (E*R/h_j^3)*((k-m_j:Nat):Real)*H.                                (G)

The subtraction in (G) is natural subtraction, exactly as in the theorem. For these k, Nat.sub_le k m_j and k<=N_j give

    ((k-m_j:Nat):Real) <= (N_j:Real).

Since E>=0,R>0,h_j>0,H>0, multiplying preserves this inequality. The right side in (G) is therefore at most

    (E*R/h_j^3)*(N_j:Real)*H = Q*d_j.                                      (H)

The equality follows from the literal Q=E*R*H and d_j=(N_j:Real)/h_j^3. Consequently we have, on one eventual row set, both (F) and the simultaneous finite error bound

    for all m_j<=k<=N_j:
      |Fhat(h_j,k)-Fhat(h_j,m_j)| <= Q*d_j.                                 (I)

Moreover Q*d_j->0 by the fixed-constant product limit law and the hypothesis d_j->0. This is the required O(N/h^3) error with its exact coefficient paid. Nonnegativity of Q*d_j holds for all rows by h_j>0 and N_j>=0, although the limit argument itself needs no such sign assumption.

## 7. Use actual148 B1 without a supplied Brownian premise

Use the exact public theorem

    Shao.OQ4.BrownianFixedTimeNormalization.fixed_time_normalization

from frozen contract SHA256 5121e85eaf86cd23acdf61ab2a4844a23786b94f59f6d762d0875776ea9fe7f0, actual complete LOCAL source SHA256 7a02028309e0930971ce49de2c4883ea18369b81d2c86798bfa27cf0e8eb75d9. Its premises are exactly that nu is a probability measure, |x|^3 is integrable, the mean is0 and second moment1. Its conclusion is the real-scale limit

    h |-> (cosineCoefficient nu (pi/(2*h)) ^ floor_nat(h^2))^(-1)
       * killedAction nu h floor_nat(h^2)
           (w |-> cos((pi/(2*h))*w)) 0  -> 1 as h->+infinity.

Unfolding only the actual definitions of principalRate, principalCosine, kernelCosine and normalizedKernelCosine identifies its function exactly with h |-> Fhat(h,floor_nat(h^2)). Compose with h_j->+infinity to obtain

    B_j := Fhat(h_j,m_j) -> 1.                                              (J)

There is no assumption here that B_j converges: (J) is obtained by calling that exact producer. There is no new public Brownian-process, Brownian-identity, desired-normalization, desired-long-time-limit, arbitrary desired block, or K premise.

Actual148's recorded ancestry remains explicit: actual139 is BrownianSurvivalBoundary, directly imported by actual143; actual143 supplies the literal killed-cosine row limit; actual145 supplies the finite discrete-to-actual-kernel equality and B4; actual146 supplies actual canonical Brownian law/process and IsBrownianReal internally. Actual148 combines that actual chain into the pure B1 conclusion above. Parent intake reports canonical146 qualified (source prefix3c223b5b, PR205, sole object prefix220e2302); actual148 itself is not yet qualified. We do not reprove, rerun or certify those ancestors here, and we do not convert any unqualified result into an extra theorem hypothesis. Acceptance of the planned import waits for the corresponding actual source qualifications.

## 8. Epsilon-uniform conclusion

Fix any real epsilon>0. By (J), eventually |B_j-1|<epsilon/2. Since Q*d_j->0, eventually |Q*d_j|<epsilon/2 and hence Q*d_j<epsilon/2. Intersect these two eventual sets with the eventual finite-absorption set yielding (F) and (I). For every resulting row j and every natural k with m_j<=k<=N_j, the triangle inequality and (I) give

    |Fhat(h_j,k)-1|
      = |(Fhat(h_j,k)-B_j)+(B_j-1)|
      <= |Fhat(h_j,k)-B_j|+|B_j-1|
      <= Q*d_j+|B_j-1|
      < epsilon/2+epsilon/2
      = epsilon.

The row set was selected before k, so this proves exactly the uniform quantifier order in (B). Equation (F) proves (A) on an eventual set independent of epsilon, and section3 proves H>0. Together these are the proposed public long_time_relative_bridge theorem. It has precisely the fixed law, moments, explicit actual S/AC, and three scale hypotheses from the intake.

## 9. Boundary, dependency, and acceptance audit

* N_j=0, m_j=0 or inadmissibly small h_j on early rows are permitted. Every assertion needing finite absorption is eventual, and section4 proves m_j<=N_j on that eventual set. The upper mass range includes k=0 and all natural k<=N_j.
* No monotonicity, strict increase, coupling between different j, uniform varying-row third-moment bound, or extra stochastic-process input is used. This proposal contains no stronger varying-law theorem.
* The all-time S and AC producers remain unpaid primitive-probability assumptions. Their occurrence is explicit in the public head and in the finite theorem call. The final source D8 without these conditions remains OPEN until those producers and the whole accepted ancestry close.
* Lower moments are derived, actual beta is used without changing the measure, the coefficient is the actual free expectation, and every inverse power is controlled by actual eventual rho>0. No division by a survival mass is used.
* H has no T parameter. This is necessary for the later terminal-block double limit but does not itself prove any terminal-block, K, Kv or general OQ4 theorem.
* Original proof attribution is retained: the delayed normalized recursion is the source section8 argument, applied through the qualified actual finite absorption theorem. No novelty claim is made.
* All10 proposed declaration heads, all6 exact imports, and the absence of any new def/abbrev/instance are in declarations.lean.txt. No theorem proof body or implementation file is present. A fresh independent complete reviewer must review this proof and all actual later Lean types/values; this author does not certify its own proof.

NEXT_DEPENDENCY: parent full mathematical/head/value/import inspection and substantive freeze, plus actual148's qualification. Implementation and any server kernel/all-owned-transitive-axiom gate must be separately authorized by the parent after that freeze. At this exact author boundary all requested mathematical deductions are complete; this author releases its directory and stops.
