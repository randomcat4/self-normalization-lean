# Complete mathematical proposal: the exact universal fixed-law window

Status: **PROVED AS A MATHEMATICAL PROPOSAL, BEFORE PARENT FREEZE**. This is a complete proof of the chosen source corollary, using the actual qualified old S4 and the already written source-bound sufficiency/CDF interfaces identified below. The newer interfaces have pending independent/formal gates; this document does not mark them qualified, implement a Lean proof, or certify an original root. All C12/OQ3/OQ4/OQ56 original root groups remain OPEN.

Author context187: gpt-6.1-sol, xhigh, fresh context. Ownership is solely this new draft directory. No other owner, implementation, source input, library, status, inbox, server, Git or cache was changed. The math-theorem skill is used; math-ultra is not used. The parent, not this author, freezes declarations and commissions the independent final reviewer.

## 1. Exact problem, conventions and inputs

The original sources are `C:/game/shao/current/oq4/sharp01.md`, `frozen01.md`, `c01/spectrum01.md` and `verdict01.md`, read in full. They ask, for a single deterministic antitone real sequence a tending to zero, whether the following statements are equivalent:

1. For every **fixed** iid real increment distribution with mean zero, positive finite second moment and finite absolute third moment,
   sup over a(n)<x<1 of |P(M_n <= x V_n)/F_B(x)-1| tends to zero.
2. a(n) n^(1/6) tends to positive infinity.

Here M_n is the maximum of the absolute sums over positive prefixes 1 through n, V_n is the square root of the actual sum of squares, and F_B is the actual time-one absolute-supremum CDF of the supplied standard Brownian motion B on its supplied probability space P. The original multiplicative event retains zero-energy atoms. Neither condition contains a supremum over increment laws. The distribution cannot depend on n or on a selected subsequence.

The proposed primary product-law property D18 spells out the universal quantifier over fixed Borel probability measures on the real line with third absolute moment finite, mean zero and second moment one. The final original-space theorem T25 quantifies over **all** iid probability spaces and AE measurable real coordinates in any fixed universe u, and displays the literal one-based weak event inside the real sSup. It has no variance-one restriction. The additional lifted Rademacher construction in Sections8–9 makes that universal quantifier nonvacuous in every u. The probability-space universe is a bookkeeping issue only; it does not restrict a mathematical law.

Definitions are exactly D01–D04, D18, D20 and D21 in `declarations.lean.txt`. No extra mathematical premises or top-level helpers are proposed. In particular, eventual a>0 is **not** assumed or used in necessity. The original monotonicity and zero-limit hypotheses are retained in the classification, although necessity itself proves the stronger implication for arbitrary a.

The actual finite-product quantity is, literally,

    p_n(x) = (pi_{i in Fin n} ν).real
      (RandomDenominatorFarTail.randomDenominatorEvent n (x sqrt(n))).
    randomDenominatorEvent n h =
      {w : closedStrip ((h/sqrt(n)) sqrt(energy(w)))}.
    e_n(x) = |p_n(x)/F_B(x)-1|.
    E_n(a) = sSup (e_n '' Ioo (a(n)) 1).

The closed strip monitors prefix0 through prefix n with weak walls. At n>0 the displayed random-denominator event is exactly closedStrip(x sqrt(energy)); at n=0 its literal convention is preserved. The proposed original-space transfer also includes n=0 exactly. Real division and sSup have their existing Lean totalized meanings; we prove finiteness before applying the ordinary supremum inequalities.

Consumed inputs, with qualification distinguished:

* **QUALIFIED OLD** S4_EVENTUAL, its full transparent S4Outputs/ProbabilityLegal values and its p/b/Q/w/delta/scale aliases. It returns both actual log-ratio residual convergence and eventual positivity of that same actual ratio. Its only analytic premises are eventual legal cells, h->infinity, n/h²->infinity and eventual bounded n/h³. No positive actual probability or log-limit is added as an input to this proposal.
* **QUALIFIED OLD** S5.actual_path_energy: for the fixed Rademacher finite product, every increment is +1 or -1 and energy=n almost everywhere; it includes Fin0. The actual two-atom law and its probability instance are qualified. Its private integral helper is not consumed.
* **MATHEMATICALLY AVAILABLE, FORMAL QUALIFICATION PENDING** BrownianPositiveCDF.probability_mono/probability_pos at the exact parent-frozen public heads. They refer to this same supplied actual F_B. Their mathematical positivity proof uses the qualified actual small-positive-radius Brownian positivity and monotonicity, with no assumption of the desired CDF.
* **MATHEMATICALLY AVAILABLE, FORMAL QUALIFICATION PENDING** OriginalWindowProduct.product_window_tendsto and OriginalIIDWindow.original_iid_sSup_tendsto, together with the actual source probability transfer. These are the fixed-law sufficiency theorem already written in the separate owner181/185 unit, not assumptions exposed in the new root signatures. Their final independent/server gates remain pending. Their exact declarations are frozen in `frozen-original-window-iid-formal-v1.lean.txt`.

The proof below completes necessity and the sharp corollary at the mathematical level, with the sufficiency input's independent/formal status explicitly pending. It does not treat an unqualified implementation as formally correct. API/provenance evidence is in `api-evidence.md`.

## 2. One actual fixed Rademacher law and its event

Use the existing law ν_R=(1/2)δ_1+(1/2)δ_{-1}, independent of n, c, j and a. Its half weight is the actual finite ENNReal 1/2. For any real function f, both Dirac summands are integrable and

    integral f dν_R = (f(1)+f(-1))/2.

This follows from the two Dirac integrals and additivity/scaling of integrals over finite measures, not from a private old lemma. Apply it to z, z² and |z|³ to obtain mean0, second1 and absolute third moment1; third integrability follows from finite support. This proves T07 and pays all admissibility assumptions for the same law.

On the finite product of this law, the qualified actual_path_energy says that almost everywhere every coordinate is ±1 and energy=n. For n>0 put s=sqrt(n)>0. The wall in productProbability is

    ((x s)/s) sqrt(energy) = x s

on this one full-measure set. Therefore for **every real x**, including x<=0, its event is AE exactly the old weak strip at height x s. Taking actual measures gives

    p_n(x) = RademacherS2Assembly.p n (x sqrt(n)).                (2.1)

All S3/S4 p aliases reduce to this S2 value, which is the finite product probability of that actual closed strip. This proves T09. The event equality is AE under the actual fixed product law; no deterministic replacement of energy is asserted for general laws.

Every p_n(x) lies in [0,1], by nonnegativity and the finite product's probability bound. This proves T08, with no appeal to an inaccessible private OriginalWindowProduct helper.

## 3. The genuine finite supremum, for any lower endpoint

Fix n>=1, s=sqrt(n)>0, d=1/s>0 and F=F_B. On the Rademacher full-measure set, the first prefix sum equals the first increment and has absolute value1. If x<d then x s<1. Equation(2.1)'s closed strip is impossible already at prefix1, so p_n(x)=0. Hence

    e_n(x)=|0/F(x)-1|=1,                                      (3.1)

using actual total real division. This includes negative x and x=0, even if F(x)=0. No assertion about negative-threshold Brownian probabilities is needed. This proves T10. The first-prefix identity is a direct finite sum calculation: the Fin n indices with i.val<1 form the singleton of index0.

If x>=d, monotonicity and positive-radius positivity give F(x)>=F(d)>0. Thus

    0 <= p_n(x)/F(x) <= 1/F(d),
    e_n(x) <= p_n(x)/F(x)+1 <= 1+1/F(d).                       (3.2)

Combining(3.1) and(3.2) proves the **global-in-x**, finite bound T11. There is no assumption on a(n), no uniform-in-n denominator bound and no asymptotic estimate in this step.

For any a(n)<1, the point (a(n)+1)/2 lies in the exact open interval. Its error witnesses nonemptiness of the window image; T11 supplies a finite upper bound for every element of that image. Consequently its real sSup is its actual least upper bound, is nonnegative (every error is nonnegative), is at most 1+1/F(d), and bounds e_n(x) for every a(n)<x<1. This proves every clause of T12. The proof uses isLUB_csSup/le_csSup only **after** nonemptiness and BddAbove have been paid.

This section removes the real-totalization hazard: when a(n) is zero or negative, an arbitrary law's image might require additional work, but this **particular** fixed Rademacher image is finite for every n>=1. Unchanged n=0 is irrelevant to any limit and is not silently patched.

## 4. Rounded integer heights: all scales proved

Let c>0 and let n_j be any natural sequence tending to infinity. Write

    r_j=n_j^(1/3), q_j=n_j^(1/6),
    m_j=Nat.ceil(c r_j), h_j=(m_j:real), x_j=h_j/sqrt(n_j).

For all n, c*n^(1/3)>=0. The natural ceiling inequalities therefore give

    0 <= h_j-c r_j < 1.                                      (4.1)

For sufficiently large j, n_j>=1, r_j>0 and q_j>0; both r_j and q_j tend to infinity. Real power arithmetic at a positive base gives r_j³=n_j and sqrt(n_j)=r_j q_j. These are genuine real exponents 1/3 and1/6. They imply all the identities in T05, in particular

    x_j q_j = h_j/r_j,
    n_j/h_j² = r_j/(h_j/r_j)²,
    n_j/h_j³ = 1/(h_j/r_j)³.                                 (4.2)

Here h_j>0 for positive n_j since h_j>=c r_j>0, so every displayed ordinary fraction in the tail is legal. Dividing(4.1) by r_j and squeezing between0 and1/r_j proves h_j/r_j->c. Also h_j>=c r_j gives h_j->infinity and hence eventually m_j>=1. The second identity in(4.2) gives n_j/h_j²->infinity: its denominator tends to c²>0, so is eventually at most, for example,2c²; its numerator tends to infinity. The third gives

    n_j/h_j³ -> 1/c³.                                       (4.3)

The first and sqrt identity give x_j=(h_j/r_j)/q_j->0 and x_j q_j->c. They also give x_j>0 and x_j sqrt(n_j)=h_j eventually.

As h_j is exactly the integer m_j, its weak cell is m_j<=h_j<m_j+1. The actual absorbing site is H_j=m_j+1, so the old transparent delta value H_j-h_j is exactly1. This is also the qualified delta_at_left identity. These prove every clause of T06. We discard only a finite tail in arguments; no false all-index positivity premise is introduced.

Equation(4.3) supplies S4's eventual bound: choose the fixed positive M=1/c³+1; eventually n_j/h_j³<=M. The four premises to S4_EVENTUAL are now fully derived: eventual cell, h_j->infinity, n_j/h_j²->infinity and this bound. No special perfect-cube subsequence is assumed.

## 5. S4 gives the actual quotient, not only its logarithm

Let Q_j denote the **old S4 actual value** p(n_j,h_j)/F_B(h_j/sqrt(n_j)). The consumed old transparent values make that identification exact. S4_EVENTUAL, with m_j and h_j above, returns

    log Q_j - w_j -> 0,
    w_j=(pi²/4)*(n_j/h_j³)*delta(m_j,h_j),                     (5.1)

and a common eventual ProbabilityLegal record containing positive p(n_j,h_j), positive F_B(h_j/sqrt(n_j)) and positive Q_j. These conclusions are obtained from S4 itself; they are not premises of this proposal's T13.

Since delta=1 and(4.3) holds, w_j->K_c=pi²/(4c³)>0. Adding its limit to the residual in(5.1) gives log Q_j->K_c. Continuity of exp gives exp(log Q_j)->exp(K_c); on S4's positive tail exp(log Q_j)=Q_j. Thus

    Q_j -> exp(K_c)>1.                                      (5.2)

By Section2 and x_j sqrt(n_j)=h_j, Q_j is eventually exactly productProbability(ν_R,n_j,x_j)/F_B(x_j). Therefore this **genuine full relative probability quotient** has limit exp(K_c). Continuity of subtraction and absolute value yields

    e_{n_j}(x_j) -> Delta_c=exp(K_c)-1>0.                     (5.3)

The positivity uses c>0 and pi>0, so K_c>0, followed by strict monotonicity of exp and exp(0)=1. This proves T13, including its criticalGap positivity clause. There is no normalized-log substitute, dropped negative spectral mode or unexplained exponentiation at a nonpositive totalized Q.

## 6. Every failure of the scale gives points in the original open window

Write b_n=a(n)n^(1/6) and suppose b_n fails to tend to positive infinity. Negating the atTop definition gives a real D for which arbitrarily large n satisfy b_n<D. Enlarge to C=max(D,0)>=0. Recursively select n_0>=1 with b_{n_0}<=C, and n_{j+1}>=n_j+1 with b_{n_{j+1}}<=C. This constructs a strictly increasing sequence of positive natural indices, hence n_j->infinity, with

    a(n_j) q_j <= C for every j.                             (6.1)

This proves T14. It uses no a-positivity, monotonicity or zero-limit assumption.

Set c=C+1>0 and take precisely the rounded x_j of Section4. Since x_j q_j->C+1, eventually x_j q_j>C+1/2>C. Together with(6.1) and q_j>0, this implies x_j>a(n_j). Since x_j->0, eventually x_j<1. Thus

    a(n_j) < x_j < 1                                        (6.2)

in the exact source window. This proves T15. The integer rounding is only in h_j; x_j is the actual real h_j/sqrt(n_j), and the law is unchanged. This works for every failure of divergence, not just failure along cubes or one prescribed critical subsequence.

## 7. Entire-window obstruction and product-law classification

Use c,n_j from Section6. Equation(5.3) gives e_{n_j}(x_j)->Delta_c>0, so eventually e_{n_j}(x_j)>=Delta_c/2. On the same tail, n_j>=1 and(6.2) imply a(n_j)<1. Section3 therefore supplies the actual finite IsLUB at each selected n_j and its ordinary pointwise lower bound. Consequently

    E_{n_j}(a) >= e_{n_j}(x_j) >= Delta_c/2 >0.                (7.1)

This proves every clause of T16, not just a pointwise/logarithmic witness. If the whole E_n(a) tended to zero, its composition with strictly increasing n_j would tend to zero. For sufficiently large j it would then be less than Delta_c/4, contradicting(7.1). Hence convergence for the fixed Rademacher law forces b_n->infinity. This proves T17 for arbitrary a.

Now retain the original Antitone a and a->0. If universalFixedLawWindow holds, apply its fixed-law quantifier to the actual ν_R and the moments of Section2, then T17 gives b_n->infinity. Conversely, if b_n->infinity, the source-bound OriginalWindowProduct.product_window_tendsto proves E_n(a)->0 separately for each fixed admissible standardized law. This is exactly D18, proving T19. The forward sufficiency's pending independent/formal status is not upgraded by this logical corollary. No common moment bound or uniformity over laws is asserted.

## 8. A concrete fixed infinite iid counterexample space, in every universe

Take μ_0=infinitePi_{i:natural} ν_R on the actual space real^natural, using the already qualified probability instance of the same ν_R. For any universe u let μ_u=μ_0.map(ULift.up) on ULift(real^natural), endowed with its standard lifted measurable space. This is an actual probability measure because up is measurable. Under down its image is exactly μ_0: composition down after up is identity and map_map/map_id apply. Let X_i(ω)=ω.down(i). Each X_i is measurable.

Infinite-product independence applied to the identity real coordinate maps gives independence of the whole base-coordinate family under μ_0. This transfers to X_i under μ_u directly: for every finite index set J and measurable real sets A_i, the preimage under up of the intersection of {X_i in A_i} is the corresponding base-coordinate intersection. By the definition of the mapped measure its μ_u mass is therefore its μ_0 mass, which is the product of ν_R(A_i). Its individual coordinate marginals have those same masses. This is the finite-event characterization of joint independence, so the X_i are jointly independent. Precomposing by the injective successor index gives iIndepFun of (X_(i+1)). Equivalently, every finite-coordinate joint map is unchanged by map_map and down(up(w))=w. The coordinate marginal formula and this same exact pushforward calculation give

    μ_u.map X_(i+1) = ν_R for every i.                        (8.1)

The measurable coordinates therefore have identical actual laws, including IdentDistrib(X_(i+1),X_1). The measurable X_1/id pair with measures μ_u/ν_R is identically distributed by(8.1). Transporting Section2's third integrability and exact integral equalities gives integrable |X_1|³, mean0 and second1>0. This proves every clause of T22. This is one fixed measure and one fixed sequence of coordinates; neither depends on a,c,j or n. No new probability instance declaration or hidden full definition value is needed.

No additional existence axiom for random variables is introduced. ULift ensures this actual test space lives in exactly Type u, even when the final universal quantifier is at a larger universe. The mathematical distribution remains ±1 with equal probabilities.

## 9. Original one-based weak events and the full original classification

Apply the pending exact source_probability_eq_product head to μ_u, X, the facts of Section8 and sigma=1>0. Its mapped standardized law is μ_u.map(X_1/1)=ν_R by(8.1), so for every n and x,

    μ_u.real{sourceMaximum(n,X)<=x sqrt(sourceEnergy(n,X))}
      = productProbability(ν_R,n,x).                         (9.1)

The original path definition uses X_(i.val+1), hence exactly X_1,...,X_n. The energy is the actual sum of squares. This equality includes Fin0 by the input's actual all-n head and preserves weak walls, actual zero-energy conventions, and every real x. At n=0 the source maximum and energy are0, its event is true, and the literal product event is closedStrip0, also true, so this edge case can also be checked directly. This proves T23; taking error-image equality and then sSup gives T24 **exactly**, not just eventually. Thus the original iid event's window error for this actual space equals the fixed Rademacher product E_n(a).

For T25, first assume the universally quantified original iid-window property in any u. Specialize it to μ_u and X from Section8; all its measurability, independence, common-law and moment premises are proved there. Equation(9.1) and T24 identify the resulting literal sSup sequence with the product Rademacher sequence. T17 forces b_n->infinity. Conversely, assume b_n->infinity. For each fixed ΩX,μ,X satisfying the displayed original assumptions, apply the pending source-bound original_iid_sSup_tendsto theorem. It derives sigma=sqrt(integral X_1²)>0, standardization and measurable versions internally; it does not require a variance-one, ordinary-measurability or atomlessness premise. This proves the displayed universal property separately for each fixed law and space.

Therefore the complete original fixed-iid-space statement and the standardized fixed-law product statement both have precisely the source criterion b_n->infinity, with the same original Antitone a and a->0. No supremum over laws, triangular array, silent threshold shift, lost weak-boundary atom, or new a>0 hypothesis occurs.

## 10. Exhaustiveness, hazards and remaining certification work

The formal proposal has exactly25 declarations:7 complete public definition values and18 theorem heads (7 private and11 public), with no new instance. All18 imports, the sole autoImplicit=false option, both universe parameters, the noncomputable section and namespace are listed. Every theorem proof obligation is covered in Sections2–9, with scalar identities and all branches in Sections3–6. No additional preflight theorem or desired limit/finiteness assumption is hidden in a root head.

Hazards explicitly resolved: arbitrary bad subsequence; integer ceil error; natural versus real exponents; actual absorbing site m+1; weak integer delta=1; negative spectral modes already included in qualified S4; actual positivity before exp(log Q); full ratio limit; finite real IsLUB; nonpositive lower endpoints; first coordinate at n>=1; Fin0; one-based iid coordinates; fixed law across n; actual second moment and zero-energy event; arbitrary measurable probability spaces and universes.

Remaining gates are precise, not missing mathematical premises: parent declaration freeze; implementation by an authorized owner; qualification of the named pending BrownianPositiveCDF/OriginalWindowProduct/OriginalIIDWindow inputs; exact-source designated-server kernel and whole-owned/transitive-axiom receipt; one fresh qualified complete independent source-to-statement/proof/type/full-value review. Only propext, Classical.choice and Quot.sound are allowed. No new server/proof-parser/Lean/test command was run here. Historical accepted old checks are reused by exact hash, never replayed or relabelled as new-consumer checks. Novelty and historical firstness are not claimed.
