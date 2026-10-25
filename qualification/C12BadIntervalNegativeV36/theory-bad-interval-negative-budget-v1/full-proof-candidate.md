# Actual bad-displacement interval negative budget

Status: complete mathematical candidate for the exact frozen subject; no
independent verdict, Lean check or axiom qualification is claimed here.
The statement was frozen in `frozen-theory-subject.json` before this proof.
The source is supplement.tex 4323–4341, 4867–4903, 4978–4999,
5046–5065 and 5564–5588. This pays only its bad interval negative part.

Throughout, rho is a probability law, EX=0, EX²=1 and |X|≤B almost surely.
Write beta=E|X|³. Boundedness gives all moments. Cauchy or monotonicity of
Lp norms gives 1≤beta and 1≤B. We use independent coordinates with this
law. All constants below are numerical and selected before rho, B, n, x,
the Brownian probability space, or the cap. The Brownian motion is denoted
Bm to distinguish it from the support bound B.

## 1. Raw concentration for a clipped and floored actual-wall statistic

Let k≥1, q≥0 and x≥0. Let c_B(t)=min(B,max(-B,t)). Define, on all of R^k,

    F_q(t) = sum_i t_i - x sqrt(max(k/2, q+sum_i c_B(t_i)^2)).

Its linear coordinates are not clipped. This is a continuous, globally
defined statistic; its quadratic part is clipped and its square root is
floored. Suppose x B sqrt(2/k)≤1/2. If one coordinate increases from s to t,
s≤t, its square contribution changes in absolute value by at most 2B(t-s).
Taking max with k/2 cannot increase that change. Both square roots are at
least sqrt(k/2), so rationalization bounds the change of the square root
by B sqrt(2/k)(t-s). Consequently F_q gains at least (t-s)/2. This argument
also covers a coordinate crossing either clipping endpoint or the floor;
no differentiability at these endpoints is needed.

Normalize Y_i=X_i/sqrt(k) and put H(y)=2 F_q(sqrt(k)y)/sqrt(k).
Increasing any coordinate of H by h≥0 increases H by at least h. Thus
H(update(v,i,t))-t is monotone in t, exactly the unrestricted hypothesis
of `iid_strong_monotonicity_concentration`. The law eta of Y satisfies
k E Y²=1 and E Y=0. Its genuine budget satisfies

    R_k(0) = k E[Y² min(|Y|,1)] ≤ k E|Y|³ = beta/sqrt(k).

The preimage under F_q of any closed interval of length v≥0 corresponds
to an interval for H of length 2v/sqrt(k). The accepted concentration
theorem therefore gives, uniformly in its location and in q,

    P(F_q(X) in [a,a+v]) ≤ (4v+80beta)/sqrt(k).                 (1)

Here and below probabilities are genuine probabilities of Borel sets.
Atoms at either endpoint remain included.

Let Q_k=sum_i X_i² and S_k=sum_i X_i. On the full-measure support set and
on Q_k≥k/2, F_q(X)=S_k-x sqrt(q+Q_k). Independence gives

    Var(Q_k)=k Var(X²) ≤ k EX⁴ ≤ k B beta.

Chebyshev yields P(Q_k<k/2)≤4B beta/k. If B≤sqrt(k), adding this exceptional
event to (1) proves the unfloored actual statistic bound

    P(S_k-x sqrt(q+Q_k) in [a,a+v])
       ≤ 84 (v+beta)/sqrt(k).                                (2)

No condition x≤1 has been used: (2) instead uses the explicit coordinate
slope condition xB sqrt(2/k)≤1/2 and B≤sqrt(k).

## 2. The large-x true-wall strip after a complete suffix is fixed

Assume n≥1, x≥16 and B≤sqrt(n)/(100x). Since 1≤B, n≥10000x².
Let n/2≤r≤n and set k=floor(r/2), ell=r-k. In particular r≥2 and
k,ell≥r/3≥n/6. Thus

    xB sqrt(2/k) ≤ sqrt(12)/100 < 1/2,
    B/sqrt(k) ≤ sqrt(6)/(100x) < 1.

The hypotheses of (2) hold for the first block of length k. Fix q≥0 and
v≥0. Initially use the upper sign and set w=x sqrt(q+Q_r). Consider

    E = {max_{0≤j≤r} S_j≤w, 0≤w-S_r≤v}.

Write the last ell prefix coordinates as a second block. On E, each of
their reversed partial sums is S_r-S_{r-j}≥-v: indeed S_r≥w-v and
S_{r-j}≤w. Hence E implies the second-block event

    R = {every reversed second-block partial sum is at least -v}.

Condition on that entire second block. Its sum s and square sum q_2 are
then fixed. The terminal gap condition implies

    S_k-x sqrt((q+q_2)+Q_k) in [-s-v,-s].

Apply (2), uniformly in this q+q_2 and interval location. Since R depends
only on the second block, Fubini bounds P(E) by

    84(v+beta)/sqrt(k) * P(R).

Reversal preserves its product law. Apply the accepted
`original_closed_survival_uniform` to the sign-reversed second block,
normalized by sqrt(ell). Its budget is at most beta/sqrt(ell), as above.
For its universal constant C_OS, P(R)≤C_OS(v+beta)/sqrt(ell). Since
sqrt(k ell)≥r/3,

    P(E) ≤ C_strip (v+beta)²/r,  C_strip=252 C_OS.              (3)

Replace the entire law by that of -X for the lower sign. Mean, variance,
B and beta are unchanged, so the same constant works. An interval-live
prefix is a subset of either signed survival event. Formula (3) is uniform
in every deterministic q≥0. In particular, after conditioning on an
independent complete actual suffix, its full square sum may be substituted
for q. The wall continues to contain the random first-block energy.
There is no assertion that this wall is an iid stopping boundary.

## 3. Actual interval negative overshoots have a cubic crossing envelope

Let Q=bridgeLaw Bm PB for an actual standard Brownian motion. At a live
interval state write w>0, |y|<w, |z|<w, T>0, d=z-y and
D=1+|d|/sqrt(T). Let b be the actual next label. If b²>T/2, the source
separated term is zero by its literal small-energy guard. If neither wall
is crossed, its projected increment is b and the term is again zero.

At an upper crossing put u=w-y. Then 0<u≤b, u²≤b²≤T/2, and y+u=w.
The accepted actual image Taylor theorem
`BridgeIntervalImageResolved.sourceRemainder_small_bound`, applied at u,
and `intervalIncrementProfile_bounds` give

    |R_Q(w,y,T,z,u)| ≤ 2 C_profile u³ T^(-3/2) D³.

The actual interval completion is nonnegative. Apply the accepted
`source_upper_projection_negative_budget` with
K=2 C_profile T^(-3/2)D³, which is nonnegative. It bounds the negative
part of the actual upper projected overshoot by K u b²≤K|b|³.
At a lower crossing use u=w+y and the accepted lower projection theorem,
with increment -b and drift -d; it gives precisely the same bound.

The actualDerivativeFamily interval branch is the guarded intervalDerivative
of the actual completion. On the live state it is its genuine spatial
derivative. The transparent identification of local/source separated terms
with these upper/lower overshoots is the established one in
SourceActualIntervalProfileBudget, with all live and small-energy guards
retained. It uses the completion/derivative identity, not an assumed
derivative oracle. Consequently, for a numerical C_0>0,

    N_r ≤ C_0 |b|³ T^(-3/2) D³                              (4)

on an active small-energy crossing, and N_r=0 on all other source branches.
The right side can be taken zero unless the prefix is interval-live and
at least one of the two actual wall gaps belongs to (0,|b|]. Terminal
interiority remains necessary for a nonzero source term; we only drop it
when bounding a nonnegative quantity above. Equality at the crossing has
zero excess and causes no exception.

## 4. Remove only the cap dependence, before using the iid law

Put h0=4beta²>0 and suppose nu(a,sigma)≤energyCutoff(a,h0,sigma).
A nonzero term at rank r requires r<nu(a,sigma), hence r<n and T≥h0 by
the exact energy-cutoff theorem. The source term with cap nu agrees there
with the term with constant cap n. Else it is zero. Its negative part is
therefore dominated pointwise by the constant-cap-n negative part times
1_{T≥h0}. Multiplication by the nonnegative weak bad-displacement indicator
preserves this domination.

This dominating function depends only on the reordered full path. Under
rho^n times an independent uniform permutation that reordered path has
the original product law. We can thus bound its expectation at deterministic
original iid ranks. This step never asserts that the arbitrary cap is an
iid stopping time, or even a reveal stopping rank. Only its stated
measurability and its pointwise comparison to energyCutoff are needed.

For fixed n, each actual source separated term is measurable and bounded
in absolute value by 16(1+n), by actual kernel bounds with C=4 and
`source_parts_uniform_bound`. The negative parts, the finite bad-masked
sum and all their products with finite-valued permutation coordinates are
genuinely integrable under the probability reveal law. Measurability of the
cap in each permutation suffices because the permutation space is finite.
All expectation comparisons and Fubini operations below are therefore
ordinary finite integrals. The cubic dominating functions used below also
are integrable: |b|≤B, |d|≤nB, and T≥h0>0 bound every displayed factor.

## 5. Early ranks: keep the crossing label in the marked suffix

For the canonical iid ordering let t=n-r. Its true suffix is
(X_{r+1},...,X_n), so its first coordinate b=X_{r+1} is included in

    T=sum_{j=r+1}^n X_j², d=sum_{j=r+1}^n X_j.

In particular the bad event is exactly |d|≥3x sqrt(T)/2 for this suffix;
it is not the event after deleting b. For 2r<n, t≥ceil(n/2). Drop the
nonnegative prefix activity and crossing indicators from (4). Its expected
bad-masked contribution is bounded by C_0 times

    E[ |X_1|³ T_t^(-3/2) (1+|d_t|/sqrt(T_t))³;
         T_t≥h0, |d_t|≥3x sqrt(T_t)/2 ].

This is exactly the existing marked function with q=3,p=3. Apply the
first summed grid in `iid_marked_and_unmarked_rare_real_suffix_budgets`.
Under delta(1+x)³≤exp(-3x²), its fixed K=2^64 and its other stated
bounded-law/mean/variance hypotheses hold. The early ranks form a subset
of its Icc(ceil(n/2),n). Their total is at most

    C_early delta A_x,
    A_x=sqrt(Psi(3x/2))+exp(-x²).                              (5)

There is no maximum over random ranks or extra n factor.

## 6. Late ranks: the actual strip changes the inverse power

Let 2r≥n, r<n, and fix the entire actual suffix of length t=n-r,
including its first label b. Now T,d,D and the bad event are constants
under the conditional prefix law, while w=x sqrt(Q_r+T) still contains
the true random prefix energy. The source crossing support from Section 3
is contained in the union of the upper and lower strips in (3), each of
width |b|, with q=T. The actual live prefix gives the required survival.

If T<h0 or b²>T/2, the relevant source contribution is zero. Otherwise
(4) and the union bound give the conditional expectation at most

    2 C_strip C_0 |b|³ T^(-3/2) D³ * (|b|+beta)²/r
       * 1_{T≥h0, |d|≥3x sqrt(T)/2, b²≤T/2}.

On this retained set beta²≤T/4 and b²≤T/2. Thus

    (|b|+beta)² ≤ 2b²+2beta² ≤ 3T/2,
    (|b|+beta)²/r ≤ 3T/n.                                   (6)

The conditional expectation is at most

    (6 C_strip C_0/n) |b|³ T^(-1/2) D³
       * 1_{T≥h0, |d|≥3x sqrt(T)/2}.

The complete iid suffix has exactly the marked q=1,p=3 law of the second
summed rare grid. Late ranks correspond to a subset of
t=1,...,floor(n/2). Taking expectations and summing therefore gives

    total late contribution ≤ C_late delta Psi(x).            (7)

This is the required gain: conditioning did not delete the cubic mark,
and (6) reduced the inverse power from T^(-3/2) to T^(-1/2)/n.
Replacing the actual wall by a fixed wall, or ignoring the strip, would
not justify this second-grid application.

## 7. Compare the early Gaussian factor and conclude

For x≥16, the elementary Gaussian integral bounds give

    Psi(x) ≥ exp(-3/2)/(sqrt(2pi) x) * exp(-x²/2),
    Psi(3x/2) ≤ exp(-9x²/8).

For the lower bound integrate the normal density on [x,x+1/x] and use
(x+1/x)²≤x²+3. For the upper bound use
integral_u^infinity exp(-s²/2) ds ≤ exp(-u²/2)/u at u=3x/2≥1.
Since exp(x²/16)≥x²/16≥x for x≥16,

    A_x/Psi(x)
       ≤ sqrt(2pi) exp(3/2) x (exp(-x²/16)+exp(-x²/2))
       ≤ 2 sqrt(2pi) exp(3/2).                               (8)

This supplies a numerical constant without assuming an unexported
Gaussian comparison from inside the rare producer. Combining (5), (7)
and (8) proves the frozen full bad interval negative budget

    0 ≤ E_mu sum_{r=0}^{n-1} 1_Bad max(-I_r,0)
       ≤ C_negative delta Psi(x).

All constants are universal; for example C_negative can be chosen as
1+C_early*2sqrt(2pi)exp(3/2)+C_late after the three old producer constants
are chosen. No constant depends on the cap, n, law, support B, x,
Brownian representation or terminal endpoint. Weak Bad includes the
strict Bad of unit192. The source interval term, including all original
guards, is the one actually bounded.

This completes the mathematical candidate. It does not pay the second-wall
one-wall bills, every retained term, the terminal corridor, or the original
finite-second-law truncation/assembly. C2/C12 therefore remain open.
