# Actual late omitted halfline retained remainder

STATUS: COMPLETE_MATHEMATICAL_CANDIDATE_PENDING_INDEPENDENT_REVIEW.
This proves the exact mathematical subject frozen in frozen-theory-subject.json
(SHA256 f586d4d922a95bb2f02286198ad0f6979dbe05ab2d34294f65c117283bad79ae).
It is not an independent verdict, a Lean declaration, a kernel pass, an axiom
receipt or original C2/C12 completion. No assumption has been changed.

The source is supplement.tex 4931–4976 and 4978–5045. The particular claim
here is its late-rank actual omitted HALFLINE RETAINED bill. The numerical
late omitted suffix producer is already qualified in v96/PR378. The all-Q
large-x strip used below is an independently accepted mathematical result
from unit193; its current Lean implementation is unqualified. These two
kinds of evidence are kept separate throughout.

## 1. Fixed objects, constants and actual source

Fix K=2^64. Let rho be a real probability law with EX=0, EX²=1,
|X|<=B0 almost surely, B0>0. Let n>0, x>=16,
B0<=sqrt(n)/(100x), beta=E|X|³, delta=beta/sqrt(n), and assume
u=delta(1+x)^3<=exp(-3x²). In this paragraph u is a scalar; below a suffix
path is denoted Uvec to avoid confusing the two. All numerical constants
are selected before rho, B0, n, x and the Brownian realization.

Boundedness gives the second and third absolute moments. The Lp inequality
gives beta>=1. Thus h0=4beta²>0. Set

    H=K beta²(1+x)^6, m=ceil_nat(H),
    nu(a,sigma)=energyCutoff(a,h0,sigma),
    tau(a,sigma)=min(energyCutoff(a,H,sigma), n-m).

Here n-m is natural subtraction. We do not assume m<=n. Since K>=4 and
1+x>=1, H>=h0>0. Let P=rho^n and mu=revealLaw(P), the actual product law
of the labeled sample and an independent uniform permutation.

Let Bm be any actual standard real Brownian motion on a probability space
PB and Q=bridgeLaw(Bm,PB). Fix J=upper or lower. Set F_J to the literal
`eventCompletionKernel J Q` and G_J to `halflineDerivative J`. At rank r
(r is a natural number represented by an element of Fin n) let

    R_r(a,sigma)=sourceRetainedRemainder J F_J G_J
                   a x (nu(a)) r sigma,
    E_r(a,sigma)={floor(n/2)<r, tau(a,sigma)<=r<nu(a,sigma)},
    Bill_J(a,sigma)=sum_{r=0}^{n-1} 1_E_r |R_r(a,sigma)|.

This is exactly the frozen source bill, including its original outer
activity, endpoint, projection and local step guards. In particular we
have not replaced the actual completion by a supplied kernel oracle.

The qualified public Brownian heads `bridge_upper_formula` and
`bridge_lower_formula` give, on their stated positive-time interior domains,

    upperCompletion Q w y T z = 1-exp(-2(w-y)(w-z)/T),
    lowerCompletion Q w y T z = 1-exp(-2(w+y)(w+z)/T).

They imply `HalflineReflectionIdentities Q` directly. Their hypotheses are
exactly the actual Brownian premise already fixed above. The qualified
`actual_halfline_kernel_data` consequently supplies measurability of G_J,
`KernelBounds J F_J G_J 4`, and the actual interior spatial derivative.
Measurability of F_J is part of the qualified event-completion data.
There is no new reflection, derivative or bound premise in our claim.

## 2. Exact omission selection and genuine integrability

For r<n put T=remainingEnergy(a,r,sigma) and t=n-r. By
`energy_cutoff_data`, including its strict first-below convention,

    r<nu(a,sigma) iff h0<=T,
    energyCutoff(a,H,sigma)<=r iff T<H.

Also min(k,n-m)<=r iff k<=r or n-m<=r. For r<=n, natural arithmetic gives
n-m<=r iff n-r<=m, even when m>n. Therefore the EXACT selection is

    E_r iff floor(n/2)<r and h0<=T and (T<H or t<=m).          (1)

Equality T=h0 is selected; equality T=H is absent from the first disjunct;
equality t=m is selected by the second. This is a single union indicator,
not a replacement by a sum of indicators. Later ranks satisfy r>n/2 in
real arithmetic, and hence r>0. No r=floor(n/2) boundary is inserted.

The qualified `actual_energy_cutoff_measurable` gives sectionwise
measurability of both cutoffs. Their finite minimum and the finite-space
permutation coordinate are measurable. The source measurability theorem
`source_parts_measurable_integrable` applies with C=4 and x>0. More
explicitly, `source_parts_uniform_bound` gives on EVERY sample, regardless
of its support or energy,

    |R_r| <= 1+24(1+n).

Consequently Bill_J is measurable, nonnegative and bounded by
n(1+24(1+n)); it is genuinely integrable under the probability measure mu.
This conclusion precedes every integral comparison below.

We will also use only measurable, genuinely integrable comparison
carriers. For a complete suffix Uvec of length t>0, write

    T=energy(Uvec), d=sum(Uvec), b=firstValue(Uvec),
    D=1+|d|/sqrt(T) when T>0.

Cauchy gives |d|<=sqrt(t)*sqrt(T), and b²<=T. Thus, when T>0,
D<=1+sqrt(t) and |b|³/sqrt(T)<=T. The selected future weight

    F_t(Uvec)=1_{h0<=T, (T<H or t<=m)} |b|³ D^5/sqrt(T),     (2)

with zero on T=0, is measurable and bounded above by
(1+sqrt(t))^5 T. Since E T=t EX²=t, this is L1 under rho^t. This also
justifies the future-weight Fubini and finite-sum operations, independently
of the final numerical budget. The qualified Gaussian-weight bound gives
0<=rankGaussianWeight<= (1+sqrt(t))³ for either singleton wall sign;
its selected full-path carriers therefore are measurable and L1 as well.
No nonintegrable real integral is assigned the value zero and used here.

## 3. Actual physical domination and whole-path transport

Let s=1 for J=upper and s=-1 for J=lower. Qualified
`actual_halfline_retained_rank_domination` holds for ALL x>0: its head has
no x<=1 premise. Use its threshold parameter h0 and cap nu=energyCutoff h0.
The cap comparison is equality. With C0=8000100 it gives pointwise

    |R_r(a,sigma)| <= C0 G_r(reorder(a,sigma)),               (3)
    G_r(p)=rankGaussianWeight h0 x {s} false p r.

Its proof retains the original actual source guards before replacing them
by the nonnegative Gaussian upper bound. We only multiply (3) by the
original E_r indicator; no endpoint restriction is inferred from an
upper-bound carrier.

Let p=reorder(a,sigma). Permutation invariance of the full sum and energy
shows that T=energy(p)-prefixSquares(p,r), and the remaining sum is the
corresponding full-minus-prefix sum of p. The cutoff identity (1) is
therefore a deterministic function of this same FULL reordered path.
It is not a choice depending on an artificial iid stopping rank.
For each fixed sigma, the qualified `iid_product_reorder_map` sends P to
P. Averaging over its actual independent uniform law gives

    E_mu[1_E_r G_r(reorder(a,sigma))]
      = E_{p~rho^n}[1_{floor(n/2)<r, h0<=T, T<H or n-r<=m} G_r(p)]. (4)

Every carrier in (4) has just been shown measurable and L1. Transport
includes the complete path and its selection together; no optional
sampling theorem and no stopping assumption are invoked.

## 4. Condition on the complete suffix, including the crossing label

Fix a late rank floor(n/2)<r<n and put t=n-r>0. Split the iid path p into
its first r coordinates V and its remaining t coordinates Uvec. The
product law is rho^r times rho^t under the canonical finite-coordinate
bijection. The suffix starts AT the rank-r next label b, so b is included
in BOTH T and d. No marked coordinate is deleted before conditioning.
Fix Uvec for the following prefix integration.

If T<h0, the selected carrier is zero. Otherwise T>=h0>0. Put

    w(V)=x sqrt(T+energy(V)),
    gap(V)=w(V)-s*sum(V),
    A={maxWithZero(s*V)<w(V)},
    M=|b|+max(s*d,0),
    Pi(V)=exp(-(max(gap(V)-M,0))²/T).

These are the actual full-energy wall and the signed prefix maximum
through r, with no substitution of deterministic prefix energy.
All are Borel; M>=0 and T are fixed under this prefix integration.
The qualified `gaussian_weight_source_state`, or directly the full
transparent `fixedGaussianWeight` value, identifies the carrier as

    G_r(V++Uvec)
       = 1_{h0<=T} |b|³/(T sqrt(T)) D³ 1_A Pi(V).            (5)

The singleton wall-sign sum has exactly one exponential. On A the
terminal prefix is included in the maximum, so gap(V)>0. This fact is
what lets a nonnegative closed-CDF estimate apply to the whole CDF below,
including atoms and equality at its upper endpoint.

## 5. All-Q large-x strip and the exact profile integral

Use Section 2 / formula (3) of the independently accepted unit193
mathematical proof, at the present prefix rank r, external energy q=T,
and sign s. Its universal constant Cs>0 was selected before all laws.
For every v>=0 it says

    P_r(maxWithZero(s*V)<=w(V), 0<=gap(V)<=v)
       <= Cs (v+beta)²/r.                                   (6)

Its hypotheses are the present support100 bound, x>=16 and r>=n/2.
The strict A is a subset of its closed survival event, and A implies
0<gap. Thus (6) bounds the ENTIRE closed sublevel probability

    P_r(A and gap<=v) <= Cs (v+beta)²/r
                     <= 2Cs (v²/r + beta²/r).               (7)

The result is uniform in every deterministic q>=0. It therefore applies
after fixing this complete suffix, for every T; it is not a result only
on a good-energy event and does not need a weighted-CDF premise. For the
lower sign (6) is proved under the reflected entire law of -X; no symmetry
of rho is assumed. The exact proof and its independent acceptance are
hash-bound inputs. Their mathematical correctness does not imply a new
qualified Lean export.

Apply the OLD QUALIFIED generic theorem
`gaussian_wall_profile_of_quadratic_closed_cdf` to the prefix probability
space with its A and gap, with parameters

    Kcdf=2Cs, Bcdf=beta/sqrt(r), Vcdf=r, Tcdf=T, Mcdf=M.

All hypotheses have been checked: r>0, T>0, M>=0, Borel A and gap, and
(7) for every v>=0; (beta/sqrt(r))²=beta²/r. The theorem gives

    E_{V~rho^r}[1_A Pi(V)]
       <= (Cs/r)(4M²+4T+2beta²).                            (8)

Here T>=4beta², D>=1 and |b|<=sqrt(T). Consequently

    M<=sqrt(T)+|d|=sqrt(T)D,
    4M²+4T+2beta² <= (4+4+1/2)TD² <= 9TD².

Inserting into (8) yields the conditional profile estimate

    E_V[1_A Pi(V)] <= 9Cs TD²/r.                            (9)

This is the bearing gain. The cubic D³ in (5) is still present; (9)
contributes exactly two MORE powers of D, giving D^5 below. There is no
additional scalar D³ absorption claim.

For completeness, the generic theorem is a closed-CDF layer-cake bound:
the Gaussian profile is integrated against (2z/T)exp(-z²/T), z>0, after
shifting its threshold by M. Its qualified proof handles atoms with the
closed sublevel set. Thus changing strict prefix survival to the upper
closed bound in (6) does not discard positive-mass boundary configurations.

## 6. Identify exactly the qualified RootA late omitted bill

Multiplying (9) by the constant suffix factor in (5), and retaining the
EXACT future selection from (1), gives

    E_V[1_{h0<=T, T<H or t<=m} G_r(V++Uvec)]
      <= (9Cs/r) F_t(Uvec)
      <= (18Cs/n) F_t(Uvec).                                (10)

The second inequality uses r>n/2 and nonnegativity. If T<h0 or selection
fails, both selected terms are zero; these branches precede division.
Fubini, already justified by Section 2, integrates (10) under rho^t.
Sum over precisely floor(n/2)<r<n. Equations (3) and (4) imply

    E_mu Bill_J <= 18 C0 Cs E_mu LateW,                      (11)

where LateW is LITERALLY the qualified producer's value

    LateW(a,sigma)=(1/n) sum_{r:Fin n}
       if floor(n/2)<r and tau(a,sigma)<=r and r<nu(a,sigma)
       then |a(sigma r)|³/sqrt(remainingEnergy(a,r,sigma))
              *(1+|remainingSum(a,r,sigma)|/
                         sqrt(remainingEnergy(a,r,sigma)))^5
       else 0.

To check (11)'s identification without weakening a selection: the whole-
path transport of this LateW is (1/n) times the sum of the F_t from (2)
at their actual tails. Identity (1) gives the if-condition, permutation
invariance gives T and d, and firstValue of the complete tail is exactly
a(sigma r). This is an equality of the complete selected carrier. We
have not paid the union by a larger unselected or double-counted sum.
Total real division in the qualified value causes no ambiguity because
its active guard forces T>=h0>0; outside the guard the value is zero.

Qualified `iid_actual_late_omitted_suffix_budget` uses K=2^64, beta,
delta, u, h0, H, m, P, nu and tau EXACTLY as fixed in Section 1. Its
premises are rho probability, the second/third integrability, EX=0,
EX²=1, n>0, x>=16 and u<=exp(-3x²), all supplied here. In particular
its head has no m<=n premise. Its universal constant Cg>0 gives

    E_mu LateW <= Cg beta sqrt(H)/n,
    E_mu LateW <= Cg delta standardNormalTail(x).             (12)

Its measurability and genuine integrability conclusions also agree with
our direct preliminary bounds. Reuse (12); no numerical omitted grid or
old producer is proved or checked again.

Choose the universal constant C=1+18*8000100*Cs*Cg. By (11)–(12),
nonnegativity of beta sqrt(H)/n and of delta standardNormalTail(x), and
C>0, the exact frozen Bill_J satisfies BOTH

    E_mu Bill_J <= C beta sqrt(H)/n,
    E_mu Bill_J <= C delta standardNormalTail(x).

Section 2 already supplied measurable Bill_J, genuine L1 and pointwise
nonnegativity. The same constant works for upper and lower J and for
every actual Brownian representation. This completes the frozen
mathematical candidate.

## 7. Boundary, evidence and original-scope ledger

* T=0 and T<h0 are inactive before inverse powers are used. Nonzero
  physical terms retain their original small-step, sourceAlive and
  endpoint tests in (3); tests are dropped only in a nonnegative bound.
* The cutoff thresholds retain T<h, T>=h0, weak t<=m and the exact strict
  late rank. Natural subtraction is handled for ALL m, including m>n.
* The complete suffix includes b, T and d before independence is used.
  The random wall retains prefix energy after conditioning. No law of
  an adaptively chosen iid suffix or fictitious iid stopping time is used.
* Lower sign uses whole-law reflection; repeated coordinate values and
  closed strip atoms do not require a continuous or symmetric law.
* Uniform physical and Gaussian bounds, plus E T=t, establish ordinary
  L1/Fubini before the numerical producer or any integral comparison.
* This is source consumption of the qualified RootA late omitted grid,
  and does not reimplement its numerical proof. It is distinct from
  RootA's active actual adaptive TERMINAL module. No shared Probability
  source or RootB weighted wall/profile source has been changed.
* It pays ONLY late omitted halfline retained terms. Early omitted
  retained terms, interval retained terms, omitted overshoots, the
  adaptive terminal comparison and final C2 assembly remain separate.
  C2/C12 stays OPEN. No new-original-theorem or novelty claim is made.

Formal continuation has one explicit public interface gap: a qualified
public all-Q x>=16/support100 closed-strip producer with the exact (6),
or an owner-approved public export after unit193 qualification. Its
current private, unqualified Lean implementation cannot be imported
through a brittle private name or promoted to an oracle premise. The
current manuscript is a complete mathematical candidate using the
already independently accepted mathematical statement. It still needs
its own fresh complete independent review. No formal196 declaration,
source, upload, Lean check or axiom check has been created.
