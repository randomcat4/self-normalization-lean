# All-rank actual bad-displacement retained budget

STATUS: COMPLETE_MATHEMATICAL_CANDIDATE_PENDING_INDEPENDENT_REVIEW.
The exact subject was frozen BEFORE proof at SHA256
13c16b21e226e01421fa7190bc19b8afdb5aa07431b04f465120e39c557e4745.
This is a mathematical proof candidate, with no independent or native
qualification claimed. It pays the actual retained rare bill, not a
positive overshoot or terminal bill. C2/C12 remains OPEN.

## 1. The frozen actual objects and cap

Let rho be a probability measure, EX=0, EX²=1 and |X|<=B0 a.e., B0>0.
Let n>0, x>=16, B0<=sqrt(n)/(100x), beta=E|X|³,
delta=beta/sqrt(n), and delta(1+x)^3<=exp(-3x²). The constants in the
proof are numerical and chosen before these data. Boundedness gives
second and third integrability, beta>=1, and h0=4beta²>0.
Let P=rho^n and mu=revealLaw(P).

Fix an arbitrary cap nu(a,sigma) such that every section a->nu(a,sigma)
is measurable and nu(a,sigma)<=energyCutoff(a,h0,sigma) pointwise.
No iid stopping or prefix-measurability property is assumed for this cap.
Let Bm be any actual standard real Brownian motion on probability PB and
Q=bridgeLaw(Bm,PB). Set F_J=eventCompletionKernel J Q; G_upper/lower
are the actual halflineDerivative values, and G_interval=intervalDerivative Q.
Write L_J for the literal sourceRetainedRemainder with these F/G and
this SAME cap nu, and O_I for the literal sourceSeparatedOvershoot of
the interval with G_interval and cap nu. At rank r:Fin n put

    T=remainingEnergy(a,r,sigma), d=remainingSum(a,r,sigma),
    Bad_r={(3x/2)*sqrt(T)<=|d|},
    B_r=|L_interval|+|L_upper|+|L_lower|+max(-O_I,0),
    Bill=sum_{r:Fin n} 1_Bad_r B_r.

The bad event is weak, uses the PRE-label true suffix, and includes its
crossing label in both T and d. We never change it to a post-label
unmarked event. All individual sourceAlive/endpoint/projection guards
are retained inside L_J and O_I.

The qualified actual Brownian upper/lower reflection formulas and actual
interval image spatial derivative supply the actual kernel data with
constant 4 for all three domains. They are consequences of the frozen
Brownian premise, not new assumptions. The sectionwise cap measurability
is exactly what source_parts_measurable_integrable requires. Its uniform
source bound gives |L_J|<=1+24(1+n), |O_I|<=16(1+n), on all samples.
The weak bad indicator is Borel by the literal remaining-energy/sum
values and the finite permutation variable. Thus Bill is measurable,
nonnegative, bounded by n(3+88(1+n)), and genuinely L1 before any
comparison, product split or Fubini below.

## 2. A cap-free pointwise Gaussian carrier

Let p=reorder(a,sigma), and for s=+1 or -1 put

    G_s(p,r)=rankGaussianWeight h0 x {s} false p r.

These are deterministic functions of the WHOLE reordered path, not of
an iid stopping time. Let C0=8000100, CP=compensatedProfileConstant>=0,
CI=2CP+40, and Cphys=C0+CI>0. We claim, on every sample/rank state,

    B_r <= Cphys (G_+(p,r)+G_-(p,r)).                        (1)

For each halfline this is precisely the qualified all-x pointwise
actual_halfline_retained_rank_domination, using h0>0, x>0 and the given
cap comparison. That head accepts arbitrary nu and has no x<=1 premise.

Here is the interval part under the SAME arbitrary cap. If its outer
activity fails, both L_interval and O_I are exactly zero. Otherwise
r<nu<=energyCutoff h0 gives T>=h0, the actual sourceAlive gives
w=x sqrt(energy(a))>0, |y|<w and |z|<w for y=prefixSum(p,r), z=sum(a),
and actual remaining-population geometry gives b²<=T for b=a(sigma r).
If T-b²=0, every strictly future coordinate is zero, whence y+b=z.

On this domain, completionExt interval F_interval equals the actual
sourceIntervalCompletion for its entire guarded argument range. The
qualified actual image derivative identifies G_interval with its spatial
derivative at (w,y,T,z). Consequently the local retained source equals
the physical IntervalGaussianLocal.retainedRemainder: for a small step,
the actual upper/lower crossing chooses w-y or -w-y, and otherwise b;
for a large step both definitions keep b. At an upper/lower small
crossing the separated source is the corresponding physical upper/lower
overshoot, with its exact derivative sign; on all other branches both
negative parts are zero. Weak crossing equality is included. These
identities are deterministic, with no law reflection or stopping premise.

Apply the qualified actual Brownian image retained bound at w,y,T,z,b.
Its premises are exactly the stated positive-time/interior conditions,
b²<=T and zero-future reachability. It gives

    |L_interval|+max(-O_I,0)
       <= CI (|b|/sqrt(T))³ (1+|z-y|/sqrt(T))³
                  intervalEnvelope(w,y,T,z,b).              (2)

All-x sourceAlive supplies the two actual signed strict prefix survival
events. The transparent gaussian_weight_source_state identifies the
right side with CI G_I(p,r), where G_I has signs {+1,-1}. Since its
prefix mask is the intersection of the two singleton masks and its
profile is the sum of their nonnegative profiles,
G_I<=G_++G_- on every branch. This also holds outside the common T/h0
selection, where every weight is zero. Combine (2) with the two halfline
bounds to obtain (1). The cap was used ONLY to get T>=h0 on active
sources; therefore no equality nu=energyCutoff or stopping assertion
has been inserted. This is the arbitrary-cap version of the physical
bridge explicitly derived in unit197, not an assumption of that unit's
currently unqualified formal result.

Multiply (1) by the weak Bad indicator. Permutation invariance of total
sum/energy identifies T and d with the complete tail of the same p.
For each fixed sigma, the qualified iid_product_reorder_map sends P to
P; average over its independent uniform probability law. The transported
carrier is therefore the iid full-path function

    1_{(3x/2)sqrt(T_tail)<=|d_tail|} (G_+(p,r)+G_-(p,r)).      (3)

The arbitrary cap has disappeared by pointwise domination BEFORE this
transport. It has not been claimed to be a function of the reordered
path or an iid stopping rank. Each Gaussian weight is nonnegative,
measurable and uniformly bounded by (1+sqrt(n-r))³, so (3) is genuinely
L1. All following iid expectations are of these cap-free carriers.

## 3. Reuse exactly the p=5 rare real-suffix grids

Fix the qualified `iid_marked_and_unmarked_rare_real_suffix_budgets`
at p=5. Its constant Cg>0 is universal after this fixed integer is chosen.
Every hypothesis in its complete head is supplied by Section 1:
bounded probability rho, EX=0, EX²=1, n>0, x>=16 and residual smallness.
Its K=2^64, h0=4beta² and beta/delta agree with ours. Its additional
H,m,vx definitions and conclusions do not impose new premises on this
proof; we use only its MARKED grids below.

For t>0, Uvec~rho^t, let T_t=energy(Uvec), d_t=sum(Uvec),
b_t=firstValue(Uvec), D_t=1+|d_t|/sqrt(T_t) on positive T_t, and define

    F_q(t,Uvec)=1_{T_t>0, h0<=T_t, (3x/2)sqrt(T_t)<=|d_t|}
                   |b_t|³/(sqrt(T_t))^q *D_t^5.

Off this selection its value is zero, exactly the producer's marked q t.
Let Ax=sqrt(standardNormalTail(3x/2))+exp(-x²). Its two exact conclusions
are

    sum_{t=ceil(n/2)}^n E F_3(t,Uvec) <= Cg delta Ax,         (4)
    (1/n) sum_{t=1}^{floor(n/2)} E F_1(t,Uvec)
                                      <= Cg delta Psi(x).  (5)

Here ceil(n/2) is Nat (n+1)/2. These are finite sums of genuine integrals,
not a maximum over a data-selected rank. The producer also supplies L1
for every F_q(t), q=1,3. Directly, q=1 is bounded by
(1+sqrt(t))^5 T_t, with E T_t=t. On h0<=T_t, q=3 is bounded by
(1+sqrt(t))^5 because |b_t|<=sqrt(T_t); it is zero otherwise.
Thus Fubini with both grids is legitimate independently of their bounds.
We reuse the already qualified numerical proof/evidence at exact hashes.

## 4. Early ranks pay directly with q=3

Take r<=floor(n/2), t=n-r>=ceil(n/2), t>0. Split the full iid path into
prefix V of length r and COMPLETE suffix Uvec of length t. The latter
starts at rank r and includes b_t. If T_t<h0 or T_t=0 the Gaussian carrier
is zero. Otherwise its exact singleton value is

    |b_t|³/(T_t sqrt(T_t)) D_t³ 1_A_s Pi_s,

with 0<=Pi_s<=1. Drop its prefix-survival indicator and exponential
in a nonnegative upper bound. D_t>=1, so D_t³<=D_t^5, and
T_t sqrt(T_t)=(sqrt(T_t))³. After multiplying by the original weak Bad,
each of the TWO singleton carriers is <=F_3(t,Uvec) pointwise.
Consequently the total expectation of the early B_r bill, after (1)
and whole-path transport, is at most

    2 Cphys sum_{t=ceil(n/2)}^n E F_3(t,Uvec)
       <=2 Cphys Cg delta Ax.                              (6)

Ranks map injectively to these exact t values, including r=0/t=n.
When a subset rather than the entire grid occurs, missing nonnegative
terms can only enlarge the upper bound. No r or prefix reciprocal is
used at r=0, and the crossing mark has not been averaged away or deleted.

## 5. Late ranks use the actual wall strip to pay q=1

Now floor(n/2)<r<n, t=n-r>0. Fix the ENTIRE suffix Uvec first. Its
T=T_t,d=d_t,b=b_t and Bad event are fixed. If T<h0, the carrier is zero.
For T>=h0, keep the actual random wall

    wall(V)=x sqrt(T+energy(V)), gap_s(V)=wall(V)-s*sum(V),
    A_s={maxWithZero(s*V)<wall(V)}, M_s=|b|+max(s*d,0),
    Pi_s(V)=exp(-(max(gap_s(V)-M_s,0))²/T).

The independently accepted all-Q, support100, x>=16 strip of unit193
applies at external energy q=T, r>=n/2 and either sign. Strict A_s
implies gap_s>0. Hence for every v>=0 its entire closed sublevel event
satisfies

    P_r(A_s and gap_s<=v)<=Cs(v+beta)²/r
                         <=2Cs(v²/r+beta²/r).               (7)

The constant Cs is universal before suffix conditioning. This result
retains the random energy of V, works for every q>=0 and includes atoms;
for the negative sign it uses the reflected entire law, not a symmetry
assumption. Its accepted mathematical proof is the evidence used here,
not the unqualified private Lean193 implementation or a RootB weighted
or good-energy-CDF interface.

The qualified generic quadratic-closed-CDF profile theorem, at
K=2Cs, B=beta/sqrt(r), Vcdf=r, Tcdf=T and M=M_s, gives

    E_V[1_A_s Pi_s] <= (Cs/r)(4M_s²+4T+2beta²)
                     <=9Cs TD_t²/r.                        (8)

All of its complete hypotheses hold: measurable A_s/gap_s, prefix
probability law, r>0, T>0, M_s>=0 and (7). The last inequality uses
T>=4beta², D_t>=1, |b|<=sqrt(T), M_s<=sqrt(T)D_t.
This exact conditional profile calculation and its evidence were already
independently accepted in unit196; we reuse it with the NEW future-only
weak Bad mask, which is constant under the prefix integration.

Multiplying (8) by |b|³D_t³/(T sqrt(T)) and the weak Bad mask gives
for each singleton carrier the conditional bound

    (9Cs/r) F_1(t,Uvec) <= (18Cs/n) F_1(t,Uvec).             (9)

The last inequality uses real r>n/2 and nonnegativity. The D³ remains
and combines with the TWO profile powers to make D^5. The complete
suffix mark and actual weak Bad event are unchanged; this is the
producer's MARKED q=1 weight, not its post-label unmarked/vx weight.
Integrate in Uvec using genuine L1 and sum the late ranks. Their t
values are a subset of 1,...,floor(n/2), for either parity. By (1),
the two signs, and (5), the total late actual source bill is at most

    36 Cphys Cs Cg delta Psi(x).                            (10)

For n with an empty late rank set this is automatic, without dividing
by r=0. No law of a randomly stopped iid suffix is used.

## 6. Convert the early factor and conclude

For x>=16 the already independently accepted unit193 mathematical
comparison gives Ax<=CA Psi(x), with universal CA>0. One explicit
choice is CA=2 sqrt(2pi) exp(3/2). To check the numerical scale without
invoking any private Lean export, integrate the standard normal density
on [x,x+1/x] to obtain

    Psi(x)>=exp(-3/2)/(sqrt(2pi)*x)*exp(-x²/2).

The Gaussian integral upper bound at u=3x/2 gives
Psi(3x/2)<=exp(-9x²/8). Thus

    Ax/Psi(x)<=sqrt(2pi)exp(3/2)*x*
                         (exp(-x²/16)+exp(-x²/2))<=CA.

Indeed exp(x²/16)>=x²/16>=x when x>=16; the second exponential is no
larger than the first. This uses a strictly positive Psi(x), guaranteed
by its positive-density integral, and includes both original Ax terms.

Add the complementary early and late finite-source sums (both L1).
Equations (6) and (10), with C=1+2Cphys Cg CA+36Cphys Cs Cg, prove

    0<=E_mu Bill <= C delta standardNormalTail(x).

Bill's actual measurability, pointwise nonnegativity and genuine
integrability were established in Section 1. The constant is universal
and works for EVERY sectionwise measurable cap dominated by the h0
energy cutoff, every allowed law and every actual Brownian realization.
No assumption in the frozen statement has been changed.

## 7. Bearing scope and remaining evidence

This is the all-rank bad actual RETAINED absolute budget for upper,
lower and interval plus the interval's own negative separated part.
It gives late retained rare control independently of the active weighted
record/positive-overshoot producer. It is not a replacement for RootB's
weighted wall probabilities needed for other source bills, and it does
not claim an adaptive terminal or positive-overshoot bound.

Both signs, weak threshold atoms, T=0, h0 equality, r=0, empty late sets,
large actual step and reachable zero-future time, arbitrary cap dependence
on a and sigma, and finite labeled permutation independence have been
handled. No source-prefix stopping assumption or extra integrability
premise is hidden. Complete consumed physical identities are the same
ones derived in unit197; only the implication r<nu<=cutoff ->h0<=T is
needed, so this new arbitrary-cap quantifier is justified explicitly.

The new proof needs its own fresh complete independent review. Old
qualified rare-grid/source/image evidence and accepted196 conditional
profile evidence may be reused at exact hashes. Formal work still needs
the public qualified all-Q/support100/large-x strip and an exact frozen
all-x interval source/rank bridge with arbitrary cap before implementing
bodies; no brittle private-name access or extra CDF oracle is allowed.
No new Lean/AX/server action has been taken, and source193/194 are not
modified by this manuscript. Original C2/C12 remains OPEN.
