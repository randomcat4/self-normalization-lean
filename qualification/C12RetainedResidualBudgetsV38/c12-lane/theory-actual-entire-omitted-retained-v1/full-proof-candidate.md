# Entire actual omitted retained bill

STATUS: COMPLETE_MATHEMATICAL_CANDIDATE_PENDING_INDEPENDENT_REVIEW.
The exact subject was frozen before this proof at SHA256
893825d8797b880276c314ce88c725b1d34df39ad8bbee8f8e7a6668660cd508.
No Lean197 source, elaborated declaration, server gate, axiom audit or
independent acceptance is asserted. C2/C12 remains OPEN.

We prove the full omitted retained bill for the actual upper, lower and
interval domains, also including the interval's own negative separated
overshoot. We reuse the qualified early omitted result and supply its
missing late counterpart from the actual Brownian image bound and the
exact late omitted real-suffix grid. The source is supplement.tex 4978–5045.

## 1. Objects and the exact bill

Keep EVERY object and assumption of the frozen subject. Thus K=2^64,
rho is a probability law with EX=0, EX²=1, |X|<=B0 a.e., B0>0;
n>0, x>=16, B0<=sqrt(n)/(100x), beta=E|X|³,
delta=beta/sqrt(n), delta(1+x)^3<=exp(-3x²). Define

    h0=4beta², H=Kbeta²(1+x)^6, m=ceil_nat(H),
    nu(a,sigma)=energyCutoff(a,h0,sigma),
    tau(a,sigma)=min(energyCutoff(a,H,sigma), n-m),
    P=rho^n, mu=revealLaw(P).

Here and throughout n-m is natural subtraction, with no m<=n premise.
Beta>=1 by the Lp inequality, so h0>0 and H>=h0. All moments needed below
exist because of bounded support. The constants will be universal.

Let Bm be any actual standard real Brownian motion on the probability
space PB and Q=bridgeLaw(Bm,PB). F_J is `eventCompletionKernel J Q`.
For upper/lower, G_J is `halflineDerivative J`; for interval it is the
literal `intervalDerivative Q`. Put

    L_J(a,sigma,r)=sourceRetainedRemainder J F_J G_J
                    a x (nu(a)) r sigma,
    O_I(a,sigma,r)=sourceSeparatedOvershoot interval G_interval
                    a x (nu(a)) r sigma,
    B_r=|L_interval|+|L_upper|+|L_lower|+max(-O_I,0),
    E_r={tau(a,sigma)<=r<nu(a,sigma)},
    Bill=sum_{r:Fin n} 1_E_r B_r.

These are actual source values with their guards, actual terminal endpoint,
actual full-energy wall and actual derivatives. The negative part belongs
to THIS interval O_I, rather than to either halfline overshoot.

As in the qualified public actual Brownian formula heads, upper and lower
completions satisfy their reflection formulas. The qualified Brownian
image theorem `sourceIntervalCompletion_spatial_hasDerivAt` supplies the
interior differentiability of the actual interval completion. Therefore
`actual_halfline_kernel_data` and `actual_interval_kernel_data` supply
measurability and KernelBounds with C=4 for all three selected kernels
and derivatives. These are consequences of the Brownian premise, not
additional regularity or kernel assumptions.

The exact cutoff measurability and `source_parts_measurable_integrable`
apply. In addition, `source_parts_uniform_bound` gives everywhere

    |L_J|<=1+24(1+n),  |O_I|<=16(1+n).

Hence Bill is measurable, nonnegative and bounded by n(3+88(1+n)). It is
genuinely L1 under mu before we use any integral comparison or Fubini.
This also handles dead sources, zero full energy and terminal equality.

## 2. The qualified early bill is literally the early part

Partition the finite ranks into r<=floor(n/2) and floor(n/2)<r. Let
Bill_early and Bill_late use these complementary masks together with E_r.
Pointwise Bill=Bill_early+Bill_late, and both are nonnegative and L1.

The qualified public head
`iid_actual_early_rare_and_omitted_retained_budget` has the same fixed K,
rho, boundedness, mean/variance, n, x, beta, delta, residual-smallness,
h0, H, m, P, nu and tau. Its transparent F/FY/L values coincide exactly
with Section 1, including the interval derivative and actual cap. Its
`earlyOmitted` is EXACTLY Bill_early, term by term: it includes all three
retained absolute values and the interval's own max(-O_I,0), at precisely
r<=floor(n/2) and tau<=r<nu.

That theorem does not require the additional support100 inequality;
our assumptions supply every premise in its actual head. Take its
universal Ce>0. Its two existing conclusions yield

    E_mu Bill_early <= Ce beta sqrt(H)/n,
    E_mu Bill_early <= Ce delta standardNormalTail(x).        (1)

No proof, axiom or numerical-grid check of this accepted producer is
repeated. Its simultaneous earlyRare conclusion is not used here.

## 3. A new all-x physical interval-to-profile bridge

Write p=reorder(a,sigma). Fix r:Fin n. Let

    w=x sqrt(energy(a)), y=prefixSum(p,r), z=sum(a),
    T=remainingEnergy(a,r,sigma), b=a(sigma r),
    G_s(p,r)=rankGaussianWeight h0 x {s} false p r, s=+1,-1,
    G_I(p,r)=rankGaussianWeight h0 x {+1,-1} false p r.

Let CP be the qualified fixed `compensatedProfileConstant` (nonnegative)
and CI=2CP+40>0. We claim, for EVERY such sample and rank,

    |L_interval|+max(-O_I,0) <= CI G_I(p,r)
                              <= CI(G_+(p,r)+G_-(p,r)).       (2)

This pointwise bridge holds for all x>0; no use is made of the old
x<=1 NUMERICAL interval consumer. Here is its complete physical argument.

If any original outer activity guard fails (r<nu, sourceAlive interval,
or T>0), both actual source values are literally zero. The Gaussian
weights are nonnegative, so (2) holds. On the active branch,

    w>0, |y|<w, |z|<w, T>0, h0<=T, b²<=T.                  (3)

The first three assertions follow from x>0 and the two actual sourceAlive
pieces (prefix and terminal). The threshold comes from r<nu and the
energy cutoff. The step-energy inequality is actual remaining-population
geometry. If T-b²=0, all coordinates strictly after the label have zero
square sum and hence zero sum. The exact prefix next-step identity then
gives y+b=z. This proves the qualified physical theorem's required
zero-future reachability condition, including the last actual label.

The source/local IDENTIFICATIONS are as follows. For fixed w,z satisfying
(3), completionExt interval F_interval w Y S z equals the literal
sourceIntervalCompletion Q w Y S z for all Y,S, by their entire guarded
values: interior Y and positive S use actual intervalCompletion; exterior
Y gives zero; S=0 gives the same reachable-endpoint indicator; other
branches give zero. At y,T the actual image derivative head and uniqueness
of the derivative identify G_interval with the derivative of this same
sourceIntervalCompletion. Thus the source's `localRemainder` equals
`ActualIntervalProjection.sourceRemainder Q w y T z c` for every increment
c appearing in the projection, with its compensation coefficient unchanged.

For b²<=T/2 and a crossing, `projectionIncrement interval` chooses w-y
at an upper crossing and -w-y at a lower crossing. These cases cannot
both hold because w>0. If neither crossing holds it chooses b. The full
transparent `IntervalGaussianLocal.retainedRemainder` makes precisely
the same choice: outside the strict new interior, select the crossed
endpoint when the step is small, otherwise keep b. When b²>T/2 both
values also keep b. Therefore the literal local retained remainder is
exactly this physical `retainedRemainder` on every branch.

For the separated value, outside a small-step crossing it is zero,
because either the local guard is false or projectionIncrement=b.
At an upper crossing its exact expression is

    -(b-(w-y))*(1-(b+(w-y))*(z-y)/T)*G_interval(w,y,T,z),

which is the physical upperOvershoot by the derivative identification.
At a lower crossing it is the physical lowerOvershoot with increment
-w-y and the same derivative; no reflected-law premise is needed for
this identity. Taking max of its negative and zero gives EXACTLY
`IntervalGaussianLocal.negativeOvershoot`, on all branches including
weak crossing equality. Hence the left side of (2) is literally

    |retainedRemainder Q w y T z b|+negativeOvershoot Q w y T z b.

Apply the QUALIFIED public Brownian image theorem
`BridgeIntervalImageResolved.actual_interval_retained_bound` with (3),
b²<=T and the zero-future reachability established above. It gives

    left side <= CI (|b|/sqrt(T))³
                    (1+|z-y|/sqrt(T))³ intervalEnvelope(w,y,T,z,b). (4)

It covers small and large actual energy steps. Its bound is an actual
Brownian conclusion; no Taylor/CDF oracle is left in our theorem.

Now actual sourceAlive supplies BOTH signed strict prefix survivals
through r. Permutation invariance gives energy(p)=energy(a) and sum(p)=z.
The complete `gaussian_weight_source_state` value then identifies G_I
on this active branch with the right side of (4) divided by CI.
Indeed intervalEnvelope is the sum of the two wallEnvelope values, and
wallEnvelope(gap,|b|,s*(z-y),T) is exactly
exp(-(max(gap-(|b|+max(s*(z-y),0)),0))²/T). This proves the first inequality
of (2) with all actual full path and threshold data preserved.

Finally the common nonnegative prefactor in the weights is the same.
Their prefix masks are A_+, A_- and A_I=A_+ intersect A_-. Their Gaussian
sums are Pi_+, Pi_- and Pi_I=Pi_++Pi_-. Therefore

    1_A_I(Pi_++Pi_-) <= 1_A_+ Pi_+ +1_A_- Pi_-.

Outside the common positive-energy/h0 guard all weights vanish. This
proves the second inequality of (2) everywhere, not just on active sources.

For each halfline separately the already qualified all-x pointwise
`actual_halfline_retained_rank_domination`, with cap exactly nu and
threshold h0, gives |L_upper|<=C0 G_+ and |L_lower|<=C0 G_-,
where C0=8000100. Combining with (2), for all sample/rank states,

    B_r <= (C0+CI)(G_+(p,r)+G_-(p,r)).                       (5)

## 4. The exact selected late profile bill

For clarity we give the mathematical profile calculation needed from
unit196 directly, rather than assuming an unqualified Lean196 theorem.
For r<n let t=n-r. The energy cutoff and natural subtraction identity give

    tau<=r<nu iff h0<=T and (T<H or t<=m).                    (6)

This remains true for m>n; it retains strict T<H and weak T>=h0,t<=m.
The selection in (6), T and remaining sum are functions of the whole
reordered path. The qualified iid reorder law transports them TOGETHER
with each G_s from mu to rho^n. All Gaussian carriers are uniformly
bounded by (1+sqrt(t))³ and thus genuinely integrable.

For a late rank floor(n/2)<r<n, condition on the complete suffix Uvec,
including its first, crossing label b. Let T=energy(Uvec), d=sum(Uvec),
D=1+|d|/sqrt(T), M_s=|b|+max(s*d,0). If (6) fails the carrier is zero.
Otherwise T>=h0>0. For the independent prefix V~rho^r, set

    wall(V)=x sqrt(T+energy(V)),
    gap_s(V)=wall(V)-s*sum(V),
    A_s={maxWithZero(s*V)<wall(V)},
    Pi_s(V)=exp(-(max(gap_s(V)-M_s,0))²/T).

The exact weight is |b|³/(T sqrt(T)) D³ 1_A_s Pi_s, with the selection
(6). The already independently accepted unit193 all-Q support100 large-x
strip, applied at q=T, gives for every v>=0

    P_r(A_s and gap_s<=v) <= Cs(v+beta)²/r
                           <= 2Cs(v²/r+beta²/r).             (7)

Here A_s implies gap_s>0; this justifies the complete closed CDF in (7).
The strip is uniform in every q>=0 and works for r>=n/2. The lower sign
uses the reflected whole law, with no symmetry premise. It keeps the
true random prefix energy and needs no good-energy or weighted-CDF
hypothesis. Its accepted mathematical proof, not its unqualified private
Lean implementation, is the source of (7).

Use the qualified generic quadratic-CDF profile theorem with
Kcdf=2Cs, Bcdf=beta/sqrt(r), Vcdf=r, Tcdf=T and Mcdf=M_s. Its complete
hypotheses are met: prefix probability law, Borel A_s and gap_s, r>0,
T>0, M_s>=0, and (7). It yields

    E_V[1_A_s Pi_s] <= (Cs/r)(4M_s²+4T+2beta²)
                    <= 9Cs TD²/r.                          (8)

For the second inequality use T>=4beta², |b|<=sqrt(T), D>=1 and
M_s<=sqrt(T)D, exactly giving 4+4+1/2<=9. The prefactor D³ is retained;
(8) supplies only two additional powers. Since r>n/2, prefix integration
of the selected G_s is at most

    (18Cs/n) 1_{h0<=T, T<H or t<=m} |b|³ D^5/sqrt(T).         (9)

No coordinate has been deleted. Cauchy gives D<=1+sqrt(t) and
|b|³/sqrt(T)<=T, so the last selected suffix carrier is bounded by
(1+sqrt(t))^5 energy(Uvec). Its genuine integral is finite because
E energy(Uvec)=t. Ordinary Fubini is justified before using the budget.
The physical source carriers were already shown L1 in Section 1.

Integrate (9) over the suffix and sum exactly the late ranks. The
whole-path transport and (6) identify the result with the SAME qualified
RootA value LateW from `iid_actual_late_omitted_suffix_budget`:

    E_mu sum_late 1_E_r G_s(reorder(a,sigma),r)
         <= 18Cs E_mu LateW.                                (10)

Its LateW is (1/n) times the exact selected |a(sigma r)|³ D^5/sqrt(T)
sum over floor(n/2)<r and tau<=r<nu. This is an equality of the selected
future carrier, not an enlargement to an unselected weight or a doubled
union. All its K/h0/H/m/nu/tau parameters match (6), for all m.

The qualified producer has a universal Cg>0 and gives

    E_mu LateW <= Cg beta sqrt(H)/n,
    E_mu LateW <= Cg delta standardNormalTail(x).             (11)

Our law's second/third integrability, mean/variance, n/x and residual
hypotheses supply its entire head. Its original proof and exact successful
source/kernel/axiom evidence are reused; nothing is recompiled or re-audited.

## 5. Close this entire omitted retained budget

Multiply (5) by the exact late E_r mask, integrate and use (10) for BOTH
signs. With Cl=36(C0+CI)Cs Cg, which is universal and positive, (11) yields

    E_mu Bill_late <= Cl beta sqrt(H)/n,
    E_mu Bill_late <= Cl delta standardNormalTail(x).         (12)

No actual interval negative part is left over: it was included in (2)
and hence in B_r. Add the complementary early result (1), using the
already established ordinary L1 equality Bill=Bill_early+Bill_late.
Take C=1+Ce+Cl. Nonnegativity of both scales gives the frozen conclusions

    E_mu Bill <= C beta sqrt(H)/n,
    E_mu Bill <= C delta standardNormalTail(x).

Measurability, genuine integrability and pointwise nonnegativity were
established in Section 1. H>=4beta² also implies beta sqrt(H)<=H/2, so
this matches the original retained omitted CH/n scale as a consequence.
This completes the mathematical candidate for the full frozen bill.

## 6. Exact evidence and remaining scope

The new mathematical step is the actual all-x interval source/profile
bridge (2), combined with the selected late profile budget. The old early
combined source bill is reused at its entire public head and exact value.
All constants precede every law and Brownian realization. The original
weak crossings, strict source interiorship, zero energy/time/reachable
future branch, finite labeled reorder, threshold equalities, post-cap
zeros and m>n natural subtraction have been covered explicitly.

There is no new weighted-wall theorem, derivative oracle, Taylor oracle,
iid stopping assumption, positivity assumption about O_I or modification
of the moment/support hypotheses. The interval sign sum was bounded by
the TWO actual singleton profile expectations; an interval survival
probability was not asserted to equal a halfline probability.

Formal implementation still needs the qualified public all-Q/support100
large-x closed-strip interface (currently mathematical evidence with
unqualified private Lean193 implementation) and an exact frozen public
all-x interval rank bridge before bodies. The old numerical x<=1 consumer
cannot be used outside its domain. No source/private-name import shortcut
has been taken. Unit196's fresh independent review is concurrent evidence
validation, not an additional premise of this proof or a formal producer.

This unit pays all three domains' OMITTED RETAINED absolute terms and the
interval's negative separated part. It does not pay omitted positive
overshoots, derive the actual adaptive terminal bound, finish weighted
record/second-wall probabilities, assemble truncation, or prove original
C2. RootA's active TERMINAL source and RootB's weighted source remain
separately owned and untouched. No independent or formal acceptance of
this new proof is claimed until its required review/gates. C2/C12 stays OPEN.
