# Exact actual one-wall source to record/future envelopes

This is a complete mathematical candidate for the three frozen pointwise
claims. No independent verdict or formal qualification is asserted yet.
The original envelope is supplement.tex 5433–5456; the label-deletion
application is 5552–5562. RootB's existing record/overshoot proxy draft
already treats numerical proxy estimates and explicitly leaves the physical
source-value/endpoint/status connection unpaid. This proof addresses that
connection only and claims no novelty or original C2 completion.

Fix the exact raw labelled path, permutation and cap from the frozen subject.
Write p=reorder(a,sigma), j=r+1, S_k=prefixSum(p,k), Q=energy(a),
w=x sqrt(Q), T=remainingEnergy(a,r,sigma), d=remainingSum(a,r,sigma),
b=p_r, U=remainingEnergy(a,j,sigma), and d'=remainingSum(a,j,sigma).
Thus the suffix (U,d') is strictly after the crossing label, and the exact
finite-sum identities are T=b²+U and d=b+d'. No independence is involved.

We first give the upper-sign proof, and then verify the entire lower-sign
transformation explicitly. All inverses below are used only on branches
where their arguments have been proved positive.

## 1. Literal zero branches and the actual active formula

The outer sourceSeparatedOvershoot definition is zero unless r<n,
r<nu(sigma), sourceAlive(.upper,a,x,r,sigma), and T>0. The local separated
definition is zero unless b²≤T/2. On a live upper state the strict source
guards say Q>0, z=S_n<w, and S_k<w for every k≤r. Thus w>0 since x>0.
If w>y+b, with y=S_r, the projected increment equals b, and the separated
factor b-projection is zero. This also proves zero on no crossing.

It remains to consider a live small-energy upper crossing, including its
equality case. Put

    y=S_r, z=S_n, u=w-y, e=y+b-w=b-u, v=w-z.

The actual conditions give 0<u≤b, e≥0 and v>0. In particular b>0.
The exact native halflineDerivative(.upper) is

    -(2v/T) exp(-2uv/T).

The actual upper projection is u, so the local source definition gives

    O = e c (2v/T) exp(-2uv/T),
    c = 1-(b+u)d/T = 1-(b+u)(b+d')/T.                       (1)

This is the literal source term on the active branch. It is not obtained
by assuming a bound on another overshoot. Since d=z-y=u-v<u and u≤b,

    (b+u)d < (b+u)u ≤ 2b² ≤ T.

Consequently c≥0. Every factor in (1) is nonnegative. On an equality
crossing e=0, hence O=0, without changing the weak crossing convention.

If nu(sigma)≤energyCutoff(a,4beta²,sigma), activity implies
T≥4beta²>0. Also b²≤T/2 gives

    U=T-b²≥T/2≥2beta²>0,  b²≤U.                            (2)

Thus the ordinary future-weight guard in the frozen subject is true on
every possible nonzero source term. In particular an active small-energy
branch at j=n is impossible, since its strict-after-label energy U is zero.

## 2. The coefficient and terminal gap are controlled by the true future

Keep the same active state. As b>0 and 0<u≤b,

    c = 1-(b+u)b/T-(b+u)d'/T
       ≤ 1+2b|d'|/T
       ≤ 1+2|d'|/sqrt(U)
       ≤ 3(1+|d'|/sqrt(U)).                                (3)

For the middle inequality use b≤sqrt(U), T≥U>0, and nonnegativity of
every multiplied quantity. Nothing bounds b by an external support
constant. Since S_j=w+e and z=S_j+d',

    v=w-z=-e-d',  0<v≤|d'|.                                (4)

The strict selected-domain terminal endpoint is exactly what gives v>0.
It has not been replaced by a prefix-history condition. Also
exp(-2uv/T)≤1 because u,v,T are positive.

Let s=|d'|/sqrt(U)≥0. Combining (1)–(4) yields

    0≤O ≤ 6e U^(-1/2) s(1+s)
          ≤ 6e U^(-1/2)(1+s)².                             (5)

All current-state square sums and sums have been converted to the exact
strict-after-crossing-label future. In particular it would be incorrect
to substitute the pre-label T or pre-label d for U or d' in this weight.

## 3. Actual first crossing supplies the record and closed strip

Let M_r=max_{0≤k≤r}S_k and D_j=max(S_j-M_r,0). The finite maximum exists
and includes rank zero. The source's strict prefix survival gives M_r<w.
On the active crossing S_j≥w. Therefore

    F_j=S_j-w=e≥0,
    S_j-M_r ≥ S_j-w=e,
    0≤F_j≤D_j.                                             (6)

Together with (2), (5) and e≤D_j, this proves claim 1 on every active
crossing. On an inactive source branch, a large-energy branch or no
crossing branch, O=0 while D_j≥0 and the selected future weight and strip
indicator are nonnegative. Hence the same bound holds on every raw path:

    0≤O≤6D_j W 1_{0≤F_j≤D_j}.                              (7)

This is an upper bound obtained after respecting every actual source
guard. In particular the right side may be positive when a source
endpoint guard is false; it is then merely a nonnegative dominating
proxy, not an assertion that the source was active.

## 4. The opposite prefix hit gives the exact circular witness

Suppose the source is active and there is k≤r with S_k≤-w. Since r<j,
this is one of the prefix arcs allowed in the frozen circular witness:
select cyclic starting index i=0 and arc length k. Its arc sum is S_k.
The finite maximum L_j therefore satisfies

    L_j≥S_j-2S_k≥S_j+2w≥3w.                                (8)

This L_j is exactly the finite sSup expression frozen in Root's
SourceWeightedPrefixWall public context at dimension j; only its value
is consumed here. No weighted CDF/profile estimate, accepted or pending,
is used. The full arc set is nonempty and finite, so selecting this
particular arc is legitimate, including k=0 if it were to occur.
For an active positive wall, a prior hit at k=0 is in fact impossible.

On a source-inactive branch the masked source is zero. Otherwise (8)
allows the corresponding circular-witness indicator to be inserted into
(7), proving claim 2. The prefix hit never includes a terminal endpoint
test. Both zero excess and failure of the prefix-hit mask are covered.

## 5. Lower sign: transform the complete state, including the derivative

For epsilon=-1 replace the entire finite path p by -p. Total energy and
every remaining energy stay the same. Prefix sums, remaining sums, next
label and strict-after-label future sum change signs. The upper strict
prefix/endpoint conditions for -p are precisely the lower strict
conditions for p. An upper weak crossing for -p is precisely a lower
weak crossing for p.

Here u=w+y, v=w+z, b_epsilon=-b, d_epsilon=-d and d'_epsilon=-d'.
The actual lower halflineDerivative is +(2v/T) exp(-2uv/T), whereas
the lower projected increment is -u. Thus its literal separated value is

    -(b+u) (1-(b-u)d/T) (2v/T) exp(-2uv/T)
      = (b_epsilon-u)
          (1-(b_epsilon+u)d_epsilon/T)
            (2v/T) exp(-2uv/T).

It is exactly formula (1) in the transformed variables, with no missing
chain-rule sign or assumed symmetry of a probability law. The future
weight uses |d'| and is unchanged. M_r, D_j, F_j and L_j are exactly
their epsilon-signed versions in the frozen subject. A prior upper hit
in p is a prior lower hit in -p. Therefore (2)–(8) prove claims 1 and 2
for epsilon=-1 as well. No Brownian-law assumption is required: the two
halflineDerivative branches are already the actual explicit formulas.

## 6. Bad displacement after deleting the actual crossing label

Now assume H≥4beta², m≤n, x≥1, and

    nu(sigma)≤min(energyCutoff(a,H,sigma),n-m).

On an active source term, r<nu gives T≥H and r<n-m. The integer
inequality r+1≤n-m gives j≤n-m, so the strict-after-label suffix length
t=n-j satisfies t≥m. Small energy implies U≥T/2≥H/2>0. These are
exactly the two structural guards on the future weight in claim 3.

Let A=3x/2>1. On the weak bad event |b+d'|≥A sqrt(b²+U), apply the
deterministic two-dimensional Cauchy inequality to

    (b,sqrt(U)) and (1,d'/sqrt(U)).

It gives

    (b+d')²≤(b²+U)(1+d'²/U).

The bad inequality and b²+U=T>0 imply

    A²≤1+d'²/U,
    d'²≥(A²-1)U,
    |d'|≥sqrt(A²-1)sqrt(U).                                 (9)

The last step uses nonnegative square roots and A>1,U>0. This deletion
uses the actual crossing label, before calling anything an independent
future; no deletion or factorization was performed earlier. It is
unchanged under the complete sign transformation of Section 5.

Consequently, whenever the source is active and Bad is true, every
guard in the frozen future weight V is true, and that V equals the
unmasked positive factor U^(-1/2)(1+|d'|/sqrt(U))² in (5). The same
record/closed-strip argument (6) now gives

    0≤O_epsilon 1_Bad
       ≤6D_j^epsilon V 1_{0≤F_j^epsilon≤D_j^epsilon}.          (10)

If Bad is false or the source is zero, the left side is zero and the
right side is nonnegative. This proves claim 3 on every raw state,
including weak Bad equality, crossing equality, reached caps, either
selected-domain exterior endpoint and zero energy. U=0 or t=0 leaves
the future weight zero and cannot conceal a nonzero active small step.

## 7. Evidence and intended numerical use

All three conclusions are pointwise physical-to-proxy bounds. They do
not assume the numerical RootB proxy estimates and do not qualify those
pending proofs. Conversely, an independently qualified numerical proxy
estimate for these same complete-path functions can now be applied to
the actual source term by monotonicity, after checking the exact law,
mask, structural cap and source hashes.

The expressions are Borel finite sums/maxima and selected positive-energy
weights. For fixed beta>0 the ordinary W is bounded by
(1+sqrt(n))²/(sqrt(2)beta): Cauchy gives |d'|/sqrt(U)≤sqrt(n-j).
Also D_j≤2 sum_i |p_i|. Thus under any bounded product law all displayed
proxies are genuinely integrable, with or without either mask. The
same conclusion follows from coordinate L1 where needed. This verifies
that the physical envelope does not introduce a divergent-integral
shortcut; it supplies no new numerical rare/second-wall payment itself.

No original C2/C12 theorem, total separated budget, retained budget,
terminal corridor or unbounded-law comparison is claimed complete.
