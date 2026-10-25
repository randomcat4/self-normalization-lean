# Actual double-separated overshoot: a closed pointwise bill

Status: complete mathematical candidate, pending independent review. This is
not a Lean receipt or a numerical probability producer. The statement was frozen
in frozen-theory-subject.json before this proof. No premise is changed here.

The source target is supplement.tex 5433–5456 and 5496–5588, especially the
classification at 5564–5585. All completions, derivatives, live guards, labels,
permutations, and rank caps below are the actual existing source objects.

## 1. Objects and claim

Let B be any actual standard real Brownian motion on a probability space and
Q = bridgeLaw B PB. Use the exact actualDerivativeFamily Q from unit191: its
upper/lower components are halflineDerivative upper/lower and its interval
component is the guarded intervalDerivative Q. The new unit191 is still a
same-batch unqualified dependency; only its transparent definition is needed
for this mathematical argument.

Fix n ≥ 0, a labelled real list a of length n, x ≥ 16, a permutation sigma,
an arbitrary cap nu : LabelPerm n → Nat, and a rank r ≥ 0. Write

    w = x sqrt(energy a),       y = prefixSum(reorder a sigma) r,
    T = energy a - prefixSquares(reorder a sigma) r,
    z = prefixSum a n,          d = z-y.

Let U, L, I be the three exact sourceSeparatedOvershoot terms at these same
arguments, and OD = U+L-I. The prefix-only flags are

    HU : for every k ≤ r, prefixSum(reorder a sigma) k < w,
    HL : for every k ≤ r, -w < prefixSum(reorder a sigma) k.

Neither flag includes a condition on the terminal endpoint z. Set

    Bad : 3 x sqrt(T)/2 < |d|,       N = max(-I,0).

There is a universal C > 0, independent of every object just listed, such that
with epsilon = C exp(-x²),

    0 ≤ OD ≤ epsilon (U+L)
               + 1_Bad (U+L+N)
               + 1_not_HL U + 1_not_HU L.                 (1)

The only input constants come from the already qualified universal actual
upper-gradient-ratio theorem. No iid, moment, support, or stopping-rank
assumption is needed for (1).

## 2. Exact interfaces reused

The source definitions and their bytes are bound in input-bindings.json.
The proof uses the following accepted contracts, without rereviewing their
unchanged proofs:

* source_separated_overshoot_sign_domination, for actual derivatives, gives
  U ≥ 0, L ≥ 0, I ≤ U+L, and OD ≥ 0 at every raw state.
* projected_negative_part_control identifies the actual small-crossing term
  as -eta e c G, where e = |b|-u ≥ 0 and c ≥ 0. The same e and c occur for
  the interval and the crossed half-line, because their raw arguments and
  projection to that crossed wall are identical.
* actual_bridge_first_upper_gradient_ratio gives one universal C > 0 and
  0 ≤ dI-dU ≤ C exp(-w²/T)(-dU) when x ≥ 16, T > 0,
  w ≥ x sqrt(T), 0 < w-y ≤ |b|, b² ≤ T/2, |z| < w, and
  |z-y| ≤ 3x sqrt(T)/2. Its derivatives are those of the actual probability
  kernels, rather than an assumed analytic substitute.
* The actual half-line and interval kernel-data contracts identify G with
  these genuine derivatives at interior states, by uniqueness of HasDerivAt.
  The interval differentiability and the two reflection identities are
  produced by the existing actual Brownian bridge modules, as in unit191.
* bridgeLaw_eq_of_isBrownianReal identifies the bridge laws of B and -B.
  Actual all-time bridge reconstruction then gives the sign-reflection
  identities used below. Their consequences are derived in section 3.

The interval derivative guard is relevant: it is read only when |y|<w,
|z|<w, and T>0. On excluded branches the source guard is zero before an
interval derivative is consumed.

## 3. Deriving the lower-gradient bound, with the same constant

Let NB(t,omega) = -B(t,omega). It is again a standard Brownian motion.
The accepted bridge-law universality contract gives

    bridgeLaw NB PB = bridgeLaw B PB = Q.                  (2)

Let R be negation of a pinned continuous bridge path. It is a continuous,
hence measurable, map of BridgeNoise to itself. Intersect the two full-measure
sets supplied by ae_bridgeNoise_eq for B and NB. On that intersection,
for every bridge time t simultaneously,

    bridgeNoise NB omega (t)
      = -B(t,omega)+t B(1,omega)
      = -bridgeNoise B omega (t).

Equality as BridgeNoise elements follows by extensionality; their endpoint
proofs are irrelevant. Taking pushforwards shows R_*Q = bridgeLaw NB PB,
and (2) therefore shows R_*Q=Q. This step is an equality of actual path laws,
not merely separate equality of one-time marginals.

The affine bridge path at (-y,-z) with noise Rg is the negative of the
affine bridge path at (y,z) with noise g. The strict interval event is
preserved and strict lower survival becomes strict upper survival. Their
measurability is already provided by the source contracts. Thus, for every
spatial argument s,

    fI(w,-s,T,-z) = fI(w,s,T,z),
    fU(w,-s,T,-z) = fL(w,s,T,z).                            (3)

At an interior state, differentiate (3) using the actual differentiability
contracts and the derivative of s ↦ -s. This gives

    dI(w,-y,T,-z) = -dI(w,y,T,z),
    dU(w,-y,T,-z) = -dL(w,y,T,z).                          (4)

Suppose now there is a first lower crossing, so y>-w, y+b≤-w,
u=w+y>0, and u≤|b|. Apply the already accepted upper-ratio theorem to
(-y,-z,-b). Its wall, T, x, small-energy condition and displacement bound
are unchanged. Equations (4) yield

    0 ≤ dL-dI ≤ C exp(-w²/T) dL.                          (5)

The constant in (5) is exactly the universal upper-ratio constant, since
the latter quantifies over every actual standard Brownian motion. No lower
ratio assumption has been added.

## 4. Literal zero branches and actual geometry

If r≥n, all three separated terms are zero by their outer definition. If
r≥nu sigma, T≤0, or energy a=0, their common source guards again make
all three zero. The energy-zero case includes the weak-wall rank-zero hit;
no positive-wall reasoning is used on that branch. If b²>T/2, the
localSeparatedOvershoot definition is zero in every domain. These cases
prove (1) immediately.

On any remaining branch r<n, use the actual next label
b=a(sigma <r,hr>). Then energy a>0, w>0 and T>0. The prefix square sum
is nonnegative, so T≤energy a. A single label square is at most the sum
of all label squares. Consequently

    w ≥ x sqrt(T),       |b| ≤ sqrt(energy a) = w/x.       (6)

These bounds hold for every finite list. No external bounded-support law
or moment assumption was inserted.

A nonzero upper term requires HU, z<w, and y+b≥w. A nonzero lower term
requires HL, -w<z, and y+b≤-w. A nonzero interval term requires HU and HL,
|z|<w, and one of those crossings. This follows directly by unfolding
sourceAlive and projectionIncrement; when the selected wall is not crossed,
the projected increment equals b and the factor b-projectionIncrement is
zero. Since w>0, the two crossing conditions cannot hold together.

At an exact equality crossing the excess e is zero. Every formula below
then remains valid with all relevant separated contributions zero. No
strict crossing replaces the weak crossing condition.

## 5. Bad displacement and prior-hit branches

On Bad, the elementary inequality -I≤max(-I,0) gives

    OD ≤ U+L+N.                                           (7)

Every other term on the right of (1) is nonnegative, so (7) suffices.
This is the step that must retain the interval negative part N.

It remains to consider not Bad, namely |d|≤3x sqrt(T)/2. If HU is false,
the upper and interval sourceAlive guards vanish, so U=I=0 and OD=L.
The term 1_not_HU L pays it. If HL is false, similarly L=I=0 and OD=U,
paid by 1_not_HL U. If both flags are false, U=L=I=0. These assertions
use only actual prefix histories. In particular an exterior endpoint by
itself is not described as a prior hit.

We may therefore assume HU and HL, in addition to not Bad.

## 6. Both prefix flags live and the endpoint is interior

Assume |z|<w. If the next point y+b is strictly between the two walls,
all three projections equal b and U=L=I=0. Otherwise there is exactly
one crossed wall.

At an upper crossing put u=w-y and e=b-u. The live flags give |y|<w;
crossing gives b≥u>0 and hence u≤|b|. The small-energy condition is
already in force. For the interval and upper domains the projection is
the same u, and their common coefficient is

    c = 1-(b+u)(z-y)/T ≥ 0.

The lower domain has no crossing, so L=0. The exact projection formula
gives

    U = e c (-dU),        I = -e c dI,
    OD = e c (dI-dU).                                    (8)

Apply the upper-gradient bound to (8), using (6) and not Bad. All
multipliers are nonnegative. Since w²/T≥x², it follows that

    0 ≤ OD ≤ C exp(-w²/T) U ≤ epsilon U.                  (9)

At a lower crossing the common projection is -u for u=w+y. Here
e=-b-u≥0, c=1-(b-u)(z-y)/T≥0, U=0, and the exact formulas read

    L=e c dL,             I=e c dI,
    OD=e c (dL-dI).                                      (10)

Apply the derived lower bound (5) to obtain OD≤epsilon L. Equations
(9) and (10) prove the regular interior case of (1).

## 7. Exterior endpoints force bad displacement on an active opposite crossing

Still assume HU and HL and not Bad. Suppose z≤-w. Then the lower and
interval endpoint guards give L=I=0. The only possible remaining
contribution U would require an upper crossing. Such a crossing gives
y≥w-b, and (6) gives b≤|b|≤w/x. Therefore

    |z-y| ≥ y-z ≥ 2w-b ≥ (2-1/x)w
             ≥ (2x-1)sqrt(T) > (3x/2)sqrt(T).             (11)

The last strict inequality follows from x≥16 and T>0. This contradicts
not Bad. Hence no active upper crossing exists and U=0.

If z≥w, the upper and interval endpoint guards vanish. An active lower
crossing similarly gives y≤-w-b and
|z-y|≥2w+b≥2w-|b|≥(2-1/x)w, giving the same contradiction. Thus L=0.
Equality endpoints z=±w are included in these cases, exactly as required
by the strict endpoint guards. Together with sections 4–6 this exhausts
every state and proves (1).

## 8. Genuine integrability and the exact integrated bill

Let P be any probability law on the finite raw path space, and let
nu(a,sigma) have measurable sections in a for every sigma. Put the
actual product reveal law P × uniformPermutationLaw n on (a,sigma).
No natural iid stopping-time interpretation is asserted or required.

The actual three kernel-data contracts have constant 4. The accepted
source_parts_uniform_bound gives |U|,|L|,|I|≤16(1+n), for each rank and
every raw path. The accepted source_parts_measurable_integrable supplies
their measurability and genuine integrability under this law. The prefix
flags are finite intersections of strict inequalities between continuous
finite sums and x sqrt(energy). Bad is measurable because the actual
remaining sum, energy and sqrt are measurable. Thus every indicator used
in (1) is measurable. Their products, N=max(-I,0), and the finite sums
are genuinely integrable by the displayed uniform bound. This does not
appeal to totalized integrals of nonintegrable functions.

Define the three nonnegative actual bills

    B0     = E sum_{r<n} (U_r+L_r),
    Bbad   = E sum_{r<n} 1_Bad_r (U_r+L_r+max(-I_r,0)),
    Bsecond= E sum_{r<n} (1_not_HL_r U_r+1_not_HU_r L_r).

Finite summation and integration of (1), justified by genuine
integrability, give the exact bound

    0 ≤ E sum_{r<n} OD_r ≤ epsilon B0+Bbad+Bsecond.         (12)

For a nonnegative measurable mask m≤1 the same argument gives the
corresponding masked bills. No positivity claim is made for a signed
mask; its absolute value may be inserted to obtain a norm bound instead.

Equation (12) isolates precisely what the root probability producers
must still pay: all one-wall overshoots at the absolute scale, bad
displacement including the interval negative part, and the opposite-hit
one-wall terms. If they give B0≤C0 delta and Bbad+Bsecond≤C1 delta Psi(x),
then (12) gives the desired rare-scale separated-double bill. The
elementary Gaussian comparison needed for this last implication is
e^{-x²}≤C2 Psi(x), for x≥16. For example the lower Mills bound yields
Psi(x)≥(2pi)^{-1/2} x/(1+x²)e^{-x²/2}; for x≥1,
(1+x²)/x≤2x and x e^{-x²/2}≤1, hence C2=2 sqrt(2pi) suffices.
This numerical conversion changes none of the three exact bills.

No bound for B0, Bbad or Bsecond is silently inferred here. In particular
the theory does not turn a pointwise classification into a completed C2
root theorem. It supplies a source-bound consumer with an explicit list
of the remaining probability interfaces.
