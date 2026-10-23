# Actual Brownian survival boundary: complete mathematical proof draft

Status: `PROVED_MATHEMATICALLY_AUTHOR_DRAFT`; independent review pending.
Formal status: `NOT_IMPLEMENTED_NOT_CHECKED`. This is a proof/declaration
proposal, not an accepted Lean result. No proof source, server object, build,
Git operation, cache change, or additional assumption was created.

Author context139, prescribed model/effort gpt-6.1-sol/xhigh. Ownership is only
this directory. The lane lead must freeze exact formal declarations before
implementation. No child context was started.

Frozen mathematical target SHA256:
`0cbca169969ec4e02691a8fdb75072843844ba6432d72df3e040719d4d9a476c`.
Original read-only source: `C:/game/shao/current/oq4/b01/proof01.md`, lines
255–259, whole-file SHA256
`7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38`.

## 1. Exact objects and conclusion

Let P be a probability measure on an arbitrary measurable space Ω. Let
`B : ℝ≥0 → Ω → ℝ` satisfy the pinned Mathlib predicate
`ProbabilityTheory.IsBrownianReal B P`. Thus the actual given process has
the standard centered Gaussian finite-dimensional laws and is almost surely
continuous. Its zero-time value is zero almost surely. No completion or
standard-Borel hypothesis on Ω is added.

Fix T > 0 in ℝ≥0 and u in [-1,1]. Write

    C = {ω : ∀ t ≤ T, |u + B_t(ω)| ≤ 1},
    D = {ω : ∀ t ≤ T, |u + B_t(ω)| < 1},
    M(ω) = sup { |u + B_t(ω)| : 0 ≤ t ≤ T }.

The supremum here is the actual path supremum of B. In Lean the real `sSup`
is total even on exceptional unbounded paths; all uses of the compact-maximum
properties below occur on the almost-sure continuous-path set.

We prove that C and D are P-null-measurable, that

    C \ D = {M = 1}   almost surely,
    P(C \ D) = P(M = 1) = 0,

and explicitly that P(C)=0 for each u=1 and u=-1. The endpoint proof uses
time inversion, independent increments, and the already formalized
Kolmogorov 0–1 law. The interior proof uses Gaussian bridge decomposition
and an explicit measurable-section argument. Neither proof invokes
reflection, strong Markov, Blumenthal's law, or an unproved immediate-crossing
criterion.

## 2. Countable representation and the actual compact maximum

Choose the existing public unit-time enumeration
`a_n = (Shao.Probability.BrownianSup.rationalTime n : ℝ)` in [0,1]. Its range
is dense in [0,1]: it enumerates all rational numbers clamped into [0,1].
Set q_n=T a_n. If T>0, {q_n} is dense in [0,T]; if T=0, every q_n is zero.

For real r define the countable event

    C_r^q = {ω : ∀ n, |u+B_(q_n)(ω)| ≤ r}.

Every coordinate B_(q_n) is AEMeasurable. Hence each inequality event is
null-measurable, and so is the countable intersection C_r^q. Also define

    D^q = ⋃_{k≥0} C^q_(1-1/(k+1)).

This is a countable union of null-measurable events. On every continuous
path, continuity and density give C=C_1^q. On such a path the continuous
function t↦|u+B_t| attains its maximum on the nonempty compact [0,T].
Consequently

    D iff M<1 iff ∃k, ∀n, |u+B_(q_n)|≤1-1/(k+1),

so D=D^q there. The implication from M<1 to the last formula uses only
the Archimedean fact that the positive sequence 1/(k+1) tends to zero.
The reverse implication first extends the fixed weak bound from the dense
set to all times and then uses 1/(k+1)>0.

It follows that the raw, uncountable C and D are null-measurable by almost
sure equality with C_1^q and D^q. This argument does not assert that strict
inequalities just on a dense set characterize D: that assertion would be
false. The common positive margin in D^q is essential.

On the same continuous-path set, M≤1 iff C and M<1 iff D. Therefore
M=1 iff C\D. This also proves that the actual level event {M=1} is
null-measurable. These representation results hold for every u and T≥0,
independently of the zero-boundary proof.

## 3. Interior starts: an independent Gaussian terminal coordinate

Assume now |u|<1. Put

    Y=B_T,                 Z_n=B_(q_n)-a_n B_T.

Both Y and the countable-vector map Z:Ω→ℝ^ℕ are AEMeasurable (the latter
by countably many AEMeasurable coordinates). Y has law γ_T=N(0,T), which
has no atoms because T>0.

We verify independence of the whole countable bridge vector and Y, rather
than just separate coordinate independence. Every finite vector consisting
of some Z_n and Y is jointly Gaussian: its entries are deterministic linear
combinations of finitely many entries of B. For every n,

    Cov(Z_n,Y) = min(q_n,T) - a_n T = q_n-a_nT = 0.

Thus finite jointly Gaussian vectors factor between their Z entries and
Y. By the π-λ theorem on coordinate cylinders this gives independence of
the countable-vector Z and Y. The pinned API
`IsGaussianProcess.indepFun_of_covariance_eq_zero` already performs this
process-level step, with its coordinate AEMeasurable hypotheses; its
finite-linear-image premise is supplied by `of_isGaussianProcess`.
In particular, if ν=P.map Z, then the joint law of (Z,Y) is ν⊗γ_T.

## 4. The needed bridge regularity is Borel and has full ν measure

Define G⊆ℝ^ℕ by

    z∈G iff ∀k∈ℕ, ∃m∈ℕ, ∀n∈ℕ,
                  a_n ≤ 1/(m+1) ⇒ |z_n| ≤ 1/(k+1).

This is a Borel set: the displayed formula has only countable operations
on coordinate closed sets; conditions involving just a_n are constants.
It says precisely enough that z_n tends uniformly to zero along those
indices for which a_n tends to zero. In particular a_n=0 implies z_n=0.

For a continuous B path with B_0=0, the function

    s ↦ B_(T s) - s B_T,       s∈[0,1],

is continuous at zero and equals zero there. For every k choose a positive
neighborhood where its absolute value is at most 1/(k+1), and then choose
m with 1/(m+1) inside that neighborhood. This proves Z(ω)∈G on the
almost-sure continuity/zero-start set. Therefore ν(G)=1. No measurable
selection of continuous paths, regular conditional probability, or
standard-Borel assumption on Ω is needed.

## 5. Deterministic sections contain at most two points

For z∈ℝ^ℕ set

    C_z = {x∈ℝ : ∀n, |u+z_n+a_n x|≤1},
    D_z = {x∈ℝ : ∃k∈ℕ, ∀n, |u+z_n+a_n x|≤1-1/(k+1)}.

For z∈G and |u|<1, we prove that C_z\D_z has at most two points. It
suffices to show that whenever x_1<x_2<x_3 all belong to C_z, the middle
point belongs to D_z.

Let η=1-|u|>0 and choose ε>0 with ε≤η/4. By z∈G, there is δ_0>0 such
that a_n≤δ_0 implies |z_n|≤ε. Choose

    0<δ≤δ_0,       δ(|x_2|+1)≤η/4.

For a_n≤δ the triangle inequality gives

    |u+z_n+a_n x_2| ≤ |u|+η/4+η/4 = 1-η/2.

For a_n>δ put y_i=u+z_n+a_n x_i. Since x_1,x_3∈C_z,

    y_2 = y_1+a_n(x_2-x_1) ≥ -1+δ(x_2-x_1),
    y_2 = y_3-a_n(x_3-x_2) ≤  1-δ(x_3-x_2).

Thus, with

    r=min(η/2, δ(x_2-x_1), δ(x_3-x_2))>0,

all n satisfy |u+z_n+a_n x_2|≤1-r. Choosing k with 1/(k+1)≤r proves
x_2∈D_z. Three ordered points in C_z\D_z are therefore impossible, so
that set is finite, with cardinality at most two. Notice that this argument
allows arbitrary continuous bridge behavior away from zero, including a
degenerate or empty admissible interval.

The regularity at zero is a genuine part of this proof. For arbitrary
sequences z, the supremum of affine functions may have a level plateau,
and the at-most-two-points conclusion need not hold.

## 6. Fubini closes the interior boundary event

Let H⊆ℝ^ℕ×ℝ be the set of (z,x) such that x∈C_z\D_z. Explicitly H is
a countable intersection minus a countable union of countable intersections
of sets defined by |u+z_n+a_n x|≤constant. It is measurable in the product
σ-algebra. For ν-almost every z (namely z∈G), its section H_z is finite,
so γ_T(H_z)=0 by non-atomicity of γ_T. By Fubini for the measurable set H,

    (ν⊗γ_T)(H) = ∫ γ_T(H_z) dν(z) = 0.

For the actual process, the algebraic identity

    Z_n+a_nY=B_(q_n)

holds pointwise for every n. Thus the preimage of H under (Z,Y) is exactly
C_1^q\D^q. Its P measure is zero by the joint-law factorization. Section 2
then gives P(C\D)=0 and P(M=1)=0 for every interior u.

Every probabilistic step here uses a countable measurable vector or a
finite-dimensional Gaussian identity. In particular there is no silent
conditioning on an unmeasurable whole continuous path.

## 7. Independent Gaussian integer walks are unbounded above

We prove the endpoint ingredient rather than assuming it. First let
X_0,X_1,… be measurable independent real random variables, and put

    S_0=0,       S_n=∑_{i<n}X_i.

Suppose each S_n has the actual law N(0,n). (For the application this will
be proved by telescoping actual pre-Brownian integer increments.) Define

    U_K = {∀n, S_n≤K}   (K∈ℕ),       U=⋃_{K∈ℕ}U_K.

U is exactly the event that the real integer sequence S_n is bounded above.
For each m, it also equals

    {∃K∈ℕ, ∀n∈ℕ, ∑_{j<n} X_(m+j)≤K}.                (7.1)

Indeed S_(m+n)=S_m+∑_{j<n}X_(m+j). If the original sequence has an upper
bound, choose a natural number at least that bound minus the finite real
S_m. Conversely an upper bound for the tail sums bounds all n≥m, and
the finite prefix S_0,…,S_(m-1) has a finite maximum. A natural number
dominates the larger of these two finite bounds. This proves (7.1)
pointwise, without exceptional sets.

Hence U belongs to every σ(X_i:i≥m), and thus to the tail σ-algebra of
the independent X_i. The pinned Kolmogorov 0–1 law gives P(U)∈{0,1}.

Let γ=N(0,1) and c=γ((-∞,1]). Its complementary interval has positive
γ measure, so c<1. This can be justified directly from the positive
Gaussian density, or from the pinned `volume ≪ gaussianReal 0 1`: if
γ((1,∞))=0, that absolute continuity would force the positive-Lebesgue-
measure interval (1,2) to be null. Fix K∈ℕ and set N=(K+1)^2. By the
Gaussian law of S_N,

    S_N/(K+1) ~ N(0,1),
    P(U_K) ≤ P(S_N≤K)
           = γ((-∞,K/(K+1)]) ≤ c.

Since U_K is increasing in K, continuity from below gives P(U)≤c<1.
The 0–1 alternative therefore forces P(U)=0. In particular, almost surely
the sequence S_n is unbounded above. This proof does not require a
Gaussian CDF limit, a random-walk recurrence theorem, or symmetry of a
whole countable process law.

## 8. Apply this lemma to actual pre-Brownian integer samples

Let W be any process satisfying `IsPreBrownianReal W P`. Define the raw
increments R_n=W_(n+1)-W_n. They are AEMeasurable and independent as an
entire countable family by `HasIndepIncrements.nat` applied to n↦n.
Choose for each n a measurable version X_n of R_n using
`AEMeasurable.mk`. Coordinatewise almost-sure equality preserves
`iIndepFun` by the pinned `iIndepFun_congr` theorem.

Intersect the countably many equality sets and the set W_0=0. On this
single full-measure set every finite sum telescopes to

    ∑_{i<n} X_i = W_n-W_0 = W_n,       for every n.

Therefore each S_n has law N(0,n), by `hasLaw_eval` and preservation of
law under almost-sure equality. Section 7 applies and proves that the
actual countable sequence W_n is unbounded above almost surely. This
argument explicitly handles AEMeasurable evaluations without completing Ω.

## 9. Time inversion gives actual crossings arbitrarily near zero

For the original B define

    W_t=t B_(1/t),

where at t=0 the Lean expression is zero, because 0 times any real is
zero (and `1/0=0`). The pinned `IsPreBrownianReal.inv` proves that W is
pre-Brownian. No continuity at zero for W is required anywhere: Section 8
uses only its finite-dimensional laws and integer independent increments.

On the full-measure event furnished by Section 8, the sequence W_n is
unbounded above. It is also unbounded above after deleting any finite
prefix: a finite set of real values is bounded above. Hence for every
integer N there is n>N with W_n>0. Such an n is positive and

    W_n = n B_(1/n)>0   ⇒   B_(1/n)>0.

For every real/NNReal T>0 choose N with 1/(N+1)≤T; then choose n>N
as above. This gives a positive time 1/n≤T with B_(1/n)>0.
Applying the same argument to the actual process -B, whose pre-Brownian
predicate follows from `.neg`, gives a positive time ≤T at which B is
negative. The two full-measure sets can be intersected once. On their
intersection the conclusion holds for **all T>0 simultaneously**: no
uncountable intersection of probability-one events is used.

Thus almost surely, for every T>0, B has both a positive value and a
negative value in (0,T]. This is the precise crossing fact needed at the
two initial endpoints. It is derived entirely from valid original inputs.

## 10. Endpoints and assembly

For u=1, every point of C must satisfy B_t≤0 for all t≤T, since
|1+B_t|≤1 implies 1+B_t≤1. Section 9 excludes this on a full-measure
set, so P(C)=0. For u=-1, the analogous bound implies B_t≥0 for all
t≤T, again excluded by Section 9. Thus P(C)=0 for each endpoint, and
P(C\D)=0 follows by monotonicity.

For any u∈[-1,1], either |u|<1 or u is one of these two endpoints.
Combine Sections 6 and 10. The compact-maximum almost-sure equality in
Section 2 then gives the actual supremum level probability zero. All
conclusions in Section 1 follow.

## 11. Boundary/assumption audit and attribution

At T=0 the zero-boundary conclusion fails for u=±1: B_0=0 almost
surely, so C has probability one, D has probability zero, and M=1 almost
surely. Thus T>0 is substantive. The measurability and compact-maximum
identification remain valid at T=0.

The given B and P remain the objects of every final event. The auxiliary
inversion and bridge variables are explicit functions of B on the same
sample space, with laws proved from the actual predicate. No replacement
canonical Brownian process or Rademacher-only statement is substituted.
Fixed positive-time atomlessness is used only after independent bridge
factorization and the finite-section proof; it is not misrepresented as
atomlessness of a supremum.

The conclusion is classical, with no novelty claim. Gaussian bridge
decomposition and time inversion are standard tools; for example time
inversion is recorded in Kees van Schaik's
[MATH4/67201 notes, Proposition 8.9](https://keesvs.net/UoM/teaching/martingales/notes/Chapter8.html).
The actual formal inputs here are the pinned Mathlib theorem definitions
and proofs identified in `api-evidence.md`, especially
`IsPreBrownianReal.inv` and the formalized Kolmogorov 0–1 law. Sections
4–7 supply the measurable-section and endpoint details rather than citing
an external unformalized Brownian crossing theorem.

This unit does not close changing horizons/starts/terminal observables,
weak convergence of the full row process, B4, B0/B1, K/Kv, general OQ4,
Spectrum, energy roots, or any other root group. Raw-leaf credit remains
zero until the prescribed independent review and exact-source server
kernel/transitive-axiom evidence exist.
