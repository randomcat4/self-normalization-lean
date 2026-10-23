# Unconditional primitive inputs and source K/Kv: complete assembly proposal

AUTHOR161_STATUS: PROVED_AS_EXACT_CONTRACT_COMPOSITION; NOT_FROZEN;
FORMAL_IMPLEMENTATION_NOT_STARTED; ROOT_BE_AND_154_156_QUALIFICATION_PENDING.
Author context: prescribed gpt-6.1-sol / xhigh / fresh context, math-theorem.
This is a complete mathematical proposal using the precise contracts below.
It is not a claim that genuine BE, unconditional K/Kv or general OQ4 is now
qualified. This author supplies neither an independent review nor a kernel
receipt. No Lean implementation, server/probe/build/cache/Git operation or
extra agent was run. All new work is confined to this owned proposal folder.

## 1. Source, target and unaltered quantifiers

Read-only original: C:/game/shao/current/oq4/b01/proof01.md, SHA256
7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38.
The source's Section 1, lines9–36, states K and Kv for iid increments within
each row, with a single common absolute-third-moment bound M; Section 9,
lines316–351, identifies the normalized terminal-block P0–P2 route to 4/pi.
Both excerpts were read. The existing exact154 and156 implementations were
read completely; their proposal/source-contract framing was also inspected.
This is a source-bound composition of those contracts and classical BE/SP
inputs. No originality or resolution of historical QWE16 is asserted.

For every natural j, let ν_j be an actual real Borel probability measure.
Set β_j=∫|x|³ dν_j. In the unit-variance statements assume, for every j,

    Integrable (x ↦ |x|³) ν_j,   ∫x dν_j=0,   ∫x² dν_j=1,
    β_j≤M for ONE real M.

Let h_j>0 tend to positive infinity and N_j be natural numbers. Retain
exactly the source scale conditions

    N_j/h_j² → positive infinity,       N_j/h_j³ → 0.                 (1.1)

Rows need not be coupled. Neither the laws nor their variances have to
converge. No symmetry, atomlessness, nonlattice condition, monotonicity,
positive survival mass or extra first/square-integrability premise is added.

For a path a:Path n=Fin n→R, the source event is literally

    C_n(h)=Shao.closedStrip h
          ={a | ∀k∈N, k≤n → |prefixSum a k|≤h}.

This includes time0, both walls and all atoms. It is equivalent for h≥0 to
remaining in the CLOSED strip under strict exit |S_k|>h. Write π_(n,ν)
for the actual Measure.pi of n copies of ν, not an arbitrary sequence of
probabilities. The existing constant λ=RademacherScalarBounds.lambda=π²/8.

The proposed public normalized and K targets are exactly

    @normalizedKernelMass ν_j (hprob j) h_j N_j 0 → 4/π;             (1.2)
    π_(N_j,ν_j).real(C_(N_j)(h_j)) /
       ((4/π) exp(-λ N_j/h_j²)) → 1.                                (1.3)

Here normalizedKernelMass ν h n z is the EXISTING value
(principalRate ν h ^ n)⁻¹ * killedMass ν h n z, where
principalRate ν h=∫cos((π/(2h))*x) dν. Its supplied probability witness is
displayed explicitly in (1.2). Natural powers, rather than a newly defined
real power, are inverted.

For Kv replace only the unit second moment by

    ∫x² dν_j=v_j,       1/2≤v_j≤2,                                 (1.4)

keeping mean0, absolute-third integrability, β_j≤M, positive heights and
both limits(1.1) literally unchanged. The target is exactly

    π_(N_j,ν_j).real(C_(N_j)(h_j)) /
       ((4/π) exp(-λ v_j N_j/h_j²)) → 1.                            (1.5)

Every proposed public premise is a corresponding154/156 premise after
deleting their primitive S/AC assumptions and the supplied Cq,Cs constants
and sign assumptions. No actual CDF/SP/SAC/asymptotic or desired-limit
premise is inserted in exchange. The sole use of genuine BE is as the
root-owned theorem below, which is still a qualification dependency.

## 2. Exhaustive proposed interface and permitted contracts

declarations.lean.txt exhaustively lists eight imports, two private helpers
and four public theorems in Shao.OQ4.UnconditionalKernelAsymptotic.
There are ZERO new top-level def/abbrev/instance/structure/notation/macro
values. All β,σ,η,Cq,Cs and row functions used below are proof-local notation.
No existing156 visibility/import/source change is proposed.

The new private helpers are lower_moments_integrable and
standardized_law_unit_moments. The latter needs only v>0, h3, mean0 and
second=v for a probability law and produces facts about its actual map.
It has no common-M input because SAC can be proved separately for each
standardized law; the existing156 adapter already handles the common8M
bound and all height/product/event transfers. No new public standardization
helper or duplicated finite-product theorem is needed.

Allowed contracts, with qualification distinguished from mathematics:

* KNOWN_ACCEPTED: Shao.Probability.actual_maximum_spitzer_laplace in the
  unchanged acceptedv57 SpitzerLaplace source2faaf41c…4890fb. It requires
  only probability ν, L>0 and 0<s<1, and concludes the actual max/endpoint
  Laplace generating-function identity. Apply it also to reflectedLaw ν.
* KNOWN_ACCEPTED: Shao.OQ4.reflectedLaw_isProbabilityMeasure in
  ReflectedSurvival, its actual reflected-CDF/survival/concentration mathematics, and
  SpitzerKernelBounds.spitzer_kernel_probability_inputs. The latter takes
  square/third integrability, second1, C_BE≥0, the actual finite-sum CDF
  inequality and the two actual SP identities, and returns β≥1, both
  constant signs and the actual S/AC predicates. Namespace is Shao.OQ4.
* FROZEN_BUT_UNQUALIFIED: Shao.Probability.iid_unitVariance_berryEsseen,
  theorem3 of coordination/public-survival-cdf-declaration-freeze.md.
  For an actual probability ν, h3, mean0, second1, k≥1 and all x it bounds
  the actual π_(k,ν) normalized sum CDF error by1024*β/sqrt(k).
  This is the ONLY genuine CDF producer invoked; it is not an extra premise.
  Its implementation, complete independent review and kernel/axiom
  qualification remain the root owner's obligation.
* EXACT_LOCAL_UNQUALIFIED:154 TerminalNormalizedKernelLimit source
  389252ae255a995174ff4345e4b5b34967cd87e8ab69c5b62713127cfdd9be8b,
  618 LF lines, formal freeze bf1a80104cb1ee7812932127d7a54c274a0db7d8a3d900cc71a092b4f781fd6d.
  Its two final public heads give(1.2)/(1.3) under precisely the unchanged
  moment/height/time inputs plus common nonnegative Cq,Cs and actual
  iidIntervalConcentration / iidOneSidedSurvival at each β_j.
* EXACT_LOCAL_UNQUALIFIED:156 VarianceKernelAsymptotic source
  6fdd2f8053b4f5cd7aa2a3fb6cd7c001aa42bd73c0022576adabbd5e23803a33,
  373 LF lines. Its final public head gives(1.5) under exactly(1.1),(1.4),
  original moment/height/common-M inputs and common nonnegative Cq,Cs with
  primitive S/AC on the ACTUAL η_j=ν_j.map(x↦x/sqrt(v_j)), parameterized
  by the ACTUAL β'_j=∫|y|³ dη_j. Its private moment helpers are not APIs.
* KNOWN_ACCEPTED: VarianceScaling.standardized_moments and the public
  sqrt-variance interfaces, unchanged source f7e0b71c…4cf70d21. These
  establish original-measure scaled test moments; actual map transport is
  proved in Section7, rather than presumed or borrowed from156 private code.

154's upstream149 spectral/150 P1 qualifications remain unpaid. Parent's
current checkpoint says152 D8 is NOW qualified at source136f8b0f/434 LF,
fresh review160ebd00964, original objectd1f6631a and parent acceptance
e8f291feb226211757264b11bec333e81c3a972a13663800066bb7928cd03956.
That update is retained; old154 prose calling all its inputs pending is not
used to revoke the accepted152 evidence. No accepted old unit is rechecked.
All future source/object bindings must match the exact accepted versions.

## 3. Lower integrability and actual β≥1

Let ν be any probability satisfying h3. The constant1 is integrable, so
1+|x|³ is integrable. For r≥0 the inequalities

    r≤1+r³,                 r²≤1+r³                                 (3.1)

follow by splitting at r≤1. In that case r≤1 and r²≤r≤1. If r≥1,
r≤r²≤r³, by multiplying the nonnegative inequalities r−1≥0 by r and r².
Apply(3.1) to r=|x|. The measurable identity and square have norms |x|
and |x|²=x², respectively; Integrable.mono' with the displayed integrable
majorant gives Integrable id ν and Integrable(x↦x²)ν. This is private1.
No integral is treated as a finite moment merely because Lean totalizes it.

Under second1, the accepted third_absolute_moment_ge_one applies with the
just-proved square integrability and h3. Its elementary content is also
explicit: for r=|x|≥0,

    (r−1)²(2r+1)=2r³−3r²+1≥0,
    hence 3x²≤2|x|³+1.

Both sides are integrable; integrate under the probability measure and use
second1 to obtain 3≤2β+1, so β≥1. This is precisely the accepted lemma
called within spitzer_kernel_probability_inputs, not a new unchecked moment
assumption. In particular every unit row β_j≥1, so if needed M≥1 follows
from the existing bound in row0. No M sign is added to a public head.

## 4. Actual CDF and both actual SP identities

Fix the same unit-variance law ν and write β=∫|x|³dν.
For each natural k≥1 and real x, invoke the exact root theorem3 at

    ν, its probability instance, h3, hmean, hsecond, k, hk, x.

This gives, with no substitutions of laws or moments,

    |π_(k,ν).real {a | prefixSum a k/sqrt(k)≤x} − Φ(x)|
         ≤1024*β/sqrt(k).                                          (4.1)

Here Φ is literally Shao.OQ4.standardNormalCDF. Both the event and the
normalization are syntactically the hCDF required by
spitzer_kernel_probability_inputs, at C_BE=(1024:R). Positive k makes
sqrt(k)>0, and(4.1) is required only there. No k=0 standardized-sum use is
made. The all-x statement is the closed CDF, retaining any endpoint atoms.

For every L>0 and s with0<s<1, the accepted actual SP theorem gives

    laplaceG(maxLaplaceMean ν L)s
       =exp(laplaceW(endpointLaplaceMean ν L)s).                     (4.2)

The existing reflectedLaw ν is exactly ν.map(x↦−x), and its accepted
probability instance follows from measurability of negation. The SAME
accepted SP theorem applied to that actual reflected law gives

    laplaceG(maxLaplaceMean(reflectedLaw ν)L)s
       =exp(laplaceW(endpointLaplaceMean(reflectedLaw ν)L)s).         (4.3)

No mean, third moment or variance premise is needed for(4.2)/(4.3).
We do not construct another SP proof or ask for an SP public assumption.
No second BE application to reflection is needed: the accepted
iid_reflected_cdf_error derives the reflected closed CDF error from(4.1)
using a strict-cutoff limit and the atomless Gaussian's reflection formula.
It does not assume the tested iid sum is atomless or replace a strict event
by a closed event for that law.

## 5. Literal universal constants and actual primitive probability inputs

Apply accepted spitzer_kernel_probability_inputs to

    ν, lower_moments_integrable(...).2, h3, hsecond,
    C_BE=1024, 0≤1024, (4.1), (4.2), (4.3).

Its literal conclusion is

    β≥1,
    0≤sqrt(2)*exp(6+3*1024),   0≤1+2*1024,
    iidOneSidedSurvival ν β (sqrt(2)*exp(6+3*1024)),
    iidIntervalConcentration ν β (1+2*1024).

The exact real arithmetic 1+2*(1024:R)=2049 gives the proposed public1
iid_unitVariance_kernel_probability_inputs. Set, proof-locally only,

    Cs=sqrt(2)*exp(6+3*(1024:R)),       Cq=(2049:R).                  (5.1)

The signs follow from the accepted conjunction (also from sqrt/exp
nonnegativity and positive2049). No floating-point evaluation or numerical
approximation of the exponential occurs. Cs is never silently replaced by
an unevaluated or smaller numerical constant.

For clarity the produced predicates expand to, for EVERY k≥1, every real
x and every nonnegative d,

    π_(k,ν).real {a | prefixSum a k∈[x,x+1]} ≤ Cq*β/sqrt(k);
    π_(k,ν).real(closedUpper d) ≤ Cs*(d+β)/sqrt(k);
    π_(k,ν).real(lowerBlockSurvival d) ≤ Cs*(d+β)/sqrt(k).            (5.2)

Both one-sided events include time0, with the supplied d≥0. The reflected
event lowerBlockSurvival d is literally {a | −a∈closedUpper d}; it is the
closed lower bound on all prefixes. No symmetry of ν is inferred. These
are all-positive-time ACTUAL finite-product inequalities, rather than
abstract sequences satisfying a surrogate generating-function identity.
The k=0 events are not part of primitive SAC and are not used there.

## 6. Common-M varying unit rows: exact154 calls

For EACH j install the given instance hprob j for ν_j and apply public1 at
h3 j, hmean j, hsecond j. Denote its result P_j. The SAME constants(5.1)
work for all j, because they depend only on literal1024. Obtain

    hCs := (P_0).2.1;              hCq := (P_0).2.2.1;
    hS j := (P_j).2.2.2.1;        hAC j := (P_j).2.2.2.2.

These signs could equivalently be proved arithmetically. The witnesses are
nonempty because the row index type is N. The SAC parameter in every row
is exactly β_j, not its upper bound M. No monotonicity of SAC in β or
changing constants is needed.

To prove proposed public2 call, verbatim,

    TerminalNormalizedKernelLimit.varying_row_normalized_kernel_mass_tendsto
      νSeq hprob h3 hmean hsecond M hM
      2049 (sqrt(2)*exp(6+3*(1024:R))) hCq hCs hAC hS
      hSeq NSeq hpos hinfty hlong hshort.

All its inputs have now been supplied or are the unchanged public inputs.
Its exact conclusion is(1.2). This is an invocation of a theorem contract,
not an extra assumed limit or a partial finite identity standing in for K.

For proposed public3 make the identical input assembly and invoke

    TerminalNormalizedKernelLimit.varying_row_closedStrip_relative_asymptotic

with exactly the SAME ordered arguments. Its exact conclusion is(1.3).
Its finite path-probability identification, rate compensation and terminal
normalization are already proved within154. This proposal does not alter
or repeat that implementation. In particular source N/h²→infinity and
N/h³→0 are not weakened to fixed-time limits or strengthened by logarithmic,
monotonicity or law-convergence conditions. The supplied common M precedes
every eventual threshold, so this is the required uniform sequential row
statement, not a fixed-law special case. No extra fixed-law theorem is needed.

## 7. Actual standardized law and actual integrals

Now fix a probability ν with h3, mean0 and ∫x²dν=v>0. Let

    σ=sqrt(v)>0,      g(x)=x/σ,      η=ν.map g.

Real.sqrt_pos gives σ>0 and Real.sq_sqrt gives σ²=v. The map g is Borel
measurable (measurable_id.div_const σ), so its actual pushforward η is a
probability, by Measure.isProbabilityMeasure_map_iff or the accepted map
probability instance. This does not use the fallback definition of map
for a nonmeasurable function. No assumption about a limiting variance occurs.

Private1 provides Integrable id ν and Integrable square ν. Invoke the
PUBLIC accepted VarianceScaling.standardized_moments at

    μ=ν, Y=id, σ, hσ, hId, hSq, h3, hmean,
    hsecond.trans (Real.sq_sqrt hv.le).symm.

It gives ν-integrability of g, g², |g|³ and the three exact identities

    ∫g dν=0,    ∫g² dν=1,
    ∫|g|³ dν=(σ⁻¹)³*β,       β=∫|x|³ dν.                          (7.1)

To move these facts to η, take each Borel real test function
f(y)=y, f(y)=y², f(y)=|y|³. It is AEStronglyMeasurable for η; g is
AEMeasurable for ν. The pinned Mathlib integrable_map_measure gives

    Integrable f η ↔ Integrable(f∘g)ν,

so its reverse implication gives ACTUAL η-integrability in all three
cases from the integrabilities just obtained. The pinned integral_map gives

    ∫f(y) dη=∫f(g(x)) dν.                                         (7.2)

Using(7.1), this yields

    η is a probability;   Integrable(y↦|y|³)η;
    ∫y dη=0;             ∫y² dη=1;
    β'=∫|y|³ dη=(σ⁻¹)³*β.                                        (7.3)

The identity and square are actually integrable as shown, although only
the needed third-integrability/mean/second facts are exposed by private2.
That helper is standardized_law_unit_moments and all of its conclusions
have been proved. The map's probability witness is installed locally when
public1 is applied to η. No156 private declaration is accessed, promoted
or assumed public. This reproduces just the moment derivation needed for
SAC, via the accepted public standardized_moments and map APIs.

The exact third formula is retained to exclude a wrong variance/β
substitution. Generally β'≠β. Unit BE is applied to η, using second1
from(7.3), and its bound is1024*β'/sqrt(k). It is NEVER applied as a
unit-variance theorem to ν whose second moment is v.

For the original Kv rows, v≥1/2 implies v>0 and, by the accepted
sqrt_variance_parameters, σ≥1/2. Thus0<σ⁻¹≤2 and(σ⁻¹)³≤8.
Nonnegativity of β and β≤M imply M≥0. The exact equality(7.3) therefore
also gives the common bound β'≤8M. This is a check of compatibility with
156's existing internal mathematics; no new M≥0 or standardized common
bound is imposed publicly, and this bound need not be reproved as a new
top-level head. The proof of β'≤8M can equivalently consume the accepted
sqrt_variance_standardization plus(7.2). Actual β' remains the SAC argument.

## 8. Standardized SAC, then one exact156 final call

For every j derive0<v_j from1/2≤v_j. Apply private2 with ν_j, v_j,
that positivity, and h3 j/hmean j/hsecond j. Its output gives a probability
witness p'_j for the literal η_j=(ν_j).map(x↦x/sqrt(v_j)), third
integrability, mean0 and second1. These facts do not require M or a variance
limit. Let β'_j denote exactly∫|y|³dη_j.

Apply proposed public1 to η_j using p'_j and those moment facts. Obtain,
for the SAME literal Cq,Cs in(5.1),

    iidIntervalConcentration η_j β'_j 2049;
    iidOneSidedSurvival η_j β'_j (sqrt(2)*exp(6+3*(1024:R))).         (8.1)

For each j these are definitionally the hAC/hS arguments of156, including
its map function and its actual integral. Define no alias of η at the
top level. All equality rewrites are either beta-reduction of proof-local
lets or the exact map/moment facts above. No comparison between original
and standardized interval events is required to produce(8.1).

Finally invoke the PUBLIC consumer

    VarianceKernelAsymptotic.varying_row_variance_closedStrip_relative_asymptotic
      νSeq hprob vSeq h3 hmean hsecond hvlower hvupper M hM
      2049 (sqrt(2)*exp(6+3*(1024:R))) hCq hCs
      (fun j => (8.1).first) (fun j => (8.1).second)
      hSeq NSeq hpos hinfty hlong hshort.

Here hCq,hCs come from the same literal producer conjunction (take row0
of η_j), and the pair labels in this display refer to the two statements
of(8.1), not to a new Lean declaration. Every other input is unchanged
from the proposed public4 head. The exact result is(1.5).

For source fidelity, the already-paid156 finite mathematics is as follows.
Its actual finite_product_standardization_map sends π_(n,ν) by the
coordinate map a↦σ⁻¹•a to π_(n,η). Its public
closedStrip_probability_standardization gives the exact probability
equality at n=N_j,h=h_j,σ=sqrt(v_j). Positive σ makes every monitored
weak prefix inequality equivalent; endpoints and time0 are retained.
The exact scale identities are

    N_j/(h_j/σ_j)²=v_j*N_j/h_j²,
    N_j/(h_j/σ_j)³=σ_j³*N_j/h_j³.

The compact variance bounds imply h_j/σ_j≥h_j/2→infinity,
N_j/(h_j/σ_j)²≥(1/2)*N_j/h_j²→infinity and
0≤N_j/(h_j/σ_j)³≤8*N_j/h_j³→0. Thus156 needs no limit of v_j or σ_j.
Its original-law probability and literal exponent −λ*v_j*N_j/h_j² are
the exact final result, not a standardized surrogate. This proposal
CONSUMES that final public theorem and does not reimplement its product,
event, or scale-transfer proofs.

## 9. Boundaries, scope and remaining qualification

The original event at n=0 is the full empty-path space for h≥0 and still
includes k=0; positive h_j is retained for every row. No new N_j≥1
assumption is introduced. Primitive CDF/SAC applies only at positive
times, as its exact contract says. Existing154/156 include zero horizons
in their finite identities and handle eventual long-time conditions.

The final denominators are strictly positive because4/π>0 and exp>0.
No survival probability, killed mass, or arbitrary rate with unproved
positivity is divided out in this new assembly. Any eventual positivity
of the principal rate needed in154 remains its previously proved internal
obligation, not a hidden new premise here. All source closed walls, strict
exit, atoms, lattice cosets and asymmetric laws are retained throughout.

This author has completed all six proposed heads mathematically from the
exact displayed producer contracts: private1 in Section3, private2 in
Section7, public1 in Sections3–5, public2/public3 in Section6, public4 in
Section8. There are no extra helpers, global definitions or unlisted
literal values. All proof-local constants have the values displayed above.

What remains unpaid is precise: genuine root BE theorem3 implementation,
complete independent source/proof review and exact-source server
kernel/all-owned axiom receipt;149 spectral/150 P1 and actual154
qualification; actual156 qualification using the matching154; and this
new module's parent declaration freeze, authorized implementation, fresh
independent complete review and source-bound server kernel/all-owned
transitive-axiom receipt. Accepted152 D8, actual SPv57, VarianceScaling and
accepted reflection/concentration machinery remain paid at their exact
old source/object evidence. No unchanged old check is replayed.

Only propext, Classical.choice and Quot.sound are allowed. No sorry,
admit, new axiom, unsafe or native_decide is proposed. All later Lean work
is server-only under the existing lane lease; this author has no active
heavy lease and ran no Lean/probe. The declaration text is a proposal,
not a claim of successful elaboration.

Unconditional original K, Kv and general OQ4 stay OPEN until the whole
named dependency chain and this assembly are fully qualified. An accepted
partial finite identity or this mathematical composition alone is not a
root-theorem closure. No novelty claim is made.

NEXT_ACTION: parent full-read and freeze the six exact heads, eight imports,
zero-new-value inventory and complete proof; preserve pending producer
qualification bindings. Author161 now performs ACTUAL_FINAL_STOP and
releases this proposal-directory writer, as explicitly assigned. No
continuation, implementation or heavy execution is implied by release.
