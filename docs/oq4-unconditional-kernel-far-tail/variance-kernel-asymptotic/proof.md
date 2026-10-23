# Actual varying-variance sequential Kv adapter: complete author proposal

STATUS: PROVED as a mathematical adapter from the exact frozen conditional
unit-variance row-K contract. This is a proposal, not a declaration freeze,
implementation, independent review, kernel result, or unconditional Kv theorem.
The row-K producer154 remains LOCAL/unqualified. Its proof was not read. The
primitive S/AC producers remain UNPAID. All original K/Kv/general OQ4 roots and
all other recorded open roots remain OPEN. No novelty claim is made.

## 1. Exact source, quantifiers, and allowed dependency

The source is C:/game/shao/current/oq4/b01/proof01.md lines9–36, SHA256
7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38.
Its K has an iid law within each row, third absolute moment bounded by one
common M, closed walls, strict exit, h→infinity, N/h²→infinity, N/h³→0.
Lines31–36 assert the variance-v form for v in [1/2,2], without replacing the
common bound by rowwise finiteness. The intake notes are orientation only,
never proof evidence. The exact immutable producer declaration contract is
frozen-terminal-normalized-kernel-formal-v1.lean.txt, SHA256
bf1a80104cb1ee7812932127d7a54c274a0db7d8a3d900cc71a092b4f781fd6d;
its parent freeze is SHA256
d0a98bd623e6618e9246b9b5ea92a0f5b5ba0e6373c500d76bc69c1b5db0699d.

For every j∈N, ν_j is an actual probability measure on real Borel space.
Assume |x|³ is ν_j-integrable, ∫x dν_j=0, ∫x² dν_j=v_j,
1/2≤v_j≤2, and β_j:=∫|x|³ dν_j≤M for the SAME real M.
The deterministic h_j are positive and tend to infinity. The horizons N_j
are natural numbers with N_j/h_j²→infinity and N_j/h_j³→0.
Set, as proof-local notation only,

    σ_j = sqrt(v_j),  g_j(x)=x/σ_j,
    η_j = ν_j.map g_j,  a_j=h_j/σ_j,
    β'_j = ∫|y|³ dη_j.

The public theorem assumes uniform nonnegative Cq,Cs and LITERALLY

    iidIntervalConcentration η_j β'_j Cq,
    iidOneSidedSurvival η_j β'_j Cs

for every j. These are assumptions on the actual standardized law, not on ν_j
or the old numerical β_j. No universal producer for them is claimed here.
No symmetry, nonlattice condition, law convergence, v_j convergence,
cross-row coupling, monotonicity, positive survival mass, arbitrary row event,
or supplied row-K/normalized-limit conclusion is assumed.

The only non-elementary limit input is the exact frozen public producer

    TerminalNormalizedKernelLimit.varying_row_closedStrip_relative_asymptotic.

It applies to probability rows of mean0, second moment1, integrable absolute
third moment with common bound, their own actual S/AC, and the three displayed
height/time conditions. Its conclusion concerns the actual finite product law
and the source's closedStrip, divided by (4/pi)exp(-λN/a²), λ=pi²/8.
We do not postulate this conclusion as a new public premise. The future module
will CALL this actual theorem only after its exact source/object qualification.

The target is the same actual original finite-product probability, divided by

    (4/pi) exp(-λ v_j N_j/h_j²),

tending to1. The finite helpers and scale transfers below are proved without
that producer; the final conditional adapter uses it once.

## 2. Lower moments and nonnegative common bound

For r≥0, r≤1+r³ and r²≤1+r³. If r≤1 both follow from r,r²≤1.
If r≥1, r≤r³ and r²≤r³, by multiplying nonnegative factors.
Take r=|x|. A probability measure is finite, so the constant1 and
1+|x|³ are integrable. The identity and square are Borel measurable, and their
norms are bounded by this integrable majorant. Thus x and x² are integrable.
This proves lower_moments_integrable with no extra moment assumption.

The integral of the everywhere nonnegative |x|³ is nonnegative. Apply the
common bound at j=0: 0≤β_0≤M. Thus 0≤M. This proves
common_moment_bound_nonneg. In the single-row helper the identical reasoning
gives 0≤M from its own β≤M; it does not require a new public M≥0 premise.

## 3. Positive, uniformly bounded actual standard deviations

The accepted sqrt_variance_parameters, at the actual v, gives

    σ>0,  σ²=v,  1/2≤σ.

Its exact accepted source and existing qualification are bound in
api-evidence.md; no old proof or successful check is replayed. Since v≤2
and σ≥0, σ>2 would imply σ²>4>2≥v=σ², a contradiction.
Thus σ≤2. This proves sqrt_variance_uniform_bounds.
In particular all later divisions by σ and all original positive h are legal.
We use the convenient coarse bounds [1/2,2], not an unjustified σ limit.

## 4. Actual mapped probability and every mapped moment

First prove the generic mapped_integrable_integral. For arbitrary real σ,
g(x)=x/σ is Borel measurable, including σ=0 under real field conventions.
Let f:R→R be Borel and suppose f∘g is ν-integrable. Borel real f is
strongly measurable and hence almost everywhere strongly measurable for
ν.map g. The pinned integrable_map_measure states exactly

    Integrable f (ν.map g) ↔ Integrable (f∘g) ν,

with these AE strong-measurability and AEMeasurable g premises. Its reverse
direction supplies actual mapped integrability. The pinned integral_map gives

    ∫ f d(ν.map g) = ∫ f(g(x)) dν.

This is a proved transport identity, not an identification of ν and its map.

For a row, apply accepted sqrt_variance_standardization at μ=ν,Y=id,v,M.
Section2 supplies both lower integrabilities and M≥0; all the remaining
arguments are exactly the row's h3, mean, second, third-bound hypotheses.
The result gives ν-integrability of g, g², |g|³ and

    ∫g dν=0,  ∫g² dν=1,
    ∫|g|³ dν=(σ⁻¹)³ β≤8M.

Apply the generic transport just proved to f(y)=y, y², and |y|³, each Borel.
It yields actual η-integrability of all three test functions and

    ∫y dη=0,  ∫y² dη=1,
    β'=∫|y|³ dη=(σ⁻¹)³β≤8M.                 (4.1)

The mapped measure really is a probability: g is measurable and the original
measure is a probability. Use the pinned map probability instance, or
Measure.isProbabilityMeasure_map_iff with the proved AEMeasurable g.
The proof never relies on the current map definition's nonmeasurable fallback.
This proves every conjunct of standardized_law_moments. The local η probability
witness is installed only as a proof-local instance where a caller needs it.
No new top-level instance, probability alias, or standardized-law definition
is introduced.

## 5. The genuine finite-product pushforward

Fix a probability ν, n∈N and any real σ. Write μ_n=pi_(i:Fin n)ν,
η=ν.map(x↦x/σ), and F(a)=σ⁻¹ • a, pointwise on Path n=Fin n→R.
For each coordinate, g(x)=x/σ is measurable, η is a probability by section4,
and hence η is sigma-finite. The pinned primary source theorem
Measure.pi_map_pi applies with every coordinate measure ν and every
coordinate function g. It gives the equality of ACTUAL measures

    μ_n.map (a↦(i↦a_i/σ)) = pi_(i:Fin n) η.      (5.1)

At every a,i, σ⁻¹*a_i=a_i/σ by the field definition of division and
commutativity, even σ=0. Function extensionality identifies this coordinate
map with F, proving finite_product_standardization_map:

    μ_n.map F = pi_(i:Fin n) η.                  (5.2)

The product theorem has a finite index type and no nonempty-index hypothesis.
For n=0 both laws are the unit mass on the unique empty path and F is the
unique self-map. Thus (5.2) includes the actual empty product, with total
mass1; it is not an induction that silently starts at n=1.

For further event transport F is measurable: each coordinate is the real
measurable function a↦a_i/σ. The finite product measurability criterion (or
the pinned AEMeasurable.of_eval for this countable index) supplies actual
(AE) measurability of F. This is proved independently of any event formula.
No independence slogan or equality of just marginals substitutes for (5.2).

## 6. Exact closed-strip probability, time zero, atoms and endpoints

Now suppose σ>0 and h≥0. Let C_n(h) denote the actual source closedStrip:

    {a : Path n | ∀ k∈N, k≤n → |prefixSum a k|≤h}.

Every prefix is a finite sum of coordinate evaluations, hence measurable.
The countable intersections of the closed inequalities are measurable.
Alternatively the accepted measurableSet_shiftedClosedSurvival at z=0,
together with shiftedClosedSurvival_eq_closedStrip for nonnegative h, gives
the same actual set measurability. In particular C_n(h/σ) is measurable
because h/σ≥0. There is no continuity-of-distribution assumption.

Accepted path_variance_scaling gives, pointwise and for every natural k,

    prefixSum(F(a),k)=prefixSum(a,k)/σ,
    F(a)∈C_n(h/σ) ↔ a∈C_n(h).                 (6.1)

Its hypotheses are exactly σ>0,h≥0. Positivity of σ makes division preserve
the weak inequalities; it does not remove equalities on the walls.
Thus F⁻¹(C_n(h/σ))=C_n(h) by set extensionality. Combining the measurable-set
map formula with the genuine measure identity (5.2) gives an ENNReal equality

    (pi_i η)(C_n(h/σ))
      = (μ_n.map F)(C_n(h/σ))
      = μ_n(F⁻¹(C_n(h/σ)))
      = μ_n(C_n(h)).                            (6.2)

Apply ENNReal.toReal to this equality, or unfold Measure.real, to obtain the
public closedStrip_probability_standardization in the declared orientation.
No subtraction, limit, conditional probability, or division by survival mass
appears. Both product laws are probabilities in any case.

The event includes k=0, where prefixSum=0. If n=0 it is the full empty-path
space for h≥0, so both real probabilities in (6.2) equal1. If h=0 the event
is exactly the paths with every monitored prefix zero; the same equality
holds. The terminal index k=n, every intermediate integer time, atoms at the
wall, lattice cosets, and both endpoints ±h are all retained pointwise.
The asymptotic theorem uses h>0 but does not need N>0 for every row.

## 7. Scaled height tends to infinity without a variance limit

For each j, sections1,3 give σ_j>0, σ_j≤2 and h_j>0. Therefore

    a_j=h_j/σ_j>0,  a_j≥h_j/2.                 (7.1)

For any real threshold R, eventually h_j≥2*max(R,0), by h_j→infinity.
Then a_j≥h_j/2≥max(R,0)≥R. This is exactly a_j→infinity.
It proves both conjuncts of standardized_height_tendsto without any
continuity argument along v_j and without assuming that v_j converges.

## 8. Both actual time ratios

Accepted sqrt_variance_scale_ratios applies at every j with h_j>0 and gives

    N_j/a_j² = v_j N_j/h_j²,
    N_j/a_j³ = σ_j³ N_j/h_j³.                  (8.1)

These are exact for N_j=0 as well. Set r_j=N_j/h_j² and s_j=N_j/h_j³.
Both are nonnegative because N_j≥0 and h_j>0. Since v_j≥1/2,

    N_j/a_j² ≥ (1/2)r_j.                      (8.2)

For any threshold R, eventually r_j≥max(0,2R), since r_j→infinity.
Then (8.2) is ≥R. This proves standardized_quadratic_ratio_tendsto.

The bounds 0<σ_j≤2 imply 0≤σ_j³≤8 by multiplication of nonnegative factors.
Consequently

    0≤N_j/a_j³≤8s_j.                          (8.3)

Given ε>0, s_j→0 supplies eventually |s_j|<ε/8; since s_j≥0,
(8.3) implies |N_j/a_j³|=N_j/a_j³<ε. This is convergence to0 and proves
standardized_cubic_ratio_tendsto. No bounded-factor convergence is presumed,
and no limit for σ_j, σ_j³ or v_j is used. The coarse8 is uniform in j.

## 9. One actual unit-variance row-K call and exact denominator

Define ηSeq j=η_j and aSeq j=a_j ONLY as proof-local functions. For every j,
install hprob j for ν_j while applying standardized_law_moments. Its output
provides actual η_j probability witnesses, η_j-integrable |y|³, mean0,
second1, and β'_j≤8M. Thus one common real bound8M is available. The public
S/AC premises are already exactly iidIntervalConcentration η_j β'_j Cq and
iidOneSidedSurvival η_j β'_j Cs. They need no rescaling of their constants,
no renaming of β_j into β'_j, and no original-law interval covering argument.
Sections7–8 supply positive a_j, a_j→infinity, N_j/a_j²→infinity,
N_j/a_j³→0. Cq,Cs are nonnegative by the public hypotheses.

Consequently the exact frozen producer, once qualified, is called at

    νSeq=ηSeq, hprob=mapped probability witnesses,
    h3=mapped third-integrability, hmean=mapped mean0,
    hsecond=mapped second1, M=8*M, hM=mapped third bound,
    Cq,Cs,hCq,hCs,hAC,hS as displayed,
    hSeq=aSeq, NSeq=NSeq, and the three proved scale limits.

It yields the limit of

    (pi_(Fin N_j)η_j).real(C_(N_j)(a_j)) /
      ((4/pi)exp(-λN_j/a_j²))  → 1.           (9.1)

For every j, section6 at n=N_j,σ=σ_j,h=h_j replaces the numerator in (9.1)
by the ORIGINAL (pi_(Fin N_j)ν_j).real(C_(N_j)(h_j)).
The first exact equality (8.1) gives, by real multiplication/division algebra,

    -λ*N_j/a_j² = -λ*v_j*N_j/h_j².            (9.2)

Applying exp and multiplying by4/pi identifies the denominators EXACTLY,
for each j, including zero horizons. Function extensionality rewrites the
whole ratio sequence, so its Tendsto conclusion is precisely the declared
varying_row_variance_closedStrip_relative_asymptotic.

Only the displayed deterministic exponential denominator occurs in the
ratio. It is positive since pi>0 and exp>0; positivity of the probability
itself is never assumed or needed, and no survival mass is divided out.

## 10. Complete inventory, source fidelity and next gate

The companion declarations.lean.txt is exhaustive: eleven theorem heads,
eight private and three public, six imports, namespace
Shao.OQ4.VarianceKernelAsymptotic. There are ZERO new def/abbrev/instance,
structure, notation or macro values. All σ,g,η,β',F,μ_n and sequence names in
this proof are mathematical/proof-local notation only, not proposed new
top-level declarations. Every head is proved above: section2 covers1–2,
section3 covers3, section4 covers4–5, section5 covers6, section6 covers7,
section7 covers8, section8 covers9–10, and section9 covers11.

This adapter preserves the intended common-M sequential Kv scope and permits
arbitrary varying variances in the fixed compact interval. The explicit
standardized-law primitive assumptions remain a real unpaid restriction
relative to the unconditional source claim. The finite transport identities
do not pay S/AC, long-time K, external Berry–Esseen, or any other open root.

Next: parent must FULL-read this proof, every literal head/import/value
inventory and the pinned API evidence, then substantively freeze them.
Only a separately authorized implementation may follow. Final acceptance
requires the actual row-K producer's qualification, an independent complete
source-to-statement/proof review of the eventual exact source, and its
server kernel plus all-owned transitive-axiom receipt. No Lean, import,
object, toolchain, Git, build or cache command was run by this proposal author.
