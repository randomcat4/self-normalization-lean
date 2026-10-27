# Unit 230 fresh independent complete SOURCE/proof review

STATUS: CORRECT
SOURCE_STATUS: SOURCE_ACCEPTED_FOR_NATIVE
qualified: false
kernelPending: true

This verdict covers the exact 10511-byte, 241-LF source
`author-01/IIDSourceStrictMomentBudgets.lean`, SHA256
`68dec15cc392157d84d3bf8d6dd8193668182458f6734daadbf668b19f2144b7`.
It is a complete independent source-to-statement and proof review, with no
critical mathematical gap found. It is not a new Lean kernel or transitive
axiom receipt. The complete exact new source must still pass its first native
server check and its same-FIRST-original-object all-actual TYPE/VALUE/AX audit
before qualification can become true.

The sole public theorem is
`Shao.OQ6.IIDSourceStrictMomentBudgets.actual_iid_source_z_strict_moment_budgets`.

## Independence, authority and evidence

The reviewer is the fresh never-author role
`/root/oq56_iid_source_strict_budgets230_source_review`, activated by
`review-activation-01/ACTIVATION.json` SHA256
`c2aa3ea0962380eaa54607bf35f584eb4b1bca70cdb78138e6bd75a29dd58d48`
and its complete `BRIEF.md` SHA256
`3f3ff8e872c9e35f8df73f4f7f9ae21f80a4abeeaf1c718183c1dae5e9405232`.
Actual runtime ACK was sent before the substantive review. The reviewer did
not author, edit or repair this source or freeze. All writes are confined to
`unit230/source-review-01/**`.

The math-theorem skill and its complete prompt-library, openai-workflow and
lean-verification references were read. The task's source-only role and the
project's server-only execution rule override the skill's generic local
toolchain-probe suggestions. No local Lean command, server request, network
request, transfer, Git/API operation, child delegation or old proof/leaf audit
replay was performed. Units 228 and 229 were not read, used, imported,
renamed, copied or retried. The requested model/effort are
gpt-6.1-sol/xhigh; actual model, actual effort and input/cachedInput/output/
reasoningSubset counts are unexposed and recorded as null.

Complete new-source read coverage is lines 1-241. Complete primary read
coverage is all lines 1-355 of read-only `C:/game/shao/current/oq56/inputs02/p51.md`,
SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`.
The complete Stage 1 candidate (159 lines), SOURCE-AND-ROUTE (179 lines),
author report (110 lines), author compatibility (131 lines), frozen preamble,
head, closing, full typed inventory, both parent intakes, import-availability
metadata, author input bindings, manifest and zero release were read.

The complete actual qualified scalar public statement was read in
`library/Shao/OQ6/ActualPhysicalCompactCDF.lean` lines 1-37, including all
parameters, local values, integrability and both inequalities. The view also
included lines 38-53 incidentally; no producer proof was re-reviewed. The
whole-file source SHA256 is
`d264ae1c1f04cee3b43ec5e44829a5986574d70f30615f7bdeb1f1bfab2a14ae`,
identical to the complete unit170 qualified-evidence source binding. That
qualified-evidence record was read completely and reused. It records the old
independent complete review, native original object and all-owned recursive
axiom evidence. None is represented as new-unit kernel evidence.

The actual `truncationF` definition, nonnegativity, continuity and both joining
formulas were read in `library/Shao/Basic/TruncationBudget.lean` lines 1-48.
The existing product transport pattern was read in
`ActualUncenteredCompactCDF.lean` lines 236-297, especially 270-277; the genuine
integrability transport pattern was read in `QuadraticFullNoise.lean`
lines 202-221, especially 205-219. These are API/interface checks rather than
duplicate reviews of accepted old proofs. The toolchain pin is
`leanprover/lean4:v4.36.0-rc1`; no toolchain was invoked.

## Exact frozen interface and semantic fidelity

The reviewer independently recomputed source bytes and hashes and compared
the exact preamble+head prefix, the ` := by` separator and the complete closing
suffix. All match the preimplementation freeze. There is exactly one top-level
theorem, no global helper, no local instance value, and zero occurrences of
sorry/admit/new axiom/unsafe/native_decide. This static scan is not a recursive
axiom audit; that remains pending for the new original object.

All ten explicit parameters are retained: mu, g, measurability of g, its L2
membership, p, 2<p, p<=3, genuine p-moment integrability, cBudget and its
positivity. The carrier universe, measurable-space instance and probability
measure instance are unchanged. The inner universal quantifiers are exactly
n>=1 and z>=1, with no sufficiently-large-n condition. There is no centering,
unit-variance, standard-Borel, positive-beta, CDF, residual, coding, external
SZ, convergence or hidden callback premise.

All nine ordinary typed values and their captures were checked in both the
statement and proof:

| Value | Exact data and scope |
| --- | --- |
| beta : real | Integral of abs(g)^p under mu; captures mu,g,p and the carrier/measurable structure, before n,z. |
| c : real | rpow(min(1/2,cBudget)/2,1/p); captures only p,cBudget, before n,z. |
| P : Measure (Fin n -> Omega) | The literal finite product of mu, capturing mu,n and the measurable carrier. |
| N : real | sqrt(n), capturing only n. |
| xi : Fin n -> (Fin n -> Omega) -> real | g(omega_i)/N, with exactly the frozen normalization. |
| projectionTest : (Fin n -> Omega) -> Fin n -> real | F(z*xi_i), at the literal source threshold z. |
| delta : Fin n -> real | The genuine coordinate integral under P. |
| L : real | The finite sum of those delta values. |
| scalarBudget : real | Integral of F(z*(g/N)) under mu, at the same normalization and threshold. |

There are exactly 19 textual ordinary typed let occurrences: nine frozen
statement values, their nine exact proof repeats and the permitted local
`f : Omega -> real := fun o => F(z*(g o/N))`. All 19 types and right-hand
sides agree with the frozen inventory after whitespace normalization. f is
inside the existing n,z,N scope and captures only g,z,N and the carrier. No
unfrozen m,d,a,b, other value helper, additional parameter or local instance
was introduced. All other proof-local declarations are typed propositions or
their proofs. The deterministic results are in STATIC-COMPATIBILITY.json.

The five outer conclusions, eleven inner packet conclusions and three window
conclusions are all supplied, with the exact dependency order and implication
directions. In particular, beta=0 is an explicit alternative in the window
packet and is not silently excluded from the theorem.

The primary remains an UNCERTIFIED_REPAIR_CANDIDATE. Its original S1 normalized
model and other unproved/repaired obligations are not upgraded. This unit
extracts only S19's quantitative projection budget ingredient (primary
223-232), with xi=g_i/sqrt(n) from 238 and the original source F convention
from 294. The source F(t)=t^2*min(abs(t),1) is exactly abs(t)^3 on abs(t)<=1
and t^2 on abs(t)>1; both formulas agree at the boundary. No cutoff atom is
lost. The compact 1+z quantity from primary S5/311 remains distinct.
The generic positive cBudget is not identified with the external cSZ or
cSZ/2. Existing p54 repairs and named Shao-Zhou attribution remain unchanged.

## Complete proof review

**Lines 1-22 and 23-67.** Imports, universe, section and namespace establish
ordinary probability/product/real-power infrastructure. The exact frozen
statement uses genuine integrability before any budget interpretation. The
explicit constant's location guarantees one c for every n,z and every mu,g
at fixed p,cBudget. Its value contains neither beta nor a model-specific
constant. The conclusion does not encode its desired strict bounds as inputs.

**Lines 68-90: nonnegativity and the constant.** From p>2 the proof obtains
p>0 and p!=0. The p-moment integrand is pointwise nonnegative, so beta>=0;
hgp separately establishes its genuine integrability. Positivity of both
1/2 and cBudget gives min(1/2,cBudget)>0 and its half is positive. Thus c>0.
The reversed rpow-multiplication identity on this positive base and the
exact exponent identity (1/p)*p=1 prove
c^p=min(1/2,cBudget)/2. Since the minimum is positive, its half is strictly
smaller. No n or z has yet been introduced. Real powers, rather than natural
powers or an unchecked root heuristic, are used throughout.

**Lines 91-119: exact scalar API join.** Fix arbitrary n>=1,z>=1. The real
cast n is at least one and strictly positive. The source calls
`normalized_observation_truncation_budget_le_rpow_moment` with
`mu g hg hg2 p hp2.le hp3 hgp n hn (z-1) hy`. Every argument matches the
complete actual public statement. p>2 supplies its non-strict lower bound;
p<=3 and hgp are passed unchanged. z>=1 gives hy:0<=z-1. The exact identity
1+(z-1)=z rewrites the integrability assertion and both real-power estimates.
The old API's N=(n:real), q=sqrt(N), beta and L reduce to the new N=sqrt(n),
beta and n*scalarBudget. These names are distinct but their actual values
match. The resulting integrability and final rate have literal F(z*g/N),
not F((1+z)*g/N). No window premise is used for this rate.

**Lines 120-135: probability law, integrability and marginal equality.** The
product P has its canonical probability instance from the given probability
mu. f is measurable by continuity of F and measurable scalar multiplication
and division of g. For every i, `measurePreserving_eval` applies to the finite
product of probability measures on the actual type Fin n -> Omega, so its
marginal is exactly mu. `integrable_comp_of_integrable` transports the genuine
scalar integrability to f(omega_i), which is definitionally projectionTest.
`integral_map` is used with the coordinate map's a.e. measurability and f's
a.e. strong measurability; its direction is correctly reversed to write the
product integral as the mapped-law integral. The coordinate map's map_eq
then gives delta_i=scalarBudget. No assumed IID integrability, independence
callback, or equality of merely informal expectations is substituted here.
Arbitrary measurable Omega is allowed; no standard-Borel premise is needed.

**Lines 136-156: total identity, signs and unconditional rate.** The finite
sum of the same scalarBudget over Fin n is n*scalarBudget by its cardinality
and real nsmul. This gives L=n*delta_i for every i. Each integrand F is
nonnegative, hence every delta_i and their sum L are nonnegative. Since
n>=1, multiplying by delta_i>=0 proves delta_i<=n*delta_i=L without dividing
by L, delta_i or n. Replacing L by n*scalarBudget in the scalar estimate gives
the unconditional source-z rate
L<=beta*z^p/n^((p-2)/2). Its normalizing n is positive, including n=1.

**Lines 157-165: beta=0 before cancellation.** Substituting beta=0 into the
unconditional rate yields L<=0. Together with L>=0 this proves L=0, and
0<=delta_i<=L gives every delta_i=0. This branch is established before the
window proof contains any inverse or field cancellation. The integrals have
already been proved integrable; the proof does not obtain vanishing from the
totalized value of a nonintegrable Bochner integral. The rate denominator
cannot introduce a hidden zero case because n>=1.

**Lines 166-221: closed positive-beta window.** The disjunction is split
explicitly. In the beta=0 branch the established L=0 is at most c^p. In the
positive-beta branch n^((p-2)/2)>0 is established before division, and all
bases used in rpow multiplication are nonnegative. z>=1 implies z>=0 and
p>0, so raising the closed upper window to p preserves its inequality.
The beta power identity uses beta>0, p!=0 and
(-1/p)*p=-1, giving (beta^(-1/p))^p=beta^(-1). The n-power identity uses
n>0 and ((p-2)/(2*p))*p=(p-2)/2. Applying mul_rpow twice is legitimate
because c, beta^(-1/p), and n^((p-2)/(2*p)) are nonnegative. Therefore
z^p<=c^p*beta^(-1)*n^((p-2)/2). Multiplication by positive beta and division
by the positive n-power preserve order. The final field cancellation cites
both beta!=0 and n^((p-2)/2)!=0, producing exactly
beta*z^p/n^((p-2)/2)<=c^p. Composing with the unconditional rate gives
L<=c^p. No use of 0 raised to a negative exponent enters the zero branch.

**Lines 222-237: strict margins and complete packet.** The outer half-margin
gives c^p<1/2 and c^p<cBudget. Hence delta_i<=L<=c^p<1/2. Also
L<=c^p<cBudget. Since z>=1, z^2>=1; multiplying by cBudget>0 gives
cBudget<=cBudget*z^2, so L<cBudget*z^2. Strictness does not depend on a
strict upper window, and is retained when z equals that upper endpoint.
The final nested conjunction supplies every frozen conclusion in order.
Lines 238-241 close only the section and namespace.

## Boundary and adversarial checks

The beta-zero model is covered for every z>=1; it never relies on the
mathematically misleading total convention for 0^(-1/p). For beta>0, the
window may be empty at small n, but the theorem makes no nonemptiness claim;
all unconditional conclusions still hold. n=1 is retained. p=3 is retained
with the explicit third-moment integrability input. p=2 is correctly outside
the frozen S19 growing-window scope, although the reused scalar API also
supports it. There is no n=0, z<1, cBudget<=0 or p=0 obligation hidden inside
the domain. All root and denominator identities are justified on the stated
positive bases. Repeated values, atoms, degenerate g and arbitrary
measurable carriers do not affect the finite-product marginal argument.

No counterexample or critical proof gap was found under the frozen
assumptions. The result is an auxiliary quantitative source ingredient only.
It proves no CDF bound, external SZ theorem/application, coding witness,
weighted epsilon limit, projection-zero-event payment, general S11/S15/DC
claim, novelty claim or original OQ56/root closure.

## Static evidence and pending machine join

The reviewer independently checked all 23 author input hashes and byte
lengths; all match their recorded exact bindings. All four author manifest
payloads and all referenced frozen payloads match. The scalar curated source
matches unit170's qualified source exactly. These checks establish provenance
and interface compatibility, not new elaboration success.

A local deterministic manifest-check command initially formed one invalid
concatenated path and consequently performed zero manifest payload checks.
That affected metadata check alone was corrected; all eight payloads in the
two existing author manifests were then verified. The failure, its cause and
the corrected binding are retained in LOCAL-STATIC-CORRECTION.json. It had no
source, frozen-byte or external effect and was not a Lean failure.

`INPUT-BINDINGS.json` distinguishes complete reads, exact API ranges and
hash-only reused evidence. `STATIC-COMPATIBILITY.json` records the independent
19-let comparison and prefix/suffix/static token results. `qualification.json`
retains qualified=false and kernelPending=true. `MANIFEST.json` binds this
review bundle; `RELEASE.json` binds the manifest and records zero ongoing
writers, heavy checks, in-flight or uncertain external operations.

After an exact-source native success and same-FIRST-original-object
all-actual TYPE/VALUE/transitive-AX receipt, this same independent reviewer may
join the new machine evidence and check actual generated interfaces and any
newly exposed risk. An unchanged proof does not require an automatic second
complete proof review. Any actual source change invalidates only the affected
review evidence and must be identified by exact byte provenance.
