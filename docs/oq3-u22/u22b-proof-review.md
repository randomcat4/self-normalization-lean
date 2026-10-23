# U22b independent complete review

## Immutable blind statement translation and acceptance prefix

Review role: fresh independent mathematical reviewer; implementation author is a different context.
Model/effort prescribed for this context: gpt-6.1-sol / xhigh; no child contexts.
Owned write surface: this report only. No implementation or evidence changes are authorized.
Method: math-theorem critical-gap verification, with project source-fidelity and axiom requirements.

This prefix was written after reading the entire actual-types artifact and before reading the
frozen scope, source implementation, author explanation, or build/audit records. The actual-types
artifact itself includes axiom summaries; these summaries are not yet independently validated.
Actual-types input SHA256: 47556e5fd5e97643398bdc2e447dff38aeb1d0ac9f45e6aabe4c0804ff07afa9.

Let mu be a measure on the real line equipped with the IsProbabilityMeasure instance.
Let k be any natural number and theta be any point in the topological interior of
bivariateMGFDomain mu (fun x => (x, x^2)), viewed in the real product space.
The actual definition of this named domain must be inspected later; its name is not evidence.
There are no other explicit caller hypotheses in the three elaborated declaration types.

Private declaration 1, open_domain_weighted_integrable, claims that
x |-> x^k exp(theta_1 x + theta_2 x^2) is mu-integrable for every such k and theta.
This is signed polynomial weighting: odd powers are not replaced by absolute powers.
Private declaration 2, open_domain_abs_weighted_integrable, claims that
x |-> |x|^k exp(theta_1 x + theta_2 x^2) is mu-integrable under the same hypotheses.
These private claims are part of the proof surface and require substantive review.

The public declaration is open_domain_weighted_moment_hasFDerivAt.
Define the total function I_n(p) = integral x, x^n exp(p_1 x + p_2 x^2) dmu
using Lean's integral on every p in R^2, including points outside the integrability domain.
Its first conclusion repeats integrability of the k-th weighted integrand at theta.
Its second conclusion is HasFDerivAt (I_k) L theta, where
L = I_(k+1)(theta) * pr0 + I_(k+2)(theta) * pr1,
pr0 and pr1 being the continuous real-linear coordinate projections R^2 -> R.
Consequently L(h_1,h_2) = I_(k+1)(theta) h_1 + I_(k+2)(theta) h_2.
The asserted derivative is an ambient, full real Frechet derivative at theta, with a
remainder little-o of the product-space norm. It is not merely a directional or
coordinate derivative, and is not a derivative only within the domain.

Blind acceptance conditions, to be checked against definitions, source, and scope:
1. The named domain must be the actual exponential integrability domain for (x,x^2).
2. The conclusion must apply to an arbitrary real probability measure and every k,
   without bounded support, fixed finite moments, or an extra sign condition on theta.
3. The proof must derive any needed local integrability and common domination from
   the interior-domain hypothesis; callers may not supply domination or the derivative.
4. A common neighborhood must support the analytic argument in every product direction;
   separately proved coordinate limits alone cannot establish this public conclusion.
5. The integrand derivative must be the true continuous linear map, its Bochner integral
   must be justified, and that integral must be identified with the displayed L.
6. Open-neighborhood choices, positive radii, shifted endpoints and all natural powers,
   including k=0, must satisfy every cited theorem's actual assumptions.
7. Actual declarations, private proofs, imports, source-to-statement meaning, and
   transitive axioms must be fully covered by source-hash-bound evidence.
8. The result is a local differentiation lemma. Its type alone does not prove a public
   B theorem, a local inverse, a Legendre identification, or the OQ3 root result.

No correctness vote is made in this prefix. No other review's vote will count as proof.
The exact byte prefix ending with the next marker is immutable; its byte count, line
count and SHA256 are computed immediately after this write and recorded in the continuation.
END IMMUTABLE BLIND PREFIX

## Prefix binding and review sequence

Immutable prefix: lines 1-60 inclusive, 4206 UTF-8 bytes, SHA256
ebf91bdae661568f11260befa1d701093970f1bc3af2518e6663e380cc0273c3.
The binding was computed immediately after prefix creation, before source/scope reads.
I then read the entire frozen scope and entire 161-line U22b source, the entire 165-line
U22a source and all its actual declaration types, the literal domain definition, relevant
original R2/root-contract text, and pinned Mathlib API statements and proof mechanisms.
Before opening author build/audit evidence, my independent mathematical finding is that
the U22b proof establishes precisely the elaborated public conclusion. Detailed grounds
follow below; mechanical acceptance still requires binding the existing receipts.

## Verdict

STATUS: CORRECT.

The exact U22b source reviewed here proves the frozen module statement, including both
private integrability lemmas and the full ambient real Frechet derivative for every
natural weighted moment of an arbitrary real probability measure at every interior
point of the actual quadratic exponential integrability domain. No critical gap,
assumption substitution, or source-to-statement mismatch was found. This is module
acceptance, with the existing source-bound server check reused, not a new root closure.

## Complete mathematical and semantic review

1. Exact statement and domain (U22b lines 9-13, 22-26, 31-40).
The full elaborated types match the entire frozen declaration in the 31-line scope,
SHA256 f8e7a4aced349c8d9f1a03810cfef98974e23a1415f9eea1a86f482586708e85.
Shao.Probability.bivariateMGFDomain is literally the set of parameters at which the
exponential integrand is Integrable (BivariateLegendre.lean lines 20-22), not the set
where a totalized numerical integral happens to be finite. With W(x)=(x,x^2), its
integrand is exactly exp(theta_1*x+theta_2*x^2). The local curated source and the actual
v43 server source both have SHA256
d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58.
The only public caller assumptions are IsProbabilityMeasure mu and theta in this
interior, in addition to arbitrary k. There is no hidden boundedness, centering,
nondegeneracy, spectral condition, fixed sign of theta_2, or supplied derivative.

2. Direct producer actually consumed (U22b lines 14-20).
I read all 165 lines and all elaborated types of QuadraticTiltCumulants.lean, source
SHA256 ea105db471a073ac5eca67b4f94ff986766fd3fe3685790fb4859497da49289a.
The projection h.2.2.2 (1,0), followed by .2.2.1 k, selects the all-natural-powers
Integrable conclusion for F(x)=1*x+0*x^2=x under the very same tilted measure.
It selects neither the directional derivative nor a Hessian assumption. The exact
U22a mathematical path is its tilt integrability equivalence (lines 28-43), continuous
parameter-line interior argument (54-67), and the Mathlib all-powers theorem used at
157. Along a continuous line theta+t*d, the interior hypothesis gives a neighborhood
of 0 in the true shifted exponential domain. integrable_tilted_iff identifies this
with the exponential integrability set for F under nu. Thus 0 is interior there;
Mathlib integrable_pow_of_mem_interior_integrableExpSet yields all powers. For d=(1,0)
this really is every power of x. No inference from mere directional differentiability
to a parameter derivative occurs anywhere in this use of U22a.

3. Change of measure and first private theorem (U22b lines 16-20).
The exponential at theta is integrable by interior_subset htheta and the literal
domain definition. The pinned integrable_tilted_iff (Tilted.lean 293-312) states
Integrable g (mu.tilted f) iff Integrable (exp(f)*g) mu, under exactly this exponential
integrability hypothesis. Its proof accounts for the normalizing integral and its
nonzero value; the probability hypothesis supplies a nonzero original measure.
Applying its forward implication to g(x)=x^k gives the required signed weighted
integrability, with the final scalar/multiplication reordering justified by real
commutativity. No normalizing factor was dropped from an integral equality: this
step transfers integrability only, for which a finite nonzero constant is harmless.

4. Second private theorem (U22b lines 22-29).
Taking the norm of the signed integrable function is valid even for odd k.
The pointwise identity is |x^k exp(q(x))|=|x|^k exp(q(x)), because exp(q(x))>0.
abs_mul, abs_pow and abs_of_pos supply precisely this identity. This proves genuine
absolute-weighted integrability and is not an assumption about moments of mu itself.
The proof works at k=0, including x=0 under Lean's ordinary natural-power convention.

5. Interior shift (U22b lines 41-61).
The local I and the two coordinate projections duplicate the public lets exactly.
The initial conjunction component is the first private theorem. The continuous map
s |-> (theta_1,theta_2+s) tends to theta at 0. Since the interior is open and contains
theta, its preimage contains a real metric ball of some positive radius r. Choosing
delta=r/2 proves delta>0 and dist(delta,0)<r, so thetaPlus=(theta_1,theta_2+delta)
remains in the interior, not merely in its closure. eps=delta/4 is strictly positive.
There is no assumption that a globally positive quadratic coefficient is integrable;
only the arbitrarily small permitted upward shift is used.

6. One common parameter neighborhood (U22b lines 62-66).
S is the product of the two open intervals (theta_i-eps,theta_i+eps). Openness and
strict positivity of eps make S a neighborhood of theta in the ambient product
topology. This neighborhood is chosen before x, so it is common to all sample values
and all directions. Open endpoints are sufficient; no boundary parameter is invoked.

7. Exponential domination (U22b lines 67-91).
For t in S, |t_1-theta_1|<=eps and t_2-theta_2<=eps. Since x^2>=0,
(t_1-theta_1)*x+(t_2-theta_2)*x^2 <= eps*|x|+eps*x^2.
The inequality 2|x|<=1+x^2, obtained from (|x|-1)^2>=0, bounds the right side by
eps/2+(3eps/2)*x^2. As 3eps/2<=delta, this is at most eps/2+delta*x^2.
Adding the original exponent and applying monotonicity and additivity of exp gives
exp(t_1*x+t_2*x^2) <= exp(eps/2)*exp(thetaPlus_1*x+thetaPlus_2*x^2).
Every multiplication uses nonnegative |x| or x^2, so the argument covers either sign
of x and of the linear parameter displacement. The unused lower bound on t_2 is
harmless. The reserve delta-3eps/2 is positive in fact; only nonnegativity is needed.

8. Actual local integrals (U22b lines 67-103, related semantic check).
The same inequality multiplied by |x|^k gives an integrable bound throughout S,
because the private absolute-weighted lemma applies at thetaPlus for every k.
Therefore these nearby I_k values are true integrals; Lean's zero convention outside
Integrable is not being used to fabricate differentiability. This is also ensured by
the hypotheses of the library differentiation theorem. The proof does not require
the entire global domain to be open; it only works at the stated interior points.

9. Candidate operator and common bound (U22b lines 92-103).
F(t,x)=x^k exp(t_1*x+t_2*x^2). F'(t,x) is the sum of its two real weighted scalars
multiplying pr0 and pr1. B(x) is exp(eps/2) times the sum of
|x|^(k+1) exp(thetaPlus dot W(x))*||pr0|| and
|x|^(k+2) exp(thetaPlus dot W(x))*||pr1||.
The two absolute-weighted integrals at the same thetaPlus are finite; multiplication
by the finite projection norms, addition and constant multiplication preserve
Integrable. This constructs hB without an extra input, and B is nonnegative.
Leaving the actual operator norms in B avoids any unproved norm normalization.

10. Full operator norm domination (U22b lines 104-125).
For every x and every t in S, the scalar coefficient norm of order j is bounded by
e^{eps/2}|x|^j exp(thetaPlus dot W(x)). The triangle inequality in the space of
continuous linear maps and norm_smul then give ||F'(t,x)||<=B(x).
The factors ||pr_i|| are nonnegative, so multiplying the scalar inequalities preserves
their directions. The all-points bound is strengthened to an almost-everywhere bound
only by Eventually.of_forall. It is one bound for the complete linear operator,
not separate scalar bounds along selected directions.

11. Genuine pointwise Frechet differential (U22b lines 126-142).
For fixed x, the affine-linear exponent has ambient HasFDerivAt with continuous
linear map x*pr0+x^2*pr1. The proof combines the actual projection derivatives,
multiplies by constants and applies the exponential chain rule and the constant
x^k multiplier. ContinuousLinearMap.ext then verifies equality on an arbitrary
product vector v: x^k exp(q)*(x*v_1+x^2*v_2) equals
x^(k+1)exp(q)*v_1+x^(k+2)exp(q)*v_2. pow_add and ring prove this for all natural k.
This is already a full operator identity. It never infers Frechet differentiability
from existence of coordinate or directional derivatives.

12. Measurability and differentiation theorem (U22b lines 143-151).
For each parameter t, F(t,.) is continuous in x, hence AEStronglyMeasurable mu.
The map x |-> F'(theta,x) into the real continuous-linear-map space is likewise
continuous and strongly measurable; no scalar-only measurability surrogate is used.
I inspected the exact pinned statement and proof of
hasFDerivAt_integral_of_dominated_of_fderiv_le (ParametricIntegral.lean 206-228).
Its arguments, in order, are the common neighborhood, eventual measurability of F,
base Integrable F(theta,.), strong measurability of F'(theta,.), common a.e. operator
norm bound on S, Integrable B, and pointwise HasFDerivAt on S for a.e. x.
U22b supplies all seven in precisely these types. The library proof shrinks to a
ball in the ambient normed parameter space, obtains a Lipschitz estimate from the
bounded full derivative on this convex ball, and applies dominated differentiation.
Thus the result is the true ambient HasFDerivAt of t |-> integral F(t,x) dmu.
The usual product norm is a norm on R^2; equivalence with its Euclidean norm preserves
the Frechet conclusion. No directional-to-Frechet shortcut or caller domination is
hidden in this invocation.

13. Bochner integral and displayed coefficients (U22b lines 152-158).
The first private lemma at theta supplies Integrable of both scalar weights of
orders k+1 and k+2. Integrable.smul_const gives integrability of each corresponding
continuous-linear-map-valued summand. These maps take values in a Banach space, so
the Bochner integral is well formed. integral_add and integral_smul_const identify
integral F'(theta,x) dmu with I_(k+1)(theta)*pr0+I_(k+2)(theta)*pr1.
The two component integrals are genuine, not undefined integrals silently set to 0.
Rewriting the full derivative theorem by this CLM equality gives exactly the public
conclusion. The final namespace/section closures at 159-161 add no declarations.

14. Quantifiers and edge cases (entire proof).
The measure and parameter are never replaced, and k remains arbitrary. Neither the
chosen r, delta nor eps depends on x. Dirac or otherwise degenerate probability laws
are allowed; no covariance inverse or positive variance is used. k=0, odd powers,
x=0 and negative x are covered by the explicit identities and inequalities above.
If the true domain has empty interior the theorem has no admissible theta, as its
type explicitly says. At a boundary point no unsupported derivative claim is made.
There is no independence, coupling, selector, finite enumeration or numerical step.

15. Original source scope and attribution.
I read original R2 report.md lines 36-114 in full, including its literal W, K and
P_theta definitions at 38-45, the finite-open-neighborhood and actual covariance
conditions at 47-60, and standardized-family discussion at 83-99. Its bytes hash to
572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55.
I also read root-contract sections 2 and 4: lines 24-42 require the same fixed law,
true domain, genuine log partition and Hessian, while 64-72 retain the full root-B
hypotheses and probability/localization obligations. U22b faithfully supplies a
local unnormalized weighted-integral differential needed for that analytic bridge.
It does not itself establish the log-partition gradient/Hessian, uniform higher
moments over a compact parameter family, a mean inverse, or the expansion engine.
Its broader arbitrary-probability input is a valid helper scope, not a replacement
of the source's additional root hypotheses. The proof uses established Mathlib
analysis and measure-change results; no novelty or historical-first claim is made.

## Existing mechanical evidence and exact binding

16. Source/scope/artifact binding.
The entire reviewed local source is 161 lines / 8930 bytes, SHA256
f28ea2e9812d5c7702c75adf096e4fbbce82e4d2464da6cda764d2349e8c6f74.
Read-only server hashing confirmed the identical active-worktree source and preserved
run source-02.lean, and confirmed the exact U22a source hash given above.
The preserved server scope.md matches the local frozen scope hash. The entire actual
types file is 19 lines / 1481 bytes, SHA256
47556e5fd5e97643398bdc2e447dff38aeb1d0ac9f45e6aabe4c0804ff07afa9.
It matches the server actual-types.txt and the three printed types in audit.log.
Receipt SHA256: 53c45a4afb39a0128ba692ff1f482917861b3264882539339fe4a89899f605eb.
The receipt's historical AUTHOR_PASS_PENDING_FRESH_FULL_PROOF_AND_U22A_ACCEPTANCE flag
predates this review; this report adds the independent U22b proof decision without
rewriting the historical author evidence or making an integration claim.

17. Complete successful server compilation, failure preservation and warnings.
I inspected both preserved logs and verified their actual server hashes. Attempt 1
was a full failed 153-line source, SHA256
a33aa0a4556720339570cc70e0de314907a76d43a79e8fa233055167ce2de9f5;
its 4572-byte failure log hash is
99b65966287f269a05e6a8f7fb03a30da0b72dee885b5696715f6379993488a2.
It records a norm simplification mismatch and an unresolved CLM equality. It remains
preserved rather than being relabeled as a success. Attempt 2 is the unchanged exact
161-line source reviewed here: exit 0, 6.480426523834467 seconds. Its 812-byte log hash
is 0cb69b0f5e7e1c8c75546083c35e86cf9bbdd07c2189d2291baccfe5ad7e9237.
The four surviving warnings are two pairs of style hints at source lines 129-130
about unnecessary <;>; there are no errors or proof placeholders in this success.
Build history hash: 51f6cfe0f77919b0d92b1421db0975bd21d19ace191ad4e21096ea07edf91195.
The current output olean is 692608 bytes, SHA256
7069680b42bf0b5f9060bc9b311fba9bd280c50238958f83090cac2fe39d2f67;
its server timestamp is the same 2026-10-23 05:15:33.229465214 UTC as build-02.log.
This timestamp is a supporting provenance observation, not a substitute for the
source/log/type bindings. I performed no new compilation and no repeated gate.

18. Actual ownership, private/generated coverage, transitive axioms.
I read all 44 lines of u22b-Audit.lean, SHA256
250eb6954404fadfc1d073e452a6a7707a8cf78242dfc3683c01d8f203b9248a.
It first verifies the frozen public theorem exists, then iterates every environment
constant and filters by env.getModuleIdxFor? == Shao.OQ3.OpenDomainWeightedMoments.
This is actual module ownership, so private names are covered despite their prefix.
It rejects every module-owned axiom and calls Lean.collectAxioms transitively for
every owned constant, rejecting anything outside propext, Classical.choice,
Quot.sound. It prints the complete actual type and axiom set for each one.
The preserved 1595-byte audit.log has SHA256
fc9b9389322d09584005d86dea66cf39b9cb6f4179d94d98fe351326276e99c8.
It names exactly the two private lemmas and one public theorem, all of which I read
and reviewed above, and ends 0 frozen definitions / 1 frozen theorem / 3 all theorems /
3 all declarations / AXIOM_GATE PASS. Hence 2 private and 0 generated declarations
are accounted for, with no owner omitted by a namespace-only scan. Each of the three
has exactly the standard three transitive axioms; no sorryAx or new project axiom.
Audit exit code is 0, 5.162406058982015 seconds, with audit-record SHA256
806e46ede8fe64b508a6b59b0903329d67ff9b1009e1763cb365802fadf4bf85.
A direct scan of the reviewed source found none of sorry, admit, axiom, unsafe or
native_decide. The full source contains no proof-bypassing extension.

19. Pinned execution environment and resource boundary.
The actual server worktree lean-toolchain is leanprover/lean4:v4.36.0-rc1; the inspected
Mathlib checkout is 807d3836b165983210ee2ecf3cd28f239436949c. The existing successful
records use CPU14-17, native -M8192, -j4, autoImplicit=false, one heavy lane command.
All my own server actions were read-only and also restricted to CPU14-17; I did not
run Lean, alter a cache, touch version pins, or modify a source/object/view.
The audit environment hash is
bdf7ed10c086200b30a78874fc0bb338b496640b769ab9d2de4e2f82df3085dd.
It records reuse of accepted-source-view with the exact v43 accepted source tree
0c08fa33511931678c7187754b6bb2926358cafc and own new U22a/U22b objects. Targeted realpath
inspection confirms U22a and U22b resolve to lead-oq3 objects, while BivariateLegendre
resolves to the accepted integration-bearing-v43 object. This matches the documented
Lean package-root execution requirement; no assumption of an unavailable own-root
BivariateLegendre object was made. This review does not create a new wrapper or gate.

20. Independent decision, permitted reuse and exact remaining scope.
My mathematical decision was recorded before author build/audit evidence was read.
No other review's vote was used as a mathematical premise. The direct U22a all-moment
path was independently checked against its actual source and the pinned Mathlib
integrability APIs; separate acceptance of the full U22a module remains its own
source-bound evidence record. This report covers every declaration and every proof
line of the unchanged U22b module, and reuses its existing successful server kernel
and transitive-axiom receipt. No mathematical or mechanical evidence gap remains for
this exact module version. Root integration must retain these hashes and the exact
accepted dependency interfaces. Changes to the proof or its consumed dependencies
require review of the affected scope, not blind reuse of this report.

The public B theorem, full log-partition/actual-mean Hessian bridge, mean-map local
inverse, Legendre/global-rate consumers, Edgeworth/cell/Laplace and far-probability
steps, original D, and the OQ3 root group remain OPEN as applicable. This local module
acceptance does not upgrade any of them. No claim of optimality or novelty is made.

END COMPLETE U22B INDEPENDENT REVIEW: CORRECT FOR THE EXACT SOURCE HASH ABOVE.
