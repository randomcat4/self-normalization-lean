# U22M + U22N independent complete review

## Immutable blind type reading

This prefix was written after reading only `u22m-actual-types.txt` and `u22n-actual-types.txt`, before reading scope notes, implementation, producer proofs, or check evidence. It describes the exported types and makes no proof-validity finding. The inventories suppress the explicit types of the existential binders; the operations displayed identify L as the covariance linear equivalence and e as a partial invertible chart with source and target.

### M: open_domain_quadratic_tilt_local_rate_derivatives

For every real measure mu equipped with a probability-measure instance, and every theta in the interior of the actual bivariate MGF domain for x |-> (x, x^2), assume the determinant of the actual parabola covariance under the exponential tilt of mu by theta.1*x + theta.2*x^2 is nonzero. There are no further displayed hypotheses.

Define Omega as that interior; nu(p) as the actual exponential tilt by p; means(p) as the pair of actual integrals of x and x^2 under nu(p); K(p) as the real logarithm of the integral of exp(p.1*x + p.2*x^2) under mu; and D as the actual tilted covariance at theta. Write pr0 and pr1 for the first and second coordinate continuous linear projections. Its displayed covariance rows are row0 = D00*pr0 + D01*pr1 and row1 = D01*pr0 + D11*pr1, so the same off-diagonal coefficient is used in both rows. The map covector takes a vector u to the covector z |-> u.1*z.1 + u.2*z.2.

The conclusion existentially supplies L and e. L, coerced to a continuous linear map, equals exactly the product of those two covariance rows. e, coerced to a function, equals the actual means map on all arguments. theta lies in e.source; means(theta) lies in e.target; and e.source is contained in Omega. Define the real function J(z) = e.symm(z).1*z.1 + e.symm(z).2*z.2 - K(e.symm(z)). The claimed regularity is C-infinity at the single point means(theta). The claimed derivative of J there is the covector theta.1*pr0 + theta.2*pr1. The actual derivative of the actual function z |-> fderiv R J z at that point is the continuous linear map covector composed with L.symm. Finally, for every z belonging to this same e.target, the true bivariate Legendre rate of mu for (x,x^2) equals J(z), with J(z) embedded into EReal.

All measure and theta quantifiers are universal; the chart and L are existential and the rate equality is universal over their target. No theta existence, nonempty global domain, global invertibility, global smoothness, or equality outside the chart target is asserted. A center in the target makes the target nonempty in each instantiated conclusion. Total-function values of e.symm outside the chart target are not given a rate interpretation. The exported derivative-of-fderiv assertion is a genuine derivative statement rather than a numeric identity for one Hessian value. The displayed inputs do not assume the derivatives, J, inverse chart, or Legendre equality that are concluded. The domain-membership and determinant conditions may fail for a particular probability measure; the theorem is conditional and does not establish those inputs. No positive-definiteness or rate-minimum claim is displayed. The listed axiom set is propext, Classical.choice, Quot.sound; that list is inventory data, not yet independently validated here.

### N: open_domain_quadratic_tilt_boundary_rate_derivatives

For every real probability measure mu, every theta in the same actual interior MGF domain, and a nonzero determinant of the same actual tilted covariance, universally quantify real level and a0. Assume level > 0 and a0 > 0. Assume the actual tilted mean pair at theta equals (a0, a0^2/level^2). Assume also theta.1 = -2*a0*theta.2/level^2. No upper bound on level, sign condition on theta.2, or second-derivative positivity appears in this type.

Define Omega, nu, means, K, D, the projections, and the two covariance rows exactly as in M. There exist L and e satisfying the same literal covariance-map identity, all-arguments means-map identity, center source and target membership, and source inclusion in Omega. With J defined from that same e and actual K, let gamma(a) = (a, a^2/level^2), f(a) = J(gamma(a)), v = (1, 2*a0/level^2), and Lambda1 = 2*theta.2/level^2 + (L.symm(v)).1 + (2*a0/level^2)*(L.symm(v)).2.

The conclusion says f is C-infinity at a0, f has derivative zero at a0, and the actual derivative function deriv(f) has derivative Lambda1 at a0. It also says eventually as real a tends to a0, the actual global bivariate EReal Legendre rate at (a,a^2/level^2) equals the finite real value f(a) embedded in EReal. The eventual quantifier supplies some neighborhood, without a global equality for all a. Lambda1 uses the inverse of the same actual covariance equivalence; its two covariance contributions equal the evaluation of L.symm(v) against v, with an additional curvature contribution 2*theta.2/level^2. The coordinate order is first moment, second moment throughout the displayed type.

All antecedents precede the existential chart and conclusions. The saddle equation is an explicit first-order relation between theta and the boundary tangent; it does not assume a derivative of f or any conclusion about Lambda1. Neither an already-known boundary rate nor a Hessian is an input. These are conditional statements: the type does not produce theta, a0, level, the center mean equation, or the saddle equation. Positive level excludes zero denominators, but no positivity of Lambda1 follows merely from its displayed definition. Zero first derivative and the asserted second derivative do not assert a local minimum, a strict minimum, or uniqueness. No Laplace asymptotic, probability bound, Edgeworth expansion, spectrum result, root-theorem closure, or attribution/novelty claim is contained in the type. The listed standard three axioms remain unvalidated inventory data at this stage.

### Blind circularity and scope assessment

On the displayed types alone, both results have substantive conclusions about the actual moment/tilt/covariance/rate objects and do not explicitly assume their own conclusions. Existential freedom is constrained by exact identities for L and e and by the formula for J. Proving these types still requires validating the actual chart, differentiating an identity on a neighborhood rather than at a single point, and connecting J to the global supremum defining the rate. M and N are local conditional analytic interfaces, not an existence or global-minimum theorem. Proof correctness and source fidelity remain unassessed in this prefix.

END IMMUTABLE BLIND PREFIX

## Blind-prefix receipt

Immutable prefix: 6640 UTF-8 bytes; SHA256 3ce3582b64ebf9e915d2f1d3689b53d967860baf1857473aeefed888296da2e2. All later material is appended after this receipt. The bytes from the initial title through the newline after END IMMUTABLE BLIND PREFIX are frozen.

## Independent findings

M: **CORRECT**. N: **CORRECT**. M-to-N batch interface: **CORRECT**. These verdicts apply to the exact frozen local analytic helper statements and source hashes below. There is no requested proof revision and no uncovered M/N proof line. No original B/D root, global minimizing saddle, positive Lambda1, Laplace expansion, or probability asymptotic is certified by this review.

This is a fresh independent source-semantic and proof review. The reviewer did not implement or alter either theorem and did not read prior proof-review reports as a substitute for checking a proof. The assignment named the risk areas; before the immutable prefix the only files opened were the two actual-TYPE inventories. Afterwards the complete frozen statements, all 258 local source lines, the same complete 258 actual server source lines, and all 520 lines of the C/D/E/L producer modules were read. Existing exact-source server checks were inspected and reused, without executing Lean, a build, or an axiom audit again.

## Source meaning and actual objects

R2 report lines 40-55 use W=(X,X^2), K=log E exp(theta dot W), the normalized actual tilt, m=grad K, and Delta=Hessian K; lines 278-284 require the dual gradient and inverse-covariance Hessian. Lines 299-314 use the curved-boundary coefficient in the saddle calculation. Root-contract sections 2 and 4 make the relevant boundary and coefficient explicit: q=a^2/x^2, m(theta0)=(a0,a0^2/x^2), s0=-2*a0*t0/x^2, and Lambda1=2*t0/x^2+(1,2*a0/x^2) Delta^(-1) (1,2*a0/x^2)^T. The historical root-contract status is not used to override current coordination acceptance states.

The correspondence is exact: mu=P, theta=(s0,t0), level=x, the first coordinate is the X mean and the second is the X^2 mean, and D is Delta for that same actual tilt. `parabolaCovariance` explicitly has entries Var(X), Cov(X,X^2), Cov(X,X^2), Var(X^2). Thus its identical off-diagonal entries are literal definitions, not an extra symmetry assumption or a matrix unrelated to the law. C supplies the finite second moments needed to identify these entries.

The baseline `bivariateMGFDomain` is the set of parameters for which exp(theta.1*X+theta.2*X^2) is integrable. `bivariateLogMGF` takes a parameter of that subtype. `bivariateLegendreRate` is an EReal supremum over the entire integrability-domain subtype, not over Omega or one chart. The baseline attained-bound lemma uses an upper bound for every such parameter and an actual attained member. Local/library and server versions of these definitions have matching hashes. Consequently the global-value conclusions of M and N have their ordinary full-domain Legendre meaning.

All uses of derivatives and log/normalization in the producer chain are at points of the true open domain Omega. Although Lean gives the displayed real expressions total values outside that set, no global-rate interpretation of those totalized values is used. In M, source inclusion in Omega and the chart inverse laws establish every new inverse parameter's domain membership. In N, the eventual chart-target membership keeps every certified boundary value in that scope.

The source's root B also retains level<1, theta.2<0, Lambda1>0, actual global saddle/localization, uniform covariance spectra, moments, WC with beta<2/5, and the explicit far-probability condition. M/N prove the particular calculus identities under weaker sufficient helper inputs; none of those original root obligations is silently removed or proved. The R2/RP Song and Laplace obligations are not replaced by an external-result axiom.

## Independently checked producer reasoning

C, `OpenDomainFrechetCumulants.lean`, all 190 lines: its private definitions are actual exponential weighted moments I_k, normalized moments I_k/I_0, their quotient-rule slopes, and the partition gradient. Lines 29-35 prove I_0>0 from true-domain membership. Lines 37-56 apply the already established actual weighted-moment derivative for k and 0, differentiate the reciprocal of the nonzero partition, and simplify the quotient derivative. Its two coefficients are E_tilt[X^(k+1)]-E_tilt[X^k]E_tilt[X] and E_tilt[X^(k+2)]-E_tilt[X^k]E_tilt[X^2]. No desired local-rate derivative is a hypothesis.

C lines 58-84 obtain the actual log-partition derivative and identify the normalized moments with actual integrals under `mu.tilted`. Lines 122-146 obtain the actual tilted probability instance and L2 facts, then use the variance/covariance integral formulas to identify D00, D01 and D11 with those normalized moments. Lines 147-175 identify the two moment-derivative rows with the literal D rows and the K gradient with the actual mean pair. Lines 176-187 additionally establish the derivative of actual fderiv K by a genuine eventual equality on the open integrability domain. M consumes C's actual K-gradient result at each inverse parameter; E consumes its actual mean derivative. These statements and their proofs do not assume an inverse chart or a conclusion of M/N.

D, `OpenDomainSmoothMean.lean`, all 103 lines: lines 14-39 induct over finite differentiability order for every actual weighted moment, using I_(j+1) and I_(j+2) as the continuous derivative coefficients on the open set; then `contDiffOn_infty` gives C-infinity on Omega. Lines 61-96 prove positivity of the actual partition, smoothness of its log and normalized moments, and equality of the actual tilted mean function with the pair of normalized moments. Lines 97-100 combine this actual smoothness with C's actual derivative for a strict mean derivative. In particular, smoothness is not supplied by a caller and K is not differentiated at an inadmissible parameter.

E, `OpenDomainMeanInverse.lean`, all 111 lines: lines 39-51 set A to the literal two-row covariance map and delta=D00*D11-D01^2, proving delta=det D and delta nonzero. Lines 52-78 construct the explicit cofactor inverse and verify both inverse identities algebraically using that nonzero determinant. Lines 79-89 package the same A into a continuous linear equivalence and use C's actual mean derivative. Lines 90-108 use D's actual C-infinity mean map and the inverse function theorem to produce a partial homeomorphism with exactly the actual means function, restrict its source to Omega, and prove the center's inverse C-infinity regularity and strict derivative L.symm. Its local inverse and the restricted chart's inverse are the same total function. Source restriction retains the center and ensures the parameters used later are in Omega. Neither an arbitrary equivalent matrix nor a formal inverse derivative is an input.

L, `OpenDomainLegendre.lean`, all 116 lines: the first theorem, lines 10-70, is the part M uses. For every p in the full true integrability domain it takes d=p-theta and F=d.1*X+d.2*X^2. The actual tilt identity gives integrability of exp F and E_tilt exp F=Z(p)/Z(theta); actual tilted first and second moments make F integrable. Jensen's exp inequality on the actual tilted probability measure gives E_tilt F <= log Z(p)-log Z(theta), since both partitions are strictly positive. Rearrangement gives the upper bound for every full-domain test p, with equality at theta. The baseline supremum/attainment theorem therefore proves the actual global EReal rate at the actual mean. This handles possible non-open boundary points p of the integrability domain as tests too.

L's second theorem, lines 72-116, was also read completely: it combines the compact actual mean chart with that same attained-rate theorem after using the actual inverse-mean identity. It introduces no separate dual-gradient or Hessian assumption and is not needed to infer M's calculus. No prior review verdict was used in place of the preceding reasoning.

## Complete M proof review

M lines 1-41 contain the exact frozen imports, namespace, binder list, definitions and conclusion. After normalizing CRLF versus LF only, this complete pre-proof text equals the Lean block in the frozen scope exactly. The actual exported TYPE has the same universal inputs and existential L/e conclusions. Lines 42-56 repeat the same actual definitions for the proof, without changing mu, tilt, means, covariance, projections or covector.

Lines 57-64 take L/e and all five structural conditions plus inverse regularity from E. Since e's function equals means and theta is in its source, `e.left_inv` yields g(m(theta))=theta for g=e.symm. This use of an inverse is valid at the center and does not assume a globally invertible mean map.

Lines 65-73 use D's K smoothness on the open true domain to obtain C-infinity at theta, rewrite the center inverse parameter to theta, and compose with the inverse's center smoothness. The coordinate products and K composition give exactly J(z)=g(z) dot z-K(g(z)) and its claimed center C-infinity regularity. No common C-infinity neighborhood is claimed at this step.

Lines 74-93 prove a separate gradient statement at an arbitrary target point z where g is differentiable. `e.map_target` and source inclusion yield g(z) in Omega; `e.right_inv` and the exact means-function identity yield m(g(z))=z. C's actual gradient of K is therefore the covector z at g(z). For every direction h, the product and chain rules give

    dJ_z[h] = (dg_z[h]).1*z.1 + g(z).1*h.1
             + (dg_z[h]).2*z.2 + g(z).2*h.2
             - (z.1*(dg_z[h]).1 + z.2*(dg_z[h]).2)
             = g(z).1*h.1 + g(z).2*h.2.

The cancellation is pointwise algebra of continuous linear maps. The `convert` first resolves equality of the total functions by function extensionality and reflexivity, then resolves equality of derivative maps by continuous-linear-map extensionality and `ring`. `covector(u)(h)=u.1*h.1+u.2*h.2`, by the actual `smulRight` definition, so there is no transpose or coefficient reversal. The temporary differentiability premise is internal to this helper and is supplied on the neighborhood used next.

Lines 94-97 specialize that helper to m(theta), use inverse differentiability from E, and rewrite g(m(theta))=theta. This proves the stated first derivative, not a supplied gradient identity.

Lines 98-106 lower the inverse's center C-infinity regularity to finite C1. The actual pinned `ContDiffAt.eventually` requires its order to be different from infinity; the proof uses order 1 and discharges precisely that requirement. It thereby gets differentiability of g at every point in some neighborhood. Intersecting with the open chart target gives the eventual identity `fderiv R J z = covector(g(z))`. This is the essential extra fact: the second derivative is not inferred from the single-point center gradient equality.

Lines 107-110 differentiate the right-hand side of that eventual identity using E's actual strict inverse derivative, converted to a Frechet derivative, and the continuous linear covector map. Eventual-equality congruence then gives the derivative of the actual fderiv J. Its value is H= covector composed with L.symm; for directions h,k,

    H(h)(k) = (L.symm h).1*k.1 + (L.symm h).2*k.2.

Since L is literally the actual covariance operator D, L.symm is its actual inverse. D has the symmetric covariance matrix from the actual law, so this is the usual inverse-covariance Hessian bilinear form, with the displayed coordinate order. This derivative concerns actual fderiv as a function into continuous linear maps.

Lines 111-123 assemble all conditions and prove the global value for every z in this same e.target. For each such z they use m(g(z))=z and g(z) in Omega, apply L's already proved full-domain Legendre attainment at g(z), and rewrite the mean to z. Thus the rate is finite and equals J throughout that target, with an EReal coercion. No locality restriction was slipped into the definition of the global supremum. Lines 124-126 are the closing blank/section/namespace lines and were read too.

M STATUS: CORRECT. Every premise of the consumed actual producer statements is supplied; the local differentiability, inverse, cancellation, second derivative and true global-rate conclusion all follow with the frozen quantifiers.

## Complete N proof review

N lines 1-47 contain the exact frozen declaration. After newline normalization only, the entire pre-proof text equals the scope's Lean block, including positive level/a0, the actual mean equation, saddle relation, all structural conclusions, Lambda1 formula, actual derivative-of-deriv statement and eventual global-rate equality. Lines 48-77 preserve the same actual definitions, obtain L/e/J from M in one elimination, set gamma(a)=(a,a^2/level^2) and V(a)=(1,2*a/level^2), and rewrite gamma(a0)=m(theta) using the exact given mean equation.

Lines 78-84 prove, for all a, gamma'(a)=V(a), and at a0, V'(a0)=w=(0,2/level^2). The first coordinate's derivative is exactly 1 and the second coordinate corresponds to the second moment; its curvature factor is exactly 2/level^2. These are actual derivative statements for the polynomial/divided-by-constant functions. Lines 85-88 prove gamma smooth and compose it with J's center smoothness to prove f=J composed with gamma is C-infinity at a0.

Lines 89-100 compute the center derivative. With v=V(a0), the actual J derivative evaluates as theta.1+theta.2*(2*a0/level^2); rewriting theta.1=-2*a0*theta.2/level^2 and using real ring algebra yields zero. The chain rule at gamma(a0)=m(theta) gives the claimed `HasDerivAt f 0 a0`. This is a derived stationarity assertion, not a caller-supplied derivative.

Lines 101-107 compose M's actual derivative of fderiv J with gamma to obtain the derivative of a |-> fderiv J(gamma(a)) as the continuous linear functional H(v). Lines 108-116 apply the derivative rule for evaluating a varying continuous linear map at a varying vector. The actual pinned rule is c'(u(a0))+c(a0)(u'), so both terms are present:

    (H(v))(v) + dJ_(m(theta))[w]
      = (L.symm v).1*1 + (L.symm v).2*(2*a0/level^2)
        + theta.1*0 + theta.2*(2/level^2)
      = 2*theta.2/level^2 + (L.symm v).1
        + (2*a0/level^2)*(L.symm v).2
      = Lambda1.

The first term is precisely the source tangent quadratic form v^T D^(-1) v. The second is the curvature term 2*theta.2/level^2 with a plus sign. No theta.1 curvature, missing factor of two, swapped vector coordinate, or missing application derivative occurs. This agrees with the source Lambda1 under level=x and theta.2=t0.

Lines 117-125 address the difference between a formula at one point and the actual derivative function near the point. They lower J's center C-infinity regularity to finite C1, use the valid finite-order eventual theorem to get differentiability near m(theta), and pull that neighborhood back by gamma's continuity and exact center equality. At each such a the genuine chain rule proves

    deriv f a = (fderiv R J (gamma a)) (V a).

Line 126 transfers the derivative proved for the right-hand side through this eventual equality. The result is exactly `HasDerivAt (deriv f) Lambda1 a0`; it is not merely a formal second-order chain expression. Lines 127-129 assemble the conclusions and pull back the open target neighborhood through the same gamma limit. M's actual global Legendre equality then yields the required eventual EReal rate equality. Lines 130-132 close the source and were read too.

N STATUS: CORRECT. The unused-premise hints for hlevel and ha0 are harmless: the frozen positive geometric assumptions remain in the exported type, while this constant-denominator calculus proof happens to be valid more broadly. Their non-use neither changes the statement nor supplies any missing root hypothesis. No positivity of Lambda1 is inferred.

## Batch interaction, scope and coverage

Batch STATUS: CORRECT. N consumes the L/e/J exported by one application of the exact reviewed M theorem, so its inverse covariance and the chart defining f belong to the same actual tilt and center. M in turn uses E's same actual covariance equivalence, C/D's same actual K and means, and L's same actual global transform. There is no cycle: C/D establish analytic inputs, E inverts means, L proves global attainment independently of M/N, M differentiates the local dual, and N restricts that actual local dual to the boundary. Imported compact-chart results in L do not presuppose M/N.

Coverage is complete: M 1-41 declaration / 42-56 local definitions / 57-73 inverse and smoothness / 74-93 arbitrary-target gradient / 94-110 center gradient and actual Hessian / 111-123 assembly and global value / 124-126 closing lines; N 1-47 declaration / 48-77 common objects / 78-88 curve calculus and smoothness / 89-100 stationarity / 101-116 Hessian and curvature / 117-126 actual derivative function / 127-129 assembly and eventual rate / 130-132 closing lines. These disjoint ranges cover all 126+132=258 source lines. The supporting C 1-190, D 1-103, E 1-111 and L 1-116 were independently read in full; BivariateLegendre 1-114 and the relevant RegularCovariance 1-45, including its actual definition, were read as baseline semantics.

The results eliminate actual local dual-gradient/Hessian and boundary-Lambda1 derivative obligations. They do not establish a global inverse, existence or uniqueness of the source minimizing saddle, a positive Lambda1, uniform spectra, compact-family derivative bounds, cell reconstruction, a Laplace estimate, far-probability bounds, or the original B/D roots. The source's unbounded-domain restrictions and fixed-level scope remain intact. These are standard calculus/convex-duality formalization helpers; this review makes no mathematical novelty, priority, or conference-strength claim.

## Mechanical evidence appendix: exact source bindings

Everything in this appendix was inspected read-only. The mathematical findings above were reached by reading the proofs, not by treating successful elaboration or prior-review status labels as a semantic verdict. All hashes are SHA256 of actual bytes. Line counts use actual split lines; scopes use LF while local proof copies use CRLF, explaining why declaration comparison needs newline normalization. Hashes always bind the unnormalized bytes.

| Artifact | Bytes | Lines | SHA256 |
|---|---:|---:|---|
| M frozen scope, ninety-fourth-unit-scope.md | 5022 | 57 | 4926ae5a30cf764994e70523d870429191d9ae3ba1569ccb788e50978146ca68 |
| M local source and actual server OpenDomainRateDerivatives.lean | 6625 | 126 | 14c9e16d43864d1b40b94bc5d0ca8e1106ba2f7fece13a118348f247c80c294e |
| M actual-TYPE inventory | 1723 | 26 | 26e13400761b9ddad7d1d685a3310fe301727558bfcc7013cdb880fe7c0b195e |
| M receipt | 4471 | 112 | b9ba39f5529aa95eb4c9563c700816d75885123a6c0505c50ddf2689f534dd8b |
| N frozen scope, ninety-fifth-unit-scope.md | 4870 | 61 | 3c3d49bf609867225d3d9ba659ba81ba68ce14628125eb79f97837325790341e |
| N local source and actual server OpenDomainBoundaryRate.lean | 7363 | 132 | 4978d909d243cb7547287dd9b1d384f795599c8f3ff9868bea42df24e453dac6 |
| N actual-TYPE inventory | 2511 | 38 | 4491f7f76be0cc649f857cf9d5a7d78d4a3a3eb5cfb3c46c6eddab6e586b4769 |
| N receipt | 3398 | 85 | 3b1ada71da203e1ddae09da1e520162459c919df34f6367197a611512390b0cc |
| C actual server OpenDomainFrechetCumulants.lean | 9834 | 190 | b5d48b414adbc80f7db44f37cc2b2b423d44263c54e8547a5a356768a116df72 |
| D actual server OpenDomainSmoothMean.lean | 5312 | 103 | d6457d90d9d0e1ccdae6d6ea041d8caef65f70b3cb6d5fa8baea1867a5bffb8e |
| E actual server OpenDomainMeanInverse.lean | 5367 | 111 | d99022fad2a59a6e90782405113d9ec22ca0d3d56d8ea54af5a90500daa8fa53 |
| L local source and actual server OpenDomainLegendre.lean | 6829 | 116 | 941c08552f300af2c85e2df7f55399b69c4468bca467fe88b8a303a6a3c74bc3 |
| R2 original report | 20102 | 523 | 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55 |
| Root contract | 9473 | 82 | a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a |
| Baseline BivariateLegendre.lean, matching library/server | 4608 | 114 | d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58 |
| Baseline RegularCovariance.lean, matching library/server | 15931 | 305 | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |

For the baseline covariance file only the relevant first 45 lines were read; its full-file hash establishes version identity, not a claim of re-reviewing its other theorems. Producer source hashes match the supplied frozen dependency hashes. The actual M/N server files were read in full and rehashed unchanged before finalizing this report. Their run snapshots source-02.lean and source-01.lean respectively are identical to the reviewed bytes.

## Mechanical evidence appendix: history and kernel receipts

M and N run directories are `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22m-20261023` and `.../u22n-20261023`. The full local build histories, receipts, audit records and environment manifests were read. The corresponding remote histories, records, manifests, Audit.lean, actual-types, scope and exact-source snapshot hashes agree with the local artifacts. The complete actual remote logs listed below were read, including the failed attempt.

| Existing server command record | Result / seconds | Exact-source SHA256 | Exact log SHA256 / bytes / lines |
|---|---|---|---|
| M complete attempt 01 | exit 1 / 5.893297674 | 58ce552323b4b6c817b9c23f2a78825aa368e632b80a1f135896f0cf53cf6d1d | b553c326396ba45318e96e0aba9a29af5ac113a1bf6fbe9d7e9b3af9e2e593ad / 4658 / 84 |
| M complete attempt 02, first success | exit 0 / 6.144972080 | 14c9e16d43864d1b40b94bc5d0ca8e1106ba2f7fece13a118348f247c80c294e | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 / 133 / 2 |
| M first all-owner transitive audit | exit 0 / 5.769427150 | 14c9e16d43864d1b40b94bc5d0ca8e1106ba2f7fece13a118348f247c80c294e | 90bad113678d18d43674f1b412139cb2816ad12502dac2eef0f81ac04fce2964 / 1970 / 33 |
| N complete attempt 01, first success | exit 0 / 6.153650083 | 4978d909d243cb7547287dd9b1d384f795599c8f3ff9868bea42df24e453dac6 | 4bc7626295ebc4f1fbc3ff0bf4ac49f55305b636727317084eac355023cffa55 / 831 / 14 |
| N first all-owner transitive audit | exit 0 / 5.900775163 | 4978d909d243cb7547287dd9b1d384f795599c8f3ff9868bea42df24e453dac6 | 3798c2bf25e1395037976b0a5e912a574aee938eca2d246995894334b8593022 / 2758 / 45 |

M's first complete attempt failed at old line 88 because `ContinuousLinearMap.ext` was applied while the conversion goal was equality of total functions. The full failure log and preserved 124-line source-01 were inspected; the remote unified diff to source-02 only adds the separate function-extensionality/reflexivity branch and nests the existing map-extensionality branch. It does not alter a statement, assumption, mathematical cancellation or proof setting. The successful M log contains only the known two-line thin-overlay Lake warning. N's successful log contains that same warning and the two unused hlevel/ha0 hints, not a suppressed proof error or removed premise. Failed records remain preserved.

Both full Audit.lean files were read: M 1901 bytes/44 lines/hash 61969c11f53130ec0c4d20540c8f2f4688dab195fb680e88547123a58b9afe84; N 1898 bytes/44 lines/hash f935797ac535e096fc2aefdbba0a00888ef3aebffbecafd206af05ceb507fbef. They import the actual compiled target module, require each frozen target to exist as a theorem, enumerate `env.constants.toList`, identify true module ownership using `getModuleIdxFor?` and the module table, reject owner axioms, and call recursive `Lean.collectAxioms` for every actual owner. The enumeration is not a namespace-prefix guess or an audit of only a preselected public-name list.

Both actual audit logs report frozen definitions 0, frozen theorems 1, all theorems 1, all declarations 1, and AXIOM_GATE PASS. Thus each actual module has exactly its one public theorem and no additional private/generated theorem or definition left outside the owner sweep. Every owner's full transitive axiom set is exactly `[propext, Classical.choice, Quot.sound]`; sorryAx and any new non-whitelisted axiom would fail this gate. No sorry/admit/new axiom/unsafe/native_decide/implemented_by occurs in either completely read target source; neither target changes proof options. The audit changes only pretty-print settings, not kernel checking.

| Other local artifacts, matching remote versions | Bytes / lines | SHA256 |
|---|---|---|
| M build-history.json | 1566 / 50 | fc929923831b8e1f0cc475dc935b886022748c3cd86f55829e498a4dd2e805a8 |
| N build-history.json | 785 / 26 | 14c4415aa1aff4bf13b9e46ec0a0b4838f92c28ea9def650c4baa756fb5eae0e |
| M audit-record.json | 496 / 18 | 0e77fce4b012c93f3f174e7eba347c4c9dd541a7e57bb589f6521437754dbdd4 |
| N audit-record.json | 498 / 18 | 12e789db96c44b9d9b335fc1b292ccc00e2078ecfee0dc373e9aa4b4878e545c |
| M audit-environment.json | 494 / 9 | 5bc30efcca632dcdb3148ad18b3cc2cd710aab6d2887ab654f66669adeb8edb0 |
| N audit-environment.json | 491 / 9 | d3d36d0bf08655f17ef169bf65c2d42b5dd0f99fcd6f7ba37e7f3b0127826b82 |

## Mechanical evidence appendix: environment and review boundaries

The actual server worktree is `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`, branch `feat/oq3-open-domain-standardization`, HEAD/parent `803d8d0fbea3c2a55b8167f7c1ff4902510f1b8e`. The actual read project pin is `leanprover/lean4:v4.36.0-rc1`; lakefile.toml sets `autoImplicit=false` and mathlib revision `807d3836b165983210ee2ecf3cd28f239436949c`. Existing execution records consistently specify CPU14-17, Lean native memory 8192 MiB, jobs 4 and autoImplicit false. This reviewer did not launch any Lean process, including a version/smoke probe, under the explicit reuse/server-only policy.

The actual `.lake/packages` link resolves to the root-authorized shared-v34 overlay. The inspected M/N manifests bind the accepted-source-view and own newly compiled objects, with L and M respectively as their parent source hash. The accepted-source-view links for M/N and C/D/E/L resolve to their own lane objects. Read-only current object fingerprints are M 356976 bytes/hash 976331f85ecd1a41e88c278e00446025fbcb1acf1236d4e01b634452c0baaa9d and N 336456 bytes/hash 31707cfce94ffcf16232cb8d43e27f7443673566df0f39b8c226fa2b327ac524. These are binding observations; they do not stand in for the existing successful source checks.

The known Lake warning was assessed narrowly. The root's inverse-contdiff cache receipt and U22e environment-change record were read. The actual IFT ContDiff object hash is 1643895d9546fb472b54a89e29d500b023358851556be7750145ea3bfb6a10ac, matching that authorization. Only four material pinned API source files were compared byte-for-byte with `git show` at the pinned mathlib commit: InverseFunctionTheorem/ContDiff.lean (0f0f0f5bcd6784785ebf9798e772a73b544ef910ca31d221701bbd4729968518), ContDiff/Defs.lean (c436e0c185d3a52da5be9be371a3c954e7a63714288aaba7ae67bc769f32b825), Deriv/Mul.lean (668434e58a11f6fe2c599adc9655494d0f23ba42937662499884df02daaa8c7c), and FDeriv/Congr.lean (7dfbf7697655649ad619e8a37a807bbd8bf23ee19669a8e29e640da99df05db6). All match. The material IFT/local-inverse, finite-order eventual regularity, varying-map application, and eventual-equality derivative congruence interfaces were read. No broad git status or cache traversal was used, and no whole-cache cleanliness assertion is made.

Authority and resource checks used AGENTS.md, SERVER.md, takeover notes, compact selected current TEAM/REGISTRY fields, and the math-theorem skill plus its mandatory prompt-library, openai-workflow and lean-verification references. Current OQ3 ownership is the activated/released-successor lead 01a1669a-bca1-75e0-9d87-d07baee7b90a under coordinator 01a16680-f408-7391-8c52-d1d5041bda8b, with one child lease. Ownership records were not interpreted as proof of ongoing execution. This reviewer spawned no child, edited no source or shared file, touched no cache, ran no build/audit, and used only the existing read-only broker for remote reads. The sole write is this append-only report. No usage counts or subscription allocation is inferred from missing runtime telemetry.

## Final scoped verdict

M CORRECT; N CORRECT; batch interface CORRECT. The exact reviewed source version has complete independent source-to-statement/proof coverage and matching pre-existing successful server kernel/transitive-axiom evidence. No mathematical or evidence revision is required for these two helpers. Acceptance is restricted to the stated local analytic interfaces; B/D and every unproved root obligation remain open in their recorded scope.

The first 6640 report bytes remain the immutable blind prefix with SHA256 3ce3582b64ebf9e915d2f1d3689b53d967860baf1857473aeefed888296da2e2. This review unit is complete. No persistent continuation is implied; the parent lead chooses and records its next source-bound dependency under its ownership.
