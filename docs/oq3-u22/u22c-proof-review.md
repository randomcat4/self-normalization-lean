# OQ3 U22c independent complete review

## Immutable blind statement translation and acceptance conditions

This prefix was written after the complete elaborated owner-type inventory and before reading the frozen scope, source implementation, author notes, dependency sources, or execution receipts. Reviewer: fresh independent gpt-6.1-sol / xhigh context; no authorship of U22c; no child contexts; no Lean or audit execution. The only owned output is this report.

Blind input: drafts/oq3/u22c-actual-types.txt, SHA256 d1a79f8b2b13e09317d9bee29d9a218b3acab0ad5bacfdb877a826f94695d433. All eighteen DECL/TYPE entries were read, including the five private definitions, four explicit private theorems, public theorem, five generated defining equations and three generated instance-proof constants. Names alone are not taken as semantic evidence.

Let Z_k(p) denote the actual private weighted moment. Its generated equation states Z_k(p) = integral x^k * exp(p.1*x + p.2*x^2) dmu, for every real measure mu, natural k and real pair p. Let m_k(p) be its actual normalization: m_k = Z_k / Z_0, using Lean's totalized division. The weighted-moment slope is the continuous linear form Z_(k+1)*fst + Z_(k+2)*snd. The normalized slope is the continuous linear form (m_(k+1)-m_k*m_1)*fst + (m_(k+2)-m_k*m_2)*snd. The partition gradient is the continuous linear form m_1*fst + m_2*snd. These exact generated equations, rather than suggestive names, fix their contents.

The explicit private assertions are: (1) Z_0(p)>0 for a probability measure at every p in the interior of bivariateMGFDomain mu (x |-> (x,x^2)); (2) m_k has the stated full Frechet derivative there, for every natural k; (3) the actual tilted integral of x^k equals m_k(p) for every measure mu and every p, with no probability, interior or integrability hypothesis; and (4) log Z_0 has the partition-gradient Frechet derivative at every interior point for a probability measure. Assertion (3) must therefore be valid under the library's actual totalized tilted/integral conventions, not merely under the usual finite-positive partition case.

The public assertion quantifies over every real probability measure and every theta in that interior. It defines the actual tilt nu(p) = mu.tilted (x |-> p.1*x + p.2*x^2), actual means(p) = (integral x dnu(p), integral x^2 dnu(p)), and actual K(p) = log(integral exp(p.1*x + p.2*x^2) dmu). At theta it asserts: nu(theta) is a probability measure; x and x^2 belong to L2(nu(theta)); means has a full HasFDerivAt derivative equal to the product of the two covariance rows; K has a full HasFDerivAt derivative equal to actual means(theta) paired with the coordinate projections; and the map p |-> fderiv R K p has a full HasFDerivAt derivative equal to the displayed continuous-linear-map-valued Hessian.

More precisely, D = parabolaCovariance(nu(theta)), row0 = D(0,0)*fst + D(0,1)*snd, row1 = D(0,1)*fst + D(1,1)*snd, and Hessian = row0.smulRight fst + row1.smulRight snd. Acceptance requires verifying from definitions that D is the actual covariance matrix of (x,x^2), and that this operator-valued map applies as h |-> (v |-> row0(h)*v.1 + row1(h)*v.2), with the stated ordering and symmetry. No nondegeneracy is required or inferred.

Acceptance conditions fixed before source inspection:
- Verify the actual two-dimensional bivariateMGFDomain, tilt, means, covariance and logarithmic integral definitions; reject surrogate functions, a one-dimensional parameter restriction, silent boundedness, caller-supplied derivatives/domination, or strengthened assumptions.
- Read every line of the final source and every actual owner type, including generated equations and proof constants. Verify derivative quotient algebra and positive denominator, all-p totalized tilted-integral identity, and the needed L2-based variance/covariance formulas.
- Verify full Frechet derivatives through actual continuous linear maps. Directional/coordinate derivatives alone are insufficient. Verify the derivative of fderiv through eventual equality on an open neighborhood of theta; no unsupported equality outside the integrability interior is allowed.
- Verify each consumed direct dependency interface at its exact source version, and align the formal claims with the original source statements and frozen scope. Do not use another reviewer's verdict as mathematical proof.
- Only after completing the mathematical review, inspect the exact source/hash-bound server kernel and transitive-axiom evidence. Require every owned declaration to be covered, with no forbidden construction and only propext, Classical.choice, Quot.sound. Reuse existing successful checks without running any check in this review.
- Acceptance is limited to this cumulant-derivative module. No strict derivative, inverse theorem or OQ3/root closure follows merely from these displayed types.

END IMMUTABLE BLIND PREFIX

Blind-prefix binding: bytes=4884; lines=25; SHA256=2f09d4e0ff1dbca4d77a0d5c03a9c50973b0fe7f7ed5d140065855fffde7c547. The bound prefix is exactly bytes 0 through 4883, inclusive, and is never rewritten.

## Mathematical review completed before receipt inspection

STATUS: CORRECT, for the exact U22c module and frozen scope identified below. At this point the mathematical/source review is complete; no author notes or execution receipt has been used to establish the mathematics. The mechanical-evidence review follows in a separate appended section.

### Exact mathematical inputs

- Frozen scope: eighty-fourth-unit-scope.md, SHA256 68c25314f2bd586061a1993d8a34f2457b6343cd829c02ef30bdb34f0b8e9f0c; read in full.
- Reviewed implementation: OpenDomainFrechetCumulants.lean, all 190 lines, SHA256 b5d48b414adbc80f7db44f37cc2b2b423d44263c54e8547a5a356768a116df72.
- Direct producer A: QuadraticTiltCumulants.lean, all 165 lines, SHA256 ea105db471a073ac5eca67b4f94ff986766fd3fe3685790fb4859497da49289a, and all four entries of u22a-actual-types.txt.
- Direct producer B: OpenDomainWeightedMoments.lean, all 161 lines, SHA256 f28ea2e9812d5c7702c75adf096e4fbbce82e4d2464da6cda764d2349e8c6f74, and all three entries of u22b-actual-types.txt.
- Original source: current/oq3/proofs/r2/report.md lines 38-60 and 83-92; root-contract.md sections 2 and 4, with the rest read for scope boundaries. No author's u22 notes or other review verdict was read or used.

### Source-to-statement fidelity

The shared bivariateMGFDomain definition (library/Shao/Probability/BivariateLegendre.lean:20-22) is exactly {p | Integrable (x |-> exp(p.1*x+p.2*x^2)) mu} for W(x)=(x,x^2). Its interior is the genuine open subset of the full real product space. It is neither a coordinate slice nor a surrogate domain. Probability of mu entails NeZero mu, so integral_exp_pos applies. There is no support restriction, centering, positivity of X, caller regularity, caller domination or nondegeneracy hypothesis in the public type.

The pinned mathlib definition Measure.tilted is withDensity of ENNReal.ofReal(exp(f x)/integral exp(f)), hence on the true domain it is exactly dnu=exp(p.W-K(p)) dmu because the partition is positive and exp(log Z)=Z. The displayed means and K are literal integrals of this tilt and of the original mu. parabolaCovariance (RegularCovariance.lean:20-24) contains Var(x), Cov(x,x^2), the same Cov(x,x^2) in the second row, and Var(x^2); covariance_comm confirms that the repeated entry is the actual reversed covariance. Its definition has no bounded-support premise; bounded theorems elsewhere in its source are not consumed here.

R2:41-45 specifies exactly W, K, exponential tilt, m=gradient K and Delta=Hessian K. R2:51-59 places these objects on an open finite-K neighborhood and subsequently imposes stronger compactness, spectral and moment conditions for later uses. U22c proves the derivative bridge from the weaker sufficient interior hypothesis; it does not assume those derivative identities as premises. R2:83-92 consumes the actual centered covariance normalization; U22c supplies the actual covariance interpretation, not its inverse square root or positivity. Root-contract section 2's domain/positive-partition guard is preserved: K and its fderiv are total Lean functions, but every differentiability assertion and the needed eventual gradient equality is at/interior to the true domain. No real-valued claim about a divergent partition is used as a log-MGF claim. Root-contract section 4's saddle, inverse map, global rate, compact-uniform conditions and tail expansion remain separate obligations.

### Consumed dependency interfaces, independently checked

A's public directional-cumulant theorem is consumed at U22c:122 only for probability of nu(theta), L2(x), and L2(x^2), with exactly the same mu, theta and interior hypothesis. Those are the first three components of the full elaborated type; h.1, h.2.1 and h.2.2.1 select them correctly. A:28-29 obtains actual tilt probability and partition positivity from the integrability domain. A:54-67 pulls that domain back along t |-> theta+t*d, proving an open scalar exponential neighborhood for every d. A:112-115 applies the scalar exponential-neighborhood Lp theorem at d=(1,0),(0,1). This justifies the consumed L2 assertions without bounded support or assumed moments. No directional derivative from A is promoted to a full derivative by U22c.

B's public elaborated interface is full HasFDerivAt of I_k(p)=integral x^k exp(p.W) at every interior p, with derivative I_(k+1)*fst+I_(k+2)*snd. This is definitionally the h0/hk required at U22c:43-46 and 63-64, not a weaker coordinate/directional assertion. B's proof builds domination internally: it chooses a positive delta with thetaPlus=(theta.1,theta.2+delta) still interior, chooses eps=delta/4 and an open product rectangle, bounds exp(p.W) by exp(eps/2)*exp(thetaPlus.W) using 2|x|<=1+x^2, and dominates the full pointwise continuous linear derivative by shifted absolute weighted moments of orders k+1,k+2. B:149-157 invokes the dominated full Frechet integral theorem and identifies the integrated continuous linear map. Its assumptions, measurability, integrable bound, base integrability and full pointwise derivative are explicitly supplied. A/B are exact version-bound producer interfaces, not unexplained mathematical votes.

### Complete source proof review

Lines 1-8 establish only the two imports, namespace, notation and noncomputable context. They add no mathematical premise or custom proof setting. Lines 9-27 give the five literal definitions bound by the blind equations. For any k, write Z=Z_0(theta), a=Z_k(theta), and s_k(v)=Z_(k+1)(theta)*v.1+Z_(k+2)(theta)*v.2.

Lines 29-35: interior_subset hp is exactly integrability of exp(p.W). integral_exp_pos, with the probability-induced nonzero measure instance, proves Z_0(p)>0. Reducing x^0=1 gives the actual denominator, not a distinct partition. This handles every later use of inverse and logarithm differentiation.

Lines 37-56: B supplies full derivatives s_0 and s_k. Composition with hasDerivAt_inv at the nonzero Z and the product rule prove D(Z_k/Z_0)(v)=s_k(v)/Z - Z_k*s_0(v)/Z^2. Evaluating the continuous linear map at an arbitrary v, the field_simp/ring step with hz is exactly the identity
D m_k(v) = (m_(k+1)-m_k*m_1)*v.1 + (m_(k+2)-m_k*m_2)*v.2.
There is no division by a possibly zero quantity or use of an unproved derivative. The funext step changes only the global function expression from Z_k * inverse Z_0 to totalized division; it adds no domain restriction or extension assumption.

Lines 58-70: B's derivative for Z_0 and the nonzero positive partition give D(log Z_0)=Z_0^(-1)*s_0 by the pinned HasFDerivAt.log rule. At arbitrary v its coefficients reduce to m_1,m_2. The ring step uses only commutativity/associativity and the definition m_j=Z_j/Z_0; this is the true gradient linear form.

Lines 72-84: the all-measure/all-p qTiltedMoment_eq is valid. The pinned integral_tilted (Tilted.lean:230-232) has no integrability, SFinite or probability premise. It rewrites the tilted integral as integral [(exp(p.W)/Z_0(p))*x^k] dmu. The pointwise ring identity commutes x^k across the factor and the unconditional integral_div (Bochner/Basic.lean:295-297) moves the constant denominator outside. The resulting value is precisely Z_k/Z_0. This proof covers mu=0, a nonintegrable exponential, and nonintegrable weighted moments under the library conventions: a nonintegrable exponential makes Z_0=0 and the tilt the zero measure, so both sides are zero; if a weighted moment is nonintegrable, both corresponding totalized integrals agree by the same library identity. No probability or finiteness conclusion outside the true domain is inferred from this identity.

Lines 86-110: the public statement is exactly the frozen declaration after elaboration, with zero public definitions and one public theorem. Its six conclusions are actual tilt probability, both required L2 memberships, full derivative of the actual mean pair, full first derivative of actual K, and full derivative of the actual fderiv of K. In particular the last function is not an author-defined replacement gradient.

Lines 111-128: local lets duplicate the actual statement objects without changing them. The exact A interface supplies hp,hx,hx2, and hp is installed as the required probability instance for variance/covariance lemmas. hR uses the globally valid private integral identity for the same nu(theta); it does not replace the tilt or depend on directional differentiation.

Lines 129-146: variance_eq_sub is applied with hx or hx2, and covariance_eq_sub with both. Their pinned hypotheses are precisely probability and the two L2 memberships. They give D00=m_2-m_1^2, D01=m_3-m_1*m_2, and D11=m_4-m_2^2. The polynomial identities x*x^2=x^3 and (x^2)^2=x^4 identify the integrands exactly. L2 guarantees the square/product integrability required for those identities to express genuine moments, so this is not a manipulation of divergent totalized covariance formulas.

Lines 147-162: continuous-linear-map extensionality checks the entire map at arbitrary v. The k=1 normalized slope gives row0; the k=2 slope gives row1 after m_2*m_1=m_1*m_2. The cross entry order agrees with the actual symmetric covariance definition. No test only on basis vectors or one directional parameter is substituted for map equality.

Lines 163-175: qTiltedMoment_eq proves means(p)=(m_1(p),m_2(p)) for every p (x^1=x for the first component). HasFDerivAt.prodMk then supplies the full product derivative, and the row equalities transport it to row0.prod row1. The pointwise gradient identity at theta likewise transports the log-partition derivative to the actual means(theta) coefficients. Product means here are ordered (x,x^2), consistently with covariance rows and coordinate projections.

Lines 176-179: HasFDerivAt.smul_const pr0 and pr1 differentiates the two scalar normalized moments as a function valued in continuous linear forms, and addition gives the derivative of qPartitionGradient. The derivative is row0.smulRight pr0 + row1.smulRight pr1. Evaluating it at increment h and argument v gives
(D00*h.1+D01*h.2)*v.1 + (D01*h.1+D11*h.2)*v.2,
which is the actual covariance bilinear form of h.W and v.W. The outer parameter increment and inner linear-form argument are in the correct order. Symmetry follows from the actual covariance cross entries; no positivity or invertibility is needed.

Lines 180-184: this is the essential local-to-fderiv step. isOpen_interior.mem_nhds htheta supplies a genuine neighborhood consisting of interior points. At each p in that neighborhood, the proved qLogPartition_hasFDerivAt gives the exact fderiv equality by HasFDerivAt.fderiv. Thus actual fderiv(log Z_0) and qPartitionGradient are eventually equal at theta. EventuallyEq.hasFDerivAt_iff transports the operator-valued derivative already proved. Only this neighborhood equality is used; no equality of fderiv with normalized moments is asserted on the domain boundary or outside the domain.

Lines 185-190: the six proved components are assembled. The final simplifications only expand K and Z_0 and eliminate x^0; they preserve the exact original K and its actual fderiv. The namespace/section closures add no declarations or assumptions. Every line of the 190-line source is included in the intervals above.

### Complete actual-owner coverage

The inventory's eighteen declarations divide as follows, with no omitted owner/private/generated declaration:
1. qWeightedMoment (private DEF): lines 9-10; exact integral definition.
2. qNormalizedMoment (private DEF): lines 16-17; exact totalized quotient.
3. qMomentSlope (private DEF): lines 12-14; exact full weighted slope.
4. qNormalizedSlope (private DEF): lines 19-23; exact normalized slope.
5. qPartitionGradient (private DEF): lines 25-27; exact normalized first-moment gradient.
6. qPartition_pos (explicit private THM): lines 29-35; positivity as reviewed.
7. qNormalizedMoment_hasFDerivAt (explicit private THM): lines 37-56; quotient derivative as reviewed, for every natural k and interior p.
8. qLogPartition_hasFDerivAt (explicit private THM): lines 58-70; log derivative as reviewed.
9. qTiltedMoment_eq (explicit private THM): lines 72-84; all-measure/all-p identity as reviewed.
10. open_domain_quadratic_tilt_frechet_cumulants (public THM): lines 86-187; exact six-part full derivative conclusion.
11-15. qWeightedMoment.eq_1, qNormalizedMoment.eq_1, qMomentSlope.eq_1, qNormalizedSlope.eq_1, qPartitionGradient.eq_1 (generated THM): their entire actual types were read blind and match respectively the five literal defining equations reviewed above. They introduce no extra premise or stronger conclusion.
16-18. qMomentSlope._proof_1 : ContinuousAdd R, _proof_2 : SMulCommClass R R R, _proof_3 : ContinuousConstSMul R R (generated THM): concrete standard real structural instances needed to form sums/scalar multiples of continuous linear maps. Their actual types have no measure/parameter/hypothesis and encode no analytic theorem or target assumption. They are included in the owner axiom coverage requirement.

### Boundary and adversarial checks

- The probability law and parameter are arbitrary under the stated interior hypothesis; all input randomness is the one actual real law. No finite support, fixed source atoms or n-dependent measure appears.
- An empty interior makes the theorem's premise unavailable rather than yielding false analytic conclusions. Boundary points are not accepted by interior_subset alone; the derivative argument specifically needs the open neighborhood.
- A point mass or a law supported on two points may give singular/zero covariance. All quotient/log rules still work because the exponential partition is positive, and none of the proof divides by a covariance entry or determinant. Degeneracy is allowed as required.
- Odd moments retain their signs. Absolute moments appear only in B's internally constructed domination, not as a replacement for the true derivatives or covariance entries.
- The all-p integral identity is deliberately stronger as a totalized equality; only interior values are used for mathematical probability and derivative claims.
- There is no directional-to-Frechet shortcut: U22c's full derivatives come from B's full dominated integral interface, inverse/product/log rules, product pairing, scalar multiplication and eventual equality.
- The public theorem proves neither strict differentiability nor a local inverse, spectral lower bound, uniform compact moment theorem, global-rate localization, weak-Cramer/Edgeworth/tail theorem, nor closure of B/D or general OQ3. This module supplies precisely the frozen analytic bridge. No novelty claim is certified.

Mathematical verdict before mechanical evidence: CORRECT. No critical mathematical gap, silent assumption change, or source-to-statement mismatch was found in the exact reviewed version.

## Existing server kernel and transitive-axiom evidence

Evidence inspection began only after the mathematical verdict section above was appended. No Lean executable, audit executable, build, dependency rebuild or gate repeat was run by this reviewer. Remote actions were read-only library-source/evidence inspection and git rev-parse. A first source-search attempt returned exit 127 because rg is unavailable on the server; it read/changed no proof or build state. The fallback used read-only Python file reads.

Receipt binding: u22c-receipt.json SHA256 0c447c8da78c464a3294bcfb2706751b1d433d4df3bb33be559498f2fb8eea78 (4361 bytes). The status AUTHOR_PASS_PENDING_FRESH_COMPLETE_REVIEW is its historical author state; this report supplies the independent complete review. Its older A/B review-label metadata was not used as a proof or acceptance vote. This review checked the consumed interfaces directly.

The saved receipt, build history and remote retained run agree on:
- Exact frozen scope: 49 lines / 4363 bytes / SHA256 68c25314f2bd586061a1993d8a34f2457b6343cd829c02ef30bdb34f0b8e9f0c.
- Exact successful source: 190 lines / 9834 bytes / SHA256 b5d48b414adbc80f7db44f37cc2b2b423d44263c54e8547a5a356768a116df72. The remote worktree source and retained source-02.lean have this same hash, matching the complete local source reviewed here.
- Full-source attempt 02: exit 0, 5.311252787709236 seconds, CPU affinity 14-17, native memory 8192 MiB, jobs 4, autoImplicit=false. Its complete success log has 766 bytes / 14 lines / SHA256 2f06ab827e7b00f05584fcef2c2152569b369cd1308515806c2a2e104870967b. I read the entire success log: its three warnings concern tactic style and letI style only, not proof gaps or weakened options.
- First complete owner audit: exit 0, 5.11190627515316 seconds, same source hash and execution constraints. audit.log has 6293 bytes / 96 lines / SHA256 355418411a2141589e6dd8082164f60355ee139c149b76276e7fa3f68fe1d5d2. The remote actual-types.txt is byte-identical to the blind input (6177 bytes / 91 lines / SHA256 d1a79f8b2b13e09317d9bee29d9a218b3acab0ad5bacfdb877a826f94695d433) and is exactly the prefix of audit.log. The remaining five audit lines report frozen definitions 0, frozen public theorems 1, all theorems 13, all declarations 18, and U22C_AXIOM_GATE PASS.

I read all 44 lines of u22c-Audit.lean, SHA256 dfda1ca5285fe082f70b80d40cee7fef553a846124b3ca85e197086f07bbb635. It imports the actual module, verifies that the frozen public target exists and is a theorem, iterates env.constants by the actual getModuleIdxFor owner (rather than a public-name heuristic), rejects every new owned axiom, and runs Lean.collectAxioms on every owned constant. It rejects any transitive axiom outside propext, Classical.choice, Quot.sound. This covers all five private definitions as well as public, explicit private and generated theorem/proof constants. All eighteen actual records list exactly those three axioms. pp.deepTerms and pp.maxSteps affect printing only; they do not weaken kernel checking.

Supporting local and remote files match by byte hash:
- u22c-build-history.json: 35a84f10fee8b5499c04da188305a262d6fbf9c442efed3b0a1152f188115408, 1567 bytes.
- u22c-audit-record.json: 46aaf867e6ba7bf59a80663804bc2f1e1c1fb0c4912556ab60658093c29f713d, 497 bytes.
- u22c-audit-environment.json: 67fe891d43d322f54bcd5e983179e43aa601df53f3649730db89efd5f2b14396, 630 bytes.

The server run is /root/rivermind-data/shao-lean-20261021/runs/oq3/u22c-20261023; worktree is workspaces/lead-oq3. I verified the remote worktree source hashes of A and B also equal the exact reviewed hashes. The reused accepted-source-view contains A/B/C .olean symlinks resolving to the lane's existing build artifacts. The manifest records the v43 accepted baseline and root's notice that v44 leaves the 286 prior sources / 1063 old objects unchanged. This read-only view is the necessary package-root import lookup arrangement, not copied caches or a shared-cache write. I did not rebuild or recheck the unchanged baseline.

The worktree lean-toolchain is leanprover/lean4:v4.36.0-rc1; the pinned mathlib checkout was independently observed at git HEAD 807d3836b165983210ee2ecf3cd28f239436949c, matching lakefile and manifest. The reviewed library APIs were read from that pinned server checkout. Source probability/covariance definitions were read from the curated read-only library snapshot. No local Lean installation or execution occurred.

The failed history is retained and consistent with the final claim. Attempt 01 checked the full 190-line source hash 32b11108d151ff0b88ed56030b87a6f936bdc0e42fb413c92e06bedf8ef5d78f, exited 1 in 5.422993700951338 seconds, and retains build-01.log (15750 bytes, SHA256 5f5ca20224e8917a13c7e7c25a32f95fa830088ab8199dd560d101ea34daecce). Its errors are unsolved goals in the four continuous-linear-map equality proofs. I inspected the entire source-01/source-02 diff: only extensionality/tactic expressions in the normalized derivative, log derivative and two row-map equalities changed. No declaration, premise, definition, conclusion or source scope changed. The successful source was reviewed in full. The separately recorded initial partial transfer/scope-directory failure involved no Lean execution; the failed scope transfer was retried after inspecting the effects, rather than concealing a mathematical build failure. No previously passed unchanged gate was repeated.

No sorry, admit, new axiom, unsafe, native_decide, implemented_by, substituted conclusion or proof-setting weakening occurs in the complete reviewed C source or consumed A/B sources. The transitive actual-owner audit supplies the additional dependency-level axiom check; its standard-three whitelist is satisfied.

## Final independent decision and evidence reuse boundary

STATUS: CORRECT.
JUSTIFICATION: The exact 190-line source proves the frozen arbitrary-probability/open-two-dimensional-domain theorem through genuine weighted-moment Frechet differentiation, a positive partition, valid normalized tilted-integral identities, L2-justified covariance formulas, and a correct neighborhood identity for the actual fderiv. Every module-owned actual type, including all private definitions and generated proof/equation constants, has been reviewed. Exact source/scope/type hashes match the existing successful server kernel and complete transitive-axiom audit evidence. No additional mathematical premise was introduced. No critical gap or unresolved material evidence discrepancy remains for U22c.

This decision certifies only Shao.OQ3.OpenDomainFrechetCumulants at source SHA256 b5d48b414adbc80f7db44f37cc2b2b423d44263c54e8547a5a356768a116df72 against the frozen U22c scope. It does not close local-inverse/strict-derivative obligations, root B/D, or general OQ3. At integration, reuse this complete independent review and the existing server receipts by checking the exact hashes, consumed interfaces and actual integration interactions; a new complete local-proof review is needed only for a changed proof or an uncovered material scope/evidence/integration risk.

Additional source bindings: original R2 report SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55; root-contract.md a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a; u22a-actual-types.txt 4c6d4ab35fb2f7e24be183aeab1e3c7b30d90a6a54aeec6c0691e598d4094c7a; u22b-actual-types.txt 47556e5fd5e97643398bdc2e447dff38aeb1d0ac9f45e6aabe4c0804ff07afa9; BivariateLegendre.lean d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58; RegularCovariance.lean 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853.

Report integrity: the immutable blind prefix is the first 4884 UTF-8 bytes / 25 LF-terminated lines, SHA256 2f09d4e0ff1dbca4d77a0d5c03a9c50973b0fe7f7ed5d140065855fffde7c547. Full-file byte count, line count and SHA256 are computed after this final append and supplied on delivery, avoiding an impossible self-referential file hash.
