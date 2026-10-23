# OQ3 U22f independent complete review

## Immutable blind actual-statement translation and acceptance prefix

Reviewer: fresh independent reviewer; requested model/effort gpt-6.1-sol/xhigh.
Ownership: only this report. No source edits, evidence edits, Lean execution, audit execution, or gate execution.
Method: math-theorem; project constraints override local Lean probing. Read skill, prompt-library, openai-workflow, lean-verification, and AGENTS.md before this prefix.
Isolation: this prefix is written after reading the complete actual-types inventory, before opening the frozen scope, source, original report, consumed interface files, or author check artifacts. The assignment itself disclosed target/evidence metadata; that disclosure is not proof evidence and is not used to certify this prefix.
Actual-types input: drafts/oq3/u22f-actual-types.txt; expected SHA256 ca8efe662783a7821fc3d7ea1f22c4978b03a492240386468d2b5c7e918ce9ad.

### Blind translation of all two actual declarations

1. Shao.OQ3.compact_open_domain_uniform_tilted_moments.
For every measure mu on the real line with an IsProbabilityMeasure instance, and every set Theta of pairs of real numbers: if Theta is compact and is contained in the interior of bivariateMGFDomain mu (x maps to (x,x^2)), define nu(p) to be mu.tilted (x maps to p.1*x + p.2*x^2). Then (a) for each theta in Theta, nu(theta) is a probability measure; and (b) for every natural k there is a real C such that C>0 and, for every theta in Theta, x maps to |x|^k is integrable under nu(theta), its integral is nonnegative, and that integral is at most C.
The order is forall mu, forall Theta, compactness/subset assumptions, then forall k, exists C>0, forall theta in Theta. C may depend on mu, Theta, and k, but not theta. There is no nonemptiness assumption on Theta; the empty compact set is included. The formal statement has no bounded-support, supplied moment, supplied derivative, supplied domination, or supplied regularity assumption.

2. Shao.OQ3.open_domain_tilted_moment_contDiffOn.
For every real probability measure mu and every natural k, the actual signed raw moment map p maps to the integral of x^k under mu.tilted (x maps to p.1*x + p.2*x^2) is ContDiffOn over R of order top on the interior of bivariateMGFDomain mu (x maps to (x,x^2)). The inventory prints the order as the coercion of top to the differentiability-order type. This is smoothness to all finite orders, pending exact notation verification, and does not by itself assert real analyticity.
The parameter domain is two dimensional. Neither p.2<0 nor bounded support nor caller-supplied regularity appears in the type. Integrals are totalized Bochner integrals, so source inspection must ensure the theorem describes genuine moments on the stated domain rather than exploiting nonintegrable integrals equal to zero.

### Acceptance criteria fixed before source inspection

- Verify actual definitions: bivariateMGFDomain, its true full two-dimensional interior, tilted measure, signed moment, and absolute moment. Reconcile every parameter, hypothesis, and conclusion with the frozen source target.
- Verify both declarations are covered in full, including all private/generated owned declarations if any; inspect the complete owned source, not only these printed signatures.
- Smoothness must apply to the actual tilted quotient and actual natural signed powers on the entire stated interior, with a justified positive normalizer there. C-infinity must not be silently strengthened to analytic omega.
- Compactness must yield one positive bound for each k uniformly in theta, with empty Theta handled without an implicit nonempty maximum. Integrability and nonnegativity must be genuine; even-power controls must preserve the meaning of odd absolute moments. k=0 and degenerate probability measures must remain valid.
- No assumptions may be added or reinterpreted. Do not infer standardized 8+delta moments, a lower variance bound, uniform spectra, a root theorem, or a local inverse from these two raw-moment declarations.
- Validate all consumed theorem types and their conditions in the pinned source environment. An independently accepted dependency may supply a previously checked interface; another review vote is not a proof of this source.
- Only after the mathematical review, inspect hash-bound server build and transitive-axiom artifacts. Confirm exact source/version binding, full owned coverage, actual success, allowed axioms only (propext, Classical.choice, Quot.sound), and preservation of failed attempts.
- Return CORRECT, INCORRECT, or UNCERTAIN separately for statement fidelity, proof, and evidence; identify any exact gap instead of silently repairing it. No repeat passed Lean/audit gate.

END IMMUTABLE BLIND PREFIX

## Prefix binding and reading order

The immutable prefix is exactly bytes [0,4771) and lines 1-32 of this report, UTF-8 without BOM, ending with LF. Prefix SHA256: 8313a913cb8e26597a57719764acdf1ac6d398cc02b93518ad626932ab3105d5. The actual-types inventory hash was independently computed and equals ca8efe662783a7821fc3d7ea1f22c4978b03a492240386468d2b5c7e918ce9ad.
After this prefix was written, I read the entire frozen scope, all 85 owned source lines, all 103 direct OpenDomainSmoothMean source lines, all 165 QuadraticTiltCumulants source lines, original R2 report lines 38-60 (and context through 66), and root-contract sections 2 and 4 (within the full 82-line contract). I inspected consumed interfaces in the actual pinned server Mathlib checkout by read-only Python file reads. I have not yet opened U22f author build/audit evidence at the time of writing the mathematical verdict below.

## Mathematical verdict, fixed before author check evidence

STATUS: CORRECT.
Statement fidelity: CORRECT for exactly the two frozen U22f raw-moment declarations.
Proof: CORRECT on complete source inspection and exact consumed interfaces. No missing mathematical premise or proof gap was found. This verdict does not rely on an author success claim or another review vote.
Evidence status at this point: NOT YET INSPECTED; see the separately appended evidence review.

### Source-to-statement fidelity and original scope

The frozen scope SHA256 is ce571d021568fc4a8976f37d8fa9241dfbd297f0228627cb231743fac54101b3. Both frozen theorem signatures match all two actual declarations, including implicit IsProbabilityMeasure mu, every natural k, the full product parameter space, the literal quadratic tilt, the interior of the true exponential-integrability set, the positive uniform constant, and explicit integrability/nonnegativity in the second target. There is no extra nonempty, boundedness, moment, domination, regularity, second-coordinate-sign, or covariance-nondegeneracy premise.

Original R2 report SHA256 is 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55. Lines 40-43 define W=(X,X^2), K(theta)=log E exp(theta dot W), and dP_theta=exp(theta dot W-K(theta))dP. Lines 50-60 require a compact parameter family in an open finite-K neighborhood and a uniformly bounded standardized 8+delta moment, together with spectral bounds. Root-contract section 2, especially lines 28-30, requires precisely this tilt and its strictly positive finite partition on the true integrability domain. Section 4, lines 66-72, preserves the standardized moment, spectral, inverse-map, weak Cramer, far-probability and expansion obligations.

U22f supplies genuine all-natural raw-moment smoothness and uniform raw absolute moments on any compact subset of the true open domain. On that domain its normalized density exp(theta dot W)/Z is exp(theta dot W-log Z), since Z>0. This faithfully contributes to the compact-moment obligation. It does not already prove the standardized vector's real-order 8+delta bound, a uniform inverse-covariance or spectrum bound, a mean-map inverse, or the root-B expansion. It does not close B/D or enlarge any previous bounded-C closure. Original EX=0, P(X>0)>0 and saddlepoint assumptions are unnecessary for these intermediate moment facts and are not being removed from a root theorem.

### Complete owned-source review, lines 1-85

- Lines 1-6: import the established OpenDomainSmoothMean chain, open only notation/namespaces, and enter a noncomputable section. There are no owned definitions, hidden hypotheses, altered local instances, or proof-setting changes.
- Lines 8-18: the first theorem's domain Omega is definitionally the entire two-dimensional interior, and I_j(p) is exactly the weighted signed numerator integral. The consumed open_domain_weighted_moment_contDiffOn mu j has exactly this domain, function and C-infinity order for every natural j. It is not restricted to a negative second parameter or bounded law.
- Lines 19-22: interior_subset hp supplies genuine integrability of the exponential from bivariateMGFDomain. IsProbabilityMeasure mu supplies NeZero mu. integral_exp_pos therefore proves I_0(p)>0, with x^0=1 simplified explicitly. Its nonzero consequence is supplied pointwise on the whole domain to ContDiffOn.div. Thus the normalized signed quotient I_k/I_0 is smooth there.
- Lines 23-35: ContDiffOn.congr asks for actual moment = quotient on the domain. integral_tilted rewrites the actual tilted-measure integral as the original-measure integral with density exp(f)/Z. For real scalars smul is multiplication. The pointwise ring identity commutes x^k past this density; integral_div moves the parameter-dependent but x-constant Z outside the integral. The final simplification identifies I_0=Z. This identity is literal and does not substitute a surrogate moment. Although the library formula is valid for totalized integrals too, all required moments on Omega are genuinely integrable by the accepted directional-cumulants interface, detailed below.
- Lines 37-53: the second theorem retains arbitrary compact Theta with Theta contained in Omega. hprob is exactly the first conjunct of open_domain_quadratic_tilt_directional_cumulants at each theta. The proof constructs both required conjuncts, rather than assuming the tilted laws are probability measures.
- Lines 54-60: for each k, M(p) is the actual signed moment of order 2*k. The first new theorem gives continuity on Omega; restriction along hTheta gives ContinuousOn M Theta. A continuous image of a compact set is compact and hence BddAbove in the real line. This produces a real upper bound B for every M(theta). C=|B|+2 is strictly positive and is chosen before theta. No maximizer, nonempty image, or pointwise-varying C is used.
- Lines 61-68: at a fixed theta the actual probability instance is installed. The full-domain directional-cumulants theorem applied to d=(1,0) has F(x)=x and provides integrability of x^j for every j. The projection .2.2.2 selects the forall-d conclusion, and .2.2.1 selects precisely its forall-j integrability conjunct. Simplification removes 1*x+0*x^2 without changing the law. Integrable.norm then gives integrability of |x^k|=|x|^k, including odd k; it is not an unjustified identification of signed x^k with |x|^k. The even signed integrand is integrable separately.
- Lines 69-75: the equality (|x|^k)^2=(x^k)^2=x^(2*k) is valid for all reals x and naturals k. abs_pow and sq_abs preserve odd-power signs until squaring; pow_mul and Nat.mul_comm handle the exponent order. For a=|x|^k>=0, (a-1)^2>=0 implies 1+a^2>=2a>=a. The nlinarith proof uses exactly these facts, yielding |x|^k<=1+x^(2*k) without a sign mistake.
- Lines 76-82: integral_nonneg uses pointwise nonnegativity of |x|^k. integral_mono is applied with both actual integrability proofs: ha and integrability of 1+x^(2*k). integral_add is justified, and the local tilted probability instance makes the integral of 1 exactly 1. The compact-image upper bound gives M(theta)<=B; le_abs_self B yields 1+B<=|B|+2. The final bound is uniform in theta and has exactly the frozen quantifier order.
- Lines 84-85 close the section and namespace. There are exactly two owned theorem declarations and no extra owned definition or private declaration in the text. Formal environment coverage is checked separately below.

### Consumed project interfaces and pinned library conditions

Direct dependency OpenDomainSmoothMean.lean is read in full, hash d6457d90d9d0e1ccdae6d6ea041d8caef65f70b3cb6d5fa8baea1867a5bffb8e; identical on the server. Its consumed theorem at lines 9-39 states all-natural weighted signed-moment C-infinity on this same full interior. Its proof inducts simultaneously over every numerator order, obtains the Frechet derivative from open_domain_weighted_moment_hasFDerivAt, and uses the open-domain unique-differentiability interface. No new assumption is introduced by consuming it. Its independently accepted review is an existing dependency certificate, not evidence that the new quotient/compact proof is correct.

QuadraticTiltCumulants.lean is read in full, hash ea105db471a073ac5eca67b4f94ff986766fd3fe3685790fb4859497da49289a; identical on the server. The used interface at lines 84-102 requires only mu a probability law and theta in the same interior. It returns the actual tilted probability measure and, for every direction d, actual all-natural integrability of F(x)^j. At d=(1,0), this is integrability of x^j. The construction is also checked: the true exponential density identity at lines 11-52 yields probability and positive Z, the continuous line through an interior theta gives 0 in the projected exponential-integrability interior at lines 54-67, and pinned integrable_pow_of_mem_interior_integrableExpSet supplies all powers at line 157. Hence this interface supplies real moment integrability, not a claim derived merely from a finite totalized integral.

The shared BivariateLegendre definition was read: bivariateMGFDomain mu W is exactly the set of theta for which exp(theta.1*(W x).1+theta.2*(W x).2) is Integrable mu. There is no surrogate domain or assumed domination in this definition. The server source hash is d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58.

Read-only server pin inspection confirms lean-toolchain leanprover/lean4:v4.36.0-rc1; both lake-manifest mathlib rev and actual Mathlib Git HEAD are 807d3836b165983210ee2ecf3cd28f239436949c. No Lean was invoked by this reviewer. The following actual pinned Mathlib source interfaces were inspected:

- MeasureTheory/Measure/Tilted.lean, SHA256 355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f: Measure.tilted at 38-43 is withDensity of ENNReal.ofReal(exp(f)/integral exp(f)); isProbabilityMeasure_tilted at 126-127 needs NeZero mu and integrability of exp(f); integral_tilted at 230-232 has no extra integrability premise and gives exactly the density-smul formula; integrable_tilted_iff at 293-295 needs actual exp(f) integrability. All uses here have real-valued measurable quadratic f and satisfy the necessary measure conditions.
- Analysis/Calculus/ContDiff/Operations.lean, SHA256 5f7ddddf74f7f532c15a98590fcb1f065cd96e55eb7c64b8bfa49242c6eb4412: ContDiffOn.div at 825-827 needs both smooth factors and a nonzero denominator at every domain point; all are supplied.
- Analysis/Calculus/ContDiff/Defs.lean, SHA256 c436e0c185d3a52da5be9be371a3c954e7a63714288aaba7ae67bc769f32b825: ContDiffOn at 471-472 is pointwise ContDiffWithinAt; contDiffOn_infty at 548-549 is exactly all finite natural differentiability orders; continuousOn at 557-558 and congr at 564-565 have the conditions used in this file. Thus the printed coe-top is C-infinity, distinct from analytic omega.
- Topology/Compactness/Compact.lean, SHA256 cdc05494e34ec5d4163211223acf44d4c980629cac5542a52ca6d7360d80754e: IsCompact.image_of_continuousOn at 110-111 requires exactly compactness and continuity on the source set, without nonemptiness.
- Topology/Order/Compact.lean, SHA256 e3d3e63921f09661fc6178857a0a72f28c27d41f7810f66607f24ac5919c7001: IsCompact.bddAbove at 322-324 requires a nonempty ambient ordered type with ClosedIciTopology, not a nonempty compact set. R meets these conditions. Therefore empty Theta is covered by the actual library theorem.
- MeasureTheory/Integral/Bochner/Basic.lean, SHA256 66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670: integral_add at 239-242 needs the two supplied integrability hypotheses; integral_div at 295-297 has no hidden premise; integral_nonneg at 647-649 is pointwise; integral_mono at 670-672 needs both supplied integrabilities; integral_exp_pos at 792-798 needs NeZero mu and exp-integrability; integral_const at 990 and the probability instance justify integral 1=1.
- MeasureTheory/Function/L1Space/Integrable.lean, SHA256 d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759: Integrable.norm at 544-545 gives integrability of the pointwise norm of an integrable real-valued function.
- Probability/Moments/IntegrableExpMul.lean, SHA256 9ddfb99776091f424dc7e1a86b6a456180e8186cae9ca1084541eff41aa9e3a8: integrable_pow_of_mem_interior_integrableExpSet at 518-522 provides all natural powers from 0 in the true integrability interior, matching the consumed cumulants proof.

### Boundary and strength attacks

Empty Theta: M '' Theta is empty and BddAbove still has a witness; the probability and moment conclusions over theta are vacuous, while C=|B|+2 remains positive. k=0: both power functions are 1, including at x=0; the actual probability integral is 1, and the proof supplies the bound through M=1. Odd k: the norm argument uses |x^k|=|x|^k and the even-power comparison, never equates signed and absolute odd moments. Degenerate probability laws: no positive covariance or nonconstant X is used, so point masses are included. Boundary parameters outside the interior: no smoothness or compact-moment conclusion is claimed there. Empty interior: the smoothness assertion is vacuous and the compact theorem can only have empty Theta. All parameter dependence and quantifiers are preserved. No analytic, standardized, spectral, inverse-map or root-closure claim follows merely from this unit.

## Existing server evidence review, after mathematical verdict

Evidence verdict: CORRECT for this exact U22f source and its two actual owned declarations. Existing successful checks were inspected and reused; no Lean, audit, gate, cache operation or build was run by this reviewer.

### Exact artifact binding

Local receipt u22f-receipt.json is 3955 bytes, SHA256 1711d9cf98bb9c68c38db323dfdc974be47e8e3fdcd90c5ad3d03ba75dab1110, with status AUTHOR_PASS_PENDING_FRESH_COMPLETE_REVIEW. Its bindings agree with the bytes inspected in this review:

- Frozen scope: 3634 bytes / 42 lines / ce571d021568fc4a8976f37d8fa9241dfbd297f0228627cb231743fac54101b3.
- Final complete source-02.lean and current local/server OpenDomainCompactMoments.lean: 4170 bytes / 85 lines / 19946ecf589a2012df33b34ad740b4ff30190bd84fe42662bdaa194c5c545093.
- Actual-types inventory: 1116 bytes / 18 lines / ca8efe662783a7821fc3d7ea1f22c4978b03a492240386468d2b5c7e918ce9ad.
- Local and remote Audit.lean: 1945 bytes / eda63ada323218525804878a8ccab874dd15dfcef0731fae8931bca2540d3723.
- Build history: 1565 bytes / 71b28b9e53f42ee6fc5bf848580d917e972a140ea7975927c28e1fac3838bdec.
- Audit record: 498 bytes / 71a341fc02b9bcade3102d52aedd175447acde499fa50eec6d66b5699ed39d86.
- Audit environment: 493 bytes / 15e1d0cd9fd26e906db36d62e5568ed2a55dfab3a59a4d278a0cd6d5856053e7.

The server evidence directory is /root/rivermind-data/shao-lean-20261021/runs/oq3/u22f-20261023. I read all three small build/audit logs there directly and computed all listed remote file hashes. No raw log was copied to this workspace.

### Complete build, warning and preserved failure

Attempt 2 checks the complete 85-line, two-public-target final source, source SHA256 19946ecf589a2012df33b34ad740b4ff30190bd84fe42662bdaa194c5c545093, exit 0 in 4.3730968199670315 seconds. build-02.log is 359 bytes, SHA256 ee2b74a47826a842d30b268001596c9671761ebf9ac8688259901ebb9fde2429. Its sole diagnostic is the line-62 style recommendation to use let instead of letI in a proposition proof. No linter suppression or other proof-setting change appears in the source. This is not a logical failure or an integrability warning, and the successful source is retained unchanged.

Attempt 1 is preserved as source-01.lean, 4176 bytes, SHA256 7c12d5deb5601c13fe0a8bae3641dd444b8d5dd3e468f1c7136f96a0dea11fef, exit 1 in 4.2845675852149725 seconds. build-01.log is 576 bytes, SHA256 81f7194c35025a16732a8301cc6e4557674774ba174f2945874077cba318950f. Its only substantive error is at line 81: add_le_add_left produced M(theta)+1<=B+1 where 1+M(theta)<=1+B was expected. A direct snapshot diff shows the sole source change is replacing that proof term by linarith [hB ...]. All declarations, assumptions, target expressions and the remaining proof are unchanged. Therefore there was no scope weakening hidden in the successful revision.

### Full owner and transitive-axiom coverage

The complete audit source was read. It checks that the two frozen names exist as theorems, enumerates every constant in the environment whose actual module owner is Shao.OQ3.OpenDomainCompactMoments, rejects owned axioms, runs Lean.collectAxioms on each owned constant, and rejects any axiom other than propext, Classical.choice, Quot.sound. It does not merely sweep a namespace or a manually selected theorem subset. The source file itself contains none of sorry, admit, axiom, unsafe, native_decide or implemented_by and has no weakened proof setting.

The first owner audit has exit 0 in 4.984939379617572 seconds, bound to the final source and the audit-source hash above. audit.log is 1230 bytes, SHA256 53fc832c28aba291dc22d4ec139c7da0bb7c40abb5fe04aa7020c9902f94bb47. I inspected its full output: both DECL/TYPE records exactly match the blind inventory, both AXIOMS lists are [propext, Classical.choice, Quot.sound], and the final counts are FROZEN_DEFINITIONS=0, FROZEN_THEOREMS=2, ALL_THEOREMS=2, ALL_DECLARATIONS=2, followed by U22F_AXIOM_GATE PASS. Thus all two actual owned declarations are the two public theorems; there is no unreviewed private or generated owned theorem in this exact module.

### Environment, resource discipline and dependency scope

Both build attempts and the audit record use CPU14-17, Lean native memory 8192 MiB, jobs 4 and autoImplicit=false; the designated OQ3 worktree is /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3. The pinned toolchain/Mathlib sources were independently observed earlier in this review. The environment manifest reuses /root/rivermind-data/shao-lean-20261021/runs/oq3/accepted-source-view and adds the lane's own new OpenDomainCompactMoments object. Direct read-only inspection confirms that the imported OpenDomainCompactMoments, OpenDomainSmoothMean, OpenDomainFrechetCumulants and QuadraticTiltCumulants objects in that view are symlinks to the lane worktree's .lake/build/lib/lean/Shao/OQ3 files. I did not modify these symlinks, packages, objects, source files, pins or root imports.

The manifest records v43 accepted objects plus the v44 notice that 286 baseline sources/1063 objects are unchanged, and no binary cache copy/shared write. This review uses that existing environment provenance and checks the needed exact local/server dependency source hashes/interfaces; it does not assert a fresh independent audit of the entire inherited baseline. U22e's unavailable inverse-function cache interface is not imported by this source and is not a premise or accepted output of U22f.

One nonblocking provenance-label discrepancy is preserved explicitly: the receipt's direct_dependency.independent_review string says 'full90line lead read', while the exact hash-bound OpenDomainSmoothMean source inspected here has 103 lines. The dependency source hash itself matches exactly, and this review read all 103 lines and validated the consumed interface. I did not use that textual review label as proof evidence, and it does not affect U22f's statement/proof or server gate binding.

## Final disposition and limits

FINAL STATUS: CORRECT.
Natural-language/source-to-statement fidelity: CORRECT for the frozen U22f contribution.
Complete owned proof: CORRECT, all 85 lines reviewed, all two actual declarations covered.
Existing server kernel/transitive-axiom evidence: CORRECT and hash-bound to this exact source, only the three allowed foundational axioms.
No critical gap, unsupported assumption, uncovered owned declaration, or required extra Lean rerun was found. This report completes the assigned fresh independent complete review; it does not merge or modify evidence status. The lane lead/coordinator may reuse this exact-source review at acceptance, checking hashes/interfaces/interactions and original-scope claims rather than automatically commissioning a duplicate complete review.

The accepted contribution consists of smooth actual signed natural raw moments on the full true two-dimensional open domain and uniform true natural absolute raw moments for arbitrary compact subsets, including the empty set. Standardized 8+delta, uniform spectra, inverse-map/compact inverse-image work, Edgeworth/cell/Laplace/far-tail estimates, and root B/D remain outside this result. No novelty or whole-OQ3 closure is certified here.

Reviewer actions: read-only local/server source and artifact inspection, writing only this report. No child context, source/evidence edit, Lean invocation, audit invocation, build or repeated passed gate. Requested/configured reviewer dispatch was fresh gpt-6.1-sol/xhigh; separate input/cached-input/output/reasoning-subset usage counts were not exposed to this reviewer and are not invented or converted into subscription percentages.
