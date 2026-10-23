STATUS: CORRECT
JUSTIFICATION: The complete frozen declaration and the complete 90-line Lean source prove the stated local two-corner exponential envelope on the true bivariate exponential-integrability domain. The actual elaborated theorem, including its explicit let-bound function, matches that declaration. The original successful server kernel and actual-module-owned recursive-axiom evidence are bound to these exact bytes and can be reused. No critical mathematical, translation, or evidence gap was found in this unit.

# CK170 independent complete proof review

Reviewer: fresh independent NON-AUTHOR context /root/oq3_u22ck_full_review; dispatch model gpt-6.1-sol, effort xhigh. This reviewer did not author or change the statement, proof, dependency, audit program, receipt, source branches, or publication. The only owned write is this report. Token telemetry was not available and no usage estimate is asserted.

Authority and method: read the applicable AGENTS.md, SERVER.md, current TEAM ownership, takeover instructions, current REGISTRY OQ3 authority, streamlined-acceptance clarification, math-theorem skill and its prompt-library/openai-workflow/lean-verification references. REGISTRY identifies OQ3 owner 01a1669a-bca1-75e0-9d87-d07baee7b90a, activated replacement with old writer released and child ceiling 1. Review used saved evidence plus read-only server Python on CPU14-17. No math-ultra, additional context, Lean invocation, heavy gate, check replay, shared-cache change, source/Git write, or cross-chat message was used.

# Exact reviewed artifacts

All local artifacts below were read completely, and their SHA256, byte count and line count were independently measured. Every corresponding server run artifact has the same SHA256. Source, scope and audit are UTF-8 without BOM and use LF; their measured CR count is zero.

| Local path under C:/game/shao lean/ | SHA256 | Bytes | Lines |
| --- | --- | ---: | ---: |
| drafts/oq3/u22ck-source.lean | 9df6b51d5654554f952c84b2b31c8140d25d1eb9dcab6e6e4ec74b0acaa955fa | 4417 | 90 |
| drafts/oq3/hundred-seventieth-unit-scope.md | 50e90678db1364934e17fa02deda49a8d468fa0dbb9301d58efbd186b77f52ec | 2647 | 23 |
| drafts/oq3/u22ck-actual-types.txt | ac7aa7a899a44da45c046a6937ff218f17fedb2e45dc730b3584175d5c2ed662 | 1035 | 18 |
| drafts/oq3/u22ck-Audit.lean | 41060d6ba1b1c12dd516244699357687c515da2c69e104c40ac0965a021e4466 | 2000 | 47 |
| drafts/oq3/u22ck-receipt.json | 836a8f660c9dadbf315f215f89970b59866d6613908c45194a434c320f7ef700 | 3724 | 87 |
| drafts/oq3/u22ck-build-history.json | 476bcc193d3c749a76a1539e197613f26eb910c96d5f67598b11891153367543 | 1059 | 26 |
| drafts/oq3/u22ck-audit-environment.json | eb116c5382290a40d0dcb4e28196933dd9b0e546602ddfecefa4410a38143d5f | 1252 | 12 |
| drafts/oq3/u22ck-audit-record.json | 9e0c6a4124bf6fadc868a0446bfda12aa71b3f0a48e8cc338389984a4aa69028 | 498 | 18 |

Server run: /root/rivermind-data/shao-lean-20261021/runs/oq3/u22ck-20261023. Its source-01.lean is byte-equal to /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3/Shao/OQ3/OpenDomainExponentialEnvelope.lean and has the source hash above. The entire frozen Lean block is textually equal to the source theorem header before `:= by`, including every binder, implication, conjunction, quantifier and the complete explicit g value. The entire 18-line actual type was read and is byte-equal to the DECL/TYPE/AXIOMS/KIND slice of the original audit.log, rather than a reconstruction from the source header.

Observed server branch: feat/oq3-middle-frequency-and-inversion; HEAD 305173d6a7ce72b0f445431b2177dda9b2c3838c; tree 2480c5d5c361e9747012006b91671b7c15d054be. CK source remains untracked (`?? Shao/OQ3/OpenDomainExponentialEnvelope.lean`); this review does not modify the frozen PR225 intake or claim CK is published there.

# Complete statement and source fidelity

Actual owner module: Shao.OQ3.OpenDomainExponentialEnvelope. Sole actual declaration: Shao.OQ3.open_domain_local_exponential_envelope, KIND theorem. Import is ONLY Shao.Probability.BivariateLegendre. All 90 source lines, all proof steps, all statement/proof local values and all 18 actual-type lines received complete review. There is one public theorem, one actual owned declaration, zero private/generated/extra owned theorems, and zero owned definitions or definition values. No generated or external-namespace declaration attributed to this module was omitted.

The statement takes an actual probability measure mu on the Borel real line, an ordinary real pair theta, and membership of theta in the interior of the FULL set

D = {q : real x real | Integrable (fun x => exp(q.1*x + q.2*x^2)) mu}.

It produces r>0 with BOTH literal points (theta.1+r,theta.2+r) and (theta.1-r,theta.2+r) in that same D. Its complete statement let-value is

g(x) = exp((theta.1+r)*x + (theta.2+r)*x^2)
     + exp((theta.1-r)*x + (theta.2+r)*x^2).

For this actual function, the conclusion is genuine Integrable g mu and pointwise nonnegativity, followed by EVERY p : real x real with ordinary product norm ||p-theta||<r: genuine Integrable of exp(p.1*x+p.2*x^2) and the pointwise inequality against this SAME g for EVERY real x. The elaborated `have g := ...;` in the pretty-printed type is the same let expression; it adds no assumption or selector. The source proof's local r is exactly delta/2, and its local g at lines56-58 repeats exactly the statement expression. All other local objects are proved facts, not assumed envelopes or hidden definitions.

The entire used project definition/value was read at BivariateLegendre.lean lines18-22: bivariateMGFDomain is exactly the Integrable exponential set displayed above, with W(x)=(x,x^2). No log of a totalized integral, restricted test domain, finite-support surrogate, or assumed continuity enters this definition. The probability typeclass is retained unchanged; the argument does not need an additional density, moment, centering, support, nondegeneracy or integrability premise.

Source scope was checked against the original read-only C:/game/shao/current/oq3/proofs/r2/report.md: the actual W and normalized tilt at lines36-60, the open-neighborhood integrability argument at lines94-99, and bounded-only stability caveats at lines343-373; repair01.md's uniform Edgeworth input lines1-41 and far-field boundary lines212-226 were also read. CK is a valid source-bound local unnormalized exponential-envelope step. It does not certify the whole informal proof or claim the normalized characteristic function is already jointly continuous. No exponential factor is silently discarded: both raw positive exponential terms in the frozen target are retained; normalization is a later obligation.

# Full proof review and primary API conditions

- Lines24-27: Metric.isOpen_iff is applied to the genuinely open set interior D and the actual hypothesis theta in that set. It yields delta>0 and ball(theta,delta) contained in interior D. Choosing r=delta/2 gives both r>0 and strict r<delta. No closed-ball endpoint is mistaken for an open-ball point.
- Lines28-35: both corner distances are proved exactly r using the ordinary Prod supremum/MAX norm. Their coordinate differences are (r,r) and (-r,r); max(|r|,|r|)=r because r>0. There is no Euclidean sqrt(2) factor in this norm. The proof's `change` operations agree with the actual norm instance.
- Lines36-49: dist_eq_norm and the exact norm identities show both corners are in the delta-ball. hball puts each in interior D, and interior_subset puts each in the FULL true D. The strict half-radius argument is valid for both corners.
- Lines50-60: membership in D definitionally supplies genuine Integrable of each literal corner exponential. Integrable.add supplies Integrable of their explicit sum g. Each exponential is positive, so g is nonnegative on every real input. The proof does not infer integrability merely from a finite-looking value of a totalized Bochner integral.
- Lines61-67: ||p-theta||<r is definitionally max(|p.1-theta.1|,|p.2-theta.2|)<r. Both absolute coordinate bounds follow by le_max_left/right. Their required consequences are theta.1-r <= p.1 <= theta.1+r and p.2 <= theta.2+r. A lower bound on p.2 is not needed since x^2>=0.
- Lines68-82: for x>=0, multiplication preserves p.1<=theta.1+r and p.2<=theta.2+r, so the phase is bounded by the PLUS corner. For x<0, theta.1-r<=p.1 reverses under multiplication by x<=0 and gives p.1*x <= (theta.1-r)*x; the square term still preserves order. This is exactly the MINUS-corner phase. In both branches exp monotonicity gives the selected corner exponential, and the other nonnegative exponential enlarges it to g. All x are covered, including x=0, arbitrary atoms, either sign and arbitrarily large absolute value.
- Lines83-87: the target exponential is continuous as a real exponential of a real polynomial, hence AEStronglyMeasurable for the real Borel domain. Integrable.mono' requires exactly that measurability and an a.e. bound ||f(x)||<=g(x). Since f(x)>0, its real norm is f(x); the previously proved pointwise bound yields the a.e. bound via Eventually.of_forall. Therefore the returned Integrable conclusion is genuine and uses no assumed envelope or continuity conclusion.
- Lines1-23 and88-90: imports, namespace, noncomputable section, whole header, explicit statement value and closing scope were also reviewed. There are no extra declarations or unreviewed proof fragments.

Primary pinned mathlib sources and exact conditions were inspected read-only:

- Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:835: IsOpen s iff every x in s has epsilon>0 with ball x epsilon subset s.
- Mathlib/Topology/Closure.lean:43-47: interior is open and interior s subset s, without assuming s itself open.
- Mathlib/Analysis/Normed/Group/Constructions.lean:235-243: the actual Prod norm is max of coordinate norms.
- Mathlib/Analysis/Complex/Exponential.lean:313-318: for arbitrary real arguments exp a<=exp b iff a<=b, with no positivity restriction on a or b.
- Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:58-60,104-106,420-423: Integrable is AEStronglyMeasurable AND HasFiniteIntegral; mono' requires the norm bound; add requires ContinuousAdd, which real addition satisfies.
- Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:237-243: Continuous.aestronglyMeasurable requires OpensMeasurableSpace on the domain, a pseudometrizable codomain and second countability of either; all hold for real-to-real maps.

# Dependency qualification and exact environment reuse

The sole direct project dependency BivariateLegendre.lean has SHA256 d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58, 4608 bytes/114 lines. That exact hash was independently measured in the curated local library, lead server worktree, and the accepted object producer's source worktree integration-bearing-v43. It equals the entry Shao/Probability/BivariateLegendre.lean in the qualified root-v60 source map.

Root receipt library/verification/receipt-v60.json independently hashes to c495f3cdf715a69339b1754bbdce781603b83b75aeeb62792406acaeba969275, 91784 bytes/974 lines. It is PASS, checked code c82108f6077d18ac3207e52f0363537dc6408658, tree 1039e99c304847135abaeefa23b635e3f8084350, pinned Lean leanprover/lean4:v4.36.0-rc1, mathlib 807d3836b165983210ee2ecf3cd28f239436949c; all seven recorded aggregate commands exit0, including all-declarations and module coverage, and qualified_complete_reviews_before_gate is true. Its explicit prior-source/artifact reuse is used here; no unchanged dependency proof/report or old gate was commissioned again. These checked-code identifiers are not conflated with a main merge/notice commit.

The actual accepted-source-view BivariateLegendre.olean resolves to integration-bearing-v43/.lake/build/lib/lean/Shao/Probability/BivariateLegendre.olean, SHA256 0379679ed486ae83d6e50e68a24bd3a5520f2f06025dae6439b5a4b6a8ba6e25, 68600 bytes. The matching producer source has the same d8bd5dc7 hash. The lead has no local build-tree BivariateLegendre.olean; this is consistent with the declared accepted-source-view reuse. The CK olean exists, SHA256 60697f7fb77677c01e623df9af412c147c92c183fd8264f7594c2a4c323b934f, 202328 bytes. Hashing these existing objects is observation, not a compiler replay or a new proof claim.

The original server dependency-source-binding.json was read completely: SHA256 3d36101c74e055a6ce5744e048fbfe0799039db50ff970d906cff37f011b8373, 467 bytes/10 lines. It records the same exact source, root-v60 receipt and checked-code identifiers and a before-first-kernel binding. The lead lean-toolchain and lakefile were read: they pin the versions above and autoImplicit=false. The mathlib symlink resolves to cache-overlays/shared-v34/packages/mathlib, as prescribed. Existing root qualification is reused only for the imported definition's original scope, not as new OQ3 root closure.

# Original server gate and whole-owned axiom coverage

Both ORIGINAL saved logs were read in their entirety and independently hashed on the server. No check was rerun.

| Saved log under the server run | SHA256 | Bytes | Lines | Recorded outcome |
| --- | --- | ---: | ---: | --- |
| build-01.log | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 | 133 | 2 | First kernel attempt1, exit0, 4.854532063007355 seconds |
| audit.log | 2e6f3a5a92d0705526bf4096f2fa73a5bda108ca63b2bc27a7ad651f068d8ed6 | 1287 | 25 | First ownership/recursive-axiom audit, exit0, 5.442293280735612 seconds |

Both receipts use affinity14-17, native memory8192MiB, jobs4, autoImplicit=false. Build history has exactly attempt1 for this complete source hash and first_complete_success_attempt=1. The complete kernel log contains only the known two-line Lake warning that mathlib has local changes; it contains no Lean error or source warning. The complete audit log adds the exact actual theorem/type, its three axioms and the five final counts/PASS lines.

The full 47-line Audit.lean was checked. It first validates the frozen theorem target, then traverses ALL environment constants using env.getModuleIdxFor? and env.header.moduleNames to select actual owner module Shao.OQ3.OpenDomainExponentialEnvelope. This is NOT a public-name-prefix audit. For each actual owner it rejects isAxiom, calls Lean.collectAxioms recursively, and rejects any axiom outside propext, Classical.choice, Quot.sound. It prints every owned declaration/type and the VALUE of every owned defnInfo, also catching private, generated and externally named owned constants. The original output is exactly:

DECL Shao.OQ3.open_domain_local_exponential_envelope
AXIOMS [propext, Classical.choice, Quot.sound]
KIND theorem
U22CK_FROZEN_DEFINITIONS 0
U22CK_FROZEN_THEOREMS 1
U22CK_ALL_THEOREMS 1
U22CK_ALL_DECLARATIONS 1
U22CK_AXIOM_GATE PASS

There are zero VALUE lines, and the unique actual declaration is the frozen theorem. Thus all actual owned theorem types and all owned definition values (none) are fully covered. An independent source-token scan found no sorry/admit/new axiom/unsafe/native_decide. The theorem's proof and explicit local values were also read completely; the whitelist result is not being substituted for semantic review.

One initial read-only API-location search failed because rg is absent on the server. It was replaced by read-only Python file scanning; it was not a Lean/kernel/audit attempt, changed no source and invalidates no saved gate. There were no author source or gate failures in the supplied original history.

# Accepted scope and remaining obligations

CORRECT for exactly CK170's true-open-domain local explicit exponential envelope. Saved exact-source kernel and whole-actual-owner transitive-axiom evidence are qualified for reuse with this independent complete review. This does not claim joint parameter/frequency characteristic-function continuity, a parameter-uniform middle-frequency gap, Song/Edgeworth, weighted errors, frequency integrals, exterior control, new-rho Laplace payment, or closure of original OQ3 B/D or other OPEN root groups. Corrected A, bounded C, p54 repairs, strict root-beta conditions and external-result attribution remain unchanged. No novelty claim is made for this auxiliary lemma.
