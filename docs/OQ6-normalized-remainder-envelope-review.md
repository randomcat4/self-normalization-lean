# Independent complete final review of unit 154

STATUS: CORRECT

The exact final unit154 source is correct for the frozen, limited p37(13)–(14) scope: genuine L1 integrability of the actual energy envelope, its fixed-n scalar-error L1 limit, and the literal accepted150-normalized correction/envelope estimates. No critical mathematical or statement-fidelity gap was found. This qualifies this exact limited module; it does not close OQ6, OQ56, or any other original root.

Reviewer: `/root/oq56_remainder154_final_review`, a fresh independent final-review context, separate from the mathematical/Lean author and the parent executor. Prescribed model/effort: gpt-6.1-sol/xhigh. Actual tool-exposed model/effort telemetry and all four usage categories are unavailable and are recorded as null. I wrote only `drafts/oq56/unit154/final-review-01/`. I ran no Lean, local compilation, server/network/Git/cache action, or child context. The mathematical conclusions below are my independent assessment, not an adoption of the author's verdict.

## Exact objects and evidence bindings

The sole accepted review target is:

- `author-01/stage2/repair-01/NormalizedRemainderEnvelope.lean`: SHA256 `4852a6d3a907f35b5bde7fb6aca467ba5d382799a15915e5dbad907e224b9116`, 19,128 bytes, 389 LF characters, valid UTF-8 without BOM/CR, one final newline.
- Preimplementation freeze: SHA256 `44f37aec156c27194e8bcf5901f9239156b1cf6b8482c26763a6d6c70971ebce`. Complete prefix/suffix, both full headers, all 18 complete header-let values, all 12 imports, explicit global parameters and exclusions were read. Both raw headers occur literally in the final source and their frozen hashes match. There are exactly two public theorem declarations and no additional global definitions, theorems, instances or private declarations.
- Accepted150 actual dependency source: SHA256 `7e781dc929166b43c69dd6ffe463c62e2d1508fa5283451852ea50afed18c237`. I read all four actual definition values and both complete public theorem headers/call conditions; I did not re-review accepted150 proof bodies or replay its checks.
- Actual-owned metadata: SHA256 `dd7a8f768374db2a9523b4bd900835c04c6ce7c037eb455c9ff9904fee185152`, 80,877 bytes.
- Compact owned audit: SHA256 `7b08c2d6b78e9600ddfb94eddba480a7c6148b19401c36da17a69cea6002fd4f`.
- Original-evidence selected-field projection: SHA256 `03e938b1f7152358f346d9bde5a439e8a797a6d4f21408e73448d1ac88cca516`.
- Direct kernel intake: SHA256 `f841611fdef8006ca8cc559783b2cc230e68188eb506fd502a8767cb1fcca947`.
- Author STOP: SHA256 `13fa06a15a4164c5bb2df2026033c63d5d26bd90914ae2b1560632098fdd8444`.
- Parent producer/audit intake: SHA256 `3c68c8ac54a14dfe30a8fe12dd02217674b70877737348fd0604ee52d18997e8`.
- Complete owned auditor source: SHA256 `f2d974b8c4726acb9cb58d38a1e0574f5a75579c21adec0e20f30a0be510210e`.

These local file/content hashes were independently recomputed. `input-bindings.json` records 52 exact reviewer input bindings and honest read scopes. `static-intake.json` records the independent byte/header/value/type/delta comparisons. These static checks are not represented as Lean execution.

The coordinator-owned TEAM.md changed during final hash validation. Its read-time binding is retained in the input manifest, and the selected current checkpoint/resource/audit-boundary text was read again; those applicable rules are unchanged. DONE records this permitted mutable administrative snapshot separately. All 51 other input hashes, including every mathematical source, freeze, type payload and server-evidence artifact, remained unchanged.

## Original source and mathematical contract

I read the complete local read-only p37, p38, p39, p54 and scope01, the complete Stage1 mathematical note/problem/assumptions/dependency ledger/provenance/manifests/DONE, its proposal and exact-header/value equivalence to the freeze, and the Stage2/repair notes and metadata. The Stage1 directory has no standalone hazards file: the complete boundary/hazard analysis is in proof-note sections 6–7 and was reviewed. Duplicated declaration-metadata headers/values were compared exactly to the fully read frozen headers/values rather than treated as new mathematics.

The immediate source is p37 section 3: H_z=(1+V)(sqrt(n)+z sqrt(1+B)), rho=4 epsilon sqrt(n), Deta=D1+W-Weta+z sqrt(1+D2)(Veta-V), Aepsilon=A+rho H_z, with B and both deleted choices unchanged. The signs and factors in all these literal expressions agree with p37(10)–(14). In particular, the correction uses W-Weta and Veta-V. It uses the original actual V, not Veta, inside H_z.

The local analytic statement legitimately needs neither independence nor a positive statistic denominator. Its probability-space, measurable/L2/total-energy hypotheses are sufficient for the energy theorem. The correction theorem additionally includes every genuine accepted150 centering/measurability/positive-small-epsilon/pointwise-approximation condition and measurable integrable nonnegative envelopes A,B with pointwise magnitude bounds. No desired envelope inequality or H integrability is assumed. Pointwise hypotheses are not silently replaced by almost-everywhere statements; future consumers starting from a.e. data must supply suitable global/clipped representatives.

The use of arbitrary lifted deleted functions is valid only for the unchanged identities and deterministic deletion bounds stated here. It proves no deleted-domain measurability, integrability, independence, or scalar factorization. Those requirements remain with the actual151/152 consumer. I do not certify the unimplemented canonical assembly merely from the author's discussion of it.

## Complete proof assessment: actual_energy_envelope_integrability

The entire declaration/proof at final source lines 23–176 was read. Its 21 top-level conjuncts are all covered, including the nested measurability/integrability pair for every real z.

1. Lines 65–87 establish measurable nonnegative V and V²=sum xi_i² pointwise. Each xi_i² is integrable by its genuine MemLp(2) hypothesis. The finite sum is integrable before the square-integrability rewrite, before MemLp V 2, and before EV²=1 is calculated by finite integral linearity. Thus the proof does not exploit totalized Bochner integrals to fake a moment hypothesis. Probability/finite measure converts L2 to L1.
2. Lines 88–111 establish measurable C=sqrt(1+B), C>=1 and C²=1+B pointwise. The actual integrability of 1+B is obtained from probability-measure constant integrability and hBint before the C² integral identity. This gives C in L2 and L1 and EC²=1+EB.
3. Lines 112–137 put 1+V in L2 and apply the genuine HolderTriple(2,2,1) multiplication rule to (1+V) and C. I checked the pinned source windows for HolderConjugate.instTwoTwo and MemLp.integrable_mul with their contexts. This is an L1 product conclusion. Expanding H_z into sqrt(n)(1+V)+z(1+V)C gives measurability and integrability for every real z. No step requires H_z in L2, E(V²B), a fourth projection moment, or independence between V and B.
4. Lines 138–159 use n>=1 and z>=0 exactly where positivity is required. The arbitrary-real-z integrability clause is not confused with positivity. The absolute-integral formula uses |rho H|=|rho|H only with positive H_z. Absolute integrability itself is valid for every real z and epsilon.
5. Lines 160–173 prove the exact two-sided real epsilon->0 limit by rho(epsilon)->0, continuity of absolute value, and multiplication by the fixed finite real integral of H_z. This is an L1 norm limit for rho H_z at fixed finite n and fixed z>=0. It proves neither uniformity in n nor convergence of an epsilon-indexed eta family. Those stronger claims do not occur in the actual type.

All arithmetic rewrites preserve the displayed functions. In particular the explicit repaired pointwise absolute-value equality uses abs_mul on the whole rho factor and then nonnegativity of H; it does not accidentally rewrite just a subfactor of rho.

## Complete proof assessment: actual_normalized_remainder_envelope_spec

The entire declaration/proof at final source lines 178–385 was read. All 36 top-level conjuncts are covered.

The local lets at 242–255 repeat exactly the 14 frozen values. The accepted150 call at 256–258 supplies every frozen hypothesis in the correct order. Its extracted conclusions are eta measurability, |Veta-V|<=rho(1+V), and |Weta-W|<=sqrt(n)rho(1+V), for precisely the same actualNormalizedFamily, sums, square-root energies and rho as the new header. No arbitrary eta, normalization scale, centers, or W/V witnesses are substituted. The first new theorem is called for the same xi and B; its H_z specializes definitionally to the new H.

Finite sums, powers and total real square root supply all remaining claimed measurability. From D2<=|D2|<=B, global monotonicity of total Real.sqrt gives 0<=b<=C at 274–278 even when D2<-1. This is mathematically sufficient for a magnitude estimate. Neither the statement nor the proof asserts b>0, 1+D2>0, quotient validity, or equality of zero-energy events. The strict epsilon bound and positive sqrt(n) establish exactly 0<rho<1 at 279–287.

At 292–313, the proof cancels D1 to obtain (W-Weta)+zb(Veta-V). Triangle inequality, the accepted150 bounds, zb>=0, b<=C and rho(1+V)>=0 yield

    |Deta-D1| <= sqrt(n)rho(1+V)+zC rho(1+V) = rho H.

This checks both orientations of the discrepancies and all nonnegative multiplication conditions. It does not divide by V, Veta or b. The z=0 case is directly included.

At 314–333 the proof establishes genuine integrability in the required order: measurable D1 is dominated by integrable A; rho H is integrable; the measurable correction Deta-D1 is dominated in absolute value by rho H; its absolute value is therefore integrable; addition gives Deta integrable. Aepsilon and A+H are integrable sums. In particular, hIntegralError uses integral_mono only after both integrability proofs exist.

At 334–360, triangle inequality gives |Deta|<=Aepsilon, nonnegative factors give Aepsilon>=0, and rho<1 gives Aepsilon<=A+H. The B bounds and equality are literally the original B. Aepsilondelete and Bepsilondelete are literally Adelete and Bdelete. The deleted-A inequality is an ordinary triangle inequality with the nonnegative rho H perturbation; the deleted-B expression is reflexively identical. Arbitrary possibly nonmeasurable deleted functions do not invalidate these pointwise inequalities, and no analytic property of them is inferred.

At 361–380, integral monotonicity and genuine scalar/sum integral linearity give the correction L1 bound, the exact absolute Aepsilon error, and the expectation identity. The absolute Aepsilon difference is pointwise rho H, hence genuinely integrable as well, although this extra integrability clause is not separately exported. The final constructor at 381–385 puts the 36 clauses in their declared order. There is no unsupported exchange of limit/integral here.

## Boundary and nonvacuity checks

- n=1 is allowed and nonvacuous: on a symmetric two-point probability space take xi=Y=+/-1, A=B=D1=D2=0 and 0<epsilon<1/4. Actual mean is zero, scale is one, eta=xi, all stated hypotheses hold, and the correction is zero. No n>=2 or U-statistic n>=3 restriction is smuggled in. n=0 is explicitly excluded, and would independently conflict with total energy one.
- At z=0, H=sqrt(n)(1+V)>0 and the correction reduces to W-Weta. For negative z, only the first theorem's all-real-z measurability/integrability claims apply; positivity/absolute-integral factorization are guarded by z>=0.
- V=0 or Veta=0 causes no undefined expression or division. Total real sqrt keeps b defined for every D2, including D2<-1; later denominator-positive source consumers retain their separate guards.
- A symmetric distribution with masses proportional to k^-5 at +/-k, rescaled to EX²=1, has finite third and infinite fourth moment. With n=1, xi=Y=X, B=X² and A=D1=D2=0, the hypotheses hold while E(V²B)=EX⁴ is infinite. For z>0, H is L1 but need not be L2. This independently confirms that the proof's factorwise L2 route avoids a materially stronger mixed-moment requirement.
- Threshold atoms are neither discarded nor used: there is no tail-event limit in this module. No normalization-family convergence or atom-safe reverse Fatou result is inferred from its scalar-envelope limit.

## Full actual-owned type, value and axiom coverage

I read EVERY full actual type string literally, in bounded contiguous line windows with no display gaps. No dictionary compression, structural summary, or unprinted duplicate-subexpression shortcut was used for this type review:

| Actual constant | Full type SHA256 | UTF-8 bytes / lines | Read windows |
| --- | --- | --- | --- |
| actual_energy_envelope_integrability | b0e328b878325ccb1f22b99fb0782c42ab5d65a370925d19a3a26e4373b186f7 | 35,761 / 459 | 1–150, 151–300, 301–459 |
| actual_normalized_remainder_envelope_spec | 378184ec5410b10945f667287377e7a3a8008a9b6b7adb3e7b10656c49de11fb | 41,534 / 492 | 1–150, 151–300, 301–450, 451–492 |

I independently rehashed the strings and their byte/line counts. Their full binders, dependent instances, let values and conjunction targets faithfully express the complete frozen statements. The expansions use the ordinary real operations, the same nu and Fin n, MemLp exponent 2, probability measure, genuine Integrable predicates and ordinary nhds(0) limit. No missing values or ellipsis were found.

The auditor selects by the actual module owner obtained from the anchor, iterates every environment constant with that owner without namespace filtering, and recursively runs Lean.collectAxioms on each. The exact inventory is two thmInfo public constants with bodies, no private/generated constants and no non-theorem full values to read. The complete values that do exist in the statements are all 18 header lets, already covered above. Both constants have exactly propext, Classical.choice and Quot.sound, six axiom occurrences in total. No unowned-name sampling or namespace-only audit is substituted. The source has no sorry/admit/new axiom/unsafe/native_decide.

## Reused original server evidence and its limits

The parent is the sole executor. I verified the exact local projection/intake/metadata hashes and their source-object-receipt agreement; I did not reopen remote original receipts, stdout, configs, objects or the remote protected-artifact inventory, did not observe their execution live, and did not independently regenerate the metadata from stdout. These are preserved parent-origin server facts reused under the current streamlined acceptance policy, not fresh reviewer executions. This limitation is explicit in qualification.json.

The origin projection binds the final source to kernel receipt `25d05c4701872160c6d46aaa2d0a40b3b9084186b75b57664d0126998c5391b6`: direct exit 0, 5.752306820824742 seconds, 2,193 protected records preserved, all owned processes ended, no timeout/cleanup/post-error, empty stdout. Its exact produced object is SHA256 `f89f94014214fdcf744c34736306886bec45ad9e73dcaee7ea7d536fbec1d49e`, 1,085,088 bytes. The author command compiled the actual source with -o and did not import its own object.

Audit receipt `6435b5c8c3dada3f03a02c9cbcedf4478e6dc9181c2b1f0e9bc924f451b59aa5` binds the same source and exact object: direct exit 0, 5.2716646771878 seconds, 2,205 protected records preserved, all owned processes ended, no timeout/cleanup/post-error. It imports that object, has no -o, and binds the complete metadata to its preserved stdout SHA256 `b36c3be0df35952cdd7288025d2008dacc4c8ae2d0d3e263d1b25e0643a5ac88` (78,387 bytes).

Both commands used the assigned OQ56 CPU22–25, native -M8192 -j4, the existing lane heavy lock and the pinned mathlib commit `807d3836b165983210ee2ecf3cd28f239436949c`. SERVER.md records the pinned Lean `leanprover/lean4:v4.36.0-rc1`; no fresh toolchain probe was performed by this reviewer.

Both strict-wrapper success fields remain FALSE. Both stderr streams contain the same preserved 134-byte Lake warning about existing local mathlib repository changes, SHA256 `11ec49f9906e54894a8ffa4551c841fd9873cf63f295722c88755032b40c3cbf`. I do not describe stderr as empty or the wrapper as clean/successful. The direct kernel/audit exits and source/object bindings support the limited mechanical gate despite this separately retained wrapper result.

The first failed source `3f71065e810baadcbb24c60918d6309988991a816815fee294e43b9bd49df94a`, failed receipt `1f5271f45c1bf64e80f0424c1499a1313be75d706750794cad69dd764b7eec88`, full bounded feedback and seven-site exact delta are retained. I read the delta and verified that its five replacement kinds with multiplicities 1+1+3+1+1 reconstruct the final source exactly. They change proof elaboration/orientation/name/pointwise presentation only; all frozen mathematics is unchanged. The failed candidate receives no acceptance from this report. No unchanged producer/audit was rerun to change formatting or warnings.

## Scope decision and remaining work

CORRECT applies only to this exact two-theorem module. The source-to-statement/proof, full actual type/value, all-owned recursive-axiom and reused exact-source server evidence gates are covered with the provenance limits just stated.

Canonical152 application/original-law pullback and original projection p0 assembly, actual151 full/deleted factorization, epsilon-indexed normalized-family convergence, all full/partial analytic-cost limits, clipping/unweighted-integrability removal, source-budget persistence, strict-buffer bad-event reverse Fatou, external Shao–Zhou invocation, Gaussian-tail division and the physical centered-row Studentizer integration remain unpaid. In particular, the p54 repair remains mandatory: uniform bounded conditional standardized p-moments, not an invented arbitrary polynomial convergence rate; actual G intersect C_n strict margins/concentration, not an envelope bad event. This review neither certifies nor reopens those separate obligations.

Shao–Zhou retain attribution for the probability engine. No novelty, priority, full probability result or original-root closure is claimed. All C12/OQ3/OQ4/OQ56 root groups remain OPEN; OQ3 remains PAUSED_BY_USER. The next source-bound mathematical dependency is the fixed-n full/partial tilted analytic-cost convergence using continuous capped weights and genuine full/deleted integrable envelopes. The present reviewer releases its assigned review directory after writing the final artifacts; no execution or writer operation remains in flight.
