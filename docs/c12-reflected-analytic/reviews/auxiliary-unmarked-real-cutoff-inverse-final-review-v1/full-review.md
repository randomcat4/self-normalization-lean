# Independent complete final review: C12 unit 182

STATUS: CORRECT

This verdict covers exactly Shao.C2.AuxiliaryUnmarkedRealCutoffInverse at source SHA256 6ad57419f8d59f43b6fb72a56ccffdd81955590a1c056b18523a86897989246a, original/imported object SHA256 6ea050acc5fe044b82cefaef3e881b8b6e49e020d670c59a197f81748b9c2f0f, and declaration/context freeze dc9884ba5d37aacf8e25c3da072df9caeab121259336e9bfc5573209385b77fc. The final corrected author receipt is 02dcf8421d8541079ac6dbf59c031a839bac76cbb842a618c06cca5d03555013 and author release is 64b744c6a5c7bc4fb0785d59e6b05873a0edf7d8cbf3be3d743772f78b3d4d28. There is no mathematical or formal evidence gap in this new unit. Two stale receipt summary descriptors were corrected by the parent before sealing; their original bytes and a harmless local JSON formatting difference are preserved and explained below.

## Independence and coverage

I was assigned this new unit as a fresh final reviewer after the author's writer and execution release. I wrote only in drafts/c12-lane/auxiliary-unmarked-real-cutoff-inverse-final-review-v1. I did not edit source, assumptions, imports, shared definitions, cache, status, inbox, registry, or another review; did not spawn agents; and did not execute Lean, Lake, an axiom audit, an old gate, a build, a commit, or a merge. RUNTIME-ACK.json records actual commencement. The requested model/effort is gpt-6.1-sol/xhigh. Backend identity and token telemetry are not independently observable here and remain null, with input, cached input, output and reasoning-subset separated.

I completely read all 286 source lines, including imports/options/context, all three declarations and every proof. I completely read all 37,907 bytes of the actual-owned type export, with all dependent lets and instances unelided. The whole-owner map contains exactly three theorem constants: one public and two private, with no generated constant and no non-theorem value to inspect. I completely read the three exact consumed public type slices, the audit implementation and owner map, the original successful kernel003 log, and the entire successful audit log by its exact prefix/type-payload/suffix decomposition. I inspected the failed-attempt exits, error locations and complete proof-only deltas. Existing qualified old proofs were bound and reused, without re-reviewing their proofs.

The exact-local-binding-map.json records 32 physically read local bindings, complete type block offsets/hashes, and exact consumed slices. The readonly-final-remote-observation.json records 53 remote bindings, including the original source reference, all receipt artifacts, the candidate source/archive/object/import, relevant qualified dependencies, native pinned API files, branch/HEAD/tree, freeze comparisons and runtime observations. All 52 expected remote bindings match; the additional reference input is freshly hashed. The unchanged source/evidence observation was made at 2026-10-25T00:55:18.872790+00:00; the five affected receipt/provenance bindings were freshly rebound at 2026-10-25T00:57:32.976347+00:00 without repeating unchanged checks. No Lean/Lake process was observed, including no process in the C12 worktree, at the source observation.

## Frozen statement and source fidelity

For each real a >= 0 and real q > 0, the public theorem chooses a positive real constant C before the probability law nu, dimension n and cutoff b. The law is a probability measure on the real line with integrable squared coordinate, mean zero and second moment one. No third moment, boundedness, atomlessness, density, or supplied inverse-moment integrability/bound is assumed. n ranges over all natural numbers, including zero, and b over all positive reals.

The actual product law is P = pi over Fin n of nu. T is the genuine sum of the n squared coordinates, and d is prefixSum at the full length n, hence the genuine full coordinate sum. I read the native definitions in FinitePath.lean lines 18–31 and the relevant measurable contracts in MeasurablePath.lean lines 53–62. There is no replacement of T by its expectation, d by a proxy, or P by an abstract moment oracle.

Let c = (1-exp(-2))/8, retained = integral z^2 on z^2 <= b, and gamma = -c when retained >= 1/2, otherwise gamma = 1. The selected integrand is

  1_{0<T and b<=T} T^(-q/2) (1+|d|/sqrt(T))^a.

The conclusion separately proves its genuine Bochner integrability, integrability on (0,1/b) of

  k(s) = s^(q/2-1) exp(gamma*s*n),

and the actual expectation bound by C times the integral of k. The encoded threshold is weak at b and at retained=1/2. The exponent q is a real, with no natural-number restriction or upper bound. All these facts are present literally in the complete public actual type, not only in prose.

I read the server reference supplement.tex lines 4431–4444 and 4474–4485 in context. This is exactly the ell=0, M0=1, a0=1, H=infinity ordinary specialization of the source damped-budget master: 1/H=0 and the count is the full unmarked n. The explicit harmless positive branch gamma=1 agrees with the already qualified ordinary producer. The source proof uses the two inverse orders q/2 and (a+q)/2 and a real-growth one-plus bound, precisely the construction here. This unit does not prove finite-H improvement, ell=1 marks, rare-event/Psi/bounded-rho bounds, physical x/time/grid/circular constraints, or the complete C2 root. Root's separately frozen rare/private heads remain hash-bound and untouched. Original finite-second-moment scope, p54 repairs and external-result attribution are unchanged. C2 and C12 remain OPEN; there is no new novelty or root-completion claim.

The full reference input has 235,015 bytes and SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd. The exact 4431–4444 slice has 663 bytes/SHA256 f0b820703003ab04fc10c0db01e67c42dd9483ba75654af684c8484cff21e7d8; the 4474–4485 proof slice has 524 bytes/SHA256 cc252f4d7460d32a12db02c4436ab90ede7027b8059f346a996a17631d8ad8df.

## Complete new proof review

### Private cutoff exponential kernel, source lines 13–46

The qualified public gamma_kernel is instantiated at alpha=q/2 and rate=1, both strictly positive. Its genuine integrability on (0,infinity) restricts to (0,1/b), after the elementary sign/product normalization of exp(-1*s) to exp(-s).

For s in this interval, positivity of s, r <= |r|, and s <= 1/b imply (r+1)s <= (|r|+1)/b. Thus r*s <= (|r|+1)/b-s, and exp(r*s) <= exp((|r|+1)/b)*exp(-s). Multiplication by nonnegative s^(q/2-1) gives the required norm domination by a constant multiple of the integrable reference kernel. Measurability is proved for the actual real-power/exponential function. Integrable.mono' therefore proves integrability of the target. The non-use of hb is only a linter warning; the interval may be empty for other b, and it is not a mathematical omission in this stronger private statement.

The dominating constant here depends on r and b. It is used only inside an integrability proof. It is never inserted into the public numerical coefficient, so this construction does not compromise uniformity in the law, n or b.

### Private real-power cutoff producer, source lines 48–178

The actual qualified ordinary real damped moment theorem supplies Ca > 0 before nu, n, b and s. It proves both integrability of |d|^a exp(-sT) and its bound by Ca*s^(-a/2)*exp(gamma*s*n) for every legal 0<s<=2/b under exactly the stated finite-second-moment law assumptions. No new premise is supplied to this interface.

Set alpha=(q+a)/2>0 and A=exp(1)*alpha>0. The private constant A*Ca is chosen before nu/n/b. On S=(0,1/b), define the actual joint function

  K(s,v)=s^(alpha-1) |d(v)|^a exp(-s*T(v)).

The source establishes its measurability and pointwise nonnegativity. The first helper at rate gamma*n supplies integrability of the actual k. For every s in S, s<=1/b<=2/b, using hb>0; the old moment theorem is therefore applicable and supplies true section integrability. Positive s allows the exact native power identity

  s^(alpha-1) s^(-a/2) = s^(q/2-1).

There is no order rounding, altered exponent, or loss of a q-dependent factor. The section integral is consequently bounded by Ca*k(s).

The proof does not infer product integrability merely from a finite-valued formal integral. In lines 120–128 it uses the nonnegative K to identify each section's integral of its norm with its integral, and dominates the actual function s -> integral ||K(s,v)|| by the genuinely integrable Ca*k. The native measurability theorem for the parameterized integral supplies the needed a.e. strong measurability. With both this outer norm-integrability and a.e. section integrability, integrable_prod_iff establishes genuine Integrable K for (volume restricted to S) product P in lines 129–130. This closes the Fubini premise before it is used.

The selected private function is the genuine |d|^a*T^(-(q+a)/2) on 0<T and b<=T, zero elsewhere. Its indicator set and branch functions are measurable and it is nonnegative. On the selected event, the public inverse_laplace contract at (alpha,T,b), halpha, hb and b<=T gives T^(-alpha) <= A times the scalar Laplace integral. The exponent -(q+a)/2=-alpha is normalized exactly. Multiplication by the nonnegative |d|^a, constant extraction and an integrand ring equality give selected(v) <= A*integral_s K(s,v). On the complement, selected=0 and the latter integral is nonnegative. This step invokes an independently qualified scalar identity, not an assumed random-variable inverse-moment bound.

Product integrability already established above gives genuine integrability in v of the inner s integral. Domination by it proves Integrable selected, using actual measurability and nonnegativity. The final estimate uses integral_mono between integrable functions, true integral_integral_swap, the section estimate, integral_mono_ae with integrable outer functions, and constant extraction. It yields exactly A*Ca times the actual k integral. There is no circular integrability argument and no unverified exchange of improper integrals.

### Public real normalized-growth master, source lines 180–284

The two private producers are instantiated at real orders 0 and a with the same real q>0. The proof chooses D=2^a>0 and C=D*(C0+Ca)>0 before introducing nu/n/b. The zero-order instance is converted to F0=T^(-q/2) on the selected event, using |d|^0=1, including d=0; the explicit local-let normalization in the passing version preserves the exact actual product law, T, retained and gamma. Fa is the actual |d|^a*T^(-(q+a)/2) selected function. Both are genuinely integrable, so D*(F0+Fa) is integrable.

The within-proof real-order inequality is complete for every u>=0 and a>=0. If u<=1, then 1+u<=2, so (1+u)^a<=2^a<=2^a*(1+u^a). If u>1, then 1+u<=2u and native real mul_rpow gives (1+u)^a<=(2u)^a=2^a*u^a<=2^a*(1+u^a). This includes a=0 and u=0. It does not rely on an old natural-order inequality for a real exponent.

On the selected positive-energy branch, the actual u=|d|/sqrt(T) is nonnegative. Native div_rpow and rpow_div_two_eq_sqrt, followed by rpow_neg, establish

  (|d|/sqrt(T))^a = |d|^a*T^(-a/2).

Positivity of T justifies native rpow_add to combine T^(-q/2)*T^(-a/2)=T^(-(q+a)/2). Thus the selected public integrand is bounded pointwise by D*(F0+Fa). Off the event all three selected functions are zero. No manipulation requires division by zero on a branch where it is used.

Actual measurability of T,d, sqrt, division and constant real powers proves measurability of the complete selected function; nonnegativity is explicit. Domination by the integrable sum proves its genuine integrability. Finally integral monotonicity, integrable addition, the two private numeric bounds and ring distribution yield C=D*(C0+Ca). All coefficient dependence is limited to a and q. The kernel-integrability component is inherited without changing gamma. This closes every conjunction component in the literal frozen public statement.

## Boundary and hidden-premise attacks

- a=0: the powers of |d|, including 0^0, use native rpow_zero=1; D=1 and the private zero-order specialization is definitionally normalized. The result remains an ordinary inverse cutoff estimate.
- q arbitrarily small positive: q/2 remains positive and q/2-1>-1 at the origin. The gamma-kernel reference covers precisely this range; no assumption q>=1 is hidden. q=0 is excluded as frozen.
- n=0: the true sum and energy are zero, so the selected event is false for b>0 and selected is zero. k(s) reduces to s^(q/2-1), which the helper integrates. There is no subtraction of a marked coordinate or covert n>=1 assumption.
- zero-energy atoms and zero full sum: the energy-zero branch is excluded by the selector; when T>0 but d=0, all native nonnegative real-power identities and the a=0 convention are valid. No atomlessness or nonzero-sum assumption is needed.
- b=T>0: the indicator includes equality and inverse_laplace requires exactly b<=T, so the cutoff boundary is covered.
- retained=1/2: the formal condition 1/2<=retained selects -c exactly as in the source. The positive gamma branch is also proved, not replaced by an always-decaying exponent.
- Large real a and laws without third or higher moments: only the qualified all-real *damped* moment interface is consumed; it already provides section integrability for legal positive s. No bare higher moment is introduced when integrating down to zero: its power loss is cancelled exactly, and the remaining q/2 kernel is genuinely integrable.
- Universal constant order: the private A*Ca and public D*(C0+Ca) are chosen before the law, n and b. The separate integrability-only domination constant exp((|gamma*n|+1)/b) cannot enter those coefficients.

I found no counterexample, strengthened hidden hypothesis, weakened quantifier, abstract oracle, finite-case substitution, or surviving proof gap.

## Pinned API and imported evidence checks

The worktree toolchain is leanprover/lean4:v4.36.0-rc1 and mathlib HEAD is 807d3836b165983210ee2ecf3cd28f239436949c. I read the critical native integrable_prod_iff, parameterized integral measurability, integral_prod_left/right and integral_integral_swap contracts in Mathlib/MeasureTheory/Integral/Prod.lean, and native rpow_add, rpow_neg, mul_rpow, div_rpow, rpow_le_rpow and rpow_div_two_eq_sqrt in Mathlib/Analysis/SpecialFunctions/Pow/Real.lean. Both entire active files were compared byte-for-byte with git show of the pinned commit and match. Their SHA256s are respectively 8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05 and f8a26d662fb7966fa5b45aef95c8d7cf0383c9921fa3e9ee1cd2c41561e9fbfd. Thus the repository-local-changes warning does not undermine these actual API contracts. P is a finite probability product and the restricted Lebesgue measure is sigma-finite; the native measure-class prerequisites for these uses are satisfied.

Qualified unit179 evidence is reused at parent-acceptance SHA256 c9ae599ed490c31d4c348999ead6647b5705b22fef0f665bb12a1895bcf09884, source f93568a407994566c92a9c6a3ec19c8dfeb7fc4dbea2baae70924166a256f22c, imported object 22353179749cc5ed25f7b6014272011b26e59c6fb805d4af6f634cbdf106dc58. Its already accepted full review, structured report, reviewer release and validation hashes were checked against that qualification without performing a new old-proof review. The consumed public actual-type slice is 13,765 bytes at offset 10,804 of the qualified export, SHA256 81845222c3b753ff59254d4dc7fe1296545023e706b94de13db9ef7525a93004; it is literally equal to the lossless consumed file and was fully read.

Root scalar qualification is reused at SHA256 2a2ca77941fa9500843582dc57681d01260abfd2abae7f0d1cab331e6ceb6c26, canonical source f96f193c561a3d6e486f1cde02f009a2af31793f517b326cc65dc556baf9e5bc, original/exported object 4f72de6085a4c06e3d683846305db91de09ca91f6c742727dcda7dfe7b414f0b. Its qualified complete report, structured report and owner-map bindings match. The public gamma_kernel complete type is the exact 3,514-byte qualified export slice at offset 4,467, SHA256 6bdcfbfc658de4ea8bf5c75c3893cf8ce4dffcdfd8ea10c4d29585eb5c5c4c9b. The public inverse_laplace type is the exact 2,190-byte slice at offset 2,277, SHA256 7ffadcf8609fc4eb4d934eaf620350acbfa24d12f60fcbdb77d623b17c3af79b. Both were completely read, and all instantiations and hypotheses above were checked. Shared/scalar source is intentionally absent in C12's source checkout; I used the canonical qualified fallback and verified the actual exported objects rather than requesting a cache/source rebuild.

## Whole-owner audit and original kernel evidence

OwnedAudit.lean selects every constant by env.getModuleIdxFor? and equality with the exact target module. It does not filter by namespace or a public-name prefix. The one public-name list is only a completeness check. For every selected constant it executes Lean.collectAxioms, checks the transitive result against propext, Classical.choice and Quot.sound, records kind/type and prints a definition value if kind is definition. The actual map has exactly the three source theorems, including both private helpers. All three have only the three permitted standard axioms. There is no extra generated owner, axiom, opaque value, definition or other kind requiring additional value review.

The complete actual-type blocks are: private real-power producer, offset 0, 17,505 bytes, SHA256 20a35c7ae49faa71cf66c1d4dec02e16a4401884375400b9158e2b1e21e1f79a; private kernel integrability, offset 17,505, 2,572 bytes, SHA256 d282a93e96308d7e3c4408d7744a3ebd456d24edf7318c67b40bbb9b391dce86; public master, offset 20,077, 17,830 bytes, SHA256 4a6b80b96a83dad134a2c5e6f7b4418a3362148b3950e880b3171e2183ca67de. These exhaust the 37,907-byte export b916c09d57c57b560722bef1496adb575e3fef4e55144dfeb79fcbe35cfff424. The definition-value export is genuinely empty, SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.

I reconstructed the entire 38,118-byte saved audit log: the 150-byte repository-warning prefix, the full exact 37,907-byte type payload at offset 150, and the complete suffix reporting AUDITED_TARGET_CONSTANTS 3 PUBLIC 1 THEOREMS 3 DEFINITIONS 0. Its original SHA256 is 508a9bf58e2054cef5ed350c1db5dffc84e7045f2b21f77a8fe49fb2a58dd81b. The original audit exit is zero. No omitted type/value/log tail is accepted on the basis of a short summary.

The original source-bound kernel attempt003 exited zero, using CPU14–17, c12-heavy.lock, -M8192 and -j4, with object output in the unit's original output folder. I read its entire 2,946-byte log, SHA256 c3aa157988d6543a11a8cdd4ace407a8b7ea957fd47f942f34cdd8b815640c14. It contains only the known mathlib working-tree warning, one unused hb warning, two letI style warnings and deprecated if_pos/if_neg warnings. There is no error or unsolved obligation. The original object's bytes match both the original output object and the actual C12 import object. I reused this successful receipt and the exhaustive audit without rerunning either.

The complete imports/context and all three head strings were independently reconstructed by regex from the current source and every archived attempt. Each reconstruction is literally the 3,109-byte frozen payload dc9884ba5d37aacf8e25c3da072df9caeab121259336e9bfc5573209385b77fc. The freeze record predates implementation and gates. Original attempt001/source dbb9d76e289b066c5d299751b288f55a75e67b6b0efcb6f3e684e4e790fe64b3 and attempt002/source fbf34051a8e43c157e8e0f569c50ffe1d34e3d4c37d6881d7db1eb890705f4b6, their commands/logs/exits, remain preserved and freshly hash-bound. Attempt001 had four local normalization/tactic failures; attempt002 retained only the zero-order local-let normalization mismatch. The full diffs show proof-only repairs: explicit division normalization, removal of a no-progress simp, associative/ring normalization, and explicit local-let unfolding in the zero-order specialization; attempt003 also simplifies the helper's equivalent multiplicative normal form. There is no changed declaration, new premise or bypass. All final affected proofs are covered by this review and the exact passing kernel receipt.

The exact new source is UTF-8 without BOM and has zero CR bytes, before the first source-bound gate by the preserved attempt archive; the final source and attempt003 archive agree. The forbidden token scan of the full candidate found no sorry, admit, axiom, unsafe or native_decide. No cache/module/toolchain change was performed by this reviewer.

## Evidence metadata discrepancies and disposition

The original author receipt's top-level allTypesComplete descriptor incorrectly named the preceding auxiliary-real-marked-moments-v71 export and its 27,485-byte hash. Its allNonTheoremValues descriptor likewise named the preceding unit's empty value export. These two stale descriptive fields were never used as authoritative evidence. The original receipt's unit182 artifact map already correctly bound the original unit182 actual-owned-types.txt at 37,907 bytes and actual-definition-values.txt at zero bytes; those artifacts, the actual owner map, original full audit log and source/object receipt all matched independently. I derive all accepted counts and review coverage from these verified unit182 artifacts.

Before final sealing the parent repaired only the two descriptors and added provenance. I compared the corrected and original JSON: all original artifact entries and all mathematical/kernel/audit/source/object/frozen fields are unchanged; the only changed original semantic descriptors are allTypesComplete and allNonTheoremValues. The additional artifact entries bind the archived original receipt/release and correction note, with one new receiptMetadataCorrection field recording that repair. The corrected descriptors now point to the exact verified unit182 exports. I freshly checked the corrected receipt and RELEASE, both archived originals and correction note against their remote bytes. The old receipt is preserved as receipt-construction-original.json at SHA256 68f15eb3976581533c847407a07080a52545727e356f3567366a1f40d266b46f and the old release as release-construction-original.json at SHA256 7b1c2e3a5ecdf5bba3b7eee4cc1a149a2b796dca2ca4c54df64152fb2babbfc5. The correction note SHA256 is 887373e5cbeef97fb7c57938315cb9ae2dabc23980a906ac9d62922f39635804. The new RELEASE explicitly releases writer/execution, heavy=false and inFlight=[]. The mathematical subject and successful checks are unchanged; no Lean/audit replay occurred. The final verdict is bound to the corrected receipt/release hashes given at the start of this report.

The local preflight-observation.json is a compact JSON serialization, 3,479 bytes/SHA256 40f9824606dc773c29fb1890e225acae7b5122d380e49f453356def0ab9c7cfb, whereas the receipt binds its original remote serialization at 3,823 bytes/SHA256 81edde20920eab53c2808153f9b46a3704e3fc35725c31a8fc7b747a820613a8. I freshly read and hash-checked the original remote file and compared parsed objects: they are exactly equal. The local map records its real local byte hash; the final remote observation records the original remote bytes and fresh current source/object bindings. This is formatting provenance, not a changed mathematical observation.

A read-only API-location query first failed because rg is absent on the server; I used a read-only Python text search instead. No Lean/audit command, source mutation or uncertain write occurred. An initial local binding assertion exposed the preflight serialization difference before the successful semantic-and-byte-separated validation. Both issues are resolved within review collection and do not alter accepted evidence.

## Final source-bound disposition

At the final read-only observation, the C12 branch is author/c12-cutoff-moment-continuation-v71, HEAD 4378e48f9eea49296924f8621b63df63f8cadd0e and tree 7a9fa222be8e10c9da9a70c58f7a748d95c3b965. The tracked worktree status is unchanged. Candidate source, all three archived heads, original kernel/audit receipts, original/imported object, qualified dependencies and the two pinned native API files match the exact bindings above. The raw logs remain on the server; only hashes, framing and findings were saved locally. There is no in-flight reviewer execution.

The source-to-statement translation, every new proof, every complete owned type, all zero-value coverage, exact consumed interfaces, their interactions, all stated edge cases and all-owned transitive axiom evidence pass. Verdict CORRECT for this exact unit only. Parent acceptance and any publication/integration remain the parent's responsibility. This report does not authorize a change to assumptions or claim completion of C2/C12.
