# Independent complete review — SourceLateOmittedSuffixBudget

Status: **CORRECT — QUALIFIED_COMPLETE_INDEPENDENT_REVIEW** for the exact source and explicitly limited mathematical scope below. Complete original-source-to-statement/proof review, all 9 actual unelided types, the sole non-theorem full value, every recursive axiom result, same-original-object bindings and immutable author publication/release evidence have all been read and validated. No critical mathematical or evidence gap remains for this unit. Root acceptance/integration is a separate coordinator action.

Reviewer: `/root/late_omitted_suffix_final_review`, separate from author `/root/permutation_reveal_candidate` and Root. Configured model/effort: `gpt-6.1-sol` / `xhigh`, fresh context. Actual runtime model/effort telemetry and input/cached-input/output/reasoning-subset counters are unavailable and recorded as null. No subagents, Lean, axiom checks, heavy commands, source/cache changes, Git or API writes were performed by the reviewer. Only this review directory is writable by this role. The math-theorem skill was used; math-ultra was not used.

## Exact scope and byte bindings

The reviewed source is `drafts/c2-late-omitted-suffix-production/SourceLateOmittedSuffixBudget.lean`, 42,556 bytes / 762 lines, SHA256 `23178ba87c6edb340724b81559a398912f5d6791f93b1b02a2067e1343f0992d`. It is UTF-8 without BOM and LF only. Reviewer-side deterministic comparison independently confirms the complete frozen context, 3 theorem heads, all 21 literal statement lets, and the single local measurable-space instance. There are no extra explicit global definitions or theorem heads. Forbidden-token scan has no matches for sorry, admit, axiom, unsafe or native_decide.

The root freeze receipt is SHA256 `417bb4d9153576dcefc5c4da8692b0a0b0e32f0a55fe5b51e9b062357865590e`; public freeze `995d938a6b32fcb06932e0660c699101e5520822a5171f9b4fe87b13dcfc5b9c`; private freeze `48b43c67c049c3be996483c0c8b8b015a1fb56b9e5f85c869bf7b5b3c9ac2e08`; production activation `0023707d2db2cd5d6b364f7380a70e63f8e8ad057ab135f1b39fcca1182ece1d`. Each was independently hashed locally. Per-head hashes are recorded in `binding-validation.json` and match the author comparison exactly.

The historical opening comment says declaration preparation; the frozen prefix was retained while the explicit later production activation authorized the bodies. It is not an assumption or an execution receipt.

All source lines 1–762 were read completely, including imports, namespace/options, local instance, both private proofs and the public proof. Original read-only main.tex lines 1299–1325 and supplement.tex lines 4896–4950 and 4978–5044 were read completely. Original full-file SHA256 values were independently checked: main `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`; supplement `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

## Source fidelity and assumptions

The public head at lines 443–475 fixes `K=2^64`, then chooses one positive C before rho/n/x. The input is an actual real probability law with genuinely integrable second and absolute third moments, mean zero and second moment one; n is positive, x is at least 16, and u is at most exp(-3x²). All beta/delta/u/h0/H/m/P/nu/tau/W/lateOmitted lets match the frozen values exactly. In particular h0=4 beta², H=K beta²(1+x)^6, m=Nat.ceil H, P is the actual finite iid product, nu is the strict-low-energy h0 cutoff and tau is min of the H cutoff and n-m.

The output pays the actual nonnegative late omitted **suffix bill** in supplement 5025–5032, with the same sample and the same label permutation, and proves its measurability, genuine Bochner integrability and both stated bounds. The original bounded auxiliary law is a subclass of these finite-third-moment auxiliary laws. This does not silently add a third moment premise to an original finite-2/p-law root theorem: no original-law return is claimed here.

No support, atomlessness, target integrability, conditional-iid, wall-profile, survival-probability, terminal-budget or abstract target-map premise has been added. h0≤H and beta≥1 are proved using the accepted moment interfaces. The actual source does not need the stronger original residual consequence m≤n/4 for this standalone nonnegative bill.

The local instance at line 25 is exactly `(n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤`. Its complete source and actual elaborated value were read. The imported reveal law uses the same discrete seed structure. The public actual type uses the new local instance for measurability and the imported local instance for reveal-law integration; both full values are definitionally `Top.top`, so their agreement is verified rather than assumed.

## Private scalar proof, lines 27–269

`los_finite_geometric_grid_integrals` keeps c>0, b≥1, H≥b, arbitrary N, m≥1 and m≤2H explicit. Its three lets are I=(0,1/b), the shifted finite sum, and the ordinary finite sum. No integrability or target bound is assumed.

Lines 48–57 establish the genuine s^(-1/2) integral on (0,B], equal to 2 sqrt B. Lines 58–140 prove, for arbitrary positive A and B, actual integrability and integral bound 4 sqrt A for s^(-1/2) min(A,1/s) on (0,B). The proof dominates an indicator by A s^(-1/2) on (0,1/A] and s^(-3/2) on (1/A,infinity). Both pieces are genuinely integrable and have integral 2 sqrt A. The split is a Lebesgue parameter split, never deletion of a rho atom.

Lines 141–171 prove the two finite geometric estimates, sum≤length and sum≤1+1/v for v>0. The constant 1 is retained. The exponential inequality exp(v)≥1+v proves the denominator estimate; there is no false bound of the full geometric sum by 1/v. N=0 remains valid.

Lines 172–202 prove actual integrability of both finite sums by length times the integrable power envelope before invoking integral comparison. The shifted estimate in 204–231 uses 1/(s+1/H)≤min(H,1/s), pays the separate constant power integral, and obtains (2+4/c)sqrt H. The ordinary estimate in 232–269 uses **only** 0<s<1/b≤1, giving 1+1/(cs)≤(1+1/c)/s, alongside the finite-length bound. It obtains 4(1+1/c)sqrt m≤8(1+1/c)sqrt H. The b≥1 guard is used and must not be removed. All comparison integrals have integrability evidence.

## Private iid grid proof, lines 271–441

`los_iid_omitted_suffix_grids` chooses c=(1-exp(-2))/8>0, the finite-cutoff constant CF at a=5,q=1, and the ordinary marked constant CS at p=5,q=1 before rho/H/N. Its positive witness is CF(2+4/c)+8 CS(1+1/c), independent of rho/H/N.

The six literal lets are beta, h0, m, Pt(k)=rho^(k+1), low and ordinary. Every k≥0 therefore has a genuine first marked coordinate in Path(k+1). The two master heads and their complete contexts/selected/kernel values were read in the accepted-interface capsule and independently compared to the immutable library source. They require finite2, centered unit2 and positive cutoff, not a hidden high moment or target budget.

Lines 311–324 derive beta≥1, h0≥1, positivity, the actual retained second moment ≥1/2, and ceil(H)≤2H. Thus the master's gamma is the actual -c branch. Lines 334–361 instantiate each master with the same rho, h0 and H, convert rpow(T,-1/2) to 1/sqrt T on the positive selected event, and preserve the fifth power. The masters provide genuine selected and scalar-kernel integrability. Lines 362–376 prove measurability directly from actual finite-path energy/sum/mark functions.

Lines 378–386 separately show 0≤a3(s)≤beta for s≥0 by an actual h3 integrable envelope. Lines 387–428 form finite kernel sums and apply the scalar lemma to integrable comparison functions. Lines 429–441 use finite integral/sum interchange with each kernel's integrability already known, then add the two bounds. N=0 is covered. The ordinary range min(N,m) includes k=m-1 whenever N≥m, hence the actual t=m term.

## Same-seed public proof, lines 443–760

The public witness C=Cg(1+(8/3)sqrt K) is selected at 479–481 before rho/n/x. All subsequent law/threshold dependence is introduced later. The same witness pays both conclusions.

Lines 500–540 define the actual Path(t) product law and selected suffix functions, then construct the fixed-r prefix/suffix product split using the pinned finite-Pi coordinate equivalence and product projection. Lines 541–562 construct the actual canonical iid sample coordinates, apply the accepted random-permutation pushforward theorem, and obtain the unconditional distribution of each fixed suffix of the same reordered path. These are derived identities, not target-map hypotheses. The complete map and local functions were read in the source.

Lines 563–594 use the accepted `gaussian_weight_source_state` geometry on the reordered path, and exact finite-permutation invariance of total energy and total sum, to identify the suffix energy T, suffix sum d and first mark b=a(sigma r). It consumes only the geometry components, with signs empty/closed false, not a Gaussian profile or wall-probability conclusion. The same p.1 and p.2 are used in nu, tau, T, d and b.

The exact cutoff identity at 596–600 is `{tau≤r<nu} ↔ {h0≤T} ∩ ({T<H} ∪ {n-r≤m})`, under proved positive thresholds. Lines 601–627 prove genuine measurability using that equality; no measurability of an arbitrary stopping selector is assumed. Lines 638–658 give the pointwise nonnegative union domination. It is valid to double-count the intersection. No step asserts a suffix remains iid after conditioning on the selected mask.

The final actual integrability route differs from the preliminary proof-map's redundant independent finite2 energy-envelope route. Lines 582–585 transport the two accepted masters' genuine selected integrabilities through the actual fixed-suffix IdentDistrib; 628–637 combine them into an integrable majorant; 659–665 use pointwise nonnegative domination and finite summation to obtain the actual stopped bill's genuine integrability. This is a valid proof-body choice under the unchanged frozen statement. It is explicitly documented by the author in final-proof-route-and-scope.md. It adds no assumption and uses no circular target integral. The standalone finite2 energy envelope described in the candidate remains mathematically valid, but is not falsely credited as implemented production code.

Lines 666–729 integrate only genuine integrable functions. The rank map r↦n-r-1 is injective on actual late ranks, with t=k+1 and k in range(floor(n/2)); the short branch additionally gives k in range(min(floor(n/2),m)). The source proves inequalities into the positive grids, not an incorrect midpoint equality. Missing grid terms are nonnegative. The constant multiplier 1/n is nonnegative because n>0.

Lines 730–760 first enlarge Cg to C, then prove sqrt H=sqrt K beta(1+x)^3 and beta sqrt H/n=sqrt K delta u. The accepted scalar tail comparison applies at y=x,A=3x² using x≥16. Together with u≤exp(-3x²), it gives the same integral ≤C delta standardNormalTail x. Tail nonnegativity is proved. No exponential surrogate is silently substituted for the actual Gaussian tail definition `(gaussianReal 0 1)(Ioi x)` converted to real.

## Boundary and atom audit

- T=h0 is included by the closed lower-energy gate. T=H is excluded from the low branch, while the short branch remains possible. No rho atom is removed.
- A concrete Rademacher law with beta=1, x=16, integral H=2^64*17^6, m=H and sufficiently large n has r=n-H, T=H and t=m. Its actual omitted gate is active although T<H is false. The production ordinary grid includes k=m-1 and pays the positive W term. This directly tests both equalities under the real public residual premise.
- Current T=0 is excluded by h0>0. Future T'=T-b²=0 is retained: the same geometry gives d=b, sqrt T=|b| and W=32b² on the current selected rank. Neither source branch imposes T'>0 or deletes this atom; both old selected masters still apply.
- Repeated numerical values remain distinct labels. The seed is one uniform permutation of all original labels.
- Every r is Fin n, so r=n is absent and suffix length is positive. n=1 and n=2 have no actual late rank; N=0 and finite empty sums are supported. Odd and even n are handled by positive enlargement, including the extra even midpoint only on the upper-bound grid.
- H integer gives m=H, while a noninteger ceil still obeys m<H+1. The last t=m term is included. Lebesgue split endpoints at 1/A are unrelated to sample atoms.

## Reuse of qualified imported evidence

The complete 981-line accepted-interface/value capsule was read, including scope exclusions. All 9 mapped head excerpts in 8 consumed main modules were compared against the actual immutable source after deleting only the final `:= by` proof delimiter from the source excerpt and trimming line-end spaces. All match. All 22 source-map rows and 6 reference bindings in source-inputs.json were hashed and matched; all 22 are exact in accepted-v93's source map. This is a metadata parse/hash validation, not a second complete review of old proofs.

For each of the 8 primary consumed modules, the exact old source, original successful object identifier, prior accepted receipt and qualified complete-review digest were bound. Each local prior receipt and qualified-review artifact has the expected hash. Full old proof reviews are reused, not commissioned or replayed. The retained v93 sources remain unchanged in curated v94. Source MarkedSuffixAveraging/FiniteIID/Spitzer/MeasurablePath/FinitePath/GaussianTail definitions and relevant measurable contracts were also read as consumed transparent interfaces, with their accepted bindings reused. The absence of an exposed direct historical MeasurablePath review path is already a baseline limitation; its exact accepted source/original object credit is inherited, not invented.

The pinned Mathlib interface receipts were read in full: finite-Pi coordinate equivalences/projections, IdentDistrib integrability/integral transport, interval rpow integrability and integral, positive-half-line rpow tail, and finite geometric identities. Their pinned commit is `807d3836b165983210ee2ecf3cd28f239436949c`; Lean is `leanprover/lean4:v4.36.0-rc1`. No old producer was recompiled, and no old axiom sweep or complete proof review was replayed.

A bounded read-only actual-source follow-up filled the ambient Fintype/measurable-space/SigmaFinite contexts for finite-Pi equivalences/evaluation/projection and the full contexts for IdentDistrib.comp/trans/integrable_iff/integral_eq. These actual Mathlib source hashes match the already pinned interface receipts. The finite product hypotheses are supplied by the real probability law and finite index types; no unidentified measure-preservation premise remains. The extra directly consumed `Shao.prefixSum_length` head and `standardNormalTail` definition were read from the exact immutable library sources as well. These are interface/value checks, not repeated old proof qualification.

## Original successful kernel evidence

The complete original whole012 receipt was read: natural exit 0 at 2026-10-25T10:08:58.708224+00:00; target source hash as above; server-only native -M8192 -j4, CPU40–43 under the original root-heavy flock. The original successful object is `/root/rivermind-data/shao-lean-20261021/outputs/common-late-omitted-suffix-v93/producer012.olean`, SHA256 `1530bda1601b96c038ca5d62735b3c32de47f467ac55e34f1447e536d636e1df`.

Reviewer read-only observation at 2026-10-25T10:17:26.102558+00:00 independently bound the current remote source and attempt012 snapshot (both 42,556 bytes, exact reviewed SHA), the original object (2,315,880 bytes, exact SHA), and original kernel log (9,319 bytes, SHA `8b1ad2b099d9082f1a1824d2b4d347ffc5dc6d449c99900fb9656fe6b2425e03`). The log has 0 error lines and 41 warnings: known pinned-mathlib local-change warning and unused/unreachable/deprecated-ite linter warnings. The full log remains on the server; only compact bindings/summary remain locally. No reviewer Lean process was launched.

Partial006/009 successes and earlier failing whole attempts are not promoted to final qualification. Audit001 busy75 is zero Lean work and zero proof/axiom credit. It is not a successful audit or a replay authorization.

## Actual owner/type/value/axiom review — complete

The complete audit source `OwnedAudit.lean` was read. Its selector uses `env.getModuleIdxFor?` and the exact target module, traversing the entire environment; there is no namespace-prefix filter. Every returned owner receives recursive `Lean.collectAxioms`, rejected unless all dependencies are in exactly propext/Classical.choice/Quot.sound. Every type is emitted with pp.all; definition and opaque expression values are emitted, theorem proof values are deliberately omitted while theorem proof bodies were fully read in the production source. Actual audit002 ran once at a natural root-lock gap and returned natural rc0 in 6.2063115034252405 seconds. It audited the original successful producer012 object, with no new producer compile.

The complete 86,585-byte / 1,204-line actual type/value artifact, SHA256 `703c7949140266e8e81a81ed4797818b13c2897b92f93ceb44a965db5d6ce068`, was read literally in full, including every dependent let, instance argument, decidability argument and target. No dictionary compression, structural-summary replacement or truncated type was used. All 9 exact owner names in the JSON report match exactly one emitted TYPE and the coverage ledger; the one definition has exactly one complete emitted VALUE. There are no ellipsis, metavariable or sorry markers, no unknown primitive/opaque cases and no foreign-namespace omission.

Let `P` below abbreviate `Shao.Probability.SourceLateOmittedSuffixBudget.iid_actual_late_omitted_suffix_budget`, and let `Q` abbreviate `_private.Shao.Probability.SourceLateOmittedSuffixBudget.0.Shao.Probability.SourceLateOmittedSuffixBudget`. The coverage JSON records every full name, exact type digest, raw type line range, value digest and axiom row.

| Actual name | Full TYPE lines | Actual meaning checked | Recursive axioms |
|---|---:|---|---|
| P._proof_2 | 5–15 | Injectivity of r↦n-r-1 on Fin n, with actual r/s bounds | propext, Quot.sound |
| Q.los_finite_geometric_grid_integrals | 19–144 | Frozen scalar 3-let head, genuine integrabilities and both constants | standard three |
| P._proof_4 | 147–156 | r<n implies n-r-1+1=n-r | propext, Quot.sound |
| Q.los_iid_omitted_suffix_grids | 160–691 | Frozen iid 6-let head, constant before law/H/N, exact low/ordinary values | standard three |
| P._proof_3 | 694–707 | Late r implies n-r-1<floor(n/2) | propext, Quot.sound |
| P | 711–1070 | Frozen public 12-let head, one C before rho/n/x, same seed/bill and both outputs | standard three |
| Shao.Probability.SourceLateOmittedSuffixBudget.labelPermMeasurableSpace | 1074 | Actual type n→MeasurableSpace(LabelPerm n); complete VALUE lines 1076–1099 is fun n→Top.top, including full standard lattice instance chain | standard three |
| P._proof_5 | 1103–1191 | Actual late/ceil short-length hypotheses imply membership in min(floor(n/2),ceil H) grid; expanded beta/H has same rho and x | standard three |
| P._proof_1 | 1194–1203 | t>0 implies t-1+1=t; unused generalized n adds no premise to public target | propext, Quot.sound |

Here “standard three” means exactly propext, Classical.choice and Quot.sound. All 9 recursive results were read; the union is exactly this whitelist. Five generated declarations are arithmetic proof helpers emitted from the fully read public proof, not extra mathematical hypotheses or hidden data definitions. The actual count is 8 theorem constants and 1 definition, not an inference from the 3 explicit theorem heads.

Audit driver SHA256 is `eca91a226f2c4830bdf651794f2a7eca6de42be1f126dea41e12d52386720176`; audit JSON SHA256 is `f3dc75d309ab8face5aa91f777e6b85f98bc9caa04610ff95b6837b4fceb920f`; audit002 command receipt SHA256 is `12edef36e98d6c8ff4eb02970878d7e5c894687dee0565f50fe4c5e989bd21a3`. Reviewer read-only server observation at 2026-10-25T10:25:30.439468+00:00 independently matched actual driver and driver snapshot, actual audit log and report, the original producer012 object, the worktree's imported object and current source. Installed and original object digests are identical `1530bda1601b96c038ca5d62735b3c32de47f467ac55e34f1447e536d636e1df`; the source remains the exact reviewed SHA.

An earlier reviewer read-only binding script encountered a POSIX path joined using Windows Path, then failed local JSON parsing of the empty error response. No Lean/axiom command or write ran, and no successful evidence was credited. The corrected bounded read-only binding above succeeded. A prior capsule-comparison false result included the terminal `:= by` delimiter absent from a theorem-head capsule; a delimiter-only correction then verified all nine heads. These are recorded mechanical validation corrections, not mathematical-source changes or replayed proof gates.

## Publication and author release — exact immutable packet

The author's PR is [PR376](https://github.com/randomcat4/shao-lean/pull/376), native head `4d9a7f036ed6f1c3bdf87abaf8afe51ee20b60ad`, tree `0b0db0b27f9a37fecef7e06e0751b2cb4c1ce616`, source blob `d1671559317d369ed090aef06c975ca79fbeb74d`. Native commit/push/create/verification receipts were read completely. The PR is draft/open/unmerged and contains only the new 762-line source module.

Reviewer independently read the native server Git blob at the frozen head, confirmed its 42,556 bytes / exact reviewed SHA256, confirmed the head/tree/blob identifiers and sole changed source relative to the preserved base, and observed clean tracked status. The author's GitHub byte verification and successful native push receipt are reused; no reviewer API write occurred.

The full final receipt and author RELEASE were read and independently hashed: receipt `3179871138d32d7a55bd079b4b50ea716c1cf5b703109d0b6cbf97a6ac2478e5`; author RELEASE `88669674a65cb5669aa0aea44219729798bf7a366f30929ac613021ede15c811`. All 47 files in the immutable artifact index matched both SHA256 and byte length. Index `9ca291c291e775df2f143d1be475d859f638933c5890be44f8d41ae6d5a254ef` matches both receipt and release. The excluded receipt/checkpoint/index/release form the documented acyclic binding; the release binds the exact final checkpoint and receipt. Old checkpoint historical busy/partial fields are not used in place of the newer successful machine receipts.

The actual author final process observation at 2026-10-25T10:22:27.934557+00:00 was read and bound by SHA256 `99a8bf6f5317de7f6a14486715d31dfd5f713e9d994e24ad583cf7ba47520722`: zero target Lean processes, no in-flight target, unchanged source/object/head and clean tracked status, with only the audit driver untracked. The author expressly released this source writer and target execution, froze its evidence bytes, and continued only a separate mathematical successor. Reviewer work likewise has zero Lean/AX/heavy execution and no in-flight tool at release.

## Accepted mathematical scope and remaining open work

This unit qualifies only the same-seed late omitted nonnegative suffix bill with the two stated bounds. Since H≥4 beta², it is also compatible with the original CH/n scale, but it does not prove a physical kernel identity, late retained/interval-negative L-to-bill comparison, terminal E, omitted overshoot payment or the final original finite-2/p-law return. Those require their actual source-bound interfaces, including B's separately owned prefix large-wall/weighted survival/record/strip chain.

C1 original immutablev85 remains complete; C2/C12/OQ56 remain OPEN. OQ3 remains separately PAUSED_BY_USER. No root completion or novelty claim is made. The result is an original-source formalization/assembly with explicit attribution to the accepted masters, not a new research-theorem priority claim.

The exact reviewed unit is **CORRECT and qualified for coordinator acceptance**, with no requested mathematical-source edit and no unresolved review obligation. Reviewer final validation and zero-inflight RELEASE accompany this report. No merge or shared integration authority is exercised by this reviewer.
