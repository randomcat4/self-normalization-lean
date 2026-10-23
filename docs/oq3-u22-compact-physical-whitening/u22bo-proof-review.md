# OQ3 U22BO / unit148 independent complete proof review

STATUS: CORRECT

JUSTIFICATION: The exact 66-line source proves the frozen conditional actual-tilt whitening-family statement. Every new statement/proof local value, the entire new proof, and the complete actual owned theorem type have been reviewed. The explicit universal spectral premise remains intact. Exact-source server kernel and whole-owner recursive axiom evidence are valid and reused; no successful gate was replayed.

Reviewer: `/root/oq3_u22bo_full_review`, fresh independent NON-AUTHOR context, prescribed `gpt-6.1-sol` / `xhigh`. I did not author or modify implementation, execute Lean/build/audit commands, spawn children, or change other reports, lane status, branches, shared packages or caches. This report is my only write. Runtime token counters were not exposed, so no token or subscription allocation is estimated.

## Coverage and exact provenance

I fully read all 66 NEW source lines, the complete frozen scope (52 lines), all 32 lines of the actual-type inventory, and the entire 48-line audit source. The module owns exactly one public theorem, `Shao.OQ3.parabola_covariance_pair_whitening_family`, one actual theorem constant, zero private/generated theorems and zero global definitions. There is no unread new proof or definition remainder. Applicable AGENTS.md, SERVER.md, selected current TEAM/REGISTRY ownership/resource fields, TAKEOVER, restart instructions, streamlined acceptance and math-theorem references were read. Review authority is restricted to this file; no lane ownership was taken.

| Artifact | SHA256 | Bytes / lines |
|---|---|---|
| `u22bo-source.lean` | `9c48fd8a9434a7c28cb9761358f93255fb0dcf0d836093fc2a0c10afd8d65fdc` | 3400 / 66 |
| `hundred-forty-eighth-unit-scope.md` | `fd82dd1240dec90a14e21f323b052028f0ef4e2bb1b048cbef91b215bda3a68d` | 5750 / 52 |
| `u22bo-actual-types.txt` | `290ac7b27482f9f70513808a7d022e0c58e13c5769f852068f3bba9be4d64048` | 1980 / 32 |
| `u22bo-receipt.json` | `f8a3c95db6580e2349f56f8bd9364298bd886de04368b943c60da3105bc6c32e` | 4713 / 112 |
| `u22bo-build-history.json` | `827f9c0335dd0b3ade6a047e1e142b00665c53704932b2ac60d069d00a810f87` | 1897 / 50 |
| `u22bo-Audit.lean` | `7b27c3794dbc1f04c1be5cd98b49d3ba72f71f627c084afdb54585e23e6da80b` | 2004 / 48 |
| `u22bo-audit-environment.json` | `590f2a01d287b26613925d06dbef379f8eb62cd5b260f3b48755859c7aef63dc` | 986 / 13 |

All local artifact hashes match their original saved server counterparts in `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22bo-20261023`. The current worktree source and archived `source-02.lean` both have the exact reviewed source hash. These frozen source bytes are UTF-8, LF-only, without BOM; they were not normalized or rewritten during review. A literal comparison confirms that the frozen Lean declaration equals the implemented declaration before `:= by`, including all local values and premises. The full actual-type text occurs verbatim in the original audit log.

The current server branch is `feat/oq3-covariance-cell-family` at parent `0b64fc057c6aec5728f5917b98d725c6f69a564f`; BO is a continuation outside the already frozen PR210 parent. This review does not assert BO publication or root integration.

## Full statement, values and source-bound semantics

Lines8-18 quantify over an actual real probability measure mu, an arbitrary set Theta of real pairs, positive real constants lo and hi, and a two-sided quadratic-form premise for EVERY p in Theta and EVERY real xi,eta. The matrix in that premise is exactly `parabolaCovariance (mu.tilted (fun x => p.1*x + p.2*x^2))`. The lower and upper constants are independent of p. There is no supplied whitening equivalence, desired operator bound, centered identity, or arbitrary replacement covariance among the assumptions.

All statement values at lines19-29 and their proof-local copies at lines43-53 match exactly. Explicitly, tilt(p) is the displayed quadratic exponential tilt of the same mu; D(p) is its actual parabolaCovariance; s(p)=sqrt(D00*D11-D01^2); t(p)=sqrt(D00+D11+2*s); A(p) has rows `((D11+s)/(s*t), -D01/(s*t))` and `(-D01/(s*t), (D00+s)/(s*t))`; B(p)=D(p)*A(p); means(p) is the pair of actual integrals of x and x^2 under that same tilt. No formula, sign, matrix order, denominator, law or parameter is substituted in the proof.

The complete actual type confirms the conclusion: there exists a family E indexed by the genuine subtype Theta, each E(p) a continuous real linear equivalence of real pairs, satisfying A(p)*D(p)*A(p)=1; the exact forward row action of A(p); the exact inverse row action of B(p)=D(p)*A(p); forward operator norm at most 2/sqrt(lo); inverse operator norm at most 4*hi/sqrt(lo); and, for EVERY real x, the displayed equality between E(p)((x,x^2)-means(p)) and both coordinates of A(p) times the corresponding centered Fin2 vector. The norm is the default product MAX norm inherited from the qualified BN interface, with no Euclidean-norm substitution. The last equality is pointwise, with no almost-everywhere or distributional weakening.

Theta may be empty; no inhabitance, compactness or chart hypothesis is hidden. Choice supplies an empty-domain family in that case. For nonempty Theta the same lo and hi are used at every point. Positivity is supplied to BN unchanged; no extra assertion outside Theta is made. There is no continuity or measurability assertion about p mapping to E(p).

The actual tilted measure and Bochner integral expressions are used as defined. This theorem does not prove integrability, a tilted probability-law instance, mean-zero/covariance identities of a transformed random law, moments, or an actual sample comparison. Those claims are absent from both frozen and actual statements, so no missing analytic hypothesis is silently borrowed to obtain them. The uniform spectral premise is assumed explicitly rather than derived from probability, compactness, finite probes or numerical tests.

## Qualified consumed interfaces and reuse

The only project theorem applied by the NEW proof is `Shao.OQ3.quadratic_whitening_pair_equiv`, from BN147 / QuadraticWhiteningPairEquiv. Its exact source SHA256 is `640a12f87e1cbfcb59a827a10e197763e24fe7be8acae274febf484965eef38a` (8222 bytes /187 lines), matching local, archived qualification and current server source. I fully read the consumed complete canonical declaration at source98-120 and actual-type inventory1-20, including ALL s/t/A/B values, its D10=D01 premise, positive lo/hi, the full universal two-sided spectral premise, and every output field. Its A is definitionally exactly BO's A(p), and its inverse B is exactly D(p)*A(p). Its conclusions contain precisely the whitening, two actions and two operator bounds required here.

BN's qualified independent review `u22bn-proof-review.md`, SHA256 `922f6ab9fd26f7afbbddd66a66be16e06eb01ed62a00caa80d3400ded84b5333` (14806 bytes /95 lines), was checked for independence, exact source binding, coverage and scope. It records STATUS CORRECT, fresh NON-AUTHOR gpt-6.1-sol/xhigh, complete reading of all187 source lines, both actual theorem types/all values/both proofs, exact-source first successful kernel evidence and all-owned recursive white3 evidence. I reused that qualified old proof/check evidence without rereading BN's entire proof or entire report. The immutable author receipt's earlier pending-review label is historical; the later hash-bound complete independent review supplies qualification. BN actual types SHA256 is `cc9e0190d00fcca31fd40f7ea1b0c9bce7d7dfec70f88eff85384ae92978e40d`; its receipt is `93dba5ac67fdaae81cdf3b96f4c1f03ef0f35b100452a0d23b0a7164cf18c2aa`.

I fully checked the consumed actual definition `parabolaCovariance` at RegularCovariance source20-24. Its entries are variance(x), covariance(x,x^2), covariance(x,x^2), variance(x^2); the two off-diagonal expressions are literally the same. This justifies BO's symmetry proof by rfl for every tilt without a covariance-symmetry lemma or integrability hypothesis. The whole source SHA256 `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` matches the curated local snapshot, current server source and accepted v56 source map. The v56 receipt is PASS at SHA256 `c01ea5fcae6b6db2a7b19d22ac585be4e0a014499de6ef324105be7168b579a4`. Its checked code commit is `0187a42cf43bb24fcf263ff55a7515303cea40c3`; current recorded merged main is `ff3e7c80acd5ce85f24c7bcc475a98a35d2cd259`. These are distinct roles, not interchangeable identifiers; no unspecified later accepted-head value is invented.

Read-only object mapping confirms accepted-source-view BN resolves to the lead-oq3 BN object (SHA256 `eb5b7080b895c92840c736ed8d3cff546155666ee53974394b2d3da23eac1e5f`). RegularCovariance resolves to the previously accepted integration-bearing-v43 object, identical to the lead object (SHA256 `deebeea0d55266fcb1c6872101634d9171132886b6b67a7b14960428e4e14038`). BO resolves to its new lead object (SHA256 `f499b0b509078e1c2b8087f2620c562ed90b8ad221d1e241a6a529ae79db9a79`). No old object or proof was rebuilt or copied locally.

## Entire NEW proof review

Lines41-53 use classical reasoning and reduce the statement's let bindings, then introduce identical local tilt/D/s/t/A/B/means values. `dsimp only` changes definitional presentation, not quantifiers or hypotheses. Every local value has been checked against both the frozen declaration and actual type.

At lines54-55, for an arbitrary subtype p, hpoint applies the qualified BN theorem to D(p), the literal symmetry proof, and exactly lo,hi,hlo,hhi and hspec(p,p.property). Subtype coercion selects the same parameter used throughout. BN's universal scalar premise is consumed in full, and the pointwise canonical matrices are definitionally the local family values. No desired property is inserted as a hypothesis.

Line56 chooses E and its four conjunction fields from the proved pointwise existential `(hpoint p).2`. This is legitimate classical choice over the subtype; Classical.choice is whitelisted. Lines57-60 supply the family, introduce arbitrary p, preserve `(hpoint p).1` as the whitening identity, and select hE's exact forward action, inverse action, forward norm and inverse norm using the correct right-associated conjunction projections. The family can therefore vary by p while the two numerical bounds stay uniform.

Lines61-63 prove the remaining identity for arbitrary real x. Rewrite the forward action at the actual centered pair. Its coordinates become `A00*(x-means.1)+A01*(x^2-means.2)` and `A10*(x-means.1)+A11*(x^2-means.2)`. On the right, Fin2 vector subtraction has exactly those centered coordinates; Matrix.mulVec/dotProduct and Fin.sum_univ_two expand each row to exactly the same two terms. Prod.ext proves both coordinate equalities. Unfolding D,tilt,means aligns the proof-local names with already reduced true-covariance/integral expressions. No distributional argument, analytic limit, matrix-norm conversion, inverse orientation change or weakened centering is used.

All66 lines and every proof-local hpoint/E/hE use are covered. Static inspection and a forbidden-token scan of the full NEW source found no sorry, admit, axiom, unsafe, native_decide, implemented_by or set_option.

## Original server evidence and failure history

All evidence inspection used bounded read-only tools/server.py requests; no Lean, audit, build or successful-check replay occurred. The pinned toolchain is `leanprover/lean4:v4.36.0-rc1`; lakefile and manifest pin mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, and the actual resolved mathlib Git HEAD matches. The package link resolves to the established shared-v34 read-only view. autoImplicit=false is set in the project. Both original kernel attempts and the first owner audit record CPU14-17, native memory8192MiB, jobs4, consistent with the single-heavy OQ3 lease; the reviewer ran no heavy command.

Original source01 SHA256 is `ab7620a61223838b42d74401046f787d1cecfc88e66a36ea2f3a036b88cc9ab1`, 3384 bytes/66 lines. The complete kernel attempt failed with exit1 in6.208224857226014s. Its preserved log is28043 bytes/392 lines, SHA256 `914fdb9d513bbae760be9557a09026ab81ab9cb59b395dbb7310293e04e0b1ca`; the diagnostic is unsolved goals at source40:69, with final centered-pair coordinate expressions leaving proof-local D/means against expanded true covariance/integrals. I inspected the failure diagnostic and relevant goal contexts, preserving the failure rather than treating it as a proof result.

The exact source01-to-source02 diff changes ONLY source63 from `simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]` to `simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, D, tilt, means]`. Thus only definitional normalization in the final coordinate proof changes; no statement, premise, local formula or conclusion changes.

Source02 is the first complete kernel success, exit0 in5.664182314649224s, at the exact reviewed hash. Original successful log is133 bytes/2 lines, SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`; I read it in full. It contains only the known mathlib thin-overlay local-changes warning and no Lean error.

The first actual-owner audit exited0 in6.492152759805322s. Its original audit-record.json SHA256 is `6d5c2a12aa20a9b01103ed95e0a78edac64c2f6b0607125a9d1b89d56b79d55a`,498 bytes/18 lines. The original audit log is2232 bytes/39 lines, SHA256 `798b83631419a982c30c172c34e1891819aea181cbf80c8407a49d7059180e18`; I read the full log, complete actual type and final counts. Audit source enumerates EVERY constant by actual module ownership `Shao.OQ3.ParabolaPairWhiteningFamily`, rejects owned axioms, runs Lean.collectAxioms recursively for each owned constant and rejects every axiom outside propext/Classical.choice/Quot.sound. Its two set_option commands only configure pretty printing.

The actual output has FROZEN_DEFINITIONS0, FROZEN_THEOREMS1, ALL_THEOREMS1, ALL_DECLARATIONS1 and AXIOM_GATE PASS. The sole owned name is precisely the reviewed public theorem and has `[propext, Classical.choice, Quot.sound]`. There are no unprinted private/generated/definition constants. This is whole-module transitive coverage, not merely checking a chosen public-name list. Source, audit source, records, actual types, counts, logs, pins and dependency objects are mutually consistent.

## Acceptance boundary and remaining work

This exact NEW unit is CORRECT with full independent source-to-statement/proof coverage and reused exact-source kernel/all-owned transitive white3 evidence. No residual BO proof gap or uncovered new declaration remains. Root acceptance may reuse this report and receipts after exact-hash/interface/integration checks; a duplicate full old-proof review or compiler pass is not required merely because the context changes.

The eliminated obligation is assembling the true tilted-covariance canonical pair-equivalence family, with explicit uniform MAX-norm bounds and exact centered Fin2 representation, from the qualified single-matrix interface. The planned next consumer is the uniform Gaussian cell-coefficient/oscillation bridge using this actual family. Deriving the uniform spectrum or a compact chart for original unbounded-law anchors, moment/exponential conditions, actual sample-law Edgeworth estimates, weighted probability reconstruction/cell summation, the full exterior, and original B/D remain OPEN. Existing corrected fixed-law A, bounded compact-tilt C, p54 repairs, strict weak-Cramer qualifications and external attribution are unchanged. This auxiliary conditional family identity does not establish a new original root closure or novelty claim.
