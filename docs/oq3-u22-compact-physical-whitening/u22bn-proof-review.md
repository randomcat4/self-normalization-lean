# OQ3 U22BN / unit147 independent complete proof review

STATUS: CORRECT

The exact 187-line source proves both frozen declarations. I found no mathematical gap, changed assumption, incorrect inverse orientation, hidden desired-bound hypothesis, or substitution of a Euclidean norm for the default real-pair norm. Acceptance is limited to the two matrix/pair-equivalence theorems at the exact source below.

Reviewer: `/root/oq3_u22bn_full_review`, fresh independent NON-AUTHOR context, prescribed `gpt-6.1-sol` / `xhigh`. I did not author or modify implementation, run Lean/build/audit commands, spawn children, or change status, evidence, branches, packages, caches or old reviews. The only authored file is this report. Runtime token counters were not exposed; no token or subscription allocation is estimated.

## Exact coverage and provenance

I fully read all 187 NEW source lines, BOTH complete actual theorem types (all32 inventory lines), the complete frozen scope (56 lines), every statement/proof local value, and BOTH entire new proofs. There are exactly two public theorem declarations, two actual owned constants, zero private/generated theorem constants and zero global definitions. Local values do not introduce unreviewed global definitions.

| Artifact | SHA256 | Bytes / lines |
|---|---|---|
| `u22bn-source.lean` | `640a12f87e1cbfcb59a827a10e197763e24fe7be8acae274febf484965eef38a` | 8222 / 187 |
| `hundred-forty-seventh-unit-scope.md` | `c994381453f4907a801c82f65423c6b50ac2a13c428ddef51b1e34e7d94e7b53` | 6118 / 56 |
| `u22bn-actual-types.txt` | `cc9e0190d00fcca31fd40f7ea1b0c9bce7d7dfec70f88eff85384ae92978e40d` | 1635 / 32 |
| `u22bn-receipt.json` | `93dba5ac67fdaae81cdf3b96f4c1f03ef0f35b100452a0d23b0a7164cf18c2aa` | 4708 / 112 |
| `u22bn-Audit.lean` | `fcd0abc7dd79822e96f724d83b9e3ee9950056d70d4b204e24be468b2779e1d8` | 2055 / 49 |
| `u22bn-build-history.json` | `80197b6421a144487344a649dc47ae29c5ceccd016ad99f1bde7259060ebeec7` | 1981 / 50 |
| `u22bn-audit-environment.json` | `def87cb03739bb784f69148cd3fc0599653bade19966ddf6c61c6fc492cef457` | 958 / 12 |

These local hashes match the original saved server artifacts in `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22bn-20261023`. The current worktree source and archived `source-02.lean` both have the reviewed source hash, 8222 bytes and187 lines. The source is UTF-8, without BOM or CR bytes; successful frozen bytes were not rewritten.

I read applicable AGENTS/SERVER instructions, current selected TEAM/REGISTRY ownership, TAKEOVER, streamlined acceptance, and math-theorem plus its required prompt/workflow/Lean references. OQ3 is the activated owner with its previous writer released and sole-child lease1. All remote inspection was bounded read-only observation on CPU14–17 through the existing transport. No successful gate was replayed.

## Complete statement and local-value fidelity

The generic theorem, source lines9–96, quantifies over arbitrary real2×2 matrices A and B with BOTH A*B=1 and B*A=1. Its statement-local F is exactly
`F M (x,y) = (M00*x + M01*y, M10*x + M11*y)`.
It constructs a real continuous linear equivalence E with function equality E=F A and inverse-function equality E.symm=F B. For EVERY real c>=0 it conditionally deduces the forward operator bound <=2*c from ALL A-entry absolute-value bounds <=c, and separately the inverse operator bound <=2*c from ALL B-entry bounds <=c. It does not take continuity, operator bounds, or the desired E as assumptions.

The canonical theorem, lines98–184, universally quantifies over a real2×2 D satisfying D10=D01, positive lo and hi, and the full two-sided quadratic-form inequality for EVERY real xi,eta:
`lo*(xi²+eta²) <= xi²*D00+2*xi*eta*D01+eta²*D11 <= hi*(xi²+eta²)`.
All statement-local values are fixed:
`s=sqrt(D00*D11-D01²)`,
`t=sqrt(D00+D11+2*s)`,
`A=[[(D11+s)/(s*t), -D01/(s*t)],[-D01/(s*t),(D00+s)/(s*t)]]`,
and `B=D*A`.
The conclusion is A*D*A=1 and existence of E with the displayed row action of EXACTLY this A, inverse row action of EXACTLY this B, forward operator norm <=2/sqrt(lo), and inverse operator norm <=4*hi/sqrt(lo). Both full actual types, including every let value, match these frozen statements and source. There is no probability law, covariance-family substitution, affine centering, altered matrix, or unspecified whitening witness hidden in the statement.

Proof-local F repeats the statement F exactly. The linear equivalence e uses toFun=F A, invFun=F B, and E=e.toContinuousLinearEquiv; no choice of a different row map is introduced. The canonical proof repeats exact s,t,A,B, then defines only U=1/sqrt(lo). The helpers hcompose, hid, hbound, hx0/hx1, hrow, hAB/hBA, hd0/hd1/hp/hm, hD01/hDentry, hU/hBentry and final hbound have their explicitly displayed types and uses reviewed below.

## Complete generic proof review

Lines31–39 establish F M (F N w)=F(M*N)w, in the correct multiplication order. Both coordinates are expanded using the actual two-term Fin2 matrix product and proved by ring algebra. F of the identity is the identity on BOTH coordinates.

Lines40–62 construct e. Its left inverse is F B after F A, hence uses B*A=1; its right inverse is F A after F B, hence uses A*B=1. The two addition identities and two scalar-multiplication identities are explicitly proved by ring algebra. Thus no injectivity/surjectivity assumption is omitted or replaced by the wrong order.

Line63 upgrades this actual finite-dimensional linear equivalence to a continuous linear equivalence. I inspected the pinned primary definition LinearEquiv.toContinuousLinearEquiv (FiniteDimension.lean:368–373): it keeps e's maps and obtains continuity of the forward linear map and inverse linear map by finite dimensionality. Both spaces here are the finite-dimensional real pair. Its coercion/inverse coercion definitions preserve the maps, justifying the two rfl witnesses at line86.

Lines64–85 prove the entire pointwise bound for arbitrary M,c,w, including w=0 and c=0. The default product norm is max(|w.1|,|w.2|), so hx0/hx1 are the appropriate coordinate bounds. In either row, triangle inequality and abs_mul give
`|Mi0*w1+Mi1*w2| <= |Mi0|*|w1|+|Mi1|*|w2| <= c*||w||+c*||w|| = 2*c*||w||`.
The multiplication inequalities use nonnegativity of the coordinate absolute values and c. Taking the maximum of the two row bounds proves the actual product-norm bound, without a Euclidean conversion.

Lines86–96 use ContinuousLinearMap.opNorm_le_bound separately for E and E.symm, with nonnegative constant2*c. I inspected its pinned primary signature (Operator/Basic.lean:196–198); it requires precisely that nonnegative constant and the all-vector pointwise bound just proved. I also inspected Prod.toNorm/Prod.norm_def (Normed/Group/Constructions.lean:235–237), which defines the maximum norm used by the source's definitional changes. Every conclusion of the generic theorem is accounted for.

## Qualified H dependency reuse

Consumed H is Shao.OQ3.quadratic_whitening_spectral_data, from QuadraticWhiteningSpectralData.lean SHA256 `83520a430712a07148396f30f7c07619ef55bda9cc9e464a98eae63e071e874e`. I fully read the consumed public declaration (source195–218), including ALL its s,t,A values and all output fields. Its inputs are exactly D, hsym, lo, hi, hlo, hhi and the same universal hspec. Its outputs are s>0, t>0, A.transpose=A, A*D*A=1, strict positivity on every nonzero vector, full two-sided transpose-frequency Euclidean-radius bounds, and ALL-entry |Aij|<=1/sqrt(lo). BN's local A is definitionally the same literal A. The proof uses H's hADA and hAentry without weakening its premises.

H's established review u22h-proof-review.md, SHA256 `798641c61ab02a64dbab081f9c70f30c00efffbf6917ada8417b1b76f9f6217b`, was checked for qualification and exact scope: STATUS CORRECT at line29 and final acceptance at line121, covering all245 old source lines and both actual public/private declarations, including source/owner axiom evidence. Its reviewer was fresh and independent. I reused that qualified evidence and did not reread H's proof bodies or commission another review.

The H hash matches the rootv55 receipt's exact source map, the local curated source, and current server source. The accepted-source-view H object resolves to the established lead-oq3 H object. Rootv55 receipt SHA256 is `7c20061123bb71ef92bb80d248fe8f7b8c06e9cf96d36fb7bf23b34f8031d109`, status PASS. Distinct identifiers were checked: checked code `a702f15563f7e7bd28d94f15615ebaf1e49c2f48`; accepted notice/head `6ebb81d10a73439bd714b6b47e0c8022bbf4474e`; merged main `040c10a68c08a9b0d0a9fcd657a691379146d35e`. They are not treated as one commit.

## Complete canonical proof review

Lines135–141 apply H to unchanged assumptions, obtain hADA, and associate A*(D*A) as (A*D)*A to get A*B=1. The reverse B*A=1 uses mul_eq_one_comm for finite square real matrices. This is the right-inverse/left-inverse theorem, not an assertion that arbitrary matrices commute. I inspected the pinned generic API: mul_eq_one_comm requires the Dedekind-finite monoid property and says a*b=1 iff b*a=1. The finite square-matrix instance is available in the imported pinned environment; the source's successful full kernel check also covers this actual application. No rectangular/infinite-dimensional inference is made.

Lines142–159 specialize the still-universal hspec at (1,0), (0,1), (1,1), (1,-1). Put a=D00, b=D01, d=D11. These give lo<=a,d<=hi and a+2*b+d<=2*hi, a-2*b+d<=2*hi. Since a,d>=lo>0, the latter inequalities imply -hi<=b<=hi. The diagonal lower absolute-value sides follow from positivity of lo and hi; the upper sides are the coordinate upper bounds. D10 is handled by explicit hsym. All four Fin2 cases are present. These finite probes are used only to derive entry bounds; they do not replace H's full universal spectral premise or whitening proof.

Lines160–173 define U=1/sqrt(lo), establish U>=0, and expand each actual entry of B=D*A into D_i0*A_0j+D_i1*A_1j. Triangle inequality, ALL D-entry bounds <=hi, and ALL H A-entry bounds <=U give |Bij|<=2*hi*U. Nonnegative absolute values and hi>0 justify both multiplication comparisons. There is no assumed inverse norm or inverse entry bound.

Lines174–184 apply the generic theorem to these actual A and B with both proved inverse equations. Function equalities are converted pointwise by congrFun to obtain BOTH displayed row actions. The forward bound uses c=U, and the inverse bound uses c=2*hi*U>=0. Its factor2 becomes 2*(2*hi*U)=4*hi/sqrt(lo). The returned whitening identity is H's exact A*D*A=1. No denominator cancellation, unproved determinant positivity, norm change, missing vector case, or sign-dependent inequality remains in this new proof.

## Original saved failure and exact-source successful evidence

I inspected the original archived source identities, exact source01-to-source02 diff, original failure diagnostics, entire successful build log, full49-line audit source, complete audit output, remote audit record, history, receipt, environment manifest and pins. Original source01 is SHA256 `2dd7aa8fca63a8d120d8adb5a1241a1c0d7a538dc412c58b88536e85c52c0755`, 8110 bytes/183 lines. Its complete build failed (exit1, 6.487588204443455s); original log is22041 bytes, SHA256 `63689c4c1433464b0774c6f73d4a248eb4a693f379e5b28daeecc604505536ca`. Diagnostics identify linarith failures at original152/155 and the hD01 indexed type mismatch at original154.

The ENTIRE delta adds only four explicit change statements, one per branch: `change |D 0 0| ≤ hi`, `change |D 0 1| ≤ hi`, `change |D 1 0| ≤ hi`, `change |D 1 1| ≤ hi`. No declaration, premise, statement/proof let value, mathematical argument or check setting changes. Source01 and its failure remain preserved.

Source02 is the first complete kernel success: exit0, 5.750722303986549s, complete reviewed187-line source at SHA256 `640a12f87e1cbfcb59a827a10e197763e24fe7be8acae274febf484965eef38a`. Successful log:133 bytes/2 lines, SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`. It contains only the known thin-overlay mathlib local-changes warning, with no Lean error.

The first actual-owner audit on successful source exited0 in6.253531327471137s. Audit log:1887 bytes/39 lines, SHA256 `14227663f07a365a918d7cb946ba229577bfc35f4ed10c036c93d40bcc89db9a`. Its source enumerates EVERY constant whose actual module owner is Shao.OQ3.QuadraticWhiteningPairEquiv, rejects owned axioms, recursively calls Lean.collectAxioms for each owned constant, and rejects every axiom outside [propext, Classical.choice, Quot.sound]. Its two set_option commands affect only pretty printing.

The full audit prints both complete reviewed actual types and reports FROZEN_DEFINITIONS0, FROZEN_THEOREMS2, ALL_THEOREMS2, ALL_DECLARATIONS2 and AXIOM_GATE PASS. Both owned names are precisely the two public theorem names above, each with exactly [propext, Classical.choice, Quot.sound]. Counts come from actual owner enumeration: no unprinted private/generated/global-definition remainder exists. This is whole-module transitive coverage, not a public-name-only audit. Static inspection/scan of the entire new source found no sorry, admit, new axiom, unsafe, native_decide, implemented_by, or set_option.

Recorded build/audit settings are CPU14–17, native8192MiB, j4, autoImplicit=false and established accepted-source-view/shared-v34 package environment. I directly checked lean-toolchain=leanprover/lean4:v4.36.0-rc1, declared mathlib pin and actual package HEAD=807d3836b165983210ee2ecf3cd28f239436949c, and its shared-v34 resolution. The new object in that view resolves to the current lead-oq3 owned object. Current branch is feat/oq3-covariance-cell-family, parent0b64fc057c6aec5728f5917b98d725c6f69a564f; BN is continuation work outside that frozen PR210 parent. No unrelated workload, cache, old module or accepted source was changed or rechecked.

## Acceptance boundary and next dependency

The independent NEWsource/type/value/proof review is complete and CORRECT, with exact-source server kernel and all-owned transitive-axiom PASS evidence reused after binding checks. There is no uncovered proof change or residual BN mathematical gap requiring another full review solely at integration.

This result supplies the actual maxnorm real-pair continuous linear equivalence for the literal canonical whitening matrix and actual inverse D*A, with constants2/sqrt(lo) and4*hi/sqrt(lo). The next dependency is application to the actual compact covariance family/selected tilt-anchor chart, including required parameter-uniform cell constants. Actual sample Edgeworth, probability reconstruction/cell summation, exterior estimates and original OQ3 B/D remain OPEN. This review claims neither a root closure nor mathematical novelty.

