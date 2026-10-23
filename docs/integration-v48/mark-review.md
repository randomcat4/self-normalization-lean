# Independent final review — SourceMarkFourierNorms

STATUS: CORRECT. Complete independent source-to-statement/proof review and complete actual-owned type/definition-value review pass for the frozen target. The original export abbreviation defect was repaired by a new rendering of the unchanged compiled object; its two previously abbreviated records have now been read completely.

Frozen target: commit `daa98425062abf12da4be9fd18f4e52d108136ed`, `Shao/Probability/SourceMarkFourierNorms.lean`; source SHA256 `67d7b455b31fd939d56f78d760f3fea0f331e375c27bcd6f1aea3ce9ab902998`; compiled object SHA256 `fa56f513ff44ca0d09436ddbb241a7b6840e3161b5aecc6048c7074f75f0fe87`. Remote commit source, current source, and object were independently hashed and matched. Commit changes exactly this one added source. Local draft bytes match the same source hash.

Reviewer is the fresh sole independent final reviewer `/root/common_mark_review`, not the author. No implementation/source edits, local Lean, new Lean proof checks, or subagents were used. Existing source-bound kernel/object/owned-axiom checks are reused under the current streamlined acceptance policy.

## Complete reading already performed

- Original supplement lines 2402–2428 and 3222–3253, frozen declaration document, candidate declarations, and source contract.
- Entire exact 852-line source, including every proof, all four public constants, and all private definitions/lemmas.
- All 72 complete actual types, all 11 actual definition values, all private/generated relation types, and all four public actual constants. The original export supplied 70 complete types and all11 complete values. The final export supplied full `schwartz_fourier_norms` (record18) and `unitFourier_schwartz_norms` (record36), which have now been completely read. Exact byte comparison confirms that all other70 complete records are unchanged.
- All 342 entries of a deterministic repeated-subexpression dictionary and every compressed record. Dictionary expansion reconstructs every normalized original expression exactly, retaining all non-whitespace content; normalized-log SHA256 `ea544a0f48f972b4c82e6b064115310f0bd49e742757e32a2c3721b3af5ea695`. The two repaired full types were then read using the same dictionary, with exact normalized reconstruction checked. Their normalized complete-record hashes are `daa2c945683f15d83bfcbd59b04a3297b8001dcb002e76cfd01bc253bdce8e11` and `c0936516ff2921ce85fca4942e73097cdac1f2b33e028aee1769b10e8e2fcbd9`. No type/value content was omitted.
- All 72 audit owner rows and their transitive axiom lists. Exported owner/definition name sets equal the audit sets exactly; counts are 61 theorems and 11 definitions, with two public theorems and two public definitions. All transitive axioms lie in `propext`, `Classical.choice`, `Quot.sound`.

## Mathematical/source findings

The public definitions are the actual negative unit-frequency transforms, retaining positive `u*y*sqrt(r)` in the exponential and the actual `u*(y*sqrt(r)+w)` sine. Quantifiers and all derivative/support assumptions match the freeze. Each constant depends only on the fixed positive interval and precedes M, amplitude, and all frequency/shift parameters. The hypotheses are actual C0/C1/C2 bounds, not a Fourier estimate.

Positive compact support pays global smoothness despite the square-root singularity at zero. The modulated amplitude and its first two derivatives have the claimed common support. Compact support and pointwise derivative budgets pay the actual L2 bounds. Plancherel and weighted Cauchy–Schwarz with `(1+(v/R)^2)^(-1)` give the unweighted Fourier bound; the derivative Fourier identity pays the |v|-weighted bound. The real-frequency conversion uses `v/(2*pi)` and pays Jacobians `2*pi` and `(2*pi)^2`; the common factor256 is sufficient.

The exponential uses `R=1+y*abs(u)`. The sine uses actual phase derivative bounds directly for its large regime, rather than the source's optional splitting into exponentials; this valid route still yields square-root growth. For the small regime it uses `abs(u*w)<=y*abs(u)/16`, `abs(sin x)<=abs(x)`, and `T^2<=T` to pay a genuine factor T. The proof then pays `min(T,1+sqrt(T))`, including the transition above1, rather than substituting an unbounded linear growth estimate. No frequency nonzero division excludes y=0, u=0, or M=0; the degenerate interval a0=a1 is retained.

This covers only marknorms(a)'s global exponential/sine L1 and |v|-weighted estimates and actual integrability, extended to all y>=0. Outside-cone tails, localized part(b), actual chi/family uniform derivative budgets, 2D integrability/continuity/inversion, and C1/C2 root closure remain outside this unit.

## Verified evidence

Author receipt SHA256 `8722a90ba1ece9677f51769df6f78549cf458f361f9475e72a1d62cb8ba431d6`.

Candidate SHA256 `1f83298d0ef5b102074c4e85a0ef9f91d8b77334bb7d55ac37d2e5553849a28c`; contract SHA256 `f4e43a8915d3e3ddec66493847fba7dc2fe102cf6c93ae6b4cb8dd8855d9969d`.

Remote output directory: `/root/rivermind-data/shao-lean-20261021/outputs/common-centered-characteristic-v44`.

- `mark-targeted-12.log` and `mark-object.log`: each SHA256 `fb0afd1748a13e3596bf676113b426dac1cc9b0f93629d7a70a6664fefb057d5`, 5935 bytes; no errors, warnings only.
- `mark-owned-audit.json`: SHA256 `e67f37fee6b9440804a12fa5300e4b012f9c88ef6b807cbce5e2e50361ae0cc6`, 17328 bytes, PASS.
- `mark-owned-audit.log`: SHA256 `2ba7d39ccfbdb3096ca6d9562d445f77830045aac2940a3ea76d8e874633dc65`, 11333 bytes, final 72/61/11/2/2 coverage receipt present.
- Original `mark-actual-owned-types-and-definition-values.log`: SHA256 `4229989fdfb33ef8bf4ea5e61f6a3dd1790975c898c167c41985022999940839`, 886880 bytes. Preserved; incomplete only in the two actual-type records identified above.

Pinned Lean `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c` match the frozen commit. Relevant actual mathlib Plancherel and derivative-Fourier interfaces were inspected. No accepted old-unit internal proof review or repeat compile was commissioned.

## Complete-export repair and final disposition

The author reran only the established exporter with `pp.all=true` and `pp.maxSteps=1000000000`; the failed unsupported `pp.maxDepth` attempt remains preserved and was not treated as evidence. The successful final exporter source was read completely and hashed: `0772fd0d70d4bbd459d1c63fb4a5c03175d7704460f135b02403c5257288fa6c`.

Final complete log: `mark-complete-actual-owned-types-and-definition-values.log`, SHA256 `5718163a79644f31771ba00a6c73133c42618d12ed8f3ea2b3fb33ece14db671`, 1215488 bytes. It has exactly72 unique target-owned names and11 definition values, each name set equal to the original transitive-axiom audit, zero literal `⋯`/`…`, zero errors, and the final 72-record export marker. Only records18 and36 differ from the original export; every other record is byte-identical and its existing complete reading is reused.

Supplement: `mark-complete-export-supplement.json`, SHA256 `e50d457bbd8502cd91f2d0589983d388fc7f6715f1092a3ec0b0bc2746105d73`; read in full and independently hash-verified. It binds the same commit, source, object and original receipt, records exporter exit0 under the existing root lock/CPU10–13/memory flags, and records no proof/targeted/owned-axiom rerun. Final read-only hash checks reconfirmed the exact frozen source, object, original receipt, original export, and audit JSON hashes above.

CORRECT applies to the two definitions and two public global-norm theorems in their frozen scope, with complete 72-type/11-value/private/generated/transitive-axiom coverage. There is no remaining review gap for this exact version. It does not close outside/localized/2D inversion work or any C1/C2 root theorem.

Reviewer state: COMPLETE_RELEASED at the user's requested natural shutdown checkpoint; zero commands in flight. No successor unit was started. Root may reuse this exact-hash review together with the original author gates and complete-export supplement for acceptance.
