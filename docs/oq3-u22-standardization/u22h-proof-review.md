# OQ3 U22h independent complete proof review

## Immutable blind-translation and acceptance prefix

This prefix was written after reading the entire actual-type inventory and before reading the unit scope, implementation, original-source excerpts, author evidence, or earlier review votes. It is a statement-acceptance record, not a correctness verdict. It will be retained verbatim when the completed review is appended.

Actual-type inventory: `drafts/oq3/u22h-actual-types.txt`; SHA256 `5ca1c1185663dbcc0f4a3d977acbd059b5bff0d124246c017e76f776dcbcdd04`; 2706 bytes; 47 lines. I read all 47 lines. It lists exactly two declarations, one public and one private, with their full types and printed axiom lists.

Blind translation of the public declaration `Shao.OQ3.quadratic_whitening_spectral_data` (inventory lines 1–24): for every actual real matrix D indexed by Fin 2, assume D(1,0)=D(0,1), positive real constants lo and hi, and, for every real xi, eta, both inequalities

`lo*(xi^2+eta^2) <= xi^2*D00+2*xi*eta*D01+eta^2*D11 <= hi*(xi^2+eta^2)`.

Define s as the nonnegative square root of `D00*D11-D01^2`, t as the nonnegative square root of `D00+D11+2*s`, and define the literal numerical matrix

`A = [[(D11+s)/(s*t), -D01/(s*t)], [-D01/(s*t), (D00+s)/(s*t)]]`.

The conclusion requires s>0 and t>0; exact symmetry `A.transpose=A`; the exact whitening identity `A*D*A=1`; strict positivity of the quadratic form `xi*(A*[xi,eta])0+eta*(A*[xi,eta])1` for every nonzero pair (specified as xi≠0 or eta≠0); for every pair, including (0,0), the Euclidean length of the transposed-frequency image `(xi*A00+eta*A10, xi*A01+eta*A11)` lies between `sqrt(xi^2+eta^2)/sqrt(hi)` and `sqrt(xi^2+eta^2)/sqrt(lo)`; and every matrix entry satisfies `abs(Aij)<=1/sqrt(lo)`.

Blind translation of the private declaration `_private.Shao.OQ3.QuadraticWhiteningSpectralData.0.Shao.OQ3.open_domain_whitening_algebra` (inventory lines 25–47): the same universally quantified inputs and assumptions, the same explicit s, t, A, and all the same conclusions through the two-sided frequency-radius estimate, without the final entrywise bound. The public theorem must supply that additional bound rather than assume it.

Acceptance criteria fixed from these actual statements: (1) neither symmetry nor the two-sided all-direction quadratic estimate may be silently weakened; (2) positive determinant and both positive square-root denominators must follow from the written assumptions; (3) whitening must cover all four entries and use the actual D, not a substituted covariance or abstract whitening witness; (4) positivity is strict on every nonzero vector; (5) frequency orientation is exactly transpose multiplication as displayed, and both radius inequalities include zero frequency; (6) the entrywise estimate must be deduced for every Fin-2 index with valid nonnegative/square-root reasoning; (7) no target conclusion is supplied as an input; (8) any subsequent acceptance is limited to this numerical matrix-algebra statement. These types alone assert no measure, probability, covariance construction, global theorem closure, or novelty result.

The inventory prints only `[propext, Classical.choice, Quot.sound]` for both declarations. The final review will check the exact source/evidence binding separately; this observation is not an independently rerun axiom audit.

---

## Verdict and independent coverage

STATUS: CORRECT

The exact U22h source below proves the frozen numerical matrix statement completely. I found no mathematical gap, weakened quantifier, hidden target-conclusion assumption, incorrect transpose, unsafe field cancellation, or missing zero-frequency case. Acceptance is for the public theorem and the entire new private helper at this exact source hash, with the existing server kernel/owner-axiom evidence reused after checking its exact bindings. It does not close a probability or OQ3 root theorem.

Reviewer context: `/root/oq3_u22h_full_review`, assigned fresh independent `gpt-6.1-sol` / `xhigh` review. I did not author or modify the implementation, run Lean/audit gates, spawn children, alter evidence/status/branches, or use earlier review votes as mathematical evidence. My only write is this report. Token-usage telemetry was not exposed to this reviewer; no usage or subscription allocation is estimated here.

The immutable prefix is the first **3370 bytes / 25 lines** of this report, SHA256 `2fe91868a67c5bfdc62b85cbed76381ef26f424eebaf99ca2ad11d23c63707f7`. I verified that binding immediately before appending this review; it predates reading the scope, proof, original-source excerpts, and author receipts. It includes both complete actual-statement translations and the fixed acceptance criteria.

## Exact inputs read

| Artifact | Exact binding | Reading/coverage |
|---|---|---|
| `u22h-actual-types.txt` | SHA256 `5ca1c1185663dbcc0f4a3d977acbd059b5bff0d124246c017e76f776dcbcdd04`; 2706 bytes; 47 lines | Entire inventory FIRST; both actual types and axiom lists |
| `eighty-ninth-unit-scope.md` | SHA256 `21eb341aac20877e7d893d10762af7abfd93421aee50b02f61f3f3b0ceaf1a21`; 4160 bytes; 45 lines | Entire frozen scope |
| `QuadraticWhiteningSpectralData.lean` | SHA256 `83520a430712a07148396f30f7c07619ef55bda9cc9e464a98eae63e071e874e`; 10995 bytes; 245 lines | ALL 245 lines, including both full statements and the complete private proof |
| Original `C:/game/shao/current/oq3/proofs/r2/report.md` | SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55` | Lines 47–67 and 80–96, including requested 53–59 and 83–92 |
| `root-contract.md` | SHA256 `a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a`; 9473 bytes; 82 lines | Entire contract, particularly sections 2 and 4 |
| Curated `library/Shao/OQ3/CovarianceWhitening.lean` | SHA256 `d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8`; 24907 bytes | Lines 1–215, including ALL of private `whitening_spectral_data` lines 29–210 |
| `u22h-receipt.json` | SHA256 `7ffd72f80d7aff912d6990d0c96f2fd0c08b08cdcec8424f1ab433ab2558de88`; 4626 bytes | Entire receipt, AFTER the mathematical reading |

I also read the required math-theorem skill references (`prompt-library.md`, `openai-workflow.md`, `lean-verification.md`), project instructions, `SERVER.md`, current ownership/transition guidance, and the audit/history/environment files listed below. Read-only server inspection confirmed the current production source has exactly the same 10995-byte / 245-line SHA256 as the local reviewed source and archived successful `source-02.lean`.

## Source fidelity and frozen interface

The frozen public declaration (scope lines 15–38) is byte-for-byte the public source declaration (lines 195–218) after removing only its proof opener ` := by`. The actual printed public type has precisely these inputs and conclusions. It introduces no public definition and no hidden typeclass or extra hypothesis. The private theorem's printed type is exactly the intermediate package without entry bounds.

The original R2 lines 53–59 require actual covariance spectra uniformly bounded above and below and refer to the standardized variable `Delta(theta)^(-1/2)(W-m(theta))`. Lines 83–92 use that standardization and comparability of the true transformed frequency norm to transport weak-Cramer constants without changing the exponent. U22h isolates the valid finite-dimensional algebra needed for those steps: the literal positive symmetric whitening matrix and its genuine two-sided transpose-frequency/entry estimates. Symmetry plus the displayed all-direction quadratic inequalities is the correct numerical meaning of the source spectral assumption. This theorem does not silently obtain a covariance, spectral hypotheses, moments, or a tilted family from unrelated objects.

Root-contract section 2 requires actual law/covariance semantics and valid open-domain inputs; section 4 retains the uniform spectra and other stronger root-B assumptions, including the separate unbounded far-event probability obligation. U22h preserves this boundary. A subsequent actual-law consumer must substitute its literal `parabolaCovariance` at each true tilt, prove symmetry, and supply the retained uniform `hspec` with common positive constants. This unit alone does not establish that substitution, the standardized family, weak-Cramer transport, any Edgeworth/cell/Laplace/far-probability estimate, B/D closure, or novelty.

Attribution is accurate: after changing only the new private theorem name back to `whitening_spectral_data`, new source lines 12–193 are exactly the full 182 lines of accepted `CovarianceWhitening.lean` lines 29–210. I checked the complete newly owned proof, not just its extension or a prior acceptance vote. The new proof contains no call through the old private declaration name, and the accepted source is unchanged. The copied argument is attributed in source lines 8–11 and the receipt. This is a reusable formal interface plus entrywise corollary, not a claim of a new inverse-square-root theorem.

## Complete proof audit

All source line references in this section refer to the reviewed 245-line `QuadraticWhiteningSpectralData.lean`.

1. **Lines 1–34: imports, attribution, and private full statement.** The `CovarianceWhitening` import supplies the accepted library context; it is not an axiom or an assumption of the target conclusion. The private statement universally quantifies the actual real Fin-2 matrix and both spectral constants. Its only matrix condition is the exact off-diagonal symmetry plus the two all-direction inequalities. All s/t/A expressions are the actual formulas in the blind translation.

2. **Lines 35–67: positivity, determinant, and square-root guards.** The aliases are `a=D00`, `b=D01`, `d=D11`, `delta=ad-b^2`, `s=sqrt(delta)`, `t=sqrt(a+d+2s)`, `den=s*t`. Applying the lower spectral inequality to (1,0) and (0,1) gives `a>=lo>0` and `d>=lo>0`. For the determinant, the tested vector (-b,a) has squared norm `b^2+a^2>0` because a>0. Its D-quadratic form is exactly `a*(ad-b^2)=a*delta`, so the lower bound makes `a*delta>0`; with a>0 this forces delta>0. Thus s>0, `a+d+2s>0`, t>0, the two square-root identities are legal, and `den!=0`. In particular, all later divisions and `field_simp` calls are guarded, and no a=0, singular matrix, or negative square-root branch is concealed.

3. **Lines 68–70: literal D.** The Fin-2 case split reconstructs `D=[[a,b],[b,d]]` using precisely `hsym : D10=D01`. This covers both off-diagonal entries rather than replacing D by a different matrix.

4. **Lines 71–116: all four whitening entries.** With `N=[[d+s,-b],[-b,a+s]]`, the four expanded numerators of `N*D*N` are separately proved. The off-diagonal numerators equal `b*(s^2-delta)=0`; the diagonal numerators equal `(s*t)^2` using both `s^2=delta` and `t^2=a+d+2s`. The explicit four Fin-2 cases establish the matrix equality, so neither an off-diagonal nor a diagonal condition is omitted. The entrywise equality `A=den^-1 • N`, definitional symmetry `A^T=A`, and the guarded scalar identity `den^-1*den^-1*den^2=1` then give exactly `A*D*A=1`.

5. **Lines 117–137: strict positive quadratic form.** For each nonzero pair, `r2=xi^2+eta^2>0` is established from either nonzero coordinate. The lower spectral bound at (-eta,xi) yields `qrot=a*eta^2-2*b*xi*eta+d*xi^2>0`. The actual A quadratic form is expanded to `(s*r2+qrot)/den`; numerator and denominator are strictly positive. This proves strict positivity of the explicit A on every nonzero pair, with no assumption that whitening alone determines the positive branch.

6. **Lines 138–150: actual transpose orientation and preserved quadratic form.** For `u=(xi,eta)` and `v=A^T*u`, the bilinear identity, associative matrix/vector multiplication, symmetry of A, and `A*D*A=1` give `v^T D v=u^T u`. Expanding the literal symmetric D produces exactly `a*v0^2+2*b*v0*v1+d*v1^2=xi^2+eta^2`. This uses the transposed frequency map required by characteristic-function pullback, not an unrelated A-vector image justified merely by notation.

7. **Lines 151–193: both frequency-radius bounds, including zero.** The conclusion is first assembled with the established positive s/t, symmetry, whitening, and positive quadratic form. For arbitrary xi,eta, the coordinates of `v=A^T*(xi,eta)` are explicitly proved to be `xi*A00+eta*A10` and `xi*A01+eta*A11`. Applying both spectral inequalities to v and substituting the preceding identity gives `lo*||v||^2<=||u||^2<=hi*||v||^2`. The radii and both spectral square roots have the necessary nonnegative/positive signs before `sq_le_sq₀` and division are used. The upper spectral inequality gives the lower radius bound `||u||/sqrt(hi)<=||v||`; the lower spectral inequality gives `||v||<=||u||/sqrt(lo)`. The proof never divides by either radius or requires u≠0, so (0,0) is included and both sides reduce to zero. No eigenvalue-separation or off-diagonal-nonzero assumption excludes scalar/diagonal/repeated-spectrum cases.

8. **Lines 194–218: full public statement.** The blank separator and full public signature are covered. It adds exactly the all-entry estimate to the private package and matches the frozen declaration and actual public type as recorded above.

9. **Lines 219–242: complete entrywise bound.** The public s/t/A aliases are definitionally the explicit formulas in its statement. Lines 225–227 invoke only the new local private helper with the original D/hsym/lo/hi/hlo/hhi/hspec, preserving its full package. With `U=1/sqrt(lo)>0`, frequency tests (1,0) and (0,1) yield respectively the norms of row 0 and row 1, since the frequency image is A-transpose multiplication. Both Fin-2 row cases are explicit. Squaring the nonnegative row norm and U legitimately gives `Ai0^2+Ai1^2<=U^2`. For each of the two column indices, the other square is nonnegative, so `Aij^2<=U^2`; `abs(Aij)>=0`, U>=0, `sq_abs`, and `sq_le_sq₀` then imply `abs(Aij)<=U`. This handles all four entries and does not replace an operator estimate by an unjustified pointwise claim.

10. **Lines 243–245: closure.** The final blank and closing section/namespace lines are covered. There are no additional hidden declarations, deferred proof obligations, or source-level proof-setting changes.

The complete argument uses only the frozen hypotheses, ordinary ordered-field/square-root reasoning, finite matrix expansion, and the explicitly proved intermediate identities. All nontrivial divisions and square-to-unsquared implications have the required sign hypotheses. There are no empirical/numerical checks standing in for general proof.

## Pinned API reading

Read-only targeted server inspection verified `lean-toolchain = leanprover/lean4:v4.36.0-rc1` and actual mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`. I did not execute Lean or change the package view.

I read the actual pinned source signatures for `Matrix.mulVec_mulVec` (`Mathlib/Data/Matrix/Mul.lean` lines 914–918), `Matrix.one_mulVec` (1028–1030), and `Matrix.dotProduct_transpose_mulVec` (1133–1135). The last states `x dot (A^T*y) = y dot (A*x)` over the relevant commutative semiring; it validates the rewrite orientation in the quadratic preservation step. The multiplication identity has the exact grouping used in the two subsequent rewrites.

I also read `Real.sqrt_nonneg` (`Mathlib/Analysis/Real/Sqrt.lean` 143–145), `Real.sq_sqrt` (177), and `Real.sqrt_pos` (285–286), plus `sq_le_sq₀` (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean` 758–759). These give exactly nonnegative square roots, squaring only for nonnegative radicands, positivity iff positive radicand, and equivalence of square-order and original order when both arguments are nonnegative. Every U22h application supplies those conditions. The deprecated `Mathlib/Data/Real/Sqrt.lean` is only a five-line forwarding module; the actual definitions were read in its current `Analysis/Real/Sqrt` target.

## Existing server evidence and full owner audit

All evidence in this section was read only after the mathematical review. The server run is `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22h-20261023`; the worktree is `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`. The receipt records branch `feat/oq3-open-domain-standardization`, parent `803d8d0fbea3c2a55b8167f7c1ff4902510f1b8e`. These are provenance, not a merge/acceptance claim.

| Evidence | SHA256 | Bytes / relevant outcome |
|---|---|---|
| `u22h-build-history.json` / remote `build-history.json` | `d365c18775e2bb83d1c79c9808dd79cea8e008f47c883be3e8dfb6a76342b181` | 1567 bytes; 50 lines; both attempts preserved |
| Remote `build-01.log` | `59508a2eba79b18e763ed607e45c235827b09bf44d79d963b451cc61feac02c9` | 1559 bytes; 28 lines; full failed-source attempt |
| Remote `build-02.log` | `5d4e55f4041f6e7cf6c9dcb674b1373e8053547eb29baf1012635e00da8cc891` | 547 bytes; 8 lines; full successful-source attempt |
| `u22h-Audit.lean` / remote `Audit.lean` | `368ddb8872f6264abdb1a74eb16dbde9733b15117796d9ae9c12696d343c1a73` | 1895 bytes; 44 lines; entire audit source read |
| `u22h-audit-record.json` / remote `audit-record.json` | `f712c728288031eabae8449c324a2107067cb0f693fb9c1dcd6c605794372ebf` | 499 bytes; 18 lines; exit 0, 5.4495877008885145 seconds |
| Remote `audit.log` | `1c86d855b0a9c3486a82176a7df75d12013073a5747351fcb27d1f4f31f4abae` | 2953 bytes; 54 lines; entire log read |
| `u22h-audit-environment.json` / remote `audit-environment.json` | `731870b69aed4dd259018b2c633015c2507acc48cf728bfd6ed1f285b37a89a5` | 583 bytes; 9 lines; accepted read-only view plus own new object |

The first attempt checked the complete 245-line source (`e1dcf9d00ee5727d45498e94be7fa919709634f6f744ce7fc9717b5d4d4bb040`, 10969 bytes), exited 1 after 15.169929107651114 seconds, and failed only at the two row-alias simplifications on lines 231–232. I read the full failed log and the exact archived source diff. The only changes to reach the reviewed version are adding `[A, s, t, U]` to those two `simpa` calls. The frozen public statement and all other proof lines are unchanged.

The second attempt checked the entire reviewed 245-line source at SHA256 `83520a430712a07148396f30f7c07619ef55bda9cc9e464a98eae63e071e874e`, exited **0** after **15.40020483545959 seconds**. The receipt and remote history agree on the exact source hash, complete scope, and one public target. The successful log contains the accepted thin-package mathlib local-changes warning and two style warnings about the `<;>` at line 135; it contains no error or proof-setting weakening. The source has no `set_option` command. A static inspection/scan of the entire reviewed source found no `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, or `implemented_by`.

The first owner audit for the successful source exited **0** after **5.4495877008885145 seconds**. I read its full 44-line source: it enumerates every constant whose actual owning module is `Shao.OQ3.QuadraticWhiteningSpectralData`, rejects owned axioms, calls `Lean.collectAxioms` for every owned constant, and rejects any axiom outside `[propext, Classical.choice, Quot.sound]`. It checks that the frozen public name is a theorem and that the expected public target is present. Its only `set_option` changes affect pretty printing (`pp.deepTerms`, `pp.maxSteps`), not proof checking.

The full audit output prints both exact declarations already blind-read and reports `U22H_FROZEN_DEFINITIONS 0`, `U22H_FROZEN_THEOREMS 1`, `U22H_ALL_THEOREMS 2`, `U22H_ALL_DECLARATIONS 2`, `U22H_AXIOM_GATE PASS`. Thus the two owned constants are exactly **one public theorem plus one private theorem**, with **zero generated theorems and zero definitions**. Both transitive axiom lists are exactly `[propext, Classical.choice, Quot.sound]`; private proof coverage is included. The local/remote actual-type inventories have the same SHA256 and full 47-line content. There is no audit coverage limited only to the public wrapper.

The recorded execution settings for both builds and the audit are server CPU14–17, native memory 8192 MiB, four jobs, `autoImplicit=false`, and the established accepted-source-view/shared-v34 package environment. The environment record lists only the new owned `QuadraticWhiteningSpectralData.olean` added to that view, without accepted-source modification or cache/package writes. I made no broad symlink-overlay status query, cache revalidation/hydration, installation, build, or audit invocation. The prior host-yield metadata problem does not erase execution evidence: the complete remote history, both archived sources, both build logs, and owner-audit log are present, hash-bound, and were read directly. I did not rerun a successful gate or rerun a command merely to recover output.

## Acceptance boundary

The independent semantic/proof review is complete and **CORRECT** for both actual declarations and all 245 source lines at the recorded hash; the reused exact-source server complete check and full transitive owner audit are **PASS**. There is no uncovered proof change or residual mathematical gap in U22h requiring another complete local-proof review solely because it reaches integration.

The reusable output is the literal positive symmetric whitening matrix with positive denominators, exact whitening, strict positive quadratic form, full two-sided true transpose-frequency bounds, and all-entry bounds. Integration must still match these exact hashes and interfaces. The later actual-law compact-family assembly and all original unclosed B/D and probability/analytic obligations remain outside this acceptance. No root closure or novelty claim follows from this finite-dimensional result.
