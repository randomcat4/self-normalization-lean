# U22DI / unit 194 complete independent review

STATUS: CORRECT

JUSTIFICATION: Both frozen declarations are proved with their complete original quantifiers and the exact single polynomial let-value. The lower moments are derived from the genuine absolute m-th moment of the same probability measure. The second theorem establishes actual polynomial integrability and its integral identity with genuine signed real raw moments. The exact successful server source, object, actual types and whole-owner recursive axiom evidence agree. No mathematical or evidence gap was found in this unit.

Reviewer: fresh non-author context `/root/oq3_u22di_full_review`, prescribed gpt-6.1-sol / xhigh. Review date: 2026-10-24. This report is the reviewer's only write. No Lean, build or axiom check was rerun, locally or remotely; no source, cache, branch or Git state was changed.

## Authority and complete coverage

Read math-theorem SKILL.md and its complete prompt-library, openai-workflow and Lean-verification references. Read workspace AGENTS.md, SERVER.md, takeover and restart instructions, current OQ3 REGISTRY fields, selected current TEAM ownership/resource state, and streamlined-acceptance-current.md. OQ3 owner is activated chat `01a1669a-bca1-75e0-9d87-d07baee7b90a`; old writer release is recorded; the child ceiling is one. Heavy execution belongs on server CPU14-17, one command at a time. This review used only read-only server operations and used no heavy command, subagent or outgoing cross-sidebar communication.

Read all 22 frozen scope lines, all 76 final production-source lines, all 19 actual-type lines, all 47 audit-source lines, and all five evidence JSON documents in full. Read the original server scope, both complete source snapshots, both complete build logs, complete audit source/log, actual types and all evidence JSON originals through tools/server.py. The local copies and corresponding server originals have identical hashes and byte/line counts below. Read the actually consumed primary Mathlib interfaces with surrounding variable/namespace context from read-only `git show HEAD:<path>`; missing sparse-checkout source paths were not hydrated. No DG or DH proof/report was read or used.

## Exact reviewed ledger

SHA256 values below were computed from bytes. Text files use UTF-8 and LF, with zero CR bytes.

| Local artifact | Lines | Bytes | SHA256 |
|---|---:|---:|---|
| hundred-ninety-fourth-unit-scope.md | 22 | 1648 | 7c8e01099717a97b0bbb765db8b1809fc71df71bf162bd5570c30e867b70bf02 |
| u22di-source.lean | 76 | 3352 | 7a060e9b5790c317c8c831f916b3c28e5094dc73a90ae4b34aa47fc4f81ef4bb |
| u22di-actual-types.txt | 19 | 1103 | b8df57f9b79d5d86c1afe63597b4f74ac6ee2c0e36bbdf6b904acebeaf19fd29 |
| u22di-Audit.lean | 47 | 2058 | 26ab94a03354986fe5ea13cf18dd596c7e6b185defd943b2029e283349d27b0e |
| u22di-receipt.json | 141 | 7698 | db564f00346643103ede4376f5a9eb72ab0029e4d9695f3d77e6b9ed2d24a296 |
| u22di-build-history.json | 50 | 2638 | df2711ba30dbeb5e802a7de7f584d3ef8899476b54b2b5dd777e27ee19543424 |
| u22di-audit-record.json | 18 | 498 | 25f3b4a2941a6dd83aad0521cdd975603bf6ef9f1a2a820aa94044be0fa824fb |
| u22di-audit-environment.json | 31 | 2485 | 6ebd68c634e77983286dc87fc19a827eb7f3f57c0cbd700e7e37051fd2e56ede |
| u22di-dependency-source-binding.json | 28 | 1951 | 4c8e69508ea1eb15680a69041bf7b56fd60509f846a9a8271715bcc84c959b7d |

Local files are under `C:/game/shao lean/drafts/oq3/`. Original evidence is under `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22di-20261023/`; the corresponding names are scope.md, source-02.lean, actual-types.txt, Audit.lean, receipt.json, build-history.json, audit-record.json, audit-environment.json and dependency-source-binding.json.

Both complete theorem headers, including the sole P let-value, compare exactly to the frozen scope after removing only the proof delimiter and outer whitespace. Final source lines 1-6 import only Mathlib and set the namespace/scopes; lines 74-76 close them. There are no additional hypotheses, parameters, project imports or hidden top-level definitions. A forbidden-token scan of the complete final source found no sorry, admit, axiom, unsafe or native_decide.

## Source-to-statement and proof review

Theorem 1, `Shao.OQ3.integrable_scalar_power_of_absolute_moment`, final source lines 8-30 and actual-type lines 5-10:

- The domain is real x, ν is the actual given Borel measure on the reals, and its only measure-class premise is IsProbabilityMeasure ν. The only moment premise is Integrable (x ↦ |x|^m) ν. Every natural j with j ≤ m is quantified, and both absolute-power and signed-power integrability are concluded for that same ν. The actual elaborated type preserves all these binders and conclusions.
- Lines 12-13 use finiteness of a probability measure to make the real constant 1 integrable, then add hM. Thus the dominator is the genuine integrable function 1 + |x|^m; no lower-moment premise is inserted.
- Lines 14-20 prove the pointwise domination. If |x| ≤ 1, nonnegativity and pow_le_one₀ give |x|^j ≤ 1, while |x|^m ≥ 0. If this inequality fails, 1 < |x|, so pow_le_pow_right₀ with j ≤ m gives |x|^j ≤ |x|^m; adding 1 preserves the bound. The boundary |x| = 1 is in the first case. No positive-order restriction is needed.
- Lines 21-25 apply Integrable.mono' with actual a.e. strong measurability from continuity of the absolute-value power. The pointwise `change` normalizes the function power `(abs ^ j) x` to `|x| ^ j`; Real.norm_eq_abs, abs_pow and abs_abs give exactly the real norm bound required by mono'. It is not a function-space norm bound.
- Lines 26-30 derive signed-power integrability by the same domination theorem, now from the already established |x|^j integrability. Continuity of the identity power supplies measurability; the second `change` normalizes `(id ^ j) x` to x^j; the identity ‖x^j‖ = |x|^j proves the norm bound. Negative x and odd j are covered without changing the signed function.
- When m = 0, j ≤ m forces j = 0 and both functions equal 1, including at x = 0 under natural-power conventions. j = m is included. There is no integrability conclusion inferred merely from a totalized integral value.

Theorem 2, `Shao.OQ3.scalar_integral_taylor_polynomial_eq_moments`, final source lines 32-72 and actual-type lines 11-19:

- The only inputs are the same ν/probability/m/hM and an arbitrary real t. P is exactly x ↦ Σ j ∈ range m, (((t*x : ℝ) : ℂ)*I)^j/(j! : ℂ). It is a local let, not a freely chosen polynomial or an extra premise. The actual elaborated type retains this exact value and concludes both Integrable P ν and equality of its actual complex integral to Σ j ∈ range m, (((t : ℂ)*I)^j/(j! : ℂ))*((∫ x, x^j ∂ν : ℝ) : ℂ).
- Lines 44-48 prove the exact pointwise factorization of each literal Taylor monomial. Complex.ofReal_mul and Complex.ofReal_pow correctly cast the real product and real power, mul_pow distributes natural powers, and commutative-ring normalization rearranges the complex factors with the same factorial inverse. This is equality, with the complete imaginary phase retained; no absolute moment replaces x^j.
- For each j ∈ range m, lines 52-55 obtain j < m from mem_range and then j ≤ m. Theorem 1 supplies actual signed real-power integrability. Integrable.ofReal then supplies integrability of its complex embedding over exactly ν.
- Lines 56-57 multiply this integrable function by the fixed complex coefficient and transport it along the symmetric pointwise factorization. This proves integrability of each actual Taylor monomial. No assumption of coefficient coherence, an error bound, exponential moments, or integrability of the Taylor terms was supplied.
- Line 58 applies integrable_finsetSum to these terms to obtain integrability of the actual P. Lines 60-63 unfold precisely its finite-sum value and use integral_finsetSum with the already established term integrability. The finite integral exchange therefore applies to genuine Bochner-integrable terms.
- Lines 64-72 compare the same finite index sets term by term. integral_congr_ae uses the exact factorization, integral_const_mul extracts its fixed complex coefficient, and integral_complex_ofReal identifies the complex integral of the real power's embedding with the complex cast of its real integral. Although the last two Mathlib identities are stated for totalized integrals, the earlier signed-real and complex integrability proofs already establish the intended genuine moments; no undefined-integral shortcut is used.
- Every occurrence of ν is the original measure. In particular the coefficients are signed raw moments, not centered moments, absolute moments, a proxy sequence or moments of a different law. No lower-integrability or coefficient identity hypothesis has leaked into the elaborated statement.
- m = 0 gives an empty sum and P = 0; the term condition is vacuous and the finite-sum theorems include this case. For m > 0 and t = 0 the j = 0 term is retained as 1 and positive-order terms vanish; there is no division by t or cancellation requiring t ≠ 0. Negative t, negative x and odd moments are covered by the exact cast/ring identity. Every natural factorial is positive and hence its complex cast is nonzero, including 0! = 1; the proof does not need an additional denominator premise or divide by a moment.

## Consumed primary interfaces and bindings

All three primary dependencies are at Mathlib commit `807d3836b165983210ee2ecf3cd28f239436949c`. The server package link resolves to the existing shared-v34/packages/mathlib read-only view. For each entry I recomputed the primary source hash from the pinned Git object and the consumed object hash/size from the actual file, and all equal the pre-first-kernel binding and receipt.

| Primary Mathlib source | Source SHA256 | Object SHA256 | Object bytes |
|---|---|---|---:|
| MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean | 272fbf423443f1cd4aa032396f85a19c2f4f80b9fe9df655de16b0df655a22c3 | 285e28dc79da676e3227511643130775980fb6b448c7910e4a50dc3cbb6211dc | 259160 |
| MeasureTheory/Integral/Bochner/Basic.lean | 66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670 | f5094fe4e519cc8ffde3283787cbd42f5f686cd9121e35776578902dadae75a7 | 688952 |
| MeasureTheory/Function/L1Space/Integrable.lean | d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759 | 6fe2b53c5cd131f560eeff2765fbdbbf956a12b8676cb5ec9b2bae9c74239aa0 | 621928 |

Read the full consumed interfaces and their relevant ambient typeclasses: Integrable definition lines 55-60; mono' 104-106; congr 126-127; integrable_const 165-167 with IsFiniteMeasure; add 419-423; integrable_finsetSum 432-445; const_mul 1023-1030; ofReal 1091-1099. The real and complex codomains satisfy all required normed/continuous-add/RCLike conditions. Read Bochner.Basic integral_finsetSum 248-251 with its actual per-term Integrable premise, integral_const_mul 288-290 and integral_congr_ae 299-301, with the ambient measure/normed-space context. Read ContinuousLinearMap integral_ofReal/integral_complex_ofReal 158-163 with its ambient real/complex embedding context. The casts and the finite-sum hypotheses match the proof's functions.

Also read the exact pinned power interfaces in Mathlib/Algebra/Order/GroupWithZero/Basic.lean: pow_le_one₀ lines 437-438 requires 0 ≤ a and a ≤ 1; pow_le_pow_right₀ lines 500-502 requires 1 ≤ a and exponent order. The proof supplies these conditions explicitly. These are known library tools, while both claimed unit declarations are proved here; no missing project lemma is renamed or assumed as an equivalent blocker.

## Reused original server kernel evidence

The frozen worktree is `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`, branch `feat/oq3-higher-characteristic-expansion`. Read-only Git queries confirmed current HEAD `e628d42b737b785ab3d29ac5511258ed0ad847cb` and tree `c4ec2880ef7431941f59582c283618002bdb9044`. These are the existing author checkpoint, not a new acceptance commit. Current production source is exactly the reviewed 3352-byte/76-line source hash above. The pinned lean-toolchain is `leanprover/lean4:v4.36.0-rc1`.

Attempt 01 is preserved, not accepted: 74 lines/3274 bytes, SHA256 `1820f4b771f4cde1d88e9eac613f7f8c9cb1146009d4287a144ec3fd44442bda`; exit 1 in 4.589058687910438 seconds. Its complete 1241-byte log has SHA256 `931558ab1faccb517bbbab7ef99c61a0ac360bbe2ffef789203bed04fecd2985`. The actual errors are the unnormalized `(abs ^ j) x` and `(id ^ j) x` pointwise expressions. A complete source comparison shows exactly the two proof-only `change` additions at final lines 24 and 29; frozen statements and P are unchanged.

Attempt 02 is the first complete success on the final source: exit 0 in 4.630347993224859 seconds, 133-byte log SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`. The complete log contains only the known Mathlib local-changes/overlay warning and no Lean diagnostic. The recorded gates use CPU14-17, native memory 8192 MiB, jobs 4 and autoImplicit=false. Failed evidence remains intact; no successful gate was repeated for this review.

The resulting current production object is 167208 bytes, SHA256 `50945f7760c63652e5759f71ce3e903ea7a1bd0717ac70c7ec8f4845f19b4209`. The audit's accepted-source-view object resolves to this exact worktree object, and its bytes/hash were verified independently by read-only inspection. This connects the original audit to the actual checked production object, rather than merely to a matching theorem-name prefix.

## Whole-owner actual declarations and transitive axioms

Read Audit.lean in full. Lines 12-19 require the frozen targets to be theorems and the frozen definition list is empty. Lines 23-27 traverse the entire environment constants table and select by `env.getModuleIdxFor?` and the actual owning module `Shao.OQ3.ScalarTaylorMomentPolynomial`. There is no public-name-prefix filter, so private, generated or external-namespace constants owned by the module would also be covered. Lines 28-32 reject owned axioms and run Lean.collectAxioms recursively for each owned constant, allowing only propext, Classical.choice and Quot.sound. Lines 33-37 emit complete types and every defnInfo value; lines 41-47 require a nonempty result and both frozen targets and report the actual totals.

The original audit exits 0 in 5.463102063164115 seconds on the same final source/object, with the same recorded CPU/memory/jobs/autoImplicit settings. Its complete 1355-byte log has SHA256 `e1b1952ba28c430d4e9bd0c896e734e54f4b25fff9e63a75915333a92d18e869`. I verified that removing only the two known overlay-warning lines and five final summary lines yields exactly all 19 lines of actual-types.txt, with no omission or truncation. The log ends U22DI_AXIOM_GATE PASS.

| Actual owned declaration | Complete actual-type coverage | Kind | Recursive axioms | Verdict |
|---|---|---|---|---|
| Shao.OQ3.integrable_scalar_power_of_absolute_moment._simp_1_1 | actual-types lines 1-4: forall any Preorder and a, (a ≤ a) = True | theorem, generated | propext | CORRECT: reflexivity converted to proposition equality; no added moment premise |
| Shao.OQ3.integrable_scalar_power_of_absolute_moment | actual-types lines 5-10, source lines 8-30, fully reviewed above | theorem, public | propext, Classical.choice, Quot.sound | CORRECT |
| Shao.OQ3.scalar_integral_taylor_polynomial_eq_moments | actual-types lines 11-19, source lines 32-72, exact P included, fully reviewed above | theorem, public | propext, Classical.choice, Quot.sound | CORRECT |

Derived from the actual whole-owner enumeration and kind records: 3 owned constants, all 3 theorems; 2 frozen/public theorems; 1 generated theorem; 0 definitions, 0 definition values to inspect, and 0 additional private or other owned constants. These counts agree with the audit output and receipt. Every actual type is covered and every required definition value is covered vacuously. All recursive axioms belong to the standard whitelist; no new axiom or untrusted proof escape appears.

## Acceptance extent

CORRECT and complete for the two exact U22DI auxiliary declarations and all actual module-owned declarations above, with original successful server kernel and whole-owner recursive-axiom evidence reused. The original receipt's author-pending-review status is historical; this report supplies the missing independent complete review for precisely the bound source version. It does not modify that receipt or authorize a merge.

The unit is Mathlib-only and does not consume pending DH, qualified DG, or a root integration baseline. The latest v65 root notice is informational: main `278190b7969ec05b90434a39c5666a51bfe87e60`, accepted `32618ea59e6fde25d96fac17a638cd3327805d5c`, tree `91b246fba9620df60d03f0d742b9d988a04f405c`, receipt SHA256 `3052f4ff588e8e77baa1f5808aeb55ebb17d249baafe1107de144ff26481f338`; none of its gates was replayed or is needed as a new premise here. The older v64 labels inside the preserved author JSON do not alter the verified Mathlib-only dependency binding.

This is a standard finite-moment/coefficient-coherence enabler, not a novelty claim or a proof of an original root theorem. OQ3 B/D, higher Edgeworth, full-frequency inversion/exterior and new-rho Laplace remain OPEN. Original source scope, p54 repairs, strict original beta scope and external-result attribution remain unchanged. There are no unresolved correctness gaps within the reviewed U22DI scope. Review complete; after verifying this report's bytes/hash/line count, the reviewer stops tools and writes.
