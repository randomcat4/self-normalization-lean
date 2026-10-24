# U22DG192 independent complete review

STATUS: CORRECT
MECHANICAL STATUS: LEAN_FULLY_CHECKED for this exact single-module theorem, reusing the original saved server kernel and whole-owned transitive-axiom gates; no gate was replayed.
GAPS: None within the frozen scope.

## Independence and coverage

Fresh non-author proof/source-to-statement/type/value/all-owned-axiom/saved-server review. The reviewer did not author or edit the theorem, freeze, audit program, receipt, dependencies, or server artifacts. The assigned reviewer configuration is gpt-6.1-sol / xhigh. No subagents, sidebar chats, outgoing coordination messages, local Lean, server Lean invocation, build, axiom-gate replay, cache mutation, or branch mutation was used. The sole write is this report.

I read AGENTS.md, SERVER.md, the current ownership/resource/acceptance instructions and selected current TEAM/REGISTRY/takeover fields, and math-theorem with its required reviewer/Lean references. REGISTRY identifies activated OQ3 lead 01a1669a-bca1-75e0-9d87-d07baee7b90a, old writer released, child ceiling one. This is a bounded reviewer assignment, not lane or integration ownership.

Complete coverage: all 65 source lines (3105 bytes), all 11 freeze lines (1092 bytes), all 6 actual-type lines (298 bytes), all 47 audit-program lines, the complete build-history/receipt/audit/environment/dependency records, both original build logs, the original complete audit log, and the exact repair diff. All owned declarations are covered: 1 public theorem, 1 actual theorem, 0 private/generated declarations, 0 definitions or definition values, and 0 statement lets. No scope is deferred to a partial proof review.

## Exact source and statement fidelity

Module: `Shao.OQ3.ImaginaryExponentialTaylorRemainder`.
The sole theorem is `Shao.OQ3.imaginary_exponential_taylor_remainder_bound`.

The frozen complete declaration and source header compare exactly, including all quantifiers and the conclusion. The elaborated actual type independently shows precisely:

`forall (m : Nat) (t : Real), norm (Complex.exp ((t : Complex) * Complex.I) - sum over j in range m of (((t : Complex) * Complex.I)^j / (j.factorial : Complex))) <= (Real.exp 1 + (m : Real) + 1) * abs(t)^m`.

Thus the theorem concerns the genuine complex exponential on the imaginary axis, the exact first m Taylor terms j=0,...,m-1, and actual natural factorials. It has no positive-order, small-argument, coefficient-bound, exponential-moment, probabilistic, integrability, or hidden typeclass premise. The actual type has no statement let or additional implicit mathematical hypothesis. Source lines 1-7 and 64-65 only establish imports, notation, namespace and the noncomputable section; they add no mathematical assumptions. No project producer theorem is consumed.

## Complete proof assessment

- Lines 13-16: the complex norm is multiplicative, the real embedding has norm abs(t), and norm(I)=1, giving norm(t*I)=abs(t). The common factor abs(t)^m is nonnegative for every natural m.
- Lines 17-26, abs(t)<=1: the unrestricted primary Mathlib complex Taylor remainder theorem applies at x=(t:Complex)*I and n=m. Rewriting its norm yields abs(t)^m*exp(abs(t)); exponential monotonicity gives exp(abs(t))<=exp(1). Both multiplications preserve inequality because abs(t)^m>=0. Nat.cast_nonneg gives m>=0, so exp(1)<=exp(1)+m+1. Every step has the required sign condition.
- Lines 27-43, abs(t)>1: hence 1<=abs(t), so 1<=abs(t)^m. For each j in range m, j<m implies j<=m. The proof derives both 1<=j! and 0<j! from natural factorial positivity, rather than assuming a coefficient estimate. Norm_div, norm_pow and norm_natCast give the exact norm abs(t)^j/(j!:Real). The positive-denominator division equivalence and 1<=j! bound this by abs(t)^j; power monotonicity for a base at least one then bounds it by abs(t)^m.
- Lines 44-51: the finite-sum triangle inequality and the pointwise term bound imply that the polynomial norm is at most card(range m)*abs(t)^m = m*abs(t)^m. The sum is exactly the frozen Taylor polynomial; no coefficient or summand is substituted.
- Lines 52-62: norm_sub_le and the primary exact identity norm(exp(t*I))=1 give the remainder bound 1+m*abs(t)^m. Since 1<=abs(t)^m, this is at most (m+1)*abs(t)^m. Positivity of exp(1) and the common nonnegative power finish the stated bound. The nlinarith step at line 60 uses the explicitly available inequality 1<=abs(t)^m and is valid elementary arithmetic.

Boundary audit: m=0 is allowed in both branches; range 0 is empty and every zero-th power, including 0^0, is 1. There is no division by m and no factorial denominator can vanish. At t=0 with m>0 the true Taylor remainder and the right side are both zero; the small branch's unrestricted Mathlib theorem already covers it. At t=0,m=0 the remainder is 1 and the right side exp(1)+1. The threshold abs(t)=1 belongs to the small branch. Negative t is handled by the norm identity and abs(t), without a sign assumption. No limiting or exceptional case is omitted.

## Primary Mathlib dependency review

I read the exact primary `Complex.norm_exp_sub_sum_le_norm_mul_exp` statement and complete proof at Exponential.lean lines 484-509 from `git show HEAD:Mathlib/Analysis/Complex/Exponential.lean` at pinned mathlib 807d3836b165983210ee2ecf3cd28f239436949c. Its statement quantifies over all complex x and all natural n, with the exact first-n-term sum and no n>0 or norm(x)<=1 premise. This is the interface actually consumed at source line 18.

I also read `Complex.norm_exp_ofReal_mul_I` at primary Trigonometric.lean lines 951-953 and its norm_cos_add_sin_mul_I dependency at lines 946-949. It is the exact all-real identity used at source line 58. The repaired import therefore supplies an existing standard fact without adding a premise. Primary source bytes were obtained from the pinned Git object because the shared package view is sparse; existing original read-only .olean artifacts were hashed, not hydrated or rebuilt.

| Primary module | Source SHA256 | Original .olean SHA256 / bytes |
| --- | --- | --- |
| Complex.Exponential | 35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146 | ca281f1c68c9ac9cfb13de361e567fcd035ee7707da2a304a146537fd9bf12ce / 210592 |
| Complex.Trigonometric | f6f2c2bb6da4d7dac960bef8d07dc2e337c474b417726c1fd15e30c6b74caafb | dd9181d032d403d4e3fcced9d814a9266cd285a3c3129771fe135b1d70a960ab / 224680 |

Both match their saved dependency bindings. The Exponential binding predates the first kernel gate. The separate immutable repair binding records Trigonometric before the second gate; its server mtime 2026-10-23T23:46:13.425027Z precedes source-02 at 23:46:14.605024Z and the successful output object at 23:46:18.309014Z. The full frozen scope was saved at 23:45:15.317188Z before source-01 at 23:45:16.113186Z. No old CQ/CV proof or report was read or rechecked.

## Saved server kernel and ownership/axiom evidence

Server originals were read through tools/server.py at `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22dg-20261023`. Every listed saved local evidence hash below matches the server original. The current server theorem source also matches the immutable first-PASS source exactly. The observed original theorem .olean is 126360 bytes, SHA256 `3381985746146f4dd8da03e3033caf1eb2837f17a3628587c9334cca61b87ffc`; its embedded version header is 4.36.0-rc1. The server lean-toolchain is leanprover/lean4:v4.36.0-rc1; lake-manifest and shared-v34 mathlib Git HEAD both identify 807d3836b165983210ee2ecf3cd28f239436949c. The current package symlink resolves to the accepted shared-v34 view.

Original failed attempt 01 is preserved: source 64 lines / 3030 bytes, SHA256 `daa492d9c718b2d423f667cd997c2ee2e315f88b18e90c12ead683bccee018d1`; exit 1 in 4.101119043305516 s; log 1929 bytes, SHA256 `ec685821e3ec508694771a9cd3c72347a8bcb6897c660207197996db0dd47340`. I read all errors and the full source diff. The changes are only the existing Trigonometric import, specialized Complex.norm_mul/div/pow names, and an explicit add_le_add application correcting operand orientation. The theorem header is unchanged. This failure is not counted as a proof success.

Original first successful attempt 02: final exact source 65 lines / 3105 bytes; exit 0 in 4.01704740524292 s; log 133 bytes, SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`. Its complete output is only the known Lake shared-overlay repository-local-changes warning. It contains no Lean proof error, sorry warning, or theorem warning. The final source was frozen at this first success, and this reviewer did not replay it.

Original whole-owned audit: exit 0 in 4.659401096403599 s; log 550 bytes, SHA256 `490f74ee3d262ed0aa3a7c3532c3d21d52f5e0648a23a026eb937d6340e7299f`. The saved execution records specify CPU14-17, M8192, j4 and autoImplicit=false for both kernel attempts and audit. All Lean execution evidenced here is on the designated server; this review performed only read-only hashing, text inspection and metadata checks.

The complete 47-line audit program enumerates the entire environment constant map and filters by actual owning module using getModuleIdxFor?, rather than by namespace or a public-name prefix. Consequently private, generated, and externally namespaced constants owned by this module would also be visited. It rejects every owned axiom, calls Lean.collectAxioms on every owned constant, rejects any recursively collected axiom outside {propext, Classical.choice, Quot.sound}, prints every full owned type, and prints every owned definition value. It verifies the frozen name is a theorem. The original log reports exactly 1 frozen theorem, 1 actual theorem and 1 actual declaration, with 0 frozen definitions, and U22DG_AXIOM_GATE PASS. The printed axiom list is exactly [propext, Classical.choice, Quot.sound]. These counts agree with the complete source and actual-type file: there is no unreviewed private/generated theorem or definition value. No sorry, admit, axiom, unsafe or native_decide token occurs in the source.

## Exact artifact ledger

| Artifact | Lines / bytes | SHA256 |
| --- | --- | --- |
| u22dg-source.lean / server source-02.lean | 65 / 3105 | fa560d715fe1ee72ab65aadbc4825db4b3183339609a8b50a83f4dcb9cab7e27 |
| hundred-ninety-second-unit-scope.md / server scope.md | 11 / 1092 | 78fe81d784fbf2992d45f8c65bdebc87033c2040a2c5770af18b4b03b4a8f12e |
| u22dg-actual-types.txt | 6 / 298 | bba53bc38bb3438683baebf7448bdd622e354a078c9150bf6bf3aa2114f005bb |
| u22dg-Audit.lean | 47 / 2018 | 34fe97a8deee1bcdd68b781aea7b48dcd5cac813b56e585db6a73751952f35c8 |
| u22dg-receipt.json | 114 / 6659 | 7e0e3f8c2e720d7974d30235f12c8b8ce0e21556a0942e1a39b33790561c6dbe |
| u22dg-build-history.json | 50 / 3005 | 4ecf96a0fa75101b28e883d54ac376bf7ab19e601dd0213a411764d85c3e8bc9 |
| u22dg-audit-record.json | 18 / 497 | 3549f49e16749aa68e9850555b339a8f56f923376827ad742080d25f9fac707d |
| u22dg-audit-environment.json | 9 / 1569 | 5b37557aab0cb1f847b49d795b87423d13b9ab9f4deb7e05ce2c40989e0f32b6 |
| u22dg-dependency-source-binding.json | 21 / 996 | 706a207fd7a88e13d0a8bd16df47daed2cc855ad68d36d9b370408947fca7b3f |
| u22dg-repair01-dependency-source-binding.json | 9 / 494 | 3124d1512999e8d9833932000bf32494c9a127b34368b89dd281da4bcc6e6e05 |

All ten local artifacts above are UTF-8 without BOM and contain no CRLF. Source/header/actual-type counts were derived from the actual bytes and ownership output, not copied from a prior unit. Review acceptance is tied to this source SHA, not to an evolving publication branch head.

## Scope and final verdict

This is a valid standard all-order pointwise analysis building block. It does not prove characteristic-function moment integrability, actual moment/cumulant polynomial coherence, a higher Edgeworth expansion, full-frequency bounds, smoothing/inversion/exterior bounds, a new-rho Laplace result, or any original OQ3/root theorem. Those remaining interfaces must be supplied by future actual consumers; no closure or novelty claim is warranted here. The existing p54 repairs, strict original 0<beta<2/5 scope and external-result attribution are unchanged.

Final decision: CORRECT, with complete independent source-to-statement/proof and actual owned type/value coverage, and exact-source original saved kernel/recursive all-owned-axiom evidence accepted by reuse. No critical or noncritical mathematical/evidence gap was found within this frozen theorem's scope. No assumptions or bytes were changed to obtain this verdict.

Reviewer work is complete. After saving and verifying this sole report, all reviewer tools and writes stop; no continued runtime is implied by this final review.

Review completed UTC: 2026-10-23T23:54:41.248914+00:00
