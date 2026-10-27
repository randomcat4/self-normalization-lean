# EZ237 independent complete final review

STATUS: CORRECT

This verdict covers exactly `Shao.OQ3.DirectionalMomentPolynomialContinuity`,
source SHA256 `2e7a41c289c933c8c829f215e96c47dc284423cdb654fcaa0cc2e326e6a5f757`.
The frozen statement, complete final proof, all two statement lets, and the
complete actual module-owned TYPE/axiom output have been reviewed. There is no
mathematical gap, assumption change, unreviewed owned definition VALUE, or
scope enlargement in this source. The server evidence below is reused from
the exact author receipts; this reviewer ran no Lean or server command.

## Independence, instructions, and read coverage

Fresh sole final reviewer: `/root/oq3_ez237_final_review`; author and reviewer
are separate. Delegation configuration: `gpt-6.1-sol`, `xhigh`, fresh context.
The reviewer has not edited the declaration, proof, receipts, or any dependency.
Only this review file is owned and written by this context.

I applied `math-theorem`, reading its SKILL.md, prompt-library.md,
openai-workflow.md, and lean-verification.md. I also read the Windows-shell7
skill for safe local reads. Project instructions supersede the skill's generic
local-toolchain probing: all Lean is server-only, and this review is explicitly
read-only outside its report. No math-ultra workflow was activated.

I read SERVER.md, the applicable AGENTS.md rules and final explicit OQ3
resumption, selected TEAM.md context, the REGISTRY.json current-authority
selection/current OQ3 fields, streamlined-acceptance-current.md, and the full
OQ3-RESUMPTION-PHASE-40.json. Current authority is the resumed existing OQ3
owner under ROOT_OQ56_OQ3_40, child ceiling 1; older pause clauses are history.
No server, Lean, AX, upload, Git, publication, child delegation, or other-chat
message was performed by this reviewer.

Reading order was frozen declaration first, then the entire final 78-line
source. I also completely read the 78-line failed source, actual-types.txt,
unit scope, primary API excerpt, receipt, audit-record, build-history,
Audit.lean, own-firstO-view-binding, and working proof.txt excerpt. Original
source read: `C:/game/shao/current/oq3/proofs/r2/report.md` lines 1-158 and
terminal sections 7-8; full `proofs/r2/repair01.md`; full
`C:/game/shao/current/oq3/verdict.md`. The verdict is at the OQ3 root, not in
proofs/r2. Existing accepted counterexample/producers were not re-reviewed or
rechecked.

## Exact local byte bindings

All following files were read as actual local bytes and SHA256/size/LF/CR
counts were independently recomputed. Every file has zero CR bytes.

| File in drafts/oq3 | SHA256 | Bytes | LF |
| --- | --- | ---: | ---: |
| u22ez-frozen-declaration.lean.txt | 666c02b24ade7e64ddccca3b106b40647a7eaa3d70148e1a7916009b1377e12b | 658 | 14 |
| u22ez-source.lean | 2e7a41c289c933c8c829f215e96c47dc284423cdb654fcaa0cc2e326e6a5f757 | 3316 | 78 |
| u22ez-attempt01-source.lean | d3aaa46fc741c9d73ce19c879295c0a14e837136a9e318e8410d545e15bf3719 | 3317 | 78 |
| u22ez-actual-types.txt | 005e3d537f833755a7d7dc85e27c6c7f3bb1d8ee42d98093a81dd8364d9324bb | 636 | 9 |
| two-hundred-thirty-seventh-unit-scope.md | 52520f7f3bf06672194474f9ca641f2dc7b39bd0ef4de3c490c235d5a1c2367d | 1381 | 22 |
| u22ez-primary-api.txt | c54f3baf1a05690144e34c1761ff20d2d0b6c52883e6f83cebb93f3a9b204176 | 450 | 8 |
| u22ez-receipt.json | 5a4bff17b758a46e50467e83b8ec3c59201b0b2f3ef6a28e04fddb680c91dead | 7911 | 267 |
| u22ez-audit-record.json | bb7cec186a33627befc2e523770e45059d197cec5e4e5a1b5db2acdcb6e7821c | 3038 | 103 |
| u22ez-build-history.json | 3b36685d7200e299d5d1c0fa8c61f29bd055851b885687b4d4c08975821dfc1c | 4527 | 164 |
| u22ez-Audit.lean | 7329235fd90ca1b491e2c4623a6705622861ac25faddc1713e0b9cb42f7ef14f | 2021 | 47 |
| u22ez-own-firstO-view-binding.json | ba238d379fc9bf4e7f825337afc28ae084a00a9b7fd6f8559bb1864f9d055bb9 | 581 | 10 |
| u22ez-proof.txt | 89e98c59a4144aa5423d7d4fdadd8655836aa1fddf87e7dccd32ff6988b3d17c | 2497 | 54 |

## Source-to-statement, quantifiers, and every statement let

The frozen 14-line declaration is an exact substring of the final source's
header, immediately followed by ` := by`; this was also checked mechanically
as text. The actual TYPE retains the same measure, natural k, hM, both lets,
all three conclusions, and quantifier order. There is one public theorem,
one actual module-owned theorem TYPE, and zero non-theorem VALUE records.

The domain is an arbitrary measure mu on the canonical measurable space
`Fin 2 -> R`; k is any natural number. The sole hypothesis hM is genuine
Integrable of the nonnegative radial kth power
`sqrt(y 0 ^ 2 + y 1 ^ 2) ^ k`. There is no probability, finite-mass,
covariance, centeredness, nonzero-frequency, k-positive, or continuity premise.

Statement let M is exactly the actual integral of
`(z.1 * y 0 + z.2 * y 1) ^ k`. Statement let b is exactly the integral of
`y 0 ^ j * y 1 ^ (k-j)`. They are fixed definitional lets, not arbitrary
functions or assumptions supplied by a caller. Source line 22's `intro M b`
does not free them. The elaborator's printed `have M := ...; have b := ...`
represents these same let values. There is no coefficient proxy or coherence
assumption. Although b is defined for all naturals, integrability is claimed
only for j <= k, and the formula uses only such indices.

The conclusions are: every actual total-degree-k mixed coordinate monomial
is integrable; for every real frequency pair z the actual directional moment
has the displayed finite binomial expansion with those actual b_j; and M is
continuous on the real product space. No conclusion about a whole-frequency
error integral or asymptotic expansion is encoded in this theorem.

## Complete proof review

1. Source lines 23-42 prove mixed integrability without totalized-integral
   shortcuts. The target mixed function is continuous, hence strongly
   measurable for an arbitrary measure, as required by `Integrable.mono'`.
   At each y, set r = sqrt(y0^2+y1^2). Nonnegative squares give
   |y0| <= r and |y1| <= r by monotonicity of sqrt and sqrt(a^2)=|a|.
   Both bases are nonnegative. Power monotonicity and `mul_le_mul` therefore
   give |y0|^j |y1|^(k-j) <= r^j r^(k-j). The guard hj supplies
   j+(k-j)=k, so the product equals r^k. The resulting norm bound is
   pointwise, stronger than the required almost-everywhere bound. hM is a
   valid integrable dominator; no lower-degree moment or finite mass is used.

2. Lines 46-50 obtain each summand's genuine integrability before exchanging
   sum and integral. Membership in range(k+1) gives j<k+1, hence j<=k.
   The already proved hmixed is multiplied by the real constant
   z1^j z2^(k-j) choose(k,j). This remains integrable for every real z,
   including negative and zero coordinates.

3. Lines 51-59 prove the pointwise binomial identity. `add_pow` uses the
   j and k-j exponents matching the frozen statement. `mul_pow` separates
   the frequency and coordinate factors; `ring` only reassociates/commutes
   real multiplication. The coefficient is choose(k,j), with z1 and y0
   carrying j and z2 and y1 carrying k-j. No factorial, sign, exponent,
   index endpoint, or coefficient is lost.

4. Lines 60-71 first substitute that pointwise identity under the actual
   integral with `integral_congr_ae`. The exact pinned
   `MeasureTheory.integral_finsetSum` is then applied to the finite set and
   the full hterm proof. Its primary statement explicitly requires
   integrability for every index in the set, which lines 46-50 supply.
   It yields the sum of actual integrals. `integral_const_mul` extracts
   precisely the frequency/binomial scalar, leaving the exact b_j integral.
   Thus the formula is not an artefact of an undefined/nonintegrable Bochner
   integral being assigned zero. In fact hterm, its finite sum, and the
   pointwise equality also ensure the directional integrand is integrable.

5. Lines 72-75 assemble the conjunction. `funext hformula` identifies M
   with the actual finite polynomial in the two frequency coordinates.
   Each b_j is a fixed real scalar; coordinate maps, natural powers,
   multiplication, and a finite sum are continuous. `fun_prop` therefore
   proves Continuous M. No assumed moment, cumulant, CGF, or error-function
   continuity is used, and no limit/integral interchange is used to obtain
   this continuity.

Boundary/quantifier attacks found no gap. For k=0, hM is Integrable of
constant 1 (including the 0^0=1 convention), so the necessary finite mass
is already supplied. The only index is j=0 and both integrands are constant
1, giving the correct constant polynomial. For k>0, an arbitrary measure
can have infinite mass at the origin while hM remains integrable; the proof
still works because each total-degree-k mixed monomial vanishes there.
The identities with zero coordinates and zero frequency use ordinary
natural powers and remain valid at both endpoints j=0 and j=k. No division
by a frequency, radius, or moment occurs. All y and all z are covered.

## Pinned API repair and retained failed attempt

The full failed source differs from the full successful source by exactly
the single textual substitution `integral_finset_sum` -> `integral_finsetSum`.
This equality was independently checked over the entire source texts.
The complete declaration and all mathematical proof steps are unchanged.
The primary API excerpt gives the actual statement and complete short proof
of integral_finsetSum in Mathlib/MeasureTheory/Integral/Bochner/Basic.lean,
file SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`.
It uses integral_eq_setToFun and setToFun_finsetSum with the supplied hf.

The working `u22ez-proof.txt` still contains the old underscored identifier.
It is a retained pre-repair proof excerpt, not the accepted compiling source
or the object binding. This review certifies the complete final source hash
2e7a41c2... above; it does not relabel that older excerpt as the successful
source. No archived bytes were modified and no proof repair is requested.

The build history retains attempt 1, source d3aaa46f..., RC1 in
5.142631266266108 seconds, log SHA256
`22fd6f1190ef3fc1867ac039c0922c0969054533e76b995a000d476f2a47bdba`
(264 bytes). The task identifies its diagnostic as the unknown underscored
identifier; the exact source delta and supplied pinned API agree with that
diagnosis. It remains a failed attempt, never a proof pass or uncertain
in-flight request. Attempt 2 is the first successful new-source attempt.

## Exact-source kernel / first-object / all-owner axiom evidence

Project pins read from SERVER.md and the local lean-toolchain are
Lean `leanprover/lean4:v4.36.0-rc1`, mathlib
`807d3836b165983210ee2ecf3cd28f239436949c`, shared-v34 package view.
This reviewer did not probe or install local Lean, compile, retrieve a binary,
or replay a successful old gate.

The consistent receipt/build-history records bind native attempt 2 to the
exact final 3316-byte/78-LF source: RC0, 5.109121363610029 seconds, at
2026-10-27T17:21:32.520132+00:00, native -M8192 -j4, current phase40 OQ3
CPU36-39,44-47. Successful native log SHA256 is
`fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`
(133 bytes). The original successful object is recorded as SHA256
`a4ed64872afd870eef0304072455595dfc0f763b269f95810c7afd0780d15678`,
170528 bytes. The own-firstO binding points accepted-source-view directly
to that worktree object's path, with one new own-firstO link, zero old entry
changes, zero shared-cache writes, and zero binary copies.

The same-first-original-object all-owner audit is recorded RC0 in
5.6611781138926744 seconds, at 2026-10-27T17:22:36.384112+00:00. Audit log
SHA256 is `8d69bab3668ad0f916412f61889e7ae1766ce372310984a8f53a8a8be5dbc46c`
(888 bytes). I completely inspected the exact Audit.lean source: it scans
every constant whose actual owning module is this module, rejects new axioms,
collects each owned constant's transitive axioms, rejects anything outside
propext/Classical.choice/Quot.sound, prints every TYPE and non-theorem defn
VALUE, checks that the frozen target exists/is a theorem, and rejects an
empty owner audit. Thus the fixed public-target list does not hide private or
generated owned declarations. The supplied output and receipt identify one
owned declaration, all-theorem count 1, actual TYPE count 1, non-theorem VALUE
count 0. I read that entire actual TYPE and compared it with the freeze.
Its transitive axioms are exactly [propext, Classical.choice, Quot.sound].
Local source inspection and token scan find no sorry, admit, new axiom,
unsafe, or native_decide. `noncomputable section` does not add an axiom.

The receipt's nested memory-helper label phase39 is explicitly the reused
unchanged helper label, while the top-level resourcePhase is phase40; the
phase40 activation explains this alias. It is not a stale OQ3 pause or an
extra execution authorization. These are reused server records, not a claim
that this reviewer independently downloaded the server logs/object or
reobserved processes. Their source/type/audit bindings are mutually consistent
and match the locally recomputed exact hashes. No additional kernel or axiom
run is required by this review.

## Original-source fidelity, dependency reuse, and limits

The original report's positive route has fixed x, a regular unique saddle,
uniform moment and covariance control, and strict 0<beta<2/5; its terminal
scope excludes the equality endpoint and stronger claims. The repair and
verdict explicitly use Song's uniform-in-law weak-Cramer Edgeworth theorem,
rather than treating the original Angst-Poly diagonal presentation as the
corrected external attribution. They retain explicit far-field localization
and the accepted near-resonance counterexample. This finite moment helper
changes none of those hypotheses, p54 repairs, attribution, or counterexample.

The source imports ER229/ActualCGFNormalizedOcticPolynomial for the common
measure/calculus environment but invokes no ER229 mathematical theorem.
There is no new definition VALUE or hidden dependency replacing an actual
moment by a formal coefficient. Exact previously qualified import evidence
may be reused; this review adds no duplicate old-proof or old-gate work.

EZ237 is a valid auxiliary finite-polynomial continuity interface needed
before deriving actual CGF/finite Edgeworth Pn frequency continuity and the
weighted characteristic-function error's integrability. It does not itself
derive that latter integrability, perform any frequency integration, prove
an exterior estimate or inversion, close B-D, or prove the original OQ3/root
result. All those original remaining scopes stay OPEN. This review makes no
novelty or historical-priority claim; the argument uses standard domination,
the binomial theorem, finite integral linearity, and polynomial continuity.

## Verdict, usage, and release

Final verdict: CORRECT for the exact frozen EZ237 helper and final source
identified above, with complete source-to-statement/proof/all-let/all-owned
TYPE coverage and consistent exact-source reused kernel/recursive-axiom
evidence. No critical gap or required mathematical/source repair remains.
The parent must read this entire report before qualification.

Usage telemetry: model=`gpt-6.1-sol`, effort=`xhigh` per fresh delegation
configuration; input_tokens=null, cached_input_tokens=null,
output_tokens=null, reasoning_subset_tokens=null. Exact counters are not
exposed to this context; no estimates or subscription-allocation claims are
substituted for them.

Runtime release: COMPLETED_STOPPED. Sole write authority for
`drafts/oq3/u22ez-proof-review.md` is released upon this report's seal. No
further writes are pending. Reviewer-owned server/heavy/Lean/AX/upload/Git/
publication/child operations=0; inflight=0; pending=0. The only modified file
is this report. This is a completed bounded review, not a persistent
continuation mechanism.
