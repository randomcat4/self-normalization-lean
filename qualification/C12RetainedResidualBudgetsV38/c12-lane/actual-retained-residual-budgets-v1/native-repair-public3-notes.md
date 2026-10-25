# public3 native001 static repair

STATUS: STATIC_REPAIR_CANDIDATE; native=NOT_RUN; formal qualification=false.
The assigned role is retained_residual_public3_native_repair_author, configured
fresh gpt-6.1-sol/xhigh. Actual backend/model/effort and input/cached-input/
output/reasoning-subset usage are unobservable and remain null. This author is
not an independent reviewer. C2/C12 remains OPEN.

The parent exclusively owns the full ActualRetainedResidualBudgets module.
This child writes only the five activated native-repair-public3 files. The
candidate contains one complete top-level theorem, exact frozen head plus
repaired body, without imports, namespaces or global helpers. It replaces only
original frozen source lines 1291-1867. No parent module, frozen source,
qualified library, common interface, coordination state or other author's file
was modified.

## Input binding and reading

Activation manifest SHA256:
051b15ed248fa5a952acff84226255de9f87bd15a6bc7949eb055aade17482ca.
All six input SHA256/byte pairs were verified before the runtime ACK and before
any proof write. The exact public3 head prefix is retained byte for byte.

| Activated input | SHA256 | Bytes |
| --- | --- | ---: |
| native001-frozen/ActualRetainedResidualBudgets.lean | eb3dc08dd050f33da808e801958ea08c07a9c8403a034d9d3164f093cb8daf4d | 104653 |
| native-repair-public3-frozen-head.lean.txt | 5f315287104739ff36ccb3c1752df86cba481b3e4ece6cb66b015cf36dd46f06 | 1386 |
| kernel001-compact-diagnostics.json | fc147c590f064657d29961f9cc03f0e77c744b2f30c3070764b1b46cef94e2c5 | 60932 |
| ../actual-retained-residual-complete-source-review-v1/review.md | 444eb4031152cdd11f3d89006e42e8fdc9a909cf3e0c5f59085bbb7268a7275f | 26013 |
| parent-source-stage-acceptance.json | bc35febbb52ed00115e94c96812ff744de99943816a22111332ae6586633c08d | 1351 |
| ../theory-actual-bad-retained-allranks-v1/full-proof-candidate.md | 56a1541ec6ac471bc863ae093acaa4dbcd28ac3dc18b19fd7889b93b2c8d7d85 | 14327 |

The complete original public3 head/body (1291-1867) was read. Consumed own-module
interfaces read in full: the three actual bill definitions (21-44), public
actual_retained_absolute_rank_gaussian_domination head (282-296), private
arr_late_fixed_suffix_gaussian_bound head and all transparent lets (337-358),
and private arr_absolute_rank_measurable_integrable head (560-571). The original
mathematical proof candidate was read in full. The qualified independent source
review's complete public3 and boundary sections (89-109) were read; its old PASS
is not claimed as independent qualification of the repaired bytes.

Additional read-only local bindings and actual consumed ranges:

| Library source | SHA256 | Bytes | Read scope |
| --- | --- | ---: | --- |
| library/Shao/Probability/SourceIIDGaussianProfileBudget.lean | 44960de7f98cd219860b8619b8f07ecfc52369a678fcb73331d8c9838ce1b8c7 | 44639 | 19-75: complete firstValue, prefixSurvival, gaussianProfiles, fixedGaussianWeight, rankGaussianWeight values and gaussian_weight_source_state head/lets; 130-139: complete fixed_gaussian_weight_measurable_bound head |
| library/Shao/Probability/SourceMarkedSuffixAveraging.lean | 879023fb756a2b6ea31fea61ffe159ffe6053aa94221302d1f09a4e2762e01c9 | 28305 | 36-39: suffixD full value; 143-151: suffix_normalized_geometry complete head |
| library/Shao/Probability/SourcePermutationReveal.lean | eb8ca14665fddaa34b063f3d53a42333db4dcf813c635e4978751b5251287b5a | 50583 | 40-45: remainingSum/remainingEnergy full values; 162-170: uniformPermutationLaw/revealLaw/randomReorder full values; 616-624: iid_randomPermutation_map_eq_pi complete head |
| library/Shao/Probability/SourceResidualRareSuffix.lean | 14cb5343b0862c2204f73babbae6bf8611c9ab27cd1fae019a49d011480406dc | 104099 | 1213-1271: complete iid_marked_and_unmarked_rare_real_suffix_budgets head, all transparent lets and outputs, at p=5; adjacent existing Gaussian proof portion 1282-1323 |
| library/Shao/Probability/SpitzerFinite.lean | 59ee31957ffec68aaff56d4eee5e833ef28fcb549bdce5f0649bf83216b1224c | 67096 | 32-41: reorder/head/tail full values |

The math-theorem skill, prompt-library, openai-workflow and lean-verification
references were read. Project-specific server-only rules and this explicit
static-only delegation supersede toolchain probing/execution in the general
skill. AGENTS.md and SERVER.md were read; compact current TEAM/REGISTRY fields
were consulted. No model contexts were spawned and no cross-chat message was
sent.

## Eight repair blocks against the frozen native001 lines

1. **1465, hA0:** replace failed `positivity` by explicit `div_nonneg`.
   The numerator is nonnegative by `pow_nonneg (abs_nonneg _) 3`; the denominator
   is nonnegative by `mul_nonneg hcut.1.le (Real.sqrt_nonneg _)`. The positive
   energy premise was already present in hcut, and is now consumed explicitly.
   No extra hypothesis or positivity at zero is asserted.
2. **1488, failed Bad branch:** record the negation of the entire marked
   selection by propositional reasoning from the existing `hbad`. Both the
   original outer Bad indicator and the complete marked selection simplify to
   zero. This also handles weak Bad failing without making any energy claim.
3. **1528, hFm:** replace the nonexistent measurable-function `.abs` field with
   `continuous_abs.measurable.comp` applied to the same measurable prefix sum.
   The integrand, measurable set and weak threshold remain identical.
4. **1680, hT:** use `congrArg` to subtract the same prefix-squares value from
   `(hperm p.1 p.2).2`. `randomReorder p` is definitionally exactly
   `Spitzer.reorder p.1 p.2`; this avoids a syntactic `rw` search through a local
   abbreviation. No permutation or suffix is changed.
5. **1686, hd:** the same `congrArg` transport with prefixSum and
   `(hperm p.1 p.2).1`, preserving the complete pre-label remaining sum.
6. **1731, hinj:** expose the already introduced function equality as
   `n - a.val = n - b.val` using `change ... at he`, before Fin.ext/omega.
   Together with `a.is_lt` and `b.is_lt`, natural subtraction is cancellable on
   this exact bounded domain. The early and late grid endpoints are unchanged.
7. **1784 and resulting 1781, hsumBound:** fix the multiplier explicitly to
   `4 * CL / (n : ℝ)` in its nonnegativity proof, including the real literal 4.
   First add the two known monotonicity inequalities at that exact coefficient;
   then use a separate ring equality to rewrite it as
   `(4 * CL) * ((1 / (n : ℝ)) * lateGrid)`. This prevents an unresolved implicit
   multiplier from leaking into `convert` and the inequality goal.
8. **1861, final Gaussian multiplication:** give the outer monotonicity witness
   the exact type `(0 : ℝ) ≤ 2`. The inner multiplier is the unchanged nonnegative
   `CR * delta`. Thus the original `2 * (CR * delta * Ax)` comparison is fully
   determined and preserves the universal final constant.

There is no diagnosed mathematical counterexample or changed premise. The
candidate preserves every threshold, sign, constant (including 8000100 and the
coefficient 8), cap quantifier, root scope and final conclusion. The diagnostic
warnings about deprecated if_pos/if_neg names are unchanged outside the actual
failed branch; a stylistic rewrite is not part of this repair.

## Validation and remaining work

Only deterministic local text/byte checks were performed: exact frozen-head
prefix; one top-level theorem; no imports/namespace/global helper; UTF-8 without
BOM and LF only; forbidden proof-token scan; exact six-input rehash; and eight
unique body replacement blocks. These are not Lean kernel checks.

The original native001 result remains natural RC1, with no object or AX pass.
Its server raw failure log is retained and was neither read nor altered by this
child. The supplied compact diagnostic blocks contain every assigned error;
no additional server extraction was needed. This child ran no Lean, AX, server,
upload, network, Git/API, installation, toolchain probe or delegated work.
Actual module-owned counts remain null. Native status remains NOT_RUN for the
new snippet.

Next responsibility belongs to the parent: assemble this exact snippet with its
independently owned preceding repairs, run the authorized source-bound server
kernel/all-owned transitive axiom gate, and obtain the required independent
review of the affected proof delta plus actual TYPE/FULLVALUE/owner receipts.
The original complete mathematical review can be reused only at its exact
covered scope; acceptance of the changed proof bytes is still pending.
