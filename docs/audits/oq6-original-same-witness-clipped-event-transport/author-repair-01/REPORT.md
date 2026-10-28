# Unit245 affected proof repair01

STATUS: COMPLETE_LOCAL_AFFECTED_PROOF_REPAIR_UNCHECKED. This is the repair author's complete source candidate. It is not an independent affected-source acceptance, a kernel pass, an axiom receipt, a machine-type join or a qualified result. `qualified=false`, `kernelPending=true`. No new mathematical interface is missing in the repaired argument; actual elaboration and the final declaration's default-budget completion remain to be tested by the lead.

The new complete source is `OriginalSameWitnessClippedEventTransport.lean`, SHA256 `85b9a4d687ebc8171b84dff11e4e9d923ae35b6837c75941b4c36f06ff225eac`, 193175 bytes and 2935 LF lines, UTF-8 without BOM or CR. It contains exactly one public theorem and no auxiliary declaration. All writes were confined to `C:/game/shao lean/drafts/oq56/unit245/author-repair-01/`. No Lean, server, PP/kernel/AX probe, upload, network, Git/API action, child context, model switch, cache write or shared-source edit was performed. The project pin remains Lean `leanprover/lean4:v4.36.0-rc1` / mathlib `807d3836b165983210ee2ecf3cd28f239436949c`; these pins were read, not executed or changed.

## Exact authorization, baseline and independence

The repair activation is `85375c40597fd35ef2da3f09c32b5e30c3bcc35ea81c69a064abdc1e1bf652f1`/19063B. All55 directly bound local inputs, the prior implementation-author FINALWRITE release `f823e4b916b84c2cef8db43523196999efc766b50593c51ea5012f8d03fa039a` and independent SOURCE-review FINALWRITE release `70380af9ec94a1b323910d17996dd0ac4e448c0ccc28e2d828efecddcc559e7c` were hash/length verified before the actual RUNTIME-ACK. Both released writer/heavy/inflight/pendingExternal/children/uncertain as zero. The ancestral Stage1 release `cb5b15e025f8cf4bc5c87614ceec72b7ef01911d59130bb42411f9189cd21047` was additionally verified after the initial ACK and before the first source edit; it is likewise FINALWRITE/all-six-zero. This timing is recorded explicitly rather than retrospectively claiming it preceded the ACK.

Preserved SOURCE001 is `f4ed3791005e6869768582b629e70d9f8c17da55f3b7f73f003e1c58ba70a93b`/192266B/2914LF. It had one complete independent mathematical SOURCE acceptance, whose exact verdict is `0bfa40bd4d3ec36ea18f6710b60d8a54701e28b83547e9331c8102e06b61b695`. Its first actual native attempt then ended naturally RC1 in24.40029141679406s with4 source errors/5 warnings and NOOBJECT. Receipt `27cc385286fd56698a6292a1b49357f5bc8f92594f0a3c48e8860739ffbfdc08`/24449564B remains on the server; its full local diagnostic projection is an unchanged bound input. All24185 protected old records, source and namespace were preserved and the owned process group ended. No AX was run on an absent object. This author neither replays nor reclassifies that failure.

The independent SOURCE judgment is reused only for exact unchanged source bytes and the unchanged mathematical interface. The three affected proof blocks below require the existing independent245 reviewer to judge the new bytes. I am the repair author and do not grant that acceptance.

## Repair1: exact original-to-reduced measurable-space direction

Old line2669 used `apply measurable_pi_iff.mpr` while the reduced m₀ instance was active on Ω. The server diagnosed that the synthesized source instance mN₀ was not definitionally the source instance mN determined by the goal's typing rules. The target theorem is the same full explicit Prop:

`@Measurable (Fin n → Ω) (Fin n → Ω) mN mN₀ id`.

New lines2669–2670 pass all structure-bearing arguments explicitly to the pinned existing equivalence:

`@measurable_pi_iff (Fin n → Ω) (Fin n) (fun _ : Fin n => Ω) mN (fun _ : Fin n => m₀) id`.

Thus its source is the original mN, its target coordinate family is the same existing m₀ and its target product is definitionally frozen mN₀. The unchanged following coordinate proof composes `@measurable_id'' Ω m₀ mΩ hm₀` with `@measurable_pi_apply ... (fun _ => mΩ) i`. Each coordinate therefore has source mN and target m₀, exactly as required. This is the same explicit-argument order recorded by the pinned primary theorem and the accepted `OriginalCountablyGeneratedModel.lean` lines249–255. That accepted source was read only as a bearing API/presentation reference; no old proof or check was rerun.

The explicit carrier/structure families are literal copies of the frozen product RHS. They are inline theorem arguments; no new instance installation, measurable-space witness, data alias or ordinary interface row is introduced.

## Repair2: exact closed-tail set conversion and symmetric-difference direction

Old line2897 used `simpa only [hT0Literal, symmDiff_comm]` on the generic A∆E bound. The diagnostic showed original-before-perturbed while the goal required perturbed-before-original; ordered simplification did not establish the intended folding/orientation with the local Tη expression. The underlying finite-k generic result is retained unchanged.

New lines2898–2905 first prove the complete literal tail-set equality as an anonymous explicitly typed Prop by `congrArg` applied to `funext hT0Literal`:

`{x | z ≤ T0 (q x)} = {x | z ≤ if V x = 0 then 0 else (W x + D1 (q x)) / (V x * Real.sqrt (1 + D2 (q x)))}`.

The full carrier annotations and the full function-to-set callback are present in production SOURCE and ACTUAL-PROP-CONTEXTS. This equality uses the already proved pointwise original-statistic identity, including its exact zero branch. It neither invokes a.e. positivity of original V nor changes T0's convention.

After this single exact set rewrite, line2906 applies one directed `rw [symmDiff_comm]` to the sole outer symmetric difference. The target is now original-literal-before-perturbed. Line2907 supplies the same existing generic A∆E inequality by `exact`. Generic E specializes the literal relation `fun a b : ℝ => b ≤ a` at the same z; its quotient is definitionally the frozen Tηk, as also certified by unchanged hPerturbedLiteral. Generic A is exactly the rewritten original quotient with fallback0. Generic Z is definitionally the same `{x | V x = 0}`. No algebraic simplification, event alias, second model, or new hypothesis is used.

## Repair3: only the outer probability subtraction is reversed

Old line2903 used `simpa only [hT0Literal, abs_sub_comm]`. Its recorded nested failure was the deterministic `Lean.Meta.acLt` heartbeat200000 limit. A permutative absolute-subtraction simplifier can compare and reorder terms throughout the expanded local expressions. The concrete source hotspot is removed.

New lines2913–2915 instantiate `abs_sub_comm` with precisely the two outer real probabilities and apply it once with `rw`. The result has original-tail probability first and perturbed-tail probability second. New lines2916–2923 then use the same explicit anonymous tail-set equality as in Repair2. Line2924 supplies the unchanged final generic absolute-probability bound by `exact`. There is no global or local option change, AC simplification, broad unfolding or raised resource/launch limit.

The final original-measure conversion, now lines2925–2930, remains byte-exact to SOURCE001: the two existing map-real equalities replace the augmented T0 tail and augmented zero payment by their original P probabilities. The final constructor, now line2931, is also byte-exact.

The additional declaration-level `whnf` timeout at old line12 is preserved as a real fourth failure. The complete diagnostic alone does not identify a distinct mathematical or kernel cause for it. Removing the actual acLt hotspot is a concrete presentation repair; success of the whole declaration under the unchanged default200000 budget is still pending. No FVar/kernel-bug diagnosis or causal-fix claim is made. If the new source produces a genuinely separate budget obstacle, it must be diagnosed from that new exact receipt before any further scoped-option proposal.

## Exact unchanged mathematics and byte map

AFFECTED-SOURCE-MAP.json partitions every old/new byte into three replacements and four exact equal ranges, each with source coordinates and SHA256. The replacements are only old2669, old2897 and old2903; no other source byte changes. The new affected bodies lie in hIdm2669–2670, hSymmDiff2898–2907 and hAbsAugmented2913–2924. REPAIR-DIFF.patch is the complete readable diff.

The four equal ranges are:

- old/new lines1–2668, 177137B, hash `b7b7dd5f6c976d5d2bf0877fb5f7e96182fff984fb6ea974b9aa42046fcc0c59`;
- old2670–2896 → new2671–2897, 14197B, hash `74cdb126aea9830aabca6bdf9252d3e38538aa47b4c4ba5086b96f10e7447ad5`;
- old2898–2902 → new2908–2912, 208B, hash `cb6532f7b614e5c13fc58bab2ef6514a5b1d788b4e74434c0357738c519d11c5`;
- old2904–2914 → new2925–2935, 387B, hash `731c5065fe60b6cfd08347075fd1da9081a310cfea9e33ff28f11584130db45d`.

The frozen preamble, public head `c8ef50722a1c0ea0c3f8cd259ab6c5084ea89f9fd42c593c2d48a4ce4734c148`/38166B, initial intro, closing and exact227B h244 call remain byte-exact. The call still precedes the global six lets and all witness selections. Its complete expected h244 Prop is exactly the36190B frozen text, without whitespace normalization. h244 remains the sole inferred named fact.

All72 full named Prop strings and all16 complete enclosing-context strings are unchanged. All138 public ordinary rows and143 optional ordinary full types/RHS/scopes/status remain unchanged:94 used/49 unused. The seven approved instance rows and four actual proof instance installations remain unchanged. The generic theorem's fifteen result-local dependent lets are untouched. The sole cg/m₀ choices, literal μ₀ trim, original mAug/ν and actualη remain the same. No assumption, witness, model choice, ordinary alias or instance is added. The only new bound variables are the explicitly typed inline primitive congruence callback arguments and literal existing product families; ACTUAL-PROP-CONTEXTS records their full types, RHS, scope and exact occurrences. The two anonymous equality Props are also recorded completely. These do not create named facts or mathematical premises.

ACTUAL-PROP-CONTEXTS updates all311 existing production-source coordinate objects and every exact lexical-prefix source binding. Public/source context strings, original p51/p54 source coordinates and primary API records retain their old complete content. COMPATIBILITY binds the new source, prior SOURCE-only judgment, preserved native failure and exact unchanged/changed ranges. Its historical original implementation inputs stay explicitly marked as historical immutable bindings, not current new-source certification.

The first60 old universal conjuncts remain forwarded in their original order, followed by the frozen nine-conjunct new clause and the old final strict-window implication; the eventual-payment branch remains forwarded whole. p51/S3/S12 and S20–S23, and p54 §2's projection-zero repair remain unchanged: z=0 is included, T0=0 on original projectionV=0, and the original projection-zero probability is paid explicitly and remains unestimated. All original n/(n−2) coefficients, clipping1, h/μ/g/r/v/rho, scalar budgets and external attribution remain fixed.

## Remaining boundaries and exact handoff

No mathematical statement or original scope is expanded. The candidate claims no CDF continuity, atom-free law, physical/unclipped comparison, probability limit, vanishing original projection-zero payment, external Shao–Zhou input existence, source completeness, or root/OQ56 closure. The new finite-k clause remains free of an externalSZ premise; inherited conditional results retain theirs.

The first local static coordinate validation caught two inclusive lexical-prefix endpoints that mapped the start, rather than the end, of the replaced old proof line. Only hAbsAugmented and hAbsOriginal prefix metadata was corrected to2907 and2924; production source and all named Prop strings stayed exact. LOCAL-STATIC-FAILURE-01.json retains the precise failed-metadata hash, affected rows and correction. The affected local static validation is rerun; this is no Lean/kernel replay.

Local static checks verify all55 activation inputs and additional relevant local read bindings, frozen sections, the exact byte partition, all named types/interfaces/contexts, source coordinate transport, unchanged data/instance counts, UTF8noBOM/LF and absence of prohibited proof escape tokens. They are not Lean or independent proof checks. No old accepted producer/leafAX/proof review, P165/P164 or Rootactivation173 adoption is replayed. Requested model/effort are gpt-6.1-sol/xhigh; actual backend/model/effort and input/cached-input/output/reasoning-subset usage remain null.

Next dependency: lead exact intake/freeze of this source, then the same existing independent245 reviewer performs the affected complete-source review against SOURCE001 and receipt27cc baseline while reusing exact unchanged coverage. Only after its acceptance may the lead run NEWsource02 native. A successful new first original object requires allactual TYPE/required VALUE and transitiveAX evidence, followed by independent qualified final join. Until then qualified=false/kernelPending=true and unit246 waits. lastzeroRELEASE.json is the final write and releases all six activity fields to zero.
