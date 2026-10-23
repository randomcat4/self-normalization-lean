# OQ3 U22au independent complete final review

STATUS: CORRECT

The global definition, both public theorem statements and complete proofs, the generated theorem, all proof-local values, and the exact frozen auxiliary scope are CORRECT. No critical mathematical or evidence gap was found. The genuine measurable finite real oscillation supremum and its finite-measure integrability are established; the source's quantitative averaged oscillation bound and original OQ3 B/D are not closed by this unit.

Reviewer: sole fresh independent complete final reviewer, separate from the author, assigned gpt-6.1-sol / xhigh. Applied math-theorem and the current project AGENTS.md, SERVER.md, compact TEAM/REGISTRY ownership, and streamlined acceptance. No math-ultra, model switch, child delegation, source change or statement revision occurred. This context owns only this report. The activated OQ3 owner and released previous writer were checked. All server observations used tools/server.py with CPU14-17 affinity and were read-only. No Lean/lake, kernel, axiom gate or accepted old proof was rerun. Actual input, cached-input, output and reasoning-subset token counts are not exposed to this reviewer; no invented counts or subscription-percentage allocation is supplied.

## Exact inputs and complete coverage

Local directory: C:/game/shao lean/drafts/oq3/. The complete final source was read, including imports, setup, the entire global definition VALUE, every proof-local value and proof step, and both closing lines: 97/97 lines, 4403 bytes. The full scope (26 lines), actual export (24 lines / 1464 bytes), Audit.lean (49 lines), receipt and audit-environment manifest were read. Complete actual ownership coverage is 4/4 constants: one definition and three theorems, comprising two public targets and one generated theorem; there are no private theorems in the export. Counts were independently derived from actual DECL/KIND/VALUE records and checked against the receipt, rather than copied from a descriptive count.

| Input | SHA256 | Lines / bytes |
| --- | --- | --- |
| hundred-twenty-eighth-unit-scope.md | 96c83b8eea718c35065f04bc681018e670cbeca3663056c757bf71fd3041144c | 26 / 2007 |
| u22au-source.lean | f1e693a8b9b2db416dd730bcdfb596030d768b911015bcfdfc50a16e97e62e2d | 97 / 4403 |
| u22au-receipt.json | fb3a105588e4a52ce7df6c03ae006bbb003f38bdcc6c2e9c8def5adb223e667e | 116 / 4441 |
| u22au-Audit.lean | 5581268eee4893fc18899a4dc01db56dabaac8c18855bfc2c2ab3b1f9741a4b5 | 49 / 2056 |
| u22au-actual-types.txt | 6ffe4fb44aecebd2853b382f45d52f22f7f20f91219356ac337366b81d30fe11 | 24 / 1464 |
| u22au-audit-environment.json | d2c314680972852ff0f1a8eaedc01d54ad0cf1ac1948221efba3c82ae3b50744 | 12 / 626 |

All these hashes were recomputed locally and match their server counterparts. These exact files are strict UTF-8, have no BOM or CR bytes, and use LF. The definition including its entire value and each complete public declaration before `:= by` match the frozen code after whitespace normalization. The archived source01-to-source02 diff changes only a proof of the absolute-value triangle inequality; no definition, quantifier, assumption or conclusion changes. Server snapshot mtimes put scope.md before source-01.lean and source-02.lean, consistently with the recorded preimplementation freeze; equality of the complete frozen interfaces was checked directly, independently of that metadata.

The observed server worktree is /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3, branch feat/oq3-cell-oscillation-probability, HEAD e541a9ec39cf235fad723cf465a2b6ba575f637c. The new source is untracked and byte-identical to run source-02.lean and the reviewed local source. Acceptance therefore binds the source SHA256, not HEAD alone.

## All complete actual owned types and definition value

The exact export below was read in full locally and in the existing server audit log. Each constant has the transitive axiom list `[propext, Classical.choice, Quot.sound]`.

```lean
-- Definition: Shao.OQ3.openBallOscillation
-- TYPE
(ℝ × ℝ → ℝ) → ℝ → ℝ × ℝ → ℝ
-- VALUE
fun f h z => sSup (insert 0 {r | ∃ u ∈ Metric.ball z h, ∃ v ∈ Metric.ball z h, r = |f u - f v|})

-- Theorem: Shao.OQ3.open_ball_oscillation_integrable
∀ (μ : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsFiniteMeasure μ] (f : ℝ × ℝ → ℝ) (C h : ℝ),
  0 ≤ C → (∀ (x : ℝ × ℝ), |f x| ≤ C) → MeasureTheory.Integrable (Shao.OQ3.openBallOscillation f h) μ

-- Generated theorem: Shao.OQ3.open_ball_oscillation_properties._simp_1_1
∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α} {ε : ℝ}, (y ∈ Metric.ball x ε) = (dist y x < ε)

-- Theorem: Shao.OQ3.open_ball_oscillation_properties
∀ (f : ℝ × ℝ → ℝ) (C h : ℝ),
  0 ≤ C →
    (∀ (x : ℝ × ℝ), |f x| ≤ C) →
      (∀ (z : ℝ × ℝ), 0 ≤ Shao.OQ3.openBallOscillation f h z ∧ Shao.OQ3.openBallOscillation f h z ≤ 2 * C) ∧
        (∀ (z u : ℝ × ℝ),
            u ∈ Metric.ball z h → ∀ v ∈ Metric.ball z h, |f u - f v| ≤ Shao.OQ3.openBallOscillation f h z) ∧
          (∀ (t : ℝ), IsOpen {z | t < Shao.OQ3.openBallOscillation f h z}) ∧
            Measurable (Shao.OQ3.openBallOscillation f h)
```

Definition verdict: CORRECT (source10-12). It is exactly the real conditional supremum of zero inserted into the set of actual absolute pair differences for two points in the moving open ball. No supremum has been replaced by a bound, measurable envelope, essential supremum, closed-ball functional or assumed integrable function. The definition is a total Lean real-valued function for every f; the theorem's global bound is what justifies interpreting its value as a finite genuine supremum. No finite-supremum assertion is made here for unbounded f. For h<=0 the open ball is empty, the set is {0} and the value is0. For h>0, z belongs to its own ball, so u=v=z already supplies0; insertion changes none of the genuine pair-supremum values relevant to the source's positive radii.

Generated theorem verdict: CORRECT. For every type universe and every PseudoMetricSpace, membership of y in the open ball centered at x of radius epsilon is definitionally `dist y x < epsilon`; the exported equality of propositions is justified by that definition/propositional extensionality. It has no hidden positivity or genuine-metric assumption. Its complete type and transitive axioms are covered by the actual owner audit and the successful source check.

## Complete proof verification: properties

Shao.OQ3.open_ball_oscillation_properties: CORRECT (source14-82). The exact quantifiers are arbitrary f:Real^2->Real, arbitrary real C,h, C>=0 and the pointwise global bound |f(x)|<=C for every x. There is no measurable, continuous, Lipschitz, probability, compactness or positive-radius premise.

Source23-25's sole term-level local `S(z)` is exactly the inserted-zero pair-value set from the global definition. It does not change a radius, center, pair, sign or function. Source26's hzero supplies nonemptiness for every z without requiring the ball to be inhabited.

Source27-35 proves hupper for every member r of S(z). If r is the inserted0, C>=0 implies0<=2*C. Otherwise membership supplies actual u,v in the exact open ball and r=|f(u)-f(v)|. The actual absolute-value triangle inequality is obtained from abs_add_le applied to f(u) and -f(v), with subtraction and abs_neg rewritten. The global hbound at those two points gives |f(u)|+|f(v)|<=C+C=2*C. The membership witnesses are not assumed to maximize anything, and no regularity of f is used.

Source36 packages this into genuine BddAbove S(z) with upper bound2*C. Source37-38 applies le_csSup with that boundedness and the actual0 member, obtaining0<=oscillation(z). Source39-40 applies csSup_le with the actual nonempty witness and hupper, obtaining oscillation(z)<=2*C. These are the correct hypotheses for a conditional real supremum, rather than complete-lattice rules applied without nonemptiness/boundedness. Source41-44 puts any specified genuine pair difference into S(z) and uses the same boundedness in le_csSup, proving the stated domination for every z,u,v and both membership hypotheses. Thus hnonneg, hsize and hpair refer to the actual global function, by definitional reduction of S.

Source45-80 proves openness for every real threshold t, with both threshold regimes covered. If t<0, nonnegativity gives t<oscillation(z) for every z, so source48-53 identifies the full superlevel set with univ and proves it open. If t is not negative, source54 derives0<=t and source55-77 proves the exact equality

`{z | t < oscillation(z)} = union over u,v and proofs of t<|f(u)-f(v)| of (ball(u,h) intersect ball(v,h))`.

For the forward direction, source61 applies exists_lt_of_lt_csSup to nonempty S(z) and the strict threshold inequality. This returns an actual member r>t and does not assume a maximum is attained. The inserted-zero case would give t<0, contradicting source54, and is eliminated at source63. The remaining member supplies exactly the pair u,v and t<|f(u)-f(v)|. The two original memberships u,v in ball(z,h) become z in ball(u,h) and ball(v,h) by Metric.mem_ball and distance symmetry (source68-69). The union's indices do not depend on z except through this ball membership.

For the reverse direction, source71-73 extracts actual u,v, their strict pair inequality and the two centered-ball memberships. Source76-77 reverses distance orientation correctly, and source74-75 combines the strict pair inequality with hpair to obtain t<oscillation(z). Thus neither direction relies on measurable f, a countable family of witnesses or an attained supremum. Source79-80 uses the topology's arbitrary-union rule and openness of the two balls' intersection. Uncountability of the pair union is harmless for openness; the proof never uses an unsupported uncountable union of merely measurable sets.

Source81 assembles exactly the bound, pair-domination and all-threshold openness components. Source82 uses measurable_of_Ioi: the preimage of Ioi(t) is precisely the already proved open superlevel set, hence Borel measurable in the usual product-real measurable space. The codomain Real has the needed BorelSpace, second-countable order topology and linear order. This is a proof of genuine Measurable for the actual supremum function; it does not assume f measurable. The two local `heq` values prove different correct set equalities for the two threshold branches; ht,ht0,hz,htr,huv and all extracted witnesses supply only the explicitly described logical evidence. No extra term-level function or measure is introduced.

## Complete proof verification: integrability and boundary cases

Shao.OQ3.open_ball_oscillation_integrable: CORRECT (source84-94). The exact additional object is an arbitrary measure mu on the fixed usual measurable Real^2, with the explicit IsFiniteMeasure instance. It is not assumed to be a probability measure, Gaussian measure, completed measure, or Lebesgue measure. All f,C,h assumptions remain unchanged.

Source89-90 obtains the four proven properties for the identical f,C,h. Source91 uses genuine integrability of the real constant function2*C under finite mu. The actual Integrable.mono' API requires AEStronglyMeasurable of the dominated function and an almost-everywhere norm bound by that real majorant. The earlier Measurable implies AEStronglyMeasurable because the codomain Real is second countable and metrizable with measurable opens; neither measurability of f nor completeness of mu is required. Source92 proves the bound everywhere, hence almost everywhere for this mu. Source93 rewrites the real norm as absolute value and removes that absolute value using the proved nonnegativity; source94 is exactly oscillation(z)<=2*C. There is no use of a totalized Bochner integral returning a default value when nonintegrable. The conclusion is the genuine conjunction AEStronglyMeasurable and HasFiniteIntegral.

All radius cases, including negative h and h=0, are covered by inserted zero and the all-real proof. Positive h permits arbitrary small or large balls without a compactness premise. C=0 forces f identically0 and oscillation0, consistently with all conclusions; the zero measure is included. Repeated points, equality at the upper bound, t=0, t<0, nonattainment of the supremum and arbitrary discontinuities/nonmeasurability of bounded f are covered. The global pointwise bound is genuinely needed for this proof's everywhere finite supremum; it is not replaced by an almost-everywhere bound. No claim of integrability for arbitrary infinite measures is made.

## Original source fidelity and qualified dependency reuse

Read in full repair01.md section2, lines43-110, including equations2-6, and report.md lines112-216, including the actual cell test, Gaussian oscillation/Edgeworth input and equations7-9. Original read-only source identities are:

- C:/game/shao/current/oq3/proofs/r2/repair01.md: SHA256 9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd.
- C:/game/shao/current/oq3/proofs/r2/report.md: SHA256 572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55.

The source test is f_Q=g_Q*indicator(B_Q), with the actual exponential weight and standardized cell. U22au supplies a real measurable pair-supremum oscillation and true integrability under any finite measure, hence a valid prerequisite for a future Gaussian integral comparison once the actual test's global bound is supplied. It does not require g_Q itself to be globally bounded: a bounded-on-cell g_Q can give a globally bounded indicator test by zero outside. That actual specialization and any later integration inequality still need to be assembled. The generic frozen hypotheses are adequate for the stated prerequisite, not an encoding of the quantitative desired bound as a premise.

The imported AQ source u22aq-source.lean has SHA256 df0428c0d002bdeb2a4c2e436c5024f32e6f58b61d8ef1e129953d1a07919909 locally and in the current server worktree. Its entire existing complete independent qualification u22apaq-proof-review.md was read and reused unchanged, SHA256 4d513e9cd8bd3ae775e697c5d39e8a4d4dc62247fac4aa6aa892ac167e784509 (138 lines / 28115 bytes). AQ supplies actual off-frontier membership and a closed-ball indicator two-point bound; the new proofs do not invoke an unreviewed AQ theorem or silently convert that pointwise bound into an integral/supremum bound. Its qualified object in accepted-source-view resolves to the own worktree object with SHA256 e03be4ab012a530b438d88ff5ea3fa6fc28420c86e1dfa6ad27799230f50479b, matching the qualified report. No old AQ proof or gate was replayed solely for this context.

The formal product-real norm is the maximum of coordinate norms, verified in the pinned primary Prod.norm_def/Prod.norm_mk. Metric.ball is the open ball for that norm, not a silently Euclidean ball. The qualitative statements here are correct in precisely this metric; no literal Euclidean radius, tube constant or covariance-whitening identity is asserted. Relating future source constants or actual standardized cell families to this metric still needs its own data.

This unit does not prove source repair01 equation4's quantitative Gaussian averaged bound, equation5's planar tube estimates or equation6's rate. It does not define/identify an external bar-omega functional, prove the actual Edgeworth comparison, instantiate a genuine covariance-whitening cell family, establish family-uniform geometry/constants, sum cell errors, close full exterior probability or prove source B/D. Those dependencies remain OPEN. No original-root closure or mathematical novelty is certified; this is a bounded auxiliary measurability/integrability result. Source assumptions, p54 repairs and external-result attribution remain unchanged.

## Pinned library conditions and existing server evidence

The server lean-toolchain file reads leanprover/lean4:v4.36.0-rc1. The actual mathlib path resolves to /root/rivermind-data/shao-lean-20261021/cache-overlays/shared-v34/packages/mathlib, HEAD 807d3836b165983210ee2ecf3cd28f239436949c. No toolchain invocation or library rebuild was made by this reviewer. Exact primary API declarations and their surrounding typeclass assumptions were inspected for le_csSup, csSup_le, exists_lt_of_lt_csSup, measurable_of_Ioi, Integrable, Integrable.mono', integrable_const, Measurable.aestronglyMeasurable, Metric.ball/mem_ball and Prod.norm_def. Each used primary file was byte-compared with git show at the pin and matched:

| Primary Mathlib file | SHA256 |
| --- | --- |
| Order/ConditionallyCompleteLattice/Basic.lean | f464444b33d463cfa8502c20a2a8c619108b1337a9003ae430383dce22be641a |
| MeasureTheory/Constructions/BorelSpace/Order.lean | b00231965385b4be92c215dff1d287910ee096833b96b4589d716fe7e9b5ad2e |
| MeasureTheory/Function/L1Space/Integrable.lean | d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759 |
| MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean | c40e8635520378f872941d129e70caba33dd2b5a054d0aebd77c3ef7a19a9e97 |
| Topology/MetricSpace/Pseudo/Defs.lean | 3463e90a92cb1c28bcf0062c46ea9ad4eb2737e1774232e8796bf69bad98d64b |
| Analysis/Normed/Group/Constructions.lean | 098a249c756acb481b5ca22d6563e3f21e29dd7318689034eabaf971a12e1216 |

In particular, exists_lt_of_lt_csSup needs the nonempty set and strict comparison, which source61 supplies; the pointwise le_csSup uses also require the proved boundedness. The measurable_of_Ioi codomain assumptions hold for Real. Integrable.mono' uses the real upper bound itself and requires the separate AEStronglyMeasurable evidence supplied at source91; this requirement is not omitted. The local-changes warning therefore does not hide a modified primary API used in this proof. The server lacks rg; the initial read-only API search failed for that missing executable and was completed using targeted Python source reads. This was not a Lean/gate failure, and no required final evidence was inaccessible.

Run: /root/rivermind-data/shao-lean-20261021/runs/oq3/u22au-20261023. The full two build logs, full audit.log, complete build-history and audit-record were read. Their bytes/hashes were recomputed. receipt.build_history exactly equals build-history.json; receipt.audit exactly equals audit-record.json; the entire actual-types.txt occurs verbatim in audit.log; actual DECL names and order exactly equal receipt.all_owned_names. Each owned constant's transitive axiom set is exactly within the standard whitelist, and their union is exactly propext/Classical.choice/Quot.sound.

| Evidence | Result / SHA256 |
| --- | --- |
| Final source-02 kernel check | exit0, 4.7908381298184395 seconds |
| build-02.log | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626; 133 bytes |
| First complete whole-owner audit | exit0, 5.807195521891117 seconds; U22AU_AXIOM_GATE PASS |
| audit.log | b282de7f757833a94bf4b2604e3cc89e2dabddaf3b997febc9c5e51bdeb825b9; 1716 bytes |
| build-history.json | 9414d6746c318fd5c094de8f2e0e176bd5c5ef91a8d94f5d2f85f81c4f4de09e |
| audit-record.json | d5f3df24068e8fc29469737f850f7d32835d1cb4fc4b96f3f80494335ddfdd30 |
| Current own OpenBallOscillation.olean | e8302c05e5b9717224b8ef8a78cad3a469d277b7f4c8fb5cc80e9a14509dca06; 162104 bytes |

The own accepted-source-view OpenBallOscillation.olean symlink resolves to that identical worktree object. The environment manifest records reuse of the accepted read-only source view plus only the module's own new artifact, and the exact qualified AQ source. Both recorded successful kernel/audit runs use CPU14-17, native8192MiB, jobs4, autoImplicit=false. The successful source log contains only the known thin-overlay/mathlib local-changes warning; it contains no proof error. No warning was suppressed or fixed by changing already successful bytes.

The audit program was read completely: it first requires both exact frozen targets to exist as theorems and the definition to exist as a definition, then iterates ALL environment constants with actual getModuleIdxFor? owner Shao.OQ3.OpenBallOscillation. It rejects owned axioms and uses Lean.collectAxioms recursively on every owned constant, including the definition and generated theorem; this is not a public-name or namespace-prefix-only audit. It records precisely one frozen definition, two frozen theorems, three total owned theorems and four total owned declarations. The source scan found no sorry/admit/new axiom/unsafe/native_decide. The noncomputable/classical setup uses only the allowed standard axioms.

Archived source-01.lean SHA256 5a55a8d730c1077814b3c357e73ac26cd4c2adce826ac1071d54115d7e822ec3 has exit1; its complete log SHA256 a4a04aa860546bed4b29bfe434a27dd4be618a64c90a4dd9692ee3670ce7f204 (362 bytes) reports the wrong abs_sub_le API arity. The exact final diff replaces only that failed proof expression with the valid abs_add_le/subtraction rewrite at source33-34. Source01 is preserved and is not counted as a successful check. The final local receipt is nonempty and exactly matches the server receipt; receipt-preparation/transfer issues described in the assignment do not leave an evidence discrepancy in the actual final artifacts inspected here. This review makes no separate claim to have observed those earlier administrative operations live.

## Final verdict and handback

Every final source line, complete actual owned type, global definition value and proof-local value is covered. The frozen definition is CORRECT; open_ball_oscillation_properties is CORRECT; open_ball_oscillation_integrable is CORRECT; open_ball_oscillation_properties._simp_1_1 is CORRECT. With the verified exact-source server kernel and recursive whole-owner axiom evidence reused, U22au meets LEAN_FULLY_CHECKED in its precise auxiliary scope. No source assumption was changed and no quantitative original-source claim was silently promoted.

Only this report is written. Its final integrity check rechecks the frozen local inputs unchanged and returns report SHA256/bytes/lines. After that check this reviewer stops all tools/writes and returns; the OQ3 lead owns the next source-bound dependency and continuation.
