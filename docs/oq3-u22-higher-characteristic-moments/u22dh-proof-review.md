# U22DH193 independent complete review

STATUS: CORRECT

The frozen theorem, its entire proof, both actual owned theorem types, and the original exact-source server kernel/transitive-axiom evidence are consistent and complete. No mathematical or evidence gap was found in DH193's stated scope.

## Independence, authority, and coverage

I am the fresh non-author reviewer assigned only `drafts/oq3/u22dh-proof-review.md`. I have not authored, edited, repaired, compiled, or audited the implementation. No child, sidebar chat, cross-sidebar message, Git mutation, cache mutation, or new Lean command was used. Read-only server Python/Git object inspection reused existing successful artifacts.

Read the math-theorem skill and its complete prompt-library, openai-workflow, and lean-verification references; applicable AGENTS.md, SERVER.md, current streamlined acceptance, takeover/restart instructions, selected current TEAM and REGISTRY fields. The prescribed delegation setting is gpt-6.1-sol/xhigh. OQ3's activated owner remains chat `01a1669a-bca1-75e0-9d87-d07baee7b90a`, old owner released, child ceiling 1. This review acquires no lane ownership. All Lean remains server-only; CPU0-9/external 80GiB and all lane limits remain intact.

Complete reading covered all 55 new source lines, all 16 frozen-scope lines, all 16 actual-type lines including both actual let-values, all 47 audit-source lines, and the complete new receipt/build-history/audit-record/environment/dependency-binding files. The original server copies, complete 133-byte build log, complete 1163-byte audit log, and current new source/object metadata were also read. There are 1 public theorem, 2 actual owned theorem constants, 0 definitions, 0 private theorems, and 1 generated theorem; no owned value body is omitted.

## Exact declaration and semantic fidelity

Source lines 9-17 equal frozen-scope lines 6-14 in mathematical content and binder order. The actual main type at actual-types lines 6-14 preserves every binder and conclusion: arbitrary measure `ν : Measure ℝ`, its genuine `IsProbabilityMeasure ν` instance, arbitrary `m : ℕ`, only the genuine finite absolute-moment premise `Integrable (fun x : ℝ => |x| ^ m) ν`, then arbitrary `t : ℝ`.

Both statement lets were read in full and compared, rather than treated as unspecified functions:

```lean
let e : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
let P : ℝ → ℂ := fun x =>
  ∑ j ∈ Finset.range m, (((t * x : ℝ) : ℂ) * Complex.I) ^ j / (j.factorial : ℂ)
```

The actual type prints these as `have e := ...; have P := ...`; this is the same let-bound phase and finite polynomial. It concludes actual integrability of e, P, and e-P, followed by the norm of their actual complex Bochner-integral difference bounded by `(Real.exp 1 + (m : ℝ) + 1) * |t| ^ m * ∫ x, |x| ^ m ∂ν`. No integrability, remainder, exponential-moment, coefficient, centering, density, support, or target-error hypothesis has appeared. The moment integral is over the same ν and the actual |x|^m, not a supplied majorant or scalar proxy.

## Complete proof assessment by source lines

- Lines 1-8 import the qualified pointwise theorem and Bochner API, open notation, and use a noncomputable section; they add no mathematical assumptions or definitions. Lines 18-20 introduce the two fixed let-values and the finite real constant C, without turning either let-value into an arbitrary input.
- Lines 21-26 prove continuity of the actual phase and actual finite polynomial. Real multiplication, real-to-complex coercion, multiplication by I, complex exponential, powers, division by fixed factorial coefficients, and finite summation are continuous. All required measurability follows for ℝ→ℂ; no moment hypothesis is used here.
- Lines 27-30 dominate the actual phase by the constant real function 1. Probability supplies the finite-measure instance needed by `integrable_const`; `Complex.norm_exp_ofReal_mul_I (t*x)` gives norm exactly 1 for every real x and t. `Integrable.mono'` receives actual ae strong measurability and the pointwise norm bound. Phase integrability is derived, not assumed or inferred from an exponential moment.
- Lines 31-37 instantiate the fully qualified DG192 bound at the real number t*x and the same arbitrary natural m. Its phase and factorial polynomial coincide exactly with e and P. The identity `|t*x|^m = |t|^m * |x|^m` uses abs_mul and mul_pow, and associativity yields exactly `C * |x|^m`. This works at all signs and zero; no division by t or x occurs.
- Lines 38-41 multiply the stated finite-moment function by the fixed real C, then apply `Integrable.mono'` to the genuine complex remainder. Continuity of e-P supplies measurability and the just-proved bound supplies domination. C is finite and nonnegative; no hidden positivity or extra integrability premise is required by the invoked API.
- Lines 42-44 derive P's integrability from the already established integrability of e and e-P. Pointwise `e x - (e x - P x) = P x` is exactly `sub_sub_cancel`; `Integrable.congr` transfers actual ae equality in the correct direction. This avoids assuming lower-order moments or the desired polynomial integrability.
- Line 45 returns all three actual integrability results. Lines 46-49 rewrite the difference of actual integrals as the integral of e-P using `integral_sub he hP`, apply the Bochner norm inequality, and compare real integrals with `integral_mono hr.norm hmajor hbound`. Both functions in the monotonicity step are proved integrable, so the estimate does not exploit Bochner's nonintegrable default value.
- Lines 50-51 pull the actual real constant C outside the integral using `integral_const_mul`, then unfold C definitionally to obtain exactly the frozen constant and moment. Lines 52-55 only close the sections/namespaces. Every source line was covered; there is no unexamined helper proof.

## Boundary and quantifier attack

Every natural m, including 0, and every real t, including 0 and negative values, remain universally quantified in both source and actual type. At m=0 the polynomial is the empty sum 0 and |x|^0=|t|^0=1, including x=t=0 by Lean's natural-power convention. Probability makes the moment integral 1, so the phase-integral norm is bounded by the stated positive coarse constant exp(1)+1; no positive-order argument was misapplied. For t=0 and m≥1, e=1 and P=1, hence remainder and integral error vanish, consistently with RHS 0. For t<0 the unit-phase identity and absolute-value product identity still apply without modification. Heavy-tailed probability laws with only the stated finite m-th moment are covered. No symmetry, independence, or regularity of ν is silently used.

## Consumed dependency and primary-interface review

DG192 was reused only by its full consumed six-line actual interface, exact bindings, and selected qualified status/verdict; its old complete proof/report was not reread and its accepted gate was not replayed. Its interface is `∀ (m : ℕ) (t : ℝ), ‖exp (↑t * I) - ∑ j ∈ range m, (↑t * I)^j / ↑j.factorial‖ ≤ (Real.exp 1 + ↑m + 1) * |t|^m`, with no hypotheses, statement lets, or definition values. Thus instantiation at t*x discharges exactly the sole pointwise estimate needed here. Its actual-type file SHA256 is `bba53bc38bb3438683baebf7448bdd622e354a078c9150bf6bf3aa2114f005bb`.

The current DG source/object remain `fa560d715fe1ee72ab65aadbc4825db4b3183339609a8b50a83f4dcb9cab7e27` / `3381985746146f4dd8da03e3033caf1eb2837f17a3628587c9334cca61b87ffc` (object 126360 bytes). Receipt hash `7e0e3f8c2e720d7974d30235f12c8b8ce0e21556a0942e1a39b33790561c6dbe` and full-review hash `3f32285182604348c468e02d13e9a16492796a4295154e802d3d2aa0239eea66` match. Selected lane status line 1670 records COMPLETE_QUALIFIED, all 86 review lines parent-read, reviewer stopped. The immutable author's pending-review receipt is correctly complemented by that later independent CORRECT verdict and qualified lane status.

Read the actually consumed primary Mathlib interfaces through read-only `git show HEAD:Mathlib/...`, including their applicable typeclass/measure context: Bochner Basic integral_sub (261-262), integral_const_mul (288-289), integral_mono (670-671), and norm_integral_le_integral_norm (970); Integrable mono' (104-105), congr (126), integrable_const (166), sub (532-533), norm (544), and const_mul (1028-1029). The API requires exactly the integrability/measurability/ae bound/equality supplied above. Complex is a complete real normed space; ℝ is an ordered complete real normed space. The `Integrable` definition (58-60) is genuine ae strong measurability plus finite norm integral. Also read Complex.norm_exp_ofReal_mul_I (Trigonometric:952) and Continuous.aestronglyMeasurable (AEStronglyMeasurable:240-242); their real/second-countable conditions hold here.

Bochner Basic source SHA256 is `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`, current object `f5094fe4e519cc8ffde3283787cbd42f5f686cd9121e35776578902dadae75a7` (688952 bytes). L1Space Integrable source is `d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759`, current object `6fe2b53c5cd131f560eeff2765fbdbbf956a12b8676cb5ec9b2bae9c74239aa0` (621928 bytes). These equal every corresponding prebound record; sparse sources were neither hydrated nor rebuilt.

## Original kernel and complete owner/axiom evidence

Original server run: `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22dh-20261023`; worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`. Pinned project toolchain is leanprover/lean4:v4.36.0-rc1, Mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`, package symlink resolves to shared-v34/packages/mathlib. No local toolchain was used. Original gates record CPU14-17, -M8192, -j4, and autoImplicit=false.

First complete kernel attempt 01 succeeded, exit 0, 4.58117925003171 seconds. All 133 build-log bytes contain only the known Lake overlay local-changes warning, no errors or proof warnings; SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`. The history has one attempt and no repairs or failed iterations. Current target source is still 2241 bytes / 55 lines, and current target olean is still 82752 bytes / `7254c1f55a11afb42754fe432a64f8036880333d1da877bca8ef6fff2b58e027`. Object mtime 2026-10-24T00:04:12.014042Z follows the original source snapshot and precedes the saved successful receipt.

Original owner/axiom audit succeeded, exit 0, 5.456648102030158 seconds; all 1163 log bytes were read, SHA256 `c56161a582b549d3baa83bd6b0a05c0b111d8e63251c832dfc127026cd658846`. Audit lines 23-32 traverse every actual environment constant by owning module, not namespace or a public-name list, reject any owned axiom, and call recursive `Lean.collectAxioms` on every owned constant with whitelist propext/Classical.choice/Quot.sound. This covers generated/private/external-namespace ownership if present. The frozen theorem exists and is a theorem, target count is exactly 1, actual theorem/declaration counts are both 2, and the gate reports PASS.

The complete actual owner list is (1) `Shao.OQ3.scalar_characteristic_integrated_taylor_remainder._simp_1_1`, whose full type is `∀ {α : Type u_1} [inst : Preorder α] (a : α), (a ≤ a) = True`, axioms [propext], kind theorem; and (2) the complete main frozen type described above, axioms [propext, Classical.choice, Quot.sound], kind theorem. No additional owner, definition body, private theorem, axiom, or namespace-scoped exception is omitted. Source contains no sorry/admit/new axiom/unsafe/native_decide. Classical reasoning uses only the accepted standard basis.

This is acceptance by the original exact-source kernel/recursive-owner evidence, not a claim that this reviewer ran Lean. Zero new Lean compilations, audit commands, smoke tests, or accepted-gate replays occurred.

## Exact new artifact ledger

- Source `u22dh-source.lean`, 2241 bytes / 55 lines: `2addc56b8b046692b8f1b07231cc1ad1905e9b1c599d2f4cfaa4fa405820736b`.
- Frozen scope, 1604 bytes / 16 lines: `9d068528d3f5a2e8040cd353b7635df7a305066849fa336906a88d600475fe2f`.
- Actual types, 911 bytes / 16 lines: `a4fdc28d65ddb3b9982914dca9e713e5d3f9e51211d6f408b6b2cfa4dfaa51a8`.
- Audit source, 2043 bytes / 47 lines: `bdc4b91d8be15a368f3ac33a1a10d2391a21b12345c979cf4d267901ef50b915`.
- Receipt: `d9ef0d797d8d8cb38c0564a92101b5eb0c720fbd57f498106fb440fed70e9d60`.
- Build history: `3e7ea6daa89bc05b2060ac1cb70b1d110e196a6eaf6dba6507995f04209e2525`.
- Audit record: `c6e9ddb96236c13f04de7cdbeef11f24de22eb0ab5f14a2c7ff699226e87bc34`.
- Audit environment: `7252e96ae7e6d54d6563c49f32288a20136b40614cf926855bd66f1d60937803`.
- Dependency bindings: `133e675f72d3ff363965678de26a5f62c653b3671b63944fd2669a6c04e878dc`.

All nine local artifacts match the original server artifacts exactly. The four source/scope/types/audit text files are valid UTF-8, without BOM or CR bytes, with the recorded LF counts. No format repair or refreeze occurred. Original run scope mtime is 00:03:52.174097Z, before source-01 at 00:04:07.878054Z and the first recorded check. Final read-only server identity observation at 2026-10-24T00:07:29.939603Z was branch `feat/oq3-higher-characteristic-expansion`, HEAD `e628d42b737b785ab3d29ac5511258ed0ad847cb`, tree `c4ec2880ef7431941f59582c283618002bdb9044`, matching the saved PR236 publication identity. No publication/merge action was taken.

## Scope and final verdict

DH193 proves the actual scalar characteristic integrated finite Taylor-remainder estimate, all natural orders and all real frequencies, with actual phase/polynomial/remainder integrability derived from genuine probability plus the stated finite absolute moment. It does not yet identify the polynomial integral with canonical moment coefficients, prove higher Edgeworth coherence, close full-frequency/inversion/exterior or new-rho Laplace arguments, or close original OQ3 B/D. Original scope, p54 repairs, strict original beta<2/5 restrictions, and external-result attribution are unchanged. This report claims correctness of this auxiliary bridge, not research novelty or original-root completion.

Final decision: CORRECT. Complete independent source-to-statement/proof and all-owned actual type/value coverage is satisfied; exact-source original kernel and whole-owned recursive transitive-axiom receipts are accepted by reuse. No critical or noncritical mathematical/evidence gap was found for this frozen unit. No assumptions, proof bytes, cached objects, or accepted old evidence were changed.

After saving and verifying this sole report, reviewer tools and writes stop. This bounded review's completion does not imply persistent runtime or lane continuation.

Review completed UTC: 2026-10-24T00:10:22.357227+00:00.
